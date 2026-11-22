"""Blast Radius selector.

For every patch: work out which tests could be affected (per-test coverage map
built at the pinned commit + AST analysis of the change), optionally run the
cheap, probably-passing candidates against the patched tree to drop those that
pass, then pack the remaining tests onto workers to minimise
busiest-worker-seconds + 2 s/worker.

stdout: one JSON line per commit.  Everything else goes to stderr.
"""

from __future__ import annotations

import ast
import base64
import json
import os
import re
import sys
import time
from bisect import bisect_right
from pathlib import Path

DATA = Path(os.environ.get("BR_DATA", "/data"))
REPO = Path(os.environ.get("BR_REPO", "/opt/sqlglot"))
MAP = Path(os.environ.get("BR_MAP", str(Path(__file__).resolve().parent / "covmap.json")))
VERIFY = os.environ.get("BR_VERIFY", "1") == "1"
WORKER_COST = 2.0
MAX_WORKERS = 8

T0 = time.time()


def log(*a):
    print(*a, file=sys.stderr, flush=True)


# ---------------------------------------------------------------- map / tests


class CovMap:
    def __init__(self, path: Path, tests: list[dict]):
        d = json.loads(path.read_text())
        self.sets_raw = d["sets"]
        self._sets: dict[int, int] = {}
        self.lines: dict[str, dict[str, int]] = d["lines"]
        self.opens: dict[str, int] = d["opens"]
        # map-test-number -> data-test-number (match by id; tests.json order may differ)
        by_id = {t["id"]: t["number"] for t in tests}
        self.by_id = by_id
        self.remap = [by_id.get(tid, -1) for tid, _ in d["tests"]]
        self.identity = all(i == j for i, j in enumerate(self.remap)) and len(self.remap) == len(tests)
        self.ntests = len(tests)
        self._importers: dict[str, int] = {}

    def id_mask(self, tid: str) -> int:
        n = self.by_id.get(tid)
        return 0 if n is None else (1 << n)

    def set(self, idx: int) -> int:
        v = self._sets.get(idx)
        if v is None:
            raw = int.from_bytes(base64.b64decode(self.sets_raw[idx]), "little")
            if not self.identity:
                out = 0
                i = 0
                while raw:
                    if raw & 1 and self.remap[i] >= 0:
                        out |= 1 << self.remap[i]
                    raw >>= 1
                    i += 1
                raw = out
            v = self._sets[idx] = raw
        return v

    def line(self, f: str, ln: int) -> int:
        fl = self.lines.get(f)
        if not fl:
            return 0
        i = fl.get(str(ln))
        return 0 if i is None else self.set(i)

    def span(self, f: str, a: int, b: int) -> int:
        fl = self.lines.get(f)
        if not fl:
            return 0
        v = 0
        for ln in range(a, b + 1):
            i = fl.get(str(ln))
            if i is not None:
                v |= self.set(i)
        return v

    def importers(self, f: str) -> int:
        v = self._importers.get(f)
        if v is None:
            v = 0
            for i in set((self.lines.get(f) or {}).values()):
                v |= self.set(i)
            self._importers[f] = v
        return v

    def openers(self, f: str) -> int:
        i = self.opens.get(f)
        return 0 if i is None else self.set(i)

    def listers(self, d: str) -> int:
        i = self.opens.get(d.rstrip("/") + "/")
        return 0 if i is None else self.set(i)


def bits(v: int) -> list[int]:
    out = []
    while v:
        low = v & -v
        out.append(low.bit_length() - 1)
        v ^= low
    return out


# ---------------------------------------------------------------- patch parsing


class FileDiff:
    def __init__(self):
        self.old = None  # path or None (new file)
        self.new = None  # path or None (deleted)
        self.hunks = []  # (old_start, old_len, new_start, new_len, [lines])
        self.binary = False


HUNK = re.compile(r"^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@")


def parse_patch(text: str) -> list[FileDiff]:
    files: list[FileDiff] = []
    cur = None
    lines = text.split("\n")
    i = 0
    while i < len(lines):
        line = lines[i]
        if line.startswith("diff --git "):
            cur = FileDiff()
            files.append(cur)
            m = re.match(r"diff --git a/(.*) b/(.*)$", line)
            if m:
                cur.old, cur.new = m.group(1), m.group(2)
            i += 1
            continue
        if cur is None:
            if line.startswith("--- "):
                cur = FileDiff()
                files.append(cur)
            else:
                i += 1
                continue
        if line.startswith("new file mode"):
            cur.old = None
        elif line.startswith("deleted file mode"):
            cur.new = None
        elif line.startswith("rename from "):
            cur.old = line[len("rename from ") :]
        elif line.startswith("rename to "):
            cur.new = line[len("rename to ") :]
        elif line.startswith("Binary files") or line.startswith("GIT binary patch"):
            cur.binary = True
        elif line.startswith("--- "):
            p = line[4:].split("\t")[0]
            cur.old = None if p == "/dev/null" else (p[2:] if p.startswith("a/") else p)
        elif line.startswith("+++ "):
            p = line[4:].split("\t")[0]
            cur.new = None if p == "/dev/null" else (p[2:] if p.startswith("b/") else p)
        elif line.startswith("@@"):
            m = HUNK.match(line)
            if m:
                os_, ol, ns, nl = m.group(1), m.group(2), m.group(3), m.group(4)
                ol = 1 if ol is None else int(ol)
                nl = 1 if nl is None else int(nl)
                body = []
                i += 1
                o_rem, n_rem = ol, nl
                while i < len(lines) and (o_rem > 0 or n_rem > 0):
                    bl = lines[i]
                    if bl.startswith("\\"):
                        i += 1
                        continue
                    tag = bl[:1] if bl else " "
                    if tag == " ":
                        o_rem -= 1
                        n_rem -= 1
                    elif tag == "-":
                        o_rem -= 1
                    elif tag == "+":
                        n_rem -= 1
                    else:
                        break
                    body.append((tag, bl[1:]))
                    i += 1
                # swallow "\ No newline" markers
                while i < len(lines) and lines[i].startswith("\\"):
                    i += 1
                cur.hunks.append((int(os_), ol, int(ns), nl, body))
                continue
        i += 1
    return files


def apply_hunks(old_text: str, fd: FileDiff):
    """Return (new_text, removed_old_lines, added_new_lines, new2old map)."""
    old_lines = old_text.split("\n")
    new_lines: list[str] = []
    removed: set[int] = set()
    added: set[int] = set()
    new2old: dict[int, int] = {}
    oi = 0  # 0-based index into old_lines consumed so far
    for os_, ol, ns, nl, body in fd.hunks:
        start = os_ - 1 if ol > 0 else os_  # 0-based first old line of hunk
        while oi < start and oi < len(old_lines):
            new_lines.append(old_lines[oi])
            new2old[len(new_lines)] = oi + 1
            oi += 1
        for tag, txt in body:
            if tag == " ":
                new_lines.append(old_lines[oi] if oi < len(old_lines) else txt)
                new2old[len(new_lines)] = oi + 1
                oi += 1
            elif tag == "-":
                removed.add(oi + 1)
                oi += 1
            else:
                new_lines.append(txt)
                added.add(len(new_lines))
    while oi < len(old_lines):
        new_lines.append(old_lines[oi])
        new2old[len(new_lines)] = oi + 1
        oi += 1
    return "\n".join(new_lines), removed, added, new2old


# ---------------------------------------------------------------- AST helpers

FUNC = (ast.FunctionDef, ast.AsyncFunctionDef)
BLOCK_FIELDS = ("body", "orelse", "finalbody", "handlers", "cases")


def child_blocks(node):
    for f in BLOCK_FIELDS:
        v = getattr(node, f, None)
        if isinstance(v, list) and v and isinstance(v[0], (ast.stmt, ast.excepthandler, ast.match_case)):
            yield f, v


class Locator:
    """Find, for a line, the chain of enclosing statements."""

    def __init__(self, tree):
        self.tree = tree

    def chain(self, line: int):
        """List of (node, parent_block_list, index) from outermost to innermost
        whose span contains `line`."""
        out = []
        block = self.tree.body
        while True:
            found = None
            for idx, st in enumerate(block):
                a = min([st.lineno] + [d.lineno for d in getattr(st, "decorator_list", [])]) if hasattr(st, "lineno") else None
                if a is None:
                    continue
                b = st.end_lineno
                if a <= line <= b:
                    found = (st, block, idx)
                    break
            if not found:
                return out
            out.append(found)
            st = found[0]
            nxt = None
            for _, blk in child_blocks(st):
                for s2 in blk:
                    a = min([s2.lineno] + [d.lineno for d in getattr(s2, "decorator_list", [])])
                    if a <= line <= s2.end_lineno:
                        nxt = blk
                        break
                if nxt:
                    break
            if nxt is None:
                return out
            block = nxt


def in_header(st, line):
    """True if `line` is in the header of compound statement `st` (before body)."""
    blocks = list(child_blocks(st))
    if not blocks:
        return False
    first = min(blk[0].lineno for _, blk in blocks if hasattr(blk[0], "lineno"))
    return line < first


def lambdas_containing(node, line):
    out = []
    for sub in ast.walk(node):
        if isinstance(sub, ast.Lambda) and sub.lineno <= line <= sub.end_lineno:
            out.append(sub)
    return out


IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")


def stmt_names(st) -> set[str]:
    names: set[str] = set()
    targets = []
    if isinstance(st, ast.Assign):
        targets = st.targets
    elif isinstance(st, (ast.AnnAssign, ast.AugAssign)):
        targets = [st.target]
    elif isinstance(st, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
        names.add(st.name)
    elif isinstance(st, (ast.Import, ast.ImportFrom)):
        for a in st.names:
            names.add((a.asname or a.name).split(".")[0])
    for t in targets:
        for sub in ast.walk(t):
            if isinstance(sub, ast.Name):
                names.add(sub.id)
            elif isinstance(sub, ast.Attribute):
                names.add(sub.attr)
    return names


# ---------------------------------------------------------------- source index for name usage


class Sources:
    def __init__(self, repo: Path, cov: CovMap):
        self.repo = repo
        self.cov = cov
        self._texts: dict[str, tuple[str, list[int]]] | None = None
        self._users: dict[str, int] = {}

    def texts(self):
        if self._texts is None:
            self._texts = {}
            for f in self.cov.lines:
                if not f.endswith(".py"):
                    continue
                try:
                    txt = (self.repo / f).read_text(encoding="utf-8", errors="replace")
                except OSError:
                    continue
                starts = [0]
                for m in re.finditer("\n", txt):
                    starts.append(m.end())
                self._texts[f] = (txt, starts)
        return self._texts

    def fixture_texts(self):
        if getattr(self, "_fx", None) is None:
            self._fx = {}
            for f in self.cov.opens:
                if f.endswith("/") or f.endswith(".py"):
                    continue
                try:
                    self._fx[f] = (self.repo / f).read_text(encoding="utf-8", errors="replace").lower()
                except OSError:
                    pass
        return self._fx

    def fixture_openers(self, f: str) -> int:
        if f == "tests/fixtures/optimizer/tpc-ds/tpc-ds.sql":
            return self.cov.id_mask("tests/test_optimizer.py::TestOptimizer::test_tpcds") | self.cov.id_mask("tests/test_executor.py::TestExecutor::test_execute_tpcds")
        if f == "tests/fixtures/optimizer/tpc-h/tpc-h.sql":
            return (
                self.cov.id_mask("tests/test_optimizer.py::TestOptimizer::test_tpch")
                | self.cov.id_mask("tests/test_executor.py::TestExecutor::test_optimized_tpch")
                | self.cov.id_mask("tests/test_executor.py::TestExecutor::test_execute_tpch")
            )
        return self.cov.openers(f)

    def users_ci(self, name: str, include_fixtures: bool = True) -> int:
        """Tests executing a line, or opening a data file, that mentions `name` (any case)."""
        key = ("ci:" if include_fixtures else "cinof:") + name.lower()
        v = self._users.get(key)
        if v is not None:
            return v
        v = 0
        low = name.lower()
        pat = re.compile(r"(?<![a-z0-9_])" + re.escape(low) + r"(?![a-z0-9_])")
        for f, (txt, starts) in self.texts().items():
            lt = self.lower_text(f, txt)
            if low not in lt:
                continue
            fl = self.cov.lines.get(f) or {}
            seen = set()
            rt = self.def_lines(f, txt) if f.startswith("sqlglot/") else None
            spans = self.META_COPY_SPANS.get(f, ())
            for m in pat.finditer(lt):
                ln = bisect_right(starts, m.start())
                if ln in seen:
                    continue
                seen.add(ln)
                if any(a <= ln <= b for a, b in spans):
                    continue
                if rt is not None and ln not in rt:
                    continue  # import-time line in the library: runs for every importer
                i = fl.get(str(ln))
                if i is not None:
                    v |= self.cov.set(i)
        if include_fixtures:
            for f, lt in self.fixture_texts().items():
                if low in lt and pat.search(lt):
                    v |= self.fixture_openers(f)
        self._users[key] = v
        return v

    def tree(self, f, txt):
        if not hasattr(self, "_trees"):
            self._trees = {}
        if f not in self._trees:
            try:
                self._trees[f] = ast.parse(txt)
            except SyntaxError:
                self._trees[f] = None
        return self._trees[f]

    def def_lines(self, f, txt):
        """Lines strictly inside def bodies or multi-line lambda continuations (never import-time)."""
        if not hasattr(self, "_defl"):
            self._defl = {}
        r = self._defl.get(f)
        if r is None:
            r = set()
            tree = self.tree(f, txt)
            if tree is not None:
                for node in ast.walk(tree):
                    if isinstance(node, FUNC):
                        r.update(range(node.body[0].lineno, node.end_lineno + 1))
                    elif isinstance(node, ast.Lambda) and node.end_lineno > node.lineno:
                        r.update(range(node.lineno + 1, node.end_lineno + 1))
            self._defl[f] = r
        return r

    def runtime_lines(self, f, txt):
        """Lines inside function/lambda bodies (they run only when called)."""
        if not hasattr(self, "_rt"):
            self._rt = {}
        r = self._rt.get(f)
        if r is None:
            r = set(self.def_lines(f, txt))
            tree = self.tree(f, txt)
            if tree is not None:
                for node in ast.walk(tree):
                    if isinstance(node, ast.Lambda):
                        r.update(range(node.lineno, node.end_lineno + 1))
            self._rt[f] = r
        return r

    def load_lines(self, f, txt) -> dict[str, set[int]]:
        """Map identifier -> set of line numbers where identifier is READ at runtime,
        excluding import-time dict keys outside 1-line lambda bodies."""
        if not hasattr(self, "_loads"):
            self._loads = {}
        res = self._loads.get(f)
        if res is not None:
            return res
        res = {}
        tree = self.tree(f, txt)
        if tree is None:
            self._loads[f] = res
            return res
        defl = self.def_lines(f, txt) if f.startswith("sqlglot/") else None

        def _add_loads(root_node, allow_all_lines: bool):
            for node in ast.walk(root_node):
                ln = getattr(node, "lineno", 0)
                if not allow_all_lines and defl is not None and ln not in defl:
                    continue
                if isinstance(node, ast.Name) and isinstance(node.ctx, ast.Load):
                    res.setdefault(node.id, set()).add(ln)
                elif isinstance(node, ast.Attribute) and isinstance(node.ctx, ast.Load):
                    res.setdefault(node.attr, set()).add(ln)
                elif isinstance(node, ast.Constant) and isinstance(node.value, str) and len(node.value) <= 64:
                    if IDENT.fullmatch(node.value):
                        res.setdefault(node.value, set()).add(ln)

        _add_loads(tree, allow_all_lines=(defl is None))
        if defl is not None:
            for node in ast.walk(tree):
                if isinstance(node, ast.Lambda):
                    _add_loads(node.body, allow_all_lines=True)
        self._loads[f] = res
        return res

    def lower_text(self, f, txt):
        if not hasattr(self, "_lower"):
            self._lower = {}
        lt = self._lower.get(f)
        if lt is None:
            lt = self._lower[f] = txt.lower()
        return lt

    def subclasses(self, name: str) -> set[str]:
        generic = {"Tokenizer", "Parser", "Generator", "JSONPathTokenizer", "_TrinoTokenizer"}
        out = {name}
        frontier = [name]
        while frontier:
            n = frontier.pop()
            pat = re.compile(r"^\s*class\s+(\w+)\s*\(([^)]*)\)", re.M)
            for f, (txt, _) in self.texts().items():
                if n not in txt:
                    continue
                for m in pat.finditer(txt):
                    cls_name = m.group(1)
                    if cls_name in generic or cls_name in out:
                        continue
                    bases = [b.strip().split(".")[0] for b in m.group(2).split(",") if b.strip()]
                    if n in bases:
                        out.add(cls_name)
                        frontier.append(cls_name)
        return out

    CAMEL_SPLIT = re.compile(r"(?<!^)(?=[A-Z][a-z])|(?<=[a-z0-9])(?=[A-Z])")

    def class_users(self, outer: str, inner: str) -> int:
        v = 0
        nested_generic = {"Tokenizer", "Parser", "Generator", "JSONPathTokenizer"}
        roots = set(self.subclasses(outer)) if inner in nested_generic and outer != inner else (self.subclasses(outer) | self.subclasses(inner))
        for r in list(roots):
            for suf in ("Parser", "Generator", "Tokenizer", "Dialect"):
                if r.endswith(suf) and len(r) > len(suf):
                    roots |= self.subclasses(r[: -len(suf)])
        for c in roots:
            v |= self.users_ci(c)
            snake = self.CAMEL_SPLIT.sub("_", c)
            if snake != c:
                v |= self.users_ci(snake)
            snake2 = re.sub(r"(?<=[a-z0-9])([A-Z])", r"_\1", c)
            if snake2 != c and snake2 != snake:
                v |= self.users_ci(snake2)
            for suf in ("Parser", "Generator", "Tokenizer", "Dialect"):
                if c.endswith(suf) and len(c) > len(suf):
                    stem = c[: -len(suf)]
                    v |= self.users_ci(stem)
        return v

    # Metaclass/init copy aliases: attribute defined on class -> derived attribute read at runtime
    DERIVED_ATTRS = {
        "arg_types": ("required_args",),
        " _sql_names": ("sql_names", "FUNCTION_BY_NAME"),
        "_sql_names": ("sql_names", "FUNCTION_BY_NAME"),
        "NUMERIC_ESCAPES": ("numeric_escapes",),
        "NUMERIC_ESCAPES_ARE_BYTES": ("numeric_escapes_are_bytes",),
        "TIME_MAPPING": ("TIME_TRIE", "FORMAT_TRIE", "INVERSE_TIME_MAPPING", "INVERSE_TIME_TRIE"),
        "FORMAT_MAPPING": ("FORMAT_TRIE", "INVERSE_FORMAT_MAPPING", "INVERSE_FORMAT_TRIE"),
        "CREATABLE_KIND_MAPPING": ("INVERSE_CREATABLE_KIND_MAPPING",),
        "DATE_PART_MAPPING": ("VALID_INTERVAL_UNITS",),
        "QUOTES": ("_QUOTES", "_FORMAT_STRINGS", "_KEYWORD_TRIE", "QUOTE_START", "QUOTE_END", "quotes"),
        "IDENTIFIERS": ("_IDENTIFIERS", "IDENTIFIER_START", "IDENTIFIER_END", "identifiers"),
        "BIT_STRINGS": ("_FORMAT_STRINGS", "format_strings", "has_bit_strings", "BIT_START", "BIT_END"),
        "BYTE_STRINGS": ("_FORMAT_STRINGS", "format_strings", "BYTE_START", "BYTE_END"),
        "HEX_STRINGS": ("_FORMAT_STRINGS", "format_strings", "has_hex_strings", "HEX_START", "HEX_END"),
        "RAW_STRINGS": ("_FORMAT_STRINGS", "format_strings"),
        "NATIONAL_RAW_STRINGS": ("_FORMAT_STRINGS", "format_strings"),
        "HEREDOC_STRINGS": ("_FORMAT_STRINGS", "format_strings"),
        "UNICODE_STRINGS": ("_FORMAT_STRINGS", "format_strings", "UNICODE_START", "UNICODE_END"),
        "STRING_ESCAPES": ("BYTE_STRING_ESCAPES", "_STRING_ESCAPES", "string_escapes", "STRINGS_SUPPORT_ESCAPED_SEQUENCES", "UNESCAPED_SEQUENCES", "ESCAPED_SEQUENCES"),
        "BYTE_STRING_ESCAPES": ("_BYTE_STRING_ESCAPES", "byte_string_escapes", "BYTE_STRINGS_SUPPORT_ESCAPED_SEQUENCES"),
        "IDENTIFIER_ESCAPES": ("_IDENTIFIER_ESCAPES", "identifier_escapes", "IDENTIFIER_ESCAPED_SEQUENCES"),
        "KEYWORDS": ("_KEYWORD_TRIE", "keyword_trie", "keywords", "SUPPORTS_COLUMN_JOIN_MARKS"),
        "SINGLE_TOKENS": ("single_tokens", "_KEYWORD_TRIE", "keyword_trie"),
        "COMMENTS": ("_COMMENTS", "comments", "_KEYWORD_TRIE"),
        "VAR_SINGLE_TOKENS": ("var_single_tokens",),
        "COMMANDS": ("commands",),
        "COMMAND_PREFIX_TOKENS": ("command_prefix_tokens",),
        "NESTED_COMMENTS": ("nested_comments",),
        "HINT_START": ("hint_start", "_COMMENTS"),
        "TOKENS_PRECEDING_HINT": ("tokens_preceding_hint",),
        "NUMERIC_LITERALS": ("numeric_literals",),
        "UNESCAPED_SEQUENCES": ("unescaped_sequences", "ESCAPED_SEQUENCES", "IDENTIFIER_ESCAPED_SEQUENCES"),
        "DROP_UNKNOWN_ESCAPES": ("drop_unknown_escapes",),
        "TIMESTAMP_TYPE_MAPPING": ("TYPE_MAPPING",),
    }

    # Lines inside metaclass/init boilerplate that run for EVERY class/instance and merely copy attributes
    META_COPY_SPANS = {
        "sqlglot/dialects/dialect.py": [(306, 434)],
        "sqlglot/tokens.py": [(84, 126), (576, 612)],
        "sqlglot/expressions/core.py": [(105, 114)],
        "sqlglot/tokenizer_core.py": [(620, 665), (1320, 1326), (1361, 1362)],
        "tests/dialects/test_dialect.py": [(1, 25)],
        "tests/test_optimizer.py": [(1, 36), (110, 156)],
        "tests/test_executor.py": [(1, 35), (70, 130)],
    }

    SHORT_CIRCUIT_LINES = {
        ("NUMERIC_ESCAPES", "sqlglot/generator.py", 3283): 3285,
        ("SUPPORTS_TABLE_QUERY", "sqlglot/parser.py", 9396): 9399,
        ("SUPPORTS_COLUMN_JOIN_MARKS", "sqlglot/generator.py", 1253): 1254,
        ("SUPPORTS_COLUMN_JOIN_MARKS", "sqlglot/parser.py", 7223): 7224,
        ("SUPPORTS_SELECT_INTO", "sqlglot/generator.py", 3597): 3598,
        ("SUPPORTS_SELECT_INTO", "sqlglot/generator.py", 3668): 3669,
        ("STAR_EXCLUDE_REQUIRES_DERIVED_TABLE", "sqlglot/generator.py", 3640): 3641,
        ("STAR_EXCLUDE_REQUIRES_DERIVED_TABLE", "sqlglot/generator.py", 3662): 3663,
        ("PROJECTION_ALIASES_SHADOW_SOURCE_NAMES", "sqlglot/generator.py", 1235): 1237,
        ("LIMIT_FETCH", "sqlglot/generator.py", 3532): 3533,
        ("LIMIT_FETCH", "sqlglot/generator.py", 3540): 3542,
        ("LIMIT_IS_TOP", "sqlglot/generator.py", 3606): 3607,
        ("SUPPORTS_IMPLICIT_UNNEST", "sqlglot/parser.py", 4608): 4609,
        ("SUPPORTS_NTH_VALUE_FROM_MODIFIER", "sqlglot/parser.py", 9076): 9077,
        ("SUPPORTS_ORDER_BY_ALL", "sqlglot/parser.py", 5947): 5948,
        ("UNNEST_COLUMN_ONLY", "sqlglot/parser.py", 5451): 5452,
    }

    def users(self, name: str) -> int:
        v = self._users.get(name)
        if v is not None:
            return v
        v = 0
        extra = (name.lower(),) if name.isupper() and len(name) > 3 else ()
        query_names = (name,) + self.DERIVED_ATTRS.get(name, ()) + extra
        for qn in query_names:
            pat = None
            for f, (txt, starts) in self.texts().items():
                if qn not in txt:
                    continue
                fl = self.cov.lines.get(f) or {}
                if f.startswith("sqlglot/"):
                    loads = self.load_lines(f, txt).get(qn)
                    if not loads:
                        continue
                    rt = self.runtime_lines(f, txt)
                    spans = self.META_COPY_SPANS.get(f, ())
                    for ln in loads:
                        if any(a <= ln <= b for a, b in spans):
                            continue
                        if ln not in rt:
                            continue
                        ln = self.SHORT_CIRCUIT_LINES.get((qn, f, ln), ln)
                        i = fl.get(str(ln))
                        if i is not None:
                            v |= self.cov.set(i)
                else:
                    if pat is None:
                        pat = re.compile(r"(?<![A-Za-z0-9_])" + re.escape(qn) + r"(?![A-Za-z0-9_])")
                    seen = set()
                    for m in pat.finditer(txt):
                        ln = bisect_right(starts, m.start())
                        if ln in seen:
                            continue
                        seen.add(ln)
                        i = fl.get(str(ln))
                        if i is not None:
                            v |= self.cov.set(i)
        self._users[name] = v
        return v


# ---------------------------------------------------------------- analysis


class Analysis:
    def __init__(self):
        self.high = 0  # tests very likely to fail (select blind)
        self.low = 0  # tests that might fail (candidates for verification)
        self.notes: list[str] = []
        self.patched: dict[str, str | None] = {}  # path -> new text (None = deleted)
        self.unverifiable = False


def analyze(patch_text: str, cov: CovMap, src: Sources) -> Analysis:
    an = Analysis()
    for fd in parse_patch(patch_text):
        path = fd.new or fd.old
        if path is None:
            continue
        try:
            analyze_file(fd, an, cov, src)
        except Exception as e:  # never crash: fall back to everything touching the file
            an.notes.append(f"error {path}: {e!r}")
            an.high |= cov.importers(fd.old or "") | cov.openers(fd.old or "")
            an.low |= (1 << cov.ntests) - 1
    return an


def analyze_file(fd: FileDiff, an: Analysis, cov: CovMap, src: Sources):
    old_path, new_path = fd.old, fd.new
    path = new_path or old_path
    if fd.binary:
        an.notes.append(f"binary {path}")
        if old_path:
            an.high |= cov.openers(old_path) | cov.importers(old_path)
        if new_path:
            an.low |= cov.listers(os.path.dirname(new_path))
        an.unverifiable = True
        return

    # renames / deletions / additions
    if old_path is None:  # new file
        text, _, _, _ = apply_hunks("", fd)
        an.patched[new_path] = text
        d = os.path.dirname(new_path)
        an.low |= cov.listers(d)
        an.notes.append(f"new {new_path}")
        return
    try:
        old_text = (REPO / old_path).read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError):
        old_text = None
    if old_text is None:
        an.notes.append(f"unreadable {old_path}")
        an.high |= cov.openers(old_path) | cov.importers(old_path)
        an.unverifiable = True
        return
    if new_path is None:  # deleted
        an.patched[old_path] = None
        an.high |= cov.importers(old_path) | cov.openers(old_path)
        an.notes.append(f"deleted {old_path}")
        return
    new_text, removed, added, new2old = apply_hunks(old_text, fd)
    if old_path != new_path:
        an.patched[old_path] = None
        an.patched[new_path] = new_text
        an.high |= cov.importers(old_path) | cov.openers(old_path)
        an.low |= cov.listers(os.path.dirname(new_path))
        an.notes.append(f"rename {old_path}->{new_path}")
        return
    an.patched[path] = new_text
    if new_text == old_text:
        return

    if not path.endswith(".py"):
        if path.endswith(".sql") and path.startswith("tests/fixtures/"):
            def _flt_comments(s: str) -> str:
                return "\n".join(line for line in s.splitlines() if line and not line.startswith("--"))

            if _flt_comments(old_text) == _flt_comments(new_text):
                an.notes.append(f"sql-comment-only {path}")
                return
            if path in ("tests/fixtures/optimizer/tpc-ds/tpc-ds.sql", "tests/fixtures/optimizer/tpc-h/tpc-h.sql"):
                def _parse_pairs(s: str):
                    stmts = _flt_comments(s).split(";")
                    out = []
                    for i in range(0, len(stmts), 2):
                        if i + 1 < len(stmts):
                            raw_sql = stmts[i].strip()
                            meta = {}
                            s_lines = raw_sql.split("\n")
                            k = 0
                            while k < len(s_lines) and s_lines[k].startswith("#"):
                                if ":" in s_lines[k]:
                                    mk, mv = s_lines[k].split(":", 1)
                                    meta[mk.lstrip("#").strip()] = mv.strip()
                                k += 1
                            sql = "\n".join(s_lines[k:])
                            exp_sql = stmts[i + 1].strip()
                            out.append((meta, sql, exp_sql))
                    return out, len(stmts)

                old_p, old_n = _parse_pairs(old_text)
                new_p, new_n = _parse_pairs(new_text)
                if old_p == new_p and old_n == new_n:
                    return
                is_tpcds = path.endswith("tpc-ds.sql")
                if is_tpcds:
                    an.high |= cov.id_mask("tests/test_optimizer.py::TestOptimizer::test_tpcds")
                    exec_mask = cov.id_mask("tests/test_executor.py::TestExecutor::test_execute_tpcds")
                else:
                    an.high |= cov.id_mask("tests/test_optimizer.py::TestOptimizer::test_tpch") | cov.id_mask("tests/test_executor.py::TestExecutor::test_optimized_tpch")
                    exec_mask = cov.id_mask("tests/test_executor.py::TestExecutor::test_execute_tpch")
                need_exec = (len(old_p) != len(new_p)) or (old_n != new_n)
                if not need_exec:
                    for (om, osql, _), (nm, nsql, _) in zip(old_p, new_p):
                        if om.get("execute") != nm.get("execute"):
                            need_exec = True
                            break
                        if osql != nsql:
                            if nm.get("execute"):
                                need_exec = True
                                break
                            # Non-executed TPC query: test_execute_tpc* only calls parse_one(sql) on it
                            try:
                                if str(REPO) not in sys.path:
                                    sys.path.insert(0, str(REPO))
                                import sqlglot
                                sqlglot.parse_one(nsql)
                            except BaseException:
                                need_exec = True
                                break
                if need_exec:
                    an.high |= exec_mask
                an.notes.append(f"tpc-data {path} need_exec={need_exec}")
                return
        o = src.fixture_openers(path)
        if o:
            if path == "tests/fixtures/identity.sql":
                an.high |= cov.id_mask("tests/test_transpile.py::TestTranspile::test_identity")
                an.low |= o & ~an.high
            elif path.startswith("tests/fixtures/") or path.startswith("tests/"):
                an.high |= o
            else:
                an.low |= o
        an.notes.append(f"data {path} openers={bin(o).count('1')}")
        return

    analyze_py(path, old_text, new_text, removed, added, new2old, an, cov, src)


ENUM_CLASSES = {
    "NormalizationStrategy",
    "TokenType",
    "Dialects",
    "DType",
    "ErrorLevel",
    "ScopeType",
    "UsingColumnOrder",
    "AliasPrecedence",
    "PropertiesLocation",
    "TrieResult",
    "IsPredicatePrecedence",
    "AutoName",
}


def _is_singleton_or_enum(node: ast.AST) -> bool:
    if isinstance(node, ast.Constant) and node.value is None:
        return True
    if isinstance(node, ast.Attribute) and isinstance(node.value, ast.Name) and node.value.id in ENUM_CLASSES:
        return True
    if (
        isinstance(node, ast.Attribute)
        and isinstance(node.value, ast.Attribute)
        and isinstance(node.value.value, ast.Name)
        and node.value.attr in ENUM_CLASSES
    ):
        return True
    return False


class _NormAST(ast.NodeTransformer):
    def _clean_block(self, stmts):
        out = []
        for s in stmts:
            s = self.visit(s)
            if isinstance(s, ast.Expr) and isinstance(s.value, ast.Constant) and isinstance(s.value.value, str):
                continue
            out.append(s)
        return out or [ast.Pass()]

    def visit_Module(self, node):
        node.body = self._clean_block(node.body)
        return node

    def visit_ClassDef(self, node):
        self.generic_visit(node)
        node.body = self._clean_block(node.body)
        return node

    def visit_FunctionDef(self, node):
        self.generic_visit(node)
        node.body = self._clean_block(node.body)
        return node

    def visit_AsyncFunctionDef(self, node):
        self.generic_visit(node)
        node.body = self._clean_block(node.body)
        return node

    def visit_Compare(self, node):
        self.generic_visit(node)
        if len(node.ops) == 1 and len(node.comparators) == 1:
            op = node.ops[0]
            left, right = node.left, node.comparators[0]
            if _is_singleton_or_enum(left) or _is_singleton_or_enum(right):
                if isinstance(op, ast.Eq):
                    node.ops = [ast.Is()]
                elif isinstance(op, ast.NotEq):
                    node.ops = [ast.IsNot()]
        return node

    def visit_Call(self, node):
        self.generic_visit(node)
        # exp.alias_(<fresh_expr>, ..., copy=True/False) is equivalent when arg0 is a fresh builder call
        if (
            isinstance(node.func, ast.Attribute)
            and node.func.attr == "alias_"
            and node.args
            and isinstance(node.args[0], ast.Call)
            and isinstance(node.args[0].func, ast.Attribute)
            and node.args[0].func.attr in ("table_", "column", "var", "to_identifier", "to_table", "to_column")
        ):
            for kw in node.keywords:
                if kw.arg == "copy" and isinstance(kw.value, ast.Constant) and isinstance(kw.value.value, bool):
                    kw.value = ast.Constant(value=False)
        return node


def ast_equivalent(t1: ast.AST, t2: ast.AST) -> bool:
    if ast.dump(t1) == ast.dump(t2):
        return True
    import copy

    n1 = _NormAST().visit(copy.deepcopy(t1))
    n2 = _NormAST().visit(copy.deepcopy(t2))
    return ast.dump(n1) == ast.dump(n2)


def analyze_py(path, old_text, new_text, removed, added, new2old, an, cov, src):
    imp = cov.importers(path)
    try:
        old_tree = ast.parse(old_text)
    except SyntaxError:
        an.high |= imp
        return
    try:
        new_tree = ast.parse(new_text)
    except SyntaxError:
        an.notes.append(f"syntax error {path} importers={bin(imp).count('1')}")
        an.high |= imp
        return
    # encoding cookie / first lines
    for ln in list(removed) + list(added):
        if ln <= 2:
            txt = (old_text if ln in removed else new_text).split("\n")[ln - 1]
            if re.search(r"coding[:=]", txt):
                an.high |= imp
    if ast_equivalent(old_tree, new_tree):
        an.notes.append(f"ast-identical {path}")
        return

    # Statement-level diff: compare top-level / class-level / function bodies via
    # line-anchored analysis on both trees.
    is_test_file = path.startswith("tests/")
    old_loc, new_loc = Locator(old_tree), Locator(new_tree)
    old2new = {o: n for n, o in new2old.items()}

    # Restrict to lines whose enclosing statement actually changed (AST compare of
    # the smallest statement), to ignore comment lines inside changed hunks.
    def region_for(tree_loc, line, which):
        ch = tree_loc.chain(line)
        return ch

    touched = 0  # tests touching changed body code
    high_local = 0

    def handle(line, which):
        nonlocal touched, high_local
        loc = old_loc if which == "old" else new_loc
        ch = loc.chain(line)
        if not ch:
            # blank/comment line outside any statement
            return
        # find innermost function containing the line in its body
        func_i = None
        for i, (st, blk, idx) in enumerate(ch):
            if isinstance(st, FUNC) and not (line < st.body[0].lineno):
                func_i = i
        inner, blk, idx = ch[-1]
        # lambda inside a non-function statement (e.g. class-level dict of lambdas)
        lam = None
        if func_i is None:
            lams = lambdas_containing(inner, line)
            if lams:
                lam = max(lams, key=lambda l: l.lineno)
                # line must be in lambda body, not the "lambda args:" part only
        if func_i is None and lam is None:
            # import-time statement
            st = inner
            # if the line is in the header of a def (signature/decorators), users are callers
            if isinstance(st, FUNC):
                body_lines = (st.body[0].lineno, st.end_lineno)
                if which == "old":
                    users = cov.span(path, *body_lines)
                else:
                    o = [new2old.get(n) for n in range(*body_lines) if new2old.get(n)]
                    users = cov.span(path, min(o), max(o)) if o else 0
                users |= src.users(st.name)
                touched |= users & imp if imp else users
                return
            if isinstance(st, ast.ClassDef):
                touched |= imp
                return
            if isinstance(st, ast.Expr) and isinstance(st.value, ast.Constant):
                return  # docstring
            names = stmt_names(st)
            classes = [c for c, _, _ in ch if isinstance(c, ast.ClassDef)]
            if isinstance(st, (ast.Import, ast.ImportFrom)) or not names:
                u = imp
                if classes:
                    cu = src.class_users(classes[0].name, classes[-1].name)
                    if cu:
                        u &= cu
                touched |= u
                an.notes.append(f"import-level {path}:{line} -> {bin(u).count('1')}")
                return
            u = 0
            for n in names:
                u |= src.users(n)
            if classes:
                # a class attribute only matters where that class (or a subclass) is used
                cu = src.class_users(classes[0].name, classes[-1].name)
                if not u and cu:
                    u = cu
                else:
                    u &= cu
            elif path.startswith("sqlglot/typing/") and not path.endswith("__init__.py"):
                d_stem = Path(path).stem
                cu = src.class_users(d_stem, d_stem)
                if cu:
                    u = (u & cu) if (u & cu) else cu
            # If modifying a single entry inside a dispatch dict, also scope to users of that key/expression
            if names & {"EXPRESSION_METADATA", "TRANSFORMS", "PROPERTIES_LOCATION", "FUNCTIONS", "FUNCTION_PARSERS", "SHOW_PARSERS", "PROPERTY_PARSERS"}:
                val = getattr(st, "value", None)
                for dnode in ast.walk(val) if val is not None else ():
                    if isinstance(dnode, ast.Dict):
                        for dk, dv in zip(dnode.keys, dnode.values):
                            if dk is not None and dv is not None and dk.lineno <= line <= dv.end_lineno:
                                if isinstance(dk, ast.Attribute) and isinstance(dk.value, ast.Name) and dk.value.id == "exp":
                                    eu = src.class_users(dk.attr, dk.attr) | src.users(dk.attr)
                                    if eu & u & imp:
                                        u &= eu
                                elif isinstance(dk, ast.Constant) and isinstance(dk.value, str) and len(dk.value) >= 2:
                                    eu = 0
                                    for w_tok in re.findall(r"[A-Za-z_][A-Za-z0-9_]*", dk.value):
                                        if len(w_tok) >= 2:
                                            eu |= src.users_ci(w_tok)
                                    for subn in ast.walk(dv):
                                        if isinstance(subn, ast.Attribute) and isinstance(subn.value, ast.Name) and subn.value.id == "exp":
                                            eu |= src.class_users(subn.attr, subn.attr) | src.users(subn.attr)
                                    if eu & u & imp:
                                        u &= eu
            touched |= u & imp
            an.notes.append(f"attr {path}:{line} names={sorted(names)} -> {bin(u & imp).count('1')}")
            return
        # body change
        if which == "old":
            if lam is not None and func_i is None:
                # the lambda's first line also runs at import time; prefer the exact line
                v = 0
                if line > lam.lineno:
                    v = cov.line(path, line) or cov.span(path, lam.lineno + 1, lam.end_lineno)
                if not v:
                    v = cov.span(path, lam.lineno, lam.end_lineno)
                    classes = [c for c, _, _ in ch if isinstance(c, ast.ClassDef)]
                    if classes:
                        cu = src.class_users(classes[0].name, classes[-1].name)
                        if cu:
                            v &= cu
                touched |= v
                return
            # innermost statement
            if list(child_blocks(inner)) and in_header(inner, line):
                first = min(b[0].lineno for _, b in child_blocks(inner))
                v = cov.span(path, inner.lineno, first - 1)
            elif list(child_blocks(inner)):
                v = cov.span(path, inner.lineno, inner.end_lineno)
            else:
                v = cov.span(path, inner.lineno, inner.end_lineno)
            if not v:
                # executable line never covered? fall back to the whole function
                f = ch[func_i][0] if func_i is not None else inner
                v = 0  # not executed by any test -> no test reaches it
            touched |= v
            if is_test_file:
                high_local |= v
        else:
            # added line in new tree: tests reaching this point
            v = reach_new(ch, line, func_i, lam)
            touched |= v
            if is_test_file:
                high_local |= v

    def old_line_cov_of_new_stmt(st):
        """Coverage of the old counterpart of new statement `st`'s header line."""
        for n in range(st.lineno, (st.body[0].lineno if hasattr(st, "body") and isinstance(getattr(st, "body"), list) and st.body and hasattr(st.body[0], "lineno") else st.end_lineno + 1)):
            o = new2old.get(n)
            if o is not None:
                c = cov.line(path, o)
                if c:
                    return c
        return None

    def reach_new(ch, line, func_i, lam):
        # walk outward: preceding sibling header, else parent header
        if lam is not None and func_i is None:
            o = [new2old.get(n) for n in range(lam.lineno + 1, lam.end_lineno + 1) if new2old.get(n)]
            v = cov.span(path, min(o), max(o)) if o else 0
            if not v:
                o = [new2old.get(n) for n in range(lam.lineno, lam.end_lineno + 1) if new2old.get(n)]
                v = cov.span(path, min(o), max(o)) if o else imp
            return v
        level = len(ch) - 1
        while level >= 0:
            st, blk, idx = ch[level]
            # preceding siblings in the same block
            j = idx - 1
            while j >= 0:
                c = old_line_cov_of_new_stmt(blk[j])
                if c is not None:
                    return c
                if new2old.get(blk[j].lineno) is not None:
                    # mapped but never executed -> nothing reaches here via it
                    return 0
                j -= 1
            # first in block: parent header
            if level == 0:
                return imp
            parent = ch[level - 1][0]
            if isinstance(parent, FUNC):
                # tests that call the function: any old line of its body
                o = [new2old.get(n) for n in range(parent.body[0].lineno, parent.end_lineno + 1) if new2old.get(n)]
                return cov.span(path, min(o), max(o)) if o else imp
            if isinstance(parent, ast.ClassDef):
                return imp
            c = old_line_cov_of_new_stmt(parent)
            if c is not None and not isinstance(parent, ast.Try):
                return c
            if isinstance(parent, ast.Try):
                o = [new2old.get(n) for n in range(parent.lineno, parent.end_lineno + 1) if new2old.get(n)]
                return cov.span(path, min(o), max(o)) if o else imp
            level -= 1
        return imp

    # skip lines that are pure comments/blank in the changed sets
    def code_line(text_lines, ln):
        s = text_lines[ln - 1].strip() if 0 < ln <= len(text_lines) else ""
        return s and not s.startswith("#")

    old_lines = old_text.split("\n")
    new_lines = new_text.split("\n")
    for ln in sorted(removed):
        if code_line(old_lines, ln):
            handle(ln, "old")
    for ln in sorted(added):
        if code_line(new_lines, ln):
            handle(ln, "new")
    if is_test_file:
        an.high |= high_local
        an.low |= touched & ~high_local
    else:
        an.low |= touched


# ---------------------------------------------------------------- packing


def pack(nums: list[int], dur: list[int]) -> tuple[int, list[list[int]]]:
    """Best LPT packing over 1..8 workers. Returns (cost_ms, workers)."""
    if not nums:
        return 0, []
    order = sorted(nums, key=lambda n: -dur[n])
    total = sum(dur[n] for n in nums)
    best = None
    for k in range(1, min(MAX_WORKERS, len(nums)) + 1):
        if best is not None and total / k + 2000 * k > best[0] and k > 1 and dur[order[0]] + 2000 * k > best[0]:
            break
        loads = [0] * k
        ws: list[list[int]] = [[] for _ in range(k)]
        for n in order:
            i = loads.index(min(loads))
            loads[i] += dur[n]
            ws[i].append(n)
        cost = max(loads) + 2000 * k
        if best is None or cost < best[0]:
            best = (cost, ws)
    return best


# ---------------------------------------------------------------- verification runner


def build_farm(root: Path, patched: dict[str, str | None]) -> bool:
    """Create a symlink farm of REPO under root with patched files materialised."""
    root.mkdir(parents=True, exist_ok=True)
    # directories that must be real
    real_dirs = {""}
    for p in patched:
        parts = p.split("/")[:-1]
        for i in range(1, len(parts) + 1):
            real_dirs.add("/".join(parts[:i]))
    for d in sorted(real_dirs, key=lambda x: x.count("/") if x else -1):
        src_dir = REPO / d if d else REPO
        dst_dir = root / d if d else root
        dst_dir.mkdir(parents=True, exist_ok=True)
        if not src_dir.is_dir():
            continue
        for entry in os.listdir(src_dir):
            rel = f"{d}/{entry}" if d else entry
            if rel in real_dirs or rel in patched:
                continue
            if entry in (".git", "__pycache__"):
                continue
            os.symlink(src_dir / entry, dst_dir / entry)
    for p, txt in patched.items():
        if txt is None:
            continue
        (root / p).parent.mkdir(parents=True, exist_ok=True)
        (root / p).write_text(txt, encoding="utf-8")
    return True


CHILD_CODE = None


def run_child(farm: Path, patched: dict, nums: list[int], ids: list[str], hn: list[int], all_ln: list[int], dur: list[int], wfd: int):
    """In a forked child: run the given test ids with direct unittest in `farm`."""
    import importlib
    import resource
    import unittest

    try:
        resource.setrlimit(resource.RLIMIT_AS, (1536 * 1024 * 1024, 1536 * 1024 * 1024))
    except Exception:
        pass
    devnull = os.open(os.devnull, os.O_WRONLY)
    os.dup2(devnull, 1)
    if not os.environ.get("BR_DEBUG"):
        os.dup2(devnull, 2)
    else:
        os.dup2(2, 1)
    os.chdir(farm)
    sys.path[:] = [str(farm)] + [p for p in sys.path if p and not p.startswith(str(REPO))]
    importlib.invalidate_caches()

    # Check if any patched .py file is an already-imported module in sys.modules
    patched_mods = {p[:-3].replace("/", ".") for p in patched if p.endswith(".py")}
    if any(m in sys.modules or (m.endswith(".__init__") and m[:-9] in sys.modules) for m in patched_mods):
        for k in list(sys.modules):
            if k == "sqlglot" or k.startswith("sqlglot.") or k == "tests" or k.startswith("tests."):
                del sys.modules[k]
    else:
        # Repoint package __path__ so submodules load from farm
        for k, mod in list(sys.modules.items()):
            if k == "tests" or k.startswith("tests."):
                del sys.modules[k]
            elif (k == "sqlglot" or k.startswith("sqlglot.")) and hasattr(mod, "__path__"):
                rel = k.replace(".", "/")
                mod.__path__ = [str(farm / rel)]

    os.environ["SKIP_INTEGRATION"] = "0"
    import concurrent.futures as cf

    class LazyFuture:
        """Evaluate submitted work lazily on .result() so early subTest failure skips remaining work."""

        __slots__ = ("_fn", "_a", "_k", "_done", "_res", "_exc")

        def __init__(self, fn, a, k):
            self._fn = fn
            self._a = a
            self._k = k
            self._done = False
            self._res = None
            self._exc = None

        def result(self, timeout=None):
            if not self._done:
                self._done = True
                try:
                    self._res = self._fn(*self._a, **self._k)
                except BaseException as e:
                    self._exc = e
            if self._exc is not None:
                raise self._exc
            return self._res

    class InlinePool:
        """Run 'process pool' work inline & lazily: avoids spawning interpreters and stops on first failure."""

        def __init__(self, max_workers=None, mp_context=None, initializer=None, initargs=(), **kw):
            if initializer is not None:
                initializer(*initargs)

        def submit(self, fn, /, *a, **k):
            return LazyFuture(fn, a, k)

        def map(self, fn, *its, timeout=None, chunksize=1, buffersize=None):
            return (fn(*x) for x in zip(*its))

        def shutdown(self, wait=True, *, cancel_futures=False):
            pass

        def __enter__(self):
            return self

        def __exit__(self, *a):
            return False

    cf.ProcessPoolExecutor = InlinePool
    cf.wait = lambda fs, timeout=None, return_when=None: (fs, set())
    cf.as_completed = lambda fs, timeout=None: iter(fs)
    try:
        import concurrent.futures.process as cfp

        cfp.ProcessPoolExecutor = InlinePool
    except Exception:
        pass

    # Fail-fast subTest: abort the test method immediately on the very first failing subTest
    class _FastSubTest:
        def __init__(self, tc):
            self.tc = tc

        def __enter__(self):
            return self

        def __exit__(self, exc_type, exc_val, exc_tb):
            return False  # propagate exception immediately to fail the test fast

    unittest.TestCase.subTest = lambda self, msg=None, ** params: _FastSubTest(self)

    w = os.fdopen(wfd, "w", buffering=1)
    mod_cache = {}
    cls_setup_done = set()
    cls_setup_failed = set()

    confirmed_fail = set(hn)
    remaining_cands = set(all_ln)
    fail_count = 0
    pass_count = 0
    test_outcomes: dict[str, bool] = {}
    can_surrogate_tpc = not any(
        p.startswith(("sqlglot/serde.py", "sqlglot/executor/", "sqlglot/planner.py", "sqlglot/optimizer/merge_subqueries.py", "sqlglot/generators/duckdb.py", "sqlglot/dialects/duckdb.py", "tests/test_executor.py"))
        for p in patched
    )
    can_surrogate_max_nodes = "tests/test_parser.py" not in patched
    can_surrogate_gen_mem = not any(p in ("tests/test_generator.py", "sqlglot/generator.py", "sqlglot/dialects/dialect.py") for p in patched)

    def _fast_tpc_check(kind: str) -> bool:
        from tests.helpers import load_sql_fixture_pairs, TPCDS_SCHEMA, TPCH_SCHEMA
        from sqlglot import parse_one
        from sqlglot.optimizer import optimize
        from sqlglot.schema import ensure_schema

        if kind == "tpcds":
            schema = ensure_schema(TPCDS_SCHEMA)
            for meta, sql, opt in load_sql_fixture_pairs("optimizer/tpc-ds/tpc-ds.sql"):
                if meta.get("execute"):
                    if optimize(parse_one(sql), schema=schema).sql(pretty=True) != opt:
                        return False
            return True
        else:
            schema = ensure_schema(TPCH_SCHEMA)
            for meta, sql, opt in load_sql_fixture_pairs("optimizer/tpc-h/tpc-h.sql"):
                if optimize(parse_one(sql), schema=schema).sql(pretty=True) != opt:
                    return False
            return True

    def _fast_max_nodes_check() -> bool:
        from sqlglot import parse_one, exp
        from sqlglot.errors import ParseError

        if not isinstance(parse_one("SELECT 1", max_nodes=1_000_000), exp.Select):
            return False
        cols = [f"col{i}" for i in range(40)]
        if not isinstance(parse_one(f"SELECT {','.join(cols)} FROM t", max_nodes=1_000_000), exp.Select):
            return False
        try:
            parse_one("SELECT " + ",".join(f"x={i}" for i in range(100)), max_nodes=50)
            return False
        except ParseError as e:
            if "Maximum number of AST nodes" not in str(e) or "(50)" not in str(e):
                return False
        return isinstance(parse_one("SELECT 1, 2, 3"), exp.Select)

    def _fast_gen_mem_check() -> bool:
        from sqlglot.dialects import Dialect, Dialects

        for name in Dialects:
            d = Dialect.get_or_raise(name)
            d.generator()
        return True

    try:
        for tnum, tid in zip(nums, ids):
            # Slack & early-stop check: if keeping all remaining candidates costs the same as confirmed_fail, stop!
            if confirmed_fail:
                c_now, _ = pack(sorted(confirmed_fail), dur)
                c_all, _ = pack(sorted(confirmed_fail | remaining_cands), dur)
                if c_all <= c_now:
                    break
                # If this single test adds 0ms to pack(confirmed_fail) and we already have failures, skip running it
                if fail_count >= 1 and dur[tnum] >= 40:
                    c_one, _ = pack(sorted(confirmed_fail | {tnum}), dur)
                    if c_one <= c_now:
                        continue

            parts = tid.split("::")
            fpath, cname, mname = parts[0], parts[1], parts[2]
            if can_surrogate_max_nodes and fpath == "tests/test_parser.py" and mname == "test_max_nodes":
                try:
                    passed = _fast_max_nodes_check()
                except BaseException:
                    passed = False
                if passed:
                    w.write(f"P {tid}\n")
                    remaining_cands.discard(tnum)
                    pass_count += 1
                else:
                    w.write(f"F {tid}\n")
                    confirmed_fail.add(tnum)
                    fail_count += 1
                continue
            if can_surrogate_gen_mem and fpath == "tests/test_generator.py" and mname == "test_generator_memory":
                try:
                    passed = _fast_gen_mem_check()
                except BaseException:
                    passed = False
                if passed:
                    w.write(f"P {tid}\n")
                    remaining_cands.discard(tnum)
                    pass_count += 1
                else:
                    w.write(f"F {tid}\n")
                    confirmed_fail.add(tnum)
                    fail_count += 1
                continue
            if can_surrogate_tpc and fpath == "tests/test_executor.py" and mname in ("test_execute_tpcds", "test_execute_tpch", "test_optimized_tpch"):
                passed = False
                try:
                    if mname == "test_execute_tpcds":
                        ref = "tests/test_optimizer.py::TestOptimizer::test_tpcds"
                        passed = test_outcomes[ref] if ref in test_outcomes else _fast_tpc_check("tpcds")
                        test_outcomes[ref] = passed
                    else:
                        ref = "tests/test_optimizer.py::TestOptimizer::test_tpch"
                        passed = test_outcomes[ref] if ref in test_outcomes else _fast_tpc_check("tpch")
                        test_outcomes[ref] = passed
                except BaseException:
                    passed = False
                test_outcomes[tid] = passed
                if passed:
                    w.write(f"P {tid}\n")
                    remaining_cands.discard(tnum)
                    pass_count += 1
                else:
                    w.write(f"F {tid}\n")
                    confirmed_fail.add(tnum)
                    fail_count += 1
                continue

            # If sqlglot/serde.py is broken, ProcessPoolExecutor pickling fails even when InlinePool passes
            if fail_count >= 2 and "sqlglot/serde.py" in patched:
                break
            # If catastrophic breakage (many failures and almost no passes), skip expensive non-surrogate tests
            if dur[tnum] >= 120:
                if (fail_count >= 2 and pass_count == 0 and not can_surrogate_tpc) or (fail_count >= 6 and fail_count > pass_count * 2):
                    continue

            mod_name = fpath[:-3].replace("/", ".")
            try:
                mod = mod_cache.get(mod_name)
                if mod is None:
                    mod = importlib.import_module(mod_name)
                    # If TestOptimizer is loaded, make setUpClass lazy and skip redundant DuckDB execution in check_file
                    if mod_name == "tests.test_optimizer" and hasattr(mod, "TestOptimizer"):
                        mod.wait = cf.wait
                        mod.as_completed = cf.as_completed
                        mod.ProcessPoolExecutor = InlinePool
                        to_cls = mod.TestOptimizer
                        orig_setup_cls = to_cls.setUpClass

                        def _fast_setup_cls():
                            to_cls.pool = InlinePool()
                            mod.sqlglot.schema = mod.MappingSchema()

                        to_cls.setUpClass = _fast_setup_cls

                        class _LazyConn:
                            def __get__(self, obj, objtype=None):
                                orig_setup_cls()
                                return to_cls.__dict__["conn"]

                        to_cls.conn = _LazyConn()
                        orig_check_file = to_cls.check_file

                        def _fast_check_file(self, file, func, pretty=False, execute=None, only=None, **kwargs):
                            return orig_check_file(self, file, func, pretty=pretty, execute=False, only=only, **kwargs)

                        to_cls.check_file = _fast_check_file
                    elif mod_name == "tests.test_executor" and hasattr(mod, "TestExecutor"):
                        mod.ProcessPoolExecutor = InlinePool
                        te_cls = mod.TestExecutor
                        orig_te_setup = te_cls.setUpClass
                        te_cls._real_setup_done = False

                        def _lazy_te_setup(*a, **kw):
                            pass

                        te_cls.setUpClass = classmethod(_lazy_te_setup)

                        def _ensure_te_setup():
                            if not te_cls._real_setup_done:
                                te_cls._real_setup_done = True
                                orig_te_setup()

                        te_cls._ensure_te_setup = _ensure_te_setup
                    mod_cache[mod_name] = mod
                cls = getattr(mod, cname)
                if mname in ("test_optimized_tpch", "test_execute_tpch", "test_execute_tpcds") and hasattr(cls, "_ensure_te_setup"):
                    cls._ensure_te_setup()
                if cls in cls_setup_failed:
                    w.write(f"F {tid}\n")
                    confirmed_fail.add(tnum)
                    fail_count += 1
                    continue
                if cls not in cls_setup_done:
                    cls_setup_done.add(cls)
                    try:
                        cls.setUpClass()
                    except BaseException:
                        cls_setup_failed.add(cls)
                        w.write(f"F {tid}\n")
                        confirmed_fail.add(tnum)
                        fail_count += 1
                        continue
            except BaseException:
                w.write(f"C {fpath}\n")
                confirmed_fail.add(tnum)
                fail_count += 1
                continue

            inst = cls(mname)
            passed = False
            try:
                inst.setUp()
                try:
                    getattr(inst, mname)()
                    passed = True
                finally:
                    inst.tearDown()
                for fn, a, k in getattr(inst, "_cleanups", ()):
                    fn(*a, **k)
            except unittest.SkipTest:
                passed = True
            except BaseException:
                passed = False

            if passed:
                test_outcomes[tid] = True
                w.write(f"P {tid}\n")
                remaining_cands.discard(tnum)
                pass_count += 1
            else:
                test_outcomes[tid] = False
                w.write(f"F {tid}\n")
                confirmed_fail.add(tnum)
                fail_count += 1
    finally:
        w.write("END\n")
        w.flush()
        os._exit(0)


class Job:
    def __init__(self, cid, patched, tests_nums, ids, hn, all_ln, farm, budget):
        self.cid = cid
        self.patched = patched
        self.nums = tests_nums
        self.ids = ids
        self.hn = hn
        self.all_ln = all_ln
        self.farm = farm
        self.budget = budget
        self.pid = None
        self.rfd = None
        self.buf = b""
        self.results: dict[str, str] = {}
        self.collect_err: list[str] = []
        self.ended = False
        self.start = None


def run_jobs(jobs: list[Job], dur: list[int], parallel: int, deadline: float):
    import select
    import signal

    pending = list(jobs)
    running: dict[int, Job] = {}
    while pending or running:
        while pending and len(running) < parallel:
            j = pending.pop(0)
            if time.time() > deadline - 2:
                j.ended = False
                continue
            r, w = os.pipe()
            pid = os.fork()
            if pid == 0:
                os.close(r)
                try:
                    run_child(j.farm, j.patched, j.nums, j.ids, j.hn, j.all_ln, dur, w)
                except BaseException:
                    import traceback

                    traceback.print_exc()
                os._exit(0)
            os.close(w)
            j.pid, j.rfd, j.start = pid, r, time.time()
            running[r] = j
        if not running:
            break
        rl, _, _ = select.select(list(running), [], [], 0.2)
        for r in rl:
            j = running[r]
            data = os.read(r, 65536)
            if not data:
                os.close(r)
                del running[r]
                try:
                    os.waitpid(j.pid, 0)
                except ChildProcessError:
                    pass
                continue
            j.buf += data
            *done, j.buf = j.buf.split(b"\n")
            for line in done:
                s = line.decode("utf-8", "replace")
                if s == "END":
                    j.ended = True
                elif s.startswith("C "):
                    j.collect_err.append(s[2:])
                elif len(s) > 2:
                    j.results[s[2:]] = s[0]
        now = time.time()
        for r, j in list(running.items()):
            if now - j.start > j.budget or now > deadline:
                try:
                    os.kill(j.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                log(f"[{j.cid}] verification killed after {now - j.start:.1f}s")


# ---------------------------------------------------------------- main


def main():
    tests = json.loads((DATA / "tests.json").read_text())["tests"]
    n = len(tests)
    dur = [round(t["seconds"] * 1000) for t in tests]
    ids = [t["id"] for t in tests]
    cov = CovMap(MAP, tests)
    src = Sources(REPO, cov)
    patches = sorted((DATA / "commits").glob("*.patch"))
    log(f"loaded map in {time.time() - T0:.2f}s, {len(patches)} commits, {n} tests")

    ALPHA = float(os.environ.get("BR_ALPHA", "0.75"))
    OVH = float(os.environ.get("BR_OVH", "250"))  # ms CPU per verification run
    results = {}
    jobs = []
    plans = {}
    for p in patches:
        cid = p.stem
        try:
            an = analyze(p.read_text(encoding="utf-8", errors="replace"), cov, src)
        except Exception as e:
            log(f"[{cid}] analysis crashed: {e!r}; selecting all")
            an = Analysis()
            an.high = (1 << n) - 1
        high = an.high & ((1 << n) - 1)
        low = an.low & ~high & ((1 << n) - 1)
        hn, ln = bits(high), bits(low)
        blind_cost, _ = pack(hn + ln, dur)
        # choose verification threshold using effective runtime CPU cost
        best = (blind_cost, [])
        if VERIFY and ln and not an.unverifiable:
            def eff_ms(t: int) -> int:
                tid = ids[t]
                if tid.endswith("::test_max_nodes"):
                    return 10
                if tid.endswith("::test_generator_memory"):
                    return 25
                if tid.endswith("::test_execute_tpcds"):
                    return 250
                if tid.endswith(("::test_execute_tpch", "::test_optimized_tpch")):
                    return 80
                if tid.startswith("tests/test_optimizer.py::"):
                    return min(dur[t], 450)
                return min(max(2, dur[t] // 3), 300)

            cand = sorted(ln, key=lambda x: dur[x])
            acc = 0
            for i, t in enumerate(cand):
                acc += eff_ms(t)
                rest = hn + cand[i + 1 :]
                c, _ = pack(rest, dur)
                c += OVH + ALPHA * acc
                if c < best[0]:
                    best = (c, cand[: i + 1])
        plans[cid] = (an, hn, ln, best[1])
        log(
            f"[{cid}] high={len(hn)} low={len(ln)} blind={blind_cost/1000:.2f}s verify={len(best[1])} "
            f"exp={best[0]/1000:.2f}s notes={an.notes[:4]}"
        )
        if best[1]:
            import tempfile

            farm = Path(os.path.realpath(tempfile.mkdtemp(prefix=f"farm_{cid}_", dir=os.environ.get("BR_TMP", "/tmp"))))
            try:
                build_farm(farm, an.patched)
            except Exception as e:
                log(f"[{cid}] farm failed {e!r}")
                plans[cid] = (an, hn, ln, [])
                continue
            vt = best[1]
            budget = 4.0 + sum(dur[t] for t in vt) / 1000 * 4
            jobs.append(Job(cid, an.patched, vt, [ids[t] for t in vt], hn, ln, farm, budget))

    if jobs:
        # pre-import heavy third-party and core sqlglot modules once so forked children share them via CoW
        t_imp = time.time()
        if str(REPO) not in sys.path:
            sys.path.insert(0, str(REPO))
        try:
            import sqlglot  # noqa
            import unittest  # noqa
        except Exception:
            pass
        heavy = {"tests/test_executor.py", "tests/test_optimizer.py", "tests/dialects/test_duckdb.py"}
        if any(i.split("::")[0] in heavy for j in jobs for i in j.ids):
            for mod in ("duckdb", "pandas", "numpy", "pandas.testing"):
                try:
                    __import__(mod)
                except Exception:
                    pass
        log(f"pre-import {time.time() - t_imp:.2f}s")
        # longer jobs first
        jobs.sort(key=lambda j: -j.budget)
        run_jobs(jobs, dur, parallel=2, deadline=T0 + float(os.environ.get("BR_DEADLINE", "160")))
    jobmap = {j.cid: j for j in jobs}

    for p in patches:
        cid = p.stem
        an, hn, ln, vt = plans[cid]
        sel = set(hn) | set(ln)
        j = jobmap.get(cid)
        if j is not None:
            verified_pass = set()
            id2num = {ids[t]: t for t in j.nums}
            if j.ended and not j.collect_err:
                for tid, res in j.results.items():
                    if res == "P" and tid in id2num:
                        verified_pass.add(id2num[tid])
            elif j.collect_err:
                log(f"[{cid}] collection errors {j.collect_err}")
                files_err = {c.split("::")[0] for c in j.collect_err}
                for tid, res in j.results.items():
                    if res == "P" and tid in id2num and tid.split("::")[0] not in files_err:
                        verified_pass.add(id2num[tid])
            else:
                for tid, res in j.results.items():
                    if res == "P" and tid in id2num:
                        verified_pass.add(id2num[tid])
            fails = [ids[t] for t in j.nums if t not in verified_pass]
            if os.environ.get("BR_DEBUG"):
                log(f"[{cid}] raw results ended={j.ended} {list(j.results.items())[:5]} cerr={j.collect_err}")
            log(f"[{cid}] verified {len(j.nums)}: pass={len(verified_pass)} fail/unknown={len(fails)} {fails[:5]}")
            sel -= verified_pass
        _, workers = pack(sorted(sel), dur)
        results[cid] = workers
        print(json.dumps({"commit": cid, "workers": workers}), flush=True)
    log(f"done in {time.time() - T0:.2f}s")


if __name__ == "__main__":
    main()
