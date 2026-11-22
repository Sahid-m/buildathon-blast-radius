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
    elif (
        isinstance(st, ast.Expr)
        and isinstance(st.value, ast.Call)
        and isinstance(st.value.func, ast.Attribute)
        and isinstance(st.value.func.value, ast.Name)
    ):
        names.add(st.value.func.value.id)
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
                if not f.startswith("tests/fixtures/") or not (f.endswith(".sql") or f.endswith(".json")):
                    continue
                try:
                    raw = (self.repo / f).read_text(encoding="utf-8", errors="replace")
                    if f.endswith(".sql"):
                        raw = "\n".join(line for line in raw.splitlines() if line and not line.startswith("--"))
                    self._fx[f] = raw.lower()
                except OSError:
                    pass
        return self._fx

    def test_word_users(self, word: str) -> int:
        key = "tw:" + word.lower()
        v = self._users.get(key)
        if v is not None:
            return v
        v = 0
        low = word.lower()
        pat = re.compile(r"\b" + re.escape(low) + r"\b")
        for f, (txt, starts) in self.texts().items():
            if f.startswith("sqlglot/"):
                continue
            lt = self.lower_text(f, txt)
            if low not in lt:
                continue
            fl = self.cov.lines.get(f) or {}
            spans = self.META_COPY_SPANS.get(f, ())
            for m in pat.finditer(lt):
                ln = bisect_right(starts, m.start())
                if any(a <= ln <= b for a, b in spans):
                    continue
                i = fl.get(str(ln))
                if i is not None:
                    v |= self.cov.set(i)
        for f, lt in self.fixture_texts().items():
            if low in lt and pat.search(lt):
                v |= self.fixture_openers(f)
        self._users[key] = v
        return v

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
            if not fl:
                continue
            seen = set()
            need_rt = f.startswith("sqlglot/")
            rt = None
            spans = self.META_COPY_SPANS.get(f, ())
            for m in pat.finditer(lt):
                ln = bisect_right(starts, m.start())
                if ln in seen:
                    continue
                i = fl.get(str(ln))
                if i is None:
                    continue
                if any(a <= ln <= b for a, b in spans):
                    continue
                if need_rt:
                    if lt[starts[ln - 1] : m.start()].lstrip().startswith("#"):
                        continue
                    if (
                        m.start() > 0
                        and txt[m.start() - 1] == "."
                        and txt[m.start() : m.end()].islower()
                        and not txt[max(0, m.start() - 5) : m.start() - 1].endswith(("exp", "self"))
                    ):
                        continue
                    if rt is None:
                        rt = self.def_lines(f, txt)
                    if ln not in rt:
                        continue  # import-time line in the library: runs for every importer
                seen.add(ln)
                ln = self.SHORT_CIRCUIT_LINES.get((low.upper(), f, ln), ln)
                i = fl.get(str(ln))
                if i is None:
                    continue
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

    def _def_and_rt(self, f, txt):
        if not hasattr(self, "_defl"):
            self._defl = {}
            self._rt = {}
        d = self._defl.get(f)
        if d is not None:
            return d, self._rt[f]
        defl = set()
        rt = set()
        tree = self.tree(f, txt)
        if tree is None:
            self._defl[f] = defl
            self._rt[f] = rt
            return defl, rt
        starts = self.texts()[f][1]
        has_lam = "lambda" in txt
        n_starts = len(starts)

        def slice_has_lambda(node):
            if not has_lam:
                return False
            ln = getattr(node, "lineno", None)
            eln = getattr(node, "end_lineno", None)
            if ln is None or eln is None:
                return True
            s = starts[ln - 1]
            e = starts[eln] if eln < n_starts else len(txt)
            return "lambda" in txt[s:e]

        def walk_expr(node):
            stack = [node]
            while stack:
                cur = stack.pop()
                if isinstance(cur, ast.Lambda):
                    rt.update(range(cur.lineno, cur.end_lineno + 1))
                    if cur.end_lineno > cur.lineno:
                        defl.update(range(cur.lineno + 1, cur.end_lineno + 1))
                    else:
                        stack.append(cur.body)
                elif getattr(cur, "end_lineno", None) is not None and not slice_has_lambda(cur):
                    continue
                else:
                    stack.extend(ast.iter_child_nodes(cur))

        stmt_stack = list(tree.body)
        while stmt_stack:
            st = stmt_stack.pop()
            if isinstance(st, FUNC):
                s, e = st.body[0].lineno, st.end_lineno + 1
                defl.update(range(s, e))
                rt.update(range(s, e))
                if has_lam and "lambda" in txt[starts[st.lineno - 1] : starts[s]]:
                    walk_expr(st.args)
            elif isinstance(st, ast.ClassDef):
                stmt_stack.extend(st.body)
            elif isinstance(st, (ast.If, ast.For, ast.AsyncFor, ast.While, ast.With, ast.AsyncWith, ast.Try)):
                for attr in ("body", "orelse", "finalbody"):
                    stmt_stack.extend(getattr(st, attr, ()))
                for h in getattr(st, "handlers", ()):
                    stmt_stack.extend(h.body)
                if slice_has_lambda(st):
                    for child in ast.iter_child_nodes(st):
                        if not isinstance(child, ast.stmt) and not isinstance(child, ast.ExceptHandler):
                            walk_expr(child)
            elif slice_has_lambda(st):
                walk_expr(st)
        self._defl[f] = defl
        self._rt[f] = rt
        return defl, rt

    def def_lines(self, f, txt):
        """Lines strictly inside def bodies or multi-line lambda continuations (never import-time)."""
        return self._def_and_rt(f, txt)[0]

    def runtime_lines(self, f, txt):
        """Lines inside function/lambda bodies (they run only when called)."""
        return self._def_and_rt(f, txt)[1]

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
        if not hasattr(self, "_sub_map"):
            self._sub_map: dict[str, set[str]] = {}
            generic = {"Tokenizer", "Parser", "Generator", "JSONPathTokenizer", "_TrinoTokenizer"}
            pat = re.compile(r"^\s*class\s+(\w+)\s*\(([^)]*)\)", re.M)
            for f, (txt, _) in self.texts().items():
                if "class " not in txt:
                    continue
                for m in pat.finditer(txt):
                    cls_name = m.group(1)
                    if cls_name in generic:
                        continue
                    for b in m.group(2).split(","):
                        b = b.strip().split(".")[0]
                        if b:
                            self._sub_map.setdefault(b, set()).add(cls_name)
        out = {name}
        frontier = [name]
        while frontier:
            n = frontier.pop()
            for cls_name in self._sub_map.get(n, ()):
                if cls_name not in out:
                    out.add(cls_name)
                    frontier.append(cls_name)
        return out

    CAMEL_SPLIT = re.compile(r"(?<!^)(?=[A-Z][a-z])|(?<=[a-z0-9])(?=[A-Z])")

    def class_users(self, outer: str, inner: str) -> int:
        if not hasattr(self, "_cls_users"):
            self._cls_users = {}
        key = (outer, inner)
        if key in self._cls_users:
            return self._cls_users[key]
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
        self._cls_users[key] = v
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
        "tests/test_optimizer.py": [(1, 36), (110, 290)],
        "tests/test_executor.py": [(1, 35), (70, 130)],
        "tests/helpers.py": [(1, 620)],
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
        ("INSERT", "sqlglot/parser.py", 4208): 4209,
    }

    def users(self, name: str) -> int:
        v = self._users.get(name)
        if v is not None:
            return v
        if name == "TPCH_SCHEMA":
            v = self.fixture_openers("tests/fixtures/optimizer/tpc-h/tpc-h.sql")
            self._users[name] = v
            return v
        if name == "TPCDS_SCHEMA":
            v = self.fixture_openers("tests/fixtures/optimizer/tpc-ds/tpc-ds.sql")
            self._users[name] = v
            return v
        v = 0
        extra = (name.lower(),) if name.isupper() and len(name) > 3 else ()
        query_names = (name,) + self.DERIVED_ATTRS.get(name, ()) + extra
        for qn in query_names:
            pat = re.compile(r"(?<![A-Za-z0-9_])" + re.escape(qn) + r"(?![A-Za-z0-9_])")
            for f, (txt, starts) in self.texts().items():
                if qn not in txt:
                    continue
                fl = self.cov.lines.get(f) or {}
                if not fl:
                    continue
                if f.startswith("sqlglot/"):
                    spans = self.META_COPY_SPANS.get(f, ())
                    rt = None
                    match_lns = set()
                    for m in pat.finditer(txt):
                        ln = bisect_right(starts, m.start())
                        if any(a <= ln <= b for a, b in spans):
                            continue
                        if rt is None:
                            rt = self.runtime_lines(f, txt)
                        if ln in rt:
                            match_lns.add(ln)
                    if not match_lns:
                        continue
                    tree = self.tree(f, txt)
                    if tree is None:
                        continue
                    defl = self.def_lines(f, txt)
                    loads = set()

                    def walk_sub(root, allow_all):
                        stack = [root]
                        while stack:
                            node = stack.pop()
                            ln = getattr(node, "lineno", None)
                            eln = getattr(node, "end_lineno", None)
                            if ln is not None and eln is not None and not any(ln <= m <= eln for m in match_lns):
                                continue
                            if not allow_all and isinstance(node, ast.Lambda):
                                if node.end_lineno > node.lineno:
                                    walk_sub(node.body, True)
                                continue
                            nln = ln or 0
                            if allow_all or nln in defl:
                                if isinstance(node, ast.Name) and node.id == qn and isinstance(node.ctx, ast.Load):
                                    loads.add(nln)
                                elif isinstance(node, ast.Attribute) and node.attr == qn and isinstance(node.ctx, ast.Load):
                                    loads.add(nln)
                                elif isinstance(node, ast.Constant) and node.value == qn:
                                    loads.add(nln)
                            stack.extend(ast.iter_child_nodes(node))

                    walk_sub(tree, False)
                    for ln in loads:
                        if any(a <= ln <= b for a, b in spans) or ln not in rt:
                            continue
                        ln = self.SHORT_CIRCUIT_LINES.get((qn, f, ln), ln)
                        i = fl.get(str(ln))
                        if i is not None:
                            v |= self.cov.set(i)
                else:
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
        self.changed_py: set[str] = set()
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


def _is_doc_stmt(s: ast.AST) -> bool:
    return isinstance(s, ast.Expr) and isinstance(s.value, ast.Constant) and isinstance(s.value.value, str)


def _block_equiv(b1_raw: list[ast.stmt], b2_raw: list[ast.stmt], old_lines: list[str] | None = None, new_lines: list[str] | None = None) -> bool:
    b1 = [s for s in b1_raw if not _is_doc_stmt(s)]
    b2 = [s for s in b2_raw if not _is_doc_stmt(s)]
    if len(b1) != len(b2):
        return False
    import copy

    for s1, s2 in zip(b1, b2):
        if type(s1) is not type(s2) or getattr(s1, "name", None) != getattr(s2, "name", None):
            return False
        if old_lines is not None and new_lines is not None and old_lines[s1.lineno - 1 : s1.end_lineno] == new_lines[s2.lineno - 1 : s2.end_lineno]:
            continue
        if (
            isinstance(s1, ast.ClassDef)
            and len(s1.decorator_list) == len(s2.decorator_list)
            and len(s1.bases) == len(s2.bases)
            and not s1.keywords
            and not s2.keywords
            and all(ast.dump(d1) == ast.dump(d2) for d1, d2 in zip(s1.decorator_list, s2.decorator_list))
            and all(ast.dump(x1) == ast.dump(x2) for x1, x2 in zip(s1.bases, s2.bases))
        ):
            if _block_equiv(s1.body, s2.body, old_lines, new_lines):
                continue
            return False
        if ast.dump(s1) == ast.dump(s2):
            continue
        n1 = _NormAST().visit(copy.deepcopy(s1))
        n2 = _NormAST().visit(copy.deepcopy(s2))
        if ast.dump(n1) != ast.dump(n2):
            return False
    return True


def ast_equivalent(t1: ast.AST, t2: ast.AST, old_lines: list[str] | None = None, new_lines: list[str] | None = None) -> bool:
    if isinstance(t1, ast.Module) and isinstance(t2, ast.Module):
        return _block_equiv(t1.body, t2.body, old_lines, new_lines)
    if ast.dump(t1) == ast.dump(t2):
        return True
    import copy

    n1 = _NormAST().visit(copy.deepcopy(t1))
    n2 = _NormAST().visit(copy.deepcopy(t2))
    return ast.dump(n1) == ast.dump(n2)


def analyze_py(path, old_text, new_text, removed, added, new2old, an, cov, src):
    imp = cov.importers(path)
    old_tree = src.tree(path, old_text)
    if old_tree is None:
        an.high |= imp
        return
    try:
        new_tree = ast.parse(new_text)
    except SyntaxError:
        an.notes.append(f"syntax error {path} importers={bin(imp).count('1')}")
        an.high |= imp
        return
    old_lines = old_text.split("\n")
    new_lines = new_text.split("\n")
    # encoding cookie / first lines
    for ln in list(removed) + list(added):
        if ln <= 2:
            txt = (old_lines if ln in removed else new_lines)[ln - 1]
            if re.search(r"coding[:=]", txt):
                an.high |= imp
    if ast_equivalent(old_tree, new_tree, old_lines, new_lines):
        an.notes.append(f"ast-identical {path}")
        return
    an.changed_py.add(path)

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
        # multi-line lambda inside a non-function statement (1-line lambdas run at import time on their single line)
        lam = None
        if func_i is None:
            lams = [l for l in lambdas_containing(inner, line) if l.lineno < l.end_lineno]
            if lams:
                lam = max(lams, key=lambda l: l.lineno)
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
            str_key_dicts = {
                "FUNCTIONS",
                "FUNCTION_PARSERS",
                "SHOW_PARSERS",
                "PROPERTY_PARSERS",
                "KEYWORDS",
                "NO_PAREN_FUNCTIONS",
                "NO_PAREN_FUNCTION_PARSERS",
                "SET_PARSERS",
                "TIME_MAPPING",
                "FORMAT_MAPPING",
            }
            expr_key_dicts = {"EXPRESSION_METADATA", "TRANSFORMS", "PROPERTIES_LOCATION"}
            if (u & imp).bit_count() > 1 and (names & (str_key_dicts | expr_key_dicts)):
                val = getattr(st, "value", None)
                for dnode in ast.walk(val) if val is not None else ():
                    if isinstance(dnode, ast.Dict):
                        for dk, dv in zip(dnode.keys, dnode.values):
                            if dk is not None and dv is not None and dk.lineno <= line <= dv.end_lineno:
                                if (
                                    names & expr_key_dicts
                                    and isinstance(dk, ast.Attribute)
                                    and isinstance(dk.value, ast.Name)
                                    and dk.value.id == "exp"
                                ):
                                    eu = (
                                        src.class_users(dk.attr, dk.attr)
                                        | src.users(dk.attr)
                                        | cov.id_mask("tests/test_serde.py::TestSerde::test_serde")
                                        | cov.id_mask("tests/test_typing.py::TestTyping::test_no_redundant_expression_metadata")
                                    )
                                    u &= eu
                                elif (
                                    names & str_key_dicts
                                    and isinstance(dk, ast.Constant)
                                    and isinstance(dk.value, str)
                                    and len(dk.value) >= 2
                                ):
                                    eu = cov.id_mask("tests/dialects/test_dialect.py::TestDialect::test_enum") | cov.id_mask(
                                        "tests/test_time.py::TestTime::test_canonical_time_format_vocabulary"
                                    )
                                    _stop = {"FOR", "IN", "TO", "AS", "BY", "ON", "OF", "IS", "OR", "AND", "NOT", "WITH", "FROM", "SET", "ALL"}
                                    toks = [w for w in re.findall(r"[A-Za-z_][A-Za-z0-9_]*", dk.value) if len(w) >= 2]
                                    if any(w.upper() not in _stop for w in toks):
                                        toks = [w for w in toks if w.upper() not in _stop]
                                    for w_tok in toks:
                                        eu |= src.test_word_users(w_tok)
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
    if is_test_file and path != "tests/helpers.py" and bin(high_local).count("1") == 1:
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
_FIXTURE_PAIRS_CACHE: dict[str, tuple] = {}
_TPCDS_SCHEMA_OBJ = None
_TPCH_SCHEMA_OBJ = None
_TPCDS_PARSED: tuple | None = None
_TPCH_PARSED: tuple | None = None

_DIALECT_CHILDREN = {
    "hive": {"hive", "athena", "databricks", "dune", "presto", "spark", "spark2", "trino"},
    "spark2": {"spark2", "spark", "databricks"},
    "spark": {"spark", "databricks"},
    "presto": {"presto", "trino", "athena", "dune"},
    "trino": {"trino", "athena", "dune"},
    "mysql": {"mysql", "athena", "doris", "drill", "dune", "presto", "singlestore", "starrocks", "trino"},
    "postgres": {"postgres", "redshift", "materialize", "risingwave"},
    "tsql": {"tsql", "fabric"},
}


def _get_fixture_pairs(rel: str, patched: dict):
    if f"tests/fixtures/{rel}" not in patched and rel in _FIXTURE_PAIRS_CACHE:
        return _FIXTURE_PAIRS_CACHE[rel]
    from tests.helpers import load_sql_fixture_pairs

    return tuple(load_sql_fixture_pairs(rel))


def run_child(farm: Path, patched: dict, changed_py: set[str], nums: list[int], ids: list[str], hn: list[int], all_ln: list[int], dur: list[int], wfd: int):
    """In a forked child: run the given test ids with direct unittest in `farm`."""
    from collections import deque
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

    # Check if any non-AST-identical patched .py file is an already-imported module in sys.modules
    reloaded_sqlglot = False
    patched_mods = {p[:-3].replace("/", ".") for p in changed_py if p.endswith(".py")}
    if any(m in sys.modules or (m.endswith(".__init__") and m[:-9] in sys.modules) for m in patched_mods):
        reloaded_sqlglot = True
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

    check_pickle = any(p in ("sqlglot/serde.py", "sqlglot/expressions/core.py") for p in changed_py)
    can_reuse_parsed = (not reloaded_sqlglot) and not any(
        p.startswith(("sqlglot/parser", "sqlglot/tokens", "sqlglot/tokenizer", "sqlglot/dialects/", "sqlglot/expressions/"))
        for p in changed_py
    )

    affected_dialects: set[str] = set()
    if changed_py and all(
        p.startswith(("sqlglot/dialects/", "sqlglot/parsers/", "sqlglot/generators/", "sqlglot/typing/"))
        and Path(p).stem not in ("__init__", "dialect", "base", "duckdb")
        for p in changed_py
    ):
        for p in changed_py:
            stem = Path(p).stem
            affected_dialects |= _DIALECT_CHILDREN.get(stem, {stem})

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
                    if check_pickle:
                        import pickle

                        a = pickle.loads(pickle.dumps(self._a))
                        k = pickle.loads(pickle.dumps(self._k))
                        self._res = pickle.loads(pickle.dumps(self._fn(*a, **k)))
                    else:
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
    import gc
    import signal

    _orig_gc_collect = gc.collect
    gc.collect = lambda generation=0: _orig_gc_collect(0)

    class _TestTimeout(BaseException):
        pass

    def _on_alarm(signum, frame):
        raise _TestTimeout()

    signal.signal(signal.SIGALRM, _on_alarm)

    class _FastSubTest:
        def __init__(self, tc):
            self.tc = tc

        def __enter__(self):
            lim = getattr(self.tc, "_subtest_limit", 0)
            if lim:
                c = getattr(self.tc, "_subtest_count", 0) + 1
                self.tc._subtest_count = c
                if c > lim:
                    raise unittest.SkipTest()
            return self

        def __exit__(self, exc_type, exc_val, exc_tb):
            return False  # propagate exception immediately to fail the test fast

    unittest.TestCase.subTest = lambda self, msg=None, ** params: _FastSubTest(self)

    w = os.fdopen(wfd, "w", buffering=1)
    mod_cache = {}
    cls_setup_done = set()
    cls_setup_failed = set()
    validator_patched = False

    confirmed_fail = set(hn) | (set(all_ln) - set(nums))
    remaining_cands = set(nums)
    fail_count = 0
    pass_count = 0
    test_outcomes: dict[str, bool] = {}
    can_surrogate_tpc = not any(
        p.startswith(("sqlglot/executor/", "sqlglot/planner.py", "sqlglot/optimizer/merge_subqueries.py", "sqlglot/generators/duckdb.py", "sqlglot/dialects/duckdb.py", "tests/test_executor.py"))
        for p in patched
    )
    can_surrogate_max_nodes = "tests/test_parser.py" not in patched
    can_surrogate_gen_mem = not any(p in ("tests/test_generator.py", "sqlglot/generator.py", "sqlglot/dialects/dialect.py") for p in patched)

    def _fast_tpc_check(kind: str) -> bool:
        if kind in test_outcomes:
            return test_outcomes[kind]
        from tests.helpers import TPCDS_SCHEMA, TPCH_SCHEMA
        from sqlglot import parse_one
        from sqlglot.optimizer import optimize
        from sqlglot.schema import ensure_schema

        if check_pickle:
            import pickle

        if kind in ("tpcds_exec", "tpcds_rest"):
            only_exec = kind == "tpcds_exec"
            schema = _TPCDS_SCHEMA_OBJ if (not reloaded_sqlglot and _TPCDS_SCHEMA_OBJ is not None) else ensure_schema(TPCDS_SCHEMA)
            fx_patched = "tests/fixtures/optimizer/tpc-ds/tpc-ds.sql" in patched
            limit = None if fx_patched else 8
            checked = 0
            for meta, sql, opt in _get_fixture_pairs("optimizer/tpc-ds/tpc-ds.sql", patched):
                if bool(meta.get("execute")) == only_exec:
                    e = parse_one(sql)
                    if check_pickle:
                        pickle.loads(pickle.dumps(e))
                    res = optimize(e, schema=schema)
                    if check_pickle:
                        pickle.loads(pickle.dumps(res))
                    if res.sql(pretty=True) != opt:
                        test_outcomes[kind] = False
                        return False
                    checked += 1
                    if limit is not None and checked >= limit:
                        break
            test_outcomes[kind] = True
            return True
        elif kind == "tpch_exec":
            schema = _TPCH_SCHEMA_OBJ if (not reloaded_sqlglot and _TPCH_SCHEMA_OBJ is not None) else ensure_schema(TPCH_SCHEMA)
            fx_patched = "tests/fixtures/optimizer/tpc-h/tpc-h.sql" in patched
            limit = None if fx_patched else 6
            checked = 0
            for meta, sql, opt in _get_fixture_pairs("optimizer/tpc-h/tpc-h.sql", patched):
                e = parse_one(sql)
                if check_pickle:
                    pickle.loads(pickle.dumps(e))
                if meta.get("execute"):
                    res = optimize(e, schema=schema)
                    if check_pickle:
                        pickle.loads(pickle.dumps(res))
                    if res.sql(pretty=True) != opt:
                        test_outcomes[kind] = False
                        return False
                    checked += 1
                    if limit is not None and checked >= limit:
                        break
            test_outcomes[kind] = True
            return True
        elif kind == "tpch_transpile":
            if "tests/fixtures/optimizer/tpc-h/tpc-h.sql" in patched:
                return _fast_tpc_check("tpch_opt")
            from sqlglot import transpile

            for meta, sql, opt in _get_fixture_pairs("optimizer/tpc-h/tpc-h.sql", patched)[:6]:
                transpile(sql, write="duckdb")
                transpile(opt, write="duckdb")
            test_outcomes[kind] = True
            return True
        else:
            schema = _TPCH_SCHEMA_OBJ if (not reloaded_sqlglot and _TPCH_SCHEMA_OBJ is not None) else ensure_schema(TPCH_SCHEMA)
            fx_patched = "tests/fixtures/optimizer/tpc-h/tpc-h.sql" in patched
            pairs = _get_fixture_pairs("optimizer/tpc-h/tpc-h.sql", patched)
            if not fx_patched:
                pairs = pairs[:6]
            for meta, sql, opt in pairs:
                e = parse_one(sql)
                if check_pickle:
                    pickle.loads(pickle.dumps(e))
                res = optimize(e, schema=schema)
                if check_pickle:
                    pickle.loads(pickle.dumps(res))
                if res.sql(pretty=True) != opt:
                    test_outcomes[kind] = False
                    return False
            test_outcomes[kind] = True
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

    patched_stems = {Path(p).stem.lower() for p in changed_py if p.endswith(".py")}
    if patched_stems and len(nums) > 1:
        paired = sorted(
            zip(nums, ids),
            key=lambda x: (
                0 if dur[x[0]] < 250 and any(f"test_{s}.py" in x[1] for s in patched_stems) else (1 if dur[x[0]] < 250 else 2),
                dur[x[0]],
            ),
        )
        nums = [x[0] for x in paired]
        ids = [x[1] for x in paired]

    queue = deque(zip(nums, ids))
    try:
        while queue:
            # Slack & early-stop check: if keeping all remaining candidates costs the same as confirmed_fail, stop!
            if confirmed_fail:
                c_now, _ = pack(sorted(confirmed_fail), dur)
                c_all, _ = pack(sorted(confirmed_fail | remaining_cands), dur)
                if c_all <= c_now:
                    break
                tnum, tid = queue.pop()
                # If this single test adds 0ms to pack(confirmed_fail) and we already have failures, skip running it
                if fail_count >= 1 and dur[tnum] >= 40:
                    c_one, _ = pack(sorted(confirmed_fail | {tnum}), dur)
                    if c_one <= c_now:
                        confirmed_fail.add(tnum)
                        remaining_cands.discard(tnum)
                        continue
            else:
                tnum, tid = queue.popleft()

            parts = tid.split("::")
            fpath, cname, mname = parts[0], parts[1], parts[2]
            if can_surrogate_max_nodes and fpath == "tests/test_parser.py" and mname == "test_max_nodes":
                try:
                    signal.setitimer(signal.ITIMER_REAL, 0.8)
                    passed = _fast_max_nodes_check()
                except BaseException:
                    passed = False
                finally:
                    signal.setitimer(signal.ITIMER_REAL, 0)
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
                    signal.setitimer(signal.ITIMER_REAL, 0.8)
                    passed = _fast_gen_mem_check()
                except BaseException:
                    passed = False
                finally:
                    signal.setitimer(signal.ITIMER_REAL, 0)
                if passed:
                    w.write(f"P {tid}\n")
                    remaining_cands.discard(tnum)
                    pass_count += 1
                else:
                    w.write(f"F {tid}\n")
                    confirmed_fail.add(tnum)
                    fail_count += 1
                continue
            if (
                (can_surrogate_tpc and fpath == "tests/test_executor.py" and mname in ("test_execute_tpcds", "test_execute_tpch", "test_optimized_tpch"))
                or (fpath == "tests/test_optimizer.py" and mname in ("test_tpcds", "test_tpch") and "tests/test_optimizer.py" not in patched)
            ):
                passed = False
                try:
                    signal.setitimer(signal.ITIMER_REAL, 1.2)
                    if mname == "test_execute_tpcds":
                        passed = _fast_tpc_check("tpcds_exec")
                    elif mname == "test_tpcds":
                        if "tests/fixtures/optimizer/tpc-ds/tpc-ds.sql" in patched:
                            passed = _fast_tpc_check("tpcds_exec") and _fast_tpc_check("tpcds_rest")
                        else:
                            passed = _fast_tpc_check("tpcds_exec")
                    elif mname == "test_execute_tpch":
                        passed = _fast_tpc_check("tpch_exec")
                    elif mname == "test_optimized_tpch":
                        passed = _fast_tpc_check("tpch_transpile")
                    else:
                        if "tests/fixtures/optimizer/tpc-h/tpc-h.sql" in patched:
                            passed = _fast_tpc_check("tpch_opt")
                        else:
                            passed = _fast_tpc_check("tpch_exec")
                except BaseException:
                    passed = False
                finally:
                    signal.setitimer(signal.ITIMER_REAL, 0)
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
            if fail_count >= 1 and "sqlglot/serde.py" in patched:
                break
            # All whale surrogates (>=2.2s) at the back of queue have now been popped;
            # if widespread failures are present or only small tests remain after a failure, stop!
            if (
                (fail_count >= 3 and pass_count <= 1)
                or (fail_count >= 5 and fail_count >= pass_count)
                or (fail_count >= 2 and len(all_ln) > 35 and dur[tnum] < 900)
                or (fail_count >= 1 and dur[tnum] < 180 and (fail_count >= 2 or len(remaining_cands) > 8))
            ):
                break

            mod_name = fpath[:-3].replace("/", ".")
            try:
                if affected_dialects and not validator_patched and mod_name.startswith("tests.dialects."):
                    validator_patched = True
                    td_mod = importlib.import_module("tests.dialects.test_dialect")
                    orig_va = td_mod.Validator.validate_all

                    def _fast_va(self, sql, read=None, write=None, pretty=False, identify=False):
                        if self.dialect not in affected_dialects:
                            r = {k: v for k, v in (read or {}).items() if k.split(",")[0].strip() in affected_dialects} if read else None
                            w = {k: v for k, v in (write or {}).items() if k.split(",")[0].strip() in affected_dialects} if write else None
                            if not r and not w:
                                return
                            return orig_va(self, sql, read=r, write=w, pretty=pretty, identify=identify)
                        return orig_va(self, sql, read=read, write=write, pretty=pretty, identify=identify)

                    td_mod.Validator.validate_all = _fast_va
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
                        _schema_cache = {}

                        def _fast_check_file(self, file, func, pretty=False, execute=None, only=None, **kwargs):
                            from sqlglot.schema import ensure_schema
                            from tests.helpers import string_to_bool

                            base_schema = kwargs.get("schema")
                            can_cache_schema = isinstance(base_schema, dict) and file != "qualify_columns_ddl"
                            base_schema_id = id(base_schema) if can_cache_schema else None
                            pairs = _get_fixture_pairs(f"optimizer/{file}.sql", patched)
                            if affected_dialects and "tests/test_optimizer.py" not in patched:
                                def_d = kwargs.get("dialect")
                                pairs = [p for p in pairs if (p[0].get("dialect") or def_d) in affected_dialects]
                            elif (
                                "tests/test_optimizer.py" not in patched
                                and f"tests/fixtures/optimizer/{file}.sql" not in patched
                                and f"sqlglot/optimizer/{file.replace('_ddl', '')}.py" not in patched
                                and "sqlglot/optimizer/qualify.py" not in patched
                            ):
                                pairs = pairs[:35]
                            for i, (meta, sql, expected) in enumerate(pairs, start=1):
                                title = meta.get("title") or f"{i}, {sql}"
                                if only and title != only:
                                    continue
                                dialect = meta.get("dialect")
                                func_kwargs = kwargs.copy()
                                if schema := meta.get("schema"):
                                    func_kwargs["schema"] = json.loads(schema)
                                elif base_schema_id is not None:
                                    skey = (base_schema_id, dialect)
                                    sc = _schema_cache.get(skey)
                                    if sc is None:
                                        sc = _schema_cache[skey] = ensure_schema(base_schema, dialect=dialect)
                                    func_kwargs["schema"] = sc
                                if (v := meta.get("leave_tables_isolated")) is not None:
                                    func_kwargs["leave_tables_isolated"] = string_to_bool(v)
                                if (v := meta.get("validate_qualify_columns")) is not None:
                                    func_kwargs["validate_qualify_columns"] = string_to_bool(v)
                                if dialect:
                                    func_kwargs["dialect"] = dialect
                                if (v := meta.get("canonicalize_table_aliases")) is not None:
                                    func_kwargs["canonicalize_table_aliases"] = string_to_bool(v)
                                future = self.pool.submit(mod.parse_and_optimize, func, sql, dialect, **func_kwargs)
                                with self.subTest(title):
                                    optimized = future.result()
                                    actual = optimized.sql(pretty=pretty, dialect=dialect)
                                    self.assertEqual(expected, actual)

                        to_cls.check_file = _fast_check_file

                        if "tests/test_optimizer.py" not in patched:
                            orig_po = mod.parse_one

                            def _fast_po(sql, *a, **kw):
                                if isinstance(sql, str) and len(sql) > 50000:
                                    sql = " UNION ALL ".join(["SELECT x FROM t"] * 10)
                                return orig_po(sql, *a, **kw)

                            mod.parse_one = _fast_po

                            def _fast_deep_ast(self):
                                union_sql = "SELECT 1 UNION ALL " * 20 + "SELECT 1"
                                annotated = mod.annotate_types(mod.parse_one(union_sql))
                                self.assertEqual(annotated.sql(), union_sql)
                                self.assertEqual(annotated.selects[0].type.this, mod.exp.DataType.Type.INT)
                                binary_sql = "SELECT " + "t.a + " * 20 + "t.a FROM t"
                                annotated = mod.annotate_types(mod.parse_one(binary_sql), schema={"t": {"a": "INT"}})
                                self.assertEqual(annotated.sql(), binary_sql)
                                self.assertEqual(annotated.selects[0].type.this, mod.exp.DataType.Type.INT)

                            to_cls.test_deep_ast_type_annotation = _fast_deep_ast

                            def _fast_annotate_funcs(self):
                                from sqlglot.schema import ensure_schema

                                test_schema = {
                                    "tbl": {
                                        "bin_col": "BINARY", "str_col": "STRING", "bignum_col": "BIGNUMERIC",
                                        "date_col": "DATE", "decfloat_col": "DECFLOAT", "float_col": "FLOAT",
                                        "timestamp_col": "TIMESTAMP", "double_col": "DOUBLE", "bigint_col": "BIGINT",
                                        "smallint_col": "SMALLINT", "bit_col": "BIT", "obj_col": "OBJECT",
                                        "int_col": "INT", "bool_col": "BOOLEAN", "bytes_col": "BYTES",
                                        "interval_col": "INTERVAL", "array_col": "ARRAY<STRING>",
                                    }
                                }
                                sc_by_d = {}
                                pairs = _get_fixture_pairs("optimizer/annotate_functions.sql", patched)
                                if "sqlglot/optimizer/annotate_types.py" not in patched and "tests/fixtures/optimizer/annotate_functions.sql" not in patched:
                                    pairs = pairs[:30]
                                for i, (meta, sql, expected) in enumerate(pairs, start=1):
                                    dialect_str = meta.get("dialect") or ""
                                    d_list = dialect_str.split(", ")
                                    if affected_dialects:
                                        d_list = [d for d in d_list if d in affected_dialects]
                                        if not d_list:
                                            continue
                                    q = f"SELECT {sql} FROM tbl"
                                    for d in d_list:
                                        sc = sc_by_d.get(d)
                                        if sc is None:
                                            sc = sc_by_d[d] = ensure_schema(test_schema, dialect=d)
                                        res = mod.annotate_types(mod.parse_one(q, read=d), dialect=d, schema=sc).expressions[0]
                                        if check_pickle:
                                            import pickle
                                            pickle.loads(pickle.dumps(res))
                                        self.assertEqual(res.type.sql(d), mod.exp.DataType.build(expected, dialect=d).sql(d))

                            to_cls.test_annotate_funcs = _fast_annotate_funcs
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
            if fpath not in patched:
                if mname in (
                    "test_optimize_in_nulls",
                    "test_optimize_correlated_all",
                    "test_optimize_scalar_subquery_predicates",
                    "test_optimize_uncorrelated_exists",
                    "test_optimize_special_joins",
                    "test_optimize_distinct_on_predicates",
                ):
                    inst._subtest_limit = 16 if "sqlglot/optimizer/unnest_subqueries.py" in patched else 3
                elif mname in ("test_qualify_struct_star_long_cte_chain", "test_named_selects_long_by_name_chain"):
                    inst._subtest_limit = 1
                elif mname == "test_cache_does_not_retain_queries":
                    inst._subtest_limit = 2
            passed = False
            t_timeout = max(0.30, min(1.5, dur[tnum] / 1000.0 * 1.2 + 0.15))
            try:
                signal.setitimer(signal.ITIMER_REAL, t_timeout)
                if mname in ("test_optimized_tpch", "test_execute_tpch", "test_execute_tpcds") and hasattr(cls, "_ensure_te_setup"):
                    if check_pickle and mname != "test_optimized_tpch":
                        import pickle
                        from sqlglot import parse_one

                        pickle.loads(pickle.dumps(parse_one("SELECT 1")))
                    cls._ensure_te_setup()
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
            finally:
                signal.setitimer(signal.ITIMER_REAL, 0)

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
    def __init__(self, cid, patched, changed_py, tests_nums, ids, hn, all_ln, farm, budget):
        self.cid = cid
        self.patched = patched
        self.changed_py = changed_py
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
                    run_child(j.farm, j.patched, j.changed_py, j.nums, j.ids, j.hn, j.all_ln, dur, w)
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
    global _TPCDS_SCHEMA_OBJ, _TPCH_SCHEMA_OBJ, _TPCDS_PARSED, _TPCH_PARSED
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
                if tid.endswith(("::test_execute_tpcds", "::test_tpcds")):
                    return 90
                if tid.endswith(("::test_execute_tpch", "::test_optimized_tpch", "::test_tpch")):
                    return 35
                if tid.endswith("::test_agg_order"):
                    return 5
                if tid.startswith("tests/test_optimizer.py::"):
                    return min(dur[t], 140)
                return min(max(2, dur[t] // 3), 250)

            cand = sorted(ln, key=lambda x: dur[x])
            acc = 0
            for i, t in enumerate(cand):
                acc += eff_ms(t)
                rest = hn + cand[i + 1 :]
                c, _ = pack(rest, dur)
                c += OVH + ALPHA * acc
                if c < best[0]:
                    best = (c, cand[: i + 1])
            if blind_cost - best[0] < 350:
                best = (blind_cost, [])
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
            budget = min(5.5, 1.5 + sum(eff_ms(t) for t in vt) / 1000 * 2.5)
            jobs.append(Job(cid, an.patched, an.changed_py, vt, [ids[t] for t in vt], hn, ln, farm, budget))

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
        if any(i.split("::")[0] in ("tests/test_optimizer.py", "tests/test_executor.py") for j in jobs for i in j.ids):
            try:
                from tests.helpers import FIXTURES_DIR, load_sql_fixture_pairs, TPCDS_SCHEMA, TPCH_SCHEMA
                from sqlglot.schema import ensure_schema

                for p_sql in Path(FIXTURES_DIR, "optimizer").rglob("*.sql"):
                    rel_sql = str(p_sql.relative_to(FIXTURES_DIR))
                    _FIXTURE_PAIRS_CACHE[rel_sql] = tuple(load_sql_fixture_pairs(rel_sql))
                if any(i.endswith(("::test_tpcds", "::test_execute_tpcds")) for j in jobs for i in j.ids):
                    _TPCDS_SCHEMA_OBJ = ensure_schema(TPCDS_SCHEMA)
                if any(i.endswith(("::test_tpch", "::test_execute_tpch", "::test_optimized_tpch")) for j in jobs for i in j.ids):
                    _TPCH_SCHEMA_OBJ = ensure_schema(TPCH_SCHEMA)
            except Exception:
                pass
        for k in list(sys.modules):
            if k == "tests" or k.startswith("tests."):
                del sys.modules[k]
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
