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
        self.remap = [by_id.get(tid, -1) for tid, _ in d["tests"]]
        self.identity = all(i == j for i, j in enumerate(self.remap)) and len(self.remap) == len(tests)
        self.ntests = len(tests)
        self._importers: dict[str, int] = {}

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

    def users_ci(self, name: str) -> int:
        """Tests executing a line, or opening a data file, that mentions `name` (any case)."""
        key = "ci:" + name.lower()
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
            rt = self.runtime_lines(f, txt) if f.startswith("sqlglot/") else None
            for m in pat.finditer(lt):
                ln = bisect_right(starts, m.start())
                if ln in seen:
                    continue
                seen.add(ln)
                if rt is not None and ln not in rt:
                    continue  # import-time line in the library: runs for every importer
                i = fl.get(str(ln))
                if i is not None:
                    v |= self.cov.set(i)
        for f, lt in self.fixture_texts().items():
            if low in lt and pat.search(lt):
                v |= self.cov.openers(f)
        self._users[key] = v
        return v

    def runtime_lines(self, f, txt):
        """Lines inside function/lambda bodies (they run only when called)."""
        if not hasattr(self, "_rt"):
            self._rt = {}
        r = self._rt.get(f)
        if r is None:
            r = set()
            try:
                tree = ast.parse(txt)
            except SyntaxError:
                tree = None
            if tree is not None:
                for node in ast.walk(tree):
                    if isinstance(node, FUNC):
                        r.update(range(node.body[0].lineno, node.end_lineno + 1))
                    elif isinstance(node, ast.Lambda):
                        r.update(range(node.lineno, node.end_lineno + 1))
            self._rt[f] = r
        return r

    def lower_text(self, f, txt):
        if not hasattr(self, "_lower"):
            self._lower = {}
        lt = self._lower.get(f)
        if lt is None:
            lt = self._lower[f] = txt.lower()
        return lt

    def subclasses(self, name: str) -> set[str]:
        out = {name}
        frontier = [name]
        while frontier:
            n = frontier.pop()
            pat = re.compile(r"^\s*class\s+(\w+)\s*\(([^)]*)\)", re.M)
            for f, (txt, _) in self.texts().items():
                if n not in txt:
                    continue
                for m in pat.finditer(txt):
                    bases = re.findall(r"[A-Za-z_][A-Za-z0-9_]*", m.group(2))
                    if n in bases and m.group(1) not in out:
                        out.add(m.group(1))
                        frontier.append(m.group(1))
        return out

    def class_users(self, outer: str, inner: str) -> int:
        v = 0
        for c in self.subclasses(outer) | self.subclasses(inner):
            v |= self.users_ci(c)
            snake = re.sub(r"(?<=[a-z0-9])([A-Z])", r"_\1", c)
            if snake != c:
                v |= self.users_ci(snake)
            for suf in ("Parser", "Generator", "Tokenizer", "Dialect"):
                if c.endswith(suf) and len(c) > len(suf):
                    v |= self.users_ci(c[: -len(suf)])
        return v

    def users(self, name: str) -> int:
        v = self._users.get(name)
        if v is not None:
            return v
        v = 0
        pat = re.compile(r"(?<![A-Za-z0-9_])" + re.escape(name) + r"(?![A-Za-z0-9_])")
        for f, (txt, starts) in self.texts().items():
            if name not in txt:
                continue
            fl = self.cov.lines.get(f) or {}
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
        o = cov.openers(path)
        if o:
            if path.startswith("tests/fixtures/") or path.startswith("tests/"):
                an.high |= o
            else:
                an.low |= o
        an.notes.append(f"data {path} openers={bin(o).count('1')}")
        return

    analyze_py(path, old_text, new_text, removed, added, new2old, an, cov, src)


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
    if ast.dump(old_tree) == ast.dump(new_tree):
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
            if isinstance(st, (ast.Import, ast.ImportFrom)) or not names:
                touched |= imp
                an.notes.append(f"import-level {path}:{line} -> importers")
                return
            u = 0
            for n in names:
                u |= src.users(n)
            classes = [c for c, _, _ in ch if isinstance(c, ast.ClassDef)]
            if classes:
                # a class attribute only matters where that class (or a subclass) is used
                u &= src.class_users(classes[0].name, classes[-1].name)
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
            if entry in (".git",):
                continue
            os.symlink(src_dir / entry, dst_dir / entry)
    for p, txt in patched.items():
        if txt is None:
            continue
        (root / p).parent.mkdir(parents=True, exist_ok=True)
        (root / p).write_text(txt, encoding="utf-8")
    return True


CHILD_CODE = None


def run_child(farm: Path, ids: list[str], wfd: int):
    """In a forked child: run the given test ids with pytest in `farm`."""
    import resource

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
    for k in list(sys.modules):
        if k == "sqlglot" or k.startswith("sqlglot.") or k == "tests" or k.startswith("tests."):
            del sys.modules[k]
    os.environ["SKIP_INTEGRATION"] = "0"
    import pytest
    import concurrent.futures as cf

    class InlinePool:
        """Run 'process pool' work inline: avoids spawning interpreters (CPU is charged)."""

        def __init__(self, max_workers=None, mp_context=None, initializer=None, initargs=(), **kw):
            if initializer is not None:
                initializer(*initargs)

        def submit(self, fn, /, *a, **k):
            f = cf.Future()
            try:
                f.set_result(fn(*a, **k))
            except BaseException as e:  # noqa
                f.set_exception(e)
            return f

        def map(self, fn, *its, timeout=None, chunksize=1, buffersize=None):
            return iter([fn(*x) for x in zip(*its)])

        def shutdown(self, wait=True, *, cancel_futures=False):
            pass

        def __enter__(self):
            return self

        def __exit__(self, *a):
            return False

    cf.ProcessPoolExecutor = InlinePool
    try:
        import concurrent.futures.process as cfp

        cfp.ProcessPoolExecutor = InlinePool
    except Exception:
        pass

    w = os.fdopen(wfd, "w", buffering=1)

    class Rep:
        def __init__(self):
            self.failed = set()

        def pytest_runtest_logreport(self, report):
            if report.failed:
                self.failed.add(report.nodeid)
            if report.when == "teardown":
                w.write(("F " if report.nodeid in self.failed else "P ") + report.nodeid + "\n")

        def pytest_collectreport(self, report):
            if report.failed:
                w.write("C " + report.nodeid + "\n")

    rep = Rep()
    try:
        pytest.main(
            ["-q", "-p", "no:cacheprovider", "-p", "no:xdist", "-p", "no:randomly", "-p", "no:timeout", "--assert=plain", "-W", "ignore", "--rootdir", str(farm)] + ids,
            plugins=[rep],
        )
    finally:
        w.write("END\n")
        w.flush()
        os._exit(0)


class Job:
    def __init__(self, cid, tests_nums, ids, farm, budget):
        self.cid = cid
        self.nums = tests_nums
        self.ids = ids
        self.farm = farm
        self.budget = budget
        self.pid = None
        self.rfd = None
        self.buf = b""
        self.results: dict[str, str] = {}
        self.collect_err: list[str] = []
        self.ended = False
        self.start = None


def run_jobs(jobs: list[Job], parallel: int, deadline: float):
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
                    run_child(j.farm, j.ids, w)
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

    ALPHA = float(os.environ.get("BR_ALPHA", "1.3"))
    OVH = float(os.environ.get("BR_OVH", "700"))  # ms CPU per verification run
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
        # choose verification threshold
        best = (blind_cost, [])
        if VERIFY and ln and not an.unverifiable:
            cand = sorted(ln, key=lambda x: dur[x])
            acc = 0
            for i, t in enumerate(cand):
                acc += dur[t]
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
            budget = 3.0 + sum(dur[t] for t in vt) / 1000 * 4
            jobs.append(Job(cid, vt, [ids[t] for t in vt], farm, budget))

    if jobs:
        # pre-import heavy modules once so forked children share them
        t_imp = time.time()
        try:
            import pytest  # noqa
            import _pytest.python  # noqa
            import _pytest.unittest  # noqa
            import _pytest.subtests  # noqa
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
        run_jobs(jobs, parallel=2, deadline=T0 + float(os.environ.get("BR_DEADLINE", "160")))
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
