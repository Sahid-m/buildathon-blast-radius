"""Generate synthetic patches and their ground-truth failing tests.

usage: python mutants.py <repo> <outdir> <count> <seed>
Writes outdir/commits/<id>.patch, outdir/tests.json (copy), outdir/answers.json
Ground truth = full pytest run on a patched copy of the repo.
"""
import difflib
import json
import os
import random
import re
import shutil
import subprocess
import sys
import tempfile

repo, outdir, count, seed = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
rng = random.Random(seed)
os.makedirs(f"{outdir}/commits", exist_ok=True)
tests_json = "/Users/sahid/Documents/Personal/Hackathons/Buildathon/blast-radius/sample/sample/tests.json"
shutil.copy(tests_json, f"{outdir}/tests.json")
tests = json.load(open(tests_json))["tests"]
id2num = {t["id"]: t["number"] for t in tests}

py_files = [os.path.relpath(os.path.join(d, f), repo) for d, _, fs in os.walk(f"{repo}/sqlglot") for f in fs if f.endswith(".py")]
fix_files = [os.path.relpath(os.path.join(d, f), repo) for d, _, fs in os.walk(f"{repo}/tests/fixtures") for f in fs if f.endswith(".sql")]
test_files = [os.path.relpath(os.path.join(d, f), repo) for d, _, fs in os.walk(f"{repo}/tests") for f in fs if f.endswith(".py") and "fixtures" not in d]

SWAPS = [(" and ", " or "), (" or ", " and "), (" == ", " != "), (" != ", " == "), (" is not ", " is "),
         (" is ", " is not "), ("True", "False"), ("False", "True"), (" < ", " <= "), (" > ", " >= "),
         ("not ", ""), (" + 1", " + 2"), (" - 1", " - 2"), ("(1)", "(2)"), ("[0]", "[1]"), ("[1]", "[0]"),
         ('"', '"x'), ("return ", "return None and ")]
COMMENTS = ["# Kept for backwards compatibility", "# Cheap check first", "# TODO: revisit", "# noqa"]


def mutate():
    kind = rng.choices(["code", "fixture", "comment", "test", "multi", "docstring"], [8, 4, 2, 1, 2, 1])[0]
    if kind == "multi":
        a = mutate_one("code")
        b = mutate_one(rng.choice(["fixture", "comment"]))
        if not a or not b or a[0] == b[0]:
            return None
        return "multi", [a, b]
    m = mutate_one(kind)
    return (kind, [m]) if m else None


def mutate_one(kind):
    if kind in ("code", "comment", "docstring"):
        f = rng.choice(py_files)
    elif kind == "fixture":
        f = rng.choice(fix_files)
    else:
        f = rng.choice(test_files)
    lines = open(f"{repo}/{f}").read().split("\n")
    for _ in range(200):
        i = rng.randrange(len(lines))
        L = lines[i]
        s = L.strip()
        if not s:
            continue
        if kind == "comment":
            if s.startswith(("#", '"', "'")) or s.endswith(("(", "[", "{", ",", "\\")):
                continue
            ind = re.match(r"\s*", L).group(0)
            new = lines[:i] + [ind + rng.choice(COMMENTS)] + lines[i:]
            return f, lines, new
        if kind == "docstring":
            if s.startswith('"""') and len(s) > 6:
                new = list(lines)
                new[i] = L.replace('"""', '""" Note:', 1)
                return f, lines, new
            continue
        if kind == "fixture":
            toks = L.split(" ")
            if len(toks) < 2 or s.startswith("#") or s.startswith("--"):
                continue
            j = rng.randrange(1, len(toks))
            toks.insert(j, rng.choice(["0", "x", "42", "NULL"]))
            new = list(lines)
            new[i] = " ".join(toks)
            return f, lines, new
        if s.startswith(("#", "import", "from", "def ", "class ", "@")):
            continue
        cands = [(a, b) for a, b in SWAPS if a in L]
        if not cands:
            continue
        a, b = rng.choice(cands)
        new = list(lines)
        new[i] = L.replace(a, b, 1)
        return f, lines, new
    return None


def to_patch(muts):
    out = []
    for f, old, new in muts:
        d = difflib.unified_diff([l + "\n" for l in old], [l + "\n" for l in new], f"a/{f}", f"b/{f}", n=3)
        body = "".join(d)
        out.append(f"diff --git a/{f} b/{f}\nindex 0000000..1111111 100644\n" + body)
    return "".join(out)


def ground_truth(muts):
    tmp = tempfile.mkdtemp(prefix="mut_")
    for d in ("sqlglot", "tests", "sqlglotc"):
        shutil.copytree(f"{repo}/{d}", f"{tmp}/{d}", ignore=shutil.ignore_patterns("__pycache__"))
    for f in ("pyproject.toml", "setup.cfg", "setup.py"):
        if os.path.exists(f"{repo}/{f}"):
            shutil.copy(f"{repo}/{f}", f"{tmp}/{f}")
    for f, old, new in muts:
        open(f"{tmp}/{f}", "w").write("\n".join(new))
    env = dict(os.environ, SKIP_INTEGRATION="0", PYTHONPATH=tmp)
    r = subprocess.run([sys.executable, "-m", "pytest", "-q", "-n", "8", "-p", "no:cacheprovider", "tests",
                        "-rfE", "--timeout", "120"], cwd=tmp, env=env, capture_output=True, text=True)
    failing = set()
    for line in r.stdout.split("\n"):
        m = re.match(r"(?:FAILED|ERROR|SUBFAILED).*? (tests/\S+)", line)
        if m:
            tid = m.group(1)
            tid = re.sub(r"\[.*$", "", tid)
            if tid in id2num:
                failing.add(id2num[tid])
            else:
                # file-level error: all tests in the file
                for t in tests:
                    if t["id"].startswith(tid):
                        failing.add(t["number"])
    shutil.rmtree(tmp, ignore_errors=True)
    tail = r.stdout.strip().split("\n")[-1]
    return sorted(failing), tail


ans_path = f"{outdir}/answers.json"
answers = json.load(open(ans_path))["commits"] if os.path.exists(ans_path) else {}
made = 0
while made < count:
    m = mutate()
    if not m:
        continue
    kind, muts = m
    cid = f"m{seed}_{len(answers):03d}"
    failing, tail = ground_truth(muts)
    open(f"{outdir}/commits/{cid}.patch", "w").write(to_patch(muts))
    answers[cid] = {"failing": failing, "kind": kind}
    json.dump({"commits": answers}, open(ans_path, "w"), indent=1)
    made += 1
    print(cid, kind, [x[0] for x in muts], len(failing), tail, flush=True)
