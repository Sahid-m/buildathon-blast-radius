"""Turn per-test coverage dumps into one compact map.

usage: python build_map.py <covdir> <tests.json> <out.json>

Output (JSON):
  tests:  [[id, seconds], ...]                 index = test number
  sets:   [base64 bitmask, ...]                interned test sets
  lines:  {file: {line: set_index}}            tests executing a line
  opens:  {file: set_index}                    tests that opened a non-.py file
  failed: [test numbers whose baseline run failed]
"""
import base64
import json
import os
import sys
from collections import defaultdict

covdir, tests_json, out = sys.argv[1:4]
tests = json.load(open(tests_json))["tests"]
n = len(tests)

line_bits = defaultdict(lambda: defaultdict(int))
open_bits = defaultdict(int)
failed = []
missing = []
for t in tests:
    num = t["number"]
    p = f"{covdir}/{num}.json"
    if not os.path.exists(p):
        missing.append(num)
        continue
    d = json.load(open(p))
    if d["rc"] != 0:
        failed.append(num)
    bit = 1 << num
    for f, ls in d["lines"].items():
        fb = line_bits[f]
        for ln in ls:
            fb[ln] |= bit
    for f in d["opens"]:
        if f.endswith(".py") or f.endswith(".pyc") or "__pycache__" in f:
            continue
        open_bits[f] |= bit

sets = {}
setlist = []


def intern(v):
    i = sets.get(v)
    if i is None:
        i = sets[v] = len(setlist)
        setlist.append(v)
    return i


lines = {f: {str(ln): intern(v) for ln, v in sorted(fb.items())} for f, fb in sorted(line_bits.items())}
opens = {f: intern(v) for f, v in sorted(open_bits.items())}
nbytes = (n + 7) // 8
enc = [base64.b64encode(v.to_bytes(nbytes, "little")).decode() for v in setlist]
json.dump(
    {
        "tests": [[t["id"], t["seconds"]] for t in tests],
        "sets": enc,
        "lines": lines,
        "opens": opens,
        "failed": failed,
        "missing": missing,
    },
    open(out, "w"),
    separators=(",", ":"),
)
print(f"files={len(lines)} sets={len(setlist)} failed={failed} missing={len(missing)} size={os.path.getsize(out)}", file=sys.stderr)
