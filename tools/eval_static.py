import json, sys, os
sys.path.insert(0, "/Users/sahid/Documents/Personal/Hackathons/Buildathon/blast-radius/repo")
os.environ.setdefault("BR_REPO", "/Users/sahid/Documents/Personal/Hackathons/Buildathon/blast-radius/work/sqlglot")
import selector as S
from pathlib import Path
data = Path(sys.argv[2] if len(sys.argv) > 2 else "data")
S.REPO = Path(os.environ["BR_REPO"])
tests = json.loads((data / "tests.json").read_text())["tests"]
ans = json.loads((data / "answers.json").read_text())["commits"]
dur = [round(t["seconds"] * 1000) for t in tests]
cov = S.CovMap(Path(sys.argv[1]), tests)
src = S.Sources(S.REPO, cov)
tot_blind = 0; miss = 0; tot_oracle = 0
for p in sorted((data / "commits").glob("*.patch")):
    cid = p.stem
    an = S.analyze(p.read_text(), cov, src)
    hn, ln = set(S.bits(an.high)), set(S.bits(an.low)) - set(S.bits(an.high))
    fail = set(ans[cid]["failing"])
    missing = fail - hn - ln
    bc, _ = S.pack(sorted(hn | ln), dur)
    oc, _ = S.pack(sorted(fail), dur)
    tot_blind += bc + (300000 if missing else 0); tot_oracle += oc
    miss += bool(missing)
    lsum = sum(dur[t] for t in ln) / 1000
    print(f"{cid} {ans[cid]['kind']:8} fail={len(fail):3} high={len(hn):4} low={len(ln):4} lowsum={lsum:7.2f} blind={bc/1000:7.2f} oracle={oc/1000:6.2f} MISS={sorted(missing)[:5]} {an.notes[:3]}")
print(f"blind total {tot_blind/1000:.1f} misses {miss} oracle {tot_oracle/1000:.1f}")
