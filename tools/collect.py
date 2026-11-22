"""Collect per-test line coverage + opened files, one forked child per test.
usage: python collect.py <repo> <tests.json> <outdir> <jobs>
"""
import json, os, sys, time, shutil


def child(t, repo, outdir):
    import pytest
    prefix = repo + os.sep
    lines = {}
    opens = set()
    mon = sys.monitoring
    TOOL = 3
    mon.use_tool_id(TOOL, "cov")

    def on_line(code, ln):
        fn = code.co_filename
        if fn.startswith(prefix):
            s = lines.get(fn)
            if s is None:
                s = lines[fn] = set()
            s.add(ln)
        return mon.DISABLE

    mon.register_callback(TOOL, mon.events.LINE, on_line)
    mon.set_events(TOOL, mon.events.LINE)

    def audit(ev, args):
        if ev == "open":
            p = args[0]
            if isinstance(p, (str, bytes, os.PathLike)):
                p = os.fsdecode(p)
                ap = os.path.realpath(p)
                if ap.startswith(prefix):
                    opens.add(ap[len(prefix):])
        elif ev in ("os.listdir", "os.scandir"):
            p = args[0]
            if isinstance(p, (str, bytes, os.PathLike)):
                ap = os.path.realpath(os.fsdecode(p))
                if ap.startswith(prefix):
                    opens.add(ap[len(prefix):] + "/")

    sys.addaudithook(audit)
    hookdir = f"{outdir}/hook_{t['number']}"
    os.makedirs(hookdir, exist_ok=True)
    os.environ["COVHOOK_DIR"] = hookdir
    os.environ["COVHOOK_PREFIX"] = prefix
    devnull = os.open(os.devnull, os.O_WRONLY)
    os.dup2(devnull, 1)
    os.dup2(devnull, 2)
    rc = pytest.main([t["id"], "-q", "-p", "no:cacheprovider", "-W", "ignore"])
    mon.set_events(TOOL, 0)
    res = {k[len(prefix):]: set(v) for k, v in lines.items()}
    nsub = 0
    for fn in os.listdir(hookdir):
        try:
            d = json.load(open(f"{hookdir}/{fn}"))
        except Exception:
            continue
        nsub += 1
        for k, v in d.items():
            res.setdefault(k, set()).update(v)
    shutil.rmtree(hookdir, ignore_errors=True)
    out = {"rc": int(rc), "nsub": nsub, "lines": {k: sorted(v) for k, v in res.items()}, "opens": sorted(opens)}
    with open(f"{outdir}/{t['number']}.json.tmp", "w") as f:
        json.dump(out, f)
    os.rename(f"{outdir}/{t['number']}.json.tmp", f"{outdir}/{t['number']}.json")


def main():
    repo, tests_json, outdir, jobs = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4])
    repo = os.path.realpath(repo)
    os.makedirs(outdir, exist_ok=True)
    os.chdir(repo)
    sys.path.insert(0, repo)
    os.environ["SKIP_INTEGRATION"] = "0"
    import pytest, _pytest.main, _pytest.unittest, _pytest.python  # noqa
    tests = json.load(open(tests_json))["tests"]
    only = os.environ.get("ONLY")
    if only:
        only = set(map(int, only.split(",")))
        tests = [t for t in tests if t["number"] in only]
    todo = [t for t in tests if not os.path.exists(f"{outdir}/{t['number']}.json")]
    todo.sort(key=lambda t: -t["seconds"])
    running = {}
    start = time.time()
    done = 0
    while todo or running:
        while todo and len(running) < jobs:
            t = todo.pop(0)
            pid = os.fork()
            if pid == 0:
                try:
                    child(t, repo, outdir)
                finally:
                    os._exit(0)
            running[pid] = t
        pid, status = os.wait()
        running.pop(pid, None)
        done += 1
        if done % 100 == 0:
            print(f"{done} done, {time.time()-start:.0f}s", file=sys.stderr, flush=True)
    print("finished", time.time() - start, file=sys.stderr)


if __name__ == "__main__":
    main()
