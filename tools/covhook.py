import os, sys
_d = os.environ.get("COVHOOK_DIR")
if _d:
    import atexit, json
    _prefix = os.environ["COVHOOK_PREFIX"]
    _lines = {}
    _mon = sys.monitoring
    _mon.use_tool_id(4, "covhook")
    def _on_line(code, ln):
        fn = code.co_filename
        if fn.startswith(_prefix):
            s = _lines.get(fn)
            if s is None:
                s = _lines[fn] = set()
            s.add(ln)
        return _mon.DISABLE
    _mon.register_callback(4, _mon.events.LINE, _on_line)
    _mon.set_events(4, _mon.events.LINE)
    def _dump():
        with open(f"{_d}/{os.getpid()}.json", "w") as f:
            json.dump({k[len(_prefix):]: sorted(v) for k, v in _lines.items()}, f)
    atexit.register(_dump)
