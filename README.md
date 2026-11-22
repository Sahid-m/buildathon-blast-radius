# Blast Radius entry (sqlglot test selection)

`selector.py` reads `/data/commits/*.patch` and `/data/tests.json` and prints one
`{"commit", "workers"}` line per commit.

## Approach

1. **Per-test coverage map (`covmap.json`)**, built once at the pinned sqlglot commit
   (`tools/collect.py` + `tools/build_map.py`). Every test runs in its *own forked
   process* (pytest pre-imported, sqlglot not), so module- and class-level lines are
   attributed to every test that imports that module, and lazy caches are attributed
   to every test that needs them. Lines run in `spawn` worker processes are captured
   too (`tools/covhook.py`, loaded via a `.pth` during collection). The map also records
   which data files (fixtures) each test opens. Test sets are interned base64 bitmasks
   (3.3 MB).
2. **Patch analysis** (AST-based, both old and new trees):
   - comment/whitespace-only change (AST identical) -> no tests;
   - syntax error / deleted / renamed module -> every test importing it (blind);
   - change inside a function or lambda body -> tests covering that statement; an
     inserted statement -> tests that reach the preceding sibling / parent header;
   - import-time change (module/class level assignment) -> importers of the module
     that execute a line mentioning the assigned name, restricted (for class
     attributes) to tests that use that class or a subclass (by name, lower-case
     name, snake-case SQL name, or a fixture mentioning it);
   - fixture / other data file -> tests that opened it (treated as very likely to fail);
   - test files: same coverage logic, test-body changes treated as likely failures.
3. **Runtime verification**: candidates that are probably passing and cheap are run
   against the patched tree (symlink farm in `/tmp`, forked pytest child, process pools
   run inline to save CPU). Tests that pass are dropped. The verify set is chosen to
   minimise CPU + expected packing cost. Timeouts or crashes keep the test selected.
4. **Packing**: LPT over 1..8 workers, minimising busiest worker + 2 s/worker.

No table from patches or edit kinds to failing tests is used; `sample/answers.json`
is only used by `score.py` for local evaluation.

## Run

```sh
make sample   # build (linux/amd64), run on sample/ under the scorer's limits, score
```

Regenerating the map (needs Python 3.13 + requirements.lock + sqlglot at eb11aec):
`python tools/collect.py <sqlglot> <tests.json> cov 8 && python tools/build_map.py cov <tests.json> covmap.json`
(install `tools/covhook.py` + a `covhook.pth` containing `import covhook` into site-packages first).

## Third-party

`score.py`, `SCORING.md`, `Makefile`, `sample/` and `requirements.lock` come from the
organisers' starter kit. Everything else is our own work, MIT licensed.
