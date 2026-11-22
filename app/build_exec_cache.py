"""Builds the TestExecutor row cache that rt/preload.py reads (run at image build time).

usage: python build_exec_cache.py REPO OUT_DIR [--check]
Runs the real TestExecutor.setUpClass of the pinned checkout and writes, for tpch and tpcds,
OUT_DIR/exec_<which>.marshal = ({table: size of its csv.gz}, {table: marshalled rows}) in schema
order (the rows of each table are packed alone, so that one table can be unpacked alone).
--check: also rebuilds every lazy attribute with preload.py (cache path) and compares it with
what setUpClass made (Table columns, rows with exact types, view contents, fixture pairs)."""
import marshal
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)


def typed(rows):
    return [tuple((type(v), repr(v)) for v in r) for r in rows]


def main():
    repo, out, check = sys.argv[1], sys.argv[2], "--check" in sys.argv
    import preload

    preload.install_environment(repo)
    preload.import_tests(["tests.test_executor"])
    mod = sys.modules["tests.test_executor"]
    cls = mod.TestExecutor
    cls.setUpClass()
    os.makedirs(out, exist_ok=True)
    for which, tables, (schema, directory) in (
        ("tpch", cls.tpch_tables, preload._exec_schema(mod, "tpch")),
        ("tpcds", cls.tpcds_tables, preload._exec_schema(mod, "tpcds")),
    ):
        assert list(tables) == list(schema)
        sizes = {t: os.path.getsize(f"{directory}{t}.csv.gz") for t in schema}
        rows = {t: marshal.dumps(tables[t].rows) for t in schema}
        path = os.path.join(out, "exec_%s.marshal" % which)
        with open(path + ".tmp", "wb") as f:
            marshal.dump((sizes, rows), f)
        os.replace(path + ".tmp", path)
        print(path, os.path.getsize(path), "bytes", file=sys.stderr)
    import zlib
    from sqlglot import parse_one
    from sqlglot.optimizer import optimize
    from sqlglot.planner import Plan
    from sqlglot.schema import ensure_schema
    schema_obj = ensure_schema(mod.TPCDS_SCHEMA, dialect=None)
    front = {}
    for i, (meta, sql, _) in enumerate(cls.tpcds_sqls):
        if meta.get("execute"):
            e = parse_one(sql)
            opt = optimize(e.copy(), schema_obj, leave_tables_isolated=True, dialect=None)
            p = Plan(opt)
            sig = (repr(e), repr(opt), tuple(type(s).__name__ for s in p.leaves),
                   tuple(str(n.type) for n in opt.walk() if n.type))
            front[i] = zlib.crc32(repr(sig).encode())
    fpath = os.path.join(out, "tpcds_front.bin")
    with open(fpath + ".tmp", "wb") as f:
        marshal.dump(front, f)
    os.replace(fpath + ".tmp", fpath)
    if not check:
        return
    preload.EXEC_CACHE = out
    bad = 0

    class Fake:  # a class with the module of TestExecutor, for _exec_build
        __module__ = mod.__name__

    for name in preload.EXEC_LAZY:
        new, old = preload._exec_build(Fake, name), getattr(cls, name)
        if name.endswith("_tables"):
            assert preload._exec_cached_rows(mod, name.split("_")[0]) is not None, "cache not used"
            ok = list(new) == list(old)
            for t in old:
                a, b = old[t], new[t]
                same = (type(a) is type(b) and a.columns == b.columns and type(a.rows) is type(b.rows)
                        and len(a.rows) == len(b.rows) and typed(a.rows) == typed(b.rows)
                        and a.column_range == b.column_range and a.reader.columns == b.reader.columns)
                if not same:
                    print("DIFF table", name, t, file=sys.stderr)
                ok = ok and same
        elif name.endswith("_conn"):
            q = "SELECT table_name FROM information_schema.tables ORDER BY 1"
            ok = old.execute(q).fetchall() == new.execute(q).fetchall()
            for (t,) in old.execute(q).fetchall():
                ok = ok and old.execute(f"SELECT * FROM {t}").fetchall() == new.execute(f"SELECT * FROM {t}").fetchall()
                ok = ok and old.execute(f"DESCRIBE {t}").fetchall() == new.execute(f"DESCRIBE {t}").fetchall()
        else:
            ok = new == old
        print("check", name, "OK" if ok else "DIFFERENT", file=sys.stderr)
        bad += not ok
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
