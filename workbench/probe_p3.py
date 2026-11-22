#!/usr/bin/env python3
"""
Security / read-only probes for the workbench server (docs/PHASE3_GATES.md W2).

Run against a server started on a SCRATCH annotations directory, e.g.:

    python3 workbench/server.py --port 8433 --fixtures --annotations /tmp/leanre-annot-probe &
    python3 workbench/probe_p3.py --port 8433 --annotations /tmp/leanre-annot-probe

(--fixtures makes every Phase 3 route answer with data even before the real
databases exist; run it again without --fixtures to probe the real ones.)

Checks, each printed as PASS/FAIL:
  A  Phase 2 probes still hold (SQLi on /api/search, 3 path traversals -> 403/404)
  B  SQL-injection payloads on every string parameter of every new GET route:
     never 5xx, never a SQLite error or schema leak, never extra rows
  C  malformed integers / enums -> 400
  D  path traversal through static paths, layer ids and export -> 400/403/404,
     and server-side sources (.py / .db / dotfiles) are not downloadable
  E  write gate: POST needs loopback Host + same Origin + X-Leanre-Write; only
     /api/annot/* accepts POST; oversized bodies refused
  F  annotation writes land inside --annotations and nowhere else; analysis
     databases are byte-for-byte untouched (size + mtime_ns + sha256 for small files)
  G  static audit: no external URLs loaded by the UI, every sqlite3.connect in
     workbench/ is read-only or in-memory, default bind is 127.0.0.1

Stdlib only. Exit status 1 if any check fails.
"""
from __future__ import annotations

import argparse
import hashlib
import http.client
import json
import os
import re
import sys
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple
from urllib.parse import quote

WORKBENCH = Path(__file__).resolve().parent
ROOT = WORKBENCH.parent

RESULTS: List[Tuple[bool, str, str]] = []


def check(ok: bool, name: str, detail: str = "") -> bool:
    RESULTS.append((bool(ok), name, detail))
    print("%s  %s%s" % ("PASS" if ok else "FAIL", name, ("   [" + detail + "]") if detail else ""), flush=True)
    return bool(ok)


class Client:
    def __init__(self, port: int) -> None:
        self.port = port

    def req(self, method: str, path: str, body: Optional[bytes] = None, headers: Optional[Dict[str, str]] = None,
            host: Optional[str] = None) -> Tuple[int, bytes]:
        conn = http.client.HTTPConnection("127.0.0.1", self.port, timeout=30)
        try:
            # putrequest so the raw path (with .. or %2e) reaches the server unnormalised
            conn.putrequest(method, path, skip_host=True, skip_accept_encoding=True)
            conn.putheader("Host", host or "127.0.0.1:%d" % self.port)
            for k, v in (headers or {}).items():
                conn.putheader(k, v)
            if body is not None:
                conn.putheader("Content-Length", str(len(body)))
            conn.endheaders()
            if body is not None:
                conn.send(body)
            resp = conn.getresponse()
            return resp.status, resp.read()
        finally:
            conn.close()

    def get(self, path: str) -> Tuple[int, bytes]:
        return self.req("GET", path)

    def get_json(self, path: str) -> Tuple[int, Any]:
        st, raw = self.get(path)
        try:
            return st, json.loads(raw.decode("utf-8"))
        except Exception:
            return st, None

    def post(self, path: str, obj: Any, **kw: Any) -> Tuple[int, Any]:
        headers = {"Content-Type": "application/json", "X-Leanre-Write": "1"}
        headers.update(kw.pop("headers", {}))
        for k in kw.pop("drop", []):
            headers.pop(k, None)
        raw = obj if isinstance(obj, (bytes, bytearray)) else json.dumps(obj).encode("utf-8")
        st, out = self.req("POST", path, body=bytes(raw), headers=headers, host=kw.pop("host", None))
        try:
            return st, json.loads(out.decode("utf-8"))
        except Exception:
            return st, None


SQLI = [
    "' OR 1=1 --",
    "\" OR \"\"=\"",
    "x'; DROP TABLE decls; --",
    "%' UNION SELECT name, sql, 1, 1 FROM sqlite_master --",
    "1; ATTACH DATABASE '/tmp/leanre_probe_pwn.db' AS pwn; --",
    "\\' OR 1=1 --",
    "') OR ('1'='1",
]
LEAK_RE = re.compile(rb"sqlite_master|CREATE TABLE|syntax error|OperationalError|Traceback|no such (table|column)|unrecognized token", re.I)

# (route, {param: benign value}, string params to attack, key holding the rows / found flag)
GET_ROUTES: List[Tuple[str, Dict[str, str], List[str]]] = [
    ("/api/p3/status", {}, []),
    ("/api/p4/status", {}, []),
    ("/api/decomp/index", {}, []),
    ("/api/decomp/doc", {"name": "spine_map"}, ["name"]),
    ("/api/decomp/doc", {"name": "published_catalogue"}, []),
    ("/api/decomp/compute", {"limit": "5"}, ["q", "bucket"]),
    ("/api/trim", {}, []),
    ("/api/bundles", {"limit": "5"}, ["only", "sort", "q"]),
    ("/api/kernel/summary", {}, []),
    ("/api/kernel/decls", {"root": "union", "status": "live", "limit": "5"}, ["root", "q", "status"]),
    ("/api/kernel/dom", {"limit": "5"}, ["tree", "node"]),
    ("/api/kernel/dom_top", {"limit": "5"}, ["tree"]),
    ("/api/kernel/taint", {"limit": "5"}, ["kind", "root"]),
    ("/api/kernel/taint_path", {"id": "1"}, ["id"]),
    ("/api/kernel/decl", {"name": "Nat"}, ["name"]),
    ("/api/kernel/slice", {"name": "Nat", "depth": "1", "max_nodes": "10"}, ["name", "dir", "edge_kind", "stop_at", "stop_lib"]),
    ("/api/flirt/tier1", {"view": "misfile", "limit": "5"}, ["q", "view", "tier", "band", "kind"]),
    ("/api/flirt/tier2", {"limit": "5"}, ["q", "repo", "grade", "variant"]),
    ("/api/flirt/tier3", {"limit": "5"}, ["q"]),
    ("/api/flirt/clusters", {"limit": "5"}, ["q", "kind", "pillar"]),
    ("/api/flirt/atlas", {"limit": "5"}, ["status", "severity", "pillar", "q"]),
    ("/api/annot/layers", {}, []),
    ("/api/annot/view", {}, ["enabled"]),
    ("/api/annot/list", {"layer": "probe/human"}, ["layer", "q"]),
    ("/api/annot/for", {"name": "Probe.Decl"}, ["name"]),
    ("/api/annot/export", {"layer": "probe/human"}, ["layer"]),
]
INT_PARAMS = [("/api/kernel/decls", "limit"), ("/api/kernel/decls", "offset"), ("/api/kernel/dom", "limit"), ("/api/kernel/taint", "limit"),
              ("/api/kernel/taint_path", "id"), ("/api/kernel/slice", "depth"), ("/api/kernel/slice", "max_nodes"),
              ("/api/flirt/tier1", "limit"), ("/api/flirt/tier2", "offset"), ("/api/flirt/tier3", "limit"), ("/api/flirt/clusters", "limit"),
              ("/api/flirt/atlas", "limit"), ("/api/bundles", "limit"),
              ("/api/decomp/compute", "limit"), ("/api/annot/list", "limit")]


def url(route: str, params: Dict[str, str]) -> str:
    return route + ("?" + "&".join("%s=%s" % (k, quote(v, safe="")) for k, v in params.items()) if params else "")


def n_rows(obj: Any) -> int:
    if not isinstance(obj, dict):
        return 0
    n = 0
    for key in ("rows", "children", "nodes"):
        if isinstance(obj.get(key), list):
            n += len(obj[key])
    return n


def snapshot_analysis() -> Dict[str, Tuple[int, int, str]]:
    """size, mtime_ns (and sha256 when < 64 MB) of every analysis artefact the server reads."""
    out: Dict[str, Tuple[int, int, str]] = {}
    outputs = ROOT / "outputs"
    paths = [p for p in outputs.rglob("*") if p.is_file() or p.is_symlink()] if outputs.is_dir() else []
    for p in sorted(paths):
        try:
            real = p.resolve()
            st = real.stat()
        except OSError:
            continue
        digest = ""
        if st.st_size < 64 * 1024 * 1024:
            digest = hashlib.sha256(real.read_bytes()).hexdigest()
        out[str(p.relative_to(ROOT))] = (st.st_size, st.st_mtime_ns, digest)
    return out


def snapshot_tree(base: Path) -> Dict[str, Tuple[int, int]]:
    out: Dict[str, Tuple[int, int]] = {}
    if base.is_dir():
        for p in sorted(base.rglob("*")):
            if p.is_file():
                st = p.stat()
                out[str(p.relative_to(base))] = (st.st_size, st.st_mtime_ns)
    return out


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--port", type=int, required=True)
    ap.add_argument("--annotations", required=True, help="the scratch --annotations directory the server was started with")
    args = ap.parse_args()
    c = Client(args.port)
    ann_dir = Path(args.annotations).resolve()
    repo_ann = (ROOT / "annotations").resolve()
    if ann_dir == repo_ann:
        print("refusing to run write probes against the repository's annotations/ — start the server with a scratch --annotations dir")
        return 2

    st, status = c.get_json("/api/p3/status")
    if st != 200 or not isinstance(status, dict):
        print("server on port %d does not answer /api/p3/status" % args.port)
        return 2
    print("server state: " + ", ".join("%s=%s" % (k, v.get("state")) for k, v in status.items() if isinstance(v, dict)))
    if not status.get("annot", {}).get("selftest_writes"):
        print("server is not running on a scratch annotations dir (selftest_writes is false)")
        return 2

    before_analysis = snapshot_analysis()
    before_repo_ann = snapshot_tree(repo_ann)
    before_workbench = snapshot_tree(WORKBENCH)

    # ---------------------------------------------------------------- A
    print("\n== A. Phase 2 probes")
    st, obj = c.get_json("/api/search?q=" + quote("' OR 1=1 --"))
    check(st == 200 and isinstance(obj, dict) and len(obj.get("results", [])) == 0, "A1 SQLi on /api/search -> 200 with 0 results", "status %s" % st)
    for i, (path, want) in enumerate([("/../data/rh_mirror/src/Main.lean", (403,)), ("/%2e%2e/data/rh_mirror/src/Main.lean", (404,)), ("/../../../../etc/passwd", (403,))], 2):
        st, raw = c.get(path)
        check(st in want and b"theorem" not in raw and b"root:" not in raw, "A%d traversal GET %s -> %s" % (i, path, "/".join(map(str, want))), "status %s" % st)

    # a real layer + record so list/for/export routes have something to leak if they were injectable
    c.post("/api/annot/layer", {"layer": "probe/human", "kind": "human", "title": "probe"})
    st, obj = c.post("/api/annot/upsert", {"fields": {"target": "decl", "name": "Probe.Decl", "layer": "probe/human", "note": "probe note",
                                                         "tag": "L", "source": "probe", "author": "probe"}})
    check(st == 200, "setup: probe annotation written through the API", "status %s %s" % (st, obj if st != 200 else ""))
    rec = (obj or {}).get("record", {})

    # ---------------------------------------------------------------- B
    print("\n== B. SQL injection on every string parameter of every Phase 3 GET route")
    for route, base, attack in GET_ROUTES:
        st0, raw0 = c.get(url(route, base))
        ok0 = st0 == 200 and not LEAK_RE.search(raw0)
        check(ok0, "B  baseline GET %s -> 200" % url(route, base), "status %s" % st0)
        try:
            base_rows = n_rows(json.loads(raw0.decode("utf-8")))
        except Exception:
            base_rows = 0
        for param in attack:
            worst = None
            for payload in SQLI:
                params = dict(base)
                params[param] = payload
                st, raw = c.get(url(route, params))
                raw_no_echo = raw.replace(json.dumps(payload).encode("utf-8"), b"\"<echo>\"")
                bad = None
                if st >= 500:
                    bad = "status %d" % st
                elif st not in (200, 400, 404):
                    bad = "unexpected status %d" % st
                elif LEAK_RE.search(raw_no_echo):
                    bad = "error/schema text leaked"
                elif st == 200:
                    try:
                        obj = json.loads(raw.decode("utf-8"))
                    except Exception:
                        obj = None
                    if obj is not None and n_rows(obj) > 0 and param not in ("enabled", "stop_at"):
                        bad = "payload returned %d rows (baseline %d)" % (n_rows(obj), base_rows)
                    if isinstance(obj, dict) and obj.get("found") is True and param in ("node", "name", "id"):
                        bad = "payload was 'found'"
                if bad:
                    worst = "%r -> %s" % (payload, bad)
                    break
            check(worst is None, "B  %s ?%s= × %d SQLi payloads: 200-empty/400/404, no leak" % (route, param, len(SQLI)), worst or "")
    check(not Path("/tmp/leanre_probe_pwn.db").exists(), "B  ATTACH payload created no database file")

    # ---------------------------------------------------------------- C
    print("\n== C. malformed integers / enums")
    for route, param in INT_PARAMS:
        bad = []
        for val in ("abc", "1 OR 1=1", "1e9", "-", "9" * 40):
            st, _ = c.get(url(route, {param: val}))
            if st != 400:
                bad.append("%s -> %d" % (val, st))
        check(not bad, "C  %s ?%s=<garbage> -> 400" % (route, param), "; ".join(bad))
    for route, param in (("/api/kernel/decls", "status"), ("/api/kernel/slice", "dir"), ("/api/kernel/slice", "edge_kind"), ("/api/kernel/slice", "stop_lib"),
                         ("/api/decomp/doc", "name"), ("/api/bundles", "only"), ("/api/bundles", "sort"),
                         ("/api/flirt/tier1", "view"), ("/api/flirt/tier1", "tier"), ("/api/flirt/tier1", "band"), ("/api/flirt/tier1", "kind"),
                         ("/api/flirt/tier2", "grade"), ("/api/flirt/tier2", "variant"),
                         ("/api/flirt/atlas", "status"), ("/api/flirt/atlas", "severity")):
        st, _ = c.get(url(route, {param: "nope"}))
        check(st == 400, "C  %s ?%s=nope -> 400" % (route, param), "status %s" % st)
    for route in ("/api/kernel/nope", "/api/flirt/nope", "/api/annot/nope", "/api/p3/nope", "/api/p4/nope", "/api/decomp/nope", "/api/trim/nope", "/api/bundles/nope", "/api/nope"):
        st, _ = c.get(route)
        check(st == 404, "C  unknown route %s -> 404" % route, "status %s" % st)

    # ---------------------------------------------------------------- D
    print("\n== D. path traversal / source download")
    for path, want in [
        ("/../outputs/kernel/kernel.db", (403,)),
        ("/../annotations/human__canonical-facts.jsonl", (403,)),
        ("/%2e%2e/outputs/leanre.db", (404,)),
        ("/..%2foutputs%2fleanre.db", (403, 404)),
        ("/api/kernel/../../server.py", (403, 404)),
        ("/api/annot/export/../../../etc/passwd", (403, 404)),
        ("/server.py", (404,)),
        ("/phase3.py", (404,)),
        ("/phase4.py", (404,)),
        ("/p3_fixtures.py", (404,)),
        ("/probe_p3.py", (404,)),
        ("/api/decomp/doc?name=../../etc/passwd", (400,)),
        ("/api/decomp/doc?name=spine_map/../phase4.py", (400,)),
        ("/api/decomp/doc?name=trim_report", (400,)),
        ("/api/decomp/doc?name=compute_atlas", (400,)),
        ("/__pycache__/phase3.cpython-313.pyc", (404,)),
        ("/.git/config", (403, 404)),
        ("//etc/passwd", (403, 404)),
    ]:
        st, raw = c.get(path)
        leaked = b"import " in raw[:4000] or b"root:x:" in raw or raw[:15] == b"SQLite format 3"
        check(st in want and not leaked, "D  GET %s -> %s" % (path, "/".join(map(str, want))), "status %s" % st)
    for layer in ("../../etc/passwd", "..", "/etc/passwd", "probe/../../evil", "a\\..\\b", "probe/human/../../x", ".hidden", "x" * 300):
        st, raw = c.get(url("/api/annot/export", {"layer": layer}))
        check(st in (400, 404) and b"root:" not in raw, "D  export ?layer=%r -> 400/404" % layer[:28], "status %s" % st)
        st, obj = c.post("/api/annot/layer", {"layer": layer, "kind": "human"})
        check(st == 400, "D  create layer %r -> 400" % layer[:28], "status %s" % st)
        st, obj = c.post("/api/annot/upsert", {"fields": {"target": "decl", "name": "X", "layer": layer, "note": "n", "tag": "L", "source": "s", "author": "a"}})
        check(st in (400, 404), "D  upsert into layer %r -> 400/404" % layer[:28], "status %s" % st)
    st, obj = c.post("/api/annot/import", {"text": '{"schema":"leanre.annot/1","type":"pack"}\n{"default_on":true,"kind":"human","layer":"../../evil","title":"x","type":"layer"}\n'})
    check(st == 400, "D  import of a pack declaring layer '../../evil' -> 400", "status %s" % st)

    # ---------------------------------------------------------------- E
    print("\n== E. write gate")
    good = {"layer": "probe/gate", "kind": "human"}
    st, _ = c.post("/api/annot/layer", good, drop=["X-Leanre-Write"])
    check(st == 403, "E  POST without X-Leanre-Write -> 403", "status %s" % st)
    st, _ = c.post("/api/annot/layer", good, headers={"Origin": "http://evil.example"})
    check(st == 403, "E  POST with foreign Origin -> 403", "status %s" % st)
    st, _ = c.post("/api/annot/layer", good, host="evil.example")
    check(st == 403, "E  POST with foreign Host (DNS rebinding) -> 403", "status %s" % st)
    st, _ = c.post("/api/annot/layer", good, headers={"Origin": "null"})
    check(st == 403, "E  POST with Origin: null -> 403", "status %s" % st)
    for path in ("/api/kernel/summary", "/api/flirt/tier1", "/api/flirt/atlas", "/api/search", "/index.html", "/api/p3/status", "/api/trim", "/api/bundles", "/api/decomp/index"):
        st, _ = c.post(path, {})
        check(st == 404, "E  POST %s -> 404 (only /api/annot/* accepts writes)" % path, "status %s" % st)
    for method in ("PUT", "DELETE", "PATCH"):
        st, _ = c.req(method, "/api/annot/layer", body=b"{}", headers={"X-Leanre-Write": "1", "Content-Type": "application/json"})
        check(st in (405, 501), "E  %s /api/annot/layer -> 405/501" % method, "status %s" % st)
    st, _ = c.req("POST", "/api/annot/layer", body=None, headers={"X-Leanre-Write": "1", "Content-Length": str(64 * 1024 * 1024)})
    check(st == 413, "E  POST declaring a 64 MB body -> 413", "status %s" % st)
    st, _ = c.post("/api/annot/layer", b"not json")
    check(st == 400, "E  POST with a non-JSON body -> 400", "status %s" % st)
    check(not (ann_dir / "probe__gate.jsonl").exists(), "E  none of the refused requests created a layer file")

    # ---------------------------------------------------------------- F
    print("\n== F. write confinement / read-only analysis data")
    produced = snapshot_tree(ann_dir)
    check("probe__human.jsonl" in produced, "F  accepted write landed in --annotations (%s)" % ann_dir, ", ".join(sorted(produced)))
    check(all(re.fullmatch(r"[a-z0-9._-]+\.jsonl", n) for n in produced), "F  --annotations contains only flat <layer>.jsonl files", ", ".join(sorted(produced)))
    if rec.get("id"):
        st, _ = c.post("/api/annot/delete", {"id": rec["id"], "expect_updated": rec.get("updated", "")})
        check(st == 200, "F  cleanup: probe annotation deleted through the API", "status %s" % st)
    after_analysis = snapshot_analysis()
    changed = sorted(k for k in set(before_analysis) | set(after_analysis) if before_analysis.get(k) != after_analysis.get(k))
    check(not changed, "F  every file under outputs/ unchanged (size, mtime_ns, sha256<64MB): %d files" % len(after_analysis),
          ("changed (another worker rebuilding?): " + ", ".join(changed[:6])) if changed else "")
    check(snapshot_tree(repo_ann) == before_repo_ann, "F  repository annotations/ untouched while serving a scratch dir")
    wb_after = snapshot_tree(WORKBENCH)
    wb_changed = sorted(k for k in set(before_workbench) | set(wb_after) if before_workbench.get(k) != wb_after.get(k) and "__pycache__" not in k)
    check(not wb_changed, "F  workbench/ untouched by the server", ", ".join(wb_changed[:6]))

    # ---------------------------------------------------------------- G
    print("\n== G. static audit")
    ext = []
    for p in sorted(WORKBENCH.glob("*")):
        if p.suffix not in (".html", ".js", ".css"):
            continue
        for ln, line in enumerate(p.read_text(encoding="utf-8").splitlines(), 1):
            for m in re.finditer(r"""(?:src|href|action)\s*=\s*["'](https?:)?//[^"']+|url\(\s*["']?(?:https?:)?//|@import\s+["'](?:https?:)?//|(?:fetch|import|importScripts)\(\s*["'](?:https?:)?//|new\s+WebSocket\(""", line):
                frag = m.group(0)
                if "127.0.0.1" in frag or "localhost" in frag:
                    continue
                ext.append("%s:%d %s" % (p.name, ln, frag[:60]))
    check(not ext, "G  zero external resource loads in workbench/*.html|js|css (no CDN)", "; ".join(ext[:5]))
    connects = []
    for p in sorted(WORKBENCH.glob("*.py")):
        if p.name == "probe_p3.py":
            continue
        for ln, line in enumerate(p.read_text(encoding="utf-8").splitlines(), 1):
            if "sqlite3.connect(" in line and not line.lstrip().startswith("#"):
                ro = "mode=ro" in line or "mode=memory" in line or "_FX_KERNEL_URI" in line or re.search(r"connect\(uri,\s*uri=True", line)
                connects.append((p.name, ln, bool(ro), line.strip()[:90]))
    not_ro = ["%s:%d %s" % (a, b, d) for a, b, ro, d in connects if not ro]
    check(connects and not not_ro, "G  every sqlite3.connect in workbench/*.py is mode=ro or in-memory (%d call sites)" % len(connects), "; ".join(not_ro))
    writes = []
    for p in sorted(WORKBENCH.glob("*.py")):
        if p.name == "probe_p3.py":
            continue
        for ln, line in enumerate(p.read_text(encoding="utf-8").splitlines(), 1):
            if re.search(r"""\.write_text\(|\.write_bytes\(|open\([^)]*["'][wax]b?\+?["']|os\.(remove|unlink|rename|replace|makedirs|mkdir)\(|shutil\.|\.mkdir\(|\.unlink\(|subprocess|os\.system""", line):
                writes.append("%s:%d %s" % (p.name, ln, line.strip()[:70]))
    check(not writes, "G  no file-writing / process-spawning call in workbench/*.py (writes only via leanre/annot.py PackStore)", "; ".join(writes[:5]))
    src = (WORKBENCH / "server.py").read_text(encoding="utf-8")
    check('"--host", default="127.0.0.1"' in src, "G  server binds 127.0.0.1 by default")

    fails = [r for r in RESULTS if not r[0]]
    print("\nPROBE SUMMARY: %d checks, %d failed" % (len(RESULTS), len(fails)))
    for _, name, detail in fails:
        print("  FAILED: %s [%s]" % (name, detail))
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
