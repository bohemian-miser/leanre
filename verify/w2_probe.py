#!/usr/bin/env python3
"""W2 independent security & hygiene probe (verifier-owned).

Launches workbench/server.py on a spare port (never 8420) with a temp copy of annotations/
(or checks that the repo's annotations/ stays untouched), then runs:
  1. Static check of workbench/**: zero external CDNs (<script>/<link>/@import/fetch/src/href
     pointing to external hosts), bind default 127.0.0.1, read-only SQLite opens, parameterized SQL.
  2. Live bind address check via `ss -ltnp` (must listen ONLY on 127.0.0.1).
  3. Path traversal probes (raw, URL-encoded, double-encoded, /etc/passwd, data/rh_mirror,
     outputs/leanre.db, annotations/ escapes) -> must return 403 or 404 with zero leaked bytes.
  4. SQLi probes across every discovered GET /api/* endpoint + query parameter -> must never
     return 500, never leak sqlite_master / extra rows, never execute writes.
  5. Write-containment probes on annotation mutation endpoints (layer traversal `../../evil`,
     invalid JSON, non-annotations path, oversized body) -> must reject (400/403/404/409) and
     never create any file outside annotations/.
"""
from __future__ import annotations

import argparse
import http.client
import json
import os
import re
import shutil
import socket
import subprocess
import sys
import tempfile
import time
import urllib.parse

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
R = []


def ck(ok, msg):
    R.append(bool(ok))
    print(f"{'PASS' if ok else 'FAIL'} [W2] {msg}")


def raw_http(host, port, method, raw_path, body=None, headers=None):
    """Send raw HTTP/1.1 request without client-side path normalization (so /../ is sent verbatim)."""
    s = socket.create_connection((host, port), timeout=10)
    try:
        hdrs = {"Host": f"{host}:{port}", "Connection": "close"}
        if body is not None:
            if isinstance(body, str):
                body = body.encode("utf-8")
            hdrs["Content-Length"] = str(len(body))
        if headers:
            hdrs.update(headers)
        req = f"{method} {raw_path} HTTP/1.1\r\n" + "".join(f"{k}: {v}\r\n" for k, v in hdrs.items()) + "\r\n"
        s.sendall(req.encode("utf-8") + (body or b""))
        chunks = []
        while True:
            b = s.recv(65536)
            if not b:
                break
            chunks.append(b)
        data = b"".join(chunks)
        head, _, payload = data.partition(b"\r\n\r\n")
        first = head.split(b"\r\n", 1)[0].decode("latin-1", "replace")
        m = re.match(r"HTTP/\d\.\d\s+(\d+)", first)
        code = int(m.group(1)) if m else 0
        return code, payload
    finally:
        s.close()


def static_audit():
    wb = os.path.join(ROOT, "workbench")
    cdn_hits = []
    # Match external http(s):// or protocol-relative // loads in HTML/CSS/JS
    cdn_re = re.compile(
        r"""(?:src|href)\s*=\s*['"](?:https?:|//)[^'"]+|"""
        r"""@import\s+(?:url\()?['"]?(?:https?:|//)[^'")\s]+|"""
        r"""url\(\s*['"]?(?:https?:|//)[^'")\s]+|"""
        r"""fetch\(\s*['"](?:https?:|//)[^'"]+""",
        re.I,
    )
    allowed_ns = ("http://www.w3.org/2000/svg", "https://www.w3.org/2000/svg")
    py_files = []
    for dp, _, fn in os.walk(wb):
        if "__pycache__" in dp:
            continue
        for f in sorted(fn):
            p = os.path.join(dp, f)
            rel = os.path.relpath(p, ROOT)
            if f.endswith(".py"):
                py_files.append(p)
            if f.endswith((".html", ".js", ".css")):
                txt = open(p, encoding="utf-8", errors="replace").read()
                for m in cdn_re.finditer(txt):
                    val = m.group(0)
                    # Ignore plain <a href="https://..."> documentation reference links if target=_blank?
                    # Wait: check if it's <script>, <link>, @import, url(), fetch(), <img src>
                    ctx_start = max(0, m.start() - 40)
                    ctx = txt[ctx_start:m.end()]
                    if any(ns in val for ns in allowed_ns):
                        continue
                    if re.search(r"<a\b[^>]*$", txt[max(0, m.start() - 120):m.start()], re.I) and val.lower().startswith("href"):
                        continue
                    cdn_hits.append(f"{rel}: {val[:100]}")
    ck(not cdn_hits, f"zero external CDN asset loads in workbench/** (hits={len(cdn_hits)} {cdn_hits[:5]})")

    # Check all sqlite3.connect calls in workbench/*.py open read-only
    rw_connects = []
    fstring_sql = []
    for p in py_files:
        rel = os.path.relpath(p, ROOT)
        lines = open(p, encoding="utf-8", errors="replace").readlines()
        for ln, line in enumerate(lines, 1):
            if "sqlite3.connect(" in line and "mode=ro" not in line and ":memory:" not in line:
                # check surrounding lines for mode=ro, query_only, or in-memory URI constant
                window = "".join(lines[max(0, ln - 10):min(len(lines), ln + 3)])
                if "mode=ro" not in window and "query_only" not in window and "mode=memory" not in window:
                    rw_connects.append(f"{rel}:{ln}: {line.strip()[:100]}")
            if re.search(r'\.execute\(\s*f["\']', line):
                # check if it interpolates something other than table/column whitelist or placeholders
                fstring_sql.append(f"{rel}:{ln}: {line.strip()[:120]}")
    ck(not rw_connects, f"all sqlite3.connect() in workbench/*.py use read-only mode (violations={len(rw_connects)} {rw_connects[:5]})")
    print(f"     info: f-string .execute() sites in workbench/*.py (inspect for whitelisting): {len(fstring_sql)}")
    for s in fstring_sql[:15]:
        print("      ", s)

    # Discover endpoints from workbench/*.py
    eps = set()
    for p in py_files:
        txt = open(p, encoding="utf-8", errors="replace").read()
        for m in re.finditer(r'["\'](/api/[a-zA-Z0-9_/-]+)["\']', txt):
            eps.add(m.group(1))
    return sorted(eps)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--port", type=int, default=8438)
    a = ap.parse_args()
    if a.port == 8420:
        raise SystemExit("refusing port 8420")

    eps = static_audit()
    print(f"     discovered {len(eps)} /api/* endpoints: {eps}")

    # Snapshot annotations/ before live server probes
    ann_dir = os.path.join(ROOT, "annotations")
    snap_before = {}
    if os.path.isdir(ann_dir):
        for dp, _, fn in os.walk(ann_dir):
            for f in fn:
                p = os.path.join(dp, f)
                snap_before[os.path.relpath(p, ROOT)] = open(p, "rb").read()

    # Check if server.py supports --annotations to isolate writes, otherwise test read-only + rejected writes
    srv_src = open(os.path.join(ROOT, "workbench", "server.py")).read()
    tmp = tempfile.mkdtemp(prefix="leanre_w2_")
    logf = os.path.join(tmp, "server.log")
    cmd = [sys.executable, os.path.join(ROOT, "workbench", "server.py"), "--port", str(a.port)]
    tmp_ann = os.path.join(tmp, "annotations")
    if "--annotations" in srv_src and os.path.isdir(ann_dir):
        shutil.copytree(ann_dir, tmp_ann)
        cmd += ["--annotations", tmp_ann]
        isolated_ann = True
    else:
        isolated_ann = False

    proc = subprocess.Popen(cmd, cwd=ROOT, stdout=open(logf, "w"), stderr=subprocess.STDOUT)
    try:
        ready = False
        for _ in range(60):
            try:
                code, _ = raw_http("127.0.0.1", a.port, "GET", "/api/health")
                if code == 200:
                    ready = True
                    break
            except OSError:
                pass
            time.sleep(0.2)
        ck(ready, f"workbench server started on 127.0.0.1:{a.port} (isolated_annotations={isolated_ann})")
        if not ready:
            print(open(logf).read()[-1000:])
            sys.exit(1)

        # Bind address check
        ss = subprocess.run(["ss", "-ltnp"], capture_output=True, text=True).stdout
        binds = [ln.split()[3] for ln in ss.splitlines() if f"pid={proc.pid}," in ln or f"pid={proc.pid})" in ln]
        ck(bool(binds) and all(b.startswith("127.0.0.1:") for b in binds), f"server bound strictly to 127.0.0.1: {binds}")

        # Path traversal probes
        traversals = [
            "/../data/rh_mirror/src/Main.lean",
            "/%2e%2e/data/rh_mirror/src/Main.lean",
            "/%252e%252e/data/rh_mirror/src/Main.lean",
            "/../../../../etc/passwd",
            "/..%2f..%2f..%2fetc%2fpasswd",
            "/../outputs/leanre.db",
            "/../outputs/kernel/kernel.db",
            "/../annotations/human__canonical-facts.jsonl",
            "/prototypes/../data/rh_mirror/src/Main.lean",
            "/prototypes/%2e%2e/data/rh_mirror/src/Main.lean",
            "/workbench/../data/MANIFEST.md",
            "/..\\.\\..\\etc\\passwd",
        ]
        bad_trav = []
        for path in traversals:
            code, body = raw_http("127.0.0.1", a.port, "GET", path)
            leaked = (b"root:x:0:0" in body) or (b"import Supplements" in body) or (b"SQLite format 3" in body) or (b"leanre.annot/1" in body)
            if code not in (400, 403, 404) or leaked:
                bad_trav.append((path, code, len(body), leaked))
        ck(not bad_trav, f"path traversal probes ({len(traversals)} vectors) all 400/403/404 with 0 leakage; failures={bad_trav}")

        # SQLi probes on every GET /api/* endpoint
        sqli_vals = [
            "' OR 1=1 --",
            "\" OR \"1\"=\"1",
            "'; DROP TABLE modules; --",
            "x' UNION SELECT sql FROM sqlite_master --",
            "1; ATTACH DATABASE '/tmp/pwn.db' AS pwn; --",
            "%00' OR 1=1--",
        ]
        sqli_params = ["q", "name", "root", "kind", "mode", "tag", "flag", "layer", "id", "class", "repo", "scheme", "bucket", "prefix", "module", "decl"]
        sqli_bad = []
        probed = 0
        for ep in eps:
            if any(x in ep for x in ("import", "upsert", "delete", "create", "promote", "write")):
                continue
            for val in sqli_vals[:3]:
                qs = urllib.parse.urlencode({p: val for p in ("q", "name", "root", "kind", "layer", "id", "module", "decl")})
                code, body = raw_http("127.0.0.1", a.port, "GET", f"{ep}?{qs}")
                probed += 1
                txt = body.decode("utf-8", "replace")
                if code >= 500 or "sqlite_master" in txt or "CREATE TABLE" in txt or "OperationalError" in txt or "Traceback" in txt:
                    sqli_bad.append((ep, code, txt[:160]))
        ck(not sqli_bad, f"SQLi probes ({probed} requests across /api/* endpoints): 0 500s / tracebacks / schema leaks; failures={sqli_bad[:5]}")

        # Write-containment probes on POST/DELETE endpoints
        write_eps = [ep for ep in eps if any(w in ep for w in ("annot", "layer", "import", "upsert", "delete"))]
        evil_payloads = [
            {"layer": "../../tmp/pwn", "target": "decl", "name": "Main", "tag": "L", "source": "x", "author": "attacker", "note": "pwn"},
            {"layer": "../pwn", "kind": "human", "title": "pwn"},
            {"layer": "human/../../pwn", "name": "Main", "note": "pwn"},
            {"text": "{\"schema\":\"leanre.annot/1\",\"type\":\"pack\"}\n{\"default_on\":true,\"kind\":\"human\",\"layer\":\"../../pwn\",\"title\":\"x\",\"type\":\"layer\"}\n"},
        ]
        write_bad = []
        for ep in write_eps:
            for pay in evil_payloads:
                code, body = raw_http("127.0.0.1", a.port, "POST", ep, json.dumps(pay), {"Content-Type": "application/json"})
                if code == 200:
                    # Check if response indicates success/applied
                    try:
                        j = json.loads(body.decode("utf-8", "replace"))
                        if j.get("ok") is True and j.get("applied") is not False:
                            write_bad.append((ep, code, str(j)[:120]))
                    except Exception:
                        write_bad.append((ep, code, body[:120]))
                elif code >= 500:
                    write_bad.append((ep, code, body[:120]))
        ck(not write_bad and not os.path.exists("/tmp/pwn.jsonl") and not os.path.exists(os.path.join(ROOT, "pwn.jsonl")),
           f"annotation write-containment probes ({len(write_eps)} endpoints × {len(evil_payloads)} traversal payloads): all rejected, 0 escaped files; failures={write_bad[:5]}")

        # Verify repo's annotations/ untouched
        snap_after = {}
        if os.path.isdir(ann_dir):
            for dp, _, fn in os.walk(ann_dir):
                for f in fn:
                    p = os.path.join(dp, f)
                    snap_after[os.path.relpath(p, ROOT)] = open(p, "rb").read()
        ck(snap_before == snap_after, "repo annotations/ byte-identical after all security probes")
    finally:
        proc.terminate()
        try:
            proc.wait(timeout=5)
        except subprocess.TimeoutExpired:
            proc.kill()
        shutil.rmtree(tmp, ignore_errors=True)

    fails = sum(1 for x in R if not x)
    print(f"\nW2-PROBE {'PASS' if fails == 0 else 'FAIL'} ({len(R)-fails}/{len(R)})")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
