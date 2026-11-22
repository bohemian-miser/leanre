#!/usr/bin/env python3
"""K2–K6 cross-check of outputs/kernel/kernel.db (schema v1) against the verifier's own
independent C++ oracle (verify/oracle_ndjson.cpp output).
Nothing here trusts a kernel.db derived column: every derived quantity is recomputed from
the VERIFIER's edges. Dominator trees are cross-checked by verify/out/dom_oracle (C++
exhaustive parent-property + parallel node-removal brute force, <=16 threads).

Usage:
  python3 verify/kernel_db_check.py --db outputs/kernel/kernel.db \
      --oracle verify/out/solution_oracle --samples 1200 --procs 16
"""
from __future__ import annotations

import argparse
import collections
import json
import os
import random
import sqlite3
import subprocess
import sys
import tempfile

import numpy as np

KINDS = ["thm", "def", "opaque", "axiom", "quot", "inductive"]
ROOTS = [
    "riemannHypothesis",
    "riemannZeta_eq_zero_re",
    "LFunction_ne_zero_of_half_lt_re",
    "LFunction_eq_zero_re",
    "LFunction_eq_zero_re_of_isPrimitive",
]
RESULTS = []


def rec(gate, ok, msg):
    RESULTS.append((gate, bool(ok)))
    print(f"{'PASS' if ok else 'FAIL'} [{gate}] {msg}", flush=True)


class CSR:
    """Memory-efficient CSR over sorted (src, dst) arrays, with optional kind array."""

    def __init__(self, n, src, dst, kind=None):
        self.n = n
        self.idx = dst.astype(np.int32, copy=False)
        self.kind = kind.astype(np.int8, copy=False) if kind is not None else None
        self.ptr = np.zeros(n + 1, np.int64)
        np.cumsum(np.bincount(src, minlength=n), out=self.ptr[1:])

    def lookup_kind(self, u: int, v: int) -> int:
        """Return edge kind (1/2/3) for u->v, or 0 if absent. Requires dst sorted per src."""
        lo, hi = int(self.ptr[u]), int(self.ptr[u + 1])
        pos = int(np.searchsorted(self.idx[lo:hi], v))
        if pos < hi - lo and int(self.idx[lo + pos]) == v:
            return int(self.kind[lo + pos]) if self.kind is not None else 1
        return 0

    def nbrs(self, fr):
        s = self.ptr[fr]
        l = self.ptr[fr + 1] - s
        tot = int(l.sum())
        if tot == 0:
            return np.empty(0, np.int32)
        off = np.repeat(s - (np.cumsum(l) - l), l) + np.arange(tot)
        return self.idx[off]

    def bfs(self, roots, depth=False):
        vis = np.zeros(self.n, bool)
        fr = np.array(list(roots), np.int64)
        vis[fr] = True
        dep = np.full(self.n, -1, np.int32) if depth else None
        d = 0
        while fr.size:
            if depth:
                dep[fr] = d
            nb = self.nbrs(fr)
            nb = nb[~vis[nb]]
            fr = np.unique(nb)
            vis[fr] = True
            d += 1
        return (vis, dep) if depth else vis


def load_oracle(prefix):
    nm = json.load(open(prefix + ".names.json"))
    src = np.fromfile(prefix + ".src.i32", np.int32)
    dst = np.fromfile(prefix + ".dst.i32", np.int32)
    kind = np.fromfile(prefix + ".kind.i8", np.int8)
    rec_kind = np.fromfile(prefix + ".rec_kind.i8", np.int8)
    n_consts = np.fromfile(prefix + ".n_consts.i32", np.int32)
    return dict(src=src, dst=dst, kind=kind, rec_kind=rec_kind, n_consts=n_consts,
                names=nm["rec_names"], const_to_rec=nm["const_to_rec"])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--db", required=True)
    ap.add_argument("--oracle", required=True)
    ap.add_argument("--leanre-db", default="outputs/leanre.db")
    ap.add_argument("--samples", type=int, default=1200)
    ap.add_argument("--procs", type=int, default=16)
    ap.add_argument("--seed", type=int, default=20261122)
    ap.add_argument("--skip-dom", action="store_true")
    a = ap.parse_args()

    db = sqlite3.connect(f"file:{a.db}?mode=ro", uri=True)
    o = load_oracle(a.oracle)
    n = len(o["names"])
    m = len(o["src"])
    ix = {nm: i for i, nm in enumerate(o["names"])}
    roots = [ix[r] for r in ROOTS]
    names = o["names"]
    rk = o["rec_kind"]
    print(f"oracle: {n:,} records, {m:,} edges; kernel.db tables: "
          + ", ".join(r[0] for r in db.execute("SELECT name FROM sqlite_master WHERE type IN ('table','view') ORDER BY 1")),
          flush=True)

    # ---- K2/K3: decls identical (id, name, kind, n_consts)
    kd = db.execute("SELECT id, name, kind, n_consts FROM decls ORDER BY id").fetchall()
    bad_d = 0
    if len(kd) == n:
        for idx_i, (i, nm, k, nc) in enumerate(kd):
            if i != idx_i or nm != names[idx_i] or k != KINDS[rk[idx_i]] or nc != int(o["n_consts"][idx_i]):
                bad_d += 1
    else:
        bad_d = -1
    rec("K2/K3", len(kd) == n and bad_d == 0,
        f"decls: kernel.db {len(kd):,} vs oracle {n:,}; (id,name,kind,n_consts) mismatches={bad_d}")

    # ---- K2: consts identical
    nc_rows = db.execute("SELECT COUNT(*) FROM consts").fetchone()[0]
    cbad = 0
    for nm, did in db.execute("SELECT name, decl_id FROM consts"):
        if o["const_to_rec"].get(nm) != did:
            cbad += 1
    rec("K2", nc_rows == len(o["const_to_rec"]) == int(o["n_consts"].sum()) and cbad == 0,
        f"consts: kernel.db={nc_rows:,} oracle={int(o['n_consts'].sum()):,} (distinct {len(o['const_to_rec']):,}); name->decl_id mismatches={cbad}")

    # ---- K3/E: edges identical set-for-set incl. kind (streaming in chunks; WITHOUT ROWID PK(src,dst) is sorted!)
    cur = db.execute("SELECT src, dst, kind FROM edges ORDER BY src, dst")
    pos = 0
    mism = 0
    extra_rows = 0
    CHUNK = 1_000_000
    while True:
        rows = cur.fetchmany(CHUNK)
        if not rows:
            break
        k_arr = np.asarray(rows, dtype=np.int32)
        ln = len(rows)
        if pos + ln > m:
            extra_rows += (pos + ln) - m
            ln_ok = max(0, m - pos)
        else:
            ln_ok = ln
        if ln_ok > 0:
            s_ok = (k_arr[:ln_ok, 0] == o["src"][pos:pos + ln_ok])
            d_ok = (k_arr[:ln_ok, 1] == o["dst"][pos:pos + ln_ok])
            k_ok = (k_arr[:ln_ok, 2] == o["kind"][pos:pos + ln_ok])
            mism += int((~(s_ok & d_ok & k_ok)).sum())
        pos += ln
    rec("K3/E", pos == m and mism == 0 and extra_rows == 0,
        f"edges: kernel.db {pos:,} vs oracle {m:,} (streamed sorted compare); mismatches={mism} extra={extra_rows}")

    # Build CSRs (already sorted by src, dst from oracle_ndjson.cpp!)
    full = CSR(n, o["src"], o["dst"], o["kind"])

    # ---- K4: roots + live_mask + stmt_mask + axioms + sorryAx + reach
    kroots = db.execute("SELECT id, name, decl_id FROM roots ORDER BY id").fetchall()
    rec("K4", [r[1] for r in kroots] == ROOTS and [r[2] for r in kroots] == roots, f"roots table = {kroots}")

    live = np.zeros(n, np.int64)
    stmt = np.zeros(n, np.int64)
    proof_deps = {}
    for r, rid in enumerate(roots):
        lv, ld = full.bfs([rid], depth=True)
        keep = ~((o["src"] == rid) & (o["kind"] == 2))
        sv = CSR(n, o["src"][keep], o["dst"][keep]).bfs([rid])
        live |= lv.astype(np.int64) << r
        stmt |= sv.astype(np.int64) << r
        proof_deps[r] = ld
    km = np.asarray(db.execute("SELECT live_mask, stmt_mask FROM decls ORDER BY id").fetchall(), dtype=np.int64)
    okl = bool((km[:, 0] == live).all())
    oks = bool((km[:, 1] == stmt).all())
    rec("K4", okl, f"live_mask exact across all {n:,} decls: {okl} (mismatches={int((km[:,0]!=live).sum())})")
    rec("K4", oks, f"stmt_mask exact across all {n:,} decls: {oks} (mismatches={int((km[:,1]!=stmt).sum())})")

    # Axioms view check
    ax_db = sorted(r[0] for r in db.execute("SELECT name FROM axioms"))
    ax_or = sorted(names[i] for i in np.nonzero(rk == KINDS.index("axiom"))[0])
    rec("K4", ax_db == ax_or == ["Classical.choice", "Quot.sound", "propext"],
        f"axioms view = {ax_db} (oracle = {ax_or}; sorryAx absent={('sorryAx' not in ix)})")

    # Verify reach table (all 5 roots) against oracle depths + edges
    for r, rid in enumerate(roots):
        rows = db.execute("SELECT decl_id, depth, parent FROM reach WHERE root_id=?", (r,)).fetchall()
        ld = proof_deps[r]
        exp_n = int((ld >= 0).sum())
        bad_dep = 0
        bad_edge = 0
        bad_pdep = 0
        for did, dep, par in rows:
            if int(ld[did]) != dep:
                bad_dep += 1
            if par is None:
                if did != rid or dep != 0:
                    bad_pdep += 1
            else:
                if full.lookup_kind(par, did) == 0:
                    bad_edge += 1
                if int(ld[par]) + 1 != dep:
                    bad_pdep += 1
        rec("K4", len(rows) == exp_n and bad_dep == 0 and bad_edge == 0 and bad_pdep == 0,
            f"reach[{ROOTS[r]}]: rows={len(rows):,} == oracle {exp_n:,}; bad_dep={bad_dep} bad_edge={bad_edge} bad_pdep={bad_pdep}")

    # ---- K5: taint_paths edge-by-edge vs ORACLE edges
    t_rows = db.execute("SELECT source_id, root_id, hop, decl_id, edge_kind FROM taint_paths ORDER BY source_id, root_id, hop").fetchall()
    srcs = {r[0]: r for r in db.execute("SELECT id, class, decl_id, origin, module, detail FROM taint_sources")}
    paths = collections.defaultdict(list)
    for sid, rid, hop, did, ek in t_rows:
        paths[(sid, rid)].append((hop, did, ek))
    perr = []
    cls_counts = collections.Counter()
    for (sid, rid), hops in paths.items():
        cls_counts[srcs[sid][1]] += 1
        if [h[0] for h in hops] != list(range(len(hops))):
            perr.append(f"{sid}/{rid}: non-contiguous hops")
            continue
        if hops[0][1] != roots[rid]:
            perr.append(f"{sid}/{rid}: hop0 {hops[0][1]} != root {roots[rid]}")
        if hops[-1][1] != srcs[sid][2]:
            perr.append(f"{sid}/{rid}: last {hops[-1][1]} != src {srcs[sid][2]}")
        for (h0, d0, _), (h1, d1, ek) in zip(hops, hops[1:]):
            ok_kind = full.lookup_kind(d0, d1)
            if ok_kind == 0:
                perr.append(f"{sid}/{rid}: MISSING edge {names[d0]} -> {names[d1]}")
            elif ek is not None and ok_kind != ek:
                perr.append(f"{sid}/{rid}: edge kind {ek} != oracle {ok_kind} on {names[d0]}->{names[d1]}")
    rec("K5", len(paths) > 0 and not perr,
        f"taint_paths: {len(paths):,} paths / {len(t_rows):,} hops validated edge-by-edge vs ORACLE edges; errors={len(perr)} {perr[:3]}; classes={dict(cls_counts)}")
    src_cls = collections.Counter(s[1] for s in srcs.values())
    print(f"     taint_sources={len(srcs):,} by class={dict(src_cls)}", flush=True)

    # ---- K5: dominator trees via independent C++ dom_oracle
    if not a.skip_dom:
        dom_bin = os.path.join(os.path.dirname(os.path.abspath(__file__)), "out", "dom_oracle")
        trees = db.execute("SELECT id, label, view, root_ids, n_nodes FROM dom_trees ORDER BY id").fetchall()
        for tid, label, view, root_ids, n_nodes in trees:
            rl = [roots[int(x)] for x in (json.loads(root_ids) if str(root_ids).strip().startswith("[") else str(root_ids).split(","))]
            rows = db.execute("SELECT decl_id, COALESCE(idom, -1), subtree_size FROM dom WHERE tree_id=?", (tid,)).fetchall()
            arr = np.asarray(rows, dtype=np.int32)
            with tempfile.NamedTemporaryFile(suffix=".bin", delete=False) as tf:
                arr.tofile(tf)
                tpath = tf.name
            try:
                cmd = [dom_bin, a.oracle, tpath, view, ",".join(map(str, rl)), str(a.samples), str(a.seed + tid), str(a.procs)]
                cp = subprocess.run(cmd, capture_output=True, text=True)
                res_line = next((l for l in cp.stdout.splitlines() if l.startswith("RESULT ")), cp.stdout[-200:])
                rec("K5", cp.returncode == 0 and len(rows) == n_nodes,
                    f"dom tree '{label}' ({view}, n_nodes={n_nodes:,}): {res_line}")
                for tl in cp.stdout.splitlines():
                    if tl.startswith(("ERR ", "TOP ")):
                        if tl.startswith("TOP "):
                            parts = tl.split()
                            did = int(parts[1])
                            print(f"       top {names[did]} ({parts[2]} {parts[3]})", flush=True)
                        else:
                            print("      ", tl, flush=True)
            finally:
                os.unlink(tpath)

    # ---- K6: decl_module alignment accounting + spot-checks against leanre.db & rh_mirror
    dm_rows = db.execute("SELECT decl_id, module, method, src_decl_id FROM decl_module").fetchall()
    meth = collections.Counter(r[2] for r in dm_rows)
    null_matched = sum(1 for r in dm_rows if r[1] is None and not str(r[2]).startswith("unmatched"))
    mod_unmatched = sum(1 for r in dm_rows if r[1] is not None and str(r[2]).startswith("unmatched"))
    matched_n = sum(1 for r in dm_rows if r[1] is not None)
    unmatched_n = sum(1 for r in dm_rows if r[1] is None)
    rec("K6", len(dm_rows) == n and len({r[0] for r in dm_rows}) == n and null_matched == 0 and mod_unmatched == 0,
        f"decl_module: rows={len(dm_rows):,} == decls {n:,}; matched={matched_n:,} ({100*matched_n/n:.2f}%) unmatched={unmatched_n:,} ({100*unmatched_n/n:.2f}%); invariant_viol={null_matched+mod_unmatched}")
    print(f"     decl_module methods: {dict(meth.most_common())}", flush=True)
    if os.path.exists(a.leanre_db):
        ldb = sqlite3.connect(f"file:{a.leanre_db}?mode=ro", uri=True)
        mods = {r[0] for r in ldb.execute("SELECT name FROM modules")}
        badmod = sum(1 for r in dm_rows if r[1] is not None and r[1] not in mods)
        rec("K6", badmod == 0, f"decl_module modules absent from outputs/leanre.db: {badmod}")
        rnd = random.Random(a.seed)
        matched_rows = [r for r in dm_rows if r[1] is not None]
        spot = rnd.sample(matched_rows, min(200, len(matched_rows)))
        disk_ok = 0
        disk_miss = []
        root_dir = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
        for did, mod, mth, _ in spot:
            fp = os.path.join(root_dir, "data", "rh_mirror", "src", mod.replace(".", "/") + ".lean")
            if not os.path.exists(fp):
                disk_miss.append((names[did], mod, mth, "missing_file"))
                continue
            txt = open(fp, encoding="utf-8", errors="replace").read()
            kname = names[did]
            parts = kname.split(".")
            if parts[0] == "_private" and "0" in parts[1:]:
                kname = ".".join(parts[parts.index("0", 1) + 1:])
            segs = [s for s in kname.split(".") if not s.startswith(("_proof_", "match_", "eq_", "inj", "mk", "rec", "casesOn", "recOn", "noConfusion", "sizeOf"))]
            leaf = segs[-1] if segs else kname.split(".")[-1]
            if leaf in txt or any(s in txt for s in reversed(segs[-3:])):
                disk_ok += 1
            else:
                disk_miss.append((names[did], mod, mth, leaf))
        rec("K6", len(disk_miss) <= 5,
            f"decl_module on-disk spot check (200 sampled matched decls in data/rh_mirror): found={disk_ok}/200 misses={len(disk_miss)} {disk_miss[:5]}")

    # ---- Meta
    meta = {k: json.loads(v) for k, v in db.execute("SELECT key, value_json FROM meta")}
    print("     meta keys:", sorted(meta), flush=True)
    for k in ("input", "counts", "timings", "schema_version", "lexicon_id", "sighash_lexicon_id"):
        if k in meta:
            print(f"     meta[{k}]:", json.dumps(meta[k], ensure_ascii=False)[:300], flush=True)

    fails = [g for g, ok in RESULTS if not ok]
    print(f"\nKERNEL-DB-CHECK {'PASS' if not fails else 'FAIL'} ({len(RESULTS)-len(fails)}/{len(RESULTS)}) fails={fails}")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
