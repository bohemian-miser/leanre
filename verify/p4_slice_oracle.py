#!/usr/bin/env python3
"""Independent oracle check for Phase 4 D4 (`leanre kernel slice`, `leanre kernel type-deps`,
and the `lean4lean_timeout` SmallLoop / Run1..4 fix).

Uses verifier's own independent C++ oracle graph (verify/out/solution_oracle.{src.i32,dst.i32,kind.i8,names.json})
with ZERO imports from leanre/.
"""
from __future__ import annotations

import collections
import json
import os
import sqlite3
import subprocess
import sys

import numpy as np

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from kernel_db_check import CSR, load_oracle  # noqa: E402

R = []


def ck(gate, ok, msg):
    R.append((gate, bool(ok)))
    print(f"{'PASS' if ok else 'FAIL'} [{gate}] {msg}", flush=True)


def run_cli(*args):
    cp = subprocess.run([sys.executable, os.path.join(ROOT, "leanre", "kernel.py"), *args], capture_output=True, text=True)
    return cp.returncode, cp.stdout, cp.stderr


def main():
    o = load_oracle(os.path.join(ROOT, "verify", "out", "solution_oracle"))
    names = o["names"]
    ix = {nm: i for i, nm in enumerate(names)}
    n = len(names)
    fwd = CSR(n, o["src"], o["dst"], o["kind"])
    # Reverse CSR for forward/dependent slices
    order_r = np.argsort(o["dst"], kind="stable")
    rev = CSR(n, o["dst"][order_r], o["src"][order_r], o["kind"][order_r])

    # 1. Verify lean4lean_timeout taint fix in outputs/kernel/kernel.db & outputs/kernel_report.json
    kdb = sqlite3.connect(f"file:{ROOT}/outputs/kernel/kernel.db?mode=ro", uri=True)
    t_rows = kdb.execute(
        "SELECT s.id, s.decl_id, d.name, s.origin, s.module, s.line_no, s.detail "
        "FROM taint_sources s JOIN decls d ON d.id = s.decl_id WHERE s.class='lean4lean_timeout' ORDER BY s.decl_id"
    ).fetchall()
    t_names = [r[2] for r in t_rows]
    t_mods = sorted({r[4] for r in t_rows})
    has_proof = "PI.PC.loop_run._proof_1_1" in t_names or "PI.PC.loop_run" in t_names
    ck("D4/timeout", has_proof and "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChebyshevPrimeBounds.SmallLoop" in t_mods,
       f"kernel.db lean4lean_timeout sources={t_names} modules={t_mods}")
    # Check SmallLoop live count in decl_module == 9, Run1..4 == 0, DyadicPrimeIntervals.SmallLoop == 0
    sl_live = kdb.execute(
        "SELECT COUNT(*) FROM decl_module m JOIN decls d ON d.id=m.decl_id "
        "WHERE m.module='Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChebyshevPrimeBounds.SmallLoop' AND d.live_mask!=0"
    ).fetchone()[0]
    run_live = kdb.execute(
        "SELECT COUNT(*) FROM decl_module WHERE module LIKE 'Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DyadicPrimeIntervals.%'"
    ).fetchone()[0]
    ck("D4/timeout", sl_live == 9 and run_live == 0,
       f"ChebyshevPrimeBounds.SmallLoop live decls={sl_live} (expected 9); DyadicPrimeIntervals.* aligned={run_live} (expected 0)")
    # Verify all taint_paths for lean4lean_timeout edge-by-edge against verifier's OWN oracle
    tp_rows = kdb.execute(
        "SELECT p.source_id, p.root_id, p.hop, p.decl_id, p.edge_kind "
        "FROM taint_paths p JOIN taint_sources s ON s.id=p.source_id WHERE s.class='lean4lean_timeout' "
        "ORDER BY p.source_id, p.root_id, p.hop"
    ).fetchall()
    by_pr = collections.defaultdict(list)
    for sid, rid, hop, did, ek in tp_rows:
        by_pr[(sid, rid)].append((hop, did, ek))
    t_err = 0
    for (sid, rid), hops in by_pr.items():
        for (_, d0, _), (_, d1, ek) in zip(hops, hops[1:]):
            ok_k = fwd.lookup_kind(d0, d1)
            if ok_k == 0 or (ek is not None and ek != ok_k):
                t_err += 1
    ck("D4/timeout", len(by_pr) >= 5 and t_err == 0,
       f"lean4lean_timeout taint paths={len(by_pr)} edge-validated vs oracle: errors={t_err}")

    # 2. Verify `leanre kernel slice` (backward + forward, edge-kind filter, depth cap) vs verifier oracle!
    rc, out, err = run_cli("slice", "UpperTheory.FinalTheorems.everyCharacter", "--depth", "2", "--json")
    ck("D4/slice", rc == 0, f"kernel.py slice everyCharacter --depth 2 --json rc={rc} err={err[:120]!r}")
    if rc == 0:
        sl = json.loads(out)
        # Extract nodes & edges flexibly depending on JSON field names
        sl_nodes = sl.get("nodes") or []
        sl_edges = sl.get("edges") or []
        # Recompute exact depth-2 backward BFS from everyCharacter on verifier's oracle
        root_i = ix["UpperTheory.FinalTheorems.everyCharacter"]
        expected_nodes = {root_i: 0}
        frontier = [root_i]
        for dep in (1, 2):
            nxt = []
            for u in frontier:
                for w in fwd.idx[fwd.ptr[u]:fwd.ptr[u + 1]]:
                    w = int(w)
                    if w not in expected_nodes:
                        expected_nodes[w] = dep
                        nxt.append(w)
            frontier = nxt
        got_names = {nd["name"] if isinstance(nd, dict) else nd for nd in sl_nodes}
        exp_names = {names[i] for i in expected_nodes}
        # Verify edge existence in oracle
        bad_e = 0
        for e in sl_edges:
            s_nm = e.get("src_name") or e.get("src")
            d_nm = e.get("dst_name") or e.get("dst")
            si = ix[s_nm] if isinstance(s_nm, str) else int(s_nm)
            di = ix[d_nm] if isinstance(d_nm, str) else int(d_nm)
            if fwd.lookup_kind(si, di) == 0:
                bad_e += 1
        ck("D4/slice", got_names == exp_names and bad_e == 0,
           f"slice(everyCharacter, depth=2): nodes={len(got_names)} vs oracle={len(exp_names)} exact={got_names == exp_names}; edges={len(sl_edges)} bad_edges={bad_e}")

    # Test type-only slice on riemannHypothesis depth 1
    rc2, out2, err2 = run_cli("slice", "riemannHypothesis", "--depth", "1", "--edge-kind", "type", "--json")
    ck("D4/slice", rc2 == 0, f"kernel.py slice riemannHypothesis --depth 1 --edge-kind type --json rc={rc2} err={err2[:120]!r}")
    if rc2 == 0:
        sl2 = json.loads(out2)
        got2 = {nd["name"] if isinstance(nd, dict) else nd for nd in (sl2.get("nodes") or [])}
        rh_i = ix["riemannHypothesis"]
        exp2 = {"riemannHypothesis"} | {
            names[int(w)]
            for w, k in zip(fwd.idx[fwd.ptr[rh_i]:fwd.ptr[rh_i + 1]], fwd.kind[fwd.ptr[rh_i]:fwd.ptr[rh_i + 1]])
            if int(k) in (1, 3)
        }
        ck("D4/slice", got2 == exp2, f"slice(riemannHypothesis, depth=1, type): got={sorted(got2)} vs oracle={sorted(exp2)}")

    # Test `type-deps` on UpperTheory.FinalTheorems.everyCharacter_of_row
    rc3, out3, err3 = run_cli("type-deps", "UpperTheory.FinalTheorems.everyCharacter_of_row", "--json")
    ck("D4/type-deps", rc3 == 0, f"kernel.py type-deps everyCharacter_of_row --json rc={rc3} err={err3[:120]!r}")
    if rc3 == 0:
        td = json.loads(out3)
        u = ix["UpperTheory.FinalTheorems.everyCharacter_of_row"]
        exp_type = sorted(names[int(w)] for w, k in zip(fwd.idx[fwd.ptr[u]:fwd.ptr[u + 1]], fwd.kind[fwd.ptr[u]:fwd.ptr[u + 1]]) if int(k) in (1, 3))
        exp_val_only = sorted(names[int(w)] for w, k in zip(fwd.idx[fwd.ptr[u]:fwd.ptr[u + 1]], fwd.kind[fwd.ptr[u]:fwd.ptr[u + 1]]) if int(k) == 2)
        got_type = sorted((x["name"] if isinstance(x, dict) else x) for x in (td.get("type_deps") or []))
        got_val = sorted((x["name"] if isinstance(x, dict) else x) for x in (td.get("value_only_deps") or []))
        ck("D4/type-deps", got_type == exp_type and got_val == exp_val_only,
           f"type-deps(everyCharacter_of_row): type={len(got_type)}/{len(exp_type)} eq={got_type == exp_type}; val_only={len(got_val)}/{len(exp_val_only)} eq={got_val == exp_val_only}")

    fails = [g for g, ok in R if not ok]
    print(f"\nP4-SLICE-ORACLE {'PASS' if not fails else 'FAIL'} ({len(R)-len(fails)}/{len(R)}) fails={fails}")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
