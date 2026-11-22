#!/usr/bin/env python3
"""K3 oracle: independent recomputation of the challenge.ndjson.zst numbers.

Input: verify/out/challenge_oracle.pkl (from verify/oracle_ndjson.py — verifier's own parser).
Compares against the Phase 2 tables in outputs/leanre.db (tcb_decls / tcb_edges) and
recomputes the canonical cones with verify/graph_oracle.py.

Cone conventions (HANDOFF §3 / leanre/ndjson.py, restated so they can be audited):
  * record-level graph (an inductive record = types+ctors+recursors as ONE node);
  * "semantic" adjacency: the 5 headline theorems contribute only their TYPE deps
    (their values are `sorry` stubs in Challenge.lean); every other node type ∪ value;
  * def-cone: start at the 5 headlines, follow edges only into non-`thm` records, and
    only out of headlines / non-`thm` records; count non-`thm` records at distance > 0.
"""
from __future__ import annotations

import json
import os
import pickle
import sqlite3
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from graph_oracle import reach  # noqa: E402

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
RH = ["riemannHypothesis", "riemannZeta_eq_zero_re"]
GRH = ["LFunction_ne_zero_of_half_lt_re", "LFunction_eq_zero_re", "LFunction_eq_zero_re_of_isPrimitive"]


def cones(G):
    names, kinds, T, V = G["rec_names"], G["rec_kinds"], G["tdeps"], G["vdeps"]
    ix = {n: i for i, n in enumerate(names)}
    heads = [ix[h] for h in RH + GRH]
    hs = set(heads)
    sem = [sorted(T[i]) if i in hs else sorted(T[i] | V[i]) for i in range(len(names))]
    full = [sorted(T[i] | V[i]) for i in range(len(names))]
    r_rh1 = reach(sem, [ix["riemannHypothesis"]])
    r_rh2 = reach(sem, [ix[h] for h in RH])
    r_grh = reach(sem, [ix[h] for h in GRH])
    r_all = reach(sem, heads)
    nonthm = [k != "thm" for k in kinds]
    dadj = [[w for w in sem[u] if nonthm[w]] if (u in hs or nonthm[u]) else [] for u in range(len(names))]
    dcone = {i for i in reach(dadj, heads) if i not in hs and nonthm[i]}
    out = {
        "records": len(names),
        "edges_union": sum(len(a) for a in full),
        "reach_riemannHypothesis": len(r_rh1),
        "reach_both_zeta_roots": len(r_rh2),
        "extra_for_3_dirichlet_grh": len(r_grh - r_rh1),
        "extra_for_3_dirichlet_grh_beyond_both_zeta": len(r_grh - r_rh2),
        "reach_all_5": len(r_all),
        "unreachable_from_all_5": sorted(names[i] for i in set(range(len(names))) - r_all),
        "pure_def_cone": len(dcone),
        "axioms": sorted(n for n, k in zip(names, kinds) if k == "axiom"),
        "axioms_reachable_all_5": sorted(names[i] for i in r_all if kinds[i] == "axiom"),
    }
    if "sorryAx" in ix:
        s = ix["sorryAx"]
        users = [(names[i], ("both" if s in T[i] and s in V[i] else "type" if s in T[i] else "value"))
                 for i in range(len(names)) if s in T[i] or s in V[i]]
        out["sorryAx_fan_in"] = len(users)
        out["sorryAx_users"] = sorted(users)
        out["sorryAx_in_semantic_closure"] = s in r_all
        out["sorryAx_reachable_if_headline_values_followed"] = s in reach(full, heads)
    return out


def compare_phase2(G):
    db = sqlite3.connect(f"file:{ROOT}/outputs/leanre.db?mode=ro", uri=True)
    names, T, V = G["rec_names"], G["tdeps"], G["vdeps"]
    p2 = {n: k for n, k in db.execute("SELECT name, kind FROM tcb_decls")}
    mine = dict(zip(names, G["rec_kinds"]))
    p2e = {(s, d): k for s, d, k in db.execute("SELECT src,dst,edge_kind FROM tcb_edges")}
    me = {}
    for i, n in enumerate(names):
        for j in T[i] | V[i]:
            me[(n, names[j])] = "both" if (j in T[i] and j in V[i]) else ("type" if j in T[i] else "value")
    cone_cols = {n: (a, b) for n, a, b in db.execute("SELECT name,in_rh_cone,in_grh_cone FROM tcb_decls")}
    return {
        "decl_name+kind_identical": p2 == mine,
        "decl_only_phase2": len(set(p2) - set(mine)), "decl_only_oracle": len(set(mine) - set(p2)),
        "edges_identical_incl_kind": p2e == me,
        "edges_only_phase2": len(set(p2e) - set(me)), "edges_only_oracle": len(set(me) - set(p2e)),
        "edge_kind_mismatch": sum(1 for k in p2e if k in me and p2e[k] != me[k]),
        "phase2_in_rh_cone": sum(a for a, _ in cone_cols.values()),
        "phase2_in_grh_cone_not_rh": sum(1 for a, b in cone_cols.values() if b and not a),
    }


if __name__ == "__main__":
    pk = sys.argv[1] if len(sys.argv) > 1 else f"{ROOT}/verify/out/challenge_oracle.pkl"
    G = pickle.load(open(pk, "rb"))["G"]
    c = cones(G)
    print(json.dumps(c, indent=1, ensure_ascii=False))
    cmp_ = compare_phase2(G)
    print(json.dumps(cmp_, indent=1))
    exp = {"records": 51692, "edges_union": 1206518, "pure_def_cone": 2570, "extra_for_3_dirichlet_grh": 470, "sorryAx_fan_in": 5}
    ok = all(c[k] == v for k, v in exp.items()) and cmp_["decl_name+kind_identical"] and cmp_["edges_identical_incl_kind"]
    for k, v in exp.items():
        print(f"{'PASS' if c[k]==v else 'FAIL'} {k}: expected {v} measured {c[k]}")
    print("K3-ORACLE", "PASS" if ok else "FAIL")
    sys.exit(0 if ok else 1)
