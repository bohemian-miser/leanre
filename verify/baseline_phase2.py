#!/usr/bin/env python3
"""Phase 2 baseline re-verification (verifier-owned; reads outputs/leanre.db read-only).

Gates 1-9 from outputs/phase2_verification_report.md §4.2, recomputed where possible from
the raw edge tables with verify/graph_oracle.py instead of trusting precomputed columns.
"""
from __future__ import annotations

import json
import os
import random
import sqlite3
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from graph_oracle import dominated_set_bruteforce, idom_bruteforce, reach  # noqa: E402

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
db = sqlite3.connect(f"file:{ROOT}/outputs/leanre.db?mode=ro", uri=True)
q = lambda s, *a: db.execute(s, a).fetchall()
res = []


def gate(name, expected, actual, how):
    ok = expected == actual
    res.append(ok)
    print(f"{'PASS' if ok else 'FAIL'}  {name}: expected={expected!r} measured={actual!r}  [{how}]")


mods = [r[0] for r in q("SELECT name FROM modules ORDER BY id")]
idx = {m: i for i, m in enumerate(mods)}
edges = q("SELECT src,dst FROM module_edges")
adj = [[] for _ in mods]
dangling = 0
for s, d in edges:
    if s in idx and d in idx:
        adj[idx[s]].append(idx[d])
    else:
        dangling += 1
gate("1 modules", 175187, len(mods), "COUNT(modules)")
gate("2 project import edges", 753261, len(edges), f"COUNT(module_edges); dangling endpoints={dangling}")

main = idx["Main"]
base = reach(adj, [main])
print(f"     reachable from Main (own BFS): {len(base):,}")
HUB = "Supplements.Kernels.MainTheoremsAll"
hub = idx[HUB]
dset = dominated_set_bruteforce(adj, main, hub, base)
# which module has the largest dominated set other than Main? check hub claim via DB column then brute-force it
top = q("SELECT name, dom_subtree_size FROM modules WHERE name!='Main' ORDER BY dom_subtree_size DESC LIMIT 3")
gate("3 hub module", HUB, top[0][0], f"largest dom_subtree_size excluding Main; top3={top}")
gate("4 hub dominator subtree", 175185, len(dset), "own node-removal reachability (|reach(Main)| - |reach(Main) w/o hub|)")

# 5/6: components = dominator-tree children of the hub; verify dom_parent column on a brute-force sample first
rnd = random.Random(20261122)
dom_parent = dict(q("SELECT name, dom_parent FROM modules"))
sample = rnd.sample([m for m in mods if m != "Main"], 400)
bad = 0
for m in sample:
    bf = idom_bruteforce(adj, main, idx[m])
    if (mods[bf] if bf is not None else None) != dom_parent[m]:
        bad += 1
gate("  dom_parent column vs brute-force idom (400 sampled modules)", 0, bad, "own node-removal oracle")
children = [m for m in mods if dom_parent[m] == HUB]
gate("5 top-level components under hub", 47060, len(children), "COUNT(dom_parent = hub)")
# singleton = hub child that dominates nothing but itself: no module has it as dom_parent
has_child = {p for p in dom_parent.values() if p}
singles = [m for m in children if m not in has_child]
gate("6 top-level singletons", 37001, len(singles), "hub children with no dominator-tree children")
# brute-force 60 of them: dominated set must be exactly {m}
bad = sum(1 for m in rnd.sample(singles, 60) if dominated_set_bruteforce(adj, main, idx[m], base) != {idx[m]})
gate("  singleton claim vs brute-force dominated set (60 sampled)", 0, bad, "own node-removal oracle")
gate("7 import-only shims", 150, q("SELECT COUNT(*) FROM modules WHERE is_shim=1")[0][0], "SUM(is_shim) [column]")
gate("8 duplicate project import lines", 308, q("SELECT COALESCE(SUM(dup_imports),0) FROM modules")[0][0], "SUM(dup_imports) [column]")
gate("9 challenge decls", 51692, q("SELECT COUNT(*) FROM tcb_decls")[0][0], "COUNT(tcb_decls)")
gate("9b challenge edges", 1206518, q("SELECT COUNT(*) FROM tcb_edges")[0][0], "COUNT(tcb_edges)")
print("extra:", dict(lines_wc=q("SELECT SUM(lines_wc) FROM modules")[0][0], bytes=q("SELECT SUM(bytes) FROM modules")[0][0],
                     declarations=q("SELECT COUNT(*) FROM declarations")[0][0]))
print(f"BASELINE {'PASS' if all(res) else 'FAIL'} ({sum(res)}/{len(res)})")
sys.exit(0 if all(res) else 1)
