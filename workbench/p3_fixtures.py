#!/usr/bin/env python3
"""
Synthetic fixtures for the Phase 3 workbench views (kernel-exact / FLIRT).

EVERYTHING HERE IS SYNTHETIC. It exists so the UI can be developed and
self-tested before (or without) the real producers' databases. Guardrail 3:
every name is prefixed ``FIXTURE.`` and every API payload built from this
module carries ``state="fixture"`` so the UI shows a permanent banner. No
number in here is, or resembles, a measurement of the real proof archive.

The graph is generated deterministically (fixed seed) and the live/dead
split, dominator tree and taint paths are *computed* from that synthetic
graph, so the views are internally consistent.
"""
from __future__ import annotations

import random
from typing import Any, Dict, List, Optional, Set, Tuple

SEED = 20261122
TAINT_KINDS = ["kexactB", "CutCptCopy", "decide_kernel", "ofReduceBool"]


def build_kernel_fixture() -> Dict[str, Any]:
    rng = random.Random(SEED)
    decls: Dict[str, Dict[str, Any]] = {}
    edges: Dict[str, List[Tuple[str, str]]] = {}

    def add(name: str, kind: str, module: str, taint: str = "") -> str:
        decls[name] = {"name": name, "kind": kind, "module": module, "taint": taint}
        edges[name] = []
        return name

    def dep(src: str, dst: str, how: Optional[str] = None) -> None:
        if src == dst or any(d == dst for d, _ in edges[src]):
            return
        edges[src].append((dst, how or rng.choice(["type", "value", "value", "both"])))

    roots = [add("FIXTURE.root_%s" % c, "theorem", "FIXTURE.Entry") for c in "ABCDE"]
    hubs = [add("FIXTURE.Hub.h%d" % i, "theorem", "FIXTURE.Hub") for i in range(4)]
    mids = [add("FIXTURE.Mid.m%02d" % i, rng.choice(["theorem", "definition"]), "FIXTURE.Mid.Part%d" % (i % 3)) for i in range(14)]
    lows = []
    for i in range(22):
        taint = TAINT_KINDS[i % 4] if i % 5 == 0 else ""
        lows.append(add("FIXTURE.Low.l%02d" % i, rng.choice(["theorem", "definition", "opaque"]), "FIXTURE.Low.Part%d" % (i % 4), taint))
    axioms = [add("FIXTURE.ax_%s" % n, "axiom", "FIXTURE.Core") for n in ("alpha", "beta", "gamma")]
    sorry = add("FIXTURE.sorry_standin", "axiom", "FIXTURE.Core")
    leaves = [add("FIXTURE.Core.c%02d" % i, rng.choice(["definition", "inductive", "constructor"]), "FIXTURE.Core") for i in range(12)]
    dead = [add("FIXTURE.Dead.d%02d" % i, rng.choice(["theorem", "definition"]), "FIXTURE.Dead.Part%d" % (i % 2)) for i in range(14)]

    dep(roots[0], hubs[0]); dep(roots[1], hubs[0]); dep(roots[1], hubs[1])
    dep(roots[2], hubs[2]); dep(roots[3], hubs[2]); dep(roots[3], hubs[3]); dep(roots[4], hubs[3])
    for i, m in enumerate(mids):
        dep(hubs[i % 4], m)
        if i % 3 == 0:
            dep(hubs[(i + 1) % 4], m)
    for i, l in enumerate(lows):
        dep(mids[i % len(mids)], l)
        if i % 4 == 1:
            dep(mids[(i * 3 + 1) % len(mids)], l)
    for l in lows:
        for c in rng.sample(leaves, 2):
            dep(l, c)
        if rng.random() < 0.35:
            dep(l, rng.choice(axioms[:2]))
    for i in range(1, len(leaves)):
        if i % 3:
            dep(leaves[i], leaves[i // 3], "type")
    for i, d in enumerate(dead):
        dep(d, rng.choice(lows))
        dep(d, rng.choice(leaves))
        if i == 0:
            dep(d, sorry)
        if i == 1:
            dep(d, axioms[2])
        if i > 2:
            dep(d, dead[i - 3])

    return {"decls": decls, "edges": edges, "roots": roots, "sorry": sorry}


KERNEL_SCHEMA_V0 = """
CREATE TABLE meta(key TEXT PRIMARY KEY, value_json TEXT);
CREATE TABLE decls(id INTEGER PRIMARY KEY, name TEXT UNIQUE, kind TEXT, n_consts INT, type_nodes INT, value_nodes INT,
  fan_in INT, fan_out INT, fan_out_type INT, fan_out_value INT, flags INT, live_mask INT, stmt_mask INT, sighash TEXT, sighash_anon TEXT);
CREATE TABLE consts(name TEXT PRIMARY KEY, decl_id INT, ckind TEXT, sighash TEXT, sighash_anon TEXT);
CREATE TABLE edges(src INT, dst INT, kind INT, PRIMARY KEY(src,dst)) WITHOUT ROWID;
CREATE INDEX edges_dst ON edges(dst,src);
CREATE TABLE roots(id INTEGER PRIMARY KEY, name TEXT, decl_id INT, grp TEXT);
CREATE TABLE reach(root_id INT, decl_id INT, depth INT, parent INT, PRIMARY KEY(root_id,decl_id)) WITHOUT ROWID;
CREATE TABLE dom_trees(id INTEGER PRIMARY KEY, label TEXT, view TEXT, root_ids TEXT, n_nodes INT);
CREATE TABLE dom(tree_id INT, decl_id INT, idom INT, depth INT, subtree_size INT, PRIMARY KEY(tree_id,decl_id)) WITHOUT ROWID;
CREATE INDEX dom_idom ON dom(tree_id,idom);
CREATE TABLE taint_sources(id INTEGER PRIMARY KEY, class TEXT, decl_id INT, origin TEXT, module TEXT, line_no INT, detail TEXT);
CREATE TABLE taint_paths(source_id INT, root_id INT, hop INT, decl_id INT, edge_kind INT, PRIMARY KEY(source_id,root_id,hop)) WITHOUT ROWID;
CREATE TABLE decl_module(decl_id INTEGER PRIMARY KEY, module TEXT, method TEXT, src_decl_id INT);
"""


def build_kernel_fixture_db(conn) -> None:
    """Materialise the synthetic graph into an (in-memory) SQLite DB that follows the
    `kernel` worker's kernel.db schema v0, so fixture mode exercises the same SQL as real data."""
    import json

    fx = build_kernel_fixture()
    decls, edges, roots = fx["decls"], fx["edges"], fx["roots"]

    # ids in dependency order (deps get smaller ids), like export order
    order: List[str] = []
    seen: Set[str] = set()

    def visit(n: str) -> None:
        if n in seen:
            return
        seen.add(n)
        for d, _ in edges[n]:
            visit(d)
        order.append(n)

    for n in sorted(decls):
        visit(n)
    ident = {n: i for i, n in enumerate(order)}
    ekind = {"type": 1, "value": 2, "both": 3}
    E: Dict[int, List[Tuple[int, int]]] = {ident[n]: [(ident[d], ekind[h]) for d, h in edges[n]] for n in decls}
    root_ids = [ident[r] for r in roots]

    def bfs(starts: List[int]) -> Dict[int, Tuple[int, Optional[int]]]:
        out: Dict[int, Tuple[int, Optional[int]]] = {s: (0, None) for s in starts}
        queue = list(starts)
        while queue:
            u = queue.pop(0)
            for v, _ in sorted(E[u]):
                if v not in out:
                    out[v] = (out[u][0] + 1, u)
                    queue.append(v)
        return out

    reach = [bfs([r]) for r in root_ids]
    stmt = []
    for r in root_ids:
        starts = sorted(v for v, k in E[r] if k in (1, 3))
        s = set(bfs(starts)) if starts else set()
        s.add(r)
        stmt.append(s)

    def dominators(starts: List[int]) -> Dict[int, Tuple[Optional[int], int, int]]:
        V = -1
        nodes = sorted(set(bfs(starts)))
        preds: Dict[int, List[int]] = {n: [] for n in nodes}
        for u in nodes:
            for v, _ in E[u]:
                preds[v].append(u)
        for s in starts:
            preds[s].append(V)
        full = set(nodes) | {V}
        dom: Dict[int, Set[int]] = {n: set(full) for n in nodes}
        dom[V] = {V}
        changed = True
        while changed:
            changed = False
            for n in nodes:
                new = set(full)
                for p in preds[n]:
                    new &= dom[p]
                new.add(n)
                if new != dom[n]:
                    dom[n] = new
                    changed = True
        sub = {n: 0 for n in nodes}
        for n in nodes:
            for d in dom[n]:
                if d != V:
                    sub[d] += 1
        out: Dict[int, Tuple[Optional[int], int, int]] = {}
        for n in nodes:
            strict = dom[n] - {n}
            idom = max(strict, key=lambda d: len(dom[d]))
            out[n] = (None if idom == V else idom, len(dom[n]) - 2, sub[n])
        return out

    conn.executescript(KERNEL_SCHEMA_V0)
    fan_in = {i: 0 for i in ident.values()}
    for u, lst in E.items():
        for v, _ in lst:
            fan_in[v] += 1
    for n in order:
        i = ident[n]
        d = decls[n]
        live = sum(1 << k for k in range(len(roots)) if i in reach[k])
        sm = sum(1 << k for k in range(len(roots)) if i in stmt[k])
        kind = {"theorem": "thm", "definition": "def", "constructor": "def"}.get(d["kind"], d["kind"])
        flags = {"": 0, "kexactB": 1, "CutCptCopy": 0, "decide_kernel": 2, "ofReduceBool": 4}[d["taint"]]
        n_db = n
        fo_t = sum(1 for _, k in E[i] if k in (1, 3))
        fo_v = sum(1 for _, k in E[i] if k in (2, 3))
        conn.execute("INSERT INTO decls VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
                     (i, n_db, kind, 1, 3, 5, fan_in[i], len(E[i]), fo_t, fo_v, flags, live, sm, "k1n:%032x" % (i + 1), "k1a:%032x" % (i + 1)))
        conn.execute("INSERT INTO consts VALUES (?,?,?,?,?)", (n_db, i, kind, "k1n:%032x" % (i + 1), "k1a:%032x" % (i + 1)))
        unmatched = d["module"].endswith("Core") and i % 2 == 0
        conn.execute("INSERT INTO decl_module VALUES (?,?,?,?)", (i, None if unmatched else d["module"], "unmatched:fixture" if unmatched else "exact", None))
        for v, k in E[i]:
            conn.execute("INSERT INTO edges VALUES (?,?,?)", (i, v, k))
    for k, r in enumerate(roots):
        conn.execute("INSERT INTO roots VALUES (?,?,?,?)", (k, r, ident[r], "FX1" if k < 2 else "FX2"))
        for v, (depth, parent) in reach[k].items():
            conn.execute("INSERT INTO reach VALUES (?,?,?,?)", (k, v, depth, parent))
    trees = [("ALL", "proof", list(range(len(roots))), root_ids)] + [(r, "proof", [k], [ident[r]]) for k, r in enumerate(roots)]
    for t, (label, view, rids, starts) in enumerate(trees):
        dm = dominators(starts)
        conn.execute("INSERT INTO dom_trees VALUES (?,?,?,?,?)", (t, label, view, json.dumps(rids), len(dm)))
        for n, (idom, depth, sub) in dm.items():
            conn.execute("INSERT INTO dom VALUES (?,?,?,?,?)", (t, n, idom, depth, sub))
    sid = 0
    for n in order:
        cls = decls[n]["taint"]
        if not cls:
            continue
        i = ident[n]
        conn.execute("INSERT INTO taint_sources VALUES (?,?,?,?,?,?,?)", (sid, cls, i, "kernel-pattern", decls[n]["module"], None, "fixture"))
        for k in range(len(roots)):
            if i not in reach[k]:
                continue
            chain = [i]
            while reach[k][chain[-1]][1] is not None:
                chain.append(reach[k][chain[-1]][1])
            chain.reverse()
            for hop, node in enumerate(chain):
                ek = None if hop == 0 else dict(E[chain[hop - 1]])[node]
                conn.execute("INSERT INTO taint_paths VALUES (?,?,?,?,?)", (sid, k, hop, node, ek))
        sid += 1
    n_edges = sum(len(v) for v in E.values())
    conn.execute("INSERT INTO meta VALUES (?,?)", ("schema_version", json.dumps(0)))
    conn.execute("INSERT INTO meta VALUES (?,?)", ("input", json.dumps({"path": "(none: synthetic graph, seed %d)" % SEED})))
    conn.execute("INSERT INTO meta VALUES (?,?)", ("counts", json.dumps({"decls": len(order), "edges": n_edges, "counting_rule": "fixture: each synthetic node is one record"})))
    conn.commit()


def build_flirt_fixture() -> Dict[str, Any]:
    rng = random.Random(SEED + 1)
    misfile = []
    for i in range(18):
        folder = "FIXTURE.Folder%d.Sub%d" % (i % 3, i % 5)
        declared = "FIXTURE.Other%d.Topic%d" % (i % 4, i % 2)
        misfile.append({
            "rank": i + 1,
            "module": "%s.Mod%02d" % (folder, i),
            "path": "FIXTURE/%s/Mod%02d.lean" % (folder.split(".", 1)[1].replace(".", "/"), i),
            "folder_ns": folder,
            "declared_ns": declared,
            "score": round(0.98 - i * 0.041, 3),
            "reason": rng.choice(["declared namespace differs from folder path", "import fingerprint matches another cluster", "type-token fingerprint outlier in folder"]),
            "evidence": "fixture evidence row %d" % (i + 1),
        })
    boiler = []
    for i in range(9):
        size = 400 - i * 37
        boiler.append({
            "cluster_id": "fx-clone-%02d" % i,
            "size": size,
            "representative": "FIXTURE.Clone%d.Template" % i,
            "fingerprint": "%016x" % rng.getrandbits(64),
            "members": ["FIXTURE.Clone%d.Inst%03d" % (i, j) for j in range(min(size, 8))],
        })
    repos = [
        {"repo": "fixture/repo-one", "commit": "0" * 7 + "a", "license": "FIXTURE-LICENSE", "signatures": 1200},
        {"repo": "fixture/repo-two", "commit": "0" * 7 + "b", "license": "FIXTURE-LICENSE", "signatures": 340},
    ]
    tier2 = []
    for i in range(24):
        rp = repos[i % 2]
        tier2.append({
            "id": i + 1,
            "decl": "FIXTURE.Mid.m%02d" % (i % 14) if i < 14 else "FIXTURE.Low.l%02d" % (i - 14),
            "module": "FIXTURE.Mid.Part%d" % (i % 3),
            "repo": rp["repo"], "commit": rp["commit"], "license": rp["license"],
            "matched_name": "Fixture.Upstream.lemma_%d" % i,
            "sighash": "%016x" % rng.getrandbits(64),
            "variant": "named" if i % 3 else "name-independent",
            "score": round(1.0 - (i % 6) * 0.07, 2),
            "evidence": "signature hash equality (fixture)",
        })
    tier3 = []
    for i in range(10):
        tier3.append({
            "cluster_id": "fx-cluster-%02d" % i,
            "label": "fixture draft label %d" % i,
            "model": "fixture-model",
            "blinded": True,
            "unblinded_label": "fixture draft label %d" % (i if i % 3 else i + 100),
            "agrees": bool(i % 3),
            "confidence": round(0.9 - i * 0.05, 2),
            "size": 60 - i * 4,
            "members": ["FIXTURE.Mid.m%02d" % ((i + j) % 14) for j in range(3)],
        })
    return {
        "misfile": misfile, "boilerplate": boiler, "repos": repos, "tier2": tier2, "tier3": tier3,
        "tier2_metrics": {"precision": 0.5, "recall": 0.5, "negative_control_fpr": 0.5, "note": "fixture placeholder values"},
    }
