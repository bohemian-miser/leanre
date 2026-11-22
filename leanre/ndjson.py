#!/usr/bin/env python3
"""Streaming Lean 4 export (NDJSON v3.1.0) parser & TCB analyzer.

Designed to stream-decompress `.ndjson.zst` via `7zz`
(no external `zstd` binary needed) using flat `array('I')` / `bytearray` tables so the
same architecture scales cleanly from `challenge.ndjson.zst` (51,692 decls, ~6.5M lines)
to `solution.ndjson.zst` (1.47M decls).
"""
from __future__ import annotations

import array
import collections
import gzip
import json
import os
import shutil
import subprocess
import time
from typing import Any, Dict, IO, List, Optional, Sequence, Set, Tuple

from db import INDEX_SQL_TCB, finalize_db, open_db, set_meta
from graph import bfs_shortest_paths, dominators_chk

SEVEN_ZZ_CANDIDATES = [
    os.path.expanduser("~/homebrew/bin/7zz"),
    "/opt/homebrew/bin/7zz",
    "/usr/local/bin/7zz",
    "7zz",
]

HEADLINE_THEOREMS = [
    "riemannHypothesis",
    "riemannZeta_eq_zero_re",
    "LFunction_ne_zero_of_half_lt_re",
    "LFunction_eq_zero_re",
    "LFunction_eq_zero_re_of_isPrimitive",
]

RH_HEADLINES = ["riemannHypothesis", "riemannZeta_eq_zero_re"]
GRH_HEADLINES = [
    "LFunction_ne_zero_of_half_lt_re",
    "LFunction_eq_zero_re",
    "LFunction_eq_zero_re_of_isPrimitive",
]

# Compact expression node tags
TAG_LEAF = 0      # sort, bvar, strVal, natVal
TAG_CONST = 1     # a = name_id
TAG_BIN = 2       # app, lam, forallE: a = child1, b = child2
TAG_LET = 3       # letE: a = type, b = value, c = body
TAG_PROJ = 4      # proj: a = struct_expr, b = typeName_id


def _find_7zz() -> str:
    for p in SEVEN_ZZ_CANDIDATES:
        if os.path.isabs(p) and os.path.exists(p):
            return p
    return "7zz"


def open_ndjson_stream(path: str) -> Tuple[IO[str], Optional[subprocess.Popen]]:
    if path.endswith(".zst"):
        zstd_exe = shutil.which("zstd")
        if zstd_exe:
            cmd = [zstd_exe, "-d", "-c", "--long=31", path]
        else:
            cmd = [_find_7zz(), "x", "-so", path]
        proc = subprocess.Popen(
            cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            errors="replace",
            bufsize=1024 * 1024,
        )
        assert proc.stdout is not None
        return proc.stdout, proc
    if path.endswith(".gz"):
        return gzip.open(path, "rt", encoding="utf-8", errors="replace"), None
    return open(path, "r", encoding="utf-8", errors="replace"), None


def infer_module_prefix(name: str) -> str:
    """Group Lean constant names into clean 1-2 segment namespace prefixes for TCB X-Ray."""
    if name in HEADLINE_THEOREMS:
        return "Challenge"
    if name in (
        "RiemannZetaZerosOnLine",
        "DirichletLNonvanishingRightOfHalf",
        "DirichletLZerosOnLine",
        "PrimitiveDirichletLZerosOnLine",
    ):
        return "Statements"
    if name in ("RiemannHypothesis", "riemannZeta"):
        return "Mathlib.RiemannZeta"
    if name in ("propext", "Classical.choice", "Quot.sound", "sorryAx") or name.startswith("Quot"):
        return "Init.Core"
    parts = name.split(".")
    if len(parts) == 1:
        return parts[0]
    p0, p1 = parts[0], parts[1]
    if p0 in (
        "DirichletCharacter",
        "Complex",
        "Real",
        "Nat",
        "Int",
        "Rat",
        "Finset",
        "Filter",
        "MeasureTheory",
        "Topology",
        "Set",
        "Function",
        "Polynomial",
        "Algebra",
        "Module",
        "LinearMap",
        "Matrix",
        "Continuous",
        "Differentiable",
        "Analytic",
        "Meromorphic",
        "LSeries",
        "ArithmeticFunction",
        "ZMod",
        "AddChar",
        "MulChar",
        "Units",
        "RingHom",
        "MonoidHom",
        "Submodule",
        "Ideal",
        "EuclideanDomain",
        "Group",
        "CommRing",
        "Field",
        "Metric",
        "NormedSpace",
        "UniformSpace",
        "TopologicalSpace",
        "MeasurableSpace",
        "ENNReal",
        "NNReal",
        "Order",
        "CompleteLattice",
        "Lattice",
        "LinearOrder",
        "PartialOrder",
        "Preorder",
        "Equiv",
        "Subtype",
        "Option",
        "List",
        "Array",
        "Fin",
        "Prod",
        "Sum",
        "Sigma",
        "PSigma",
        "PProd",
        "Classical",
        "Decidable",
        "Eq",
        "And",
        "Or",
        "Not",
        "Exists",
        "Iff",
        "Bool",
        "String",
        "Char",
        "Lean",
    ):
        return p0
    return f"{p0}.{p1}"


def parse_ndjson_export(path: str, verbose: bool = True) -> Dict[str, Any]:
    """Stream-parse a Lean 4 NDJSON v3.1.0 export into compact declaration DAG + TCB stats."""
    t0 = time.time()
    names: List[str] = [""]  # index 0 = anonymous root
    expr_tag = bytearray()
    expr_a = array.array("I")
    expr_b = array.array("I")
    expr_c = array.array("I")

    def ensure_expr(eid: int) -> None:
        cur = len(expr_tag)
        if eid >= cur:
            grow = eid - cur + 1
            expr_tag.extend(b"\x00" * grow)
            expr_a.extend([0] * grow)
            expr_b.extend([0] * grow)
            expr_c.extend([0] * grow)

    # Declarations stored as: (name_id, name_str, kind, type_roots, val_roots, extra_const_nids)
    decls: List[Tuple[int, str, str, List[int], List[int], List[int]]] = []
    const_to_decl: Dict[int, int] = {}
    export_meta: Dict[str, Any] = {}
    kind_counts: collections.Counter = collections.Counter()
    ind_breakdown = {"records": 0, "types": 0, "ctors": 0, "recs": 0, "mutual_blocks": 0}
    line_count = 0

    stream, proc = open_ndjson_stream(path)
    try:
        loads = json.loads
        for raw_line in stream:
            line_count += 1
            obj = loads(raw_line)
            if "ie" in obj:
                eid = obj["ie"]
                ensure_expr(eid)
                if "app" in obj:
                    d = obj["app"]
                    expr_tag[eid] = TAG_BIN
                    expr_a[eid] = d["fn"]
                    expr_b[eid] = d["arg"]
                elif "lam" in obj:
                    d = obj["lam"]
                    expr_tag[eid] = TAG_BIN
                    expr_a[eid] = d["type"]
                    expr_b[eid] = d["body"]
                elif "forallE" in obj:
                    d = obj["forallE"]
                    expr_tag[eid] = TAG_BIN
                    expr_a[eid] = d["type"]
                    expr_b[eid] = d["body"]
                elif "const" in obj:
                    expr_tag[eid] = TAG_CONST
                    expr_a[eid] = obj["const"]["name"]
                elif "letE" in obj:
                    d = obj["letE"]
                    expr_tag[eid] = TAG_LET
                    expr_a[eid] = d["type"]
                    expr_b[eid] = d["value"]
                    expr_c[eid] = d["body"]
                elif "proj" in obj:
                    d = obj["proj"]
                    expr_tag[eid] = TAG_PROJ
                    expr_a[eid] = d["struct"]
                    expr_b[eid] = d["typeName"]
                else:
                    expr_tag[eid] = TAG_LEAF
            elif "in" in obj:
                nid = obj["in"]
                if nid >= len(names):
                    names.extend([""] * (nid - len(names) + 1))
                if "str" in obj:
                    s = obj["str"]
                    pre = names[s["pre"]]
                    names[nid] = f"{pre}.{s['str']}" if pre else s["str"]
                elif "num" in obj:
                    nu = obj["num"]
                    pre = names[nu["pre"]]
                    names[nid] = f"{pre}.{nu['i']}" if pre else str(nu["i"])
            elif "thm" in obj:
                d = obj["thm"]
                nid = d["name"]
                idx = len(decls)
                decls.append((nid, names[nid], "thm", [d["type"]], [d["value"]], []))
                const_to_decl[nid] = idx
                kind_counts["thm"] += 1
            elif "def" in obj:
                d = obj["def"]
                nid = d["name"]
                idx = len(decls)
                decls.append((nid, names[nid], "def", [d["type"]], [d["value"]], []))
                const_to_decl[nid] = idx
                kind_counts["def"] += 1
            elif "inductive" in obj:
                ind = obj["inductive"]
                types = ind.get("types", [])
                ctors = ind.get("ctors", [])
                recs = ind.get("recs", [])
                ind_breakdown["records"] += 1
                ind_breakdown["types"] += len(types)
                ind_breakdown["ctors"] += len(ctors)
                ind_breakdown["recs"] += len(recs)
                if len(types) > 1:
                    ind_breakdown["mutual_blocks"] += 1
                primary_nid = types[0]["name"]
                idx = len(decls)
                t_roots = [t["type"] for t in types] + [c["type"] for c in ctors] + [r["type"] for r in recs]
                v_roots = [rule["rhs"] for r in recs for rule in r.get("rules", [])]
                all_nids = [t["name"] for t in types] + [c["name"] for c in ctors] + [r["name"] for r in recs]
                decls.append((primary_nid, names[primary_nid], "inductive", t_roots, v_roots, all_nids))
                for an in all_nids:
                    const_to_decl[an] = idx
                kind_counts["inductive"] += 1
            elif "opaque" in obj:
                d = obj["opaque"]
                nid = d["name"]
                idx = len(decls)
                decls.append((nid, names[nid], "opaque", [d["type"]], [d["value"]], []))
                const_to_decl[nid] = idx
                kind_counts["opaque"] += 1
            elif "quot" in obj:
                d = obj["quot"]
                nid = d["name"]
                idx = len(decls)
                decls.append((nid, names[nid], "quot", [d["type"]], [], []))
                const_to_decl[nid] = idx
                kind_counts["quot"] += 1
            elif "axiom" in obj:
                d = obj["axiom"]
                nid = d["name"]
                idx = len(decls)
                decls.append((nid, names[nid], "axiom", [d["type"]], [], []))
                const_to_decl[nid] = idx
                kind_counts["axiom"] += 1
            elif "meta" in obj:
                export_meta = obj["meta"]
            # 'il' universe level lines ignored for declaration dependency graph
    finally:
        stream.close()
        if proc is not None:
            proc.wait()
            if proc.returncode != 0:
                err_txt = proc.stderr.read() if proc.stderr else ""
                raise RuntimeError(f"7zz exited with {proc.returncode}: {err_txt[:300]}")

    t_parse = time.time() - t0
    n_decl = len(decls)
    n_expr = len(expr_tag)
    if verbose:
        print(
            f"[ndjson] streamed {line_count:,} lines -> {n_decl:,} decls, {n_expr:,} exprs in {t_parse:.2f}s"
        )

    # Walk expression DAGs to extract exact type vs value declaration edges and expr node sizes.
    t1 = time.time()
    seen_gen = array.array("I", [0]) * n_expr
    gen = 0

    def collect_refs(roots: Sequence[int]) -> Tuple[Set[int], int]:
        nonlocal gen
        gen += 1
        g = gen
        refs: Set[int] = set()
        stack: List[int] = []
        nodes_visited = 0
        for r in roots:
            if r < n_expr and seen_gen[r] != g:
                seen_gen[r] = g
                stack.append(r)
        while stack:
            e = stack.pop()
            nodes_visited += 1
            tag = expr_tag[e]
            if tag == TAG_BIN:
                a = expr_a[e]
                b = expr_b[e]
                if seen_gen[a] != g:
                    seen_gen[a] = g
                    stack.append(a)
                if seen_gen[b] != g:
                    seen_gen[b] = g
                    stack.append(b)
            elif tag == TAG_CONST:
                nid = expr_a[e]
                d_idx = const_to_decl.get(nid)
                if d_idx is not None:
                    refs.add(d_idx)
            elif tag == TAG_LET:
                a, b, c = expr_a[e], expr_b[e], expr_c[e]
                if seen_gen[a] != g:
                    seen_gen[a] = g
                    stack.append(a)
                if seen_gen[b] != g:
                    seen_gen[b] = g
                    stack.append(b)
                if seen_gen[c] != g:
                    seen_gen[c] = g
                    stack.append(c)
            elif tag == TAG_PROJ:
                a = expr_a[e]
                nid = expr_b[e]
                d_idx = const_to_decl.get(nid)
                if d_idx is not None:
                    refs.add(d_idx)
                if seen_gen[a] != g:
                    seen_gen[a] = g
                    stack.append(a)
        return refs, nodes_visited

    edges: List[Tuple[int, int, str]] = []
    expr_nodes_arr = [0] * n_decl
    adj_all: List[List[int]] = [[] for _ in range(n_decl)]
    adj_type: List[List[int]] = [[] for _ in range(n_decl)]
    fan_in = [0] * n_decl
    fan_out = [0] * n_decl

    name_to_idx: Dict[str, int] = {d[1]: i for i, d in enumerate(decls)}
    headline_set = {name_to_idx[h] for h in HEADLINE_THEOREMS if h in name_to_idx}

    for i, (_nid, _nm, _kind, t_roots, v_roots, _all_nids) in enumerate(decls):
        t_refs, t_nodes = collect_refs(t_roots)
        v_refs, v_nodes = collect_refs(v_roots) if v_roots else (set(), 0)
        t_refs.discard(i)
        v_refs.discard(i)
        expr_nodes_arr[i] = t_nodes + v_nodes
        all_r = t_refs | v_refs
        fan_out[i] = len(all_r)
        adj_type[i] = sorted(t_refs)
        # Semantic TCB traversal: for the 5 challenge headline theorems, skip their `sorry` proof value!
        if i in headline_set:
            adj_all[i] = sorted(t_refs)
        else:
            adj_all[i] = sorted(all_r)
        for dst in sorted(all_r):
            fan_in[dst] += 1
            if dst in t_refs and dst in v_refs:
                ek = "both"
            elif dst in t_refs:
                ek = "type"
            else:
                ek = "value"
            edges.append((i, dst, ek))

    t_walk = time.time() - t1
    if verbose:
        print(f"[ndjson] walked expr DAGs -> {len(edges):,} decl edges in {t_walk:.2f}s")

    # Compute cones & BFS depths from RH and from all 5 headlines (using semantic adj_all)
    rh_idx = [name_to_idx[h] for h in RH_HEADLINES if h in name_to_idx]
    grh_idx = [name_to_idx[h] for h in GRH_HEADLINES if h in name_to_idx]
    all_head_idx = [name_to_idx[h] for h in HEADLINE_THEOREMS if h in name_to_idx]

    # Single-root distance from `riemannHypothesis` specifically
    rh_primary = [name_to_idx["riemannHypothesis"]] if "riemannHypothesis" in name_to_idx else rh_idx
    dist_rh, _ = bfs_shortest_paths(rh_primary, adj_all, n_decl)
    dist_grh, _ = bfs_shortest_paths(grh_idx, adj_all, n_decl)
    dist_any, _ = bfs_shortest_paths(all_head_idx, adj_all, n_decl)

    # Check sorryAx isolation!
    sorry_idx = name_to_idx.get("sorryAx")
    sorry_in_statement_closure = (sorry_idx is not None and dist_any[sorry_idx] != -1)
    sorry_direct_users = []
    if sorry_idx is not None:
        for src, dst, ek in edges:
            if dst == sorry_idx:
                sorry_direct_users.append({"name": decls[src][1], "edge_kind": ek})

    # Virtual super-root `__HEADLINES__` (index = n_decl) -> all 5 headlines for dominator tree
    vroot = n_decl
    dom_adj = adj_all + [all_head_idx]
    dom_radj: List[List[int]] = [[] for _ in range(n_decl + 1)]
    for u in range(n_decl + 1):
        for w in dom_adj[u]:
            dom_radj[w].append(u)
    idom, rpo, dom_size, _dom_w, _dom_ch = dominators_chk(vroot, dom_adj, dom_radj, n_decl + 1)

    # Also compute pure definition-only cone (following only edges between non-thm nodes from headline types)
    is_def_arr = [0 if d[2] == "thm" else 1 for d in decls]
    def_adj = [
        [w for w in adj_all[u] if is_def_arr[w] == 1] if (u in headline_set or is_def_arr[u] == 1) else []
        for u in range(n_decl)
    ]
    dist_def_only, _ = bfs_shortest_paths(all_head_idx, def_adj, n_decl)
    def_only_count = sum(1 for i in range(n_decl) if dist_def_only[i] > 0 and is_def_arr[i] == 1)

    # Build prefix stats & top dominators summary
    prefix_counts: collections.Counter = collections.Counter()
    prefix_defs: collections.Counter = collections.Counter()
    prefix_rh_defs: collections.Counter = collections.Counter()
    axioms_found: List[Dict[str, Any]] = []
    decl_rows: List[Tuple[Any, ...]] = []

    for i, (_nid, nm, kind, _tr, _vr, _an) in enumerate(decls):
        pref = infer_module_prefix(nm)
        is_def = is_def_arr[i]
        in_rh = 1 if dist_rh[i] != -1 else 0
        in_grh = 1 if dist_grh[i] != -1 else 0
        prefix_counts[pref] += 1
        if is_def:
            prefix_defs[pref] += 1
            if in_rh:
                prefix_rh_defs[pref] += 1
        if kind == "axiom":
            axioms_found.append({
                "name": nm,
                "in_statement_closure": dist_any[i] != -1,
                "depth_from_any": dist_any[i],
                "fan_in": fan_in[i],
            })
        dp_idx = idom[i]
        if i in headline_set:
            dp_name = None
        elif dp_idx == vroot:
            dp_name = "__HEADLINES__"
        elif dp_idx >= 0:
            dp_name = decls[dp_idx][1]
        else:
            dp_name = None
        decl_rows.append((
            i + 1,
            nm,
            kind,
            pref,
            is_def,
            expr_nodes_arr[i],
            dist_rh[i],
            dist_any[i],
            in_rh,
            in_grh,
            dp_name,
            dom_size[i],
            fan_in[i],
            fan_out[i],
        ))

    edge_rows = [(decls[s][1], decls[d][1], ek) for (s, d, ek) in edges]

    # Top definitions by dominator subtree size & by shallow depth from RH/GRH
    top_dom_defs = sorted(
        (
            {
                "name": decls[i][1],
                "kind": decls[i][2],
                "module_prefix": infer_module_prefix(decls[i][1]),
                "dom_subtree_size": dom_size[i],
                "depth_from_rh": dist_rh[i],
                "depth_from_any": dist_any[i],
                "fan_in": fan_in[i],
                "fan_out": fan_out[i],
                "expr_nodes": expr_nodes_arr[i],
                "dom_parent": None if i in headline_set else ("__HEADLINES__" if idom[i] == vroot else (decls[idom[i]][1] if idom[i] >= 0 else None)),
            }
            for i in range(n_decl)
            if is_def_arr[i] == 1 and dist_any[i] > 0
        ),
        key=lambda x: (-x["dom_subtree_size"], x["depth_from_any"], -x["fan_in"]),
    )[:40]

    top_shallow_defs = sorted(
        (
            {
                "name": decls[i][1],
                "kind": decls[i][2],
                "module_prefix": infer_module_prefix(decls[i][1]),
                "depth_from_rh": dist_rh[i],
                "depth_from_any": dist_any[i],
                "in_rh_cone": 1 if dist_rh[i] != -1 else 0,
                "in_grh_cone": 1 if dist_grh[i] != -1 else 0,
                "dom_subtree_size": dom_size[i],
                "fan_in": fan_in[i],
                "fan_out": fan_out[i],
                "expr_nodes": expr_nodes_arr[i],
            }
            for i in range(n_decl)
            if is_def_arr[i] == 1 and 0 < dist_any[i] <= 4
        ),
        key=lambda x: (x["depth_from_any"], -x["dom_subtree_size"], -x["fan_in"]),
    )[:80]

    # Top key headline / target definitions reading list (depth 1-3 from RH and Dirichlet LFunction)
    rh_only_count = sum(1 for i in range(n_decl) if dist_rh[i] != -1)
    grh_only_extra = sum(1 for i in range(n_decl) if dist_grh[i] != -1 and dist_rh[i] == -1)
    any_reachable = sum(1 for i in range(n_decl) if dist_any[i] != -1)
    total_defs = sum(is_def_arr)
    total_thms = n_decl - total_defs

    stats = {
        "export_meta": export_meta,
        "ndjson_lines": line_count,
        "expr_records": n_expr,
        "decl_count": n_decl,
        "unpacked_constants_est": (
            kind_counts["thm"]
            + kind_counts["def"]
            + kind_counts["opaque"]
            + kind_counts["quot"]
            + kind_counts["axiom"]
            + ind_breakdown["types"]
            + ind_breakdown["ctors"]
            + ind_breakdown["recs"]
        ),
        "edge_count": len(edges),
        "kind_counts": dict(kind_counts),
        "inductive_breakdown": ind_breakdown,
        "definitions_count": total_defs,
        "theorems_count": total_thms,
        "definitions_pct": round(100.0 * total_defs / max(1, n_decl), 2),
        "theorems_pct": round(100.0 * total_thms / max(1, n_decl), 2),
        "reachable_from_headlines_type_only": any_reachable,
        "reachable_from_rh": rh_only_count,
        "extra_for_dirichlet_grh": grh_only_extra,
        "pure_def_cone_count": def_only_count,
        "axioms_in_export": axioms_found,
        "sorry_in_statement_closure": sorry_in_statement_closure,
        "sorry_direct_users": sorry_direct_users,
        "top_prefixes": [
            {
                "prefix": pref,
                "total": cnt,
                "definitions": prefix_defs[pref],
                "theorems": cnt - prefix_defs[pref],
                "rh_definitions": prefix_rh_defs[pref],
            }
            for pref, cnt in prefix_counts.most_common(35)
        ],
        "top_dom_definitions": top_dom_defs,
        "top_shallow_definitions": top_shallow_defs,
        "elapsed_seconds": round(time.time() - t0, 2),
    }

    return {
        "stats": stats,
        "decl_rows": decl_rows,
        "edge_rows": edge_rows,
    }


def run_ndjson_to_db(ndjson_path: str, db_path: str, verbose: bool = True) -> Dict[str, Any]:
    res = parse_ndjson_export(ndjson_path, verbose=verbose)
    t0 = time.time()
    conn = open_db(db_path, bulk_mode=True)
    try:
        conn.execute("DELETE FROM tcb_decls;")
        conn.execute("DELETE FROM tcb_edges;")
        conn.executemany(
            """INSERT INTO tcb_decls(
                id, name, kind, module_prefix, is_definition, expr_nodes,
                depth_from_rh, depth_from_any, in_rh_cone, in_grh_cone,
                dom_parent, dom_subtree_size, fan_in, fan_out
            ) VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?)""",
            res["decl_rows"],
        )
        conn.executemany(
            "INSERT OR IGNORE INTO tcb_edges(src, dst, edge_kind) VALUES (?,?,?)",
            res["edge_rows"],
        )
        conn.executescript(INDEX_SQL_TCB)
        set_meta(conn, "tcb_stats", res["stats"])
        finalize_db(conn)
    finally:
        conn.close()
    if verbose:
        print(
            f"[ndjson] wrote {len(res['decl_rows']):,} tcb_decls & {len(res['edge_rows']):,} tcb_edges to {db_path} in {time.time()-t0:.2f}s"
        )
    return res["stats"]
