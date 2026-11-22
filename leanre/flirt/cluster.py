#!/usr/bin/env python3
"""FLIRT Phase 4 -- Kernel-graph-aware coarse blueprint clustering & boilerplate collapse.

    python3 leanre/flirt/cluster.py --kernel-db outputs/kernel/kernel.db \
        --tier1-db outputs/flirt/tier1.db --out outputs/flirt/clusters.json

Partitions 100% of the live kernel declaration graph (`dom_trees` `ALL`, 1,468,414 decls)
into ~100-140 human-legible coarse blueprint clusters via a deterministic dominator-tree
frontier cut + per-pillar semantic residual grouping, while collapsing:
  1. Compiler auxiliaries (`._proof_N`, `._simp_N`, `.match_N`, `aux_prefix:*`)
  2. `CutCptCopy` / `kcopy` / `SideCopy` / `LamCopy` copy shells
  3. Live `*_Statement` forwarding wrappers (`tier1.db` `is_statement_wrapper = 1`)
  4. Duplicate user theorem statements sharing an identical kernel `sighash` (`k1n`)

All database reads use `mode=ro`. Zero raw `.lean` source text is emitted; every count
and edge is tagged `[L]` (machine-extracted from pinned local DBs).
"""
from __future__ import annotations

import argparse
import array
import collections
import json
import os
import re
import sqlite3
import sys
import time
from typing import Any, Dict, List, Optional, Sequence, Set, Tuple

HERE = os.path.dirname(os.path.abspath(__file__))
LEANRE = os.path.dirname(HERE)
REPO = os.path.dirname(LEANRE)

DEFAULT_KERNEL_DB = os.path.join(REPO, "outputs", "kernel", "kernel.db")
DEFAULT_TIER1_DB = os.path.join(REPO, "outputs", "flirt", "tier1.db")
DEFAULT_OUT = os.path.join(REPO, "outputs", "flirt", "clusters.json")
SCHEMA_VERSION = "leanre.flirt.clusters/1"

# Canonical Phase 4 pillar roots (used strictly for lineage tagging on the real proof;
# generic fallback tags every node under the largest root as `main_cone` on other repos).
PILLAR_ROOT_NAMES: Dict[str, str] = {
    "UpperTheory.Lit.every_character_of_theta_integrals_local_matching": "pillar_theta",
    "UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter": "pillar_galois",
    "UpperTheory.One.vwin_of_row": "pillar_window",
    "UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin": "pillar_volume_lit",
    "allChi": "shared_diamond",
}

_RE_AUX_NAME = re.compile(r"\._(?:proof|simp|cstage|closed)_\d|\.(?:match|eq)_\d+$")
_RE_COPY_NAME = re.compile(r"(?:CutCptCopy|SideCopy|LamCopy|\blam_copy\b|\bsigSpan_copy\b|_copy\d*$)")


def _is_aux(name: str, method: Optional[str]) -> bool:
    if method and method.startswith("aux_prefix:"):
        return True
    return bool(_RE_AUX_NAME.search(name))


def _is_copy_shell(name: str, module: Optional[str], copy_taint_ids: Set[int], did: int) -> bool:
    if did in copy_taint_ids:
        return True
    if module and (module.endswith(".CutCptCopy") or ".SideCopy." in module or module.endswith(".LamCopy")):
        return True
    return bool(_RE_COPY_NAME.search(name))


def build_clusters(
    kernel_db: str = DEFAULT_KERNEL_DB,
    tier1_db: Optional[str] = DEFAULT_TIER1_DB,
    out_path: Optional[str] = DEFAULT_OUT,
    split_threshold: int = 25000,
    min_dom_cluster: int = 1500,
    min_residual_cluster: int = 1500,
    max_edges_emit: int = 2500,
    verbose: bool = True,
) -> Dict[str, Any]:
    """Run deterministic kernel-aware blueprint clustering and boilerplate collapse."""
    t0 = time.time()
    ck = sqlite3.connect(f"file:{kernel_db}?mode=ro", uri=True)
    try:
        # 1. Load live declarations & dominator tree (tree_id=0, ALL proof view)
        n_decls_total = ck.execute("SELECT MAX(id) + 1 FROM decls").fetchone()[0] or 0
        if verbose:
            print(f"[cluster] loading kernel.db ({n_decls_total:,} decl slots)...", flush=True)

        name_of: List[str] = [""] * n_decls_total
        kind_of: List[str] = [""] * n_decls_total
        sighash_of: List[str] = [""] * n_decls_total
        flags_of = array.array("I", [0]) * n_decls_total
        live_of = bytearray(n_decls_total)
        fan_in_of = array.array("I", [0]) * n_decls_total

        live_ids: List[int] = []
        name_to_id: Dict[str, int] = {}
        for did, nm, knd, sh, flg, lm, fi in ck.execute(
            "SELECT id, name, kind, COALESCE(sighash,''), flags, live_mask, fan_in FROM decls"
        ):
            name_of[did] = nm
            kind_of[did] = knd
            sighash_of[did] = sh
            flags_of[did] = flg
            fan_in_of[did] = fi
            if lm != 0:
                live_of[did] = 1
                live_ids.append(did)
            name_to_id[nm] = did

        mod_of: List[Optional[str]] = [None] * n_decls_total
        method_of: List[Optional[str]] = [None] * n_decls_total
        for did, mod, meth in ck.execute("SELECT decl_id, module, method FROM decl_module"):
            mod_of[did] = mod
            method_of[did] = meth

        copy_taint_ids: Set[int] = set()
        compute_taint_ids: Dict[int, Set[str]] = collections.defaultdict(set)
        for cls, did in ck.execute("SELECT class, decl_id FROM taint_sources"):
            if cls in ("CutCptCopy", "kcopy"):
                copy_taint_ids.add(did)
            if cls in ("decide_kernel", "decide_kernel_pattern", "lean4lean_timeout", "slow_con_leche", "kexactB", "CutCptCopy", "kcopy"):
                compute_taint_ids[did].add(cls)

        # Load dominator tree tree_id=0 (ALL)
        children: Dict[int, List[int]] = collections.defaultdict(list)
        idom_of = array.array("i", [-1]) * n_decls_total
        depth_of = array.array("i", [-1]) * n_decls_total
        sub_sz_of = array.array("I", [0]) * n_decls_total
        roots: List[int] = []

        for did, idom, dep, sz in ck.execute(
            "SELECT decl_id, idom, depth, subtree_size FROM dom WHERE tree_id = 0"
        ):
            depth_of[did] = dep
            sub_sz_of[did] = sz
            if idom is None:
                idom_of[did] = -1
                roots.append(did)
            else:
                idom_of[did] = idom
                children[idom].append(did)

        # Load Tier 1 module metadata (statement wrappers, lines_wc, top_domain, forensic flags)
        stmt_wrapper_mods: Set[str] = set()
        mod_lines: Dict[str, int] = {}
        mod_domain: Dict[str, str] = {}
        tier1_total_mods = 0
        if tier1_db and os.path.exists(tier1_db):
            c1 = sqlite3.connect(f"file:{tier1_db}?mode=ro", uri=True)
            try:
                for mod, lwc, wrap, tdom in c1.execute(
                    "SELECT module, lines_wc, is_statement_wrapper, top_domain FROM module_fingerprints"
                ):
                    tier1_total_mods += 1
                    mod_lines[mod] = lwc
                    mod_domain[mod] = tdom
                    if wrap:
                        stmt_wrapper_mods.add(mod)
            finally:
                c1.close()

        # 2. Assign pillar lineage by walking down from dominator roots
        # Precedence order: pillar_theta overrides pillar_volume_lit (since theta sits inside every_character_of_literature_of_vWin)
        pillar_id_map: Dict[int, str] = {}
        for nm, pil in PILLAR_ROOT_NAMES.items():
            if nm in name_to_id:
                pillar_id_map[name_to_id[nm]] = pil

        pillar_of: Dict[int, str] = {}
        # BFS down dom tree from each root
        roots.sort(key=lambda r: (-sub_sz_of[r], r))
        primary_root = roots[0] if roots else -1
        for r in roots:
            start_pil = pillar_id_map.get(r, "tcb_mathlib_core" if r != primary_root else "shared_diamond")
            stack = [(r, start_pil)]
            while stack:
                u, pil = stack.pop()
                cur_pil = pillar_id_map.get(u, pil)
                pillar_of[u] = cur_pil
                for c in children.get(u, ()):
                    stack.append((c, cur_pil))

        # 3. Deterministic dominator frontier cut
        dom_cluster_roots: List[int] = []
        residual_nodes: List[Tuple[int, int]] = []  # (decl_id, split_parent_id)
        tcb_nodes: List[int] = []

        def _collect_subtree(root_u: int) -> List[int]:
            out_ids: List[int] = []
            st = [root_u]
            while st:
                x = st.pop()
                out_ids.append(x)
                st.extend(children.get(x, ()))
            return out_ids

        def _walk_frontier(u: int) -> None:
            ch = sorted(children.get(u, ()), key=lambda c: (-sub_sz_of[c], c))
            big = [c for c in ch if sub_sz_of[c] >= min_dom_cluster]
            if sub_sz_of[u] >= split_threshold and big:
                residual_nodes.append((u, u))
                for c in ch:
                    if sub_sz_of[c] < min_dom_cluster:
                        for x in _collect_subtree(c):
                            residual_nodes.append((x, u))
                for c in big:
                    _walk_frontier(c)
            else:
                dom_cluster_roots.append(u)

        for r in roots:
            if sub_sz_of[r] >= min_dom_cluster:
                _walk_frontier(r)
            else:
                for x in _collect_subtree(r):
                    tcb_nodes.append(x)

        # Build explicit cluster membership lists (exact partition of all live decls!)
        raw_clusters: List[Dict[str, Any]] = []

        # (a) Dominator frontier clusters
        for u in dom_cluster_roots:
            members = _collect_subtree(u)
            raw_clusters.append({
                "kind": "dom_subtree",
                "pillar": pillar_of.get(u, "shared_diamond"),
                "root_decl_id": u,
                "root_decl": name_of[u],
                "dom_depth": int(depth_of[u]),
                "idom_name": name_of[idom_of[u]] if idom_of[u] >= 0 else None,
                "members": members,
                "title_hint": name_of[u],
            })

        # (b) Residual neighborhoods under split parents, grouped by (pillar, folder_l2)
        res_groups: Dict[Tuple[str, str], List[int]] = collections.defaultdict(list)
        for did, _sp in residual_nodes:
            pil = pillar_of.get(did, "shared_diamond")
            mod = mod_of[did]
            if mod:
                parts = mod.split(".")
                fl2 = f"{parts[0]}.{parts[1]}" if len(parts) >= 2 else parts[0]
            else:
                fl2 = "<library_or_unmatched>"
            res_groups[(pil, fl2)].append(did)

        small_tails: Dict[str, List[int]] = collections.defaultdict(list)
        for (pil, fl2), mems in sorted(res_groups.items(), key=lambda kv: (-len(kv[1]), kv[0])):
            if len(mems) >= min_residual_cluster:
                # Pick highest-subtree member as representative anchor
                rep = max(mems, key=lambda x: (sub_sz_of[x], fan_in_of[x], -x))
                raw_clusters.append({
                    "kind": "residual_neighborhood",
                    "pillar": pil,
                    "root_decl_id": rep,
                    "root_decl": name_of[rep],
                    "dom_depth": int(depth_of[rep]),
                    "idom_name": name_of[idom_of[rep]] if idom_of[rep] >= 0 else None,
                    "members": mems,
                    "title_hint": f"{pil}::{fl2}",
                })
            else:
                small_tails[pil].extend(mems)

        for pil, mems in sorted(small_tails.items()):
            if not mems:
                continue
            rep = max(mems, key=lambda x: (sub_sz_of[x], fan_in_of[x], -x))
            raw_clusters.append({
                "kind": "residual_tail",
                "pillar": pil,
                "root_decl_id": rep,
                "root_decl": name_of[rep],
                "dom_depth": int(depth_of[rep]),
                "idom_name": name_of[idom_of[rep]] if idom_of[rep] >= 0 else None,
                "members": mems,
                "title_hint": f"{pil}::<residual_tail>",
            })

        # (c) TCB / Mathlib root cluster (all live decls outside big dominator roots)
        if tcb_nodes:
            rep = max(tcb_nodes, key=lambda x: (fan_in_of[x], sub_sz_of[x], -x))
            raw_clusters.append({
                "kind": "tcb_library_root",
                "pillar": "tcb_mathlib_core",
                "root_decl_id": rep,
                "root_decl": name_of[rep],
                "dom_depth": 0,
                "idom_name": None,
                "members": tcb_nodes,
                "title_hint": "TCB & Shared Mathlib/Core Library",
            })

        # Sort clusters deterministically by (-live_decls, title_hint) and assign BP001..
        raw_clusters.sort(key=lambda c: (-len(c["members"]), c["pillar"], c["title_hint"]))
        cluster_idx_of = array.array("i", [-1]) * n_decls_total
        for idx, cl in enumerate(raw_clusters):
            cl["cluster_id"] = f"BP{idx + 1:03d}"
            for did in cl["members"]:
                cluster_idx_of[did] = idx

        # Verify exact 100% partition of all live decls in tree_id=0!
        assigned_live = sum(len(cl["members"]) for cl in raw_clusters)
        if assigned_live != len(live_ids):
            # Any live decl not in dom(tree_id=0) (should be 0, defensive check)
            missing = [d for d in live_ids if cluster_idx_of[d] == -1]
            if missing:
                idx = len(raw_clusters)
                raw_clusters.append({
                    "kind": "unassigned_live",
                    "pillar": "tcb_mathlib_core",
                    "root_decl_id": missing[0],
                    "root_decl": name_of[missing[0]],
                    "dom_depth": -1,
                    "idom_name": None,
                    "members": missing,
                    "title_hint": "Unassigned live decls",
                    "cluster_id": f"BP{idx + 1:03d}",
                })
                for did in missing:
                    cluster_idx_of[did] = idx

        # 4. Mutually exclusive live-cone boilerplate collapse (aux > copy_shell > stmt_wrapper > k1n_dup > core)
        # Global k1n deduplication across user non-wrapper non-copy theorems (lowest decl_id = canonical first def)
        seen_k1n: Set[str] = set()
        role_of = bytearray(n_decls_total)  # 0=core, 1=aux, 2=copy_shell, 3=stmt_wrapper, 4=k1n_dup
        for did in sorted(live_ids):
            nm = name_of[did]
            mod = mod_of[did]
            meth = method_of[did]
            if _is_aux(nm, meth):
                role_of[did] = 1
            elif _is_copy_shell(nm, mod, copy_taint_ids, did):
                role_of[did] = 2
            elif mod and mod in stmt_wrapper_mods:
                role_of[did] = 3
            elif kind_of[did] == "thm" and sighash_of[did]:
                sh = sighash_of[did]
                if sh in seen_k1n:
                    role_of[did] = 4
                else:
                    seen_k1n.add(sh)
                    role_of[did] = 0
            else:
                role_of[did] = 0

        # 5. Stream exact inter-cluster directed edges from kernel.db (mode=ro)
        if verbose:
            print(f"[cluster] built {len(raw_clusters)} coarse clusters; streaming inter-cluster edges...", flush=True)
        t_edge = time.time()
        n_cl = len(raw_clusters)
        intra_edges = [0] * n_cl
        # (src_c, dst_c) -> [type_only, value_only, both]
        edge_agg: Dict[Tuple[int, int], List[int]] = {}
        ext_fan_in = array.array("I", [0]) * n_decls_total

        cur = ck.execute("SELECT src, dst, kind FROM edges")
        while True:
            batch = cur.fetchmany(250000)
            if not batch:
                break
            for src, dst, knd in batch:
                cs = cluster_idx_of[src]
                cd = cluster_idx_of[dst]
                if cs < 0 or cd < 0:
                    continue
                if cs == cd:
                    intra_edges[cs] += 1
                else:
                    ext_fan_in[dst] += 1
                    key = (cs, cd)
                    acc = edge_agg.get(key)
                    if acc is None:
                        acc = [0, 0, 0]
                        edge_agg[key] = acc
                    if knd == 1:
                        acc[0] += 1
                    elif knd == 2:
                        acc[1] += 1
                    else:
                        acc[2] += 1
        if verbose:
            print(f"[cluster] aggregated {len(edge_agg):,} inter-cluster edge pairs in {time.time()-t_edge:.1f}s", flush=True)

        # Out-degree & in-degree in coarse cluster DAG
        out_deg = [0] * n_cl
        in_deg = [0] * n_cl
        for (cs, cd) in edge_agg:
            out_deg[cs] += 1
            in_deg[cd] += 1

        # 6. Summarize each cluster cleanly (ZERO raw .lean text!)
        clusters_out: List[Dict[str, Any]] = []
        tot_aux = tot_copy = tot_wrap = tot_k1n = tot_core = 0
        all_live_mods: Set[str] = set()
        by_pillar: Dict[str, Dict[str, Any]] = collections.defaultdict(
            lambda: {"clusters": 0, "live_decls": 0, "effective_core_decls": 0, "live_modules": set()}
        )

        for idx, cl in enumerate(raw_clusters):
            mems = cl["members"]
            n_mem = len(mems)
            c_aux = c_copy = c_wrap = c_k1n = c_core = 0
            fl2_ctr: collections.Counter = collections.Counter()
            ns2_ctr: collections.Counter = collections.Counter()
            dom_ctr: collections.Counter = collections.Counter()
            cl_mods: Set[str] = set()
            comp_flags: collections.Counter = collections.Counter()

            for did in mems:
                rl = role_of[did]
                if rl == 1:
                    c_aux += 1
                elif rl == 2:
                    c_copy += 1
                elif rl == 3:
                    c_wrap += 1
                elif rl == 4:
                    c_k1n += 1
                else:
                    c_core += 1

                mod = mod_of[did]
                if mod:
                    cl_mods.add(mod)
                    parts = mod.split(".")
                    fl2_ctr[f"{parts[0]}.{parts[1]}" if len(parts) >= 2 else parts[0]] += 1
                    td = mod_domain.get(mod)
                    if td and td != "none":
                        dom_ctr[td] += 1
                if rl != 1:
                    np = name_of[did].split(".")
                    ns2_ctr[f"{np[0]}.{np[1]}" if len(np) >= 2 else np[0]] += 1
                if flags_of[did] & 3:
                    comp_flags["kernel_decide_refl"] += 1
                if did in compute_taint_ids:
                    for fl in compute_taint_ids[did]:
                        comp_flags[fl] += 1

            tot_aux += c_aux
            tot_copy += c_copy
            tot_wrap += c_wrap
            tot_k1n += c_k1n
            tot_core += c_core
            all_live_mods.update(cl_mods)

            user_decls = n_mem - c_aux
            collapse_pct = round(100.0 * (n_mem - c_core) / max(1, n_mem), 2)
            lines_sum = sum(mod_lines.get(m, 0) for m in cl_mods)

            # Top 8 boundary decls: root decl first, then highest external fan-in core user decls
            root_id = cl["root_decl_id"]
            cand_bd = [d for d in mems if role_of[d] == 0 and d != root_id]
            cand_bd.sort(key=lambda d: (-ext_fan_in[d], -sub_sz_of[d], d))
            bd_ids = ([root_id] if root_id >= 0 else []) + cand_bd[:7]
            boundary_decls = [
                {
                    "id": int(d),
                    "name": name_of[d],
                    "kind": kind_of[d],
                    "module": mod_of[d],
                    "subtree_size": int(sub_sz_of[d]),
                    "ext_fan_in": int(ext_fan_in[d]),
                    "sighash": sighash_of[d] or None,
                }
                for d in bd_ids
            ]

            pil = cl["pillar"]
            bp = by_pillar[pil]
            bp["clusters"] += 1
            bp["live_decls"] += n_mem
            bp["effective_core_decls"] += c_core
            bp["live_modules"].update(cl_mods)

            clusters_out.append({
                "cluster_id": cl["cluster_id"],
                "kind": cl["kind"],
                "pillar": pil,
                "title_hint": cl["title_hint"],
                "root_decl": cl["root_decl"],
                "root_decl_id": int(root_id),
                "dom_depth": cl["dom_depth"],
                "idom_name": cl["idom_name"],
                "live_decls": n_mem,
                "user_decls": user_decls,
                "aux_collapsed": c_aux,
                "copy_shell_collapsed": c_copy,
                "stmt_wrapper_collapsed": c_wrap,
                "k1n_dup_collapsed": c_k1n,
                "effective_core_decls": c_core,
                "collapse_pct": collapse_pct,
                "live_modules": len(cl_mods),
                "total_lines_wc": lines_sum,
                "top_folders_l2": [{"folder": k, "decls": v} for k, v in fl2_ctr.most_common(4)],
                "top_namespaces": [{"namespace": k, "decls": v} for k, v in ns2_ctr.most_common(4)],
                "tier1_top_domain": dom_ctr.most_common(1)[0][0] if dom_ctr else "none",
                "compute_flags": dict(comp_flags),
                "intra_edges": intra_edges[idx],
                "out_degree_clusters": out_deg[idx],
                "in_degree_clusters": in_deg[idx],
                "boundary_decls": boundary_decls,
                "provenance": "L",
            })

        # Format edges sorted by total_edges DESC
        edges_all = [
            {
                "src": raw_clusters[cs]["cluster_id"],
                "dst": raw_clusters[cd]["cluster_id"],
                "type_edges": acc[0],
                "value_edges": acc[1],
                "both_edges": acc[2],
                "total_edges": acc[0] + acc[1] + acc[2],
                "provenance": "L",
            }
            for (cs, cd), acc in edge_agg.items()
        ]
        edges_all.sort(key=lambda e: (-e["total_edges"], e["src"], e["dst"]))
        edges_emitted = edges_all[:max_edges_emit]

        by_pillar_json = {
            pil: {
                "clusters": d["clusters"],
                "live_decls": d["live_decls"],
                "effective_core_decls": d["effective_core_decls"],
                "collapse_pct": round(100.0 * (d["live_decls"] - d["effective_core_decls"]) / max(1, d["live_decls"]), 2),
                "live_modules": len(d["live_modules"]),
            }
            for pil, d in sorted(by_pillar.items(), key=lambda kv: -kv[1]["live_decls"])
        }

        kind_counts = collections.Counter(c["kind"] for c in clusters_out)
        n_live = len(live_ids)
        result: Dict[str, Any] = {
            "schema": SCHEMA_VERSION,
            "provenance": "[L] extracted deterministically from outputs/kernel/kernel.db (dom tree ALL) + outputs/flirt/tier1.db",
            "params": {
                "split_threshold": split_threshold,
                "min_dom_cluster": min_dom_cluster,
                "min_residual_cluster": min_residual_cluster,
                "dom_tree": "ALL (tree_id=0)",
                "collapse_precedence": "aux > copy_shell > stmt_wrapper > k1n_dup > effective_core",
            },
            "totals": {
                "live_decls": n_live,
                "clusters_count": len(clusters_out),
                "clusters_by_kind": dict(kind_counts),
                "aux_collapsed": tot_aux,
                "copy_shell_collapsed": tot_copy,
                "stmt_wrapper_collapsed": tot_wrap,
                "k1n_dup_collapsed": tot_k1n,
                "effective_core_decls": tot_core,
                "collapse_pct": round(100.0 * (n_live - tot_core) / max(1, n_live), 2),
                "inter_cluster_edge_pairs_total": len(edges_all),
                "inter_cluster_edge_pairs_emitted": len(edges_emitted),
                "live_modules_covered": len(all_live_mods),
                "tier1_total_modules": tier1_total_mods,
                "dead_modules_not_in_kernel": max(0, tier1_total_mods - len(all_live_mods)) if tier1_total_mods else None,
            },
            "by_pillar": by_pillar_json,
            "clusters": clusters_out,
            "edges": edges_emitted,
            "elapsed_seconds": round(time.time() - t0, 2),
        }

        if out_path:
            os.makedirs(os.path.dirname(os.path.abspath(out_path)), exist_ok=True)
            with open(out_path, "w", encoding="utf-8") as f:
                json.dump(result, f, indent=2, sort_keys=True, ensure_ascii=False)
                f.write("\n")

        if verbose:
            t = result["totals"]
            print(
                f"[cluster] wrote {out_path}: {t['clusters_count']} clusters covering {t['live_decls']:,} live decls "
                f"-> {t['effective_core_decls']:,} effective core decls ({t['collapse_pct']}% boilerplate collapsed) "
                f"in {result['elapsed_seconds']}s",
                flush=True,
            )
        return result
    finally:
        ck.close()


def main(argv: Optional[Sequence[str]] = None) -> int:
    ap = argparse.ArgumentParser(description="FLIRT Phase 4: kernel-aware coarse blueprint clustering & boilerplate collapse")
    ap.add_argument("--kernel-db", default=DEFAULT_KERNEL_DB)
    ap.add_argument("--tier1-db", default=DEFAULT_TIER1_DB)
    ap.add_argument("--out", default=DEFAULT_OUT)
    ap.add_argument("--split-threshold", type=int, default=25000)
    ap.add_argument("--min-dom-cluster", type=int, default=1500)
    ap.add_argument("--min-residual-cluster", type=int, default=1500)
    ap.add_argument("--max-edges", type=int, default=2500)
    ap.add_argument("--quiet", action="store_true")
    a = ap.parse_args(argv)
    build_clusters(
        kernel_db=a.kernel_db,
        tier1_db=a.tier1_db or None,
        out_path=a.out or None,
        split_threshold=a.split_threshold,
        min_dom_cluster=a.min_dom_cluster,
        min_residual_cluster=a.min_residual_cluster,
        max_edges_emit=a.max_edges,
        verbose=not a.quiet,
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
