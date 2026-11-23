#!/usr/bin/env python3
"""leanre.export_site — Standalone static offline HTML explorer generator.

Generates a single self-contained, zero-CDN, XSS-safe, deterministic HTML file
ready for offline inspection or GitHub Pages hosting. Embeds compact summaries
of:
  - `leanre.decomp/v1` proof blueprints (`outputs/decomp/*.json`)
  - `leanre.trim/1` virtual-strip waterfall (`trim_report.json`)
  - `leanre.flirt_atlas/v1` cluster atlas (`cluster_labels_141.json`)
  - `kernel.db` dominator spine, live/dead split, roots & unread `bundles`

Guardrails:
  - Python 3.9+ stdlib only; zero third-party dependencies or external CDNs.
  - Strictly read-only SQLite access (`mode=ro`, `PRAGMA query_only=1`).
  - Refuses symlink output targets and ignores symlinked inputs in `decomp_dir`.
  - XSS-safe JSON embedding (`<`, `>`, `&` escaped) + safe DOM rendering
    (no `innerHTML` with data strings).
  - Deterministic output (sorted keys/rows, zero timestamps or host paths).
"""
from __future__ import annotations

import argparse
import collections
import html
import json
import os
import sqlite3
import sys
import tempfile
from typing import Any, Dict, List, Optional, Sequence, Set, Tuple

_HERE = os.path.dirname(os.path.abspath(__file__))
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)

SCHEMA_VERSION = "leanre.static_site/1"
MAX_TEXT_SUMMARY = 280
MAX_HEADER_LEN = 220


def _open_ro(path: str) -> sqlite3.Connection:
    real = os.path.realpath(path)
    if not os.path.isfile(real):
        raise FileNotFoundError(f"Missing SQLite database: {path}")
    conn = sqlite3.connect(f"file:{real}?mode=ro", uri=True)
    conn.execute("PRAGMA query_only=1")
    return conn


def _safe_write_text(out_path: str, text: str) -> None:
    if os.path.islink(out_path):
        raise ValueError(f"Refusing to write through symlink: {out_path}")
    parent = os.path.dirname(os.path.abspath(out_path))
    if parent:
        os.makedirs(parent, exist_ok=True)
    with open(out_path, "w", encoding="utf-8") as f:
        f.write(text)


def _clip(text: Any, limit: int = MAX_TEXT_SUMMARY) -> str:
    if text is None:
        return ""
    s = " ".join(str(text).split())
    if len(s) <= limit:
        return s
    return s[: max(0, limit - 1)] + "…"


def _safe_github_url(url: Any) -> Optional[str]:
    if isinstance(url, str) and url.startswith("https://github.com/"):
        return url
    return None


def _escape_json_for_script(obj: Any) -> str:
    """Serialize JSON safely for embedding inside `<script type="application/json">`."""
    raw = json.dumps(obj, ensure_ascii=True, sort_keys=True, separators=(",", ":"))
    return (
        raw.replace("<", "\\u003c")
        .replace(">", "\\u003e")
        .replace("&", "\\u0026")
    )


def _summarize_blueprint(
    doc: Dict[str, Any],
    filename: str,
    max_nodes: int = 250,
    max_edges: int = 450,
) -> Dict[str, Any]:
    raw_nodes = [n for n in (doc.get("nodes") or []) if isinstance(n, dict) and n.get("id")]
    raw_edges = [e for e in (doc.get("edges") or []) if isinstance(e, dict) and e.get("src") and e.get("dst")]
    raw_claims = doc.get("claims") or []
    raw_horn = doc.get("horn") or []
    raw_opaque = doc.get("opaque") or []

    verdict_counts: collections.Counter[str] = collections.Counter()
    status_counts: collections.Counter[str] = collections.Counter()
    role_counts: collections.Counter[str] = collections.Counter()
    tag_counts: collections.Counter[str] = collections.Counter()

    for n in raw_nodes:
        verdict_counts[str(n.get("verdict") or "unknown")] += 1
        status_counts[str(n.get("status") or "UNKNOWN")] += 1
        role_counts[str(n.get("role") or "unknown")] += 1
        tag_counts[str(n.get("tag") or "L")] += 1

    root_id = str(doc.get("root") or "")

    def _node_rank(n: Dict[str, Any]) -> Tuple[int, int, int, str]:
        nid = str(n.get("id") or "")
        dom = n.get("dom") if isinstance(n.get("dom"), dict) else {}
        sub = int(dom.get("subtree") or 0)
        st_rank = 0 if n.get("status") == "READ" else (1 if n.get("status") == "PARTIAL" else 2)
        return (0 if nid == root_id else 1, st_rank, -sub, nid)

    ranked_nodes = sorted(raw_nodes, key=_node_rank)[: max(1, max_nodes)]
    kept_ids: Set[str] = {str(n["id"]) for n in ranked_nodes}

    nodes_out: List[Dict[str, Any]] = []
    for n in ranked_nodes:
        dom = n.get("dom") if isinstance(n.get("dom"), dict) else None
        nodes_out.append({
            "id": str(n["id"]),
            "kind": str(n.get("kind") or ""),
            "module": _clip(n.get("module"), 140),
            "anchor": _clip(n.get("anchor"), 140),
            "header": _clip(n.get("header"), MAX_HEADER_LEN),
            "role": str(n.get("role") or ""),
            "status": str(n.get("status") or ""),
            "verdict": str(n.get("verdict") or ""),
            "tag": str(n.get("tag") or "L"),
            "dom_depth": int(dom["depth"]) if dom and dom.get("depth") is not None else None,
            "dom_subtree": int(dom["subtree"]) if dom and dom.get("subtree") is not None else None,
            "idom": dom.get("idom") if dom else None,
            "summary": _clip(n.get("summary"), MAX_TEXT_SUMMARY),
        })

    edges_filtered = [
        e for e in raw_edges
        if str(e["src"]) in kept_ids and str(e["dst"]) in kept_ids
    ]
    edges_filtered.sort(key=lambda e: (str(e["src"]), str(e["dst"]), str(e.get("rel") or "")))
    edges_out = [
        {
            "src": str(e["src"]),
            "dst": str(e["dst"]),
            "rel": str(e.get("rel") or "both"),
            "tag": str(e.get("tag") or "L"),
        }
        for e in edges_filtered[: max(0, max_edges)]
    ]

    claims_out: List[Dict[str, str]] = []
    for c in raw_claims[:40]:
        if isinstance(c, dict):
            claims_out.append({
                "tag": str(c.get("tag") or "L"),
                "text": _clip(c.get("text"), MAX_TEXT_SUMMARY),
            })
        elif isinstance(c, str):
            claims_out.append({"tag": "L", "text": _clip(c, MAX_TEXT_SUMMARY)})

    pins_in = doc.get("pins") if isinstance(doc.get("pins"), dict) else {}
    safe_pins = {
        str(k): _clip(v, 80)
        for k, v in sorted(pins_in.items())
        if isinstance(v, (str, int, float, bool)) and not str(v).startswith("/")
    }

    return {
        "file": os.path.basename(filename),
        "pillar": str(doc.get("pillar") or ""),
        "root": root_id,
        "pins": safe_pins,
        "counts": {
            "nodes": len(raw_nodes),
            "nodes_shown": len(nodes_out),
            "edges": len(raw_edges),
            "edges_shown": len(edges_out),
            "horn": len(raw_horn),
            "claims": len(raw_claims),
            "opaque": len(raw_opaque),
            "verdicts": dict(sorted(verdict_counts.items())),
            "statuses": dict(sorted(status_counts.items())),
            "roles": dict(sorted(role_counts.items())),
            "tags": dict(sorted(tag_counts.items())),
        },
        "claims": claims_out,
        "nodes": nodes_out,
        "edges": edges_out,
    }


def _summarize_trim_report(doc: Dict[str, Any]) -> Dict[str, Any]:
    baseline = doc.get("baseline") if isinstance(doc.get("baseline"), dict) else {}
    wf = doc.get("c8_waterfall") if isinstance(doc.get("c8_waterfall"), dict) else {}
    steps_in = wf.get("steps") if isinstance(wf.get("steps"), list) else []

    steps_out: List[Dict[str, Any]] = []
    for st in steps_in:
        if not isinstance(st, dict):
            continue
        steps_out.append({
            "step_id": str(st.get("step_id") or ""),
            "label": _clip(st.get("label"), 180),
            "precision": _clip(st.get("precision"), 100),
            "before": st.get("before") or {},
            "removed": st.get("removed") or {},
            "after": st.get("after") or {},
        })

    epistemic = doc.get("epistemic_scope") if isinstance(doc.get("epistemic_scope"), dict) else {}
    pins_in = doc.get("pins") if isinstance(doc.get("pins"), dict) else {}
    safe_pins = {
        k: pins_in[k]
        for k in ("mirror_commit", "solution_uncompressed_sha256", "workers_used", "elapsed_seconds")
        if k in pins_in
    }

    return {
        "schema": str(doc.get("schema") or "leanre.trim/1"),
        "provenance": _clip(doc.get("provenance"), 200),
        "pins": safe_pins,
        "epistemic_scope": {str(k): _clip(v, 220) for k, v in sorted(epistemic.items())},
        "baseline": {
            "total_modules": baseline.get("total_modules"),
            "live_modules_total": baseline.get("live_modules_total"),
            "unused_zero_kernel_modules": baseline.get("unused_zero_kernel_modules"),
            "total_lines_wc": baseline.get("total_lines_wc"),
            "total_bytes": baseline.get("total_bytes"),
            "kernel_total_records": baseline.get("kernel_total_records"),
            "kernel_live_records": baseline.get("kernel_live_records"),
            "kernel_live_value_nodes": baseline.get("kernel_live_value_nodes"),
            "kernel_project_matched_live": baseline.get("kernel_project_matched_live"),
            "kernel_external_library_live": baseline.get("kernel_external_library_live"),
        },
        "steps": steps_out,
        "irreducible_core": wf.get("irreducible_core_estimate") or {},
        "further_headroom": wf.get("further_refactoring_headroom_not_in_main_waterfall") or {},
    }


def _summarize_cluster_atlas(doc: Dict[str, Any], max_clusters: int = 200) -> Dict[str, Any]:
    clusters_in = doc.get("clusters") if isinstance(doc.get("clusters"), list) else []
    clusters_sorted = sorted(
        (c for c in clusters_in if isinstance(c, dict)),
        key=lambda c: str(c.get("cluster_id") or ""),
    )[: max(0, max_clusters)]

    clusters_out: List[Dict[str, Any]] = []
    for c in clusters_sorted:
        cnt = c.get("counts") if isinstance(c.get("counts"), dict) else {}
        imp = c.get("imports_and_tier1") if isinstance(c.get("imports_and_tier1"), dict) else {}
        bl = c.get("blinded_label") if isinstance(c.get("blinded_label"), dict) else {}
        ma = c.get("mismatch_audit") if isinstance(c.get("mismatch_audit"), dict) else {}
        reps_in = c.get("top3_rep_decls") if isinstance(c.get("top3_rep_decls"), list) else []
        reps_out = []
        for r in reps_in[:3]:
            if not isinstance(r, dict):
                continue
            reps_out.append({
                "name": str(r.get("name") or ""),
                "kind": str(r.get("kind") or ""),
                "module": str(r.get("module") or ""),
                "line": r.get("line"),
                "subtree_size": r.get("subtree_size"),
                "github_url": _safe_github_url(r.get("github_url")),
            })
        clusters_out.append({
            "cluster_id": str(c.get("cluster_id") or ""),
            "kind": str(c.get("kind") or ""),
            "pillar": str(c.get("pillar") or ""),
            "root_decl": str(c.get("root_decl") or ""),
            "dom_depth": c.get("dom_depth"),
            "idom_name": c.get("idom_name"),
            "counts": {
                "live_decls": cnt.get("live_decls", 0),
                "user_decls": cnt.get("user_decls", 0),
                "effective_core_decls": cnt.get("effective_core_decls", 0),
                "collapse_pct": cnt.get("collapse_pct", 0.0),
                "live_modules": cnt.get("live_modules", 0),
                "dead_source_decls_in_live_modules": cnt.get("dead_source_decls_in_live_modules", 0),
            },
            "tier1_top_domain": imp.get("tier1_top_domain"),
            "blinded_label": {
                "label": _clip(bl.get("label"), 160),
                "primary_domain": bl.get("primary_domain"),
                "secondary_domain": bl.get("secondary_domain"),
                "confidence": bl.get("confidence"),
                "provenance": bl.get("provenance", "M"),
            },
            "mismatch_audit": {
                "status": ma.get("status"),
                "severity": ma.get("severity"),
                "folder_l2": ma.get("folder_l2"),
                "reason": _clip(ma.get("reason"), 220),
            },
            "top3_rep_decls": reps_out,
        })

    return {
        "schema": str(doc.get("schema") or "leanre.flirt_atlas/v1"),
        "mirror_commit": str(doc.get("mirror_commit") or ""),
        "epistemic_note": _clip(doc.get("epistemic_note"), 260),
        "totals": doc.get("totals") or {},
        "clusters_total": len(clusters_in),
        "clusters": clusters_out,
    }


def _short_decl_name(name: str) -> str:
    s = str(name or "")
    return s.rsplit(".", 1)[-1] if "." in s else s


def _island_slug(lead_name: str) -> str:
    short = _short_decl_name(lead_name)
    if short == "strongResolutionOfSingularitiesCharZero":
        return "strongResolution"
    return short or "island"


def _summarize_portability(doc: Dict[str, Any]) -> Dict[str, Any]:
    raw_targets = [t for t in (doc.get("targets") or []) if isinstance(t, dict)]
    overlap = doc.get("overlap") if isinstance(doc.get("overlap"), dict) else {}
    n = len(raw_targets)
    proj_mat = overlap.get("project_decls_matrix")
    jacc_mat = overlap.get("project_jaccard_matrix")
    has_mat = isinstance(proj_mat, list) and len(proj_mat) == n and all(
        isinstance(row, list) and len(row) == n for row in proj_mat
    )

    visited: Set[int] = set()
    components: List[List[int]] = []
    for i in range(n):
        if i in visited:
            continue
        comp: List[int] = []
        q: collections.deque[int] = collections.deque([i])
        visited.add(i)
        while q:
            u = q.popleft()
            comp.append(u)
            if has_mat:
                for v in range(n):
                    if v not in visited and v != u:
                        val = proj_mat[u][v]
                        if isinstance(val, (int, float)) and val > 0:
                            visited.add(v)
                            q.append(v)
        comp.sort()
        components.append(comp)

    islands: List[Dict[str, Any]] = []
    island_by_member: Dict[int, Dict[str, Any]] = {}
    for idx, comp in enumerate(components, 1):
        members = [raw_targets[m] for m in comp]
        lead = max(
            members,
            key=lambda t: (int((t.get("cone") or {}).get("project_decls") or 0), str(t.get("name") or "")),
        )
        lead_name = str(lead.get("name") or "")
        slug = _island_slug(lead_name)
        inter_max = 0
        if has_mat:
            cset = set(comp)
            for u in comp:
                for v in range(n):
                    if v not in cset:
                        val = int(proj_mat[u][v] or 0)
                        if val > inter_max:
                            inter_max = val
        proj_vals = [int((m.get("cone") or {}).get("project_decls") or 0) for m in members]
        spec_vals = [int((m.get("cone") or {}).get("spec_cone_project_decls") or 0) for m in members]
        ext_vals = [int((m.get("boundary") or {}).get("direct_external_decls") or 0) for m in members]
        tiers = sorted({str((m.get("contamination") or {}).get("tier") or "unknown") for m in members})
        isl = {
            "id": f"island_{idx}",
            "index": idx,
            "slug": slug,
            "lead_target": lead_name,
            "lead_short": _short_decl_name(lead_name),
            "member_indices": comp,
            "member_names": [str(m.get("name") or "") for m in members],
            "member_shorts": [_short_decl_name(str(m.get("name") or "")) for m in members],
            "tiers": tiers,
            "max_project_decls": max(proj_vals) if proj_vals else 0,
            "min_spec_cone_project_decls": min(spec_vals) if spec_vals else 0,
            "max_spec_cone_project_decls": max(spec_vals) if spec_vals else 0,
            "max_direct_external_decls": max(ext_vals) if ext_vals else 0,
            "inter_island_project_overlap": inter_max,
            "pairwise_disjoint": inter_max == 0,
        }
        islands.append(isl)
        for mi in comp:
            island_by_member[mi] = isl

    targets_out: List[Dict[str, Any]] = []
    for idx, t in enumerate(raw_targets):
        cone = t.get("cone") if isinstance(t.get("cone"), dict) else {}
        bnd = t.get("boundary") if isinstance(t.get("boundary"), dict) else {}
        cont = t.get("contamination") if isinstance(t.get("contamination"), dict) else {}
        isl = island_by_member.get(idx) or {}
        top_prefs = [
            {
                "prefix": _clip(p.get("prefix"), 80),
                "distinct_decls": int(p.get("distinct_decls") or 0),
                "type_decls": int(p.get("type_decls") or 0),
                "call_edges": int(p.get("call_edges") or 0),
            }
            for p in (bnd.get("top_external_prefixes") or [])[:12]
            if isinstance(p, dict) and p.get("prefix")
        ]
        targets_out.append({
            "index": idx,
            "name": str(t.get("name") or ""),
            "short_name": _short_decl_name(str(t.get("name") or "")),
            "kind": str(t.get("kind") or ""),
            "module": _clip(t.get("module"), 180),
            "sighash": _clip(t.get("sighash"), 64),
            "island_id": str(isl.get("id") or ""),
            "island_slug": str(isl.get("slug") or ""),
            "cone": {
                "total_decls": int(cone.get("total_decls") or 0),
                "project_decls": int(cone.get("project_decls") or 0),
                "external_decls": int(cone.get("external_decls") or 0),
                "spec_cone_total_decls": int(cone.get("spec_cone_total_decls") or 0),
                "spec_cone_project_decls": int(cone.get("spec_cone_project_decls") or 0),
                "dom_subtree_size": int(cone.get("dom_subtree_size") or 0),
                "dom_depth": cone.get("dom_depth"),
                "module_count": int(cone.get("module_count") or 0),
                "vn1_forwarding_aliases": int(cone.get("vn1_forwarding_aliases") or 0),
            },
            "boundary": {
                "direct_external_decls": int(bnd.get("direct_external_decls") or 0),
                "direct_external_type_decls": int(bnd.get("direct_external_type_decls") or 0),
                "direct_call_edges": int(bnd.get("direct_call_edges") or 0),
                "distinct_prefixes_total": int(bnd.get("distinct_prefixes_total") or 0),
                "top_external_prefixes": top_prefs,
            },
            "contamination": {
                "tier": str(cont.get("tier") or "unknown"),
                "reasons": [_clip(r, 200) for r in (cont.get("reasons") or [])[:5]],
                "axioms": [str(a) for a in (cont.get("axioms") or [])[:12]],
                "non_standard_axioms": [str(a) for a in (cont.get("non_standard_axioms") or [])[:12]],
                "has_sorry": bool(cont.get("has_sorry")),
                "mega_records_count": len(cont.get("mega_records") or []),
                "significant_root_dirs": [str(r) for r in (cont.get("significant_root_dirs") or [])[:8]],
            },
        })

    pins_in = doc.get("pins") if isinstance(doc.get("pins"), dict) else {}
    safe_pins = {
        str(k): _clip(v, 80)
        for k, v in sorted(pins_in.items())
        if isinstance(v, (str, int, float, bool)) and not str(v).startswith("/") and k != "elapsed_seconds"
    }
    union_sum = overlap.get("union_summary") if isinstance(overlap.get("union_summary"), dict) else {}
    standalone_cnt = sum(1 for t in targets_out if t["contamination"]["tier"] == "standalone-ready")
    scoped_cnt = sum(1 for t in targets_out if t["contamination"]["tier"] == "scoped")

    return {
        "schema": str(doc.get("schema") or "leanre.portability/1"),
        "pins": safe_pins,
        "summary": {
            "targets_count": len(targets_out),
            "islands_count": len(islands),
            "pairwise_disjoint_islands": sum(1 for isl in islands if isl["pairwise_disjoint"]),
            "standalone_ready_count": standalone_cnt,
            "scoped_count": scoped_cnt,
            "union_total_decls": union_sum.get("union_total_decls"),
            "union_project_decls": union_sum.get("union_project_decls"),
            "union_external_decls": union_sum.get("union_external_decls"),
            "union_module_count": union_sum.get("union_module_count"),
        },
        "islands": islands,
        "targets": targets_out,
        "overlap": {
            "target_names": [t["name"] for t in targets_out],
            "short_names": [t["short_name"] for t in targets_out],
            "island_ids": [t["island_id"] for t in targets_out],
            "project_decls_matrix": proj_mat if has_mat else [],
            "project_jaccard_matrix": jacc_mat if (isinstance(jacc_mat, list) and len(jacc_mat) == n) else [],
            "union_summary": union_sum,
        },
    }


def _summarize_kernel_db(
    kernel_db_path: str,
    src_root: Optional[str] = None,
    with_bundles: Optional[bool] = None,
) -> Dict[str, Any]:
    conn = _open_ro(kernel_db_path)
    try:
        total_decls = int(conn.execute("SELECT COUNT(*) FROM decls").fetchone()[0])
        live_decls = int(conn.execute("SELECT COUNT(*) FROM decls WHERE live_mask != 0").fetchone()[0])
        dead_decls = total_decls - live_decls
        total_edges = int(conn.execute("SELECT COUNT(*) FROM edges").fetchone()[0])
        vn1_live = int(
            conn.execute(
                "SELECT COUNT(*) FROM decls WHERE live_mask != 0 AND value_nodes = 1 AND kind IN ('thm', 'def', 'opaque')"
            ).fetchone()[0]
        )

        by_kind: Dict[str, Dict[str, int]] = {}
        for kind, tot, liv in conn.execute(
            "SELECT kind, COUNT(*), COALESCE(SUM(CASE WHEN live_mask != 0 THEN 1 ELSE 0 END), 0) "
            "FROM decls GROUP BY kind ORDER BY kind"
        ):
            by_kind[str(kind)] = {"total": int(tot), "live": int(liv), "dead": int(tot) - int(liv)}

        roots = [
            {"id": int(r[0]), "name": str(r[1]), "decl_id": int(r[2]), "grp": str(r[3])}
            for r in conn.execute("SELECT id, name, decl_id, grp FROM roots ORDER BY id")
        ]

        tables = {
            r[0]
            for r in conn.execute("SELECT name FROM sqlite_master WHERE type='table'")
        }
        has_decl_module = "decl_module" in tables
        has_taint = "taint_sources" in tables

        tree_row = conn.execute("SELECT id, label, view, n_nodes FROM dom_trees WHERE label='ALL'").fetchone()
        if tree_row is None:
            tree_row = conn.execute("SELECT id, label, view, n_nodes FROM dom_trees ORDER BY id LIMIT 1").fetchone()

        top_dom: List[Dict[str, Any]] = []
        tree_meta: Optional[Dict[str, Any]] = None
        if tree_row is not None:
            tid, tlabel, tview, tn = int(tree_row[0]), str(tree_row[1]), str(tree_row[2]), int(tree_row[3])
            tree_meta = {"id": tid, "label": tlabel, "view": tview, "n_nodes": tn}
            if has_decl_module:
                q = (
                    "SELECT d.id, d.name, d.kind, dm.module, dm.method, dm2.depth, dm2.subtree_size, "
                    "       dp.name, d.value_nodes, d.fan_in, d.fan_out, d.flags "
                    "FROM dom dm2 "
                    "JOIN decls d ON d.id = dm2.decl_id "
                    "LEFT JOIN decl_module dm ON dm.decl_id = d.id "
                    "LEFT JOIN decls dp ON dp.id = dm2.idom "
                    "WHERE dm2.tree_id = ? "
                    "ORDER BY dm2.subtree_size DESC, d.id ASC LIMIT 100"
                )
            else:
                q = (
                    "SELECT d.id, d.name, d.kind, NULL, NULL, dm2.depth, dm2.subtree_size, "
                    "       dp.name, d.value_nodes, d.fan_in, d.fan_out, d.flags "
                    "FROM dom dm2 "
                    "JOIN decls d ON d.id = dm2.decl_id "
                    "LEFT JOIN decls dp ON dp.id = dm2.idom "
                    "WHERE dm2.tree_id = ? "
                    "ORDER BY dm2.subtree_size DESC, d.id ASC LIMIT 100"
                )
            for row in conn.execute(q, (tid,)):
                top_dom.append({
                    "id": int(row[0]),
                    "name": str(row[1]),
                    "kind": str(row[2]),
                    "module": row[3],
                    "method": row[4],
                    "depth": int(row[5]),
                    "subtree_size": int(row[6]),
                    "idom": row[7],
                    "value_nodes": int(row[8]),
                    "fan_in": int(row[9]),
                    "fan_out": int(row[10]),
                    "flags": int(row[11]),
                })

        if has_decl_module:
            dead_rows = conn.execute(
                "SELECT d.id, d.name, d.kind, dm.module, d.value_nodes "
                "FROM decls d LEFT JOIN decl_module dm ON dm.decl_id = d.id "
                "WHERE d.live_mask = 0 ORDER BY d.id ASC LIMIT 50"
            ).fetchall()
        else:
            dead_rows = conn.execute(
                "SELECT id, name, kind, NULL, value_nodes FROM decls WHERE live_mask = 0 ORDER BY id ASC LIMIT 50"
            ).fetchall()
        dead_sample = [
            {
                "id": int(r[0]),
                "name": str(r[1]),
                "kind": str(r[2]),
                "module": r[3],
                "value_nodes": int(r[4]),
            }
            for r in dead_rows
        ]

        taint_counts: Dict[str, int] = {}
        if has_taint:
            for cls, cnt in conn.execute("SELECT class, COUNT(*) FROM taint_sources GROUP BY class ORDER BY class"):
                taint_counts[str(cls)] = int(cnt)

        alignment_summary: Dict[str, int] = {}
        if has_decl_module:
            for mth, cnt in conn.execute("SELECT method, COUNT(*) FROM decl_module GROUP BY method ORDER BY method"):
                alignment_summary[str(mth)] = int(cnt)
    finally:
        conn.close()

    bundles_summary: Optional[Dict[str, Any]] = None
    run_bundles_now = (total_decls <= 50_000) if with_bundles is None else bool(with_bundles)
    if run_bundles_now:
        try:
            import bundles as _bundles
            brep = _bundles.run_bundles(
                kernel_db_path=kernel_db_path,
                src_root=src_root if (src_root and os.path.isdir(src_root)) else None,
                top=50,
            )
            bundles_summary = {
                "summary": brep.get("summary") or {},
                "source_mode": (brep.get("pins") or {}).get("source_mode"),
                "bundles": [
                    {
                        "name": b.get("name"),
                        "module": b.get("module"),
                        "anchor": b.get("anchor"),
                        "universe_kind": b.get("universe_kind"),
                        "total_fields": b.get("total_fields"),
                        "projected_fields": b.get("projected_fields"),
                        "unread_fields": b.get("unread_fields"),
                        "unread_ratio": b.get("unread_ratio"),
                        "unread_field_names": b.get("unread_field_names") or [],
                        "projected_field_names": b.get("projected_field_names") or [],
                        "top_caller": b.get("top_caller"),
                        "rh_depth": b.get("rh_depth"),
                        "weighted_score": b.get("weighted_score"),
                    }
                    for b in (brep.get("bundles") or [])
                ],
                "placeholders": [
                    {"name": p.get("name"), "module": p.get("module"), "fan_in": p.get("fan_in")}
                    for p in (brep.get("placeholders") or [])[:25]
                ],
                "true_slots": (brep.get("true_slots") or [])[:25],
            }
        except Exception:
            bundles_summary = None

    return {
        "db_name": os.path.basename(kernel_db_path),
        "counts": {
            "total_decls": total_decls,
            "live_decls": live_decls,
            "dead_decls": dead_decls,
            "total_edges": total_edges,
            "vn1_live_aliases": vn1_live,
            "by_kind": by_kind,
        },
        "roots": roots,
        "dom_tree": tree_meta,
        "top_dominators": top_dom,
        "dead_sample": dead_sample,
        "taint_counts": taint_counts,
        "alignment_methods": alignment_summary,
        "bundles": bundles_summary,
    }


_HTML_TEMPLATE = """<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>__TITLE__</title>
<style>
:root{
  --bg:#0a0d12;--chrome:#0f131b;--panel:#121721;--elev:#171e2b;--hover:#1e2738;
  --border:#222c3d;--border-hi:#32415a;--hi:#e6edf7;--body:#c6d0e0;--muted:#8392ab;--dim:#58657c;
  --sel:#38bdf8;--lean:#34d399;--horn:#2dd4bf;--note:#f59e0b;--taint:#f87171;--std:#60a5fa;--meta:#fb923c;
  --mono:ui-monospace,"SF Mono",SFMono-Regular,Menlo,Consolas,monospace;
  --sans:-apple-system,BlinkMacSystemFont,"Segoe UI",Inter,Roboto,Arial,sans-serif;
}
*{box-sizing:border-box}
html,body{margin:0;padding:0;min-height:100%;background:var(--bg);color:var(--hi);font-family:var(--sans);font-size:13px;line-height:1.45}
a{color:var(--sel);text-decoration:none}a:hover{text-decoration:underline}
code,.mono{font-family:var(--mono)}
header{position:sticky;top:0;z-index:20;display:flex;align-items:center;gap:14px;padding:10px 18px;background:var(--chrome);border-bottom:1px solid var(--border);flex-wrap:wrap}
.brand{display:flex;align-items:baseline;gap:8px;white-space:nowrap}
.brand h1{margin:0;font-family:var(--mono);font-size:15px;font-weight:700;letter-spacing:.4px}
.brand h1 span{color:var(--sel)}
.brand .sub{font-size:12px;color:var(--muted)}
.tabs{display:flex;gap:6px;flex-wrap:wrap}
.tab{background:transparent;color:var(--muted);border:1px solid transparent;border-radius:6px;padding:5px 11px;font-size:12px;font-weight:600;cursor:pointer}
.tab:hover{background:var(--hover);color:var(--hi)}
.tab.active{background:var(--elev);color:var(--sel);border-color:var(--border-hi)}
.tab[disabled]{opacity:.35;cursor:not-allowed}
.spacer{flex:1}
.badge{display:inline-flex;align-items:center;gap:5px;padding:2px 8px;border-radius:999px;font-family:var(--mono);font-size:11px;border:1px solid var(--border);background:var(--elev);color:var(--body)}
.b-L{color:var(--lean);border-color:rgba(52,211,153,.35)}
.b-S{color:var(--std);border-color:rgba(96,165,250,.35)}
.b-C{color:var(--body);border-color:var(--border-hi)}
.b-M{color:var(--meta);border-color:rgba(251,146,60,.35)}
.b-high,.b-taint{color:var(--taint);border-color:rgba(248,113,113,.4)}
.b-moderate,.b-note{color:var(--note);border-color:rgba(245,158,11,.4)}
main{max-width:1440px;margin:0 auto;padding:18px}
.view{display:none}.view.active{display:block}
.grid{display:grid;grid-template-columns:repeat(auto-fit,minmax(210px,1fr));gap:12px;margin-bottom:18px}
.card{background:var(--panel);border:1px solid var(--border);border-radius:8px;padding:14px}
.card .k{font-size:11px;text-transform:uppercase;letter-spacing:.6px;color:var(--muted)}
.card .v{font-family:var(--mono);font-size:22px;font-weight:700;margin-top:4px;color:var(--hi)}
.card .d{font-size:11px;color:var(--dim);margin-top:4px}
.panel{background:var(--panel);border:1px solid var(--border);border-radius:8px;padding:14px;margin-bottom:16px}
.panel h2{margin:0 0 10px 0;font-size:14px;font-weight:600;color:var(--hi)}
.toolbar{display:flex;gap:10px;align-items:center;flex-wrap:wrap;margin-bottom:12px}
input[type=search],select{background:var(--elev);color:var(--hi);border:1px solid var(--border);border-radius:6px;padding:6px 10px;font-size:12px}
input[type=search]{min-width:240px}
table{width:100%;border-collapse:collapse;font-size:12px}
th,td{text-align:left;padding:7px 9px;border-bottom:1px solid var(--border);vertical-align:top}
th{color:var(--muted);font-weight:600;font-size:11px;text-transform:uppercase;letter-spacing:.4px;background:var(--chrome);position:sticky;top:0}
tr:hover td{background:var(--hover)}
tr.sel td{background:rgba(56,189,248,.12)}
.scroll{max-height:480px;overflow:auto;border:1px solid var(--border);border-radius:6px}
.split{display:grid;grid-template-columns:1.35fr 1fr;gap:14px}
@media(max-width:960px){.split{grid-template-columns:1fr}}
.bar-wrap{display:flex;align-items:center;gap:8px}
.bar-track{flex:1;height:10px;background:var(--elev);border-radius:4px;overflow:hidden;border:1px solid var(--border)}
.bar-fill{height:100%;background:var(--sel)}
.bar-fill.rm{background:var(--taint)}
.bar-fill.core{background:var(--lean)}
.detail-box{background:var(--elev);border:1px solid var(--border);border-radius:6px;padding:12px}
.detail-box h3{margin:0 0 6px 0;font-size:13px;font-family:var(--mono);word-break:break-all}
.kv{display:grid;grid-template-columns:130px 1fr;gap:4px 10px;font-size:12px;margin-top:8px}
.kv .kk{color:var(--muted)}.kv .kvv{word-break:break-word}
svg.mini{width:100%;height:260px;background:var(--chrome);border:1px solid var(--border);border-radius:6px;display:block;margin-top:10px}
.claims{display:flex;flex-direction:column;gap:6px;margin-top:8px}
.claim{padding:8px 10px;background:var(--elev);border-left:3px solid var(--lean);border-radius:4px;font-size:12px}
.empty{color:var(--muted);padding:16px;text-align:center}
.port-cards{display:grid;grid-template-columns:repeat(auto-fit,minmax(240px,1fr));gap:10px;margin-bottom:14px}
.port-card{background:var(--elev);border:1px solid var(--border);border-radius:6px;padding:10px 12px;cursor:pointer;text-align:left;color:var(--hi);font:inherit}
.port-card:hover{border-color:var(--border-hi);background:var(--hover)}
.port-card.active{border-color:var(--sel);box-shadow:inset 0 0 0 1px var(--sel)}
.mat-wrap{overflow:auto;border:1px solid var(--border);border-radius:6px}
table.mat{font-family:var(--mono);font-size:11px}
table.mat th,table.mat td{text-align:right;white-space:nowrap;border-right:1px solid var(--border)}
table.mat th:first-child{text-align:left}
table.mat td.hm-0{background:#0b0e14;color:var(--dim)}
table.mat td.hm-lo{background:#12253a;color:#93c5fd}
table.mat td.hm-mid{background:#13364b;color:#7dd3fc}
table.mat td.hm-hi{background:#123c33;color:var(--lean);font-weight:700}
table.mat td.hm-self{background:#1a2233;color:var(--hi);font-weight:700}
</style>
</head>
<body>
<header>
  <div class="brand">
    <h1>lean<span>re</span></h1>
    <span class="sub" id="siteTitle">__TITLE__</span>
  </div>
  <div class="tabs" id="tabBar" role="tablist">
    <button class="tab active" data-view="overview">Overview</button>
    <button class="tab" data-view="blueprints">Blueprints</button>
    <button class="tab" data-view="trim">Trim Waterfall</button>
    <button class="tab" data-view="flirt">FLIRT Atlas</button>
    <button class="tab" data-view="portability">Portability Gems</button>
    <button class="tab" data-view="kernel">Kernel &amp; Bundles</button>
  </div>
  <div class="spacer"></div>
  <span class="badge b-L">OFFLINE · ZERO-CDN</span>
</header>
<main>
  <section class="view active" id="view-overview"></section>
  <section class="view" id="view-blueprints"></section>
  <section class="view" id="view-trim"></section>
  <section class="view" id="view-flirt"></section>
  <section class="view" id="view-portability"></section>
  <section class="view" id="view-kernel"></section>
</main>
<script id="leanre-data" type="application/json">__PAYLOAD_JSON__</script>
<script>
(function(){
"use strict";
const DATA = JSON.parse(document.getElementById("leanre-data").textContent || "{}");

function el(tag, attrs, children){
  const node = document.createElement(tag);
  if(attrs){
    for(const [k,v] of Object.entries(attrs)){
      if(v === null || v === undefined) continue;
      if(k === "className") node.className = String(v);
      else if(k === "textContent") node.textContent = String(v);
      else if(k === "style" && typeof v === "object") Object.assign(node.style, v);
      else if(k.startsWith("on") && typeof v === "function") node.addEventListener(k.slice(2), v);
      else node.setAttribute(k, String(v));
    }
  }
  if(children !== undefined){
    const arr = Array.isArray(children) ? children : [children];
    for(const c of arr){
      if(c === null || c === undefined) continue;
      node.appendChild(typeof c === "string" || typeof c === "number" ? document.createTextNode(String(c)) : c);
    }
  }
  return node;
}

function clear(node){ while(node.firstChild) node.removeChild(node.firstChild); }
function fmtNum(n){ return (typeof n === "number" && isFinite(n)) ? n.toLocaleString("en-US") : "—"; }
function badge(text, cls){ return el("span", {className: "badge " + (cls || "")}, text); }

function safeGithubLink(url, label){
  if(typeof url === "string" && url.startsWith("https://github.com/")){
    return el("a", {href: url, target: "_blank", rel: "noopener noreferrer"}, label);
  }
  return el("span", {className: "mono"}, label);
}

function makeTable(headers, rows, onRowClick){
  const thead = el("thead", null, el("tr", null, headers.map(h => el("th", null, h))));
  const tbody = el("tbody");
  for(const r of rows){
    const tr = el("tr", null, r.cells.map(c => el("td", null, c)));
    if(onRowClick){
      tr.style.cursor = "pointer";
      tr.addEventListener("click", () => {
        for(const sibling of tbody.children) sibling.classList.remove("sel");
        tr.classList.add("sel");
        onRowClick(r.item);
      });
    }
    tbody.appendChild(tr);
  }
  return el("div", {className: "scroll"}, el("table", null, [thead, tbody]));
}

function switchView(name){
  for(const b of document.querySelectorAll("#tabBar .tab")){
    b.classList.toggle("active", b.getAttribute("data-view") === name);
  }
  for(const v of document.querySelectorAll("main .view")){
    v.classList.toggle("active", v.id === "view-" + name);
  }
}

function renderOverview(){
  const root = document.getElementById("view-overview");
  clear(root);
  const cards = [];
  const bps = DATA.blueprints || [];
  if(bps.length){
    const totalNodes = bps.reduce((a,b)=>a+(b.counts.nodes||0),0);
    cards.push(el("div",{className:"card"},[
      el("div",{className:"k"},"Decompiled Blueprints"),
      el("div",{className:"v"},fmtNum(bps.length)),
      el("div",{className:"d"},fmtNum(totalNodes) + " total nodes across leanre.decomp/v1 packs")
    ]));
  }
  if(DATA.trim_report){
    const b = DATA.trim_report.baseline || {};
    const c = DATA.trim_report.irreducible_core || {};
    cards.push(el("div",{className:"card"},[
      el("div",{className:"k"},"Trim Waterfall"),
      el("div",{className:"v"},fmtNum(c.modules || b.live_modules_total) + " / " + fmtNum(b.total_modules)),
      el("div",{className:"d"},"Irreducible modules (" + (c.pct_of_corpus_modules || "—") + "% of corpus)")
    ]));
  }
  if(DATA.cluster_atlas){
    const t = DATA.cluster_atlas.totals || {};
    cards.push(el("div",{className:"card"},[
      el("div",{className:"k"},"FLIRT Cluster Atlas"),
      el("div",{className:"v"},fmtNum(t.clusters_count || (DATA.cluster_atlas.clusters||[]).length)),
      el("div",{className:"d"},"Effective core: " + fmtNum(t.effective_core_decls) + " (" + (t.collapse_pct || "—") + "% collapsed)")
    ]));
  }
  if(DATA.portability && DATA.portability.summary){
    const ps = DATA.portability.summary;
    cards.push(el("div",{className:"card"},[
      el("div",{className:"k"},"Portability Gems"),
      el("div",{className:"v"},fmtNum(ps.pairwise_disjoint_islands) + " islands"),
      el("div",{className:"d"},fmtNum(ps.standalone_ready_count) + " standalone-ready / " + fmtNum(ps.targets_count) + " targets · " + fmtNum(ps.union_project_decls) + " union proj decls")
    ]));
  }
  if(DATA.kernel){
    const k = DATA.kernel.counts || {};
    cards.push(el("div",{className:"card"},[
      el("div",{className:"k"},"Kernel Declarations"),
      el("div",{className:"v"},fmtNum(k.live_decls) + " live"),
      el("div",{className:"d"},fmtNum(k.dead_decls) + " dead · " + fmtNum(k.total_edges) + " edges · " + fmtNum(k.vn1_live_aliases) + " vn=1 aliases")
    ]));
    if(DATA.kernel.bundles && DATA.kernel.bundles.summary){
      const bs = DATA.kernel.bundles.summary;
      cards.push(el("div",{className:"card"},[
        el("div",{className:"k"},"1-Ctor Structure Bundles"),
        el("div",{className:"v"},fmtNum((DATA.kernel.bundles.bundles||[]).length) + " unread"),
        el("div",{className:"d"},fmtNum(bs.total_live_1ctor_project_inductives) + " live 1-ctor inductives inspected")
      ]));
    }
  }
  if(!cards.length){
    cards.push(el("div",{className:"card"},[el("div",{className:"k"},"Status"),el("div",{className:"v"},"Empty"),el("div",{className:"d"},"No datasets embedded")]));
  }
  root.appendChild(el("div",{className:"grid"},cards));

  const legend = el("div",{className:"panel"},[
    el("h2",null,"Provenance & Offline Verification"),
    el("div",{className:"toolbar"},[
      badge("[L] Verified Lean / Kernel Fact","b-L"),
      badge("[S] Standard Math Definition","b-S"),
      badge("[C] Community / External Claim","b-C"),
      badge("[M] Heuristic / Analogy","b-M")
    ]),
    el("p",{style:{color:"var(--body)",margin:"6px 0 0 0"}},
      "Static self-contained explorer generated by leanre.export_site. Zero external network requests, zero CDN assets, and XSS-safe DOM rendering.")
  ]);
  root.appendChild(legend);
}

function drawMiniGraph(svg, centerNode, allNodes, edges){
  while(svg.firstChild) svg.removeChild(svg.firstChild);
  const NS = "http://www.w3.org/2000/svg";
  const W = 520, H = 260;
  svg.setAttribute("viewBox", "0 0 " + W + " " + H);
  if(!centerNode) return;
  const neigh = [];
  const seen = new Set([centerNode.id]);
  for(const e of edges){
    if(e.src === centerNode.id && !seen.has(e.dst)){ seen.add(e.dst); neigh.push({id:e.dst, dir:"out", rel:e.rel}); }
    else if(e.dst === centerNode.id && !seen.has(e.src)){ seen.add(e.src); neigh.push({id:e.src, dir:"in", rel:e.rel}); }
    if(neigh.length >= 10) break;
  }
  const cx = W/2, cy = H/2;
  const pos = new Map([[centerNode.id, {x:cx, y:cy}]]);
  const ins = neigh.filter(x=>x.dir==="in");
  const outs = neigh.filter(x=>x.dir==="out");
  ins.forEach((n, idx)=>{
    const y = (H / (ins.length + 1)) * (idx + 1);
    pos.set(n.id, {x: 92, y});
  });
  outs.forEach((n, idx)=>{
    const y = (H / (outs.length + 1)) * (idx + 1);
    pos.set(n.id, {x: W - 92, y});
  });
  for(const n of neigh){
    const p1 = pos.get(n.dir==="in" ? n.id : centerNode.id);
    const p2 = pos.get(n.dir==="in" ? centerNode.id : n.id);
    const line = document.createElementNS(NS, "line");
    line.setAttribute("x1", p1.x); line.setAttribute("y1", p1.y);
    line.setAttribute("x2", p2.x); line.setAttribute("y2", p2.y);
    line.setAttribute("stroke", n.dir==="in" ? "#2dd4bf" : "#38bdf8");
    line.setAttribute("stroke-width", "1.4");
    line.setAttribute("stroke-opacity", "0.75");
    svg.appendChild(line);
  }
  function drawNode(id, x, y, fill, isCenter){
    const g = document.createElementNS(NS, "g");
    const r = document.createElementNS(NS, "rect");
    const w = isCenter ? 168 : 148, h = 26;
    r.setAttribute("x", x - w/2); r.setAttribute("y", y - h/2);
    r.setAttribute("width", w); r.setAttribute("height", h);
    r.setAttribute("rx", "5"); r.setAttribute("fill", "#171e2b");
    r.setAttribute("stroke", fill); r.setAttribute("stroke-width", isCenter ? "2" : "1.2");
    const t = document.createElementNS(NS, "text");
    t.setAttribute("x", x); t.setAttribute("y", y + 4);
    t.setAttribute("text-anchor", "middle"); t.setAttribute("fill", "#e6edf7");
    t.setAttribute("font-size", "10"); t.setAttribute("font-family", "monospace");
    const shortName = id.length > 21 ? "…" + id.slice(-20) : id;
    t.textContent = shortName;
    g.appendChild(r); g.appendChild(t);
    svg.appendChild(g);
  }
  drawNode(centerNode.id, cx, cy, "#38bdf8", true);
  for(const n of neigh){
    const p = pos.get(n.id);
    drawNode(n.id, p.x, p.y, n.dir==="in" ? "#2dd4bf" : "#34d399", false);
  }
}

function renderBlueprints(){
  const root = document.getElementById("view-blueprints");
  clear(root);
  const bps = DATA.blueprints || [];
  if(!bps.length){ root.appendChild(el("div",{className:"panel empty"},"No leanre.decomp/v1 blueprints embedded.")); return; }

  let curIdx = 0;
  const selBp = el("select", null, bps.map((b, i) => el("option", {value: String(i)}, b.file + " (" + b.pillar + ", " + b.counts.nodes + " nodes)")));
  const qIn = el("input", {type: "search", placeholder: "Filter node id, module, or summary…"});
  const verdictSel = el("select", null, [
    el("option", {value: ""}, "All verdicts"),
    el("option", {value: "real"}, "real"),
    el("option", {value: "wrapper"}, "wrapper"),
    el("option", {value: "proxy"}, "proxy"),
    el("option", {value: "degenerate"}, "degenerate"),
    el("option", {value: "vacuous"}, "vacuous")
  ]);
  const metaBar = el("div", {className: "toolbar"});
  const claimsBox = el("div", {className: "claims"});
  const leftWrap = el("div");
  const rightWrap = el("div", {className: "detail-box"});

  function showDetail(node, bp){
    clear(rightWrap);
    if(!node){ rightWrap.appendChild(el("div",{className:"empty"},"Select a blueprint node to inspect details & local edges.")); return; }
    rightWrap.appendChild(el("h3", null, node.id));
    rightWrap.appendChild(el("div", {className: "toolbar"}, [
      badge("[" + (node.tag || "L") + "]", "b-" + (node.tag || "L")),
      badge(node.status || "?", node.status === "OPAQUE" ? "b-high" : "b-L"),
      badge(node.verdict || "?", node.verdict === "wrapper" ? "b-note" : "b-S"),
      badge(node.role || "?")
    ]));
    const kv = el("div", {className: "kv"}, [
      el("div", {className: "kk"}, "Kind"), el("div", {className: "kvv mono"}, node.kind || "—"),
      el("div", {className: "kk"}, "Anchor"), el("div", {className: "kvv mono"}, node.anchor || node.module || "—"),
      el("div", {className: "kk"}, "Dom"), el("div", {className: "kvv mono"}, node.dom_subtree !== null ? ("depth=" + node.dom_depth + ", subtree=" + node.dom_subtree) : "—"),
      el("div", {className: "kk"}, "Header"), el("div", {className: "kvv mono"}, node.header || "—"),
      el("div", {className: "kk"}, "Summary"), el("div", {className: "kvv"}, node.summary || "—")
    ]);
    rightWrap.appendChild(kv);
    const svg = document.createElementNS("http://www.w3.org/2000/svg", "svg");
    svg.setAttribute("class", "mini");
    drawMiniGraph(svg, node, bp.nodes, bp.edges);
    rightWrap.appendChild(svg);
  }

  function refresh(){
    const bp = bps[curIdx];
    clear(metaBar);
    metaBar.appendChild(badge("root: " + (bp.root || "—"), "b-S"));
    metaBar.appendChild(badge("nodes: " + bp.counts.nodes_shown + "/" + bp.counts.nodes));
    metaBar.appendChild(badge("edges: " + bp.counts.edges_shown + "/" + bp.counts.edges));
    metaBar.appendChild(badge("opaque: " + bp.counts.opaque, bp.counts.opaque > 0 ? "b-note" : "b-L"));

    clear(claimsBox);
    for(const c of (bp.claims || []).slice(0, 6)){
      claimsBox.appendChild(el("div", {className: "claim"}, [badge("[" + c.tag + "]", "b-" + c.tag), " ", c.text]));
    }

    const q = qIn.value.trim().toLowerCase();
    const vf = verdictSel.value;
    const filtered = (bp.nodes || []).filter(n => {
      if(vf && n.verdict !== vf) return false;
      if(q){
        const hay = (n.id + " " + (n.module||"") + " " + (n.summary||"")).toLowerCase();
        if(!hay.includes(q)) return false;
      }
      return true;
    });
    clear(leftWrap);
    leftWrap.appendChild(makeTable(
      ["Declaration", "Status", "Verdict", "Dom", "Role"],
      filtered.map(n => ({
        item: n,
        cells: [
          el("span", {className: "mono"}, n.id),
          badge(n.status, n.status === "OPAQUE" ? "b-high" : "b-L"),
          n.verdict,
          n.dom_subtree !== null ? fmtNum(n.dom_subtree) : "—",
          n.role
        ]
      })),
      n => showDetail(n, bp)
    ));
    showDetail(filtered[0] || null, bp);
  }

  selBp.addEventListener("change", () => { curIdx = Number(selBp.value) || 0; refresh(); });
  qIn.addEventListener("input", refresh);
  verdictSel.addEventListener("change", refresh);

  root.appendChild(el("div", {className: "panel"}, [
    el("div", {className: "toolbar"}, [selBp, qIn, verdictSel]),
    metaBar,
    claimsBox
  ]));
  root.appendChild(el("div", {className: "split"}, [
    el("div", {className: "panel"}, [el("h2", null, "Blueprint Nodes"), leftWrap]),
    el("div", {className: "panel"}, [el("h2", null, "Inspector & Local Cone"), rightWrap])
  ]));
  refresh();
}

function renderTrim(){
  const root = document.getElementById("view-trim");
  clear(root);
  const tr = DATA.trim_report;
  if(!tr){ root.appendChild(el("div",{className:"panel empty"},"No trim_report.json embedded.")); return; }
  const base = tr.baseline || {};
  const core = tr.irreducible_core || {};
  const baseLines = Math.max(1, Number(base.total_lines_wc || 1));

  const barsPanel = el("div", {className: "panel"}, [el("h2", null, "Virtual Proof Stripper Waterfall (Exact Line & Kernel Conservation)")]);
  for(const st of (tr.steps || [])){
    const rm = (st.removed && st.removed.lines_wc) || 0;
    const af = (st.after && st.after.lines_wc) || 0;
    const pctKeep = Math.max(0, Math.min(100, (af / baseLines) * 100));
    const pctRm = Math.max(0, Math.min(100, (rm / baseLines) * 100));
    barsPanel.appendChild(el("div", {style:{marginBottom:"10px"}}, [
      el("div", {style:{display:"flex",justifyContent:"space-between",marginBottom:"3px"}}, [
        el("span", {className:"mono"}, st.step_id + " — " + st.label),
        el("span", {className:"mono",style:{color:"var(--muted)"}}, "-" + fmtNum(rm) + " lines (" + pctRm.toFixed(2) + "%) → " + fmtNum(af) + " left")
      ]),
      el("div", {className:"bar-track"}, [
        el("div", {className:"bar-fill core", style:{width: pctKeep.toFixed(2) + "%", display:"inline-block"}}),
        el("div", {className:"bar-fill rm", style:{width: pctRm.toFixed(2) + "%", display:"inline-block"}})
      ])
    ]));
  }
  root.appendChild(barsPanel);

  const rows = (tr.steps || []).map(st => ({
    item: st,
    cells: [
      el("span",{className:"mono"},st.step_id),
      fmtNum(st.removed && st.removed.modules),
      fmtNum(st.removed && st.removed.lines_wc),
      fmtNum(st.removed && st.removed.kernel_live_decls),
      fmtNum(st.after && st.after.modules),
      fmtNum(st.after && st.after.lines_wc),
      fmtNum(st.after && st.after.kernel_live_decls)
    ]
  }));
  root.appendChild(el("div",{className:"panel"},[
    el("h2",null,"Conservation Table (Irreducible Core: " + fmtNum(core.modules) + " modules / " + fmtNum(core.lines_wc) + " lines / " + fmtNum(core.kernel_live_decls_total) + " live decls)"),
    makeTable(["Step","−Modules","−Lines","−Kernel Decls","After Modules","After Lines","After Live Decls"], rows)
  ]));
}

function renderFlirt(){
  const root = document.getElementById("view-flirt");
  clear(root);
  const atlas = DATA.cluster_atlas;
  if(!atlas){ root.appendChild(el("div",{className:"panel empty"},"No cluster_labels_141.json FLIRT atlas embedded.")); return; }
  const clusters = atlas.clusters || [];
  const qIn = el("input", {type: "search", placeholder: "Search cluster, root_decl, domain, or pillar…"});
  const sevSel = el("select", null, [
    el("option", {value: ""}, "All severities"),
    el("option", {value: "high"}, "high"),
    el("option", {value: "moderate"}, "moderate"),
    el("option", {value: "low"}, "low"),
    el("option", {value: "none"}, "none")
  ]);
  const tableWrap = el("div");
  const detailWrap = el("div", {className: "detail-box"});

  function showCluster(c){
    clear(detailWrap);
    if(!c){ detailWrap.appendChild(el("div",{className:"empty"},"Select a FLIRT cluster row to inspect reps & mismatch audit.")); return; }
    const bl = c.blinded_label || {};
    const ma = c.mismatch_audit || {};
    detailWrap.appendChild(el("h3", null, c.cluster_id + " · " + c.root_decl));
    detailWrap.appendChild(el("div", {className: "toolbar"}, [
      badge(c.pillar || "?", "b-S"),
      badge("mismatch: " + (ma.severity || "none"), ma.severity === "high" ? "b-high" : (ma.severity === "moderate" ? "b-note" : "b-L")),
      badge("[M] conf=" + (bl.confidence ?? "—"), "b-M")
    ]));
    detailWrap.appendChild(el("div", {className: "kv"}, [
      el("div",{className:"kk"},"[M] Label"), el("div",{className:"kvv"},bl.label || "—"),
      el("div",{className:"kk"},"Tier-1 Domain"), el("div",{className:"kvv mono"},c.tier1_top_domain || "—"),
      el("div",{className:"kk"},"Core / Live"), el("div",{className:"kvv mono"},fmtNum(c.counts.effective_core_decls) + " / " + fmtNum(c.counts.live_decls) + " (" + c.counts.collapse_pct + "% collapsed)"),
      el("div",{className:"kk"},"Mismatch Audit"), el("div",{className:"kvv"},ma.reason || "—")
    ]));
    if((c.top3_rep_decls || []).length){
      detailWrap.appendChild(el("h2", {style:{marginTop:"12px"}}, "Top Representative Declarations"));
      const ul = el("ul", {style:{margin:"6px 0 0 18px",padding:0}});
      for(const r of c.top3_rep_decls){
        ul.appendChild(el("li", {style:{marginBottom:"4px"}}, [
          safeGithubLink(r.github_url, r.name),
          el("span", {style:{color:"var(--muted)"}}, " (subtree=" + fmtNum(r.subtree_size) + ")")
        ]));
      }
      detailWrap.appendChild(ul);
    }
  }

  function refresh(){
    const q = qIn.value.trim().toLowerCase();
    const sv = sevSel.value;
    const filtered = clusters.filter(c => {
      const ma = c.mismatch_audit || {};
      const bl = c.blinded_label || {};
      if(sv && ma.severity !== sv) return false;
      if(q){
        const hay = (c.cluster_id + " " + c.pillar + " " + c.root_decl + " " + (bl.label||"") + " " + (c.tier1_top_domain||"")).toLowerCase();
        if(!hay.includes(q)) return false;
      }
      return true;
    });
    clear(tableWrap);
    tableWrap.appendChild(makeTable(
      ["Cluster", "Pillar", "Core Decls", "Collapse%", "Severity", "[M] Blinded Label"],
      filtered.map(c => ({
        item: c,
        cells: [
          el("span",{className:"mono"},c.cluster_id),
          c.pillar,
          fmtNum(c.counts.effective_core_decls),
          (c.counts.collapse_pct ?? 0) + "%",
          badge((c.mismatch_audit && c.mismatch_audit.severity) || "none", (c.mismatch_audit && c.mismatch_audit.severity)==="high" ? "b-high" : ((c.mismatch_audit && c.mismatch_audit.severity)==="moderate" ? "b-note" : "b-L")),
          (c.blinded_label && c.blinded_label.label) || "—"
        ]
      })),
      showCluster
    ));
    showCluster(filtered[0] || null);
  }

  qIn.addEventListener("input", refresh);
  sevSel.addEventListener("change", refresh);

  root.appendChild(el("div",{className:"panel"},[
    el("div",{className:"toolbar"},[qIn, sevSel, badge("shown: " + clusters.length + " / " + atlas.clusters_total)])
  ]));
  root.appendChild(el("div",{className:"split"},[
    el("div",{className:"panel"},[el("h2",null,"141 FLIRT Clusters"),tableWrap]),
    el("div",{className:"panel"},[el("h2",null,"Cluster Audit"),detailWrap])
  ]));
  refresh();
}

function renderPortability(){
  const root = document.getElementById("view-portability");
  clear(root);
  const pt = DATA.portability;
  if(!pt || !(pt.targets || []).length){
    root.appendChild(el("div",{className:"panel empty"},"No portability_gems.json embedded."));
    return;
  }
  const sm = pt.summary || {};
  const islands = pt.islands || [];
  const targets = pt.targets || [];
  const ov = pt.overlap || {};
  let activeIsland = "";

  root.appendChild(el("div",{className:"grid"},[
    el("div",{className:"card"},[
      el("div",{className:"k"},"Pairwise-Disjoint Islands"),
      el("div",{className:"v"},fmtNum(sm.pairwise_disjoint_islands) + " / " + fmtNum(sm.islands_count)),
      el("div",{className:"d"},"0 shared project decls across disjoint islands")
    ]),
    el("div",{className:"card"},[
      el("div",{className:"k"},"Standalone-Ready Gems"),
      el("div",{className:"v"},fmtNum(sm.standalone_ready_count) + " / " + fmtNum(sm.targets_count)),
      el("div",{className:"d"},fmtNum(sm.scoped_count) + " scoped")
    ]),
    el("div",{className:"card"},[
      el("div",{className:"k"},"Union Project Cone"),
      el("div",{className:"v"},fmtNum(sm.union_project_decls)),
      el("div",{className:"d"},fmtNum(sm.union_module_count) + " modules")
    ]),
    el("div",{className:"card"},[
      el("div",{className:"k"},"Union External Boundary"),
      el("div",{className:"v"},fmtNum(sm.union_external_decls)),
      el("div",{className:"d"},fmtNum(sm.union_total_decls) + " union total decls")
    ])
  ]));

  const cardsWrap = el("div",{className:"port-cards"});
  const tblWrap = el("div");
  const detWrap = el("div",{className:"detail-box"});

  function showTarget(t){
    clear(detWrap);
    if(!t){ detWrap.appendChild(el("div",{className:"empty"},"Select a target to inspect its spec cone and Mathlib boundary.")); return; }
    const cone = t.cone || {};
    const bnd = t.boundary || {};
    const cont = t.contamination || {};
    detWrap.appendChild(el("h3",null,t.name));
    detWrap.appendChild(el("div",{className:"toolbar"},[
      badge(cont.tier || "unknown", cont.tier === "standalone-ready" ? "b-L" : "b-note"),
      badge(cont.has_sorry ? "sorry" : "0 sorry", cont.has_sorry ? "b-high" : "b-L"),
      t.island_slug ? badge("island: " + t.island_slug, "b-S") : null
    ]));
    detWrap.appendChild(el("div",{className:"kv"},[
      el("div",{className:"kk"},"Module"), el("div",{className:"kvv mono"},t.module || "—"),
      el("div",{className:"kk"},"Project Cone"), el("div",{className:"kvv mono"},fmtNum(cone.project_decls) + " proj / " + fmtNum(cone.total_decls) + " tot (" + fmtNum(cone.module_count) + " mods)"),
      el("div",{className:"kk"},"Spec Cone"), el("div",{className:"kvv mono"},fmtNum(cone.spec_cone_project_decls) + " proj / " + fmtNum(cone.spec_cone_total_decls) + " tot"),
      el("div",{className:"kk"},"Dom Subtree"), el("div",{className:"kvv mono"},fmtNum(cone.dom_subtree_size) + " (depth " + String(cone.dom_depth ?? "—") + ")"),
      el("div",{className:"kk"},"Mathlib Boundary"), el("div",{className:"kvv mono"},fmtNum(bnd.direct_external_decls) + " direct ext decls · " + fmtNum(bnd.distinct_prefixes_total) + " prefixes"),
      el("div",{className:"kk"},"Axioms"), el("div",{className:"kvv mono"},(cont.axioms || []).join(", ") || "none"),
      el("div",{className:"kk"},"Verdict Notes"), el("div",{className:"kvv"},(cont.reasons || []).join("; ") || "—")
    ]));
    const prefs = bnd.top_external_prefixes || [];
    if(prefs.length){
      const maxD = Math.max(1, ...prefs.map(p => Number(p.distinct_decls || 1)));
      detWrap.appendChild(el("h2",{style:{marginTop:"12px"}},"Top External (Mathlib) Boundary Prefixes"));
      for(const p of prefs.slice(0, 10)){
        detWrap.appendChild(el("div",{style:{marginBottom:"6px"}},[
          el("div",{style:{display:"flex",justifyContent:"space-between",fontSize:"11px"}},[
            el("span",{className:"mono"},p.prefix),
            el("span",{className:"mono",style:{color:"var(--muted)"}},fmtNum(p.distinct_decls) + " decls · " + fmtNum(p.call_edges) + " edges")
          ]),
          el("div",{className:"bar-track"},el("div",{className:"bar-fill",style:{width:Math.max(4,(p.distinct_decls/maxD)*100).toFixed(1)+"%"}}))
        ]));
      }
    }
  }

  function refresh(){
    clear(cardsWrap);
    for(const isl of islands){
      const act = activeIsland === isl.id;
      const btn = el("button",{className:"port-card" + (act ? " active" : ""), onclick: () => { activeIsland = act ? "" : isl.id; refresh(); }},[
        el("div",{style:{display:"flex",justifyContent:"space-between",alignItems:"center",marginBottom:"4px"}},[
          el("span",{className:"mono",style:{fontWeight:"700"}},"Island " + isl.index + " · " + isl.slug),
          badge(isl.pairwise_disjoint ? "0 overlap" : "shared", isl.pairwise_disjoint ? "b-L" : "b-note")
        ]),
        el("div",{className:"mono",style:{fontSize:"11px",color:"var(--muted)",marginBottom:"6px"}},(isl.member_shorts || []).join(" + ")),
        el("div",{style:{fontSize:"11px",color:"var(--body)"}},fmtNum(isl.max_project_decls) + " proj · spec " + fmtNum(isl.min_spec_cone_project_decls) + " · ext " + fmtNum(isl.max_direct_external_decls))
      ]);
      cardsWrap.appendChild(btn);
    }

    const shown = activeIsland ? targets.filter(t => t.island_id === activeIsland) : targets;
    clear(tblWrap);
    tblWrap.appendChild(makeTable(
      ["Theorem", "Island", "Tier", "Proj Cone", "Spec Proj", "Ext Decls"],
      shown.map(t => ({
        item: t,
        cells: [
          el("span",{className:"mono"},t.short_name || t.name),
          el("span",{className:"mono"},t.island_slug || "—"),
          badge((t.contamination && t.contamination.tier) || "?", (t.contamination && t.contamination.tier) === "standalone-ready" ? "b-L" : "b-note"),
          fmtNum(t.cone && t.cone.project_decls),
          fmtNum(t.cone && t.cone.spec_cone_project_decls),
          fmtNum(t.boundary && t.boundary.direct_external_decls)
        ]
      })),
      showTarget
    ));
    showTarget(shown[0] || null);
  }

  root.appendChild(el("div",{className:"panel"},[
    el("h2",null,"Mathlib-Portable Islands (click card to filter)"),
    cardsWrap
  ]));
  root.appendChild(el("div",{className:"split"},[
    el("div",{className:"panel"},[el("h2",null,"Portable Targets"),tblWrap]),
    el("div",{className:"panel"},[el("h2",null,"Spec Cone & Mathlib Boundary"),detWrap])
  ]));

  const mat = ov.project_decls_matrix || [];
  const jmat = ov.project_jaccard_matrix || [];
  const names = ov.short_names || ov.target_names || [];
  if(mat.length && names.length === mat.length){
    const thead = el("thead",null,el("tr",null,[el("th",null,"Target")].concat(names.map(nm => el("th",null,nm.length > 16 ? nm.slice(0,15)+"…" : nm)))));
    const tbody = el("tbody");
    mat.forEach((row, ri) => {
      const cells = [el("th",null,names[ri])];
      row.forEach((val, ci) => {
        const jv = (jmat[ri] && jmat[ri][ci] != null) ? Number(jmat[ri][ci]) : (ri === ci ? 1 : 0);
        const cls = ri === ci ? "hm-self" : (val === 0 ? "hm-0" : (jv >= 0.7 ? "hm-hi" : (jv >= 0.2 ? "hm-mid" : "hm-lo")));
        const txt = ri !== ci && val > 0 ? (fmtNum(val) + " (" + (jv*100).toFixed(0) + "%)") : fmtNum(val);
        cells.push(el("td",{className:cls},txt));
      });
      tbody.appendChild(el("tr",null,cells));
    });
    root.appendChild(el("div",{className:"panel"},[
      el("h2",null,"Pairwise Project-Declaration Overlap Matrix (0 = disjoint)"),
      el("div",{className:"mat-wrap"},el("table",{className:"mat"},[thead,tbody]))
    ]));
  }
  refresh();
}

function renderKernel(){
  const root = document.getElementById("view-kernel");
  clear(root);
  const k = DATA.kernel;
  if(!k){ root.appendChild(el("div",{className:"panel empty"},"No kernel.db summary embedded.")); return; }

  const rootsPanel = el("div",{className:"panel"},[
    el("h2",null,"Kernel Roots (" + k.db_name + ")"),
    el("div",{className:"toolbar"},(k.roots||[]).map(r => badge(r.grp + ": " + r.name, "b-L")))
  ]);
  root.appendChild(rootsPanel);

  if((k.top_dominators || []).length){
    const maxSub = Math.max(1, ...k.top_dominators.map(x => Number(x.subtree_size || 1)));
    root.appendChild(el("div",{className:"panel"},[
      el("h2",null,"Dominator Spine (" + ((k.dom_tree && k.dom_tree.label) || "ALL") + ")"),
      makeTable(
        ["Declaration", "Kind", "Module", "Depth", "Subtree", "vn", "Immediate Dominator"],
        k.top_dominators.map(d => ({
          item: d,
          cells: [
            el("span",{className:"mono"},d.name),
            d.kind,
            el("span",{className:"mono"},d.module || d.method || "—"),
            String(d.depth),
            el("div",{className:"bar-wrap"},[
              el("span",{className:"mono",style:{minWidth:"44px"}},fmtNum(d.subtree_size)),
              el("div",{className:"bar-track"},el("div",{className:"bar-fill",style:{width:Math.max(4,(d.subtree_size/maxSub)*100).toFixed(1)+"%"}}))
            ]),
            String(d.value_nodes),
            el("span",{className:"mono"},d.idom || "VIRTUAL_ROOT")
          ]
        }))
      )
    ]));
  }

  if((k.dead_sample || []).length){
    root.appendChild(el("div",{className:"panel"},[
      el("h2",null,"Dead Declarations (live_mask = 0)"),
      makeTable(
        ["Declaration", "Kind", "Module", "vn"],
        k.dead_sample.map(d => ({
          item: d,
          cells: [el("span",{className:"mono"},d.name), d.kind, el("span",{className:"mono"},d.module || "—"), String(d.value_nodes)]
        }))
      )
    ]));
  }

  if(k.bundles && (k.bundles.bundles || []).length){
    root.appendChild(el("div",{className:"panel"},[
      el("h2",null,"1-Ctor Structure Unread Fields (" + (k.bundles.source_mode || "") + ")"),
      makeTable(
        ["Structure", "Module", "Projected", "Unread", "Unread Fields", "Top Caller"],
        k.bundles.bundles.map(b => ({
          item: b,
          cells: [
            el("span",{className:"mono"},b.name),
            el("span",{className:"mono"},b.module || "—"),
            (b.projected_field_names || []).join(", ") || String(b.projected_fields),
            String(b.unread_fields) + "/" + String(b.total_fields),
            el("span",{className:"mono"},(b.unread_field_names || []).join(", ")),
            el("span",{className:"mono"},b.top_caller || "—")
          ]
        }))
      )
    ]));
  }
}

for(const btn of document.querySelectorAll("#tabBar .tab")){
  const v = btn.getAttribute("data-view");
  const has = (v === "overview") ||
    (v === "blueprints" && (DATA.blueprints || []).length > 0) ||
    (v === "trim" && !!DATA.trim_report) ||
    (v === "flirt" && !!DATA.cluster_atlas) ||
    (v === "portability" && !!(DATA.portability && (DATA.portability.targets || []).length > 0)) ||
    (v === "kernel" && !!DATA.kernel);
  if(!has) btn.setAttribute("disabled", "disabled");
  btn.addEventListener("click", () => { if(!btn.hasAttribute("disabled")) switchView(v); });
}

renderOverview();
renderBlueprints();
renderTrim();
renderFlirt();
renderPortability();
renderKernel();
})();
</script>
</body>
</html>
"""


def build_site_payload(
    decomp_dir: Optional[str] = None,
    *,
    trim_report: Optional[str] = None,
    cluster_labels: Optional[str] = None,
    portability: Optional[str] = None,
    kernel_db: Optional[str] = None,
    src_root: Optional[str] = None,
    title: str = "leanre — Static Proof Explorer",
    max_nodes_per_blueprint: int = 250,
    max_clusters: int = 200,
    with_bundles: Optional[bool] = None,
) -> Dict[str, Any]:
    """Collect and deterministically summarize available leanre artifacts."""
    blueprints: List[Dict[str, Any]] = []
    resolved_trim = trim_report
    resolved_clusters = cluster_labels
    resolved_portability = portability

    if decomp_dir:
        if not os.path.isdir(decomp_dir):
            raise FileNotFoundError(f"Missing decomp_dir: {decomp_dir}")
        for fn in sorted(os.listdir(decomp_dir)):
            if not fn.endswith(".json"):
                continue
            full = os.path.join(decomp_dir, fn)
            if os.path.islink(full) or not os.path.isfile(full):
                continue
            with open(full, "r", encoding="utf-8") as f:
                doc = json.load(f)
            if not isinstance(doc, dict):
                continue
            sc = doc.get("schema")
            if sc == "leanre.decomp/v1":
                blueprints.append(_summarize_blueprint(doc, fn, max_nodes=max_nodes_per_blueprint))
            elif sc == "leanre.trim/1" and resolved_trim is None:
                resolved_trim = full
            elif sc == "leanre.flirt_atlas/v1" and resolved_clusters is None:
                resolved_clusters = full
            elif sc == "leanre.portability/1" and resolved_portability is None:
                resolved_portability = full

        parent_out = os.path.dirname(os.path.abspath(decomp_dir))
        if resolved_clusters is None:
            sib = os.path.join(parent_out, "flirt", "cluster_labels_141.json")
            if os.path.isfile(sib) and not os.path.islink(sib):
                resolved_clusters = sib
        if resolved_portability is None:
            sib_p = os.path.join(parent_out, "portability_gems.json")
            if os.path.isfile(sib_p) and not os.path.islink(sib_p):
                resolved_portability = sib_p

    trim_summary: Optional[Dict[str, Any]] = None
    if resolved_trim:
        if os.path.islink(resolved_trim):
            raise ValueError(f"Refusing symlinked trim_report: {resolved_trim}")
        with open(resolved_trim, "r", encoding="utf-8") as f:
            trim_summary = _summarize_trim_report(json.load(f))

    atlas_summary: Optional[Dict[str, Any]] = None
    if resolved_clusters:
        if os.path.islink(resolved_clusters):
            raise ValueError(f"Refusing symlinked cluster_labels: {resolved_clusters}")
        with open(resolved_clusters, "r", encoding="utf-8") as f:
            atlas_summary = _summarize_cluster_atlas(json.load(f), max_clusters=max_clusters)

    portability_summary: Optional[Dict[str, Any]] = None
    if resolved_portability:
        if os.path.islink(resolved_portability):
            raise ValueError(f"Refusing symlinked portability report: {resolved_portability}")
        with open(resolved_portability, "r", encoding="utf-8") as f:
            portability_summary = _summarize_portability(json.load(f))

    kernel_summary: Optional[Dict[str, Any]] = None
    if kernel_db:
        if os.path.islink(kernel_db):
            raise ValueError(f"Refusing symlinked kernel_db: {kernel_db}")
        kernel_summary = _summarize_kernel_db(kernel_db, src_root=src_root, with_bundles=with_bundles)

    return {
        "schema": SCHEMA_VERSION,
        "title": title,
        "blueprints": blueprints,
        "trim_report": trim_summary,
        "cluster_atlas": atlas_summary,
        "portability": portability_summary,
        "kernel": kernel_summary,
    }


def export_static_site(
    decomp_dir: Optional[str],
    out_html: str,
    *,
    trim_report: Optional[str] = None,
    cluster_labels: Optional[str] = None,
    portability: Optional[str] = None,
    kernel_db: Optional[str] = None,
    src_root: Optional[str] = None,
    title: str = "leanre — Static Proof Explorer",
    max_nodes_per_blueprint: int = 250,
    max_clusters: int = 200,
    with_bundles: Optional[bool] = None,
) -> Dict[str, Any]:
    """Generate a self-contained, zero-CDN, XSS-safe, deterministic offline HTML viewer."""
    if os.path.islink(out_html):
        raise ValueError(f"Refusing to write through symlink: {out_html}")
    payload = build_site_payload(
        decomp_dir=decomp_dir,
        trim_report=trim_report,
        cluster_labels=cluster_labels,
        portability=portability,
        kernel_db=kernel_db,
        src_root=src_root,
        title=title,
        max_nodes_per_blueprint=max_nodes_per_blueprint,
        max_clusters=max_clusters,
        with_bundles=with_bundles,
    )
    esc_title = html.escape(title, quote=True)
    payload_json = _escape_json_for_script(payload)
    out_text = (
        _HTML_TEMPLATE
        .replace("__TITLE__", esc_title)
        .replace("__PAYLOAD_JSON__", payload_json)
    )
    _safe_write_text(out_html, out_text)
    return {
        "schema": SCHEMA_VERSION,
        "out_html": os.path.basename(out_html),
        "bytes": len(out_text.encode("utf-8")),
        "blueprints": len(payload["blueprints"]),
        "has_trim_report": payload["trim_report"] is not None,
        "has_cluster_atlas": payload["cluster_atlas"] is not None,
        "has_portability": payload["portability"] is not None,
        "has_kernel": payload["kernel"] is not None,
    }


def export_tiny_demo_site(
    out_html: str,
    *,
    title: Optional[str] = None,
    demo_dir: Optional[str] = None,
) -> Dict[str, Any]:
    """Build examples/tiny_demo into a scratch kernel.db and export an offline HTML site."""
    if os.path.islink(out_html):
        raise ValueError(f"Refusing to write through symlink: {out_html}")
    repo_root = os.path.abspath(os.path.join(_HERE, ".."))
    ddir = os.path.abspath(demo_dir or os.path.join(repo_root, "examples", "tiny_demo"))
    ndjson_path = os.path.join(ddir, "demo.ndjson")
    if not os.path.isfile(ndjson_path):
        raise FileNotFoundError(f"Missing tiny_demo NDJSON export: {ndjson_path}")

    import kernel as _kernel
    roots = ["TinyDemo.main_theorem:DEMO"]
    headline = ["TinyDemo.main_theorem"]
    toml_path = os.path.join(ddir, "leanre.toml")
    if os.path.isfile(toml_path):
        try:
            import config as _config
            cfg = _config.load_config(toml_path)
            if cfg.kernel_root_specs():
                roots = cfg.kernel_root_specs()
            if cfg.headline_roots:
                headline = list(cfg.headline_roots)
        except Exception:
            pass

    with tempfile.TemporaryDirectory(prefix="leanre_demo_site_") as td:
        kout = os.path.join(td, "kernel_out")
        _kernel.run_pipeline(
            input_path=ndjson_path,
            out_dir=kout,
            src_dir=ddir,
            roots=roots,
            threads=2,
            workers=1,
            auto_build=False,
            verbose=False,
        )
        kdb_path = os.path.join(kout, "kernel.db")
        port_path: Optional[str] = None
        try:
            import portability as _portability
            prep = _portability.analyze_portability(
                decls=headline,
                kernel_db_path=kdb_path,
                src_root=ddir,
            )
            port_path = os.path.join(td, "portability_gems.json")
            with open(port_path, "w", encoding="utf-8") as f:
                json.dump(prep, f, sort_keys=True)
        except Exception:
            port_path = None

        return export_static_site(
            decomp_dir=None,
            out_html=out_html,
            portability=port_path,
            kernel_db=kdb_path,
            src_root=ddir,
            title=title or "leanre — Tiny Demo Explorer",
            with_bundles=True,
        )


def _cmd_export_site(args: argparse.Namespace) -> int:
    if getattr(args, "demo", False):
        res = export_tiny_demo_site(
            out_html=args.out,
            title=None if args.title == "leanre — Static Proof Explorer" else args.title,
        )
    else:
        res = export_static_site(
            decomp_dir=args.decomp_dir,
            out_html=args.out,
            trim_report=args.trim_report,
            cluster_labels=args.cluster_labels,
            portability=args.portability,
            kernel_db=args.kernel_db,
            src_root=args.src_root,
            title=args.title,
            max_nodes_per_blueprint=args.max_nodes,
            max_clusters=args.max_clusters,
            with_bundles=args.with_bundles,
        )
    print(json.dumps(res, indent=2, sort_keys=True))
    return 0


def _add_export_site_args(p: argparse.ArgumentParser) -> None:
    p.add_argument("--demo", action="store_true", help="Build and export the bundled examples/tiny_demo corpus")
    p.add_argument("--decomp-dir", default=None, help="Directory of leanre.decomp/v1 JSON blueprints")
    p.add_argument("--trim-report", default=None, help="Optional trim_report.json path")
    p.add_argument("--cluster-labels", default=None, help="Optional cluster_labels_141.json path")
    p.add_argument("--portability", default=None, help="Optional portability_gems.json path")
    p.add_argument("--kernel-db", default=None, help="Optional kernel.db path")
    p.add_argument("--src-root", default=None, help="Optional Lean source directory for bundle unread-field resolution")
    p.add_argument("--out", required=True, help="Output HTML path")
    p.add_argument("--title", default="leanre — Static Proof Explorer", help="Page title")
    p.add_argument("--max-nodes", type=int, default=250, help="Max nodes embedded per blueprint (default: 250)")
    p.add_argument("--max-clusters", type=int, default=200, help="Max FLIRT clusters embedded (default: 200)")
    p.add_argument("--with-bundles", action="store_true", default=None, help="Force unread-bundle analysis on kernel.db")


def register_cli(sub: Any, dest: str = "export_site_func") -> argparse.ArgumentParser:
    p = sub.add_parser("export-site", help="Export a self-contained offline static HTML explorer")
    _add_export_site_args(p)
    p.set_defaults(**{dest: _cmd_export_site})
    return p


def main(argv: Optional[Sequence[str]] = None) -> int:
    ap = argparse.ArgumentParser(prog="export_site", description="Generate self-contained offline leanre HTML explorer")
    _add_export_site_args(ap)
    args = ap.parse_args(argv)
    return _cmd_export_site(args)


if __name__ == "__main__":
    sys.exit(main())
