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
import datetime
import hashlib
import html
import json
import os
import re
import sqlite3
import sys
import tempfile
from typing import Any, Dict, List, Optional, Sequence, Set, Tuple

_HERE = os.path.dirname(os.path.abspath(__file__))
_REPO_ROOT = os.path.abspath(os.path.join(_HERE, ".."))
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)

SCHEMA_VERSION = "leanre.static_site/1"
SPLIT_MANIFEST_SCHEMA = "leanre.site_manifest/1"
SITE_ASSETS_DIR = os.path.join(_HERE, "site_assets")
MAX_TEXT_SUMMARY = 280
MAX_HEADER_LEN = 220
MAX_SPLIT_FILE_BYTES = 25 * 1024 * 1024
MAX_SEARCH_SHARD_BYTES = 140 * 1024
MAX_SEARCH_TOTAL_BYTES = 3_950_000


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


def _summarize_macro_circuit(
    kernel_db_path: str,
    *,
    src_root: Optional[str] = None,
    portability_json: Optional[str] = None,
    max_nodes: int = 12,
) -> Optional[Dict[str, Any]]:
    """Build a deterministic, compact offline Zoom 0 Macro Proof Circuit summary + SVG."""
    import circuit as _circuit

    raw = _circuit.build_macro_circuit(
        kernel_db_path=kernel_db_path,
        src_root=src_root if (src_root and os.path.isdir(src_root)) else None,
        portability_json=portability_json,
        max_nodes=max_nodes,
    )
    # Strip timing jitter & host/temp paths before rendering so SVG & JSON are byte-deterministic
    pins = dict(raw.get("pins") or {})
    pins["elapsed_seconds"] = 0
    pins["kernel_db"] = os.path.basename(kernel_db_path)
    pins["src_root"] = os.path.basename(src_root) if (src_root and os.path.isdir(src_root)) else None
    raw["pins"] = pins

    svg_dark = _circuit.render_circuit_svg(raw, theme="dark")
    st = raw.get("stats") or {}
    compact_nodes = [
        {
            "id": str(n.get("id") or ""),
            "label": str(n.get("label") or ""),
            "full_name": str(n.get("full_name") or ""),
            "kind": str(n.get("kind") or ""),
            "status": str(n.get("status") or ""),
            "badge": str(n.get("badge") or ""),
            "tooltip": _clip(n.get("tooltip"), 240),
            "zoom_target": n.get("zoom_target"),
        }
        for n in (raw.get("nodes") or [])
    ]
    return {
        "schema": str(raw.get("schema") or "leanre.circuit/1"),
        "mode": "macro",
        "title": str(raw.get("title") or "Macro Proof-Circuit Map"),
        "stats": {
            "total_decls": int(st.get("total_decls") or 0),
            "live_decls": int(st.get("live_decls") or 0),
            "dead_decls": int(st.get("dead_decls") or 0),
            "roots_count": int(st.get("roots_count") or 0),
            "pillars_count": int(st.get("pillars_count") or 0),
            "shared_diamond_roots": int(st.get("shared_diamond_roots") or 0),
            "shared_diamond_decls": int(st.get("shared_diamond_decls") or 0),
            "cross_pillar_shared_edges": int(st.get("cross_pillar_shared_edges") or 0),
            "motif_clusters_count": int(st.get("motif_clusters_count") or 0),
            "islands_count": int(st.get("islands_count") or 0),
            "node_count": int(st.get("node_count") or 0),
            "wire_count": int(st.get("wire_count") or 0),
        },
        "badges": list(raw.get("badges") or [])[:6],
        "legend": list(raw.get("legend") or [])[:8],
        "nodes": compact_nodes,
        "svg": svg_dark,
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
.cir-wrap{position:relative;height:620px;overflow:hidden;border:1px solid var(--border);border-radius:6px;background:#0b1020;cursor:grab}
.cir-wrap.dragging{cursor:grabbing}
.cir-stage{position:absolute;top:0;left:0;transform-origin:0 0}
.cir-stage svg{display:block;user-select:none}
.cir-stage .circuit-node{cursor:pointer;transition:opacity .15s}
.cir-stage .circuit-node:hover rect{filter:brightness(1.16)}
.cir-stage .circuit-node.dim{opacity:.18}
.cir-stage .circuit-node.hl rect{stroke-width:2.8 !important}
.cir-btn{background:var(--elev);color:var(--hi);border:1px solid var(--border);border-radius:6px;padding:5px 10px;font-size:12px;font-weight:600;cursor:pointer}
.cir-btn:hover{border-color:var(--sel);background:var(--hover)}
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
    <button class="tab" data-view="circuit">Proof Circuit</button>
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
  <section class="view" id="view-circuit"></section>
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
  if(DATA.circuit && DATA.circuit.stats){
    const cs = DATA.circuit.stats;
    cards.push(el("div",{className:"card"},[
      el("div",{className:"k"},"Macro Proof Circuit (Zoom 0)"),
      el("div",{className:"v"},fmtNum(cs.node_count) + " nodes"),
      el("div",{className:"d"},fmtNum(cs.motif_clusters_count) + " motifs · " + fmtNum(cs.islands_count) + " islands · " + fmtNum(cs.shared_diamond_decls) + " shared diamond")
    ]));
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

function renderCircuit(){
  const root = document.getElementById("view-circuit");
  clear(root);
  const c = DATA.circuit;
  if(!c || !c.svg){
    root.appendChild(el("div",{className:"panel empty"},"No Zoom 0 Macro Proof Circuit embedded (pass --kernel-db or --demo)."));
    return;
  }
  const st = c.stats || {};
  root.appendChild(el("div",{className:"grid"},[
    el("div",{className:"card"},[
      el("div",{className:"k"},"Live / Dead Split"),
      el("div",{className:"v"},fmtNum(st.live_decls) + " live"),
      el("div",{className:"d"},fmtNum(st.dead_decls) + " dead / " + fmtNum(st.total_decls) + " total")
    ]),
    el("div",{className:"card"},[
      el("div",{className:"k"},"Shared Diamond"),
      el("div",{className:"v"},fmtNum(st.shared_diamond_decls)),
      el("div",{className:"d"},fmtNum(st.shared_diamond_roots) + " roots · " + fmtNum(st.pillars_count) + " dominator pillars")
    ]),
    el("div",{className:"card"},[
      el("div",{className:"k"},"Motif Clusters (k1n/k1a)"),
      el("div",{className:"v"},fmtNum(st.motif_clusters_count)),
      el("div",{className:"d"},"Repeated kernel signature shapes")
    ]),
    el("div",{className:"card"},[
      el("div",{className:"k"},"Portable Islands"),
      el("div",{className:"v"},fmtNum(st.islands_count)),
      el("div",{className:"d"},fmtNum(st.node_count) + " circuit nodes · " + fmtNum(st.wire_count) + " wires")
    ])
  ]));

  const qIn = el("input",{type:"search",placeholder:"Highlight pillar, motif, or island…"});
  const wrap = el("div",{className:"cir-wrap"});
  const stage = el("div",{className:"cir-stage"});
  wrap.appendChild(stage);
  const detail = el("div",{className:"detail-box",style:{marginTop:"12px"}});
  const nodeById = new Map();
  for(const n of (c.nodes || [])) nodeById.set(n.id, n);

  let scale = 1, tx = 14, ty = 14, dragging = false, sx = 0, sy = 0;
  function applyXf(){ stage.style.transform = "translate(" + tx + "px," + ty + "px) scale(" + scale + ")"; }
  function fit(){
    const svg = stage.querySelector("svg");
    if(!svg) return;
    const sw = Number(svg.getAttribute("width")) || 1360;
    const sh = Number(svg.getAttribute("height")) || 760;
    const cw = wrap.clientWidth || 1200;
    const ch = wrap.clientHeight || 620;
    scale = Math.max(0.25, Math.min(1.1, Math.min((cw - 24) / sw, (ch - 24) / sh)));
    tx = Math.max(8, (cw - sw * scale) / 2);
    ty = Math.max(8, (ch - sh * scale) / 2);
    applyXf();
  }
  function showNode(obj){
    clear(detail);
    if(!obj){
      detail.appendChild(el("div",{className:"empty"},"Click any node in the Zoom 0 Macro Proof Circuit above to inspect details and CLI zoom command."));
      return;
    }
    const zt = obj.zoom_target || null;
    detail.appendChild(el("h3",null,obj.full_name || obj.label || obj.id));
    detail.appendChild(el("div",{className:"toolbar"},[
      obj.kind ? badge(obj.kind,"b-S") : null,
      obj.status ? badge(obj.status,obj.status === "dead" ? "b-high" : "b-L") : null,
      obj.badge ? badge(obj.badge,"b-C") : null
    ]));
    detail.appendChild(el("div",{className:"kv"},[
      el("div",{className:"kk"},"Summary"), el("div",{className:"kvv"},obj.tooltip || "—"),
      el("div",{className:"kk"},"Deep Zoom CLI"), el("div",{className:"kvv mono"},(zt && zt.mode && zt.target) ? ("leanre circuit " + zt.mode + " " + zt.target) : "—")
    ]));
  }
  function applySearch(){
    const q = qIn.value.trim().toLowerCase();
    for(const g of stage.querySelectorAll(".circuit-node")){
      const obj = nodeById.get(g.getAttribute("data-node-id") || "") || {};
      const hay = ((obj.label||"") + " " + (obj.full_name||"") + " " + (obj.tooltip||"") + " " + (obj.badge||"")).toLowerCase();
      const hit = q ? hay.includes(q) : false;
      g.classList.toggle("dim", Boolean(q && !hit));
      g.classList.toggle("hl", hit);
    }
  }

  const parser = new DOMParser();
  const doc = parser.parseFromString(c.svg, "image/svg+xml");
  if(doc && !doc.querySelector("parsererror") && doc.documentElement && doc.documentElement.nodeName.toLowerCase() === "svg"){
    for(const bad of doc.documentElement.querySelectorAll("script,foreignObject,iframe,object,embed")) bad.remove();
    const svgEl = document.importNode(doc.documentElement, true);
    stage.appendChild(svgEl);
    for(const g of svgEl.querySelectorAll(".circuit-node")){
      const nid = g.getAttribute("data-node-id") || "";
      const obj = nodeById.get(nid) || {id: nid, label: nid};
      g.addEventListener("click", (ev) => { ev.stopPropagation(); showNode(obj); });
    }
  }

  wrap.addEventListener("pointerdown", (ev) => { if(ev.button !== 0) return; dragging = true; sx = ev.clientX - tx; sy = ev.clientY - ty; wrap.classList.add("dragging"); });
  window.addEventListener("pointermove", (ev) => { if(!dragging) return; tx = ev.clientX - sx; ty = ev.clientY - sy; applyXf(); });
  window.addEventListener("pointerup", () => { dragging = false; wrap.classList.remove("dragging"); });
  wrap.addEventListener("wheel", (ev) => {
    ev.preventDefault();
    const r = wrap.getBoundingClientRect();
    const mx = ev.clientX - r.left, my = ev.clientY - r.top;
    const ns = Math.max(0.2, Math.min(3.5, scale * (ev.deltaY < 0 ? 1.12 : 0.89)));
    tx = mx - (mx - tx) * (ns / scale); ty = my - (my - ty) * (ns / scale); scale = ns; applyXf();
  }, {passive: false});
  qIn.addEventListener("input", applySearch);

  root.appendChild(el("div",{className:"panel"},[
    el("h2",null,c.title || "Zoom 0 · Macro Proof Circuit"),
    el("div",{className:"toolbar"},[
      qIn,
      el("button",{className:"cir-btn",onclick:()=>{ scale = Math.min(3.5, scale * 1.2); applyXf(); }},"+"),
      el("button",{className:"cir-btn",onclick:()=>{ scale = Math.max(0.2, scale / 1.2); applyXf(); }},"−"),
      el("button",{className:"cir-btn",onclick:fit},"Fit"),
      el("button",{className:"cir-btn",onclick:()=>{
        const blob = new Blob([c.svg], {type:"image/svg+xml;charset=utf-8"});
        const u = URL.createObjectURL(blob);
        const a = document.createElement("a");
        a.href = u; a.download = "leanre_macro_circuit.svg";
        document.body.appendChild(a); a.click(); a.remove(); URL.revokeObjectURL(u);
      }},"Download SVG")
    ]),
    wrap,
    detail
  ]));
  showNode(null);
  requestAnimationFrame(fit);
  window._leanreFitCircuit = fit;
}

for(const btn of document.querySelectorAll("#tabBar .tab")){
  const v = btn.getAttribute("data-view");
  const has = (v === "overview") ||
    (v === "circuit" && !!(DATA.circuit && DATA.circuit.svg)) ||
    (v === "blueprints" && (DATA.blueprints || []).length > 0) ||
    (v === "trim" && !!DATA.trim_report) ||
    (v === "flirt" && !!DATA.cluster_atlas) ||
    (v === "portability" && !!(DATA.portability && (DATA.portability.targets || []).length > 0)) ||
    (v === "kernel" && !!DATA.kernel);
  if(!has) btn.setAttribute("disabled", "disabled");
  btn.addEventListener("click", () => {
    if(!btn.hasAttribute("disabled")){
      switchView(v);
      if(v === "circuit" && typeof window._leanreFitCircuit === "function") requestAnimationFrame(window._leanreFitCircuit);
    }
  });
}

renderOverview();
renderCircuit();
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
    circuit_summary: Optional[Dict[str, Any]] = None
    if kernel_db:
        if os.path.islink(kernel_db):
            raise ValueError(f"Refusing symlinked kernel_db: {kernel_db}")
        kernel_summary = _summarize_kernel_db(kernel_db, src_root=src_root, with_bundles=with_bundles)
        circuit_summary = _summarize_macro_circuit(
            kernel_db,
            src_root=src_root,
            portability_json=resolved_portability,
        )

    return {
        "schema": SCHEMA_VERSION,
        "title": title,
        "blueprints": blueprints,
        "trim_report": trim_summary,
        "cluster_atlas": atlas_summary,
        "portability": portability_summary,
        "kernel": kernel_summary,
        "circuit": circuit_summary,
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
        "has_circuit": payload["circuit"] is not None,
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


# ---------------------------------------------------------------------------
# Lazy-Sharded Split-Directory Static Site Builder (`--split-dir`)
# ---------------------------------------------------------------------------

CURATED_BUNDLE_SHOWCASE: Tuple[str, ...] = (
    "OpenLiteratureStatements",
    "HypsAlt",
    "RealInAlt",
    "FamCore",
    "ChOK",
    "Green",
    "VWin",
    "UnitaryGroupThirdPlaceHypotheses",
    "SizeData₂",
    "Host",
    "CovolumeBoundOfX",
    "DivX",
    "D7",
    "FamP",
    "AllRowsAlt",
    "ThetaLocalInputs",
    "LiteratureCMHypothesis",
)

CURATED_THEOREM_SHOWCASE: Tuple[str, ...] = (
    "riemannHypothesis",
    "riemannZeta_eq_zero_re",
    "allChi",
    "everyCharacter",
    "everyCharacter_of_row",
    "vwin_of_row",
    "every_character_of_theta_integrals_local_matching",
    "topCovolSlim2_use_alt_alt",
    "galoisLocalGlobalStrong_recParameter",
    "llOf_alt",
    "linkGLOBAL7_items",
    "ch_balance",
    "sEEofTT",
    "joint_a_ramified_holds",
    "boundsMu",
    "slope_bounds",
    "linkG_concrete5",
    "deRham_potentiallySemistable",
    "strongResolutionOfSingularitiesCharZero",
    "finiteH_of_isProper",
    "abelianHodgeDeRham'",
    "globalEulerChar_full",
    "bijective_gsRealRes",
    "exists_baseLattice_of_prime_alt",
    "deep_slim_use",
    "memberE_closing_alt_alt",
    "bwit_exists_alt",
    "exists_ranks_rankVal_frame",
    "fieldChi",
    "core_gm",
    "QH.meanSqK",
    "siegelLower",
    "arith_hilbert_samuel_of_literature",
    "places_at_of",
    "vwinAt_of_joint",
    "divinN_of_hypV",
    "twisted_multiplicity_eq",
)

CANONICAL_FINDING_ORDER: Tuple[str, ...] = (
    "tcb-and-statements",
    "proof-map",
    "remark-vs-code",
    "dead-code-and-timeouts",
    "proof-size-and-bloat",
    "aliases-and-dummy-slots",
    "intentional-shortcuts",
    "genuine-math",
)

_ANALYSIS_HEADING_TO_CATEGORY: Dict[str, str] = {
    "mathematical reading guide & deep chain audits": "Math audits",
    "core": "Core",
    "pillar analyses": "Pillars",
    "classical theorems": "Classical theorems",
    "`dom >= 1,000` closures": "dom >= 1,000 closures",
    "blueprint, semantic audits & portability": "Semantic rechecks",
    "corpus sweeps & cross-repo benchmarks": "Benchmarks & sweeps",
}

_DECOMP_FRIENDLY_TITLES: Dict[str, str] = {
    "spine_map": "Spine & 332k Shared Diamond",
    "pillar_theta": "Pillar A — Theta Integrals & Local Matching",
    "pillar_galois": "Pillar B — Galois Representations & Row0b",
    "pillar_window": "Pillar C — Window Inequality & VWin",
    "pillar_volume_lit": "Pillar D — Self-Intersection Volume & Literature",
    "tcb_audit": "Layer 2 Semantic TCB & Contract Audit",
    "explicit_formula_bridge": "Explicit Formula Bridge (TopG → ZeroFreeAll)",
    "stageu_existence": "Pillar A — StageU Existence & Bundles",
    "stageu_hyps_spine": "Pillar A — HypsAlt & Definite Side",
    "allrows_engines": "Pillar A — AllRows & LinkR Engines",
    "linkg_consumer_bridge": "Pillar A — LinkG Consumer Bridge",
    "pillar_a_onto_galc_open0": "Pillar A — Onto / GalC / Open0",
    "geo_one_galois": "Pillar B — geoOne & Geometric Realization",
    "vwin_engines": "Pillar C — VWin & Window Engines",
    "covolume_engines": "Pillar D — Covolume & Height Engines",
    "literature_engines": "Pillar D — Literature Engines",
    "diamond_shared_library": "Shared Diamond — 18 Roots & Row Siblings",
    "published_catalogue": "Published Results Catalogue",
    "anomaly_sweep": "Whole-Corpus Structural Anomaly Sweep",
    "unread_bundles_census": "Unread Bundles & Placeholders Census",
    "decide_kernel_live14": "Live 14 decide +kernel Files Audit",
}

_SUBSCRIPT_MAP = str.maketrans("₀₁₂₃₄₅₆₇₈₉", "0123456789")
_FORBIDDEN_HOST_PATH_RE = re.compile(
    r"(?:"
    + "/" + "usr" + "/" + "local" + "/" + r"[^/\s]+/home/"
    + "|" + "/" + "usr" + "/" + "local" + "/" + "google"
    + "|" + "/" + "ho" + r"me/[A-Za-z0-9_.-]+"
    + "|" + "/" + "Us" + r"ers/[A-Za-z0-9_.-]+"
    + ")"
)
_FALLBACK_SPLIT_HTML = """<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>__TITLE__</title>
<style>
:root{--bg:#0b1020;--panel:#121a30;--border:#273557;--text:#e2e8f0;--muted:#94a3b8;--accent:#38bdf8;--mono:ui-monospace,Menlo,Consolas,monospace}
*{box-sizing:border-box}
body{margin:0;padding:24px;background:var(--bg);color:var(--text);font-family:system-ui,-apple-system,sans-serif;font-size:14px;line-height:1.5}
.wrap{max-width:1100px;margin:0 auto}
.card{background:var(--panel);border:1px solid var(--border);border-radius:10px;padding:16px;margin-bottom:16px}
h1,h2{margin:0 0 10px 0}
.kpis{display:grid;grid-template-columns:repeat(auto-fit,minmax(160px,1fr));gap:10px}
.kpi{background:rgba(255,255,255,.03);border:1px solid var(--border);border-radius:8px;padding:10px}
.kpi .lbl{font-size:11px;color:var(--muted);text-transform:uppercase}
.kpi .val{font-family:var(--mono);font-size:20px;font-weight:700;color:var(--accent)}
code,pre{font-family:var(--mono)}
a{color:var(--accent)}
</style>
</head>
<body>
<div class="wrap">
  <div class="card">
    <h1 id="title">__TITLE__</h1>
    <div id="meta" style="color:var(--muted)">Loading manifest.json…</div>
  </div>
  <div class="kpis" id="kpis"></div>
  <div class="card" id="circuits" style="margin-top:16px"></div>
</div>
<script>
(function(){
"use strict";
fetch("./manifest.json").then(function(r){return r.json();}).then(function(m){
  document.getElementById("title").textContent = m.title || "leanre Static Site";
  document.getElementById("meta").textContent = "schema=" + (m.schema || "") + " · repo=" + (m.repo_name || "");
  var k = document.getElementById("kpis");
  var st = m.stats || {};
  [["Live Decls", st.live_decls], ["Total Decls", st.total_decls], ["Edges", st.edges], ["Blueprints", st.blueprints_count], ["Search Entries", st.search_entries]].forEach(function(pair){
    var d = document.createElement("div"); d.className = "kpi";
    var l = document.createElement("div"); l.className = "lbl"; l.textContent = pair[0];
    var v = document.createElement("div"); v.className = "val"; v.textContent = String(pair[1] != null ? pair[1] : 0);
    d.appendChild(l); d.appendChild(v); k.appendChild(d);
  });
  var c = document.getElementById("circuits");
  var h = document.createElement("h2"); h.textContent = "Pre-rendered Circuits";
  c.appendChild(h);
  var p = document.createElement("div");
  p.textContent = "Bundles: " + ((m.circuits && m.circuits.bundles || []).length) + " · Theorems: " + ((m.circuits && m.circuits.theorems || []).length);
  c.appendChild(p);
}).catch(function(err){
  document.getElementById("meta").textContent = "Failed to load manifest.json: " + err;
});
})();
</script>
</body>
</html>
"""


def _safe_write_bytes(out_path: str, data: bytes) -> None:
    if os.path.islink(out_path):
        raise ValueError(f"Refusing to write through symlink: {out_path}")
    parent = os.path.dirname(os.path.abspath(out_path))
    if parent:
        os.makedirs(parent, exist_ok=True)
    with open(out_path, "wb") as f:
        f.write(data)


def _safe_write_json(out_path: str, obj: Any) -> int:
    raw = json.dumps(obj, ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode("utf-8")
    _safe_write_bytes(out_path, raw)
    return len(raw)


def _safe_slug(name: str, used: Set[str]) -> str:
    """Create a clean GitHub-Pages-safe ASCII slug unique across `used`."""
    short = str(name or "").rsplit(".", 1)[-1]
    norm = short.translate(_SUBSCRIPT_MAP).replace("'", "_prime")
    cleaned = re.sub(r"[^A-Za-z0-9_-]+", "_", norm).strip("._")
    if not cleaned:
        cleaned = "item"
    exact_ascii = (cleaned == short and short == name)
    cand = cleaned
    if cand in used or (not exact_ascii and len(name) > len(short) and "." in name):
        full_norm = name.translate(_SUBSCRIPT_MAP).replace("'", "_prime").replace(".", "_")
        full_clean = re.sub(r"[^A-Za-z0-9_-]+", "_", full_norm).strip("._")
        if full_clean and full_clean not in used and len(full_clean) <= 96:
            cand = full_clean
    if cand in used or not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9_-]*", cand):
        h = hashlib.sha1(name.encode("utf-8", errors="replace")).hexdigest()[:6]
        base = re.sub(r"^[^A-Za-z0-9]+", "", cand) or "item"
        cand = f"{base[:72]}_{h}"
    while cand in used:
        h = hashlib.sha1(f"{name}:{len(used)}".encode("utf-8")).hexdigest()[:6]
        cand = f"{cand[:72]}_{h}"
    used.add(cand)
    return cand


def _search_prefix_bucket(text: str) -> str:
    """Return lowercase 2-char alphanumeric shard key ('a0'..'zz') or '_'."""
    alnum = re.sub(r"[^a-z0-9]", "", str(text or "").lower())
    if len(alnum) >= 2:
        return alnum[:2]
    return "_"


def _sanitize_text_paths(val: str) -> str:
    return _FORBIDDEN_HOST_PATH_RE.sub("<path>", val)


def _sanitize_json_value(obj: Any) -> Any:
    if isinstance(obj, str):
        return _sanitize_text_paths(obj) if _FORBIDDEN_HOST_PATH_RE.search(obj) else obj
    if isinstance(obj, list):
        return [_sanitize_json_value(v) for v in obj]
    if isinstance(obj, dict):
        return {k: _sanitize_json_value(v) for k, v in obj.items()}
    return obj


def _sanitize_circuit_payload(payload: Dict[str, Any], *, mode: str) -> Dict[str, Any]:
    """Strip workstation paths and raw multi-line/step proof bodies before SVG & JSON export."""
    out = json.loads(json.dumps(payload, ensure_ascii=False))
    pins = out.get("pins")
    if isinstance(pins, dict):
        if pins.get("kernel_db"):
            pins["kernel_db"] = os.path.basename(str(pins["kernel_db"]))
        if pins.get("src_root"):
            pins["src_root"] = os.path.basename(str(pins["src_root"]))
        if mode == "macro":
            pins["elapsed_seconds"] = 0
    if mode == "theorem":
        for node in out.get("nodes") or []:
            if not isinstance(node, dict):
                continue
            nid = str(node.get("id") or "")
            if nid.startswith("step:"):
                lbl = str(node.get("label") or nid)
                line_no = node.get("line_no")
                callees = [str(c.get("short") or "") for c in (node.get("callees") or []) if c.get("short")]
                outputs = [str(x) for x in (node.get("outputs") or []) if x]
                parts = [lbl]
                if line_no is not None:
                    parts.append(f"L{line_no}")
                if outputs:
                    parts.append("-> " + ", ".join(outputs[:4]))
                if callees:
                    parts.append("calls: " + ", ".join(callees[:4]))
                node["full_name"] = " | ".join(parts)
                node["tooltip"] = " | ".join(parts)
    return _sanitize_json_value(out)


def _resolve_preferred_decl(
    conn: sqlite3.Connection,
    query: str,
    *,
    preferred_kinds: Tuple[str, ...] = (),
) -> Optional[Tuple[int, str, str, int, int, int]]:
    """Resolve a declaration name/suffix without failing on benign suffix collisions.

    Returns ``(decl_id, fqn, kind, live_mask, fan_in, dom_subtree)`` or ``None``.
    """
    q = str(query or "").strip()
    if not q:
        return None
    has_dom = (
        conn.execute("SELECT 1 FROM sqlite_master WHERE type='table' AND name='dom'").fetchone()
        is not None
    )
    has_dm = (
        conn.execute("SELECT 1 FROM sqlite_master WHERE type='table' AND name='decl_module'").fetchone()
        is not None
    )

    def _fetch(where_sql: str, param: str) -> List[Tuple[int, str, str, int, int, int, int]]:
        if has_dom and has_dm:
            sql = (
                "SELECT d.id, d.name, d.kind, d.live_mask, d.fan_in, "
                "       COALESCE(dm_tree.subtree_size, 0), "
                "       CASE WHEN dm.decl_id IS NOT NULL THEN 1 ELSE 0 END "
                "FROM decls d "
                "LEFT JOIN dom dm_tree ON dm_tree.decl_id = d.id AND dm_tree.tree_id = 0 "
                "LEFT JOIN decl_module dm ON dm.decl_id = d.id "
                f"WHERE {where_sql}"
            )
        elif has_dom:
            sql = (
                "SELECT d.id, d.name, d.kind, d.live_mask, d.fan_in, "
                "       COALESCE(dm_tree.subtree_size, 0), 1 "
                "FROM decls d "
                "LEFT JOIN dom dm_tree ON dm_tree.decl_id = d.id AND dm_tree.tree_id = 0 "
                f"WHERE {where_sql}"
            )
        else:
            sql = (
                "SELECT d.id, d.name, d.kind, d.live_mask, d.fan_in, 0, 1 "
                f"FROM decls d WHERE {where_sql}"
            )
        return [
            (int(r[0]), str(r[1]), str(r[2]), int(r[3]), int(r[4]), int(r[5]), int(r[6]))
            for r in conn.execute(sql, (param,)).fetchall()
        ]

    for cand in (q, q[7:] if q.startswith("_root_.") else q):
        exact_rows = _fetch("d.name = ?", cand)
        if exact_rows:
            r = exact_rows[0]
            return r[:6]

    import kernel as _kernel
    q_clean = q[7:] if q.startswith("_root_.") else q
    glob_pat = f"*.{_kernel._escape_glob(q_clean)}"
    rows = _fetch("d.name GLOB ?", glob_pat)
    if not rows:
        try:
            did, fqn, _ = _kernel._resolve_decl_id(conn, q, allow_suffix=True, allow_const_folding=True)
            rows = _fetch("d.id = ?", str(did))
            if not rows:
                row = conn.execute(
                    "SELECT id, name, kind, live_mask, fan_in FROM decls WHERE id = ?",
                    (did,),
                ).fetchone()
                if row:
                    return (int(row[0]), str(row[1]), str(row[2]), int(row[3]), int(row[4]), 0)
        except Exception:
            return None
    if not rows:
        return None

    kind_prio = {k: i for i, k in enumerate(preferred_kinds)}

    def _rank(r: Tuple[int, str, str, int, int, int, int]) -> Tuple[int, int, int, int, int, int, str]:
        _did, name, kind, live_mask, fan_in, sub, in_proj = r
        return (
            0 if live_mask != 0 else 1,
            0 if in_proj else 1,
            kind_prio.get(kind, len(kind_prio) + 1),
            0 if not name.startswith("_private.") else 1,
            -sub,
            -fan_in,
            name,
        )

    best = min(rows, key=_rank)
    return best[:6]


def _extract_md_title_and_summary(md_text: str, fallback_slug: str) -> Tuple[str, str]:
    title = fallback_slug.replace("_", " ").replace("-", " ")
    lines = md_text.splitlines()
    for ln in lines:
        s = ln.strip()
        if s.startswith("# "):
            raw_t = s[2:].strip()
            raw_t = re.sub(r"\[([^\]]+)\]\([^)]+\)", r"\1", raw_t)
            raw_t = raw_t.replace("`", "")
            title = _clip(raw_t, 140)
            break

    para_lines: List[str] = []
    in_fence = False
    for ln in lines:
        s = ln.strip()
        if s.startswith("```"):
            in_fence = not in_fence
            continue
        if in_fence:
            continue
        if not s:
            if para_lines:
                break
            continue
        if s.startswith(("#", ">", "|", "---", "===", "<details", "<summary")):
            if para_lines:
                break
            continue
        if s.startswith(("- ", "* ")) and not para_lines:
            continue
        para_lines.append(s)
    summary_raw = " ".join(para_lines)
    summary_raw = re.sub(r"\[([^\]]+)\]\([^)]+\)", r"\1", summary_raw)
    summary_raw = summary_raw.replace("**", "").replace("`", "")
    return title, _clip(summary_raw, 240)


def _parse_analysis_categories(analysis_dir: str) -> Tuple[Dict[str, str], List[str]]:
    readme = os.path.join(analysis_dir, "README.md")
    cat_map: Dict[str, str] = {}
    order: List[str] = []
    if not os.path.isfile(readme) or os.path.islink(readme):
        return cat_map, order
    with open(readme, "r", encoding="utf-8", errors="replace") as f:
        text = f.read()
    cur_cat = "Analysis"
    for ln in text.splitlines():
        s = ln.strip()
        if s.startswith("## "):
            h = s[3:].strip().lower()
            cur_cat = _ANALYSIS_HEADING_TO_CATEGORY.get(h, s[3:].strip())
            continue
        for fn in re.findall(r"\(([A-Za-z0-9_.-]+\.md)\)", s):
            if fn == "README.md":
                continue
            slug = fn[:-3]
            if slug not in cat_map:
                cat_map[slug] = cur_cat
                order.append(slug)
    return cat_map, order


def _fallback_dossier_category(slug: str) -> str:
    low = slug.lower()
    if low.startswith("dom"):
        return "dom >= 1,000 closures"
    if low.startswith(("adversarial_", "audit_padic", "audit_hironaka", "audit_cohomology")):
        return "Semantic rechecks"
    if low.startswith(("audit_", "rh_proof")):
        return "Math audits"
    if low.startswith(("pillar_", "geo_one", "away_tame0", "galois_", "vwin_", "kato_", "stageu_", "allrows_", "linkg_", "theta_", "fourier_", "counting_", "covolume_", "arakelov_")):
        return "Pillars"
    if low.startswith(("famous_", "literature_", "classical_", "harish_", "compactification_", "siegel_", "convolution_")):
        return "Classical theorems"
    if low.startswith(("generic_corpus", "unread_", "anomaly_", "duplication_", "cluster_atlas")):
        return "Benchmarks & sweeps"
    return "Core"


def _collect_markdown_docs(
    src_dir: Optional[str],
    out_subdir: str,
    split_dir: str,
    *,
    is_findings: bool = False,
    is_dossiers: bool = False,
) -> List[Dict[str, Any]]:
    if not src_dir or not os.path.isdir(src_dir) or os.path.islink(src_dir):
        return []
    cat_map: Dict[str, str] = {}
    order_list: List[str] = []
    if is_dossiers:
        cat_map, order_list = _parse_analysis_categories(src_dir)
    elif is_findings:
        order_list = list(CANONICAL_FINDING_ORDER)
    order_rank = {slug: idx for idx, slug in enumerate(order_list)}

    files = sorted(
        fn
        for fn in os.listdir(src_dir)
        if fn.endswith(".md") and fn.upper() != "README.MD"
    )
    files.sort(key=lambda fn: (order_rank.get(fn[:-3], len(order_rank) + 1), fn))

    out: List[Dict[str, Any]] = []
    for fn in files:
        full = os.path.join(src_dir, fn)
        if os.path.islink(full) or not os.path.isfile(full):
            continue
        with open(full, "r", encoding="utf-8", errors="replace") as f:
            raw_text = f.read()
        if _FORBIDDEN_HOST_PATH_RE.search(raw_text):
            raw_text = _sanitize_text_paths(raw_text)
        raw_bytes = raw_text.encode("utf-8")
        slug = fn[:-3]
        rel_path = f"data/{out_subdir}/{fn}"
        _safe_write_bytes(os.path.join(split_dir, rel_path), raw_bytes)
        title, summary = _extract_md_title_and_summary(raw_text, slug)
        entry: Dict[str, Any] = {
            "slug": slug,
            "title": title,
            "path": rel_path,
            "bytes": len(raw_bytes),
        }
        if is_findings:
            entry["summary"] = summary
        if is_dossiers:
            entry["category"] = cat_map.get(slug) or _fallback_dossier_category(slug)
        out.append(entry)
    return out


def _collect_split_blueprints(
    decomp_dir: Optional[str],
    split_dir: str,
) -> Tuple[List[Dict[str, Any]], Optional[str]]:
    if not decomp_dir or not os.path.isdir(decomp_dir) or os.path.islink(decomp_dir):
        return [], None
    blueprints: List[Dict[str, Any]] = []
    found_trim: Optional[str] = None
    for fn in sorted(os.listdir(decomp_dir)):
        if not fn.endswith(".json"):
            continue
        full = os.path.join(decomp_dir, fn)
        if os.path.islink(full) or not os.path.isfile(full):
            continue
        try:
            with open(full, "r", encoding="utf-8") as f:
                doc = json.load(f)
        except (OSError, json.JSONDecodeError):
            continue
        if not isinstance(doc, dict):
            continue
        sc = doc.get("schema")
        if sc == "leanre.trim/1" and found_trim is None:
            found_trim = full
            continue
        if sc != "leanre.decomp/v1":
            continue
        clean_doc = _sanitize_json_value(doc)
        rel_path = f"data/decomp/{fn}"
        nbytes = _safe_write_json(os.path.join(split_dir, rel_path), clean_doc)
        nodes = [n for n in (clean_doc.get("nodes") or []) if isinstance(n, dict)]
        non_opaque = sum(1 for n in nodes if n.get("status") != "OPAQUE")
        stem = fn[:-5]
        title = str(
            clean_doc.get("title")
            or _DECOMP_FRIENDLY_TITLES.get(stem)
            or stem.replace("_", " ").title()
        )
        blueprints.append({
            "id": stem,
            "title": title,
            "pillar": str(clean_doc.get("pillar") or ""),
            "root": str(clean_doc.get("root") or ""),
            "path": rel_path,
            "bytes": nbytes,
            "node_count": len(nodes),
            "non_opaque_count": non_opaque,
        })
    return blueprints, found_trim


def _strip_atlas_input_paths(doc: Any) -> Any:
    """Strip any absolute filesystem paths under `inputs.*` to safe basenames."""
    if not isinstance(doc, dict) or not isinstance(doc.get("inputs"), dict):
        return doc
    out = dict(doc)
    clean_inputs: Dict[str, Any] = {}
    for k, v in doc["inputs"].items():
        if isinstance(v, str) and (os.path.isabs(v) or v.startswith("/") or re.match(r"^[A-Za-z]:[/\\]", v)):
            clean_inputs[k] = os.path.basename(v.rstrip("/\\")) or "<path>"
        else:
            clean_inputs[k] = v
    out["inputs"] = clean_inputs
    return out


def _copy_compact_json_asset(
    src_path: Optional[str],
    split_dir: str,
    rel_dst: str,
    transform: Optional[Any] = None,
) -> Optional[str]:
    if not src_path:
        return None
    if os.path.islink(src_path):
        raise ValueError(f"Refusing symlinked asset: {src_path}")
    if not os.path.isfile(src_path):
        return None
    with open(src_path, "r", encoding="utf-8") as f:
        doc = json.load(f)
    if transform is not None:
        doc = transform(doc)
    clean_doc = _sanitize_json_value(doc)
    _safe_write_json(os.path.join(split_dir, rel_dst), clean_doc)
    return rel_dst


def _resolve_repo_meta(
    *,
    config_path: Optional[str],
    src_root: Optional[str],
    kernel_db: Optional[str],
    decomp_dir: Optional[str],
    demo_mode: bool,
    title: Optional[str],
    repo_url_override: Optional[str],
    pinned_commit_override: Optional[str],
    src_prefix_override: Optional[str],
) -> Dict[str, Any]:
    import config as _config

    cfg = None
    if config_path:
        cfg = _config.load_config(config_path)
    elif demo_mode:
        demo_toml = os.path.join(_REPO_ROOT, "examples", "tiny_demo", "leanre.toml")
        if os.path.isfile(demo_toml):
            cfg = _config.load_config(demo_toml)
    else:
        for probe in (src_root, decomp_dir, kernel_db):
            if not probe:
                continue
            loc = _config.find_local_config(probe)
            if loc is not None:
                cfg = _config.load_config(str(loc))
                break
        if cfg is None:
            for probe in (src_root, decomp_dir, kernel_db):
                if not probe:
                    continue
                try:
                    if os.path.realpath(probe).startswith(_REPO_ROOT + os.sep):
                        root_toml = os.path.join(_REPO_ROOT, "leanre.toml")
                        if os.path.isfile(root_toml):
                            cfg = _config.load_config(root_toml)
                            break
                except OSError:
                    pass

    repo_name = (cfg.project_name if cfg and cfg.project_name else "") or (
        "tiny_demo" if demo_mode else (os.path.basename(os.path.abspath(src_root)) if src_root else "leanre")
    )
    pinned_commit = pinned_commit_override if pinned_commit_override is not None else (
        cfg.pinned_commit if cfg and cfg.pinned_commit else None
    )

    repo_url: Optional[str] = None
    src_prefix: str = ""
    if cfg and cfg.repo_url:
        repo_url = cfg.repo_url.rstrip("/")
    if cfg and cfg.upstream_url_template:
        m = re.match(r"^(https://github\.com/[^/]+/[^/]+)/blob/\{commit\}/(.*?)\{path\}", cfg.upstream_url_template)
        if m:
            if not repo_url:
                repo_url = m.group(1).rstrip("/")
            src_prefix = m.group(2)
    if not src_prefix and not demo_mode and src_root and os.path.basename(os.path.realpath(src_root)) == "src":
        src_prefix = "src/"
    if repo_url_override is not None:
        repo_url = repo_url_override.rstrip("/") or None
    if src_prefix_override is not None:
        src_prefix = src_prefix_override

    eff_title = title
    if not eff_title:
        eff_title = "leanre — Tiny Demo Explorer" if demo_mode else f"leanre — {repo_name} Proof Explorer"

    return {
        "title": eff_title,
        "repo_name": repo_name,
        "repo_url": repo_url,
        "pinned_commit": pinned_commit,
        "src_prefix": src_prefix,
        "cfg": cfg,
    }


def _count_files_and_lines(
    *,
    leanre_db: Optional[str],
    src_root: Optional[str],
    trim_doc: Optional[Dict[str, Any]],
    kernel_conn: Optional[sqlite3.Connection],
) -> Tuple[int, int]:
    if leanre_db and os.path.isfile(leanre_db) and not os.path.islink(leanre_db):
        lconn = _open_ro(leanre_db)
        try:
            row = lconn.execute("SELECT COUNT(*), COALESCE(SUM(lines_wc), 0) FROM modules").fetchone()
            if row and int(row[0]) > 0:
                return int(row[0]), int(row[1])
        finally:
            lconn.close()
    if trim_doc and isinstance(trim_doc.get("baseline"), dict):
        base = trim_doc["baseline"]
        if base.get("total_modules") and base.get("total_lines_wc"):
            return int(base["total_modules"]), int(base["total_lines_wc"])
    if src_root and os.path.isdir(src_root):
        total_files = 0
        total_lines = 0
        for root, dirs, files in os.walk(src_root):
            dirs[:] = sorted(d for d in dirs if d not in (".git", ".lake", "build", "__pycache__"))
            for fn in files:
                if fn.endswith(".lean"):
                    total_files += 1
                    try:
                        with open(os.path.join(root, fn), "rb") as f:
                            total_lines += sum(1 for _ in f)
                    except OSError:
                        pass
        if total_files > 0:
            return total_files, total_lines
    if kernel_conn is not None:
        has_dm = (
            kernel_conn.execute(
                "SELECT 1 FROM sqlite_master WHERE type='table' AND name='decl_module'"
            ).fetchone()
            is not None
        )
        if has_dm:
            cnt = int(kernel_conn.execute("SELECT COUNT(DISTINCT module) FROM decl_module").fetchone()[0])
            return cnt, 0
    return 0, 0


def _build_overview_pillars(
    conn: Optional[sqlite3.Connection],
    *,
    live_decls: int,
    macro_payload: Optional[Dict[str, Any]],
) -> List[Dict[str, Any]]:
    if conn is None or live_decls <= 0:
        return []
    has_dom = (
        conn.execute("SELECT 1 FROM sqlite_master WHERE type='table' AND name='dom'").fetchone()
        is not None
    )
    if not has_dom:
        return []
    trow = conn.execute("SELECT id FROM dom_trees WHERE label='ALL'").fetchone()
    if trow is None:
        trow = conn.execute("SELECT id FROM dom_trees ORDER BY id LIMIT 1").fetchone()
    if trow is None:
        return []
    tid = int(trow[0])

    # Check if canonical RH spine markers exist in tree 0
    rh_markers = [
        "allChi",
        "UpperTheory.FinalTheorems.everyCharacter",
        "UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter",
        "UpperTheory.FinalTheorems.everyCharacter_of_row",
        "UpperTheory.One.vwin_of_row",
        "UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin",
        "UpperTheory.Lit.every_character_of_theta_integrals_local_matching",
        "SelfIntersectionVolumeEstimates.topCovolSlim2_use_alt_alt",
    ]
    ph = ",".join("?" for _ in rh_markers)
    rh_rows = {
        str(r[0]): (int(r[1]), int(r[2]), str(r[3]) if r[3] is not None else None)
        for r in conn.execute(
            f"SELECT d.name, dm.subtree_size, dm.depth, dp.name "
            f"FROM decls d "
            f"JOIN dom dm ON dm.decl_id = d.id AND dm.tree_id = ? "
            f"LEFT JOIN decls dp ON dp.id = dm.idom "
            f"WHERE d.name IN ({ph})",
            [tid, *rh_markers],
        ).fetchall()
    }

    def _pct(sz: int) -> float:
        return round(100.0 * sz / max(1, live_decls), 2)

    if len(rh_rows) == len(rh_markers):
        allchi_sz = rh_rows["allChi"][0]
        bridge_sz = max(0, live_decls - allchi_sz)
        ev_sz = rh_rows["UpperTheory.FinalTheorems.everyCharacter"][0]
        b_sz = rh_rows["UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter"][0]
        row_sz = rh_rows["UpperTheory.FinalTheorems.everyCharacter_of_row"][0]
        c_sz = rh_rows["UpperTheory.One.vwin_of_row"][0]
        lit_vw_sz = rh_rows["UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin"][0]
        a_sz = rh_rows["UpperTheory.Lit.every_character_of_theta_integrals_local_matching"][0]
        d_sz = rh_rows["SelfIntersectionVolumeEstimates.topCovolSlim2_use_alt_alt"][0]
        lit_res_sz = max(0, lit_vw_sz - 1 - a_sz - d_sz)
        row_sib_sz = max(0, row_sz - 1 - c_sz - lit_vw_sz)
        dia_sz = max(0, ev_sz - 1 - b_sz - row_sz)
        return [
            {
                "id": "main",
                "name": "Main (5 headline roots)",
                "label": "Main",
                "role": "root",
                "decl": "riemannHypothesis",
                "target": "riemannHypothesis",
                "subtree_size": live_decls,
                "pct_live": 100.0,
                "depth": 0,
                "idom": None,
                "note": "5 headline RH/GRH theorems over Mathlib predicates",
                "description": "5 headline RH/GRH theorems over Mathlib predicates",
                "circuit_mode": "theorem",
                "circuit_target": "riemannHypothesis",
            },
            {
                "id": "bridge",
                "name": "Bridge outside allChi",
                "label": "bridge",
                "role": "bridge",
                "decl": None,
                "target": None,
                "subtree_size": bridge_sz,
                "pct_live": _pct(bridge_sz),
                "depth": 0,
                "idom": None,
                "note": "Functional-equation reflection outside allChi (Mathlib + 31 project decls)",
                "description": "Functional-equation reflection outside allChi (Mathlib + 31 project decls)",
                "circuit_mode": None,
                "circuit_target": None,
            },
            {
                "id": "allChi",
                "name": "allChi",
                "label": "allChi",
                "role": "spine",
                "decl": "allChi",
                "target": "allChi",
                "subtree_size": allchi_sz,
                "pct_live": _pct(allchi_sz),
                "depth": rh_rows["allChi"][1],
                "idom": rh_rows["allChi"][2],
                "note": "Single bottleneck dominating 96.0% of all live declarations",
                "description": "Single bottleneck dominating 96.0% of all live declarations",
                "circuit_mode": "theorem",
                "circuit_target": "allChi",
            },
            {
                "id": "everyCharacter",
                "name": "everyCharacter",
                "label": "everyCharacter",
                "role": "waist",
                "decl": "UpperTheory.FinalTheorems.everyCharacter",
                "target": "UpperTheory.FinalTheorems.everyCharacter",
                "subtree_size": ev_sz,
                "pct_live": _pct(ev_sz),
                "depth": rh_rows["UpperTheory.FinalTheorems.everyCharacter"][1],
                "idom": rh_rows["UpperTheory.FinalTheorems.everyCharacter"][2],
                "note": "Modus ponens: Row0b(IsRecT) -> EveryCharacter",
                "description": "Modus ponens: Row0b(IsRecT) -> EveryCharacter",
                "circuit_mode": "theorem",
                "circuit_target": "UpperTheory.FinalTheorems.everyCharacter",
            },
            {
                "id": "pillar_b",
                "name": "Pillar B — Galois Representations (Row0b)",
                "label": "Pillar B",
                "role": "pillar",
                "decl": "UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter",
                "target": "UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter",
                "subtree_size": b_sz,
                "pct_live": _pct(b_sz),
                "depth": rh_rows["UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter"][1],
                "idom": rh_rows["UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter"][2],
                "note": "Unconditional l-adic Galois representations for polarized cuspidal automorphic reps",
                "description": "Unconditional l-adic Galois representations for polarized cuspidal automorphic reps",
                "circuit_mode": "theorem",
                "circuit_target": "UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter",
            },
            {
                "id": "everyCharacter_of_row",
                "name": "everyCharacter_of_row",
                "label": "everyCharacter_of_row",
                "role": "spine",
                "decl": "UpperTheory.FinalTheorems.everyCharacter_of_row",
                "target": "UpperTheory.FinalTheorems.everyCharacter_of_row",
                "subtree_size": row_sz,
                "pct_live": _pct(row_sz),
                "depth": rh_rows["UpperTheory.FinalTheorems.everyCharacter_of_row"][1],
                "idom": rh_rows["UpperTheory.FinalTheorems.everyCharacter_of_row"][2],
                "note": "Packs Row0b into OpenLiteratureStatements and applies VWin",
                "description": "Packs Row0b into OpenLiteratureStatements and applies VWin",
                "circuit_mode": "theorem",
                "circuit_target": "UpperTheory.FinalTheorems.everyCharacter_of_row",
            },
            {
                "id": "pillar_c",
                "name": "Pillar C — Window / Continuous Sha^1 (VWin)",
                "label": "Pillar C",
                "role": "pillar",
                "decl": "UpperTheory.One.vwin_of_row",
                "target": "UpperTheory.One.vwin_of_row",
                "subtree_size": c_sz,
                "pct_live": _pct(c_sz),
                "depth": rh_rows["UpperTheory.One.vwin_of_row"][1],
                "idom": rh_rows["UpperTheory.One.vwin_of_row"][2],
                "note": "Windowed continuous Galois cohomology Sha^1_Sl bound",
                "description": "Windowed continuous Galois cohomology Sha^1_Sl bound",
                "circuit_mode": "theorem",
                "circuit_target": "UpperTheory.One.vwin_of_row",
            },
            {
                "id": "every_character_of_literature_of_vWin",
                "name": "every_character_of_literature_of_vWin",
                "label": "lit_vWin",
                "role": "spine",
                "decl": "UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin",
                "target": "UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin",
                "subtree_size": lit_vw_sz,
                "pct_live": _pct(lit_vw_sz),
                "depth": rh_rows["UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin"][1],
                "idom": rh_rows["UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin"][2],
                "note": "Integrates Pillar A, Pillar D, and classical geometry subtrees",
                "description": "Integrates Pillar A, Pillar D, and classical geometry subtrees",
                "circuit_mode": None,
                "circuit_target": None,
            },
            {
                "id": "pillar_a",
                "name": "Pillar A — Theta Integrals & HypsAlt",
                "label": "Pillar A",
                "role": "pillar",
                "decl": "UpperTheory.Lit.every_character_of_theta_integrals_local_matching",
                "target": "UpperTheory.Lit.every_character_of_theta_integrals_local_matching",
                "subtree_size": a_sz,
                "pct_live": _pct(a_sz),
                "depth": rh_rows["UpperTheory.Lit.every_character_of_theta_integrals_local_matching"][1],
                "idom": rh_rows["UpperTheory.Lit.every_character_of_theta_integrals_local_matching"][2],
                "note": "Definite-side HypsAlt producer + windowed Landau zero-free consumer",
                "description": "Definite-side HypsAlt producer + windowed Landau zero-free consumer",
                "circuit_mode": "theorem",
                "circuit_target": "UpperTheory.Lit.every_character_of_theta_integrals_local_matching",
            },
            {
                "id": "pillar_d",
                "name": "Pillar D — Arakelov Covolume Bounds",
                "label": "Pillar D",
                "role": "pillar",
                "decl": "SelfIntersectionVolumeEstimates.topCovolSlim2_use_alt_alt",
                "target": "SelfIntersectionVolumeEstimates.topCovolSlim2_use_alt_alt",
                "subtree_size": d_sz,
                "pct_live": _pct(d_sz),
                "depth": rh_rows["SelfIntersectionVolumeEstimates.topCovolSlim2_use_alt_alt"][1],
                "idom": rh_rows["SelfIntersectionVolumeEstimates.topCovolSlim2_use_alt_alt"][2],
                "note": "Moriwaki bigness, Hilbert-Samuel, and covering covolume lower bounds",
                "description": "Moriwaki bigness, Hilbert-Samuel, and covering covolume lower bounds",
                "circuit_mode": "theorem",
                "circuit_target": "SelfIntersectionVolumeEstimates.topCovolSlim2_use_alt_alt",
            },
            {
                "id": "lit_residual",
                "name": "Literature & Classical Geometry Subtrees",
                "label": "Literature residual",
                "role": "residual",
                "decl": None,
                "target": None,
                "subtree_size": lit_res_sz,
                "pct_live": _pct(lit_res_sz),
                "depth": 4,
                "idom": "UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin",
                "note": "Toroidal compactification, resolution of singularities, theta/published libraries",
                "description": "Toroidal compactification, resolution of singularities, theta/published libraries",
                "circuit_mode": None,
                "circuit_target": None,
            },
            {
                "id": "row_siblings",
                "name": "Shared Row-Side Siblings",
                "label": "Row siblings",
                "role": "shared",
                "decl": None,
                "target": None,
                "subtree_size": row_sib_sz,
                "pct_live": _pct(row_sib_sz),
                "depth": 3,
                "idom": "UpperTheory.FinalTheorems.everyCharacter_of_row",
                "note": "Shared between Pillar C and literature side (globalEulerChar, abelianDeRham, ...)",
                "description": "Shared between Pillar C and literature side (globalEulerChar, abelianDeRham, ...)",
                "circuit_mode": None,
                "circuit_target": None,
            },
            {
                "id": "shared_diamond",
                "name": "Shared Diamond (Pillar B ∩ Row)",
                "label": "Shared diamond",
                "role": "diamond",
                "decl": None,
                "target": None,
                "subtree_size": dia_sz,
                "pct_live": _pct(dia_sz),
                "depth": 2,
                "idom": "UpperTheory.FinalTheorems.everyCharacter",
                "note": "100% reachable from both Pillar B and everyCharacter_of_row",
                "description": "100% reachable from both Pillar B and everyCharacter_of_row",
                "circuit_mode": None,
                "circuit_target": None,
            },
        ]

    # Generic project dominator hierarchy
    out: List[Dict[str, Any]] = []
    rows = conn.execute(
        "SELECT d.name, d.kind, dm.subtree_size, dm.depth, dp.name "
        "FROM dom dm "
        "JOIN decls d ON d.id = dm.decl_id "
        "LEFT JOIN decls dp ON dp.id = dm.idom "
        "WHERE dm.tree_id = ? "
        "ORDER BY dm.subtree_size DESC, dm.depth ASC, d.id ASC LIMIT 12",
        (tid,),
    ).fetchall()
    for name, kind, sub, depth, idom in rows:
        sub_i = int(sub)
        note_s = f"{kind} (dom={sub_i:,}, depth={depth})"
        out.append({
            "id": re.sub(r"[^A-Za-z0-9_]+", "_", str(name)).strip("_") or "node",
            "name": str(name),
            "label": _short_decl_name(str(name)),
            "role": "root" if int(depth) == 0 else "pillar",
            "decl": str(name),
            "target": str(name),
            "subtree_size": sub_i,
            "pct_live": _pct(sub_i),
            "depth": int(depth),
            "idom": str(idom) if idom is not None else None,
            "note": note_s,
            "description": note_s,
            "circuit_mode": "bundle" if kind == "inductive" else "theorem",
            "circuit_target": str(name),
        })
    if macro_payload and (macro_payload.get("stats") or {}).get("shared_diamond_decls"):
        dsz = int(macro_payload["stats"]["shared_diamond_decls"])
        note_d = "Shared subgraph reached across >= 2 major branches"
        out.append({
            "id": "shared_diamond",
            "name": "Shared Diamond",
            "label": "Shared diamond",
            "role": "diamond",
            "decl": None,
            "target": None,
            "subtree_size": dsz,
            "pct_live": _pct(dsz),
            "depth": 1,
            "idom": None,
            "note": note_d,
            "description": note_d,
            "circuit_mode": None,
            "circuit_target": None,
        })
    return out


def _select_bundle_targets(
    conn: sqlite3.Connection,
    kernel_db: str,
    src_root: Optional[str],
    *,
    max_bundles: int,
    demo_mode: bool,
) -> List[str]:
    if max_bundles <= 0:
        return []
    total_decls = int(conn.execute("SELECT COUNT(*) FROM decls").fetchone()[0])
    has_dm = (
        conn.execute("SELECT 1 FROM sqlite_master WHERE type='table' AND name='decl_module'").fetchone()
        is not None
    )
    selected: List[str] = []
    seen: Set[str] = set()

    def _add_fqn(fqn: str) -> None:
        if fqn and fqn not in seen and len(selected) < max_bundles:
            seen.add(fqn)
            selected.append(fqn)

    # 1. Curated showcase first (gracefully skipped when absent)
    for nm in CURATED_BUNDLE_SHOWCASE:
        if len(selected) >= max_bundles:
            break
        res = _resolve_preferred_decl(conn, nm, preferred_kinds=("inductive", "def"))
        if res is not None:
            _add_fqn(res[1])

    # 2. Small / demo corpus: include all live project inductives
    if demo_mode or total_decls <= 5_000:
        if has_dm:
            rows = conn.execute(
                "SELECT d.name FROM decls d JOIN decl_module dm ON dm.decl_id = d.id "
                "WHERE d.kind = 'inductive' AND d.live_mask != 0 "
                "ORDER BY d.fan_in DESC, d.id ASC"
            ).fetchall()
        else:
            rows = conn.execute(
                "SELECT name FROM decls WHERE kind = 'inductive' AND live_mask != 0 "
                "ORDER BY fan_in DESC, id ASC"
            ).fetchall()
        for (nm,) in rows:
            _add_fqn(str(nm))
        return selected[:max_bundles]

    # 3. Large DB: merge ranked unread bundles (`bundles.run_bundles`) + highest fan_in project inductives
    if len(selected) < max_bundles:
        try:
            import bundles as _bundles
            for sort_mode in ("dom", "cone"):
                if len(selected) >= max_bundles:
                    break
                brep = _bundles.run_bundles(
                    kernel_db_path=kernel_db,
                    src_root=src_root if (src_root and os.path.isdir(src_root)) else None,
                    top=max(40, max_bundles),
                    sort_by=sort_mode,
                )
                for b in brep.get("bundles") or []:
                    _add_fqn(str(b.get("name") or ""))
        except Exception:
            pass

    if len(selected) < max_bundles:
        if has_dm:
            q = (
                "SELECT d.name FROM decls d JOIN decl_module dm ON dm.decl_id = d.id "
                "WHERE d.kind = 'inductive' AND d.live_mask != 0 "
                "ORDER BY d.fan_in DESC, d.id ASC LIMIT ?"
            )
        else:
            q = (
                "SELECT name FROM decls WHERE kind = 'inductive' AND live_mask != 0 "
                "ORDER BY fan_in DESC, id ASC LIMIT ?"
            )
        for (nm,) in conn.execute(q, (max_bundles * 3,)).fetchall():
            _add_fqn(str(nm))
            if len(selected) >= max_bundles:
                break

    return selected[:max_bundles]


def _select_theorem_targets(
    conn: sqlite3.Connection,
    *,
    max_theorems: int,
    demo_mode: bool,
) -> List[Tuple[str, int]]:
    if max_theorems <= 0:
        return []
    total_decls = int(conn.execute("SELECT COUNT(*) FROM decls").fetchone()[0])
    has_dm = (
        conn.execute("SELECT 1 FROM sqlite_master WHERE type='table' AND name='decl_module'").fetchone()
        is not None
    )
    has_dom = (
        conn.execute("SELECT 1 FROM sqlite_master WHERE type='table' AND name='dom'").fetchone()
        is not None
    )
    tid = 0
    if has_dom:
        trow = conn.execute("SELECT id FROM dom_trees WHERE label='ALL'").fetchone()
        if trow is None:
            trow = conn.execute("SELECT id FROM dom_trees ORDER BY id LIMIT 1").fetchone()
        if trow is not None:
            tid = int(trow[0])

    import circuit as _circuit
    selected: List[Tuple[str, int]] = []
    seen: Set[str] = set()

    def _add(fqn: str, dom_sz: int) -> None:
        if fqn and fqn not in seen and len(selected) < max_theorems:
            seen.add(fqn)
            selected.append((fqn, int(dom_sz)))

    for nm in CURATED_THEOREM_SHOWCASE:
        if len(selected) >= max_theorems:
            break
        res = _resolve_preferred_decl(conn, nm, preferred_kinds=("thm", "def"))
        if res is not None:
            _add(res[1], res[5])

    if demo_mode or total_decls <= 5_000:
        if has_dm and has_dom:
            q = (
                "SELECT d.name, COALESCE(dm_tree.subtree_size, 0) AS sub "
                "FROM decls d JOIN decl_module dm ON dm.decl_id = d.id "
                "LEFT JOIN dom dm_tree ON dm_tree.decl_id = d.id AND dm_tree.tree_id = ? "
                "WHERE d.live_mask != 0 AND d.kind IN ('thm', 'def') "
                "ORDER BY sub DESC, d.fan_in DESC, d.id ASC"
            )
            rows = conn.execute(q, (tid,)).fetchall()
        elif has_dm:
            rows = conn.execute(
                "SELECT d.name, 0 FROM decls d JOIN decl_module dm ON dm.decl_id = d.id "
                "WHERE d.live_mask != 0 AND d.kind IN ('thm', 'def') "
                "ORDER BY d.fan_in DESC, d.id ASC"
            ).fetchall()
        else:
            rows = conn.execute(
                "SELECT name, 0 FROM decls WHERE live_mask != 0 AND kind IN ('thm', 'def') "
                "ORDER BY fan_in DESC, id ASC"
            ).fetchall()
        for nm, sub in rows:
            if not _circuit._is_aux_name(str(nm)):
                _add(str(nm), int(sub))
        return selected[:max_theorems]

    if len(selected) < max_theorems:
        if has_dm and has_dom:
            rows = conn.execute(
                "SELECT d.name, dm_tree.subtree_size "
                "FROM dom dm_tree "
                "JOIN decls d ON d.id = dm_tree.decl_id "
                "JOIN decl_module dm ON dm.decl_id = d.id "
                "WHERE dm_tree.tree_id = ? AND d.live_mask != 0 AND d.kind IN ('thm', 'def') "
                "ORDER BY dm_tree.subtree_size DESC, d.id ASC LIMIT ?",
                (tid, max_theorems * 3),
            ).fetchall()
        elif has_dom:
            rows = conn.execute(
                "SELECT d.name, dm_tree.subtree_size "
                "FROM dom dm_tree JOIN decls d ON d.id = dm_tree.decl_id "
                "WHERE dm_tree.tree_id = ? AND d.live_mask != 0 AND d.kind IN ('thm', 'def') "
                "ORDER BY dm_tree.subtree_size DESC, d.id ASC LIMIT ?",
                (tid, max_theorems * 3),
            ).fetchall()
        else:
            rows = conn.execute(
                "SELECT name, 0 FROM decls WHERE live_mask != 0 AND kind IN ('thm', 'def') "
                "ORDER BY fan_in DESC, id ASC LIMIT ?",
                (max_theorems * 3,),
            ).fetchall()
        for nm, sub in rows:
            s_nm = str(nm)
            if not _circuit._is_aux_name(s_nm):
                _add(s_nm, int(sub))
                if len(selected) >= max_theorems:
                    break

    return selected[:max_theorems]


def _bundle_badge_text(payload: Dict[str, Any]) -> str:
    st = payload.get("stats") or {}
    dropped = int(st.get("consumers_dropped_input") or 0)
    cons = int(st.get("consumers_total") or 0)
    cond = int(st.get("conditional_prop_fields") or 0)
    t_slots = int(st.get("literal_true_fields") or 0)
    fields = int(st.get("total_fields") or 0)
    if dropped > 0:
        return f"{dropped}/{cons} dropped"
    if t_slots > 0:
        return f"{t_slots} True stub"
    if cond > 0:
        return f"{cond} cond · {fields} fields"
    return f"{fields} fields · {cons} cons"


def _theorem_badge_text(payload: Dict[str, Any], dom_sz: int) -> str:
    st = payload.get("stats") or {}
    dropped = int(st.get("binders_dropped") or 0)
    steps = int(st.get("steps_count") or 0)
    badges = ((payload.get("meta") or {}).get("semantic_badges") or [])
    for b in badges:
        if b.get("label") == "else 0":
            return "else 0"
    if dropped > 0:
        return f"{dropped} dropped"
    if dom_sz >= 1_000_000:
        return f"dom {dom_sz / 1_000_000:.2f}M"
    if dom_sz >= 1_000:
        return f"dom {dom_sz:,}"
    return f"{steps} steps"


def _load_decl_line_lookup(
    *,
    leanre_db: Optional[str],
    src_root: Optional[str],
    demo_mode: bool,
) -> Tuple[Dict[Tuple[str, str], int], Dict[str, int]]:
    by_name_mod: Dict[Tuple[str, str], int] = {}
    by_name: Dict[str, int] = {}
    if leanre_db and os.path.isfile(leanre_db) and not os.path.islink(leanre_db):
        lconn = _open_ro(leanre_db)
        try:
            for nm, mod, ln in lconn.execute("SELECT name, module, line_no FROM declarations"):
                s_nm = str(nm)
                s_mod = str(mod or "")
                i_ln = int(ln or 0)
                if i_ln > 0:
                    by_name_mod[(s_nm, s_mod)] = i_ln
                    if s_nm not in by_name:
                        by_name[s_nm] = i_ln
        finally:
            lconn.close()
        return by_name_mod, by_name

    if src_root and os.path.isdir(src_root) and (demo_mode or sum(len(fs) for _, _, fs in os.walk(src_root)) <= 1500):
        try:
            import kernel as _kernel
            src_exact, _by_ml, _nfiles = _kernel.scan_source_decl_modules(src_root, workers=1)
            for nm, (mod, ln) in src_exact.items():
                if ln > 0:
                    by_name_mod[(nm, mod)] = ln
                    by_name.setdefault(nm, ln)
        except Exception:
            pass
    return by_name_mod, by_name


def _build_search_shards(
    split_dir: str,
    *,
    conn: Optional[sqlite3.Connection],
    search_limit: int,
    findings: Sequence[Dict[str, Any]],
    dossiers: Sequence[Dict[str, Any]],
    research: Sequence[Dict[str, Any]],
    blueprints: Sequence[Dict[str, Any]],
    bundle_entries: Sequence[Dict[str, Any]],
    theorem_entries: Sequence[Dict[str, Any]],
    by_name_mod_line: Dict[Tuple[str, str], int],
    by_name_line: Dict[str, int],
    max_shard_bytes: int = MAX_SEARCH_SHARD_BYTES,
    max_total_bytes: int = MAX_SEARCH_TOTAL_BYTES,
) -> Dict[str, Any]:
    circuit_by_name: Dict[str, str] = {}
    for b in bundle_entries:
        circuit_by_name[b["name"]] = b["path"]
    for t in theorem_entries:
        circuit_by_name.setdefault(t["name"], t["path"])

    bp_by_root: Dict[str, str] = {}
    for bp in blueprints:
        if bp.get("root"):
            bp_by_root.setdefault(str(bp["root"]), str(bp["id"]))

    seen_decls: Set[str] = set()
    high_priority_rows: List[Tuple[str, List[Any]]] = []  # (bucket, entry)

    def _add_doc_entry(bucket_text: str, entry: List[Any]) -> None:
        high_priority_rows.append((_search_prefix_bucket(bucket_text), entry))

    for f_item in findings:
        _add_doc_entry(f_item["slug"], [f_item["title"], "finding", 0, 1, f_item["path"], None, None, f_item["slug"]])
        b_t = _search_prefix_bucket(f_item["title"])
        if b_t != _search_prefix_bucket(f_item["slug"]):
            _add_doc_entry(f_item["title"], [f_item["title"], "finding", 0, 1, f_item["path"], None, None, f_item["slug"]])

    for d_item in dossiers:
        _add_doc_entry(d_item["slug"], [d_item["title"], "dossier", 0, 1, d_item["path"], None, None, d_item["slug"]])
        b_t = _search_prefix_bucket(d_item["title"])
        if b_t != _search_prefix_bucket(d_item["slug"]):
            _add_doc_entry(d_item["title"], [d_item["title"], "dossier", 0, 1, d_item["path"], None, None, d_item["slug"]])

    for r_item in research:
        _add_doc_entry(r_item["slug"], [r_item["title"], "research", 0, 1, r_item["path"], None, None, r_item["slug"]])

    for bp in blueprints:
        rc = circuit_by_name.get(str(bp.get("root") or ""))
        _add_doc_entry(bp["id"], [bp["title"], "blueprint", int(bp["node_count"]), 1, bp["path"], None, rc, bp["id"]])
        b_t = _search_prefix_bucket(bp["title"])
        if b_t != _search_prefix_bucket(bp["id"]):
            _add_doc_entry(bp["title"], [bp["title"], "blueprint", int(bp["node_count"]), 1, bp["path"], None, rc, bp["id"]])

    decl_entries: List[Tuple[bool, List[Any]]] = []  # (is_pinned, entry)
    if conn is not None and search_limit > 0:
        has_dm = (
            conn.execute("SELECT 1 FROM sqlite_master WHERE type='table' AND name='decl_module'").fetchone()
            is not None
        )
        has_dom = (
            conn.execute("SELECT 1 FROM sqlite_master WHERE type='table' AND name='dom'").fetchone()
            is not None
        )
        tid = 0
        if has_dom:
            trow = conn.execute("SELECT id FROM dom_trees WHERE label='ALL'").fetchone()
            if trow is None:
                trow = conn.execute("SELECT id FROM dom_trees ORDER BY id LIMIT 1").fetchone()
            if trow is not None:
                tid = int(trow[0])

        def _row_to_entry(name: str, kind: str, dom_sz: int, live_m: int, mod: Optional[str]) -> List[Any]:
            s_mod = str(mod or "")
            ln = by_name_mod_line.get((name, s_mod)) or by_name_line.get(name)
            return [
                name,
                kind,
                int(dom_sz),
                1 if int(live_m) != 0 else 0,
                s_mod,
                ln,
                circuit_by_name.get(name),
                bp_by_root.get(name),
            ]

        # Ensure all pre-rendered circuit targets are present
        pre_names = sorted(circuit_by_name.keys())
        for i in range(0, len(pre_names), 400):
            chunk = pre_names[i : i + 400]
            ph = ",".join("?" for _ in chunk)
            if has_dm and has_dom:
                q = (
                    f"SELECT d.name, d.kind, COALESCE(dm_tree.subtree_size, 0), d.live_mask, dm.module "
                    f"FROM decls d LEFT JOIN decl_module dm ON dm.decl_id = d.id "
                    f"LEFT JOIN dom dm_tree ON dm_tree.decl_id = d.id AND dm_tree.tree_id = ? "
                    f"WHERE d.name IN ({ph})"
                )
                qrows = conn.execute(q, [tid, *chunk]).fetchall()
            elif has_dm:
                q = (
                    f"SELECT d.name, d.kind, 0, d.live_mask, dm.module "
                    f"FROM decls d LEFT JOIN decl_module dm ON dm.decl_id = d.id "
                    f"WHERE d.name IN ({ph})"
                )
                qrows = conn.execute(q, chunk).fetchall()
            else:
                q = f"SELECT name, kind, 0, live_mask, '' FROM decls WHERE name IN ({ph})"
                qrows = conn.execute(q, chunk).fetchall()
            for r in qrows:
                nm = str(r[0])
                if nm not in seen_decls:
                    seen_decls.add(nm)
                    decl_entries.append((True, _row_to_entry(nm, str(r[1]), int(r[2]), int(r[3]), r[4])))

        # Ensure ALL dom >= 1,000 declarations are present
        if has_dom:
            if has_dm:
                dom1k_rows = conn.execute(
                    "SELECT d.name, d.kind, dm_tree.subtree_size, d.live_mask, dm.module "
                    "FROM dom dm_tree JOIN decls d ON d.id = dm_tree.decl_id "
                    "LEFT JOIN decl_module dm ON dm.decl_id = d.id "
                    "WHERE dm_tree.tree_id = ? AND dm_tree.subtree_size >= 1000 "
                    "ORDER BY dm_tree.subtree_size DESC, d.id ASC",
                    (tid,),
                ).fetchall()
            else:
                dom1k_rows = conn.execute(
                    "SELECT d.name, d.kind, dm_tree.subtree_size, d.live_mask, '' "
                    "FROM dom dm_tree JOIN decls d ON d.id = dm_tree.decl_id "
                    "WHERE dm_tree.tree_id = ? AND dm_tree.subtree_size >= 1000 "
                    "ORDER BY dm_tree.subtree_size DESC, d.id ASC",
                    (tid,),
                ).fetchall()
            for r in dom1k_rows:
                nm = str(r[0])
                if nm not in seen_decls:
                    seen_decls.add(nm)
                    decl_entries.append((True, _row_to_entry(nm, str(r[1]), int(r[2]), int(r[3]), r[4])))

        # Fill remaining up to search_limit ordered by dom DESC, fan_in DESC
        rem = max(0, search_limit - len(decl_entries))
        if rem > 0:
            fetch_lim = rem + len(seen_decls) + 50
            if has_dm and has_dom:
                top_rows = conn.execute(
                    "SELECT d.name, d.kind, COALESCE(dm_tree.subtree_size, 0) AS sub, d.live_mask, dm.module "
                    "FROM decls d JOIN decl_module dm ON dm.decl_id = d.id "
                    "LEFT JOIN dom dm_tree ON dm_tree.decl_id = d.id AND dm_tree.tree_id = ? "
                    "WHERE d.live_mask != 0 "
                    "ORDER BY sub DESC, d.fan_in DESC, d.id ASC LIMIT ?",
                    (tid, fetch_lim),
                ).fetchall()
            elif has_dm:
                top_rows = conn.execute(
                    "SELECT d.name, d.kind, 0, d.live_mask, dm.module "
                    "FROM decls d JOIN decl_module dm ON dm.decl_id = d.id "
                    "WHERE d.live_mask != 0 ORDER BY d.fan_in DESC, d.id ASC LIMIT ?",
                    (fetch_lim,),
                ).fetchall()
            elif has_dom:
                top_rows = conn.execute(
                    "SELECT d.name, d.kind, COALESCE(dm_tree.subtree_size, 0) AS sub, d.live_mask, '' "
                    "FROM decls d LEFT JOIN dom dm_tree ON dm_tree.decl_id = d.id AND dm_tree.tree_id = ? "
                    "WHERE d.live_mask != 0 ORDER BY sub DESC, d.fan_in DESC, d.id ASC LIMIT ?",
                    (tid, fetch_lim),
                ).fetchall()
            else:
                top_rows = conn.execute(
                    "SELECT name, kind, 0, live_mask, '' FROM decls WHERE live_mask != 0 "
                    "ORDER BY fan_in DESC, id ASC LIMIT ?",
                    (fetch_lim,),
                ).fetchall()
            for r in top_rows:
                if len(decl_entries) >= search_limit:
                    break
                nm = str(r[0])
                if nm not in seen_decls:
                    seen_decls.add(nm)
                    decl_entries.append((False, _row_to_entry(nm, str(r[1]), int(r[2]), int(r[3]), r[4])))

    # Bucket into 2-char leaf-prefix shards with optional per-shard `mod_prefixes` compression
    # to keep every shard < 150 KB and all shards combined < 4 MB.
    raw_shards: Dict[str, List[Tuple[bool, List[Any]]]] = collections.defaultdict(list)
    for bucket, entry in high_priority_rows:
        raw_shards[bucket].append((True, entry))
    for is_pinned, entry in decl_entries:
        short = str(entry[0]).rsplit(".", 1)[-1]
        bucket = _search_prefix_bucket(short)
        raw_shards[bucket].append((is_pinned, entry))

    def _pack_shard(entries: List[List[Any]]) -> Any:
        # Try 3-segment (or 2-segment) module prefix table when entries repeat common prefixes
        if len(entries) < 8:
            return entries
        pref_counts: collections.Counter[str] = collections.Counter()
        for e in entries:
            mod_s = str(e[4] or "")
            if "." in mod_s and not mod_s.startswith("data/"):
                parts = mod_s.split(".")
                if len(parts) >= 3:
                    pref_counts[".".join(parts[:3])] += 1
                elif len(parts) == 2:
                    pref_counts[parts[0]] += 1
        common = sorted(p for p, c in pref_counts.items() if c >= 2)
        if not common:
            return entries
        pref_idx = {p: idx for idx, p in enumerate(common)}
        packed_entries: List[List[Any]] = []
        for e in entries:
            mod_s = str(e[4] or "")
            new_mod: Any = mod_s
            if "." in mod_s and not mod_s.startswith("data/"):
                parts = mod_s.split(".")
                p3 = ".".join(parts[:3]) if len(parts) >= 3 else parts[0]
                if p3 in pref_idx:
                    rest = ".".join(parts[3:]) if len(parts) >= 3 else ".".join(parts[1:])
                    new_mod = f"{pref_idx[p3]}:{rest}" if rest else pref_idx[p3]
            packed_entries.append([e[0], e[1], e[2], e[3], new_mod, e[5], e[6], e[7]])
        packed_obj = {"mod_prefixes": common, "entries": packed_entries}
        raw_sz = len(json.dumps(entries, ensure_ascii=False, separators=(",", ":")))
        pak_sz = len(json.dumps(packed_obj, ensure_ascii=False, separators=(",", ":")))
        return packed_obj if pak_sz + 64 < raw_sz else entries

    shard_keys = sorted(raw_shards.keys())
    # Sort each bucket with pinned + higher-dom first, then pack and enforce per-shard + total caps
    prepared: List[Tuple[str, Any, int, int]] = []
    running_total_bytes = 0
    total_entries = 0

    # Pass 1: fit pinned items first across all shards, then non-pinned while under total budget
    pinned_only: Dict[str, List[List[Any]]] = {}
    non_pinned_pool: List[Tuple[int, str, List[Any]]] = []
    for sk in shard_keys:
        p_list = [e for pin, e in raw_shards[sk] if pin]
        np_list = [e for pin, e in raw_shards[sk] if not pin]
        p_list.sort(key=lambda e: (-int(e[2] or 0), str(e[0])))
        pinned_only[sk] = p_list
        for e in np_list:
            non_pinned_pool.append((-int(e[2] or 0), sk, e))
    non_pinned_pool.sort(key=lambda t: (t[0], t[1], str(t[2][0])))

    shard_lists: Dict[str, List[List[Any]]] = {sk: list(pinned_only[sk]) for sk in shard_keys}
    pinned_counts: Dict[str, int] = {sk: len(pinned_only[sk]) for sk in shard_keys}
    shard_est: Dict[str, int] = {}
    shard_adds_since_pack: Dict[str, int] = collections.Counter()

    def _exact_shard_bytes(rows_sk: List[List[Any]]) -> int:
        if not rows_sk:
            return 2
        return len(json.dumps(_pack_shard(rows_sk), ensure_ascii=False, separators=(",", ":")).encode("utf-8"))

    for sk in shard_keys:
        sz = _exact_shard_bytes(shard_lists[sk])
        shard_est[sk] = sz
        running_total_bytes += sz
        total_entries += len(shard_lists[sk])

    rebalanced = False
    for _neg_dom, sk, entry in non_pinned_pool:
        if shard_est[sk] >= max_shard_bytes:
            continue
        est_row = len(json.dumps(entry, ensure_ascii=False, separators=(",", ":")).encode("utf-8")) + 1
        if shard_est[sk] + est_row > max_shard_bytes or shard_adds_since_pack[sk] >= 40:
            cand_sz = _exact_shard_bytes(shard_lists[sk] + [entry])
            if cand_sz > max_shard_bytes:
                shard_est[sk] = max(shard_est[sk], max_shard_bytes)
                continue
            delta = cand_sz - shard_est[sk]
            if running_total_bytes + delta > max_total_bytes:
                if not rebalanced:
                    rebalanced = True
                    for rsk in shard_keys:
                        shard_est[rsk] = _exact_shard_bytes(shard_lists[rsk])
                        shard_adds_since_pack[rsk] = 0
                    running_total_bytes = sum(shard_est.values())
                    cand_sz = _exact_shard_bytes(shard_lists[sk] + [entry])
                    delta = cand_sz - shard_est[sk]
                if running_total_bytes + delta > max_total_bytes:
                    continue
            shard_lists[sk].append(entry)
            shard_est[sk] = cand_sz
            shard_adds_since_pack[sk] = 0
            running_total_bytes += delta
            total_entries += 1
        else:
            if running_total_bytes + est_row > max_total_bytes:
                if not rebalanced:
                    rebalanced = True
                    for rsk in shard_keys:
                        shard_est[rsk] = _exact_shard_bytes(shard_lists[rsk])
                        shard_adds_since_pack[rsk] = 0
                    running_total_bytes = sum(shard_est.values())
                if running_total_bytes + est_row > max_total_bytes:
                    cand_sz = _exact_shard_bytes(shard_lists[sk] + [entry])
                    delta = cand_sz - shard_est[sk]
                    if running_total_bytes + delta > max_total_bytes:
                        break
                    shard_lists[sk].append(entry)
                    shard_est[sk] = cand_sz
                    shard_adds_since_pack[sk] = 0
                    running_total_bytes += delta
                    total_entries += 1
                    continue
            shard_lists[sk].append(entry)
            shard_est[sk] += est_row
            shard_adds_since_pack[sk] += 1
            running_total_bytes += est_row
            total_entries += 1

    final_shards: List[str] = []
    actual_total_bytes = 0
    actual_total_entries = 0
    for sk in shard_keys:
        rows_sk = shard_lists[sk]
        if not rows_sk:
            continue
        p_keep = pinned_counts.get(sk, 0)
        obj_sk = _pack_shard(rows_sk)
        raw_bytes = json.dumps(obj_sk, ensure_ascii=False, separators=(",", ":")).encode("utf-8")
        while len(raw_bytes) > max_shard_bytes and len(rows_sk) > p_keep:
            rows_sk.pop()
            obj_sk = _pack_shard(rows_sk)
            raw_bytes = json.dumps(obj_sk, ensure_ascii=False, separators=(",", ":")).encode("utf-8")
        rows_sk.sort(key=lambda e: (-int(e[2] or 0), str(e[0])))
        obj_sk = _pack_shard(rows_sk)
        nbytes = _safe_write_json(os.path.join(split_dir, "data", "search", f"{sk}.json"), obj_sk)
        actual_total_bytes += nbytes
        actual_total_entries += len(rows_sk)
        final_shards.append(sk)

    return {
        "shard_prefix_len": 2,
        "shard_template": "data/search/{prefix}.json",
        "bucket_mode": "leaf_prefix2",
        "bucket_key": "leaf",
        "total_entries": actual_total_entries,
        "total_bytes": actual_total_bytes,
        "shards": final_shards,
    }


def _copy_or_fallback_assets(split_dir: str, title: str) -> List[str]:
    copied: List[str] = []
    esc_title = html.escape(title, quote=True)
    for fn in ("index.html", "site.js", "site.css"):
        src = os.path.join(SITE_ASSETS_DIR, fn)
        dst = os.path.join(split_dir, fn)
        if os.path.isfile(src) and not os.path.islink(src):
            with open(src, "rb") as f:
                data = f.read()
            _safe_write_bytes(dst, data)
            copied.append(fn)
        elif fn == "index.html":
            _safe_write_text(dst, _FALLBACK_SPLIT_HTML.replace("__TITLE__", esc_title))
    _safe_write_bytes(os.path.join(split_dir, ".nojekyll"), b"")
    return copied


def _verify_split_dir_safety(split_dir: str) -> Dict[str, Any]:
    total_bytes = 0
    file_count = 0
    max_file_bytes = 0
    max_file_rel = ""
    for root, dirs, files in os.walk(split_dir, followlinks=False):
        dirs.sort()
        files.sort()
        for fn in files:
            full = os.path.join(root, fn)
            if os.path.islink(full):
                raise ValueError(f"Unexpected symlink inside split_dir: {full}")
            rel = os.path.relpath(full, split_dir).replace(os.sep, "/")
            if fn.endswith(".lean"):
                raise ValueError(f"Refusing exported raw .lean file inside split_dir: {rel}")
            sz = os.path.getsize(full)
            if sz > MAX_SPLIT_FILE_BYTES:
                raise ValueError(f"File exceeds 25 MB GitHub Pages limit ({sz:,} bytes): {rel}")
            total_bytes += sz
            file_count += 1
            if sz > max_file_bytes:
                max_file_bytes = sz
                max_file_rel = rel
            if fn.endswith((".json", ".md", ".html", ".js", ".css", ".svg")):
                with open(full, "r", encoding="utf-8", errors="replace") as f:
                    txt = f.read()
                m = _FORBIDDEN_HOST_PATH_RE.search(txt)
                if m:
                    raise ValueError(f"Workstation path {m.group(0)!r} leaked into exported file: {rel}")
    return {
        "total_bytes": total_bytes,
        "file_count": file_count,
        "max_file_bytes": max_file_bytes,
        "max_file_rel": max_file_rel,
    }


def export_split_site(
    split_dir: str,
    *,
    decomp_dir: Optional[str] = None,
    trim_report: Optional[str] = None,
    cluster_labels: Optional[str] = None,
    clusters_json: Optional[str] = None,
    tier1_summary: Optional[str] = None,
    tier2_summary: Optional[str] = None,
    portability: Optional[str] = None,
    benchmark: Optional[str] = None,
    atlas_summary: Optional[str] = None,
    kernel_db: Optional[str] = None,
    leanre_db: Optional[str] = None,
    src_root: Optional[str] = None,
    findings_dir: Optional[str] = None,
    analysis_dir: Optional[str] = None,
    research_dir: Optional[str] = None,
    flirt_dir: Optional[str] = None,
    config_path: Optional[str] = None,
    title: Optional[str] = None,
    repo_url: Optional[str] = None,
    pinned_commit: Optional[str] = None,
    src_prefix: Optional[str] = None,
    max_bundles: int = 60,
    max_theorems: int = 80,
    max_circuits: Optional[int] = None,
    search_limit: int = 30_000,
    demo_mode: bool = False,
) -> Dict[str, Any]:
    """Export a zero-CDN, lazy-sharded static site directory ready for GitHub Pages."""
    if os.path.islink(split_dir):
        raise ValueError(f"Refusing symlinked split_dir target: {split_dir}")
    os.makedirs(split_dir, exist_ok=True)

    # Resolve sibling paths when decomp_dir / flirt_dir are given
    resolved_trim = trim_report
    resolved_clusters_lbl = cluster_labels
    resolved_clusters = clusters_json
    resolved_t1 = tier1_summary
    resolved_t2 = tier2_summary
    resolved_port = portability
    resolved_bench = benchmark
    resolved_atlas = atlas_summary
    resolved_flirt_dir = flirt_dir
    if decomp_dir and os.path.isdir(decomp_dir):
        parent_out = os.path.dirname(os.path.abspath(decomp_dir))
        if resolved_flirt_dir is None:
            cand_f = os.path.join(parent_out, "flirt")
            if os.path.isdir(cand_f):
                resolved_flirt_dir = cand_f
        if resolved_port is None:
            cand_p = os.path.join(parent_out, "portability_gems.json")
            if os.path.isfile(cand_p) and not os.path.islink(cand_p):
                resolved_port = cand_p
        if resolved_bench is None:
            cand_b = os.path.join(parent_out, "xrepo_benchmark.json")
            if os.path.isfile(cand_b) and not os.path.islink(cand_b):
                resolved_bench = cand_b
        if resolved_atlas is None:
            cand_a = os.path.join(parent_out, "atlas_summary.json")
            if os.path.isfile(cand_a) and not os.path.islink(cand_a):
                resolved_atlas = cand_a
        if leanre_db is None:
            cand_ldb = os.path.join(parent_out, "leanre.db")
            if os.path.isfile(cand_ldb) and not os.path.islink(cand_ldb):
                leanre_db = cand_ldb

    if resolved_flirt_dir and os.path.isdir(resolved_flirt_dir):
        if resolved_clusters_lbl is None:
            p = os.path.join(resolved_flirt_dir, "cluster_labels_141.json")
            if os.path.isfile(p) and not os.path.islink(p):
                resolved_clusters_lbl = p
        if resolved_clusters is None:
            p = os.path.join(resolved_flirt_dir, "clusters.json")
            if os.path.isfile(p) and not os.path.islink(p):
                resolved_clusters = p
        if resolved_t1 is None:
            p = os.path.join(resolved_flirt_dir, "tier1_summary.json")
            if os.path.isfile(p) and not os.path.islink(p):
                resolved_t1 = p
        if resolved_t2 is None:
            p = os.path.join(resolved_flirt_dir, "tier2_summary.json")
            if os.path.isfile(p) and not os.path.islink(p):
                resolved_t2 = p

    # Resolve effective bundle/theorem circuit caps if --max-circuits was given
    eff_max_bundles = max(0, int(max_bundles))
    eff_max_theorems = max(0, int(max_theorems))
    if max_circuits is not None:
        mc = max(0, int(max_circuits))
        if mc == 0:
            eff_max_bundles = 0
            eff_max_theorems = 0
        elif eff_max_bundles + eff_max_theorems > mc:
            eff_max_bundles = min(eff_max_bundles, max(1 if mc >= 2 else 0, (mc * 3) // 7))
            eff_max_theorems = min(eff_max_theorems, max(0, mc - eff_max_bundles))

    meta_info = _resolve_repo_meta(
        config_path=config_path,
        src_root=src_root,
        kernel_db=kernel_db,
        decomp_dir=decomp_dir,
        demo_mode=demo_mode,
        title=title,
        repo_url_override=repo_url,
        pinned_commit_override=pinned_commit,
        src_prefix_override=src_prefix,
    )
    site_title = meta_info["title"]
    copied_assets = _copy_or_fallback_assets(split_dir, site_title)

    # Collect markdown docs & blueprints
    findings = _collect_markdown_docs(findings_dir, "findings", split_dir, is_findings=True)
    dossiers = _collect_markdown_docs(analysis_dir, "analysis", split_dir, is_dossiers=True)
    research = _collect_markdown_docs(research_dir, "research", split_dir)
    blueprints, discovered_trim = _collect_split_blueprints(decomp_dir, split_dir)
    if resolved_trim is None and discovered_trim is not None:
        resolved_trim = discovered_trim

    # Copy compact JSON assets (preserving original schemas)
    trim_doc: Optional[Dict[str, Any]] = None
    if resolved_trim and os.path.isfile(resolved_trim) and not os.path.islink(resolved_trim):
        with open(resolved_trim, "r", encoding="utf-8") as f:
            trim_doc = json.load(f)

    asset_paths = {
        "atlas": _copy_compact_json_asset(
            resolved_atlas, split_dir, "data/atlas_summary.json", transform=_strip_atlas_input_paths
        ),
        "portability": _copy_compact_json_asset(resolved_port, split_dir, "data/portability_gems.json"),
        "benchmark": _copy_compact_json_asset(resolved_bench, split_dir, "data/xrepo_benchmark.json"),
        "cluster_labels": _copy_compact_json_asset(resolved_clusters_lbl, split_dir, "data/flirt/cluster_labels_141.json"),
        "clusters": _copy_compact_json_asset(resolved_clusters, split_dir, "data/flirt/clusters.json"),
        "trim_report": _copy_compact_json_asset(resolved_trim, split_dir, "data/trim_report.json"),
        "tier1_summary": _copy_compact_json_asset(resolved_t1, split_dir, "data/flirt/tier1_summary.json"),
        "tier2_summary": _copy_compact_json_asset(resolved_t2, split_dir, "data/flirt/tier2_summary.json"),
    }
    if resolved_flirt_dir and os.path.isdir(resolved_flirt_dir):
        for fn in sorted(os.listdir(resolved_flirt_dir)):
            if fn.endswith(".json") and fn not in (
                "cluster_labels_141.json", "clusters.json", "tier1_summary.json", "tier2_summary.json"
            ):
                _copy_compact_json_asset(
                    os.path.join(resolved_flirt_dir, fn),
                    split_dir,
                    f"data/flirt/{fn}",
                )

    if not meta_info["pinned_commit"] and trim_doc and isinstance(trim_doc.get("pins"), dict):
        mc_val = trim_doc["pins"].get("mirror_commit")
        if mc_val:
            meta_info["pinned_commit"] = str(mc_val)

    # Kernel DB stats, overview pillars, circuits, and sharded search
    total_decls = 0
    live_decls = 0
    dead_decls = 0
    total_edges = 0
    total_files = 0
    total_lines = 0
    overview_pillars: List[Dict[str, Any]] = []
    macro_rel: Optional[str] = None
    bundle_entries: List[Dict[str, Any]] = []
    theorem_entries: List[Dict[str, Any]] = []

    kconn: Optional[sqlite3.Connection] = None
    try:
        if kernel_db:
            if os.path.islink(kernel_db):
                raise ValueError(f"Refusing symlinked kernel_db: {kernel_db}")
            kconn = _open_ro(kernel_db)
            total_decls = int(kconn.execute("SELECT COUNT(*) FROM decls").fetchone()[0])
            live_decls = int(kconn.execute("SELECT COUNT(*) FROM decls WHERE live_mask != 0").fetchone()[0])
            dead_decls = max(0, total_decls - live_decls)
            total_edges = int(kconn.execute("SELECT COUNT(*) FROM edges").fetchone()[0])

            import circuit as _circuit
            macro_raw = _circuit.build_macro_circuit(
                kernel_db_path=kernel_db,
                src_root=src_root if (src_root and os.path.isdir(src_root)) else None,
                portability_json=resolved_port,
            )
            macro_clean = _sanitize_circuit_payload(macro_raw, mode="macro")
            macro_svg_dark = _circuit.render_circuit_svg(macro_clean, theme="dark")
            macro_svg_light = _circuit.render_circuit_svg(macro_clean, theme="light")
            macro_rel = "data/circuits/macro.json"
            _safe_write_json(
                os.path.join(split_dir, macro_rel),
                {
                    "schema": macro_clean.get("schema", "leanre.circuit/1"),
                    "mode": "macro",
                    "name": None,
                    "payload": macro_clean,
                    "svg_dark": macro_svg_dark,
                    "svg_light": macro_svg_light,
                },
            )

            overview_pillars = _build_overview_pillars(
                kconn, live_decls=live_decls, macro_payload=macro_clean
            )

            bundle_targets = _select_bundle_targets(
                kconn,
                kernel_db,
                src_root,
                max_bundles=eff_max_bundles,
                demo_mode=demo_mode,
            )
            used_bundle_slugs: Set[str] = set()
            for fqn in bundle_targets:
                try:
                    raw_b = _circuit.build_bundle_circuit(
                        kernel_db_path=kernel_db,
                        target=fqn,
                        src_root=src_root if (src_root and os.path.isdir(src_root)) else None,
                        max_nodes=16,
                        exact_case=True,
                    )
                except Exception:
                    continue
                clean_b = _sanitize_circuit_payload(raw_b, mode="bundle")
                svg_d = _circuit.render_circuit_svg(clean_b, theme="dark")
                svg_l = _circuit.render_circuit_svg(clean_b, theme="light")
                slug = _safe_slug(clean_b.get("target") or fqn, used_bundle_slugs)
                rel_b = f"data/circuits/bundle/{slug}.json"
                _safe_write_json(
                    os.path.join(split_dir, rel_b),
                    {
                        "schema": clean_b.get("schema", "leanre.circuit/1"),
                        "mode": "bundle",
                        "name": clean_b.get("target") or fqn,
                        "payload": clean_b,
                        "svg_dark": svg_d,
                        "svg_light": svg_l,
                    },
                )
                st = clean_b.get("stats") or {}
                pins_b = clean_b.get("pins") or {}
                bundle_entries.append({
                    "name": str(clean_b.get("target") or fqn),
                    "short": _short_decl_name(str(clean_b.get("target") or fqn)),
                    "badge": _bundle_badge_text(clean_b),
                    "path": rel_b,
                    "producers": int(st.get("producers_total") or 0),
                    "consumers": int(st.get("consumers_total") or 0),
                    "dropped_consumers": int(st.get("consumers_dropped_input") or 0),
                    "fields": int(st.get("total_fields") or 0),
                    "cond_fields": int(st.get("conditional_prop_fields") or 0),
                    "true_fields": int(st.get("literal_true_fields") or 0),
                    "elapsed_s": float(pins_b.get("elapsed_seconds") or 0.0),
                })

            theorem_targets = _select_theorem_targets(
                kconn,
                max_theorems=eff_max_theorems,
                demo_mode=demo_mode,
            )
            used_thm_slugs: Set[str] = set()
            for fqn, dom_sz in theorem_targets:
                try:
                    raw_t = _circuit.build_theorem_circuit(
                        kernel_db_path=kernel_db,
                        decl=fqn,
                        src_root=src_root if (src_root and os.path.isdir(src_root)) else None,
                        max_nodes=32,
                        exact_case=True,
                    )
                except Exception:
                    continue
                clean_t = _sanitize_circuit_payload(raw_t, mode="theorem")
                svg_d = _circuit.render_circuit_svg(clean_t, theme="dark")
                svg_l = _circuit.render_circuit_svg(clean_t, theme="light")
                slug = _safe_slug(clean_t.get("target") or fqn, used_thm_slugs)
                rel_t = f"data/circuits/theorem/{slug}.json"
                _safe_write_json(
                    os.path.join(split_dir, rel_t),
                    {
                        "schema": clean_t.get("schema", "leanre.circuit/1"),
                        "mode": "theorem",
                        "name": clean_t.get("target") or fqn,
                        "payload": clean_t,
                        "svg_dark": svg_d,
                        "svg_light": svg_l,
                    },
                )
                st = clean_t.get("stats") or {}
                theorem_entries.append({
                    "name": str(clean_t.get("target") or fqn),
                    "short": _short_decl_name(str(clean_t.get("target") or fqn)),
                    "badge": _theorem_badge_text(clean_t, dom_sz),
                    "path": rel_t,
                    "dom": int(dom_sz),
                    "steps": int(st.get("steps_count") or 0),
                    "binders_used": int(st.get("binders_used") or 0),
                    "binders_dropped": int(st.get("binders_dropped") or 0),
                    "kind": str(st.get("decl_kind") or "thm"),
                })

        total_files, total_lines = _count_files_and_lines(
            leanre_db=leanre_db,
            src_root=src_root,
            trim_doc=trim_doc,
            kernel_conn=kconn,
        )

        by_nm_mod_ln, by_nm_ln = _load_decl_line_lookup(
            leanre_db=leanre_db,
            src_root=src_root,
            demo_mode=demo_mode,
        )
        search_meta = _build_search_shards(
            split_dir,
            conn=kconn,
            search_limit=max(0, int(search_limit)),
            findings=findings,
            dossiers=dossiers,
            research=research,
            blueprints=blueprints,
            bundle_entries=bundle_entries,
            theorem_entries=theorem_entries,
            by_name_mod_line=by_nm_mod_ln,
            by_name_line=by_nm_ln,
        )
    finally:
        if kconn is not None:
            kconn.close()

    generated_at = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    manifest: Dict[str, Any] = {
        "schema": SPLIT_MANIFEST_SCHEMA,
        "title": site_title,
        "repo_name": meta_info["repo_name"],
        "repo_url": meta_info["repo_url"],
        "pinned_commit": meta_info["pinned_commit"],
        "src_prefix": meta_info["src_prefix"],
        "generated_at": generated_at,
        "demo_mode": bool(demo_mode),
        "stats": {
            "total_decls": total_decls,
            "live_decls": live_decls,
            "dead_decls": dead_decls,
            "edges": total_edges,
            "total_files": total_files,
            "total_lines": total_lines,
            "blueprints_count": len(blueprints),
            "dossiers_count": len(dossiers),
            "findings_count": len(findings),
            "circuits_bundle_count": len(bundle_entries),
            "circuits_theorem_count": len(theorem_entries),
            "search_entries": search_meta["total_entries"],
            "search_shards": len(search_meta["shards"]),
        },
        "overview_pillars": overview_pillars,
        "findings": findings,
        "dossiers": dossiers,
        "research": research,
        "blueprints": blueprints,
        "circuits": {
            "macro": macro_rel,
            "bundles": bundle_entries,
            "theorems": theorem_entries,
        },
        "assets": asset_paths,
        "search": {
            "shard_prefix_len": search_meta["shard_prefix_len"],
            "shard_template": search_meta["shard_template"],
            "bucket_mode": search_meta["bucket_mode"],
            "bucket_key": search_meta["bucket_key"],
            "total_entries": search_meta["total_entries"],
            "shards": search_meta["shards"],
        },
    }
    manifest_bytes = _safe_write_json(os.path.join(split_dir, "manifest.json"), manifest)
    safety = _verify_split_dir_safety(split_dir)

    return {
        "schema": SPLIT_MANIFEST_SCHEMA,
        "split_dir": os.path.basename(os.path.abspath(split_dir)),
        "demo_mode": bool(demo_mode),
        "copied_site_assets": copied_assets,
        "manifest_bytes": manifest_bytes,
        "total_bytes": safety["total_bytes"],
        "file_count": safety["file_count"],
        "max_file_bytes": safety["max_file_bytes"],
        "max_file_rel": safety["max_file_rel"],
        "search_bytes": search_meta["total_bytes"],
        "stats": manifest["stats"],
    }


def export_tiny_demo_split_site(
    split_dir: str,
    *,
    title: Optional[str] = None,
    demo_dir: Optional[str] = None,
    max_bundles: int = 60,
    max_theorems: int = 80,
    max_circuits: Optional[int] = None,
    search_limit: int = 30_000,
) -> Dict[str, Any]:
    """Build examples/tiny_demo into a scratch kernel.db and export a split static site."""
    if os.path.islink(split_dir):
        raise ValueError(f"Refusing symlinked split_dir target: {split_dir}")
    ddir = os.path.abspath(demo_dir or os.path.join(_REPO_ROOT, "examples", "tiny_demo"))
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

    with tempfile.TemporaryDirectory(prefix="leanre_demo_split_") as td:
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

        return export_split_site(
            split_dir,
            portability=port_path,
            kernel_db=kdb_path,
            src_root=ddir,
            config_path=toml_path if os.path.isfile(toml_path) else None,
            title=title or "leanre — Tiny Demo Explorer",
            max_bundles=max_bundles,
            max_theorems=max_theorems,
            max_circuits=max_circuits,
            search_limit=search_limit,
            demo_mode=True,
        )


def _auto_discover_split_inputs(args: argparse.Namespace) -> Dict[str, Optional[str]]:
    """Auto-discover local repo artifacts when CLI runs `--split-dir` inside a repo."""
    explicit_any = any(
        getattr(args, k, None) is not None
        for k in (
            "decomp_dir", "trim_report", "cluster_labels", "portability", "kernel_db",
            "src_root", "findings_dir", "analysis_dir", "research_dir", "flirt_dir", "benchmark",
            "atlas_summary",
        )
    )
    anchor_root: Optional[str] = None
    if not explicit_any:
        cwd = os.path.realpath(os.getcwd())
        if os.path.isfile(os.path.join(cwd, "leanre.toml")) or os.path.isdir(os.path.join(cwd, "outputs")):
            anchor_root = cwd
        elif os.path.isfile(os.path.join(_REPO_ROOT, "leanre.toml")):
            anchor_root = _REPO_ROOT
    else:
        for probe in (args.kernel_db, args.decomp_dir, args.src_root):
            if probe:
                real_p = os.path.realpath(probe)
                if real_p.startswith(_REPO_ROOT + os.sep):
                    anchor_root = _REPO_ROOT
                    break

    def _pick(val: Optional[str], *rel_parts: str, is_dir: bool = False) -> Optional[str]:
        if val is not None:
            return val
        if anchor_root is None:
            return None
        cand = os.path.join(anchor_root, *rel_parts)
        if is_dir:
            return cand if (os.path.isdir(cand) and not os.path.islink(cand)) else None
        return cand if (os.path.isfile(cand) and not os.path.islink(cand)) else None

    src_cand = args.src_root
    if src_cand is None and anchor_root is not None:
        s_def = os.path.join(anchor_root, "data", "rh_mirror", "src")
        if os.path.isdir(s_def):
            src_cand = s_def
        elif os.path.isdir(os.path.join(anchor_root, "src")):
            src_cand = os.path.join(anchor_root, "src")

    return {
        "decomp_dir": _pick(args.decomp_dir, "outputs", "decomp", is_dir=True),
        "trim_report": _pick(args.trim_report, "outputs", "decomp", "trim_report.json"),
        "cluster_labels": _pick(args.cluster_labels, "outputs", "flirt", "cluster_labels_141.json"),
        "portability": _pick(args.portability, "outputs", "portability_gems.json"),
        "benchmark": _pick(args.benchmark, "outputs", "xrepo_benchmark.json"),
        "atlas_summary": _pick(getattr(args, "atlas_summary", None), "outputs", "atlas_summary.json"),
        "kernel_db": _pick(args.kernel_db, "outputs", "kernel", "kernel.db"),
        "leanre_db": _pick(args.leanre_db, "outputs", "leanre.db"),
        "src_root": src_cand,
        "findings_dir": _pick(args.findings_dir, "findings", is_dir=True),
        "analysis_dir": _pick(args.analysis_dir, "analysis", is_dir=True),
        "research_dir": _pick(args.research_dir, "research", is_dir=True),
        "flirt_dir": _pick(args.flirt_dir, "outputs", "flirt", is_dir=True),
    }


def _cmd_export_site(args: argparse.Namespace) -> int:
    if not getattr(args, "out", None) and not getattr(args, "split_dir", None):
        print("error: export-site requires --out <file.html> or --split-dir <dir>", file=sys.stderr)
        return 2

    results: List[Dict[str, Any]] = []
    if getattr(args, "split_dir", None):
        if getattr(args, "demo", False):
            res_s = export_tiny_demo_split_site(
                split_dir=args.split_dir,
                title=None if args.title == "leanre — Static Proof Explorer" else args.title,
                max_bundles=args.max_bundles,
                max_theorems=args.max_theorems,
                max_circuits=args.max_circuits,
                search_limit=args.search_limit,
            )
        else:
            disc = _auto_discover_split_inputs(args)
            res_s = export_split_site(
                split_dir=args.split_dir,
                decomp_dir=disc["decomp_dir"],
                trim_report=disc["trim_report"],
                cluster_labels=disc["cluster_labels"],
                portability=disc["portability"],
                benchmark=disc["benchmark"],
                atlas_summary=disc["atlas_summary"],
                kernel_db=disc["kernel_db"],
                leanre_db=disc["leanre_db"],
                src_root=disc["src_root"],
                findings_dir=disc["findings_dir"],
                analysis_dir=disc["analysis_dir"],
                research_dir=disc["research_dir"],
                flirt_dir=disc["flirt_dir"],
                config_path=args.config,
                title=None if args.title == "leanre — Static Proof Explorer" else args.title,
                repo_url=args.repo_url,
                pinned_commit=args.pinned_commit,
                src_prefix=args.src_prefix,
                max_bundles=args.max_bundles,
                max_theorems=args.max_theorems,
                max_circuits=args.max_circuits,
                search_limit=args.search_limit,
                demo_mode=False,
            )
        results.append(res_s)

    if getattr(args, "out", None):
        if getattr(args, "demo", False):
            res_h = export_tiny_demo_site(
                out_html=args.out,
                title=None if args.title == "leanre — Static Proof Explorer" else args.title,
            )
        else:
            res_h = export_static_site(
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
        results.append(res_h)

    print(json.dumps(results[0] if len(results) == 1 else {"exports": results}, indent=2, sort_keys=True))
    return 0


def _add_export_site_args(p: argparse.ArgumentParser) -> None:
    p.add_argument("--demo", action="store_true", help="Build and export the bundled examples/tiny_demo corpus")
    p.add_argument("--decomp-dir", default=None, help="Directory of leanre.decomp/v1 JSON blueprints")
    p.add_argument("--trim-report", default=None, help="Optional trim_report.json path")
    p.add_argument("--cluster-labels", default=None, help="Optional cluster_labels_141.json path")
    p.add_argument("--portability", default=None, help="Optional portability_gems.json path")
    p.add_argument("--benchmark", default=None, help="Optional xrepo_benchmark.json path")
    p.add_argument("--atlas-summary", default=None, help="Optional atlas_summary.json path for --split-dir")
    p.add_argument("--kernel-db", default=None, help="Optional kernel.db path")
    p.add_argument("--leanre-db", default=None, help="Optional leanre.db path for file/line counts & decl line numbers")
    p.add_argument("--src-root", default=None, help="Optional Lean source directory for bundle unread-field resolution")
    p.add_argument("--findings-dir", default=None, help="Optional findings/*.md directory for --split-dir")
    p.add_argument("--analysis-dir", default=None, help="Optional analysis/*.md directory for --split-dir")
    p.add_argument("--research-dir", default=None, help="Optional research/*.md directory for --split-dir")
    p.add_argument("--flirt-dir", default=None, help="Optional flirt/*.json directory for --split-dir")
    p.add_argument("--config", default=None, help="Optional leanre.toml profile path")
    p.add_argument("--repo-url", default=None, help="Override upstream GitHub repository URL")
    p.add_argument("--pinned-commit", default=None, help="Override pinned commit SHA")
    p.add_argument("--src-prefix", default=None, help="Override source prefix (e.g. 'src/')")
    p.add_argument("--out", default=None, help="Output single-file HTML path")
    p.add_argument("--split-dir", default=None, help="Output directory for lazy-sharded static site (GitHub Pages)")
    p.add_argument("--title", default="leanre — Static Proof Explorer", help="Page title")
    p.add_argument("--max-nodes", type=int, default=250, help="Max nodes embedded per blueprint (default: 250)")
    p.add_argument("--max-clusters", type=int, default=200, help="Max FLIRT clusters embedded (default: 200)")
    p.add_argument("--max-bundles", type=int, default=60, help="Max pre-rendered bundle circuits in --split-dir (default: 60)")
    p.add_argument("--max-theorems", type=int, default=80, help="Max pre-rendered theorem circuits in --split-dir (default: 80)")
    p.add_argument("--max-circuits", type=int, default=None, help="Optional total cap on pre-rendered bundle+theorem circuits")
    p.add_argument("--search-limit", type=int, default=30_000, help="Max declarations indexed in search shards (default: 30000)")
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
