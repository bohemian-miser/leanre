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
    (v === "kernel" && !!DATA.kernel);
  if(!has) btn.setAttribute("disabled", "disabled");
  btn.addEventListener("click", () => { if(!btn.hasAttribute("disabled")) switchView(v); });
}

renderOverview();
renderBlueprints();
renderTrim();
renderFlirt();
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

        if resolved_clusters is None:
            sib = os.path.join(os.path.dirname(os.path.abspath(decomp_dir)), "flirt", "cluster_labels_141.json")
            if os.path.isfile(sib) and not os.path.islink(sib):
                resolved_clusters = sib

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
        "kernel": kernel_summary,
    }


def export_static_site(
    decomp_dir: Optional[str],
    out_html: str,
    *,
    trim_report: Optional[str] = None,
    cluster_labels: Optional[str] = None,
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
        "has_kernel": payload["kernel"] is not None,
    }


def _cmd_export_site(args: argparse.Namespace) -> int:
    res = export_static_site(
        decomp_dir=args.decomp_dir,
        out_html=args.out,
        trim_report=args.trim_report,
        cluster_labels=args.cluster_labels,
        kernel_db=args.kernel_db,
        src_root=args.src_root,
        title=args.title,
        max_nodes_per_blueprint=args.max_nodes,
        max_clusters=args.max_clusters,
        with_bundles=args.with_bundles,
    )
    print(json.dumps(res, indent=2, sort_keys=True))
    return 0


def register_cli(sub: Any, dest: str = "export_site_func") -> argparse.ArgumentParser:
    p = sub.add_parser("export-site", help="Export a self-contained offline static HTML explorer")
    p.add_argument("--decomp-dir", default=None, help="Directory of leanre.decomp/v1 JSON blueprints")
    p.add_argument("--trim-report", default=None, help="Optional trim_report.json path")
    p.add_argument("--cluster-labels", default=None, help="Optional cluster_labels_141.json path")
    p.add_argument("--kernel-db", default=None, help="Optional kernel.db path")
    p.add_argument("--src-root", default=None, help="Optional Lean source directory for bundle unread-field resolution")
    p.add_argument("--out", required=True, help="Output HTML path")
    p.add_argument("--title", default="leanre — Static Proof Explorer", help="Page title")
    p.add_argument("--max-nodes", type=int, default=250, help="Max nodes embedded per blueprint (default: 250)")
    p.add_argument("--max-clusters", type=int, default=200, help="Max FLIRT clusters embedded (default: 200)")
    p.add_argument("--with-bundles", action="store_true", default=None, help="Force unread-bundle analysis on kernel.db")
    p.set_defaults(**{dest: _cmd_export_site})
    return p


def main(argv: Optional[Sequence[str]] = None) -> int:
    ap = argparse.ArgumentParser(prog="export_site", description="Generate self-contained offline leanre HTML explorer")
    ap.add_argument("--decomp-dir", default=None, help="Directory of leanre.decomp/v1 JSON blueprints")
    ap.add_argument("--trim-report", default=None, help="Optional trim_report.json path")
    ap.add_argument("--cluster-labels", default=None, help="Optional cluster_labels_141.json path")
    ap.add_argument("--kernel-db", default=None, help="Optional kernel.db path")
    ap.add_argument("--src-root", default=None, help="Optional Lean source directory for bundle resolution")
    ap.add_argument("--out", required=True, help="Output HTML path")
    ap.add_argument("--title", default="leanre — Static Proof Explorer", help="Page title")
    ap.add_argument("--max-nodes", type=int, default=250, help="Max nodes embedded per blueprint (default: 250)")
    ap.add_argument("--max-clusters", type=int, default=200, help="Max FLIRT clusters embedded (default: 200)")
    ap.add_argument("--with-bundles", action="store_true", default=None, help="Force unread-bundle analysis on kernel.db")
    args = ap.parse_args(argv)
    return _cmd_export_site(args)


if __name__ == "__main__":
    sys.exit(main())
