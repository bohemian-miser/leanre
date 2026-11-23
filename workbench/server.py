#!/usr/bin/env python3
"""
leanre Workbench Server ("Ghidra for Lean")
Python 3.9 stdlib ONLY (http.server, sqlite3, json, urllib.parse).

Serves workbench/ static assets on http://127.0.0.1:8420 and exposes fast,
read-only JSON APIs over outputs/leanre.db, outputs/forensics_report.json,
and outputs/workbench_bundle.json.

Phase 3 (see phase3.py): read-only kernel-exact and FLIRT APIs over
outputs/kernel/ and outputs/flirt/, plus annotation-pack APIs whose writes
are confined to annotations/ (the only thing this server ever writes).

Never reads or dumps full raw unlicensed .lean files from data/.
"""
from __future__ import annotations

import argparse
import collections
import json
import mimetypes
import os
import sqlite3
import sys
import time
from http import HTTPStatus
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Tuple
from urllib.parse import parse_qs, urlparse

WORKBENCH_DIR = Path(__file__).resolve().parent
PROJECT_ROOT = WORKBENCH_DIR.parent
DEFAULT_OUTPUTS_DIR = PROJECT_ROOT / "outputs"
PROTOTYPES_DIR = PROJECT_ROOT / "prototypes"
DEFAULT_ANNOTATIONS_DIR = PROJECT_ROOT / "annotations"

if str(WORKBENCH_DIR) not in sys.path:
    sys.path.insert(0, str(WORKBENCH_DIR))
import phase3  # noqa: E402  (workbench/phase3.py)
import phase4  # noqa: E402  (workbench/phase4.py)

# Static assets are served by extension allowlist only (no .py / .db / dotfiles).
STATIC_EXTS = {".html", ".js", ".css", ".json", ".svg", ".png", ".ico"}
MAX_POST_BYTES = 16 * 1024 * 1024
P3_PREFIXES = (
    "/api/p3/",
    "/api/p4/",
    "/api/decomp/",
    "/api/trim",
    "/api/bundles",
    "/api/portability",
    "/api/hygiene",
    "/api/circuit",
    "/api/kernel/",
    "/api/flirt/",
    "/api/annot/",
)


def load_project_config(
    config_path: Optional[str] = None, outputs_dir: Optional[Path] = None
) -> Dict[str, Any]:
    """Load safe, path-sanitized project metadata from leanre.toml if present."""
    root_str = str(PROJECT_ROOT)
    if root_str not in sys.path:
        sys.path.insert(0, root_str)
    try:
        from leanre import config as config_mod
    except Exception:
        return {"has_config": False, "name": "", "root_module": "Main", "src_dir": "src"}

    cfg = None
    if config_path:
        p = Path(config_path)
        if p.is_file():
            try:
                cfg = config_mod.load_config(str(p))
            except Exception:
                cfg = None
    if cfg is None:
        search_dirs: List[Path] = []
        if outputs_dir is not None:
            search_dirs.append(outputs_dir.resolve().parent)
        search_dirs.append(PROJECT_ROOT)
        for d in search_dirs:
            cand = d / "leanre.toml"
            if cand.is_file():
                try:
                    cfg = config_mod.load_config(str(cand))
                    break
                except Exception:
                    continue
    if cfg is None:
        return {"has_config": False, "name": "", "root_module": "Main", "src_dir": "src"}

    tmpl = str(cfg.upstream_url_template or "")
    if tmpl and not tmpl.startswith("https://github.com/"):
        tmpl = ""
    src_dir = str(cfg.src_dir or "src")
    if Path(src_dir).is_absolute():
        src_dir = Path(src_dir).name or "src"
    return {
        "has_config": bool(cfg.source_path),
        "name": str(cfg.project_name or ""),
        "root_module": str(cfg.root_module or "Main"),
        "src_dir": src_dir,
        "pinned_commit": str(cfg.pinned_commit or ""),
        "upstream_url_template": tmpl,
        "headline_roots": list(cfg.headline_roots or [])[:20],
        "rh_gates": bool(cfg.rh_gates),
        "lean_toolchain": str(cfg.lean_toolchain or ""),
    }

# Bitmask mapping matching leanre schema contract
FLAG_BITS = {
    "kexactB": 1,
    "kcopy": 2,
    "CutCptCopy": 4,
    "addDecl": 8,
    "run_tac": 16,
    "decide_kernel": 32,
    "positivity_ext": 64,
    "BuildAid": 128,
    "OpenLiteratureStatements": 256,
    "slow_con_leche": 512,
    "lean4lean_timeout": 1024,
    "sorry": 2048,
    "axiom": 4096,
    "native_decide": 8192,
    "unsafe": 16384,
    "implemented_by": 32768,
}

# Friendly aliases for query parameters
FLAG_ALIASES = {
    "decide +kernel": "decide_kernel",
    "decide_kernel": "decide_kernel",
    "slowest": "slow_con_leche",
    "slowest_con_leche": "slow_con_leche",
    "slow_con_leche": "slow_con_leche",
    "timeout": "lean4lean_timeout",
    "lean4lean_timeout": "lean4lean_timeout",
}


def safe_json_loads(raw: Any, default: Any) -> Any:
    if raw is None:
        return default
    if not isinstance(raw, str):
        return raw
    try:
        return json.loads(raw)
    except Exception:
        return default


def short_label(name: str, max_len: int = 34) -> str:
    if not name:
        return ""
    if len(name) <= max_len:
        return name
    parts = name.split(".")
    if len(parts) >= 2:
        tail = ".".join(parts[-2:])
        if len(tail) <= max_len:
            return tail
    last = parts[-1]
    if len(last) <= max_len:
        return last
    return last[: max_len - 1] + "…"


class LeanREStore:
    """Thread-safe read-only query layer over outputs/leanre.db and JSON outputs."""

    def __init__(
        self,
        db_path: Path,
        outputs_dir: Path,
        project_config: Optional[Dict[str, Any]] = None,
    ) -> None:
        self.db_path = db_path
        self.outputs_dir = outputs_dir
        self.project_config: Dict[str, Any] = dict(project_config or {})
        self._overview_cache: Optional[Dict[str, Any]] = None
        self._overview_mtime: float = 0.0
        self._investigations_cache: Optional[Dict[str, Any]] = None
        self._investigations_mtime: float = 0.0

    def db_ready(self) -> bool:
        return self.db_path.is_file() and self.db_path.stat().st_size > 0

    def _connect(self) -> sqlite3.Connection:
        # Read-only URI when file exists
        uri = "file:{}?mode=ro".format(self.db_path.as_posix())
        conn = sqlite3.connect(uri, uri=True, timeout=10.0)
        conn.row_factory = sqlite3.Row
        return conn

    def _read_json_file(self, filename: str) -> Optional[Dict[str, Any]]:
        path = self.outputs_dir / filename
        if not path.is_file():
            return None
        try:
            with path.open("r", encoding="utf-8") as fh:
                return json.load(fh)
        except Exception:
            return None

    def _table_exists(self, conn: sqlite3.Connection, table: str) -> bool:
        row = conn.execute(
            "SELECT 1 FROM sqlite_master WHERE type='table' AND name=?", (table,)
        ).fetchone()
        return row is not None

    def _meta_dict(self, conn: sqlite3.Connection) -> Dict[str, Any]:
        out: Dict[str, Any] = {}
        if not self._table_exists(conn, "meta"):
            return out
        for r in conn.execute("SELECT key, value_json FROM meta"):
            out[r["key"]] = safe_json_loads(r["value_json"], r["value_json"])
        return out

    def _classify_module_role(self, row: sqlite3.Row) -> str:
        name = row["name"]
        mask = int(row["forensic_flags_bitmask"] or 0)
        if name in (
            "Main",
            "Statements",
            "Supplements.Kernels.MainTheorems",
            "Supplements.Kernels.MainTheoremsAll",
            "Supplements.Kernels.MainTheoremsCritical",
        ):
            return "entry"
        if mask & (1 | 2 | 4 | 8 | 16 | 2048 | 4096 | 8192 | 16384 | 32768):
            return "forensic"
        if mask & (32 | 512 | 1024):
            return "slow"
        if (
            "MainConclusion" in name
            or "EveryCharacter" in name
            or "ExistsPageN" in name
            or "StatementOC" in name
            or "WindowInequality" in name
            or "ThetaChainSpec" in name
        ):
            return "crux"
        if (
            "RhOfRight" in name
            or "CritLine" in name
            or "ClaimStrip" in name
            or "Imprimitive" in name
            or "GammaFactorNonvanishing" in name
        ):
            return "classical"
        if int(row["dom_subtree_size"] or 0) >= 1000:
            return "hub"
        return "normal"

    # ------------------------------------------------------------------
    # GET /api/overview
    # ------------------------------------------------------------------
    def get_overview(self) -> Dict[str, Any]:
        mtime = self.db_path.stat().st_mtime if self.db_ready() else 0.0
        bundle_path = self.outputs_dir / "workbench_bundle.json"
        if bundle_path.is_file():
            mtime = max(mtime, bundle_path.stat().st_mtime)
        if self._overview_cache is not None and mtime == self._overview_mtime:
            return self._overview_cache

        bundle = self._read_json_file("workbench_bundle.json") or {}
        report = self._read_json_file("forensics_report.json") or {}

        if not self.db_ready():
            res = {
                "mode": "bundle_only" if bundle else "empty",
                "db_ready": False,
                "project": self.project_config,
                "meta": bundle.get("meta", report.get("meta", {})),
                "overview": bundle.get("overview", {}),
                "forensics_report": report,
            }
            return res

        conn = self._connect()
        try:
            meta = self._meta_dict(conn)
            corpus_stats = meta.get("corpus_stats") or bundle.get("overview", {}).get("corpus_stats") or {}
            tcb_stats = meta.get("tcb_stats") or bundle.get("overview", {}).get("tcb_stats") or {}
            forensic_summary = meta.get("forensic_summary") or {}
            acceptance_gates = meta.get("acceptance_gates") or bundle.get("meta", {}).get("acceptance_gates") or {}
            bindiff_v1 = meta.get("bindiff_v1") or bundle.get("meta", {}).get("bindiff_v1") or {}
            provenance = meta.get("provenance") or bundle.get("meta", {}) or {}

            # Live forensic counts from forensic_hits & modules
            forensic_counts: Dict[str, int] = {}
            if self._table_exists(conn, "forensic_hits"):
                for r in conn.execute(
                    "SELECT tag, COUNT(*) AS hit_count, COUNT(DISTINCT module) AS mod_count "
                    "FROM forensic_hits GROUP BY tag ORDER BY hit_count DESC"
                ):
                    forensic_counts[r["tag"]] = int(r["hit_count"])
                    forensic_counts[r["tag"] + "_modules"] = int(r["mod_count"])

            # Single-pass bitmask summary over modules with forensic_flags_bitmask != 0 (avoids 16 table scans)
            if self._table_exists(conn, "modules"):
                bit_totals: Dict[str, int] = {k: 0 for k in FLAG_BITS}
                for r in conn.execute(
                    "SELECT forensic_flags_bitmask, COUNT(*) AS c FROM modules "
                    "WHERE forensic_flags_bitmask != 0 GROUP BY forensic_flags_bitmask"
                ):
                    mask = int(r["forensic_flags_bitmask"])
                    c = int(r["c"])
                    for fname, bit in FLAG_BITS.items():
                        if mask & bit:
                            bit_totals[fname] += c
                for fname, cnt in bit_totals.items():
                    forensic_counts.setdefault(fname + "_modules", cnt)
                    if cnt > 0 or fname in (
                        "kexactB", "kcopy", "CutCptCopy", "addDecl", "run_tac",
                        "decide_kernel", "slow_con_leche", "lean4lean_timeout",
                        "sorry", "axiom", "native_decide", "OpenLiteratureStatements"
                    ):
                        forensic_counts.setdefault(fname, cnt)

            # Horn counts
            horn_edges_cnt = 0
            horn_decls_cnt = 0
            if self._table_exists(conn, "horn_edges"):
                horn_edges_cnt = int(conn.execute("SELECT COUNT(*) FROM horn_edges").fetchone()[0])
                horn_decls_cnt = int(conn.execute("SELECT COUNT(DISTINCT decl_id) FROM horn_edges").fetchone()[0])

            # Namespace stats tree (depth 1 and 2)
            ns_rows: List[Dict[str, Any]] = []
            if self._table_exists(conn, "namespace_stats"):
                for r in conn.execute(
                    "SELECT prefix, depth, parent, module_count, lines_wc, lines_eof, bytes, "
                    "decl_count, thm_count, def_count, shim_count, mathlib_import_count, "
                    "forensic_hit_count, top_decl_prefixes_json "
                    "FROM namespace_stats ORDER BY depth ASC, module_count DESC"
                ):
                    ns_rows.append({
                        "prefix": r["prefix"],
                        "depth": int(r["depth"]),
                        "parent": r["parent"],
                        "module_count": int(r["module_count"]),
                        "lines_wc": int(r["lines_wc"]),
                        "lines_eof": int(r["lines_eof"]),
                        "bytes": int(r["bytes"]),
                        "decl_count": int(r["decl_count"]),
                        "thm_count": int(r["thm_count"]),
                        "def_count": int(r["def_count"]),
                        "shim_count": int(r["shim_count"]),
                        "mathlib_import_count": int(r["mathlib_import_count"]),
                        "forensic_hit_count": int(r["forensic_hit_count"]),
                        "top_decl_prefixes": safe_json_loads(r["top_decl_prefixes_json"], []),
                    })

            # Top TCB namespaces directly from tcb_decls
            tcb_namespaces: List[Dict[str, Any]] = []
            tcb_kind_counts: Dict[str, int] = {}
            if self._table_exists(conn, "tcb_decls"):
                for r in conn.execute("SELECT kind, COUNT(*) AS c FROM tcb_decls GROUP BY kind"):
                    tcb_kind_counts[r["kind"]] = int(r["c"])
                for r in conn.execute(
                    "SELECT module_prefix, COUNT(*) AS total, "
                    "SUM(is_definition) AS defs, SUM(CASE WHEN is_definition=0 THEN 1 ELSE 0 END) AS thms, "
                    "SUM(in_rh_cone) AS rh_cnt "
                    "FROM tcb_decls GROUP BY module_prefix ORDER BY total DESC LIMIT 25"
                ):
                    tcb_namespaces.append({
                        "prefix": r["module_prefix"],
                        "total": int(r["total"]),
                        "defs": int(r["defs"] or 0),
                        "thms": int(r["thms"] or 0),
                        "rh_cnt": int(r["rh_cnt"] or 0),
                    })

            # Top dominator hubs & slowest / timeout hotspots
            top_hubs: List[Dict[str, Any]] = []
            if self._table_exists(conn, "modules"):
                for r in conn.execute(
                    "SELECT name, file_path, lines, decl_count, fan_in, fan_out, dom_parent, "
                    "dom_subtree_size, rev_reach, forensic_flags_json "
                    "FROM modules ORDER BY dom_subtree_size DESC LIMIT 20"
                ):
                    top_hubs.append({
                        "name": r["name"],
                        "file_path": r["file_path"],
                        "lines": int(r["lines"]),
                        "decl_count": int(r["decl_count"]),
                        "fan_in": int(r["fan_in"]),
                        "fan_out": int(r["fan_out"]),
                        "dom_parent": r["dom_parent"],
                        "dom_subtree_size": int(r["dom_subtree_size"]),
                        "rev_reach": int(r["rev_reach"]),
                        "flags": safe_json_loads(r["forensic_flags_json"], []),
                    })

            bundle_ov = bundle.get("overview", {})
            res = {
                "mode": "live_sqlite",
                "db_ready": True,
                "project": self.project_config,
                "meta": {
                    "provenance": provenance,
                    "acceptance_gates": acceptance_gates,
                    "bindiff_v1": bindiff_v1,
                },
                "overview": {
                    "corpus_stats": corpus_stats,
                    "tcb_stats": tcb_stats,
                    "tcb_kind_counts": tcb_kind_counts,
                    "tcb_namespaces": tcb_namespaces,
                    "forensic_counts": forensic_counts,
                    "forensic_summary": forensic_summary,
                    "horn_stats": {
                        "horn_edges": horn_edges_cnt,
                        "horn_decls": horn_decls_cnt,
                    },
                    "namespaces": ns_rows,
                    "top_hubs": top_hubs,
                    "slowest_con_leche": bundle_ov.get("slowest_con_leche", []),
                    "timeout_modules": bundle_ov.get("timeout_modules", []),
                    "trailing_nl_stats": bundle_ov.get("trailing_nl_stats", {}),
                    "clone_stats": bundle_ov.get("clone_stats", {}),
                    "top_components": bundle_ov.get("top_components", []),
                    "top_imported": bundle_ov.get("top_imported", []),
                },
            }
            self._overview_cache = res
            self._overview_mtime = mtime
            return res
        finally:
            conn.close()

    # ------------------------------------------------------------------
    # GET /api/search?q=...&kind=...&flag=...&ns=...&limit=50
    # ------------------------------------------------------------------
    def search(
        self,
        q: str = "",
        kind: str = "all",
        flag: str = "",
        ns: str = "",
        limit: int = 50,
    ) -> Dict[str, Any]:
        limit = max(1, min(int(limit), 200))
        q = q.strip()
        flag_raw = flag.strip()
        flag_norm = FLAG_ALIASES.get(flag_raw, flag_raw)
        ns = ns.strip()
        kind = (kind or "all").strip().lower()

        if not self.db_ready():
            return {"query": q, "kind": kind, "flag": flag_norm, "ns": ns, "total": 0, "results": []}

        conn = self._connect()
        try:
            results: List[Dict[str, Any]] = []
            like_q = "%{}%".format(q)
            prefix_q = "{}%".format(q)

            # Special shortcut flags
            if flag_norm == "tcb_def":
                sql = (
                    "SELECT name, kind, module_prefix, is_definition, depth_from_rh, "
                    "dom_subtree_size, fan_in, fan_out FROM tcb_decls WHERE is_definition = 1 "
                )
                params: List[Any] = []
                if q:
                    sql += "AND (name LIKE ? OR module_prefix LIKE ?) "
                    params.extend([like_q, like_q])
                sql += "ORDER BY CASE WHEN depth_from_rh >= 0 THEN depth_from_rh ELSE 999 END ASC, dom_subtree_size DESC LIMIT ?"
                params.append(limit)
                for r in conn.execute(sql, params):
                    results.append({
                        "id": r["name"],
                        "name": r["name"],
                        "display": short_label(r["name"], 42),
                        "kind": "tcb",
                        "subkind": r["kind"],
                        "module": r["module_prefix"],
                        "line_no": None,
                        "lines": None,
                        "dom_subtree_size": int(r["dom_subtree_size"]),
                        "fan_in": int(r["fan_in"]),
                        "fan_out": int(r["fan_out"]),
                        "depth_from_rh": int(r["depth_from_rh"]),
                        "flags": ["tcb_def"],
                        "snippet": "{} (depth_rh={}, dom={})".format(
                            r["kind"], r["depth_from_rh"], r["dom_subtree_size"]
                        ),
                    })
                return {"query": q, "kind": "tcb", "flag": flag_norm, "ns": ns, "total": len(results), "results": results}

            if flag_norm == "horn_spine":
                sql = (
                    "SELECT he.decl_name, he.module, he.line_no, he.req_prop, he.prov_prop, "
                    "m.dom_subtree_size, m.lines "
                    "FROM horn_edges he LEFT JOIN modules m ON m.name = he.module WHERE 1=1 "
                )
                params = []
                if q:
                    sql += "AND (he.decl_name LIKE ? OR he.req_prop LIKE ? OR he.prov_prop LIKE ? OR he.module LIKE ?) "
                    params.extend([like_q, like_q, like_q, like_q])
                sql += "ORDER BY COALESCE(m.dom_subtree_size, 0) DESC, he.id ASC LIMIT ?"
                params.append(limit)
                seen_decl: Set[Tuple[str, str]] = set()
                for r in conn.execute(sql, params):
                    key = (r["module"], r["decl_name"])
                    if key in seen_decl:
                        continue
                    seen_decl.add(key)
                    results.append({
                        "id": r["module"],
                        "name": r["decl_name"],
                        "display": short_label(r["decl_name"], 40),
                        "kind": "horn",
                        "subkind": "horn",
                        "module": r["module"],
                        "line_no": int(r["line_no"]),
                        "lines": int(r["lines"] or 0),
                        "dom_subtree_size": int(r["dom_subtree_size"] or 0),
                        "fan_in": 0,
                        "fan_out": 0,
                        "flags": ["horn"],
                        "snippet": "REQUIRES {} ⟹ {}".format(
                            short_label(r["req_prop"], 24), short_label(r["prov_prop"], 24)
                        ),
                    })
                return {"query": q, "kind": "horn", "flag": flag_norm, "ns": ns, "total": len(results), "results": results}

            # Forensic flag filter via forensic_hits + modules bitmask
            if flag_norm:
                bit = FLAG_BITS.get(flag_norm, 0)
                if self._table_exists(conn, "forensic_hits"):
                    sql = (
                        "SELECT fh.tag, fh.severity, fh.module, fh.line_no, fh.decl_name, fh.snippet, "
                        "fh.hops_to_main, m.lines, m.dom_subtree_size, m.fan_in, m.fan_out "
                        "FROM forensic_hits fh LEFT JOIN modules m ON m.name = fh.module "
                        "WHERE fh.tag = ? "
                    )
                    params = [flag_norm]
                    if q:
                        sql += "AND (fh.module LIKE ? OR COALESCE(fh.decl_name, '') LIKE ? OR fh.snippet LIKE ?) "
                        params.extend([like_q, like_q, like_q])
                    if ns:
                        sql += "AND fh.module LIKE ? "
                        params.append(ns + "%")
                    sql += "ORDER BY fh.hops_to_main ASC, COALESCE(m.dom_subtree_size, 0) DESC LIMIT ?"
                    params.append(limit)
                    for r in conn.execute(sql, params):
                        results.append({
                            "id": r["module"],
                            "name": r["module"],
                            "display": short_label(r["module"], 40),
                            "kind": "forensic",
                            "subkind": r["tag"],
                            "module": r["module"],
                            "line_no": int(r["line_no"]),
                            "lines": int(r["lines"] or 0),
                            "dom_subtree_size": int(r["dom_subtree_size"] or 0),
                            "fan_in": int(r["fan_in"] or 0),
                            "fan_out": int(r["fan_out"] or 0),
                            "hops_to_main": int(r["hops_to_main"] or 0),
                            "flags": [r["tag"]],
                            "snippet": (r["decl_name"] + ": " if r["decl_name"] else "") + (r["snippet"] or ""),
                        })
                if not results and bit and self._table_exists(conn, "modules"):
                    sql = (
                        "SELECT name, lines, dom_subtree_size, fan_in, fan_out, forensic_flags_json, file_path "
                        "FROM modules WHERE (forensic_flags_bitmask & ?) != 0 "
                    )
                    params = [bit]
                    if q:
                        sql += "AND name LIKE ? "
                        params.append(like_q)
                    if ns:
                        sql += "AND name LIKE ? "
                        params.append(ns + "%")
                    sql += "ORDER BY dom_subtree_size DESC, lines DESC LIMIT ?"
                    params.append(limit)
                    for r in conn.execute(sql, params):
                        results.append({
                            "id": r["name"],
                            "name": r["name"],
                            "display": short_label(r["name"], 40),
                            "kind": "module",
                            "subkind": flag_norm,
                            "module": r["name"],
                            "line_no": 1,
                            "lines": int(r["lines"]),
                            "dom_subtree_size": int(r["dom_subtree_size"]),
                            "fan_in": int(r["fan_in"]),
                            "fan_out": int(r["fan_out"]),
                            "flags": safe_json_loads(r["forensic_flags_json"], []),
                            "snippet": r["file_path"],
                        })
                return {"query": q, "kind": kind, "flag": flag_norm, "ns": ns, "total": len(results), "results": results}

            # Namespace-scoped browsing or general search across modules, declarations, horn, tcb
            per_bucket = limit if kind != "all" else max(10, limit // 2)

            if kind in ("all", "module"):
                sql = (
                    "SELECT name, file_path, lines, decl_count, dom_subtree_size, fan_in, fan_out, "
                    "forensic_flags_json FROM modules WHERE 1=1 "
                )
                params = []
                if ns:
                    sql += "AND (name = ? OR name LIKE ?) "
                    params.extend([ns, ns + ".%"])
                if q:
                    sql += "AND (name LIKE ? OR file_path LIKE ?) "
                    params.extend([like_q, like_q])
                    sql += (
                        "ORDER BY CASE WHEN name = ? THEN 0 WHEN name LIKE ? THEN 1 ELSE 2 END, "
                        "dom_subtree_size DESC, fan_in DESC LIMIT ?"
                    )
                    params.extend([q, prefix_q, per_bucket])
                else:
                    sql += "ORDER BY dom_subtree_size DESC, fan_in DESC, lines DESC LIMIT ?"
                    params.append(per_bucket)
                for r in conn.execute(sql, params):
                    results.append({
                        "id": r["name"],
                        "name": r["name"],
                        "display": short_label(r["name"], 42),
                        "kind": "module",
                        "subkind": "module",
                        "module": r["name"],
                        "line_no": 1,
                        "lines": int(r["lines"]),
                        "dom_subtree_size": int(r["dom_subtree_size"]),
                        "fan_in": int(r["fan_in"]),
                        "fan_out": int(r["fan_out"]),
                        "flags": safe_json_loads(r["forensic_flags_json"], []),
                        "snippet": "{} · {} decls".format(r["file_path"], r["decl_count"]),
                    })

            if kind in ("all", "decl") and (q or kind == "decl"):
                decl_lim = max(10, limit // 3) if kind == "all" else limit
                rows_d: List[sqlite3.Row] = []
                if q and not ns:
                    # Fast indexed NOCASE prefix scan first (sub-ms on 1.06M declarations)
                    hi_q = q[:-1] + chr(ord(q[-1]) + 1)
                    rows_d = conn.execute(
                        "SELECT d.name, d.kind, d.module, d.line_no, d.signature_snippet, d.forensic_tags, "
                        "d.horn_proves, COALESCE(m.dom_subtree_size, 0) AS dom_sz "
                        "FROM (SELECT id, name, kind, module, line_no, signature_snippet, forensic_tags, horn_proves "
                        "      FROM declarations WHERE name COLLATE NOCASE >= ? AND name COLLATE NOCASE < ? LIMIT 150) d "
                        "LEFT JOIN modules m ON m.name = d.module "
                        "ORDER BY CASE WHEN d.name COLLATE NOCASE = ? THEN 0 ELSE 1 END, dom_sz DESC LIMIT ?",
                        (q, hi_q, q, decl_lim),
                    ).fetchall()
                if len(rows_d) < decl_lim:
                    need = decl_lim - len(rows_d)
                    seen_names = {(r["module"], r["name"], int(r["line_no"])) for r in rows_d}
                    sub_sql = (
                        "SELECT id, name, kind, module, line_no, signature_snippet, forensic_tags, horn_proves "
                        "FROM declarations WHERE 1=1 "
                    )
                    sub_params: List[Any] = []
                    if ns:
                        sub_sql += "AND module >= ? AND module < ? "
                        sub_params.extend([ns, ns[:-1] + chr(ord(ns[-1]) + 1)])
                    if q:
                        sub_sql += "AND name LIKE ? "
                        sub_params.append(like_q)
                    sub_sql += "LIMIT 250"
                    more_d = conn.execute(
                        "SELECT d.name, d.kind, d.module, d.line_no, d.signature_snippet, d.forensic_tags, "
                        "d.horn_proves, COALESCE(m.dom_subtree_size, 0) AS dom_sz "
                        "FROM (" + sub_sql + ") d LEFT JOIN modules m ON m.name = d.module "
                        "ORDER BY dom_sz DESC LIMIT ?",
                        sub_params + [need + len(seen_names)],
                    ).fetchall()
                    for r in more_d:
                        key = (r["module"], r["name"], int(r["line_no"]))
                        if key not in seen_names:
                            seen_names.add(key)
                            rows_d.append(r)
                            if len(rows_d) >= decl_lim:
                                break
                for r in rows_d:
                    results.append({
                        "id": r["module"],
                        "name": r["name"],
                        "display": short_label(r["name"], 42),
                        "kind": "decl",
                        "subkind": r["kind"],
                        "module": r["module"],
                        "line_no": int(r["line_no"]),
                        "lines": None,
                        "dom_subtree_size": int(r["dom_sz"]),
                        "fan_in": 0,
                        "fan_out": 0,
                        "flags": safe_json_loads(r["forensic_tags"], []),
                        "snippet": r["signature_snippet"],
                    })

            if kind == "horn":
                sql = (
                    "SELECT he.decl_name, he.module, he.line_no, he.req_prop, he.prov_prop, "
                    "COALESCE(m.dom_subtree_size, 0) AS dom_sz "
                    "FROM horn_edges he LEFT JOIN modules m ON m.name = he.module WHERE 1=1 "
                )
                params = []
                if q:
                    sql += "AND (he.decl_name LIKE ? OR he.req_prop LIKE ? OR he.prov_prop LIKE ?) "
                    params.extend([like_q, like_q, like_q])
                sql += "ORDER BY dom_sz DESC LIMIT ?"
                params.append(limit)
                for r in conn.execute(sql, params):
                    results.append({
                        "id": r["module"],
                        "name": r["decl_name"],
                        "display": short_label(r["decl_name"], 40),
                        "kind": "horn",
                        "subkind": "horn",
                        "module": r["module"],
                        "line_no": int(r["line_no"]),
                        "lines": None,
                        "dom_subtree_size": int(r["dom_sz"]),
                        "fan_in": 0,
                        "fan_out": 0,
                        "flags": ["horn"],
                        "snippet": "{} ⟹ {}".format(
                            short_label(r["req_prop"], 24), short_label(r["prov_prop"], 24)
                        ),
                    })

            if kind in ("all", "tcb") and (q or kind == "tcb") and self._table_exists(conn, "tcb_decls"):
                sql = (
                    "SELECT name, kind, module_prefix, is_definition, depth_from_rh, "
                    "dom_subtree_size, fan_in, fan_out FROM tcb_decls WHERE 1=1 "
                )
                params = []
                if q:
                    sql += "AND (name LIKE ? OR module_prefix LIKE ?) "
                    params.extend([like_q, like_q])
                    sql += (
                        "ORDER BY CASE WHEN name = ? THEN 0 WHEN name LIKE ? THEN 1 ELSE 2 END, "
                        "is_definition DESC, dom_subtree_size DESC LIMIT ?"
                    )
                    params.extend([q, prefix_q, max(10, limit // 3) if kind == "all" else limit])
                else:
                    sql += "ORDER BY is_definition DESC, CASE WHEN depth_from_rh >= 0 THEN depth_from_rh ELSE 999 END ASC, dom_subtree_size DESC LIMIT ?"
                    params.append(limit)
                for r in conn.execute(sql, params):
                    results.append({
                        "id": r["name"],
                        "name": r["name"],
                        "display": short_label(r["name"], 42),
                        "kind": "tcb",
                        "subkind": r["kind"],
                        "module": r["module_prefix"],
                        "line_no": None,
                        "lines": None,
                        "dom_subtree_size": int(r["dom_subtree_size"]),
                        "fan_in": int(r["fan_in"]),
                        "fan_out": int(r["fan_out"]),
                        "depth_from_rh": int(r["depth_from_rh"]),
                        "flags": ["tcb_def"] if r["is_definition"] else ["tcb_thm"],
                        "snippet": "TCB {} · {} · depth_rh={}".format(
                            r["kind"], r["module_prefix"], r["depth_from_rh"]
                        ),
                    })

            return {
                "query": q,
                "kind": kind,
                "flag": flag_norm,
                "ns": ns,
                "total": len(results),
                "results": results[:limit],
            }
        finally:
            conn.close()

    # ------------------------------------------------------------------
    # GET /api/module?name=...&kind=...
    # ------------------------------------------------------------------
    def _reconstruct_path_to_main(self, conn: sqlite3.Connection, mod_name: str, max_hops: int = 80) -> List[str]:
        path: List[str] = [mod_name]
        cur = mod_name
        seen = {cur}
        for _ in range(max_hops):
            if cur == "Main":
                break
            row = conn.execute("SELECT parent_to_main FROM modules WHERE name = ?", (cur,)).fetchone()
            if not row or not row["parent_to_main"]:
                break
            nxt = row["parent_to_main"]
            if nxt in seen:
                break
            path.append(nxt)
            seen.add(nxt)
            cur = nxt
        return path

    def _reconstruct_dom_chain(self, conn: sqlite3.Connection, mod_name: str, max_hops: int = 80) -> List[str]:
        chain: List[str] = [mod_name]
        cur = mod_name
        seen = {cur}
        for _ in range(max_hops):
            row = conn.execute("SELECT dom_parent FROM modules WHERE name = ?", (cur,)).fetchone()
            if not row or not row["dom_parent"]:
                break
            nxt = row["dom_parent"]
            if nxt in seen:
                break
            chain.append(nxt)
            seen.add(nxt)
            cur = nxt
        return chain

    def get_module(self, name: str, kind: str = "") -> Dict[str, Any]:
        name = (name or "").strip()
        kind = (kind or "").strip().lower()
        if not name or not self.db_ready():
            return {"found": False, "name": name}

        conn = self._connect()
        try:
            # Explicit TCB lookup or fallback to TCB if not a module
            if kind == "tcb":
                tcb = self._get_tcb_detail(conn, name)
                if tcb is not None:
                    return tcb

            row = conn.execute("SELECT * FROM modules WHERE name = ?", (name,)).fetchone()

            # If not a module, check if it's a declaration name -> resolve owning module
            resolved_decl: Optional[str] = None
            if row is None and kind != "tcb":
                drow = conn.execute(
                    "SELECT module, name FROM declarations WHERE name = ? LIMIT 1", (name,)
                ).fetchone()
                if drow:
                    resolved_decl = drow["name"]
                    row = conn.execute("SELECT * FROM modules WHERE name = ?", (drow["module"],)).fetchone()

            # Check Horn proposition -> resolve declaring/proving module
            if row is None and kind != "tcb" and self._table_exists(conn, "horn_edges"):
                hrow = conn.execute(
                    "SELECT module, decl_name FROM horn_edges WHERE prov_prop = ? OR req_prop = ? LIMIT 1",
                    (name, name),
                ).fetchone()
                if hrow:
                    resolved_decl = hrow["decl_name"]
                    row = conn.execute("SELECT * FROM modules WHERE name = ?", (hrow["module"],)).fetchone()

            # Check TCB decl if still not found
            if row is None:
                tcb = self._get_tcb_detail(conn, name)
                if tcb is not None:
                    return tcb
                return {"found": False, "name": name}

            mod_name = row["name"]
            mod_dict = {
                "name": mod_name,
                "file_path": row["file_path"],
                "namespace_top": row["namespace_top"],
                "namespace_l2": row["namespace_l2"],
                "lines": int(row["lines"]),
                "lines_wc": int(row["lines_wc"]),
                "bytes": int(row["bytes"]),
                "trailing_nl": bool(row["trailing_nl"]),
                "decl_count": int(row["decl_count"]),
                "thm_count": int(row["thm_count"]),
                "def_count": int(row["def_count"]),
                "import_count": int(row["import_count"]),
                "imports_mathlib": bool(row["imports_mathlib"]),
                "fan_in": int(row["fan_in"]),
                "fan_out": int(row["fan_out"]),
                "bfs_depth": int(row["bfs_depth"]),
                "bottom_depth": int(row["bottom_depth"]),
                "parent_to_main": row["parent_to_main"],
                "dom_parent": row["dom_parent"],
                "dom_subtree_size": int(row["dom_subtree_size"]),
                "dom_subtree_lines": int(row["dom_subtree_lines"]),
                "rev_reach": int(row["rev_reach"]),
                "is_shim": bool(row["is_shim"]),
                "dup_imports": int(row["dup_imports"]),
                "clone_cluster_size": int(row["clone_cluster_size"]),
                "zlib_ratio": float(row["zlib_ratio"] or 0.0),
                "forensic_flags": safe_json_loads(row["forensic_flags_json"], []),
                "role": self._classify_module_role(row),
            }

            imports = [
                {
                    "name": r["dst"],
                    "lines": int(r["lines"] or 0),
                    "dom_subtree_size": int(r["dom_subtree_size"] or 0),
                    "flags": safe_json_loads(r["forensic_flags_json"], []),
                }
                for r in conn.execute(
                    "SELECT e.dst, m.lines, m.dom_subtree_size, m.forensic_flags_json "
                    "FROM module_edges e LEFT JOIN modules m ON m.name = e.dst "
                    "WHERE e.src = ? ORDER BY COALESCE(m.dom_subtree_size, 0) DESC LIMIT 80",
                    (mod_name,),
                )
            ]

            imported_by_total = int(
                conn.execute("SELECT COUNT(*) FROM module_edges WHERE dst = ?", (mod_name,)).fetchone()[0]
            )
            imported_by = [
                {
                    "name": r["src"],
                    "lines": int(r["lines"] or 0),
                    "dom_subtree_size": int(r["dom_subtree_size"] or 0),
                    "flags": safe_json_loads(r["forensic_flags_json"], []),
                }
                for r in conn.execute(
                    "SELECT e.src, m.lines, m.dom_subtree_size, m.forensic_flags_json "
                    "FROM module_edges e LEFT JOIN modules m ON m.name = e.src "
                    "WHERE e.dst = ? ORDER BY COALESCE(m.dom_subtree_size, 0) DESC LIMIT 60",
                    (mod_name,),
                )
            ]

            declarations = [
                {
                    "id": int(r["id"]),
                    "name": r["name"],
                    "kind": r["kind"],
                    "line_no": int(r["line_no"]),
                    "signature_snippet": r["signature_snippet"],
                    "horn_requires": safe_json_loads(r["horn_requires_json"], []),
                    "horn_proves": r["horn_proves"],
                    "forensic_tags": safe_json_loads(r["forensic_tags"], []),
                }
                for r in conn.execute(
                    "SELECT id, name, kind, line_no, signature_snippet, horn_requires_json, "
                    "horn_proves, forensic_tags FROM declarations WHERE module = ? "
                    "ORDER BY line_no ASC LIMIT 120",
                    (mod_name,),
                )
            ]

            horn_clauses: List[Dict[str, Any]] = []
            for d in declarations:
                if d["horn_requires"] or d["horn_proves"]:
                    horn_clauses.append({
                        "decl": d["name"],
                        "module": mod_name,
                        "line_no": d["line_no"],
                        "requires": d["horn_requires"],
                        "proves": d["horn_proves"],
                        "snippet": d["signature_snippet"],
                    })

            forensic_hits = [
                {
                    "tag": r["tag"],
                    "severity": r["severity"],
                    "module": r["module"],
                    "line_no": int(r["line_no"]),
                    "decl_name": r["decl_name"],
                    "snippet": r["snippet"],
                    "hops_to_main": int(r["hops_to_main"]),
                    "shortest_path_to_main": safe_json_loads(r["shortest_path_to_main_json"], []),
                }
                for r in conn.execute(
                    "SELECT tag, severity, module, line_no, decl_name, snippet, hops_to_main, "
                    "shortest_path_to_main_json FROM forensic_hits WHERE module = ? ORDER BY line_no ASC LIMIT 80",
                    (mod_name,),
                )
            ]

            shortest_path = self._reconstruct_path_to_main(conn, mod_name)
            dom_chain = self._reconstruct_dom_chain(conn, mod_name)

            return {
                "found": True,
                "entity_kind": "module",
                "name": mod_name,
                "resolved_decl": resolved_decl,
                "module": mod_dict,
                "imports": imports,
                "imported_by": imported_by,
                "imported_by_total": imported_by_total,
                "declarations": declarations,
                "horn_clauses": horn_clauses,
                "forensic_hits": forensic_hits,
                "shortest_path_to_main": shortest_path,
                "dominator_chain": dom_chain,
                "tcb_detail": None,
            }
        finally:
            conn.close()

    def _get_tcb_detail(self, conn: sqlite3.Connection, name: str) -> Optional[Dict[str, Any]]:
        if not self._table_exists(conn, "tcb_decls"):
            return None
        row = conn.execute("SELECT * FROM tcb_decls WHERE name = ?", (name,)).fetchone()
        if row is None:
            return None

        deps = [
            {
                "name": r["dst"],
                "edge_kind": r["edge_kind"],
                "kind": r["kind"] or "?",
                "is_definition": bool(r["is_definition"]),
                "depth_from_rh": int(r["depth_from_rh"]) if r["depth_from_rh"] is not None else -1,
                "dom_subtree_size": int(r["dom_subtree_size"] or 0),
                "module_prefix": r["module_prefix"] or "",
            }
            for r in conn.execute(
                "SELECT e.dst, e.edge_kind, d.kind, d.is_definition, d.depth_from_rh, "
                "d.dom_subtree_size, d.module_prefix "
                "FROM tcb_edges e LEFT JOIN tcb_decls d ON d.name = e.dst "
                "WHERE e.src = ? ORDER BY COALESCE(d.is_definition, 0) DESC, COALESCE(d.dom_subtree_size, 0) DESC LIMIT 80",
                (name,),
            )
        ]

        used_by_total = int(
            conn.execute("SELECT COUNT(*) FROM tcb_edges WHERE dst = ?", (name,)).fetchone()[0]
        )
        used_by = [
            {
                "name": r["src"],
                "edge_kind": r["edge_kind"],
                "kind": r["kind"] or "?",
                "is_definition": bool(r["is_definition"]),
                "depth_from_rh": int(r["depth_from_rh"]) if r["depth_from_rh"] is not None else -1,
                "dom_subtree_size": int(r["dom_subtree_size"] or 0),
                "module_prefix": r["module_prefix"] or "",
            }
            for r in conn.execute(
                "SELECT e.src, e.edge_kind, d.kind, d.is_definition, d.depth_from_rh, "
                "d.dom_subtree_size, d.module_prefix "
                "FROM tcb_edges e LEFT JOIN tcb_decls d ON d.name = e.src "
                "WHERE e.dst = ? ORDER BY CASE WHEN COALESCE(d.depth_from_rh, -1) >= 0 THEN d.depth_from_rh ELSE 999 END ASC LIMIT 60",
                (name,),
            )
        ]

        # Reconstruct TCB dominator chain
        dom_chain = [name]
        cur = name
        seen = {cur}
        for _ in range(40):
            r2 = conn.execute("SELECT dom_parent FROM tcb_decls WHERE name = ?", (cur,)).fetchone()
            if not r2 or not r2["dom_parent"] or r2["dom_parent"] in seen:
                break
            nxt = r2["dom_parent"]
            dom_chain.append(nxt)
            seen.add(nxt)
            cur = nxt

        return {
            "found": True,
            "entity_kind": "tcb",
            "name": name,
            "module": None,
            "imports": [],
            "imported_by": [],
            "imported_by_total": 0,
            "declarations": [],
            "horn_clauses": [],
            "forensic_hits": [],
            "shortest_path_to_main": [],
            "dominator_chain": dom_chain,
            "tcb_detail": {
                "name": row["name"],
                "kind": row["kind"],
                "module_prefix": row["module_prefix"],
                "is_definition": bool(row["is_definition"]),
                "expr_nodes": int(row["expr_nodes"]),
                "depth_from_rh": int(row["depth_from_rh"]),
                "depth_from_any": int(row["depth_from_any"]),
                "in_rh_cone": bool(row["in_rh_cone"]),
                "in_grh_cone": bool(row["in_grh_cone"]),
                "dom_parent": row["dom_parent"],
                "dom_subtree_size": int(row["dom_subtree_size"]),
                "fan_in": int(row["fan_in"]),
                "fan_out": int(row["fan_out"]),
                "deps": deps,
                "used_by": used_by,
                "used_by_total": used_by_total,
            },
        }

    # ------------------------------------------------------------------
    # GET /api/subgraph?root=...&mode=imports|horn|taint|tcb&depth=2&max_nodes=80
    # ------------------------------------------------------------------
    def get_subgraph(
        self,
        root: str = "Main",
        mode: str = "imports",
        depth: int = 2,
        max_nodes: int = 60,
    ) -> Dict[str, Any]:
        mode = (mode or "imports").strip().lower()
        depth = max(1, min(int(depth), 4))
        max_nodes = max(10, min(int(max_nodes), 150))
        root = (root or "").strip()

        if not self.db_ready():
            bundle = self._read_json_file("workbench_bundle.json") or {}
            sample = bundle.get("sample_subgraphs", {}).get(mode)
            if sample:
                return sample
            return {"root": root, "mode": mode, "depth": depth, "nodes": [], "edges": [], "truncated": False}

        conn = self._connect()
        try:
            if mode == "imports":
                return self._subgraph_imports(conn, root or "Main", depth, max_nodes)
            if mode == "horn":
                return self._subgraph_horn(conn, root, depth, max_nodes)
            if mode == "taint":
                return self._subgraph_taint(conn, root or "tag:kexactB", depth, max_nodes)
            if mode == "tcb":
                return self._subgraph_tcb(conn, root or "riemannHypothesis", depth, max_nodes)
            return self._subgraph_imports(conn, root or "Main", depth, max_nodes)
        finally:
            conn.close()

    def _subgraph_imports(
        self, conn: sqlite3.Connection, root: str, depth: int, max_nodes: int
    ) -> Dict[str, Any]:
        # Verify root exists; if not, fallback to Main
        rrow = conn.execute("SELECT name FROM modules WHERE name = ?", (root,)).fetchone()
        if rrow is None:
            # Try resolving decl name
            drow = conn.execute("SELECT module FROM declarations WHERE name = ? LIMIT 1", (root,)).fetchone()
            root = drow["module"] if drow else "Main"

        visited: Dict[str, int] = {root: 0}
        queue: collections.deque = collections.deque([(root, 0)])
        truncated = False

        # Always include shortest path to Main if root != Main (gives immediate context)
        path_to_main = self._reconstruct_path_to_main(conn, root)
        path_set = set(path_to_main)
        for idx, pname in enumerate(path_to_main):
            if pname not in visited and len(visited) < max_nodes:
                visited[pname] = -idx

        while queue and len(visited) < max_nodes:
            cur, d = queue.popleft()
            if d >= depth:
                continue

            # Upstream imports (what cur depends on) — prioritize high dom_subtree_size / forensic
            up_rows = conn.execute(
                "SELECT e.dst FROM module_edges e LEFT JOIN modules m ON m.name = e.dst "
                "WHERE e.src = ? ORDER BY COALESCE(m.dom_subtree_size, 0) DESC, COALESCE(m.fan_in, 0) DESC LIMIT 18",
                (cur,),
            ).fetchall()
            for r in up_rows:
                nxt = r["dst"]
                if nxt not in visited:
                    if len(visited) >= max_nodes:
                        truncated = True
                        break
                    visited[nxt] = d + 1
                    queue.append((nxt, d + 1))

            # Downstream importers (who imports cur) — only 1 hop away when root != Main
            if d == 0 and root != "Main" and len(visited) < max_nodes:
                dn_rows = conn.execute(
                    "SELECT e.src FROM module_edges e LEFT JOIN modules m ON m.name = e.src "
                    "WHERE e.dst = ? ORDER BY COALESCE(m.dom_subtree_size, 0) DESC, COALESCE(m.bfs_depth, 999) ASC LIMIT 8",
                    (cur,),
                ).fetchall()
                for r in dn_rows:
                    nxt = r["src"]
                    if nxt not in visited:
                        if len(visited) >= max_nodes:
                            truncated = True
                            break
                        visited[nxt] = -1

        node_names = list(visited.keys())
        placeholders = ",".join("?" for _ in node_names)
        mod_rows: Dict[str, sqlite3.Row] = {}
        for r in conn.execute(
            "SELECT * FROM modules WHERE name IN ({})".format(placeholders), node_names
        ):
            mod_rows[r["name"]] = r

        dom_chain = set(self._reconstruct_dom_chain(conn, root))

        # Fetch all edges among selected nodes
        edges_raw = conn.execute(
            "SELECT src, dst FROM module_edges WHERE src IN ({0}) AND dst IN ({0})".format(placeholders),
            node_names + node_names,
        ).fetchall()

        nodes: List[Dict[str, Any]] = []
        min_layer = min(visited.values()) if visited else 0
        for nm in node_names:
            r = mod_rows.get(nm)
            if not r:
                continue
            flags = safe_json_loads(r["forensic_flags_json"], [])
            nodes.append({
                "id": nm,
                "label": short_label(nm, 30),
                "sublabel": r["namespace_l2"] or r["namespace_top"],
                "kind": "module",
                "role": self._classify_module_role(r),
                "layer": visited[nm] - min_layer,
                "is_root": nm == root,
                "on_dom_spine": nm in dom_chain,
                "on_main_path": nm in path_set,
                "metrics": {
                    "lines": int(r["lines"]),
                    "dom": int(r["dom_subtree_size"]),
                    "fi": int(r["fan_in"]),
                    "fo": int(r["fan_out"]),
                    "decls": int(r["decl_count"]),
                    "depth": int(r["bfs_depth"]),
                },
                "flags": flags,
            })

        edges: List[Dict[str, Any]] = []
        seen_e: Set[Tuple[str, str]] = set()
        for r in edges_raw:
            s, t = r["src"], r["dst"]
            if (s, t) in seen_e:
                continue
            seen_e.add((s, t))
            dst_row = mod_rows.get(t)
            is_dom = bool(dst_row and dst_row["dom_parent"] == s)
            on_path = s in path_set and t in path_set
            edges.append({
                "src": s,
                "dst": t,
                "label": "dom" if is_dom else "imports",
                "kind": "dom" if is_dom else "import",
                "is_dom": is_dom,
                "is_highlight": on_path or is_dom,
            })

        return {
            "root": root,
            "mode": "imports",
            "depth": depth,
            "max_nodes": max_nodes,
            "truncated": truncated,
            "direction_hint": "A → B : module A imports module B (green edges = dominator tree)",
            "nodes": nodes,
            "edges": edges,
        }

    def _subgraph_horn(
        self, conn: sqlite3.Connection, root: str, depth: int, max_nodes: int
    ) -> Dict[str, Any]:
        if not self._table_exists(conn, "horn_edges"):
            return {"root": root, "mode": "horn", "depth": depth, "nodes": [], "edges": [], "truncated": False}

        # Find seed Horn edges: either matching a module, decl_name, proposition, or default top RH spine
        seed_rows: List[sqlite3.Row] = []
        if root and root not in ("Main", "spine", "RH"):
            seed_rows = conn.execute(
                "SELECT * FROM horn_edges WHERE module = ? OR decl_name = ? OR prov_prop = ? OR req_prop = ? LIMIT 40",
                (root, root, root, root),
            ).fetchall()
            if not seed_rows:
                like_r = "%{}%".format(root)
                seed_rows = conn.execute(
                    "SELECT * FROM horn_edges WHERE module LIKE ? OR decl_name LIKE ? OR prov_prop LIKE ? OR req_prop LIKE ? LIMIT 40",
                    (like_r, like_r, like_r, like_r),
                ).fetchall()

        if not seed_rows:
            # Default: the top-level RH/GRH Horn spine around RiemannHypothesis / EveryCharacter / ZeroFreeAll / VWin / Row0b
            seed_props = [
                "RiemannHypothesis",
                "UpperTheory.EveryCharacter",
                "Formalism.HC.ZeroFreeAll",
                "UpperTheory.Top.VWin",
                "UpperTheory.GalStar.Row0b",
                "GlobalTheory.GLq.Green",
                "RiemannZetaZerosOnLine",
                "DirichletLNonvanishingRightOfHalf",
                "DirichletLZerosOnLine",
                "PrimitiveDirichletLZerosOnLine",
            ]
            ph = ",".join("?" for _ in seed_props)
            seed_rows = conn.execute(
                "SELECT * FROM horn_edges WHERE prov_prop IN ({0}) OR req_prop IN ({0}) LIMIT 60".format(ph),
                seed_props + seed_props,
            ).fetchall()

        if not seed_rows:
            # Fallback: highest-dominator Horn edges in DB
            seed_rows = conn.execute(
                "SELECT he.* FROM horn_edges he LEFT JOIN modules m ON m.name = he.module "
                "ORDER BY COALESCE(m.dom_subtree_size, 0) DESC LIMIT 35"
            ).fetchall()

        # Expand across propositions for `depth` hops
        collected_edges: Dict[int, sqlite3.Row] = {int(r["id"]): r for r in seed_rows}
        frontier_props: Set[str] = set()
        for r in seed_rows:
            frontier_props.add(r["req_prop"])
            frontier_props.add(r["prov_prop"])

        seen_props = set(frontier_props)
        truncated = False
        for _ in range(max(0, depth - 1)):
            if not frontier_props or len(collected_edges) >= max_nodes:
                break
            batch = list(frontier_props)[:30]
            ph = ",".join("?" for _ in batch)
            more = conn.execute(
                "SELECT he.* FROM horn_edges he LEFT JOIN modules m ON m.name = he.module "
                "WHERE he.prov_prop IN ({0}) OR he.req_prop IN ({0}) "
                "ORDER BY COALESCE(m.dom_subtree_size, 0) DESC LIMIT ?".format(ph),
                batch + batch + [max_nodes],
            ).fetchall()
            next_frontier: Set[str] = set()
            for r in more:
                eid = int(r["id"])
                if eid not in collected_edges:
                    if len(collected_edges) >= max_nodes:
                        truncated = True
                        break
                    collected_edges[eid] = r
                    for p in (r["req_prop"], r["prov_prop"]):
                        if p not in seen_props:
                            seen_props.add(p)
                            next_frontier.add(p)
            frontier_props = next_frontier

        # Build bipartite-reduced or proposition+theorem logic graph:
        # Group edges by (decl_name, module, prov_prop) so multi-premise theorems render as clean Horn gates!
        gates: Dict[Tuple[str, str], Dict[str, Any]] = {}
        props: Set[str] = set()
        for r in collected_edges.values():
            key = (r["decl_name"], r["module"])
            if key not in gates:
                gates[key] = {
                    "decl_name": r["decl_name"],
                    "module": r["module"],
                    "line_no": int(r["line_no"]),
                    "reqs": [],
                    "prov": r["prov_prop"],
                }
            if r["req_prop"] not in gates[key]["reqs"]:
                gates[key]["reqs"].append(r["req_prop"])
            props.add(r["req_prop"])
            props.add(r["prov_prop"])

        # Cap total nodes cleanly
        nodes: List[Dict[str, Any]] = []
        edges: List[Dict[str, Any]] = []
        node_ids: Set[str] = set()

        # Look up module metrics for gate modules
        mod_list = list({g["module"] for g in gates.values()})
        mod_map: Dict[str, sqlite3.Row] = {}
        if mod_list:
            ph = ",".join("?" for _ in mod_list)
            for r in conn.execute("SELECT name, lines, dom_subtree_size, forensic_flags_json FROM modules WHERE name IN ({})".format(ph), mod_list):
                mod_map[r["name"]] = r

        # Prioritize headline propositions first so they are never truncated out
        def prop_rank(p: str) -> Tuple[int, str]:
            hl = ("RiemannHypothesis", "UpperTheory.EveryCharacter", "Formalism.HC.ZeroFreeAll",
                  "UpperTheory.Top.VWin", "UpperTheory.GalStar.Row0b", "GlobalTheory.GLq.Green", "Hyps")
            for idx, h in enumerate(hl):
                if p == h or p.endswith("." + h):
                    return (idx, p)
            return (100, p)

        # Allocate roughly half the budget to propositions, half to theorem gates
        prop_cap = max(12, max_nodes // 2)
        for p in sorted(props, key=prop_rank):
            if len(nodes) >= prop_cap:
                truncated = True
                break
            pid = "prop:" + p
            node_ids.add(pid)
            is_headline = any(k in p for k in ("RiemannHypothesis", "EveryCharacter", "ZeroFreeAll", "RiemannZetaZeros"))
            nodes.append({
                "id": pid,
                "inspect_name": p,
                "label": short_label(p, 30),
                "sublabel": "Prop / Interface",
                "kind": "horn_prop",
                "role": "entry" if is_headline else "horn_prop",
                "is_root": p == root or (root in ("", "Main", "spine", "RH") and p == "RiemannHypothesis"),
                "on_dom_spine": is_headline,
                "metrics": {},
                "flags": ["prop"],
            })

        # Sort gates by dominator subtree size so top-spine gates always appear
        sorted_gates = sorted(
            gates.values(),
            key=lambda g: (
                0 if "prop:" + g["prov"] in node_ids else 1,
                -(int(mod_map[g["module"]]["dom_subtree_size"]) if g["module"] in mod_map else 0),
                g["decl_name"],
            ),
        )
        for g in sorted_gates:
            if len(nodes) >= max_nodes:
                truncated = True
                break
            if "prop:" + g["prov"] not in node_ids and not any("prop:" + rq in node_ids for rq in g["reqs"]):
                continue
            gid = g["module"] + "::" + g["decl_name"]
            if gid in node_ids:
                continue
            node_ids.add(gid)
            mr = mod_map.get(g["module"])
            nodes.append({
                "id": gid,
                "inspect_name": g["module"],
                "decl_name": g["decl_name"],
                "label": short_label(g["decl_name"], 30),
                "sublabel": short_label(g["module"], 28) + ":" + str(g["line_no"]),
                "kind": "horn_thm",
                "role": "crux" if len(g["reqs"]) >= 2 else "classical",
                "is_root": g["module"] == root or g["decl_name"] == root,
                "on_dom_spine": True,
                "metrics": {
                    "lines": int(mr["lines"]) if mr else 0,
                    "dom": int(mr["dom_subtree_size"]) if mr else 0,
                    "reqs": len(g["reqs"]),
                },
                "flags": safe_json_loads(mr["forensic_flags_json"], []) if mr else [],
            })
            prov_id = "prop:" + g["prov"]
            if prov_id in node_ids:
                edges.append({
                    "src": gid,
                    "dst": prov_id,
                    "label": "PROVES",
                    "kind": "horn_prov",
                    "is_highlight": True,
                })
            for req in g["reqs"]:
                req_id = "prop:" + req
                if req_id in node_ids:
                    edges.append({
                        "src": req_id,
                        "dst": gid,
                        "label": "REQUIRES",
                        "kind": "horn_req",
                        "is_highlight": False,
                    })

        return {
            "root": root or "RiemannHypothesis",
            "mode": "horn",
            "depth": depth,
            "max_nodes": max_nodes,
            "truncated": truncated,
            "direction_hint": "Premise Prop ⇢ (REQUIRES) ⇢ Theorem ⟶ (PROVES) ⟶ Conclusion Prop",
            "nodes": nodes,
            "edges": edges,
        }

    def _subgraph_taint(
        self, conn: sqlite3.Connection, root: str, depth: int, max_nodes: int
    ) -> Dict[str, Any]:
        # Root can be "tag:kexactB", "tag:CutCptCopy", "tag:decide_kernel", "tag:slow_con_leche",
        # "tag:all", "Main" (multi-hotspot overview), or a specific module name.
        hits: List[sqlite3.Row] = []
        tag_filter = ""
        if root in ("", "Main", "tag:all"):
            # Pick representative highest-signal hotspots across all forensic categories
            anchors = [
                "Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.Imports",
                "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LamCopy",
                "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChebyshevPrimeBounds.SmallLoop",
                "Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvFiveLogLeSumInvPrimes",
            ]
            ph_a = ",".join("?" for _ in anchors)
            hits = list(conn.execute(
                "SELECT * FROM forensic_hits WHERE module IN ({}) GROUP BY module".format(ph_a),
                anchors,
            ).fetchall())
            seen_m = {h["module"] for h in hits}
            for tag_pick in ("CutCptCopy", "kcopy", "kexactB", "lean4lean_timeout", "slow_con_leche"):
                for r in conn.execute(
                    "SELECT * FROM forensic_hits WHERE tag = ? ORDER BY hops_to_main ASC, id ASC LIMIT 3",
                    (tag_pick,),
                ):
                    if r["module"] not in seen_m:
                        seen_m.add(r["module"])
                        hits.append(r)
        elif root.startswith("tag:"):
            tag_filter = FLAG_ALIASES.get(root[4:], root[4:])
            hits = conn.execute(
                "SELECT * FROM forensic_hits WHERE tag = ? GROUP BY module ORDER BY hops_to_main ASC, id ASC LIMIT 16",
                (tag_filter,),
            ).fetchall()
        else:
            # Specific module: trace its hits or reconstruct path to Main
            hits = conn.execute(
                "SELECT * FROM forensic_hits WHERE module = ? LIMIT 10", (root,)
            ).fetchall()

        paths: List[Tuple[str, str, List[str]]] = []
        hotspot_mods: Set[str] = set()
        for h in hits:
            p = safe_json_loads(h["shortest_path_to_main_json"], [])
            if not p:
                p = self._reconstruct_path_to_main(conn, h["module"])
            if p:
                paths.append((h["module"], h["tag"], p))
                hotspot_mods.add(h["module"])

        if not paths and root and not root.startswith("tag:"):
            p = self._reconstruct_path_to_main(conn, root)
            if p:
                paths.append((root, "target", p))
                hotspot_mods.add(root)

        if not paths:
            # Fallback: top forensic hits across all tags
            for h in conn.execute("SELECT * FROM forensic_hits ORDER BY hops_to_main ASC LIMIT 12"):
                p = safe_json_loads(h["shortest_path_to_main_json"], []) or self._reconstruct_path_to_main(conn, h["module"])
                if p:
                    paths.append((h["module"], h["tag"], p))
                    hotspot_mods.add(h["module"])

        node_set: Set[str] = set()
        edge_set: Set[Tuple[str, str]] = set()
        truncated = False
        for _mod, _tag, p in paths:
            new_cnt = sum(1 for nm in p if nm not in node_set)
            if len(node_set) + new_cnt > max_nodes and len(node_set) > 0:
                truncated = True
                continue
            for nm in p:
                node_set.add(nm)
            # p is [hotspot, ..., Main] where p[i+1] imports p[i]
            # In taint flow: taint flows from hotspot p[i] UP into importer p[i+1]
            for i in range(len(p) - 1):
                edge_set.add((p[i], p[i + 1]))

        if not node_set:
            return {"root": root, "mode": "taint", "depth": depth, "nodes": [], "edges": [], "truncated": False}

        node_names = list(node_set)
        ph = ",".join("?" for _ in node_names)
        mod_map: Dict[str, sqlite3.Row] = {}
        for r in conn.execute("SELECT * FROM modules WHERE name IN ({})".format(ph), node_names):
            mod_map[r["name"]] = r

        nodes: List[Dict[str, Any]] = []
        for nm in node_names:
            r = mod_map.get(nm)
            flags = safe_json_loads(r["forensic_flags_json"], []) if r else []
            role = "entry" if nm == "Main" else ("forensic" if nm in hotspot_mods else (self._classify_module_role(r) if r else "normal"))
            nodes.append({
                "id": nm,
                "label": short_label(nm, 30),
                "sublabel": (r["namespace_l2"] or r["namespace_top"]) if r else "",
                "kind": "forensic" if nm in hotspot_mods else "module",
                "role": role,
                "is_root": nm in hotspot_mods or nm == root,
                "on_dom_spine": True,
                "on_main_path": True,
                "metrics": {
                    "lines": int(r["lines"]) if r else 0,
                    "dom": int(r["dom_subtree_size"]) if r else 0,
                    "fi": int(r["fan_in"]) if r else 0,
                    "fo": int(r["fan_out"]) if r else 0,
                    "depth": int(r["bfs_depth"]) if r else 0,
                },
                "flags": flags,
            })

        edges = [
            {
                "src": s,
                "dst": t,
                "label": "imported by",
                "kind": "taint",
                "is_highlight": True,
            }
            for (s, t) in sorted(edge_set)
        ]

        return {
            "root": root,
            "mode": "taint",
            "depth": depth,
            "max_nodes": max_nodes,
            "truncated": truncated,
            "direction_hint": "Hotspot ⟶ (imported by) ⟶ … ⟶ Main  (shortest dependency propagation paths)",
            "nodes": nodes,
            "edges": edges,
        }

    def _subgraph_tcb(
        self, conn: sqlite3.Connection, root: str, depth: int, max_nodes: int
    ) -> Dict[str, Any]:
        if not self._table_exists(conn, "tcb_decls"):
            return {"root": root, "mode": "tcb", "depth": depth, "nodes": [], "edges": [], "truncated": False}

        rrow = conn.execute("SELECT name FROM tcb_decls WHERE name = ?", (root,)).fetchone()
        if rrow is None:
            # Try suffix match (e.g., RiemannHypothesis -> RiemannHypothesis)
            rrow = conn.execute(
                "SELECT name FROM tcb_decls WHERE name LIKE ? ORDER BY is_definition DESC, dom_subtree_size DESC LIMIT 1",
                ("%" + root + "%",),
            ).fetchone()
            root = rrow["name"] if rrow else "riemannHypothesis"

        visited: Dict[str, int] = {root: 0}
        queue: collections.deque = collections.deque([(root, 0)])
        truncated = False

        while queue and len(visited) < max_nodes:
            cur, d = queue.popleft()
            if d >= depth:
                continue
            # Prioritize DEFINITIONS over theorems so the human-auditable semantic TCB surfaces first!
            dep_rows = conn.execute(
                "SELECT e.dst FROM tcb_edges e LEFT JOIN tcb_decls t ON t.name = e.dst "
                "WHERE e.src = ? ORDER BY COALESCE(t.is_definition, 0) DESC, "
                "CASE WHEN e.edge_kind IN ('type','both') THEN 0 ELSE 1 END, "
                "COALESCE(t.dom_subtree_size, 0) DESC LIMIT 16",
                (cur,),
            ).fetchall()
            for r in dep_rows:
                nxt = r["dst"]
                if nxt not in visited:
                    if len(visited) >= max_nodes:
                        truncated = True
                        break
                    visited[nxt] = d + 1
                    queue.append((nxt, d + 1))

            if d == 0 and len(visited) < max_nodes:
                up_rows = conn.execute(
                    "SELECT e.src FROM tcb_edges e LEFT JOIN tcb_decls t ON t.name = e.src "
                    "WHERE e.dst = ? ORDER BY CASE WHEN COALESCE(t.depth_from_rh,-1) >= 0 THEN t.depth_from_rh ELSE 999 END ASC LIMIT 6",
                    (cur,),
                ).fetchall()
                for r in up_rows:
                    nxt = r["src"]
                    if nxt not in visited:
                        if len(visited) >= max_nodes:
                            truncated = True
                            break
                        visited[nxt] = -1

        names = list(visited.keys())
        ph = ",".join("?" for _ in names)
        tmap: Dict[str, sqlite3.Row] = {}
        for r in conn.execute("SELECT * FROM tcb_decls WHERE name IN ({})".format(ph), names):
            tmap[r["name"]] = r

        edges_raw = conn.execute(
            "SELECT src, dst, edge_kind FROM tcb_edges WHERE src IN ({0}) AND dst IN ({0})".format(ph),
            names + names,
        ).fetchall()

        min_l = min(visited.values()) if visited else 0
        nodes: List[Dict[str, Any]] = []
        for nm in names:
            r = tmap.get(nm)
            if not r:
                continue
            is_def = bool(r["is_definition"])
            is_hl = nm in (
                "riemannHypothesis",
                "riemannZeta_eq_zero_re",
                "LFunction_ne_zero_of_half_lt_re",
                "LFunction_eq_zero_re",
                "LFunction_eq_zero_re_of_isPrimitive",
                "RiemannHypothesis",
            )
            role = "entry" if is_hl else ("forensic" if r["kind"] == "axiom" else ("tcb_def" if is_def else "tcb_thm"))
            nodes.append({
                "id": nm,
                "label": short_label(nm, 30),
                "sublabel": "{} · {}".format(r["kind"], short_label(r["module_prefix"], 22)),
                "kind": "tcb_def" if is_def else "tcb_thm",
                "role": role,
                "layer": visited[nm] - min_l,
                "is_root": nm == root,
                "on_dom_spine": r["dom_parent"] in tmap or is_hl,
                "metrics": {
                    "dom": int(r["dom_subtree_size"]),
                    "fi": int(r["fan_in"]),
                    "fo": int(r["fan_out"]),
                    "depth": int(r["depth_from_rh"]),
                    "expr": int(r["expr_nodes"]),
                },
                "flags": [r["kind"]],
            })

        edges: List[Dict[str, Any]] = []
        for r in edges_raw:
            dst_r = tmap.get(r["dst"])
            is_dom = bool(dst_r and dst_r["dom_parent"] == r["src"])
            ek = r["edge_kind"]
            if ek == "value":
                edge_cls = "tcb_val"
            elif is_dom:
                edge_cls = "dom"
            else:
                edge_cls = "tcb"
            edges.append({
                "src": r["src"],
                "dst": r["dst"],
                "label": ek,
                "kind": edge_cls,
                "is_dom": is_dom,
                "is_highlight": is_dom or ek in ("type", "both"),
            })

        return {
            "root": root,
            "mode": "tcb",
            "depth": depth,
            "max_nodes": max_nodes,
            "truncated": truncated,
            "direction_hint": "A → B : solid = statement type dep, dashed = proof value stub (e.g. sorryAx)",
            "nodes": nodes,
            "edges": edges,
        }

    # ------------------------------------------------------------------
    # GET /api/investigations
    # ------------------------------------------------------------------
    def get_investigations(self) -> Dict[str, Any]:
        bundle = self._read_json_file("workbench_bundle.json") or {}
        if bundle.get("investigations"):
            return {"investigations": bundle["investigations"], "source": "workbench_bundle.json"}

        # Dynamic fallback built straight from SQLite if bundle isn't present
        return {
            "source": "server_default",
            "investigations": [
                {
                    "id": "recon_main",
                    "title": "1. Recon main()",
                    "subtitle": "Main.lean → Statements → RhOfRight → Horn spine",
                    "mode": "imports",
                    "root": "Main",
                    "view": "graph",
                    "steps": [
                        {
                            "title": "Start at Main.lean",
                            "mode": "imports",
                            "root": "Main",
                            "depth": 2,
                            "focus_node": "Main",
                            "right_tab": "decompiled",
                            "provenance": "L",
                            "text": "Every RE audit starts at the entry point. Main.lean is 12 lines exporting 5 headline theorems against Mathlib definitions.",
                        },
                        {
                            "title": "Inspect Statements.lean (the spec)",
                            "mode": "imports",
                            "root": "Main",
                            "depth": 2,
                            "focus_node": "Statements",
                            "right_tab": "explain",
                            "provenance": "L",
                            "text": "Statements.lean imports ONLY Mathlib — locking the specification to Mathlib's RiemannHypothesis and DirichletCharacter.LFunction.",
                        },
                        {
                            "title": "Read the 62-line reflection adapter",
                            "mode": "imports",
                            "root": "Formalism.GammaFactorNonvanishing.RhOfRight",
                            "depth": 1,
                            "focus_node": "Formalism.GammaFactorNonvanishing.RhOfRight",
                            "right_tab": "decompiled",
                            "provenance": "L",
                            "text": "RhOfRight.lean reduces RiemannHypothesis to non-vanishing for Re(s) > 1/2 via Mathlib's functional equation.",
                        },
                        {
                            "title": "Switch to Horn-Skeleton Logic Flow",
                            "mode": "horn",
                            "root": "RiemannHypothesis",
                            "depth": 2,
                            "focus_node": "prop:RiemannHypothesis",
                            "right_tab": "decompiled",
                            "provenance": "L",
                            "text": "The top of the proof uses dependency injection (REQUIRES A ∧ B ⟹ PROVES C), turning module soup into a readable logical circuit.",
                        },
                    ],
                },
                {
                    "id": "tcb_xray",
                    "title": "2. TCB X-Ray",
                    "subtitle": "51,692 real challenge.ndjson declarations",
                    "mode": "tcb",
                    "root": "riemannHypothesis",
                    "view": "graph",
                    "steps": [
                        {
                            "title": "The Semantic TCB root: riemannHypothesis",
                            "mode": "tcb",
                            "root": "riemannHypothesis",
                            "depth": 2,
                            "focus_node": "riemannHypothesis",
                            "right_tab": "forensics",
                            "provenance": "L",
                            "text": "Even after nanoda & con-leche verify the proof, a human must trust the definitions inside challenge.ndjson (51,692 total declarations).",
                        },
                        {
                            "title": "Audit riemannZeta",
                            "mode": "tcb",
                            "root": "riemannZeta",
                            "depth": 2,
                            "focus_node": "riemannZeta",
                            "right_tab": "explain",
                            "provenance": "L",
                            "text": "Only definitions (not kernel-checked theorems) carry semantic meaning. Trace riemannZeta into HurwitzZeta and Mellin transforms.",
                        },
                        {
                            "title": "Audit DirichletCharacter.LFunction (GRH scope)",
                            "mode": "tcb",
                            "root": "DirichletCharacter.LFunction",
                            "depth": 2,
                            "focus_node": "DirichletCharacter.LFunction",
                            "right_tab": "explain",
                            "provenance": "L",
                            "text": "GRH in this archive covers Dirichlet L-functions only — not Dedekind zeta or general Hecke L-functions.",
                        },
                    ],
                },
                {
                    "id": "ai_forensics",
                    "title": "3. AI Proof Forensics",
                    "subtitle": "kexactB, CutCptCopy, decide +kernel, slowest con-leche",
                    "mode": "taint",
                    "root": "tag:kexactB",
                    "view": "graph",
                    "steps": [
                        {
                            "title": "Elaborator-bypass taint: kexactB",
                            "mode": "taint",
                            "root": "tag:kexactB",
                            "depth": 3,
                            "focus_node": "Main",
                            "right_tab": "forensics",
                            "provenance": "L",
                            "text": "kexactB assigns elaborated terms directly to goals without elaborator type-checking — leaving the kernel as the sole soundness barrier.",
                        },
                        {
                            "title": "Declaration-copying metaprogram: CutCptCopy",
                            "mode": "taint",
                            "root": "tag:CutCptCopy",
                            "depth": 3,
                            "focus_node": "Main",
                            "right_tab": "forensics",
                            "provenance": "L",
                            "text": "CutCptCopy invokes addDecl to duplicate declarations programmatically; shortest path shows how it reaches Main.",
                        },
                        {
                            "title": "Kernel compute tables: decide +kernel timeouts",
                            "mode": "taint",
                            "root": "tag:lean4lean_timeout",
                            "depth": 3,
                            "focus_node": "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChebyshevPrimeBounds.SmallLoop",
                            "right_tab": "explain",
                            "provenance": "L",
                            "text": "5 modules hit default fuel limits in lean4lean because they evaluate finite prime/interval computations inside the kernel via decide +kernel.",
                        },
                        {
                            "title": "Slowest con-leche checks: lam_copy (55.2s)",
                            "mode": "taint",
                            "root": "tag:slow_con_leche",
                            "depth": 3,
                            "focus_node": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LamCopy",
                            "right_tab": "explain",
                            "provenance": "L",
                            "text": "Checker logs act like a CPU profiler: lam_copy and sigSpan_copy dominate con-leche replay time.",
                        },
                    ],
                },
                {
                    "id": "namespace_reality",
                    "title": "4. Namespace Reality",
                    "subtitle": "All 175,187 files — why directory names lie",
                    "mode": "imports",
                    "root": "Main",
                    "view": "treemap",
                    "steps": [
                        {
                            "title": "175,187 files by folder — the giant misnomer",
                            "mode": "imports",
                            "root": "Main",
                            "depth": 1,
                            "view": "treemap",
                            "focus_node": "Main",
                            "right_tab": "explain",
                            "provenance": "L",
                            "text": "Development/AbelianVarietyTheory holds ~99,187 files (>56% of the entire proof!), yet its inner declarations are mostly p-adic GL_n rep theory & theta-chain code.",
                        },
                        {
                            "title": "Misfiled prime table inside DivisorProofs",
                            "mode": "imports",
                            "root": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvFiveLogLeSumInvPrimes",
                            "depth": 1,
                            "view": "graph",
                            "focus_node": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvFiveLogLeSumInvPrimes",
                            "right_tab": "forensics",
                            "provenance": "L",
                            "text": "Even GlobalTheory.PrimeRecip.table_ok (a 17.2s decide +kernel prime reciprocal table) is filed under AbelianVarietyTheory/Proofs/DivisorProofs/.",
                        },
                    ],
                },
            ],
        }


def make_handler(store: LeanREStore, p3: "phase3.Phase3", p4: Optional["phase4.Phase4"] = None):
    class WorkbenchHandler(BaseHTTPRequestHandler):
        def log_message(self, fmt: str, *args: Any) -> None:
            # Quiet structured request logging to stderr
            sys.stderr.write("[leanre-ui] %s - %s\n" % (self.address_string(), fmt % args))

        def _send_json(self, obj: Any, status: int = 200) -> None:
            raw = json.dumps(obj, ensure_ascii=False).encode("utf-8")
            self.send_response(status)
            self.send_header("Content-Type", "application/json; charset=utf-8")
            self.send_header("Content-Length", str(len(raw)))
            self.send_header("Cache-Control", "no-store")
            self.end_headers()
            self.wfile.write(raw)

        def _send_file(self, path: Path) -> None:
            if not path.is_file():
                self.send_error(HTTPStatus.NOT_FOUND, "Not found")
                return
            ctype, _ = mimetypes.guess_type(str(path))
            if path.suffix == ".js":
                ctype = "application/javascript; charset=utf-8"
            elif path.suffix == ".css":
                ctype = "text/css; charset=utf-8"
            elif path.suffix == ".html":
                ctype = "text/html; charset=utf-8"
            elif path.suffix == ".json":
                ctype = "application/json; charset=utf-8"
            else:
                ctype = ctype or "application/octet-stream"
            raw = path.read_bytes()
            self.send_response(HTTPStatus.OK)
            self.send_header("Content-Type", ctype)
            self.send_header("Content-Length", str(len(raw)))
            self.send_header("Cache-Control", "no-cache")
            self.end_headers()
            self.wfile.write(raw)

        def do_GET(self) -> None:
            parsed = urlparse(self.path)
            path = parsed.path
            qs = parse_qs(parsed.query)

            def q1(key: str, default: str = "") -> str:
                vals = qs.get(key)
                return vals[0] if vals else default

            try:
                # API routes
                if path == "/api/health":
                    self._send_json({
                        "ok": True,
                        "db_ready": store.db_ready(),
                        "project_name": store.project_config.get("name", ""),
                        "ts": time.time(),
                    })
                    return
                if path == "/api/overview":
                    self._send_json(store.get_overview())
                    return
                if path == "/api/search":
                    self._send_json(
                        store.search(
                            q=q1("q"),
                            kind=q1("kind", "all"),
                            flag=q1("flag"),
                            ns=q1("ns"),
                            limit=int(q1("limit", "50") or "50"),
                        )
                    )
                    return
                if path == "/api/module":
                    self._send_json(store.get_module(name=q1("name"), kind=q1("kind")))
                    return
                if path == "/api/subgraph":
                    self._send_json(
                        store.get_subgraph(
                            root=q1("root"),
                            mode=q1("mode", "imports"),
                            depth=int(q1("depth", "2") or "2"),
                            max_nodes=int(q1("max_nodes", "60") or "60"),
                        )
                    )
                    return
                if path == "/api/investigations":
                    self._send_json(store.get_investigations())
                    return
                if path.startswith(P3_PREFIXES):
                    try:
                        res = p4.handle_get(path, q1) if p4 is not None else None
                        if res is None:
                            res = p3.handle_get(path, q1)
                    except phase3.ApiError as err:
                        self._send_json({"error": err.message}, status=err.status)
                        return
                    if isinstance(res, phase3.RawResponse):
                        self._send_raw(res)
                    else:
                        self._send_json(res)
                    return
                if path.startswith("/api/"):
                    self._send_json({"error": "unknown API route"}, status=404)
                    return

                # Static routes inside workbench/
                if path in ("/", "/index.html"):
                    self._send_file(WORKBENCH_DIR / "index.html")
                    return

                # Allow seamless relative link to playable math labs in prototypes/
                if path == "/prototypes/concept_map_demo.html":
                    self._send_file(PROTOTYPES_DIR / "concept_map_demo.html")
                    return

                # Allow bundle fetch
                if path == "/outputs/workbench_bundle.json":
                    self._send_file(store.outputs_dir / "workbench_bundle.json")
                    return

                # Safe static asset lookup strictly within WORKBENCH_DIR
                rel = path.lstrip("/")
                if ".." in rel or rel.startswith("/"):
                    self.send_error(HTTPStatus.FORBIDDEN, "Forbidden")
                    return
                candidate = (WORKBENCH_DIR / rel).resolve()
                if WORKBENCH_DIR.resolve() not in candidate.parents:
                    self.send_error(HTTPStatus.FORBIDDEN, "Forbidden")
                    return
                if candidate.suffix not in STATIC_EXTS or any(part.startswith(".") for part in Path(rel).parts):
                    self.send_error(HTTPStatus.NOT_FOUND, "Not found")
                    return
                self._send_file(candidate)
            except Exception as exc:
                self._send_json({"error": str(exc)}, status=500)

        def _send_raw(self, res: "phase3.RawResponse") -> None:
            self.send_response(res.status)
            self.send_header("Content-Type", res.content_type)
            self.send_header("Content-Length", str(len(res.body)))
            self.send_header("Cache-Control", "no-store")
            self.send_header("X-Content-Type-Options", "nosniff")
            if res.filename:
                self.send_header("Content-Disposition", 'attachment; filename="{}"'.format(res.filename))
            self.end_headers()
            self.wfile.write(res.body)

        def _write_request_allowed(self) -> Optional[str]:
            """Writes are same-origin only: loopback Host, matching Origin, custom header
            (a cross-site page cannot send X-Leanre-Write without a CORS preflight, which
            this server never answers)."""
            port = self.server.server_address[1]
            allowed_hosts = {"127.0.0.1:%d" % port, "localhost:%d" % port}
            host = self.headers.get("Host", "")
            if host not in allowed_hosts:
                return "Host not allowed"
            origin = self.headers.get("Origin")
            if origin is not None and origin not in {"http://" + h for h in allowed_hosts}:
                return "cross-origin write refused"
            if self.headers.get("X-Leanre-Write") != "1":
                return "missing X-Leanre-Write header"
            return None

        def do_POST(self) -> None:
            parsed = urlparse(self.path)
            path = parsed.path
            qs = parse_qs(parsed.query)

            def q1(key: str, default: str = "") -> str:
                vals = qs.get(key)
                return vals[0] if vals else default

            try:
                if not path.startswith("/api/annot/"):
                    self._send_json({"error": "POST is only accepted on /api/annot/*"}, status=404)
                    return
                why = self._write_request_allowed()
                if why:
                    self._send_json({"error": why}, status=403)
                    return
                raw_len = self.headers.get("Content-Length", "")
                if not raw_len.isdigit():
                    self._send_json({"error": "Content-Length required"}, status=411)
                    return
                if int(raw_len) > MAX_POST_BYTES:
                    self._send_json({"error": "body too large"}, status=413)
                    return
                body = self.rfile.read(int(raw_len))
                try:
                    res = p3.handle_post(path, q1, body)
                except phase3.ApiError as err:
                    self._send_json({"error": err.message}, status=err.status)
                    return
                self._send_json(res)
            except Exception as exc:
                self._send_json({"error": str(exc)}, status=500)

    return WorkbenchHandler


def main() -> None:
    parser = argparse.ArgumentParser(description="leanre Ghidra-for-Lean interactive workbench server")
    parser.add_argument("--host", default="127.0.0.1", help="Bind host (default 127.0.0.1)")
    parser.add_argument("--port", type=int, default=8420, help="Bind port (default 8420)")
    parser.add_argument("--db", default=str(DEFAULT_OUTPUTS_DIR / "leanre.db"), help="Path to leanre.db")
    parser.add_argument("--outputs", default=str(DEFAULT_OUTPUTS_DIR), help="Path to outputs/ directory")
    parser.add_argument("--annotations", default=str(DEFAULT_ANNOTATIONS_DIR),
                        help="Annotation-pack directory (the ONLY place this server writes)")
    parser.add_argument("--config", default=None, help="Optional path to leanre.toml profile")
    parser.add_argument("--src-root", default=None, help="Optional Lean source directory for live hygiene/bundles")
    parser.add_argument("--fixtures", action="store_true",
                        help="Serve SYNTHETIC fixtures for Phase 3 sources that are not built yet "
                             "(the UI shows a permanent banner). Default: show 'not built yet'.")
    args = parser.parse_args()

    outputs_path = Path(args.outputs)
    proj_cfg = load_project_config(config_path=args.config, outputs_dir=outputs_path)
    src_root_path = Path(args.src_root) if args.src_root else None

    store = LeanREStore(db_path=Path(args.db), outputs_dir=outputs_path, project_config=proj_cfg)
    p3 = phase3.Phase3(
        project_root=PROJECT_ROOT,
        outputs_dir=outputs_path,
        annotations_dir=Path(args.annotations),
        fixtures=args.fixtures,
    )
    p4 = phase4.Phase4(p3, project_config=proj_cfg, src_root=src_root_path)
    server = ThreadingHTTPServer((args.host, args.port), make_handler(store, p3, p4))
    print(
        "leanre workbench serving http://{}:{}  (db={}, ready={})".format(
            args.host, args.port, args.db, store.db_ready()
        ),
        flush=True,
    )
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\nShutting down.", flush=True)
    finally:
        server.server_close()


if __name__ == "__main__":
    main()
