#!/usr/bin/env python3
"""SQLite schema and bulk-loading helpers for leanre (outputs/leanre.db)."""
from __future__ import annotations

import json
import sqlite3
from typing import Any, Dict

FORENSIC_FLAGS: Dict[str, int] = {
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

FORENSIC_SEVERITY: Dict[str, str] = {
    "kexactB": "audit",
    "kcopy": "audit",
    "CutCptCopy": "audit",
    "addDecl": "audit",
    "run_tac": "interesting",
    "decide_kernel": "interesting",
    "positivity_ext": "info",
    "BuildAid": "info",
    "OpenLiteratureStatements": "interesting",
    "slow_con_leche": "interesting",
    "lean4lean_timeout": "interesting",
    "sorry": "critical",
    "axiom": "critical",
    "native_decide": "critical",
    "unsafe": "critical",
    "implemented_by": "critical",
}

SCHEMA_SQL = """
CREATE TABLE IF NOT EXISTS meta (
    key TEXT PRIMARY KEY,
    value_json TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS modules (
    id INTEGER PRIMARY KEY,
    name TEXT UNIQUE NOT NULL,
    file_path TEXT NOT NULL,
    namespace_top TEXT NOT NULL,
    namespace_l2 TEXT NOT NULL,
    lines INTEGER NOT NULL,
    lines_wc INTEGER NOT NULL,
    bytes INTEGER NOT NULL,
    trailing_nl INTEGER NOT NULL,
    decl_count INTEGER NOT NULL,
    thm_count INTEGER NOT NULL,
    def_count INTEGER NOT NULL,
    import_count INTEGER NOT NULL,
    imports_mathlib INTEGER NOT NULL,
    fan_in INTEGER NOT NULL,
    fan_out INTEGER NOT NULL,
    bfs_depth INTEGER NOT NULL,
    bottom_depth INTEGER NOT NULL,
    parent_to_main TEXT,
    dom_parent TEXT,
    dom_subtree_size INTEGER NOT NULL,
    dom_subtree_lines INTEGER NOT NULL,
    rev_reach INTEGER NOT NULL,
    is_shim INTEGER NOT NULL,
    dup_imports INTEGER NOT NULL,
    clone_sig TEXT,
    clone_cluster_size INTEGER NOT NULL,
    zlib_ratio REAL NOT NULL,
    forensic_flags_bitmask INTEGER NOT NULL,
    forensic_flags_json TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS module_edges (
    src TEXT NOT NULL,
    dst TEXT NOT NULL,
    PRIMARY KEY (src, dst)
);

CREATE TABLE IF NOT EXISTS declarations (
    id INTEGER PRIMARY KEY,
    name TEXT NOT NULL,
    kind TEXT NOT NULL,
    module TEXT NOT NULL,
    line_no INTEGER NOT NULL,
    signature_snippet TEXT NOT NULL,
    horn_requires_json TEXT NOT NULL,
    horn_proves TEXT,
    forensic_tags TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS horn_edges (
    id INTEGER PRIMARY KEY,
    req_prop TEXT NOT NULL,
    prov_prop TEXT NOT NULL,
    decl_id INTEGER NOT NULL,
    decl_name TEXT NOT NULL,
    module TEXT NOT NULL,
    line_no INTEGER NOT NULL
);

CREATE TABLE IF NOT EXISTS forensic_hits (
    id INTEGER PRIMARY KEY,
    tag TEXT NOT NULL,
    severity TEXT NOT NULL,
    module TEXT NOT NULL,
    line_no INTEGER NOT NULL,
    decl_name TEXT,
    snippet TEXT NOT NULL,
    hops_to_main INTEGER NOT NULL,
    shortest_path_to_main_json TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS tcb_decls (
    id INTEGER PRIMARY KEY,
    name TEXT UNIQUE NOT NULL,
    kind TEXT NOT NULL,
    module_prefix TEXT NOT NULL,
    is_definition INTEGER NOT NULL,
    expr_nodes INTEGER NOT NULL,
    depth_from_rh INTEGER NOT NULL,
    depth_from_any INTEGER NOT NULL,
    in_rh_cone INTEGER NOT NULL,
    in_grh_cone INTEGER NOT NULL,
    dom_parent TEXT,
    dom_subtree_size INTEGER NOT NULL,
    fan_in INTEGER NOT NULL,
    fan_out INTEGER NOT NULL
);

CREATE TABLE IF NOT EXISTS tcb_edges (
    src TEXT NOT NULL,
    dst TEXT NOT NULL,
    edge_kind TEXT NOT NULL,
    PRIMARY KEY (src, dst)
);

CREATE TABLE IF NOT EXISTS namespace_stats (
    prefix TEXT PRIMARY KEY,
    depth INTEGER NOT NULL,
    parent TEXT,
    module_count INTEGER NOT NULL,
    lines_wc INTEGER NOT NULL,
    lines_eof INTEGER NOT NULL,
    bytes INTEGER NOT NULL,
    decl_count INTEGER NOT NULL,
    thm_count INTEGER NOT NULL,
    def_count INTEGER NOT NULL,
    shim_count INTEGER NOT NULL,
    mathlib_import_count INTEGER NOT NULL,
    forensic_hit_count INTEGER NOT NULL,
    top_decl_prefixes_json TEXT NOT NULL
);
"""

INDEX_SQL_SCAN = """
CREATE INDEX IF NOT EXISTS idx_modules_name_nocase ON modules(name COLLATE NOCASE);
CREATE INDEX IF NOT EXISTS idx_modules_ns_top ON modules(namespace_top);
CREATE INDEX IF NOT EXISTS idx_modules_ns_l2 ON modules(namespace_l2);
CREATE INDEX IF NOT EXISTS idx_modules_dom_parent ON modules(dom_parent);
CREATE INDEX IF NOT EXISTS idx_modules_dom_size ON modules(dom_subtree_size DESC);
CREATE INDEX IF NOT EXISTS idx_modules_fan_in ON modules(fan_in DESC);
CREATE INDEX IF NOT EXISTS idx_modules_flags ON modules(forensic_flags_bitmask);
CREATE INDEX IF NOT EXISTS idx_modules_clone ON modules(clone_sig);

CREATE INDEX IF NOT EXISTS idx_mod_edges_dst ON module_edges(dst);

CREATE INDEX IF NOT EXISTS idx_decls_name ON declarations(name);
CREATE INDEX IF NOT EXISTS idx_decls_name_nocase ON declarations(name COLLATE NOCASE);
CREATE INDEX IF NOT EXISTS idx_decls_module ON declarations(module);
CREATE INDEX IF NOT EXISTS idx_decls_horn_proves ON declarations(horn_proves);
CREATE INDEX IF NOT EXISTS idx_decls_kind ON declarations(kind);

CREATE INDEX IF NOT EXISTS idx_horn_req ON horn_edges(req_prop);
CREATE INDEX IF NOT EXISTS idx_horn_prov ON horn_edges(prov_prop);
CREATE INDEX IF NOT EXISTS idx_horn_mod ON horn_edges(module);

CREATE INDEX IF NOT EXISTS idx_hits_tag ON forensic_hits(tag);
CREATE INDEX IF NOT EXISTS idx_hits_mod ON forensic_hits(module);
"""

INDEX_SQL_TCB = """
CREATE INDEX IF NOT EXISTS idx_tcb_name_nocase ON tcb_decls(name COLLATE NOCASE);
CREATE INDEX IF NOT EXISTS idx_tcb_prefix ON tcb_decls(module_prefix);
CREATE INDEX IF NOT EXISTS idx_tcb_is_def ON tcb_decls(is_definition);
CREATE INDEX IF NOT EXISTS idx_tcb_depth_rh ON tcb_decls(depth_from_rh);
CREATE INDEX IF NOT EXISTS idx_tcb_dom_parent ON tcb_decls(dom_parent);
CREATE INDEX IF NOT EXISTS idx_tcb_dom_size ON tcb_decls(dom_subtree_size DESC);
CREATE INDEX IF NOT EXISTS idx_tcb_fan_in ON tcb_decls(fan_in DESC);

CREATE INDEX IF NOT EXISTS idx_tcb_edges_dst ON tcb_edges(dst);
CREATE INDEX IF NOT EXISTS idx_tcb_edges_kind ON tcb_edges(edge_kind);
"""


def open_db(path: str, bulk_mode: bool = False) -> sqlite3.Connection:
    conn = sqlite3.connect(path)
    if bulk_mode:
        conn.execute("PRAGMA journal_mode = MEMORY;")
        conn.execute("PRAGMA synchronous = OFF;")
        conn.execute("PRAGMA temp_store = MEMORY;")
        conn.execute("PRAGMA cache_size = -131072;")
    else:
        conn.execute("PRAGMA cache_size = -65536;")
    conn.executescript(SCHEMA_SQL)
    return conn


def finalize_db(conn: sqlite3.Connection) -> None:
    conn.commit()
    conn.execute("ANALYZE;")
    conn.commit()
    conn.execute("PRAGMA synchronous = FULL;")
    conn.execute("PRAGMA journal_mode = DELETE;")


def set_meta(conn: sqlite3.Connection, key: str, value: Any) -> None:
    conn.execute(
        "INSERT OR REPLACE INTO meta(key, value_json) VALUES (?, ?)",
        (key, json.dumps(value, ensure_ascii=False)),
    )


def get_meta(conn: sqlite3.Connection, key: str, default: Any = None) -> Any:
    row = conn.execute("SELECT value_json FROM meta WHERE key = ?", (key,)).fetchone()
    return json.loads(row[0]) if row else default


def flags_to_bitmask(tags: Any) -> int:
    mask = 0
    for t in tags:
        mask |= FORENSIC_FLAGS.get(t, 0)
    return mask
