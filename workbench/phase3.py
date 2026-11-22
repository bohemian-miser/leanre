#!/usr/bin/env python3
"""
Phase 3 workbench backend: kernel-exact, FLIRT and annotation-pack APIs.

Design rules (docs/PHASE3_GATES.md W1-W2):
  * Analysis databases (outputs/kernel/kernel.db, outputs/flirt/*.db) are
    opened READ-ONLY (sqlite URI mode=ro) and queried with parameterized SQL
    only. Table/column identifiers are fixed literals in this file; nothing
    from a request is ever interpolated into SQL text.
  * The only writes this server ever performs go through leanre/annot.py and
    land under annotations/ (layer ids are validated and path-confined).
  * Every source is in exactly one state:
        ready    real extracted data            -> provenance [L]
        fixture  synthetic stand-in (--fixtures)-> permanent banner in the UI
        absent   producer has not built it yet  -> "not built yet" panel
  * Stdlib only.
"""
from __future__ import annotations

import json
import os
import re
import sqlite3
import sys
import threading
from pathlib import Path
from typing import Any, Callable, Dict, List, Optional, Tuple

import p3_fixtures

MAX_LIMIT = 500
ROOT_UNION = "union"


class ApiError(Exception):
    """Raised for client errors; carries the HTTP status to send."""

    def __init__(self, status: int, message: str) -> None:
        super().__init__(message)
        self.status = status
        self.message = message


class RawResponse:
    """Non-JSON response (annotation pack download)."""

    def __init__(self, body: bytes, content_type: str, filename: str = "", status: int = 200) -> None:
        self.body = body
        self.content_type = content_type
        self.filename = filename
        self.status = status


def clamp_int(raw: str, default: int, lo: int, hi: int, name: str) -> int:
    if raw is None or raw == "":
        return default
    if not re.fullmatch(r"-?\d{1,9}", raw):
        raise ApiError(400, "parameter '%s' must be an integer" % name)
    return max(lo, min(hi, int(raw)))


def one_of(raw: str, allowed: List[str], default: str, name: str) -> str:
    if raw is None or raw == "":
        return default
    if raw not in allowed:
        raise ApiError(400, "parameter '%s' must be one of: %s" % (name, ", ".join(allowed)))
    return raw


def like_escape(q: str) -> str:
    """Escape LIKE wildcards; use with  LIKE ? ESCAPE '\\'  and a bound parameter."""
    return q.replace("\\", "\\\\").replace("%", "\\%").replace("_", "\\_")


def ro_connect(path: Path) -> sqlite3.Connection:
    conn = sqlite3.connect("file:{}?mode=ro".format(path.as_posix()), uri=True, timeout=10.0)
    conn.row_factory = sqlite3.Row
    conn.execute("PRAGMA query_only = ON")
    return conn


def rel_to(root: Path, p: Path) -> str:
    try:
        return p.relative_to(root).as_posix()
    except ValueError:
        return p.as_posix()


def absent(source: str, owner: str, what: str) -> Dict[str, Any]:
    return {
        "state": "absent",
        "source": source,
        "message": "Not built yet: %s is produced by the `%s` worker and %s does not exist on this machine." % (what, owner, source),
    }


# ---------------------------------------------------------------------------
# Kernel-exact: SQL provider over the `kernel` worker's kernel.db (schema v0,
# docs/KERNEL.md). Every statement below is a fixed literal; request values are
# only ever bound as parameters.
# ---------------------------------------------------------------------------
KERNEL_TABLES = ("meta", "decls", "edges", "roots", "reach", "dom_trees", "dom", "taint_sources", "taint_paths", "decl_module")
PATH_ID_BASE = 64  # path id = taint_sources.id * 64 + roots.id


class SqlKernel:
    def __init__(self, connect: Callable[[], sqlite3.Connection], state: str, source: str, version_key: Callable[[], Any]) -> None:
        self._connect = connect
        self.state = state
        self.source = source
        self._version_key = version_key
        self._cache: Dict[str, Any] = {}
        self._cache_ver: Any = None
        self._lock = threading.Lock()

    # ---- plumbing ----------------------------------------------------------
    def _env(self, extra: Dict[str, Any]) -> Dict[str, Any]:
        out = {"state": self.state, "source": self.source, "provenance": "FIXTURE" if self.state == "fixture" else "L"}
        out.update(extra)
        return out

    def _cached(self, key: str, fn: Callable[[], Any]) -> Any:
        with self._lock:
            ver = self._version_key()
            if ver != self._cache_ver:
                self._cache = {}
                self._cache_ver = ver
            if key in self._cache:
                return self._cache[key]
        val = fn()
        with self._lock:
            self._cache[key] = val
        return val

    def missing_tables(self) -> List[str]:
        conn = self._connect()
        try:
            have = {r[0] for r in conn.execute("SELECT name FROM sqlite_master WHERE type IN ('table','view')")}
        finally:
            conn.close()
        return [t for t in KERNEL_TABLES if t not in have]

    def _roots(self, conn: sqlite3.Connection) -> List[Dict[str, Any]]:
        return [dict(r) for r in conn.execute("SELECT id, name, decl_id, grp FROM roots ORDER BY id")]

    def _root_mask(self, conn: sqlite3.Connection, root: str) -> int:
        roots = self._roots(conn)
        if root == ROOT_UNION:
            m = 0
            for r in roots:
                m |= 1 << int(r["id"])
            return m
        for r in roots:
            if r["name"] == root:
                return 1 << int(r["id"])
        raise ApiError(400, "unknown root")

    # ---- summary -----------------------------------------------------------
    def summary(self) -> Dict[str, Any]:
        return self._cached("summary", self._summary)

    def _summary(self) -> Dict[str, Any]:
        conn = self._connect()
        try:
            meta: Dict[str, Any] = {}
            for r in conn.execute("SELECT key, value_json FROM meta"):
                raw = r["value_json"]
                if raw is not None and len(raw) <= 4096:
                    try:
                        meta[r["key"]] = json.loads(raw)
                    except Exception:
                        meta[r["key"]] = raw
            roots = self._roots(conn)
            total = 0
            union_live = 0
            union_stmt = 0
            root_live: Dict[int, int] = {int(r["id"]): 0 for r in roots}
            root_stmt: Dict[int, int] = {int(r["id"]): 0 for r in roots}
            # Single pass over decls grouped by (live_mask, stmt_mask) — ~10x faster on 1.47M rows.
            for lm, sm, cnt in conn.execute("SELECT live_mask, stmt_mask, COUNT(*) FROM decls GROUP BY live_mask, stmt_mask"):
                lm_i = int(lm or 0)
                sm_i = int(sm or 0)
                c_i = int(cnt or 0)
                total += c_i
                if lm_i:
                    union_live += c_i
                if sm_i:
                    union_stmt += c_i
                for rid in root_live:
                    bit = 1 << rid
                    if lm_i & bit:
                        root_live[rid] += c_i
                    if sm_i & bit:
                        root_stmt[rid] += c_i
            meta_counts = meta.get("counts") if isinstance(meta.get("counts"), dict) else {}
            if isinstance(meta_counts.get("edges"), int):
                n_edges = int(meta_counts["edges"])
            else:
                n_edges = int(conn.execute("SELECT COUNT(*) FROM edges").fetchone()[0])
            n_consts = int(meta_counts["constants"]) if isinstance(meta_counts.get("constants"), int) else None
            axioms = [dict(r) for r in conn.execute("SELECT name, live_mask FROM decls WHERE kind = 'axiom' ORDER BY name")]
            sorry = conn.execute("SELECT live_mask FROM decls WHERE name = 'sorryAx'").fetchone()
            sorry_mask = int(sorry[0] or 0) if sorry else None
            out_roots = []
            all_mask = 0
            for r in roots:
                rid = int(r["id"])
                bit = 1 << rid
                all_mask |= bit
                live = root_live[rid]
                out_roots.append({
                    "name": r["name"], "label": r["name"], "group": r["grp"], "live": live, "dead": total - live, "stmt": root_stmt[rid],
                    "axioms": [a["name"] for a in axioms if int(a["live_mask"] or 0) & bit],
                    "sorry_in_export": sorry_mask is not None,
                    "sorry_reachable": bool(sorry_mask is not None and sorry_mask & bit),
                })
            out_roots.append({
                "name": ROOT_UNION, "label": "Union of all %d roots" % len(roots), "group": "", "live": union_live, "dead": total - union_live, "stmt": union_stmt,
                "axioms": [a["name"] for a in axioms if int(a["live_mask"] or 0) & all_mask],
                "sorry_in_export": sorry_mask is not None,
                "sorry_reachable": bool(sorry_mask is not None and sorry_mask & all_mask),
            })
            src_n = {r[0]: int(r[1]) for r in conn.execute("SELECT class, COUNT(*) FROM taint_sources GROUP BY class")}
            path_n = {r[0]: int(r[1]) for r in conn.execute(
                "SELECT s.class, COUNT(*) FROM taint_paths p JOIN taint_sources s ON s.id = p.source_id WHERE p.hop = 0 GROUP BY s.class")}
            trees = [dict(r) for r in conn.execute("SELECT id, label, view, n_nodes FROM dom_trees ORDER BY id")]
            unmatched = int(conn.execute("SELECT COUNT(*) FROM decl_module WHERE module IS NULL").fetchone()[0])
            return self._env({
                "meta": meta, "decls": total, "constants": n_consts, "edges": n_edges, "module_unmatched": unmatched,
                "roots": out_roots,
                "taint_kinds": [{"kind": k, "sources": src_n[k], "paths": path_n.get(k, 0)} for k in sorted(src_n)],
                "dom_trees": trees,
                "root_names": [r["name"] for r in roots],
            })
        finally:
            conn.close()

    # ---- live / dead -------------------------------------------------------
    def decls(self, root: str, status: str, q: str, limit: int, offset: int) -> Dict[str, Any]:
        conn = self._connect()
        try:
            mask = self._root_mask(conn, root)
            where = {
                "live": "(d.live_mask & :mask) != 0",
                "dead": "(d.live_mask & :mask) = 0",
                "stmt": "(d.stmt_mask & :mask) != 0",
                "all": "1 = 1",
            }[status]  # fixed literals selected by a validated enum
            params: Dict[str, Any] = {"mask": mask, "limit": limit, "offset": offset}
            if q:
                where += " AND d.name LIKE :q ESCAPE '\\'"
                params["q"] = "%" + like_escape(q) + "%"
            total = int(conn.execute("SELECT COUNT(*) FROM decls d WHERE " + where, params).fetchone()[0])
            rows = [{
                "name": r["name"], "kind": r["kind"], "module": r["module"], "module_method": r["method"],
                "live": bool(int(r["live_mask"] or 0) & mask), "stmt": bool(int(r["stmt_mask"] or 0) & mask),
            } for r in conn.execute(
                "SELECT d.name, d.kind, d.live_mask, d.stmt_mask, m.module, m.method FROM decls d "
                "LEFT JOIN decl_module m ON m.decl_id = d.id WHERE " + where + " ORDER BY d.id DESC LIMIT :limit OFFSET :offset", params)]
            return self._env({"root": root, "status": status, "total": total, "offset": offset, "rows": rows})
        finally:
            conn.close()

    # ---- dominators --------------------------------------------------------
    def _tree(self, conn: sqlite3.Connection, label: str) -> sqlite3.Row:
        if label == "":
            row = conn.execute("SELECT id, label, view, root_ids, n_nodes FROM dom_trees ORDER BY id LIMIT 1").fetchone()
        else:
            row = conn.execute("SELECT id, label, view, root_ids, n_nodes FROM dom_trees WHERE label = ?", (label,)).fetchone()
        if row is None:
            raise ApiError(400, "unknown dominator tree")
        return row

    def dom(self, tree_label: str, node: str, limit: int) -> Dict[str, Any]:
        conn = self._connect()
        try:
            tree = self._tree(conn, tree_label)
            tid = tree["id"]
            base = {"tree": tree["label"], "view": tree["view"], "tree_nodes": tree["n_nodes"]}
            kid_sql = ("SELECT d.name, d.kind, x.subtree_size FROM dom x JOIN decls d ON d.id = x.decl_id "
                       "WHERE x.tree_id = ? AND x.idom {} ORDER BY x.subtree_size DESC, x.decl_id LIMIT ?")
            if node == "":
                kids = conn.execute(kid_sql.format("IS NULL"), (tid, limit)).fetchall()
                n_kids = int(conn.execute("SELECT COUNT(*) FROM dom WHERE tree_id = ? AND idom IS NULL", (tid,)).fetchone()[0])
                base.update({
                    "found": True, "virtual": True,
                    "node": {"name": "", "kind": "virtual root", "module": None, "subtree": tree["n_nodes"], "depth": -1},
                    "chain": [],
                })
            else:
                row = conn.execute(
                    "SELECT d.id, d.name, d.kind, x.idom, x.depth, x.subtree_size, m.module FROM decls d "
                    "JOIN dom x ON x.decl_id = d.id AND x.tree_id = ? LEFT JOIN decl_module m ON m.decl_id = d.id WHERE d.name = ?",
                    (tid, node)).fetchone()
                if row is None:
                    base.update({"found": False, "node": {"name": node}, "chain": [], "children": [], "n_children": 0})
                    return self._env(base)
                chain = [{"name": row["name"], "subtree": row["subtree_size"]}]
                cur = row["idom"]
                guard = 0
                while cur is not None and guard < 100000:
                    up = conn.execute(
                        "SELECT d.name, x.idom, x.subtree_size FROM dom x JOIN decls d ON d.id = x.decl_id WHERE x.tree_id = ? AND x.decl_id = ?",
                        (tid, cur)).fetchone()
                    if up is None:
                        break
                    chain.append({"name": up["name"], "subtree": up["subtree_size"]})
                    cur = up["idom"]
                    guard += 1
                chain.reverse()
                if len(chain) > 400:  # keep the payload bounded; the UI shows the elision
                    base["chain_elided"] = len(chain) - 400
                    chain = chain[:200] + chain[-200:]
                kids = conn.execute(kid_sql.format("= ?"), (tid, row["id"], limit)).fetchall()
                n_kids = int(conn.execute("SELECT COUNT(*) FROM dom WHERE tree_id = ? AND idom = ?", (tid, row["id"])).fetchone()[0])
                base.update({
                    "found": True, "virtual": False,
                    "node": {"name": row["name"], "kind": row["kind"], "module": row["module"], "subtree": row["subtree_size"], "depth": row["depth"]},
                    "chain": chain,
                })
            base["children"] = [{"name": k["name"], "kind": k["kind"], "subtree": k["subtree_size"]} for k in kids]
            base["n_children"] = n_kids
            return self._env(base)
        finally:
            conn.close()

    def dom_top(self, tree_label: str, limit: int) -> Dict[str, Any]:
        def run() -> Dict[str, Any]:
            conn = self._connect()
            try:
                tree = self._tree(conn, tree_label)
                rows = conn.execute(
                    "SELECT d.name, d.kind, x.subtree_size, x.depth FROM dom x JOIN decls d ON d.id = x.decl_id "
                    "WHERE x.tree_id = ? ORDER BY x.subtree_size DESC, x.decl_id LIMIT ?", (tree["id"], limit)).fetchall()
                return self._env({"tree": tree["label"], "rows": [
                    {"name": r["name"], "kind": r["kind"], "subtree": r["subtree_size"], "depth": r["depth"]} for r in rows]})
            finally:
                conn.close()
        return self._cached("dom_top/%s/%d" % (tree_label, limit), run)

    # ---- taint -------------------------------------------------------------
    def taint(self, kind: str, root: str, limit: int, offset: int) -> Dict[str, Any]:
        conn = self._connect()
        try:
            root_id = -1
            if root:
                hit = [r for r in self._roots(conn) if r["name"] == root]
                if not hit:
                    raise ApiError(400, "unknown root")
                root_id = int(hit[0]["id"])
            params = {"kind": kind, "root": root_id, "limit": limit, "offset": offset}
            where = ("FROM taint_paths p JOIN taint_sources s ON s.id = p.source_id "
                     "WHERE p.hop = 0 AND (:kind = '' OR s.class = :kind) AND (:root < 0 OR p.root_id = :root)")
            total = int(conn.execute("SELECT COUNT(*) " + where, params).fetchone()[0])
            rows = conn.execute(
                "SELECT s.id AS sid, s.class, s.origin, s.module, s.detail, p.root_id, d.name AS source_name, r.name AS root_name, "
                "(SELECT MAX(q.hop) FROM taint_paths q WHERE q.source_id = p.source_id AND q.root_id = p.root_id) AS hops "
                + where.replace("WHERE", "JOIN decls d ON d.id = s.decl_id JOIN roots r ON r.id = p.root_id WHERE", 1)
                + " ORDER BY s.class, hops, s.id, p.root_id LIMIT :limit OFFSET :offset", params).fetchall()
            return self._env({"kind": kind, "root": root, "total": total, "offset": offset, "rows": [{
                "id": int(r["sid"]) * PATH_ID_BASE + int(r["root_id"]), "kind": r["class"], "origin": r["origin"],
                "root": r["root_name"], "source": r["source_name"], "length": r["hops"], "detail": r["detail"],
            } for r in rows]})
        finally:
            conn.close()

    def taint_path(self, pid: int) -> Dict[str, Any]:
        sid, rid = divmod(pid, PATH_ID_BASE)
        conn = self._connect()
        try:
            src = conn.execute("SELECT class, origin, module, line_no, detail FROM taint_sources WHERE id = ?", (sid,)).fetchone()
            hops = conn.execute(
                "SELECT p.hop, p.decl_id, p.edge_kind, d.name, d.kind, m.module FROM taint_paths p JOIN decls d ON d.id = p.decl_id "
                "LEFT JOIN decl_module m ON m.decl_id = d.id WHERE p.source_id = ? AND p.root_id = ? ORDER BY p.hop", (sid, rid)).fetchall()
            if src is None or not hops:
                return self._env({"found": False, "id": pid})
            names = {1: "type", 2: "value", 3: "type+value"}
            edges = []
            for a, b in zip(hops, hops[1:]):
                # independent re-check of each hop against the stored dependency graph
                e = conn.execute("SELECT kind FROM edges WHERE src = ? AND dst = ?", (a["decl_id"], b["decl_id"])).fetchone()
                edges.append({"src": a["name"], "dst": b["name"], "dep": names.get(e["kind"] if e else b["edge_kind"], "?"),
                              "in_graph": e is not None, "kind_matches": bool(e is not None and (b["edge_kind"] is None or e["kind"] == b["edge_kind"]))})
            root = conn.execute("SELECT name FROM roots WHERE id = ?", (rid,)).fetchone()
            return self._env({
                "found": True, "id": pid, "kind": src["class"], "origin": src["origin"], "detail": src["detail"],
                "source_module": src["module"], "source_line": src["line_no"],
                "root": root["name"] if root else None, "source": hops[-1]["name"],
                "nodes": [{"name": h["name"], "kind": h["kind"], "module": h["module"]} for h in hops], "edges": edges,
            })
        finally:
            conn.close()

    # ---- one declaration ---------------------------------------------------
    def decl(self, name: str) -> Dict[str, Any]:
        conn = self._connect()
        try:
            via = None
            row = conn.execute("SELECT * FROM decls WHERE name = ?", (name,)).fetchone()
            if row is None and self._has_consts(conn):
                c = conn.execute("SELECT decl_id, ckind FROM consts WHERE name = ?", (name,)).fetchone()
                if c is not None:
                    row = conn.execute("SELECT * FROM decls WHERE id = ?", (c["decl_id"],)).fetchone()
                    via = c["ckind"]
            if row is None:
                return self._env({"found": False, "name": name})
            m = conn.execute("SELECT module, method FROM decl_module WHERE decl_id = ?", (row["id"],)).fetchone()
            live = int(row["live_mask"] or 0)
            stmt = int(row["stmt_mask"] or 0)
            roots = self._roots(conn)
            keys = row.keys()
            return self._env({
                "found": True, "name": row["name"], "queried": name, "via_const": via, "kind": row["kind"],
                "module": m["module"] if m else None, "module_method": m["method"] if m else None,
                "type_deps": row["fan_out_type"], "value_deps": row["fan_out_value"], "fan_in": row["fan_in"], "fan_out": row["fan_out"],
                "flags": row["flags"],
                "live_roots": [r["name"] for r in roots if live & (1 << int(r["id"]))],
                "stmt_roots": [r["name"] for r in roots if stmt & (1 << int(r["id"]))],
                "sighash": row["sighash"] if "sighash" in keys else None,
                "sighash_anon": row["sighash_anon"] if "sighash_anon" in keys else None,
            })
        finally:
            conn.close()

    @staticmethod
    def _has_consts(conn: sqlite3.Connection) -> bool:
        return conn.execute("SELECT 1 FROM sqlite_master WHERE type='table' AND name='consts'").fetchone() is not None


_FX_KERNEL_URI = "file:leanre_p3_fixture_kernel?mode=memory&cache=shared"


def fixture_kernel() -> SqlKernel:
    """Synthetic graph in an in-memory SQLite DB with the real schema (nothing is written to disk)."""
    anchor = sqlite3.connect(_FX_KERNEL_URI, uri=True, check_same_thread=False)
    if anchor.execute("SELECT COUNT(*) FROM sqlite_master").fetchone()[0] == 0:
        p3_fixtures.build_kernel_fixture_db(anchor)

    def connect() -> sqlite3.Connection:
        conn = sqlite3.connect(_FX_KERNEL_URI, uri=True, timeout=10.0)
        conn.row_factory = sqlite3.Row
        conn.execute("PRAGMA query_only = ON")
        return conn

    k = SqlKernel(connect, "fixture", "workbench/p3_fixtures.py (synthetic, in-memory)", lambda: 0)
    k._anchor = anchor  # keep the shared in-memory DB alive
    return k


TIER1_TABLES = ("meta", "misfiles", "boilerplate_clusters")


class SqlTier1:
    """Read-only SQL provider over outputs/flirt/tier1.db (produced by `flirt`)."""

    def __init__(self, connect: Callable[[], sqlite3.Connection], source: str, version_key: Callable[[], Any]) -> None:
        self._connect = connect
        self.state = "ready"
        self.source = source
        self._version_key = version_key
        self._cache: Dict[str, Any] = {}
        self._cache_ver: Any = None
        self._lock = threading.Lock()

    def _env(self, extra: Dict[str, Any]) -> Dict[str, Any]:
        out = {"state": self.state, "source": self.source, "provenance": "L"}
        out.update(extra)
        return out

    def _cached(self, key: str, fn: Callable[[], Any]) -> Any:
        with self._lock:
            ver = self._version_key()
            if ver != self._cache_ver:
                self._cache = {}
                self._cache_ver = ver
            if key in self._cache:
                return self._cache[key]
        val = fn()
        with self._lock:
            self._cache[key] = val
        return val

    def missing_tables(self) -> List[str]:
        conn = self._connect()
        try:
            have = {r[0] for r in conn.execute("SELECT name FROM sqlite_master WHERE type IN ('table','view')")}
        finally:
            conn.close()
        return [t for t in TIER1_TABLES if t not in have]

    def _header(self) -> Dict[str, Any]:
        def run() -> Dict[str, Any]:
            conn = self._connect()
            try:
                meta: Dict[str, Any] = {}
                for r in conn.execute("SELECT key, value_json FROM meta"):
                    try:
                        meta[r["key"]] = json.loads(r["value_json"])
                    except Exception:
                        meta[r["key"]] = r["value_json"]
                tier_counts = {r[0]: int(r[1]) for r in conn.execute("SELECT tier, COUNT(*) FROM misfiles GROUP BY tier")}
                cols = {r[1] for r in conn.execute("PRAGMA table_info(misfiles)")}
                has_band = "band" in cols
                band_counts = {r[0]: int(r[1]) for r in conn.execute("SELECT band, COUNT(*) FROM misfiles GROUP BY band")} if has_band else {}
                bulk_rows = []
                if conn.execute("SELECT 1 FROM sqlite_master WHERE type='table' AND name='bulk_namespace_remappings'").fetchone():
                    bulk_rows = [dict(r) for r in conn.execute(
                        "SELECT folder_l2, declared_top_ns, module_count, folder_non_shim_count, share_of_folder "
                        "FROM bulk_namespace_remappings ORDER BY module_count DESC")]
                kind_counts = {r[0]: int(r[1]) for r in conn.execute("SELECT kind, COUNT(*) FROM boilerplate_clusters GROUP BY kind")}
                red_total = int(conn.execute("SELECT COALESCE(SUM(redundant_modules), 0) FROM boilerplate_clusters").fetchone()[0])
                mi = meta.get("mathlib_import_stats") or {}
                ms = meta.get("misfile_scoring") or {}
                if has_band:
                    cb = ms.get("calibrated_bands") if isinstance(ms.get("calibrated_bands"), dict) else {}
                    bulk_band = cb.get("bulk_namespace_remapping") if isinstance(cb.get("bulk_namespace_remapping"), dict) else {}
                    bulk_cnt = bulk_band.get("count")
                    if not isinstance(bulk_cnt, int):
                        bulk_cnt = sum(int(b.get("module_count") or 0) for b in bulk_rows)
                    summary = {
                        "extreme_outliers": band_counts.get("extreme_outlier", 0),
                        "cross_domain_misfiles": band_counts.get("cross_domain_misfile", 0),
                        "isolated_ns_outliers": band_counts.get("isolated_ns_outlier", 0),
                        "bulk_remapped_modules": bulk_cnt,
                        "boilerplate_clusters": sum(kind_counts.values()),
                        "redundant_modules": red_total,
                    }
                else:
                    summary = {
                        "high_misfiles": tier_counts.get("high", 0),
                        "medium_misfiles": tier_counts.get("medium", 0),
                        "boilerplate_clusters": sum(kind_counts.values()),
                        "redundant_modules": red_total,
                        "import_whole_mathlib": int(mi.get("modules_importing_whole_mathlib") or 0),
                    }
                commit = str(meta.get("mirror_commit") or "")
                detail = "%s · %s files · mirror@%s" % (meta.get("schema") or "tier1", meta.get("file_count") or "?", commit[:8] if commit else "?")
                return {
                    "summary": summary,
                    "has_band": has_band,
                    "band_counts": band_counts,
                    "tier_counts": tier_counts,
                    "kind_counts": kind_counts,
                    "bulk_remappings": bulk_rows,
                    "calibration": ms.get("kernel_precision_calibration") or ms.get("calibrated_bands") or {},
                    "source_detail": detail,
                }
            finally:
                conn.close()
        return self._cached("header", run)

    def tier1(self, view: str, q: str, tier: str, band: str, kind: str, limit: int, offset: int) -> Dict[str, Any]:
        hdr = self._header()
        conn = self._connect()
        try:
            params: Dict[str, Any] = {"limit": limit, "offset": offset}
            if view == "boilerplate":
                where = ["1 = 1"]
                if kind != "all":
                    where.append("kind = :kind")
                    params["kind"] = kind
                if q:
                    where.append("(cluster_id LIKE :q ESCAPE '\\' OR representative LIKE :q ESCAPE '\\' OR summary LIKE :q ESCAPE '\\')")
                    params["q"] = "%" + like_escape(q) + "%"
                wsql = " AND ".join(where)
                if not q and kind != "all":
                    total = hdr["kind_counts"].get(kind, 0)
                elif not q and kind == "all":
                    total = sum(hdr["kind_counts"].values())
                else:
                    total = int(conn.execute("SELECT COUNT(*) FROM boilerplate_clusters WHERE " + wsql, params).fetchone()[0])
                rows = []
                for r in conn.execute(
                    "SELECT cluster_id, kind, size, redundant_modules, total_lines, representative, sig_hash, summary, sample_members_json "
                    "FROM boilerplate_clusters WHERE " + wsql + " ORDER BY size DESC, cluster_id LIMIT :limit OFFSET :offset", params):
                    try:
                        members = json.loads(r["sample_members_json"] or "[]")
                    except Exception:
                        members = []
                    rows.append({
                        "cluster_id": r["cluster_id"], "kind": r["kind"], "size": r["size"],
                        "redundant_modules": r["redundant_modules"], "total_lines": r["total_lines"],
                        "representative": r["representative"], "fingerprint": r["sig_hash"],
                        "summary": r["summary"], "members": members[:8],
                    })
                return self._env({
                    "view": view, "kind": kind, "kind_counts": hdr["kind_counts"], "total": total, "offset": offset,
                    "rows": rows, "summary": hdr["summary"], "source_detail": hdr["source_detail"],
                })
            # misfile view
            where = ["1 = 1"]
            if hdr["has_band"] and band != "all":
                where.append("band = :band")
                params["band"] = band
            elif tier != "all" and (not hdr["has_band"] or band == "all"):
                where.append("tier = :tier")
                params["tier"] = tier
            if q:
                where.append("(module LIKE :q ESCAPE '\\' OR declared_ns LIKE :q ESCAPE '\\' OR folder_ns LIKE :q ESCAPE '\\' OR COALESCE(flag_decl,'') LIKE :q ESCAPE '\\')")
                params["q"] = "%" + like_escape(q) + "%"
            wsql = " AND ".join(where)
            if not q and hdr["has_band"] and band != "all":
                total = hdr["band_counts"].get(band, 0)
            elif not q and tier != "all" and (not hdr["has_band"] or band == "all"):
                total = hdr["tier_counts"].get(tier, 0)
            elif not q and tier == "all" and band == "all":
                total = sum(hdr["tier_counts"].values())
            else:
                total = int(conn.execute("SELECT COUNT(*) FROM misfiles WHERE " + wsql, params).fetchone()[0])
            sel_cols = ("rank, module, file_path, folder_ns, declared_ns, score, tier, band, flag_decl, reason"
                        if hdr["has_band"] else "rank, module, file_path, folder_ns, declared_ns, score, tier, flag_decl, reason")
            rows = [{
                "rank": r["rank"], "module": r["module"], "path": r["file_path"],
                "folder_ns": r["folder_ns"], "declared_ns": r["declared_ns"],
                "score": round(float(r["score"]), 4), "tier": r["tier"],
                "band": r["band"] if hdr["has_band"] else None,
                "reason": r["reason"], "evidence": ("flag_decl: " + r["flag_decl"]) if r["flag_decl"] else "",
            } for r in conn.execute(
                "SELECT " + sel_cols + " FROM misfiles WHERE " + wsql + " ORDER BY rank LIMIT :limit OFFSET :offset", params)]
            return self._env({
                "view": view, "tier": tier, "band": band,
                "band_counts": hdr["band_counts"], "tier_counts": hdr["tier_counts"],
                "bulk_remappings": hdr["bulk_remappings"], "calibration": hdr["calibration"],
                "total": total, "offset": offset,
                "rows": rows, "summary": hdr["summary"], "source_detail": hdr["source_detail"],
            })
        finally:
            conn.close()


TIER2_TABLES = ("meta", "corpora", "corpus_sigs", "proof_sigs", "matches", "controls")


class SqlTier2:
    """Read-only SQL provider over outputs/flirt/tier2.db (produced by `xrepo`)."""

    def __init__(self, connect: Callable[[], sqlite3.Connection], source: str, version_key: Callable[[], Any]) -> None:
        self._connect = connect
        self.state = "ready"
        self.source = source
        self._version_key = version_key
        self._cache: Dict[str, Any] = {}
        self._cache_ver: Any = None
        self._lock = threading.Lock()

    def _env(self, extra: Dict[str, Any]) -> Dict[str, Any]:
        out = {"state": self.state, "source": self.source, "provenance": "L"}
        out.update(extra)
        return out

    def _cached(self, key: str, fn: Callable[[], Any]) -> Any:
        with self._lock:
            ver = self._version_key()
            if ver != self._cache_ver:
                self._cache = {}
                self._cache_ver = ver
            if key in self._cache:
                return self._cache[key]
        val = fn()
        with self._lock:
            self._cache[key] = val
        return val

    def missing_tables(self) -> List[str]:
        conn = self._connect()
        try:
            have = {r[0] for r in conn.execute("SELECT name FROM sqlite_master WHERE type IN ('table','view')")}
        finally:
            conn.close()
        return [t for t in TIER2_TABLES if t not in have]

    def _header(self) -> Dict[str, Any]:
        def run() -> Dict[str, Any]:
            conn = self._connect()
            try:
                meta: Dict[str, Any] = {}
                for r in conn.execute("SELECT key, value_json FROM meta"):
                    try:
                        meta[r["key"]] = json.loads(r["value_json"])
                    except Exception:
                        meta[r["key"]] = r["value_json"]
                repos = [{
                    "repo": r["repo"], "commit": r["commit_sha"], "license": r["license"],
                    "toolchain": r["lean_toolchain"], "files": r["lean_files"], "signatures": r["decls"],
                } for r in conn.execute("SELECT repo, commit_sha, license, lean_toolchain, lean_files, decls FROM corpora ORDER BY decls DESC, repo")]
                thresh = int(meta.get("strong_min_tokens") or 6)
                by_var = meta.get("strong_min_tokens_by_variant") or {"s1n": thresh, "s1t": thresh}
                ctl_rows = [dict(r) for r in conn.execute(
                    "SELECT control, variant, min_tokens, n, tp, fp, fn, precision, recall, fpr, note FROM controls")]
                by = {(r["control"], r["variant"], int(r["min_tokens"])): r for r in ctl_rows}
                t_s1n = int(by_var.get("s1n", thresh))
                t_s1t = int(by_var.get("s1t", thresh))
                t_s1a = int(by_var.get("s1a", 16))
                restate = by.get(("restate_selfmatch", "s1n", t_s1n)) or by.get(("restate_selfmatch", "s1t", t_s1t)) or {}
                fdr_n = by.get(("fdr_estimate", "s1n", t_s1n)) or {}
                fdr_t = by.get(("fdr_estimate", "s1t", t_s1t)) or {}
                fdr_a = by.get(("fdr_estimate", "s1a", t_s1a)) or {}
                neg_p = by.get(("neg_perm", "s1n", t_s1n)) or {}
                neg_s = by.get(("neg_swap", "s1t", t_s1t)) or by.get(("neg_swap", "s1n", t_s1n)) or {}
                fpr_val = neg_p.get("fpr") if neg_p.get("fpr") is not None else neg_s.get("fpr")
                grade_counts = {r[0]: int(r[1]) for r in conn.execute("SELECT grade, COUNT(*) FROM matches GROUP BY grade")}
                variant_counts = {r[0]: int(r[1]) for r in conn.execute("SELECT variant, COUNT(*) FROM matches WHERE grade = 'strong' GROUP BY variant")}
                thresh_txt = ", ".join("%s>=%s" % (k, by_var[k]) for k in sorted(by_var))
                notes = [
                    "Strong thresholds: %s." % thresh_txt,
                    "Held-out synthetic restatement control (s1n>=%d, n=%s): precision=%s, recall=%s." % (
                        t_s1n, restate.get("n", "?"),
                        "%.4f" % restate["precision"] if isinstance(restate.get("precision"), (int, float)) else "—",
                        "%.4f" % restate["recall"] if isinstance(restate.get("recall"), (int, float)) else "—",
                    ),
                    "Negative controls: perm(s1n) fpr=%s, swap(s1t) fpr=%s; est. FDR s1n=%s, s1t=%s%s." % (
                        "%.2e" % neg_p["fpr"] if isinstance(neg_p.get("fpr"), (int, float)) else "—",
                        "%.2e" % neg_s["fpr"] if isinstance(neg_s.get("fpr"), (int, float)) else "—",
                        "%.4f" % fdr_n["fpr"] if isinstance(fdr_n.get("fpr"), (int, float)) else "—",
                        "%.4f" % fdr_t["fpr"] if isinstance(fdr_t.get("fpr"), (int, float)) else "—",
                        (", s1a=%.4f" % fdr_a["fpr"]) if isinstance(fdr_a.get("fpr"), (int, float)) else "",
                    ),
                ]
                return {
                    "repos": repos,
                    "grade_counts": grade_counts,
                    "variant_counts": variant_counts,
                    "metrics": {
                        "precision": round(restate["precision"], 4) if isinstance(restate.get("precision"), (int, float)) else None,
                        "recall": round(restate["recall"], 4) if isinstance(restate.get("recall"), (int, float)) else None,
                        "negative_control_fpr": ("%.2e" % fpr_val) if isinstance(fpr_val, (int, float)) else None,
                        "strong_min_tokens": thresh,
                        "note": " ".join(notes),
                    },
                    "source_detail": "%s · %s proof files" % (meta.get("sighash_impl") or "SIGHASH v1", meta.get("proof_files") or "?"),
                }
            finally:
                conn.close()
        return self._cached("header", run)

    def tier2(self, repo: str, q: str, grade: str, variant: str, limit: int, offset: int) -> Dict[str, Any]:
        hdr = self._header()
        conn = self._connect()
        try:
            where = ["1 = 1"]
            params: Dict[str, Any] = {"limit": limit, "offset": offset}
            if grade != "all":
                where.append("m.grade = :grade")
                params["grade"] = grade
            if variant != "all":
                where.append("m.variant = :variant")
                params["variant"] = variant
            if repo:
                where.append("m.repo = :repo")
                params["repo"] = repo
            if q:
                where.append("(p.name LIKE :q ESCAPE '\\' OR p.module LIKE :q ESCAPE '\\' OR m.corpus_name LIKE :q ESCAPE '\\')")
                params["q"] = "%" + like_escape(q) + "%"
            wsql = " AND ".join(where)
            if not q and not repo and variant == "all" and grade != "all":
                total = hdr["grade_counts"].get(grade, 0)
            elif not q and not repo and variant == "all" and grade == "all":
                total = sum(hdr["grade_counts"].values())
            else:
                total = int(conn.execute("SELECT COUNT(*) FROM matches m JOIN proof_sigs p ON p.id = m.proof_id WHERE " + wsql, params).fetchone()[0])
            rows = [{
                "id": "%d:%s" % (r["proof_id"], r["variant"]),
                "decl": r["decl"], "module": r["module"], "kind": r["kind"], "line_no": r["line_no"],
                "repo": r["repo"], "commit": r["commit_sha"], "license": r["license"],
                "matched_name": r["corpus_name"], "matched_module": r["cmod"], "matched_line": r["cline"],
                "sighash": r["sighash"], "variant": r["variant"], "grade": r["grade"],
                "score": r["n_tokens"], "n_candidates": r["n_candidates"],
                "evidence": "%s · %d tok · %d cand · %s:%s" % (
                    r["grade"], r["n_tokens"], r["n_candidates"], r["cmod"], r["cline"]),
            } for r in conn.execute(
                "SELECT m.proof_id, m.variant, m.grade, m.sighash, m.n_tokens, m.n_candidates, "
                "m.repo, m.commit_sha, m.corpus_name, p.name AS decl, p.module, p.kind, p.line_no, "
                "c.module AS cmod, c.line_no AS cline, cp.license "
                "FROM matches m JOIN proof_sigs p ON p.id = m.proof_id "
                "JOIN corpus_sigs c ON c.id = m.corpus_id JOIN corpora cp ON cp.repo = m.repo "
                "WHERE " + wsql + " ORDER BY m.n_tokens DESC, m.proof_id, m.variant LIMIT :limit OFFSET :offset", params)]
            return self._env({
                "grade": grade, "variant": variant, "grade_counts": hdr["grade_counts"], "variant_counts": hdr["variant_counts"],
                "total": total, "offset": offset, "rows": rows,
                "repos": hdr["repos"], "metrics": hdr["metrics"], "source_detail": hdr["source_detail"],
            })
        finally:
            conn.close()


class JsonTier3:
    """Read-only JSON provider over outputs/flirt/tier3_pilot.json (produced by `flirt`)."""

    def __init__(self, path: Path, source: str) -> None:
        self._path = path
        self.state = "ready"
        self.source = source
        self._cache: Optional[Dict[str, Any]] = None
        self._cache_ver: Any = None
        self._lock = threading.Lock()

    def _load(self) -> Dict[str, Any]:
        st = self._path.stat()
        ver = (st.st_ino, st.st_mtime_ns, st.st_size)
        with self._lock:
            if self._cache is not None and self._cache_ver == ver:
                return self._cache
        data = json.loads(self._path.read_text(encoding="utf-8"))
        with self._lock:
            self._cache = data
            self._cache_ver = ver
        return data

    def tier3(self, q: str, limit: int, offset: int) -> Dict[str, Any]:
        data = self._load()
        rows = list(data.get("clusters") or [])
        if q:
            ql = q.lower()
            rows = [r for r in rows if any(ql in str(r.get(k, "")).lower() for k in (
                "cluster_id", "label", "primary_domain", "unblinded_label", "unblinded_domain", "target_name", "cohort"))]
        return {
            "state": self.state,
            "source": self.source,
            "provenance": "M",
            "ai_draft": True,
            "layer": data.get("layer") or "ai/flirt-tier3-pilot",
            "layer_kind": data.get("layer_kind") or "ai-draft",
            "default_on": False,
            "model": data.get("model") or "",
            "breaks": data.get("breaks") or "",
            "leak_test": data.get("leak_test"),
            "agreement": data.get("agreement") or {},
            "unfold_hops": data.get("unfold_hops"),
            "ab_unfolding_comparison": data.get("ab_unfolding_comparison"),
            "total": len(rows),
            "offset": offset,
            "rows": rows[offset:offset + limit],
        }


class FixtureFlirt:
    state = "fixture"
    source = "workbench/p3_fixtures.py (synthetic)"

    def __init__(self) -> None:
        self.fx = p3_fixtures.build_flirt_fixture()

    def _env(self, extra: Dict[str, Any], prov: str = "FIXTURE") -> Dict[str, Any]:
        out = {"state": self.state, "source": self.source, "provenance": prov}
        out.update(extra)
        return out

    @staticmethod
    def _page(rows: List[Dict[str, Any]], q: str, keys: List[str], limit: int, offset: int) -> Tuple[int, List[Dict[str, Any]]]:
        if q:
            ql = q.lower()
            rows = [r for r in rows if any(ql in str(r.get(k, "")).lower() for k in keys)]
        return len(rows), rows[offset:offset + limit]

    def tier1(self, view: str, q: str, tier: str, band: str, kind: str, limit: int, offset: int) -> Dict[str, Any]:
        if view == "boilerplate":
            total, rows = self._page(self.fx["boilerplate"], q, ["representative", "cluster_id"], limit, offset)
        else:
            total, rows = self._page(self.fx["misfile"], q, ["module", "declared_ns", "folder_ns"], limit, offset)
        return self._env({"view": view, "tier": tier, "band": band, "kind": kind, "total": total, "offset": offset, "rows": rows,
                          "summary": {"misfile_rows": len(self.fx["misfile"]), "boilerplate_clusters": len(self.fx["boilerplate"])}})

    def tier2(self, repo: str, q: str, grade: str, variant: str, limit: int, offset: int) -> Dict[str, Any]:
        rows = [r for r in self.fx["tier2"] if (not repo or r["repo"] == repo) and (variant == "all" or r["variant"] == variant)]
        total, rows = self._page(rows, q, ["decl", "matched_name", "module"], limit, offset)
        return self._env({"grade": grade, "variant": variant, "grade_counts": {"strong": len(self.fx["tier2"])}, "total": total, "offset": offset,
                          "rows": rows, "repos": self.fx["repos"], "metrics": self.fx["tier2_metrics"]})

    def tier3(self, q: str, limit: int, offset: int) -> Dict[str, Any]:
        total, rows = self._page(self.fx["tier3"], q, ["label", "cluster_id"], limit, offset)
        agree = sum(1 for r in self.fx["tier3"] if r["agrees"])
        return self._env({"total": total, "offset": offset, "rows": rows, "ai_draft": True,
                          "agreement": {"agree": agree, "of": len(self.fx["tier3"])}}, prov="FIXTURE")


# ---------------------------------------------------------------------------
# Registry: picks ready / fixture / absent per source
# ---------------------------------------------------------------------------
class Phase3:
    def __init__(self, project_root: Path, outputs_dir: Path, annotations_dir: Path, fixtures: bool = False) -> None:
        self.project_root = project_root
        self.outputs_dir = outputs_dir
        self.annotations_dir = annotations_dir
        self.fixtures = fixtures
        self._fx_kernel: Optional[SqlKernel] = None
        self._real_k: Optional[SqlKernel] = None
        self._real_t1: Optional[SqlTier1] = None
        self._real_t2: Optional[SqlTier2] = None
        self._real_t3: Optional[JsonTier3] = None
        self._annot_mod: Any = None
        self._fx_flirt: Optional[FixtureFlirt] = None

    # ---- source resolution -------------------------------------------------
    def kernel_db(self) -> Path:
        return self.outputs_dir / "kernel" / "kernel.db"

    def kernel(self):
        real = self._real_kernel()
        if real is not None:
            return real
        if self.fixtures:
            if self._fx_kernel is None:
                self._fx_kernel = fixture_kernel()
            return self._fx_kernel
        return None

    def flirt(self, tier: int):
        real = self._real_flirt(tier)
        if real is not None:
            return real
        if self.fixtures:
            if self._fx_flirt is None:
                self._fx_flirt = FixtureFlirt()
            return self._fx_flirt
        return None

    def _real_kernel(self) -> Optional[SqlKernel]:
        db = self.kernel_db()
        if not (db.is_file() and db.stat().st_size > 0):
            self._real_k = None
            return None
        if self._real_k is None:
            k = SqlKernel(lambda: ro_connect(db), "ready", rel_to(self.project_root, db),
                          lambda: (db.stat().st_ino, db.stat().st_mtime_ns, db.stat().st_size))
            try:
                missing = k.missing_tables()
            except sqlite3.Error as exc:
                self._kernel_problem = "cannot open %s: %s" % (rel_to(self.project_root, db), exc)
                return None
            if missing:
                self._kernel_problem = "%s exists but is not a complete kernel.db yet (missing tables: %s)" % (
                    rel_to(self.project_root, db), ", ".join(missing))
                return None
            self._kernel_problem = ""
            self._real_k = k
        return self._real_k

    def _real_tier1(self) -> Optional[SqlTier1]:
        db = self.outputs_dir / "flirt" / "tier1.db"
        if not (db.is_file() and db.stat().st_size > 0):
            self._real_t1 = None
            return None
        if self._real_t1 is None:
            t1 = SqlTier1(lambda: ro_connect(db), rel_to(self.project_root, db),
                          lambda: (db.stat().st_ino, db.stat().st_mtime_ns, db.stat().st_size))
            try:
                missing = t1.missing_tables()
            except sqlite3.Error:
                return None
            if missing:
                return None
            self._real_t1 = t1
        return self._real_t1

    def _real_tier2(self) -> Optional[SqlTier2]:
        db = self.outputs_dir / "flirt" / "tier2.db"
        if not (db.is_file() and db.stat().st_size > 0):
            self._real_t2 = None
            return None
        if self._real_t2 is None:
            t2 = SqlTier2(lambda: ro_connect(db), rel_to(self.project_root, db),
                          lambda: (db.stat().st_ino, db.stat().st_mtime_ns, db.stat().st_size))
            try:
                missing = t2.missing_tables()
            except sqlite3.Error:
                return None
            if missing:
                return None
            self._real_t2 = t2
        return self._real_t2

    def _real_tier3(self) -> Optional[JsonTier3]:
        p = self.outputs_dir / "flirt" / "tier3_pilot.json"
        if not (p.is_file() and p.stat().st_size > 0):
            self._real_t3 = None
            return None
        if self._real_t3 is None:
            t3 = JsonTier3(p, rel_to(self.project_root, p))
            try:
                d = t3._load()
                if not isinstance(d, dict) or not isinstance(d.get("clusters"), list):
                    return None
            except Exception:
                return None
            self._real_t3 = t3
        return self._real_t3

    def _real_flirt(self, tier: int):
        if tier == 1:
            return self._real_tier1()
        if tier == 2:
            return self._real_tier2()
        if tier == 3:
            return self._real_tier3()
        return None

    _kernel_problem = ""

    def _absent_kernel(self) -> Dict[str, Any]:
        if self._kernel_problem:
            return {"state": "absent", "source": rel_to(self.project_root, self.kernel_db()),
                    "message": "Not built yet: " + self._kernel_problem + ". Produced by the `kernel` worker."}
        return absent(rel_to(self.project_root, self.kernel_db()), "kernel", "the kernel-exact declaration graph")

    def _absent_flirt(self, tier: int) -> Dict[str, Any]:
        owner = "xrepo" if tier == 2 else "flirt"
        target = "outputs/flirt/tier%d*" % tier
        return {
            "state": "absent",
            "source": target,
            "message": "Not built yet: the FLIRT Tier %d output is produced by the `%s` worker and has not landed at %s yet." % (tier, owner, target),
        }

    # ---- status ------------------------------------------------------------
    def status(self) -> Dict[str, Any]:
        def st(p, absent_obj):
            if p is None:
                return absent_obj
            return {"state": p.state, "source": p.source}

        out = {
            "kernel": st(self.kernel(), self._absent_kernel()),
            "flirt_tier1": st(self.flirt(1), self._absent_flirt(1)),
            "flirt_tier2": st(self.flirt(2), self._absent_flirt(2)),
            "flirt_tier3": st(self.flirt(3), self._absent_flirt(3)),
            "annot": self.annot_status(),
        }
        out["fixture_sources"] = sorted(k for k, v in out.items() if isinstance(v, dict) and v.get("state") == "fixture")
        return out

    # ---- annotations: thin adapter over leanre/annot.py (PackStore) ---------
    def _annot(self):
        """Import leanre/annot.py lazily; None while the `annot` worker has not landed it."""
        if self._annot_mod is None:
            path = self.project_root / "leanre" / "annot.py"
            if not path.is_file():
                return None
            leanre_dir = str(self.project_root / "leanre")
            if leanre_dir not in sys.path:
                sys.path.insert(0, leanre_dir)
            try:
                import annot  # type: ignore
            except Exception:
                return None
            self._annot_mod = annot
        return self._annot_mod

    def _store(self):
        return self._annot().PackStore(str(self.annotations_dir))

    def annot_status(self) -> Dict[str, Any]:
        if self._annot() is None:
            return absent("leanre/annot.py", "annot", "the annotation-pack library")
        default_dir = (self.project_root / "annotations").resolve()
        return {
            "state": "ready",
            "source": rel_to(self.project_root, self.annotations_dir) + "/",
            # the browser self-test only performs its write round-trip on a scratch directory
            "selftest_writes": self.annotations_dir.resolve() != default_dir,
        }

    # ---- GET dispatch ------------------------------------------------------
    def handle_get(self, path: str, q1: Callable[..., str]) -> Optional[Dict[str, Any]]:
        """Return a JSON-able dict for a Phase 3 GET route, or None if not ours."""
        if path == "/api/p3/status":
            return self.status()

        if path.startswith("/api/kernel/"):
            k = self.kernel()
            limit = clamp_int(q1("limit"), 100, 1, MAX_LIMIT, "limit")
            offset = clamp_int(q1("offset"), 0, 0, 10 ** 8, "offset")
            if path == "/api/kernel/summary":
                return k.summary() if k else self._absent_kernel()
            if path == "/api/kernel/decls":
                status = one_of(q1("status"), ["live", "dead", "stmt", "all"], "live", "status")
                root = q1("root")[:512]
                if not k:
                    return self._absent_kernel()
                return k.decls(root or ROOT_UNION, status, q1("q")[:256], limit, offset)
            if path == "/api/kernel/dom":
                return k.dom(q1("tree")[:512], q1("node")[:512], limit) if k else self._absent_kernel()
            if path == "/api/kernel/dom_top":
                return k.dom_top(q1("tree")[:512], limit) if k else self._absent_kernel()
            if path == "/api/kernel/taint":
                return k.taint(q1("kind")[:64], q1("root")[:512], limit, offset) if k else self._absent_kernel()
            if path == "/api/kernel/taint_path":
                pid = clamp_int(q1("id"), 0, 0, 10 ** 9 - 1, "id")
                return k.taint_path(pid) if k else self._absent_kernel()
            if path == "/api/kernel/decl":
                return k.decl(q1("name")[:512]) if k else self._absent_kernel()
            raise ApiError(404, "unknown kernel route")

        if path.startswith("/api/flirt/"):
            limit = clamp_int(q1("limit"), 100, 1, MAX_LIMIT, "limit")
            offset = clamp_int(q1("offset"), 0, 0, 10 ** 8, "offset")
            q = q1("q")[:256]
            if path == "/api/flirt/tier1":
                view = one_of(q1("view"), ["misfile", "boilerplate"], "misfile", "view")
                tier = one_of(q1("tier"), ["all", "high", "medium"], "high", "tier")
                band = one_of(q1("band"), ["all", "extreme_outlier", "cross_domain_misfile", "isolated_ns_outlier"], "all", "band")
                kind = one_of(q1("kind"), ["all", "alpha_body_clone", "sigset_clone", "statement_wrapper", "import_shim"], "all", "kind")
                f = self.flirt(1)
                return f.tier1(view, q, tier, band, kind, limit, offset) if f else self._absent_flirt(1)
            if path == "/api/flirt/tier2":
                grade = one_of(q1("grade"), ["strong", "weak", "defsig", "all"], "strong", "grade")
                variant = one_of(q1("variant"), ["all", "s1n", "s1t", "s1a"], "all", "variant")
                f = self.flirt(2)
                return f.tier2(q1("repo")[:256], q, grade, variant, limit, offset) if f else self._absent_flirt(2)
            if path == "/api/flirt/tier3":
                f = self.flirt(3)
                return f.tier3(q, limit, offset) if f else self._absent_flirt(3)
            raise ApiError(404, "unknown flirt route")

        if path.startswith("/api/annot/"):
            return self.annot_get(path, q1)
        raise ApiError(404, "unknown Phase 3 route")

    # ---- annotation routes --------------------------------------------------
    def _load_pack(self):
        pack, issues = self._store().load()
        return pack, issues

    @staticmethod
    def _rec_out(annot: Any, pack: Any, key: Any, rec: Dict[str, Any]) -> Dict[str, Any]:
        out = dict(rec)
        out["id"] = annot.key_id(key)
        out["draft_layer"] = pack.layers.get(key[0], {}).get("kind") == "ai-draft"
        return out

    def annot_get(self, path: str, q1: Callable[..., str]) -> Any:
        if path not in ("/api/annot/layers", "/api/annot/list", "/api/annot/for", "/api/annot/view", "/api/annot/export"):
            raise ApiError(404, "unknown annot route")
        annot = self._annot()
        if annot is None:
            return self.annot_status()
        env = self.annot_status()
        try:
            pack, issues = self._load_pack()
            if path == "/api/annot/layers":
                env.update({"layers": annot.layer_table(pack), "issues": issues[:100], "tags": list(annot.TAGS), "targets": list(annot.TARGETS)})
                return env
            if path == "/api/annot/view":
                raw = q1("enabled")[:4096]
                enabled = [x for x in raw.split(",") if x] if q1("explicit") == "1" else None
                if enabled is not None:
                    enabled = [l for l in enabled if l in pack.layers]
                v = annot.view(pack, enabled)
                env.update({"enabled": v["enabled"], "conflicts": v["conflicts"][:200], "targets": {
                    k: {"target": e["target"], "name": e["name"], "rename": e.get("rename"), "rename_draft": e.get("rename_draft", False),
                        "rename_layer": e.get("rename_layer"), "rename_conflict": e.get("rename_conflict", False), "n": len(e["annotations"])}
                    for k, e in v["targets"].items()}})
                return env
            if path == "/api/annot/export":
                layer = q1("layer")[:300]
                layers = None
                fname = "leanre-annotations.jsonl"
                if layer:
                    if layer not in pack.layers:
                        raise ApiError(404, "unknown layer")
                    layers = [layer]
                    fname = annot.layer_filename(layer)
                if annot.errors_of(issues):
                    raise ApiError(409, "annotation store has errors; fix them before exporting: " + "; ".join(i["msg"] for i in annot.errors_of(issues)[:3]))
                return RawResponse(annot.dumps(pack, layers).encode("utf-8"), "application/x-ndjson; charset=utf-8", fname)
            limit = clamp_int(q1("limit"), 200, 1, MAX_LIMIT, "limit")
            offset = clamp_int(q1("offset"), 0, 0, 10 ** 8, "offset")
            rows = []
            if path == "/api/annot/list":
                layer = q1("layer")[:300]
                if layer not in pack.layers:
                    raise ApiError(404, "unknown layer")
                ql = q1("q")[:256].lower()
                for key in sorted(pack.annots, key=annot._sort_key):
                    if key[0] != layer:
                        continue
                    rec = pack.annots[key]
                    if ql and ql not in " ".join(str(rec.get(f, "")) for f in ("name", "rename", "note", "author")).lower():
                        continue
                    rows.append(self._rec_out(annot, pack, key, rec))
            else:  # /api/annot/for
                name = q1("name")[:1024]
                for key in sorted(pack.annots, key=annot._sort_key):
                    if key[2] == name:
                        rows.append(self._rec_out(annot, pack, key, pack.annots[key]))
            env.update({"total": len(rows), "offset": offset, "rows": rows[offset:offset + limit]})
            return env
        except annot.PackError as exc:
            raise ApiError(409 if isinstance(exc, annot.ConflictError) else 400, "; ".join(str(i.get("msg", i)) for i in exc.issues[:5]))

    def handle_post(self, path: str, q1: Callable[..., str], body: bytes) -> Dict[str, Any]:
        routes = ("/api/annot/layer", "/api/annot/upsert", "/api/annot/delete", "/api/annot/import", "/api/annot/promote")
        if path not in routes:
            raise ApiError(404, "unknown route")
        annot = self._annot()
        if annot is None:
            raise ApiError(503, self.annot_status()["message"])
        try:
            req = json.loads(body.decode("utf-8"))
        except Exception:
            raise ApiError(400, "body must be UTF-8 JSON")
        if not isinstance(req, dict):
            raise ApiError(400, "body must be a JSON object")

        def s(key: str, limit: int = 4096) -> str:
            v = req.get(key, "")
            if v is None:
                return ""
            if not isinstance(v, str) or len(v) > limit:
                raise ApiError(400, "field '%s' must be a string of at most %d chars" % (key, limit))
            return v

        store = self._store()
        self._assert_inside_annotations(store, annot)
        try:
            if path == "/api/annot/layer":
                layer = s("layer", 300)
                annot.layer_filename(layer)  # validates the id (raises PackError)
                kind = one_of(s("kind", 16), list(annot.LAYER_KINDS), "human", "kind")
                rec = store.ensure_layer(layer, kind, s("title", 200))
                return {"ok": True, "layer": rec}
            if path == "/api/annot/upsert":
                fields = req.get("fields")
                if not isinstance(fields, dict):
                    raise ApiError(400, "'fields' must be an object")
                allowed = {"target", "name", "layer", "sighash", "slot", "rename", "aliases", "note", "tag", "source", "author", "breaks", "draft", "extra"}
                clean = {k: v for k, v in fields.items() if k in allowed and v not in ("", None)}
                layer = clean.get("layer")
                if not isinstance(layer, str):
                    raise ApiError(400, "missing layer")
                annot.layer_filename(layer)
                pack, _ = store.load()
                if layer not in pack.layers:
                    raise ApiError(404, "unknown layer (create it first)")
                exp = s("expect_updated", 40) or None
                rec = store.upsert(clean, expect_updated=exp)
                return {"ok": True, "record": rec}
            if path == "/api/annot/delete":
                rid = s("id", 64)
                try:
                    store.delete(rid, expect_updated=s("expect_updated", 40))
                except KeyError:
                    raise ApiError(404, "no such annotation")
                return {"ok": True, "deleted": rid}
            if path == "/api/annot/promote":
                pack, issues = store.load()
                if annot.errors_of(issues):
                    raise annot.PackError(annot.errors_of(issues))
                to_layer = s("to_layer", 300)
                annot.layer_filename(to_layer)
                if to_layer not in pack.layers or pack.layers[to_layer]["kind"] != "human":
                    raise ApiError(400, "promote target must be an existing human layer")
                try:
                    rec = annot.promote(pack, s("id", 64), to_layer, author=s("author", 200), tag=s("tag", 8), source=s("source", 600),
                                        now=annot.utc_now(), breaks=s("breaks", 600) or None)
                except KeyError:
                    raise ApiError(404, "no such annotation")
                store._save_layers(pack, [to_layer])
                return {"ok": True, "record": rec}
            # /api/annot/import
            text = req.get("text")
            if not isinstance(text, str):
                raise ApiError(400, "'text' must be the pack contents")
            resolve = req.get("resolve") or {}
            if not isinstance(resolve, dict) or any(v not in ("ours", "theirs") for v in resolve.values()):
                raise ApiError(400, "'resolve' must map conflict ids to 'ours' or 'theirs'")
            rep = store.import_text(text, resolve=resolve, dry_run=bool(req.get("dry_run")))
            rep["added_n"], rep["identical_n"] = len(rep.get("added", [])), len(rep.get("identical", []))
            rep["added"], rep["identical"] = rep["added"][:50], rep["identical"][:50]
            rep["conflicts_n"] = len(rep.get("conflicts", []))
            rep["conflicts"] = rep["conflicts"][:200]
            return rep
        except annot.PackError as exc:
            raise ApiError(409 if isinstance(exc, annot.ConflictError) else 400, "; ".join(str(i.get("msg", i)) for i in exc.issues[:5]))

    def _assert_inside_annotations(self, store: Any, annot: Any) -> None:
        """Belt and braces: the store root must be the configured annotations dir, and it must
        not be (or sit inside) any analysis-output directory."""
        root = Path(store.root).resolve()
        if root != self.annotations_dir.resolve():
            raise ApiError(500, "annotation store root mismatch")
        out = self.outputs_dir.resolve()
        if root == out or out in root.parents:
            raise ApiError(500, "refusing to write annotations under the analysis outputs directory")
