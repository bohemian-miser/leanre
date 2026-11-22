#!/usr/bin/env python3
"""
Phase 4 workbench backend: Proof Blueprint / Decompiler, live Kernel Cone
Slicer, FLIRT Coarse Clusters, and Computation / Dead-Code Atlas.

Design rules (docs/PHASE4_GATES.md D6, docs/PHASE3_GATES.md W2):
  * Strictly READ-ONLY: zero file writes, zero DB mutations. Every SQLite
    query uses fixed literal SQL with bound parameters over mode=ro connections.
  * Every JSON artifact path under outputs/decomp/ and outputs/flirt/ is
    resolved via a fixed allowlist — user parameters never touch filesystem
    paths.
  * Every source degrades cleanly with state="absent" ("Not built yet") when
    its producer has not written the file yet.
  * Stdlib only.
"""
from __future__ import annotations

import collections
import json
import re
import sqlite3
import threading
from pathlib import Path
from typing import Any, Callable, Dict, List, Optional, Set, Tuple

import phase3

DECOMP_KEY_RE = re.compile(r"^[a-z0-9][a-z0-9_-]{0,63}$")

# Core architecture leanre.decomp/v1 documents (always shown first in canonical order)
DECOMP_DOCS: Dict[str, Dict[str, str]] = {
    "spine_map": {
        "file": "spine_map.json",
        "title": "Spine & 332k Shared Diamond",
        "pillar": "spine",
        "owner": "spine",
        "root_hint": "allChi",
    },
    "pillar_theta": {
        "file": "pillar_theta.json",
        "title": "Pillar A — Theta Integrals & Local Matching",
        "pillar": "theta",
        "owner": "theta",
        "root_hint": "UpperTheory.Lit.every_character_of_theta_integrals_local_matching",
    },
    "pillar_galois": {
        "file": "pillar_galois.json",
        "title": "Pillar B — Galois Representations & Row0b",
        "pillar": "galois",
        "owner": "galois",
        "root_hint": "UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter",
    },
    "pillar_window": {
        "file": "pillar_window.json",
        "title": "Pillar C — Window Inequality & VWin",
        "pillar": "window",
        "owner": "window",
        "root_hint": "UpperTheory.One.vwin_of_row",
    },
    "pillar_volume_lit": {
        "file": "pillar_volume_lit.json",
        "title": "Pillar D — Self-Intersection Volume & Literature",
        "pillar": "volume",
        "owner": "volume",
        "root_hint": "SelfIntersectionVolumeEstimates.topCovolSlim2_use_alt_alt",
    },
    "tcb_audit": {
        "file": "tcb_audit.json",
        "title": "Layer 2 Semantic TCB & Contract Audit",
        "pillar": "tcb",
        "owner": "tcb",
        "root_hint": "riemannHypothesis",
    },
}

# Friendly titles for dynamically discovered deep-dive leanre.decomp/v1 docs
EXTRA_DECOMP_TITLES: Dict[str, str] = {
    "explicit_formula_bridge": "Explicit Formula Bridge (TopG → ZeroFreeAll)",
    "stageu_existence": "Pillar A Deep Dive — StageU Existence & Bundles",
    "stageu_hyps_spine": "Pillar A Deep Dive — HypsAlt & Definite Side",
    "allrows_engines": "Pillar A Deep Dive — AllRows & LinkR Engines",
    "linkg_consumer_bridge": "Pillar A Deep Dive — LinkG Consumer Bridge",
    "pillar_a_onto_galc_open0": "Pillar A Deep Dive — Onto / GalC / Open0",
    "geo_one_galois": "Pillar B Deep Dive — geoOne & Geometric Realization",
    "vwin_engines": "Pillar C Deep Dive — VWin & Window Engines",
    "covolume_engines": "Pillar D Deep Dive — Covolume & Height Engines",
    "literature_engines": "Pillar D Deep Dive — Literature Engines",
    "diamond_shared_library": "332k Shared Diamond — 17 Deep Engines & Library",
    "published_catalogue": "Published Results Catalogue (510 Props)",
    "anomaly_sweep": "Anomaly & Edge-Case Sweep (TCB / Semantics)",
}

DECOMP_ORDER = [
    "spine_map",
    "pillar_theta",
    "pillar_galois",
    "pillar_window",
    "pillar_volume_lit",
    "tcb_audit",
]

EDGE_KIND_NAMES = {1: "type", 2: "value", 3: "type+value"}


class CachedJson:
    """Thread-safe mtime/inode-cached read-only JSON file loader."""

    def __init__(self, path: Path) -> None:
        self.path = path
        self._lock = threading.Lock()
        self._ver: Any = None
        self._data: Any = None

    def exists(self) -> bool:
        return self.path.is_file() and self.path.stat().st_size > 0

    def load(self) -> Optional[Any]:
        if not self.exists():
            with self._lock:
                self._ver = None
                self._data = None
            return None
        st = self.path.stat()
        ver = (st.st_ino, st.st_mtime_ns, st.st_size)
        with self._lock:
            if self._data is not None and self._ver == ver:
                return self._data
        try:
            data = json.loads(self.path.read_text(encoding="utf-8"))
        except Exception:
            return None
        with self._lock:
            self._ver = ver
            self._data = data
        return data


class Phase4:
    """Phase 4 read-only endpoints layered alongside Phase3."""

    def __init__(self, p3: phase3.Phase3) -> None:
        self.p3 = p3
        self.project_root = p3.project_root
        self.outputs_dir = p3.outputs_dir
        self._decomp_dir = self.outputs_dir / "decomp"
        self._decomp_lock = threading.Lock()
        self._decomp_cache: Dict[str, CachedJson] = {
            k: CachedJson(self._decomp_dir / meta["file"])
            for k, meta in DECOMP_DOCS.items()
        }
        self._compute_cache = CachedJson(self._decomp_dir / "compute_atlas.json")
        self._trim_cache = CachedJson(self._decomp_dir / "trim_report.json")
        self._clusters_cache = CachedJson(self.outputs_dir / "flirt" / "clusters.json")

    def _rel(self, p: Path) -> str:
        return phase3.rel_to(self.project_root, p)

    def _discover_decomp(self) -> List[Tuple[str, Dict[str, str], CachedJson, Optional[Dict[str, Any]]]]:
        """Dynamically discover all valid leanre.decomp/v1 JSON files in outputs/decomp/.

        Core 6 docs appear first in DECOMP_ORDER (showing absent if not built yet);
        any additional *.json directly inside outputs/decomp/ whose top-level
        `schema` is `"leanre.decomp/v1"` is registered automatically (no symlinks
        escaping outputs/decomp/, safe stem regex only).
        """
        extra_keys: List[str] = []
        if self._decomp_dir.is_dir():
            root_real = self._decomp_dir.resolve()
            for entry in sorted(self._decomp_dir.iterdir(), key=lambda p: p.name):
                if entry.suffix != ".json" or not entry.is_file():
                    continue
                key = entry.stem
                if key in DECOMP_DOCS or not DECOMP_KEY_RE.fullmatch(key):
                    continue
                try:
                    real = entry.resolve()
                except OSError:
                    continue
                if root_real not in real.parents:
                    continue
                with self._decomp_lock:
                    cj = self._decomp_cache.get(key)
                    if cj is None:
                        cj = CachedJson(entry)
                        self._decomp_cache[key] = cj
                doc = cj.load()
                if isinstance(doc, dict) and doc.get("schema") == "leanre.decomp/v1":
                    extra_keys.append(key)

        out: List[Tuple[str, Dict[str, str], CachedJson, Optional[Dict[str, Any]]]] = []
        for key in DECOMP_ORDER:
            meta = DECOMP_DOCS[key]
            cj = self._decomp_cache[key]
            doc = cj.load()
            if isinstance(doc, dict) and doc.get("schema") not in (None, "leanre.decomp/v1"):
                doc = None
            out.append((key, dict(meta, group="core"), cj, doc if isinstance(doc, dict) else None))
        for key in extra_keys:
            cj = self._decomp_cache[key]
            doc = cj.load()
            if not isinstance(doc, dict) or doc.get("schema") != "leanre.decomp/v1":
                continue
            title = EXTRA_DECOMP_TITLES.get(key) or key.replace("_", " ").title()
            meta = {
                "file": key + ".json",
                "title": title,
                "pillar": str(doc.get("pillar") or "decomp"),
                "owner": str(doc.get("pillar") or "decomp"),
                "root_hint": str(doc.get("root") or ""),
                "group": "deep",
            }
            out.append((key, meta, cj, doc))
        return out

    # ------------------------------------------------------------------ status
    def status(self) -> Dict[str, Any]:
        entries = self._discover_decomp()
        decomp_status: Dict[str, Any] = {}
        ready_n = 0
        for key, meta, cj, doc in entries:
            src = self._rel(cj.path)
            if isinstance(doc, dict):
                ready_n += 1
                decomp_status[key] = {
                    "state": "ready",
                    "source": src,
                    "title": meta["title"],
                    "group": meta["group"],
                    "pillar": doc.get("pillar") or meta["pillar"],
                    "nodes": len(doc.get("nodes") or []),
                    "edges": len(doc.get("edges") or []),
                    "horn": len(doc.get("horn") or []),
                    "claims": len(doc.get("claims") or []),
                    "opaque": len(doc.get("opaque") or []),
                }
            else:
                decomp_status[key] = {
                    "state": "absent",
                    "source": src,
                    "title": meta["title"],
                    "group": meta["group"],
                    "pillar": meta["pillar"],
                    "owner": meta["owner"],
                }

        k = self.p3.kernel()
        comp = self._compute_cache.load()
        trim = self._trim_cache.load()
        cl = self._clusters_cache.load()
        return {
            "decomp_ready": ready_n,
            "decomp_total": len(entries),
            "decomp": decomp_status,
            "compute_atlas": (
                {"state": "ready", "source": self._rel(self._compute_cache.path)}
                if isinstance(comp, dict)
                else phase3.absent(self._rel(self._compute_cache.path), "arch", "the computation & dead-code atlas")
            ),
            "trim": (
                {"state": "ready", "source": self._rel(self._trim_cache.path)}
                if isinstance(trim, dict)
                else phase3.absent(self._rel(self._trim_cache.path), "trim", "the virtual proof stripper report")
            ),
            "flirt_clusters": (
                {"state": "ready", "source": self._rel(self._clusters_cache.path)}
                if isinstance(cl, (dict, list))
                else phase3.absent(self._rel(self._clusters_cache.path), "flirt", "the FLIRT coarse structural clusters")
            ),
            "kernel_slice": (
                {"state": k.state, "source": k.source}
                if k is not None
                else self.p3._absent_kernel()
            ),
        }

    # ------------------------------------------------------------------ decomp
    def decomp_index(self) -> Dict[str, Any]:
        entries = self._discover_decomp()
        docs: List[Dict[str, Any]] = []
        ready = 0
        for key, meta, cj, doc in entries:
            src = self._rel(cj.path)
            if isinstance(doc, dict):
                ready += 1
                nodes = doc.get("nodes") or []
                verdicts: Dict[str, int] = {}
                statuses: Dict[str, int] = {}
                for n in nodes:
                    if isinstance(n, dict):
                        v = str(n.get("verdict") or "unknown")
                        s = str(n.get("status") or "OPAQUE")
                        verdicts[v] = verdicts.get(v, 0) + 1
                        statuses[s] = statuses.get(s, 0) + 1
                docs.append({
                    "key": key,
                    "group": meta["group"],
                    "state": "ready",
                    "source": src,
                    "title": meta["title"],
                    "pillar": doc.get("pillar") or meta["pillar"],
                    "owner": meta["owner"],
                    "root": doc.get("root") or meta["root_hint"],
                    "schema": doc.get("schema") or "leanre.decomp/v1",
                    "pins": doc.get("pins") or {},
                    "counts": {
                        "nodes": len(nodes),
                        "edges": len(doc.get("edges") or []),
                        "horn": len(doc.get("horn") or []),
                        "claims": len(doc.get("claims") or []),
                        "opaque": len(doc.get("opaque") or []),
                    },
                    "verdicts": verdicts,
                    "statuses": statuses,
                })
            else:
                docs.append({
                    "key": key,
                    "group": meta["group"],
                    "state": "absent",
                    "source": src,
                    "title": meta["title"],
                    "pillar": meta["pillar"],
                    "owner": meta["owner"],
                    "root": meta["root_hint"],
                    "message": "Not built yet: produced by `%s` at %s." % (meta["owner"], src),
                })
        return {
            "state": "ready" if ready else "absent",
            "ready": ready,
            "total": len(entries),
            "source": "outputs/decomp/",
            "provenance": "L",
            "docs": docs,
        }

    def decomp_doc(self, key: str) -> Dict[str, Any]:
        if not key or not DECOMP_KEY_RE.fullmatch(key):
            raise phase3.ApiError(400, "invalid decomp document key")
        entries = {k: (meta, cj, doc) for k, meta, cj, doc in self._discover_decomp()}
        if key not in entries:
            raise phase3.ApiError(400, "unknown decomp document; expected a registered leanre.decomp/v1 key")
        meta, cj, doc = entries[key]
        src = self._rel(cj.path)
        if not isinstance(doc, dict):
            return phase3.absent(src, meta["owner"], meta["title"])
        return {
            "state": "ready",
            "source": src,
            "provenance": "L",
            "key": key,
            "group": meta["group"],
            "title": meta["title"],
            "owner": meta["owner"],
            "doc": doc,
        }

    # ------------------------------------------------------------------ trim waterfall
    def trim_report(self) -> Dict[str, Any]:
        src = self._rel(self._trim_cache.path)
        data = self._trim_cache.load()
        if not isinstance(data, dict):
            return phase3.absent(src, "trim", "the virtual proof stripper report")
        return {
            "state": "ready",
            "source": src,
            "provenance": "L",
            "data": data,
        }

    # ------------------------------------------------------------------ compute & dead code
    def compute_atlas(self, q: str, bucket: str, limit: int, offset: int) -> Dict[str, Any]:
        src = self._rel(self._compute_cache.path)
        data = self._compute_cache.load()
        if not isinstance(data, dict):
            return phase3.absent(src, "arch", "the computation & 28,904-file dead-code atlas")
        out: Dict[str, Any] = {
            "state": "ready",
            "source": src,
            "provenance": "L",
            "data": data,
        }
        # Normalize triage rows from leanre.compute_atlas/1 (spot_checks_per_bucket) or flat lists
        rows_raw: List[Dict[str, Any]] = []
        zk = data.get("zero_kernel_classification")
        if isinstance(zk, dict) and isinstance(zk.get("spot_checks_per_bucket"), dict):
            for bname, items in zk["spot_checks_per_bucket"].items():
                if isinstance(items, list):
                    for it in items:
                        if isinstance(it, dict):
                            row = dict(it)
                            row.setdefault("bucket", bname)
                            rows_raw.append(row)
        else:
            for k in ("dead_files", "dead_modules", "dead_code_samples", "triage_rows"):
                if isinstance(data.get(k), list):
                    rows_raw = [r for r in data[k] if isinstance(r, dict)]
                    break
        if rows_raw:
            rows = rows_raw
            if bucket:
                bl = bucket.lower()
                rows = [r for r in rows if str(r.get("bucket") or r.get("category") or r.get("class") or "").lower() == bl]
            if q:
                ql = q.lower()
                rows = [r for r in rows if ql in json.dumps(r, ensure_ascii=False).lower()]
            out["triage_total"] = len(rows)
            out["triage_offset"] = offset
            out["triage_rows"] = rows[offset:offset + limit]
        return out

    # ------------------------------------------------------------------ FLIRT clusters
    def flirt_clusters(self, q: str, kind: str, pillar: str, limit: int, offset: int) -> Dict[str, Any]:
        src = self._rel(self._clusters_cache.path)
        data = self._clusters_cache.load()
        if data is None:
            return phase3.absent(src, "flirt", "the FLIRT coarse structural clustering output")
        if isinstance(data, list):
            clusters = data
            totals: Dict[str, Any] = {"clusters_count": len(clusters)}
            by_pillar: Dict[str, Any] = {}
        else:
            clusters = list(data.get("clusters") or data.get("neighborhoods") or data.get("groups") or [])
            totals = dict(data.get("totals") or data.get("summary") or data.get("stats") or {})
            by_pillar = dict(data.get("by_pillar") or {})
        summary = {
            k: v for k, v in totals.items()
            if isinstance(v, (int, float, str)) and k in (
                "clusters_count", "live_decls", "effective_core_decls", "collapse_pct",
                "aux_collapsed", "stmt_wrapper_collapsed", "k1n_dup_collapsed",
                "copy_shell_collapsed", "inter_cluster_edge_pairs_total", "dead_modules_not_in_kernel",
            )
        }
        if not summary:
            summary = {"clusters": len(clusters)}
        kinds_count: Dict[str, int] = {}
        pillars_count: Dict[str, int] = {}
        for c in clusters:
            if isinstance(c, dict):
                ck = str(c.get("kind") or c.get("category") or c.get("type") or "cluster")
                kinds_count[ck] = kinds_count.get(ck, 0) + 1
                pl = str(c.get("pillar") or "")
                if pl:
                    pillars_count[pl] = pillars_count.get(pl, 0) + 1
        rows = clusters
        if kind and kind != "all":
            rows = [c for c in rows if isinstance(c, dict) and str(c.get("kind") or c.get("category") or c.get("type") or "cluster") == kind]
        if pillar and pillar != "all":
            rows = [c for c in rows if isinstance(c, dict) and str(c.get("pillar") or "") == pillar]
        if q:
            ql = q.lower()
            rows = [c for c in rows if ql in json.dumps(c, ensure_ascii=False).lower()]
        return {
            "state": "ready",
            "source": src,
            "provenance": "L",
            "summary": summary,
            "by_pillar": by_pillar,
            "kind": kind,
            "kind_counts": kinds_count,
            "pillar": pillar,
            "pillar_counts": pillars_count,
            "total": len(rows),
            "offset": offset,
            "rows": rows[offset:offset + limit],
        }

    # ------------------------------------------------------------------ kernel cone slicer
    def kernel_slice(
        self,
        name: str,
        direction: str,
        depth: int,
        edge_kind: str,
        max_nodes: int,
        stop_at: str,
        stop_lib: bool,
    ) -> Dict[str, Any]:
        k = self.p3.kernel()
        if k is None:
            return self.p3._absent_kernel()
        conn = k._connect()
        try:
            if not name:
                # Default to top dominator of ALL, or first root
                row = conn.execute(
                    "SELECT d.name FROM dom x JOIN decls d ON d.id = x.decl_id WHERE x.tree_id = 0 ORDER BY x.subtree_size DESC, x.decl_id LIMIT 1"
                ).fetchone()
                if row is None:
                    row = conn.execute("SELECT name FROM roots ORDER BY id LIMIT 1").fetchone()
                name = row["name"] if row else ""

            via = None
            target = conn.execute("SELECT * FROM decls WHERE name = ?", (name,)).fetchone()
            if target is None and k._has_consts(conn):
                c = conn.execute("SELECT decl_id, ckind FROM consts WHERE name = ?", (name,)).fetchone()
                if c is not None:
                    target = conn.execute("SELECT * FROM decls WHERE id = ?", (c["decl_id"],)).fetchone()
                    via = c["ckind"]
            if target is None:
                # Provide up to 15 prefix/substring suggestions so typos are easy to recover from
                sugg = [
                    {"name": r["name"], "kind": r["kind"]}
                    for r in conn.execute(
                        "SELECT name, kind FROM decls WHERE name LIKE ? ESCAPE '\\' ORDER BY fan_in DESC LIMIT 15",
                        ("%" + phase3.like_escape(name) + "%",),
                    )
                ] if name else []
                return k._env({"found": False, "queried": name, "suggestions": sugg})

            tid = int(target["id"])
            roots = k._roots(conn)
            live = int(target["live_mask"] or 0)
            stmt = int(target["stmt_mask"] or 0)
            t_mod = conn.execute("SELECT module, method FROM decl_module WHERE decl_id = ?", (tid,)).fetchone()
            t_dom = conn.execute("SELECT idom, depth, subtree_size FROM dom WHERE tree_id = 0 AND decl_id = ?", (tid,)).fetchone()
            t_idom_name = None
            if t_dom is not None and t_dom["idom"] is not None:
                ir = conn.execute("SELECT name FROM decls WHERE id = ?", (t_dom["idom"],)).fetchone()
                t_idom_name = ir["name"] if ir else None

            # Direct type & value deps (independent of slice filters — mirrors `leanre kernel type-deps`)
            direct_type = [
                {"name": r["name"], "kind": r["kind"], "dep": EDGE_KIND_NAMES.get(r["ekind"], "?"), "module": r["module"]}
                for r in conn.execute(
                    "SELECT d.name, d.kind, e.kind AS ekind, m.module FROM edges e JOIN decls d ON d.id = e.dst "
                    "LEFT JOIN decl_module m ON m.decl_id = d.id WHERE e.src = ? AND e.kind IN (1, 3) ORDER BY d.fan_in DESC, d.id LIMIT 100",
                    (tid,),
                )
            ]
            direct_value = [
                {"name": r["name"], "kind": r["kind"], "dep": "value", "module": r["module"]}
                for r in conn.execute(
                    "SELECT d.name, d.kind, m.module FROM edges e JOIN decls d ON d.id = e.dst "
                    "LEFT JOIN decl_module m ON m.decl_id = d.id WHERE e.src = ? AND e.kind = 2 ORDER BY d.fan_in DESC, d.id LIMIT 100",
                    (tid,),
                )
            ]
            dom_children = [
                {"name": r["name"], "kind": r["kind"], "subtree": r["subtree_size"]}
                for r in conn.execute(
                    "SELECT d.name, d.kind, x.subtree_size FROM dom x JOIN decls d ON d.id = x.decl_id "
                    "WHERE x.tree_id = 0 AND x.idom = ? ORDER BY x.subtree_size DESC, x.decl_id LIMIT 25",
                    (tid,),
                )
            ]

            # Shortest path from first reachable root down to tid via `reach`
            path_to_root: List[Dict[str, Any]] = []
            path_root_name = None
            for r in roots:
                rid = int(r["id"])
                if live & (1 << rid):
                    path_root_name = r["name"]
                    chain_ids: List[int] = [tid]
                    cur = tid
                    guard = 0
                    while guard < 200:
                        pr = conn.execute("SELECT parent FROM reach WHERE root_id = ? AND decl_id = ?", (rid, cur)).fetchone()
                        if pr is None or pr["parent"] is None:
                            break
                        cur = int(pr["parent"])
                        chain_ids.append(cur)
                        guard += 1
                    chain_ids.reverse()
                    if chain_ids:
                        ph = ",".join("?" for _ in chain_ids)
                        meta_map = {
                            int(x["id"]): {"name": x["name"], "kind": x["kind"], "module": x["module"]}
                            for x in conn.execute(
                                "SELECT d.id, d.name, d.kind, m.module FROM decls d LEFT JOIN decl_module m ON m.decl_id = d.id WHERE d.id IN (" + ph + ")",
                                chain_ids,
                            )
                        }
                        path_to_root = [meta_map[i] for i in chain_ids if i in meta_map]
                    break

            # Bounded BFS cone slice
            kind_filter = {
                "all": (1, 2, 3),
                "type": (1, 3),
                "value": (2, 3),
                "both": (3,),
            }[edge_kind]
            stop_prefixes = [s.strip() for s in stop_at.split(",") if s.strip()] if stop_at else []
            lib_prefixes = ("Init.", "Std.", "Lean.", "Mathlib.", "Batteries.", "Aesop.", "Qq.")

            def should_stop(nm: str, mod_method: Optional[str]) -> bool:
                if stop_lib:
                    if nm.startswith(lib_prefixes) or (mod_method and mod_method.startswith("unmatched:")):
                        return True
                for p in stop_prefixes:
                    if nm.startswith(p):
                        return True
                return False

            visited: Dict[int, int] = {tid: 0}  # decl_id -> bfs depth
            node_info: Dict[int, Dict[str, Any]] = {}
            slice_edges: List[Tuple[int, int, int]] = []
            truncated = False
            q: collections.deque = collections.deque([(tid, 0)])

            # Fixed literal SQL selected by validated direction & edge_kind
            if direction == "deps":
                step_sql = (
                    "SELECT e.src, e.dst, e.kind, d.id AS nid, d.name, d.kind AS nkind, d.fan_in, d.fan_out, "
                    "m.module, m.method, x.subtree_size "
                    "FROM edges e JOIN decls d ON d.id = e.dst "
                    "LEFT JOIN decl_module m ON m.decl_id = d.id "
                    "LEFT JOIN dom x ON x.tree_id = 0 AND x.decl_id = d.id "
                    "WHERE e.src = ? ORDER BY COALESCE(x.subtree_size, 0) DESC, d.fan_in DESC, d.id LIMIT 200"
                )
            else:
                step_sql = (
                    "SELECT e.src, e.dst, e.kind, d.id AS nid, d.name, d.kind AS nkind, d.fan_in, d.fan_out, "
                    "m.module, m.method, x.subtree_size "
                    "FROM edges e JOIN decls d ON d.id = e.src "
                    "LEFT JOIN decl_module m ON m.decl_id = d.id "
                    "LEFT JOIN dom x ON x.tree_id = 0 AND x.decl_id = d.id "
                    "WHERE e.dst = ? ORDER BY COALESCE(x.subtree_size, 0) DESC, d.fan_in DESC, d.id LIMIT 200"
                )

            node_info[tid] = {
                "id": target["name"], "decl_id": tid, "kind": target["kind"],
                "module": t_mod["module"] if t_mod else None, "module_method": t_mod["method"] if t_mod else None,
                "depth": 0, "subtree": t_dom["subtree_size"] if t_dom else 0,
                "fan_in": target["fan_in"], "fan_out": target["fan_out"], "stopped": False,
            }

            while q:
                u, d_cur = q.popleft()
                if d_cur >= depth:
                    continue
                if u != tid and node_info[u].get("stopped"):
                    continue
                for r in conn.execute(step_sql, (u,)):
                    ek = int(r["kind"])
                    if ek not in kind_filter:
                        continue
                    nid = int(r["nid"])
                    if nid in visited:
                        slice_edges.append((int(r["src"]), int(r["dst"]), ek))
                        continue
                    if len(visited) >= max_nodes:
                        truncated = True
                        break
                    visited[nid] = d_cur + 1
                    st_flag = should_stop(r["name"], r["method"])
                    node_info[nid] = {
                        "id": r["name"], "decl_id": nid, "kind": r["nkind"],
                        "module": r["module"], "module_method": r["method"],
                        "depth": d_cur + 1, "subtree": int(r["subtree_size"] or 0),
                        "fan_in": r["fan_in"], "fan_out": r["fan_out"], "stopped": st_flag,
                    }
                    slice_edges.append((int(r["src"]), int(r["dst"]), ek))
                    if not st_flag and d_cur + 1 < depth:
                        q.append((nid, d_cur + 1))

            # Deduplicate edges and convert ids -> names
            seen_e: Set[Tuple[int, int]] = set()
            edges_out = []
            for a, b, ek in slice_edges:
                if (a, b) in seen_e or a not in node_info or b not in node_info:
                    continue
                seen_e.add((a, b))
                edges_out.append({"src": node_info[a]["id"], "dst": node_info[b]["id"], "dep": EDGE_KIND_NAMES.get(ek, "?")})
            nodes_out = sorted(node_info.values(), key=lambda n: (n["depth"], -n["subtree"], n["id"]))
            keys = target.keys()
            return k._env({
                "found": True,
                "direction": direction,
                "depth": depth,
                "edge_kind": edge_kind,
                "max_nodes": max_nodes,
                "truncated": truncated,
                "target": {
                    "id": tid, "name": target["name"], "queried": name, "via_const": via, "kind": target["kind"],
                    "module": t_mod["module"] if t_mod else None, "module_method": t_mod["method"] if t_mod else None,
                    "fan_in": target["fan_in"], "fan_out": target["fan_out"],
                    "fan_out_type": target["fan_out_type"], "fan_out_value": target["fan_out_value"],
                    "type_nodes": target["type_nodes"], "value_nodes": target["value_nodes"],
                    "flags": target["flags"],
                    "live_roots": [r["name"] for r in roots if live & (1 << int(r["id"]))],
                    "stmt_roots": [r["name"] for r in roots if stmt & (1 << int(r["id"]))],
                    "sighash": target["sighash"] if "sighash" in keys else None,
                    "sighash_anon": target["sighash_anon"] if "sighash_anon" in keys else None,
                    "dom": ({"depth": t_dom["depth"], "subtree": t_dom["subtree_size"], "idom": t_idom_name} if t_dom else None),
                },
                "direct_type_deps": direct_type,
                "direct_value_deps": direct_value,
                "dom_children": dom_children,
                "path_root": path_root_name,
                "path_to_root": path_to_root,
                "nodes": nodes_out,
                "edges": edges_out,
            })
        finally:
            conn.close()

    # ------------------------------------------------------------------ GET dispatch
    def handle_get(self, path: str, q1: Callable[..., str]) -> Optional[Dict[str, Any]]:
        if path == "/api/p4/status":
            return self.status()
        if path == "/api/trim":
            return self.trim_report()
        if path == "/api/decomp/index":
            return self.decomp_index()
        if path == "/api/decomp/doc":
            return self.decomp_doc(q1("name")[:64])
        if path == "/api/decomp/compute":
            limit = phase3.clamp_int(q1("limit"), 100, 1, phase3.MAX_LIMIT, "limit")
            offset = phase3.clamp_int(q1("offset"), 0, 0, 10 ** 8, "offset")
            return self.compute_atlas(q1("q")[:256], q1("bucket")[:64], limit, offset)
        if path == "/api/flirt/clusters":
            limit = phase3.clamp_int(q1("limit"), 100, 1, phase3.MAX_LIMIT, "limit")
            offset = phase3.clamp_int(q1("offset"), 0, 0, 10 ** 8, "offset")
            return self.flirt_clusters(q1("q")[:256], q1("kind")[:64] or "all", q1("pillar")[:64] or "all", limit, offset)
        if path == "/api/kernel/slice":
            direction = phase3.one_of(q1("dir"), ["deps", "rdeps"], "deps", "dir")
            depth = phase3.clamp_int(q1("depth"), 2, 1, 4, "depth")
            edge_kind = phase3.one_of(q1("edge_kind"), ["all", "type", "value", "both"], "all", "edge_kind")
            max_nodes = phase3.clamp_int(q1("max_nodes"), 60, 5, 200, "max_nodes")
            stop_lib = phase3.one_of(q1("stop_lib"), ["0", "1"], "0", "stop_lib") == "1"
            return self.kernel_slice(
                name=q1("name")[:512],
                direction=direction,
                depth=depth,
                edge_kind=edge_kind,
                max_nodes=max_nodes,
                stop_at=q1("stop_at")[:256],
                stop_lib=stop_lib,
            )
        if path.startswith(("/api/p4/", "/api/decomp/", "/api/trim")):
            raise phase3.ApiError(404, "unknown Phase 4 route")
        return None
