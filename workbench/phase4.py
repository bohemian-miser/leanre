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
import sys
import threading
from pathlib import Path
from typing import Any, Callable, Dict, List, Optional, Set, Tuple

import phase3

DECOMP_KEY_RE = re.compile(r"^[a-z0-9][a-z0-9_-]{0,63}$")
PORTABILITY_ISLAND_RE = re.compile(r"^[A-Za-z0-9_.'\-]{1,160}$")
HYGIENE_DECL_RE = re.compile(
    r"^[A-Za-z_\u00C0-\u024F\u0370-\u03FF\u2100-\u214F]"
    r"[A-Za-z0-9_.'\u00C0-\u024F\u0370-\u03FF\u2070-\u209F\u2100-\u214F]{0,255}$"
)
HYGIENE_MAX_CONE_DEPTH = 2
HYGIENE_MAX_DECLS = 40
HYGIENE_CACHE_MAX = 64
CIRCUIT_TARGET_RE = HYGIENE_DECL_RE
CIRCUIT_MAX_NODES_MIN = 2
CIRCUIT_MAX_NODES_MAX = 64
CIRCUIT_CACHE_MAX = 48
CIRCUIT_RH_SHOWCASE: Tuple[Tuple[str, str, str, str, bool], ...] = (
    ("UpperTheory.LiteratureTheorems.OpenLiteratureStatements", "bundle", "OpenLiteratureStatements", "152/195 dropped", True),
    ("GlobalTheory.Mem.R3.RealInAlt", "bundle", "RealInAlt", "3 conditional", True),
    ("GlobalTheory.Fc.HypsAlt", "bundle", "HypsAlt", "46 fields", True),
    ("UpperTheory.One.M.New.llOf_alt", "theorem", "llOf_alt", "11 dropped wires", True),
    ("Formalism.MainNotions.linkGLOBAL7_items", "theorem", "linkGLOBAL7_items", "step wiring", True),
    ("Deduction.ch_balance", "theorem", "ch_balance", "balance", True),
    ("Formalism.IndefR.AutomorphicEvaluation.sEEofTT", "theorem", "sEEofTT", "else 0", True),
)

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

    def __init__(
        self,
        p3: phase3.Phase3,
        project_config: Optional[Dict[str, Any]] = None,
        src_root: Optional[Path] = None,
    ) -> None:
        self.p3 = p3
        self.project_root = p3.project_root
        self.outputs_dir = p3.outputs_dir
        self.project_config: Dict[str, Any] = dict(project_config or {})
        self._src_root: Optional[Path] = src_root
        self._decomp_dir = self.outputs_dir / "decomp"
        self._decomp_lock = threading.Lock()
        self._decomp_cache: Dict[str, CachedJson] = {
            k: CachedJson(self._decomp_dir / meta["file"])
            for k, meta in DECOMP_DOCS.items()
        }
        self._compute_cache = CachedJson(self._decomp_dir / "compute_atlas.json")
        self._trim_cache = CachedJson(self._decomp_dir / "trim_report.json")
        self._clusters_cache = CachedJson(self.outputs_dir / "flirt" / "clusters.json")
        self._atlas_cache = CachedJson(self.outputs_dir / "flirt" / "cluster_labels_141.json")
        self._portability_cache = CachedJson(self.outputs_dir / "portability_gems.json")
        self._bundles_lock = threading.Lock()
        self._bundles_ver: Any = None
        self._bundles_data: Optional[Dict[str, Any]] = None
        self._hygiene_lock = threading.Lock()
        self._hygiene_cache: "collections.OrderedDict[Any, Dict[str, Any]]" = collections.OrderedDict()
        self._circuit_lock = threading.Lock()
        self._circuit_cache: "collections.OrderedDict[Any, Dict[str, Any]]" = collections.OrderedDict()
        self._circuit_svg_cache: "collections.OrderedDict[Any, str]" = collections.OrderedDict()
        self._circuit_presets_ver: Any = None
        self._circuit_presets_data: Optional[List[Dict[str, Any]]] = None

    def _resolve_src_root(self) -> Optional[Path]:
        if self._src_root is not None and self._src_root.is_dir():
            return self._src_root
        candidates: List[Path] = []
        cfg_src = str(self.project_config.get("src_dir") or "").strip()
        if cfg_src and ".." not in cfg_src and not Path(cfg_src).is_absolute():
            candidates.append(self.outputs_dir.parent / cfg_src)
            candidates.append(self.project_root / cfg_src)
        candidates.append(self.project_root / "data" / "rh_mirror" / "src")
        for cand in candidates:
            if cand.is_dir():
                return cand
        return None

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
        atlas = self._atlas_cache.load()
        port = self._portability_cache.load()
        kdb_path = self.outputs_dir / "kernel" / "kernel.db"
        bundles_mod_path = self.project_root / "leanre" / "bundles.py"
        kernel_mod_path = self.project_root / "leanre" / "kernel.py"
        circuit_mod_path = self.project_root / "leanre" / "circuit.py"
        bundles_ready = kdb_path.is_file() and kdb_path.stat().st_size > 0 and bundles_mod_path.is_file()
        hygiene_ready = kdb_path.is_file() and kdb_path.stat().st_size > 0 and kernel_mod_path.is_file()
        circuit_ready = kdb_path.is_file() and kdb_path.stat().st_size > 0 and circuit_mod_path.is_file()
        return {
            "project": self.project_config,
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
            "bundles": (
                {"state": "ready", "source": "leanre/bundles.py + " + self._rel(kdb_path)}
                if bundles_ready
                else phase3.absent("leanre/bundles.py + " + self._rel(kdb_path), "bundles", "the 5,497-structure unread-field bundle audit")
            ),
            "portability": (
                {"state": "ready", "source": self._rel(self._portability_cache.path)}
                if isinstance(port, dict) and isinstance(port.get("targets"), list)
                else phase3.absent(self._rel(self._portability_cache.path), "portability", "the Mathlib-portability islands report")
            ),
            "hygiene": (
                {"state": "ready", "source": "leanre/kernel.py + " + self._rel(kdb_path)}
                if hygiene_ready
                else phase3.absent("leanre/kernel.py + " + self._rel(kdb_path), "kernel", "the live proof-hygiene auditor")
            ),
            "circuit": (
                {"state": "ready", "source": "leanre/circuit.py + " + self._rel(kdb_path)}
                if circuit_ready
                else phase3.absent("leanre/circuit.py + " + self._rel(kdb_path), "circuit", "the 3-level Proof Circuit visualizer")
            ),
            "flirt_clusters": (
                {"state": "ready", "source": self._rel(self._clusters_cache.path)}
                if isinstance(cl, (dict, list))
                else phase3.absent(self._rel(self._clusters_cache.path), "flirt", "the FLIRT coarse structural clusters")
            ),
            "flirt_atlas": (
                {"state": "ready", "source": self._rel(self._atlas_cache.path)}
                if isinstance(atlas, dict) and isinstance(atlas.get("clusters"), list)
                else phase3.absent(self._rel(self._atlas_cache.path), "flirt-atlas", "the 141-cluster blinded FLIRT atlas")
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

    # ------------------------------------------------------------------ unread bundles (leanre/bundles.py)
    def _load_bundles_cached(self) -> Optional[Dict[str, Any]]:
        kdb_path = self.outputs_dir / "kernel" / "kernel.db"
        if not kdb_path.is_file() or kdb_path.stat().st_size == 0:
            with self._bundles_lock:
                self._bundles_ver = None
                self._bundles_data = None
            return None
        st = kdb_path.stat()
        src_root = self.project_root / "data" / "rh_mirror" / "src"
        has_src = src_root.is_dir()
        ver = (st.st_ino, st.st_mtime_ns, st.st_size, has_src)
        with self._bundles_lock:
            if self._bundles_data is not None and self._bundles_ver == ver:
                return self._bundles_data
            root_str = str(self.project_root)
            if root_str not in sys.path:
                sys.path.insert(0, root_str)
            try:
                from leanre import bundles as bundles_mod
            except Exception:
                return None
            try:
                rep = bundles_mod.run_bundles(
                    kernel_db_path=str(kdb_path),
                    src_root=str(src_root) if has_src else None,
                    top=0,
                    sort_by="dom",
                    only="all",
                )
            except Exception:
                return None
            self._bundles_ver = ver
            self._bundles_data = rep
            return rep

    def bundles_audit(
        self, only: str = "all", sort_by: str = "score", q: str = "", limit: int = 50, offset: int = 0
    ) -> Dict[str, Any]:
        only = phase3.one_of(only, ["all", "prop", "type", "placeholder"], "all", "only")
        sort_by = phase3.one_of(sort_by, ["score", "ratio", "unread", "dom", "cone"], "score", "sort")
        src_lbl = "leanre/bundles.py + " + self._rel(self.outputs_dir / "kernel" / "kernel.db")
        rep = self._load_bundles_cached()
        if not isinstance(rep, dict):
            return phase3.absent(src_lbl, "bundles", "the 5,497-structure unread-field bundle audit")

        if only == "placeholder":
            rows = list(rep.get("placeholders") or [])
        else:
            rows = list(rep.get("bundles") or [])
            if only == "prop":
                rows = [r for r in rows if r.get("is_prop") is True and (r.get("unread_fields") or 0) > 0]
            elif only == "type":
                rows = [r for r in rows if r.get("is_prop") is False and (r.get("unread_fields") or 0) > 0]

        ql = q.strip().lower()
        if ql:
            def _hit(r: Dict[str, Any]) -> bool:
                hay = " ".join([
                    str(r.get("name") or ""),
                    str(r.get("module") or ""),
                    str(r.get("anchor") or ""),
                    str(r.get("top_caller") or ""),
                    " ".join(r.get("unread_field_names") or []),
                    " ".join(r.get("helper_subdecls_excluded") or []),
                ]).lower()
                return ql in hay
            rows = [r for r in rows if _hit(r)]

        if sort_by == "ratio":
            rows.sort(key=lambda r: (-(r.get("unread_ratio") or 0.0), -(r.get("unread_fields") or 0), -(r.get("weighted_score") or 0.0), -(r.get("fan_in") or 0), r.get("name") or ""))
        elif sort_by == "unread":
            rows.sort(key=lambda r: (-(r.get("unread_fields") or 0), -(r.get("unread_ratio") or 0.0), -(r.get("weighted_score") or 0.0), -(r.get("fan_in") or 0), r.get("name") or ""))
        elif sort_by == "dom":
            rows.sort(key=lambda r: (-(r.get("max_caller_dom_sub") or 0), -(r.get("weighted_score") or 0.0), -(r.get("unread_fields") or 0), -(r.get("fan_in") or 0), r.get("name") or ""))
        elif sort_by == "cone":
            rows.sort(key=lambda r: (-(r.get("cone_score") or 0.0), -(r.get("fan_in") or 0), -(r.get("max_caller_dom_sub") or 0), -(r.get("unread_fields") or 0), r.get("name") or ""))
        else:
            rows.sort(key=lambda r: (-(r.get("weighted_score") or 0.0), -(r.get("max_caller_dom_sub") or 0), -(r.get("unread_fields") or 0), -(r.get("fan_in") or 0), r.get("name") or ""))

        return {
            "state": "ready",
            "source": src_lbl,
            "provenance": "L",
            "schema": rep.get("schema") or "leanre.bundles/1",
            "pins": rep.get("pins") or {},
            "summary": rep.get("summary") or {},
            "only": only,
            "sort": sort_by,
            "total": len(rows),
            "limit": limit,
            "offset": offset,
            "rows": rows[offset : offset + limit],
            "placeholders": rep.get("placeholders") or [],
            "true_slots": rep.get("true_slots") or [],
            "eliminated_top": rep.get("eliminated_top") or [],
            "literal_true_field_hits": rep.get("literal_true_field_hits") or [],
        }

    # ------------------------------------------------------------------ 141-cluster blinded FLIRT atlas
    def flirt_atlas(
        self,
        status_f: str = "all",
        severity_f: str = "all",
        pillar_f: str = "all",
        q: str = "",
        limit: int = 150,
        offset: int = 0,
    ) -> Dict[str, Any]:
        status_f = phase3.one_of(status_f, ["all", "cross_domain_misplaced", "partial_drift", "aligned"], "all", "status")
        severity_f = phase3.one_of(severity_f, ["all", "high", "moderate", "low", "none"], "all", "severity")
        src = self._rel(self._atlas_cache.path)
        data = self._atlas_cache.load()
        if not isinstance(data, dict) or not isinstance(data.get("clusters"), list):
            return phase3.absent(src, "flirt-atlas", "the 141-cluster blinded FLIRT atlas")

        all_rows = [r for r in data.get("clusters") or [] if isinstance(r, dict)]
        status_counts: Dict[str, int] = {}
        severity_counts: Dict[str, int] = {}
        pillar_counts: Dict[str, int] = {}
        for r in all_rows:
            ma = r.get("mismatch_audit") or {}
            st = str(ma.get("status") or "unknown")
            sv = str(ma.get("severity") or "none")
            pl = str(r.get("pillar") or "other")
            status_counts[st] = status_counts.get(st, 0) + 1
            severity_counts[sv] = severity_counts.get(sv, 0) + 1
            pillar_counts[pl] = pillar_counts.get(pl, 0) + 1

        ql = q.strip().lower()
        rows: List[Dict[str, Any]] = []
        for r in all_rows:
            ma = r.get("mismatch_audit") or {}
            bl = r.get("blinded_label") or {}
            if status_f != "all" and str(ma.get("status") or "") != status_f:
                continue
            if severity_f != "all" and str(ma.get("severity") or "") != severity_f:
                continue
            if pillar_f and pillar_f != "all" and str(r.get("pillar") or "") != pillar_f:
                continue
            if ql:
                mods = " ".join(str(d.get("module") or "") + " " + str(d.get("name") or "") for d in (r.get("top3_rep_decls") or []) if isinstance(d, dict))
                hay = " ".join([
                    str(r.get("cluster_id") or ""),
                    str(r.get("pillar") or ""),
                    str(r.get("root_decl") or ""),
                    str(bl.get("label") or ""),
                    str(bl.get("primary_domain") or ""),
                    str(bl.get("secondary_domain") or ""),
                    " ".join(bl.get("evidence_tokens") or []),
                    str(ma.get("folder_l2") or ""),
                    str(ma.get("reason") or ""),
                    mods,
                ]).lower()
                if ql not in hay:
                    continue
            rows.append(r)

        return {
            "state": "ready",
            "source": src,
            "provenance": "L+M",
            "schema": data.get("schema") or "leanre.flirt_atlas/v1",
            "mirror_commit": data.get("mirror_commit") or "",
            "epistemic_note": data.get("epistemic_note") or "",
            "totals": data.get("totals") or {},
            "status_counts": status_counts,
            "severity_counts": severity_counts,
            "pillar_counts": pillar_counts,
            "total": len(rows),
            "limit": limit,
            "offset": offset,
            "rows": rows[offset : offset + limit],
        }

    # ------------------------------------------------------------------ portability gems
    @staticmethod
    def _short_decl_name(name: str) -> str:
        s = str(name or "")
        return s.rsplit(".", 1)[-1] if "." in s else s

    @classmethod
    def _island_slug(cls, lead_name: str) -> str:
        short = cls._short_decl_name(lead_name)
        if short == "strongResolutionOfSingularitiesCharZero":
            return "strongResolution"
        return short or "island"

    def _build_portability_islands(
        self, targets: List[Dict[str, Any]], overlap: Dict[str, Any]
    ) -> List[Dict[str, Any]]:
        n = len(targets)
        proj_mat = overlap.get("project_decls_matrix")
        has_mat = isinstance(proj_mat, list) and len(proj_mat) == n and all(
            isinstance(row, list) and len(row) == n for row in proj_mat
        )
        visited: Set[int] = set()
        components: List[List[int]] = []
        for i in range(n):
            if i in visited:
                continue
            comp: List[int] = []
            q: collections.deque = collections.deque([i])
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
        for idx, comp in enumerate(components, 1):
            members = [targets[m] for m in comp]
            lead = max(members, key=lambda t: (int((t.get("cone") or {}).get("project_decls") or 0), str(t.get("name") or "")))
            lead_name = str(lead.get("name") or "")
            slug = self._island_slug(lead_name)
            inter_max = 0
            if has_mat:
                comp_set = set(comp)
                for u in comp:
                    for v in range(n):
                        if v not in comp_set:
                            val = int(proj_mat[u][v] or 0)
                            if val > inter_max:
                                inter_max = val

            # Aggregate top external (Mathlib) prefixes across island members
            prefix_agg: Dict[str, Dict[str, int]] = {}
            for m in members:
                for p in ((m.get("boundary") or {}).get("top_external_prefixes") or []):
                    if not isinstance(p, dict) or not p.get("prefix"):
                        continue
                    pk = str(p["prefix"])
                    cur = prefix_agg.get(pk)
                    dd = int(p.get("distinct_decls") or 0)
                    ce = int(p.get("call_edges") or 0)
                    if cur is None or dd > cur["distinct_decls"]:
                        prefix_agg[pk] = {"prefix": pk, "distinct_decls": dd, "call_edges": ce}
            top_prefixes = sorted(
                prefix_agg.values(),
                key=lambda x: (-x["distinct_decls"], -x["call_edges"], x["prefix"]),
            )[:8]

            tiers = sorted({str((m.get("contamination") or {}).get("tier") or "unknown") for m in members})
            spec_vals = [int((m.get("cone") or {}).get("spec_cone_project_decls") or 0) for m in members]
            proj_vals = [int((m.get("cone") or {}).get("project_decls") or 0) for m in members]
            ext_vals = [int((m.get("boundary") or {}).get("direct_external_decls") or 0) for m in members]
            root_dirs: Set[str] = set()
            for m in members:
                for rd in ((m.get("contamination") or {}).get("significant_root_dirs") or []):
                    root_dirs.add(str(rd))

            islands.append({
                "id": f"island_{idx}",
                "index": idx,
                "slug": slug,
                "lead_target": lead_name,
                "lead_short": self._short_decl_name(lead_name),
                "member_indices": comp,
                "member_count": len(comp),
                "member_names": [str(m.get("name") or "") for m in members],
                "member_shorts": [self._short_decl_name(str(m.get("name") or "")) for m in members],
                "tiers": tiers,
                "max_project_decls": max(proj_vals) if proj_vals else 0,
                "min_spec_cone_project_decls": min(spec_vals) if spec_vals else 0,
                "max_spec_cone_project_decls": max(spec_vals) if spec_vals else 0,
                "max_direct_external_decls": max(ext_vals) if ext_vals else 0,
                "inter_island_project_overlap": inter_max,
                "pairwise_disjoint": inter_max == 0,
                "significant_root_dirs": sorted(root_dirs),
                "top_mathlib_prefixes": top_prefixes,
            })
        return islands

    def portability_gems(self, island: str = "") -> Dict[str, Any]:
        island = (island or "").strip()
        if island:
            if ".." in island or "/" in island or "\\" in island or not PORTABILITY_ISLAND_RE.fullmatch(island):
                raise phase3.ApiError(400, "invalid 'island' parameter")

        src = self._rel(self._portability_cache.path)
        data = self._portability_cache.load()
        if not isinstance(data, dict) or not isinstance(data.get("targets"), list):
            return phase3.absent(src, "portability", "the Mathlib-portability islands report")

        raw_targets = [t for t in (data.get("targets") or []) if isinstance(t, dict)]
        overlap = data.get("overlap") if isinstance(data.get("overlap"), dict) else {}
        all_islands = self._build_portability_islands(raw_targets, overlap)

        island_by_member: Dict[int, Dict[str, Any]] = {}
        for isl in all_islands:
            for mi in isl["member_indices"]:
                island_by_member[mi] = isl

        enriched_targets: List[Dict[str, Any]] = []
        for idx, t in enumerate(raw_targets):
            isl = island_by_member.get(idx)
            row = dict(t)
            row["index"] = idx
            row["short_name"] = self._short_decl_name(str(t.get("name") or ""))
            row["island_id"] = isl["id"] if isl else ""
            row["island_slug"] = isl["slug"] if isl else ""
            enriched_targets.append(row)

        selected_island: Optional[Dict[str, Any]] = None
        if island:
            il = island.lower()
            for isl in all_islands:
                candidates = [
                    isl["id"].lower(),
                    isl["slug"].lower(),
                    isl["lead_target"].lower(),
                    isl["lead_short"].lower(),
                ] + [m.lower() for m in isl["member_names"]] + [m.lower() for m in isl["member_shorts"]]
                if il in candidates or any(il in c for c in candidates):
                    selected_island = isl
                    break
            if selected_island is None:
                return {
                    "state": "ready",
                    "source": src,
                    "provenance": "L",
                    "schema": str(data.get("schema") or "leanre.portability/1"),
                    "found": False,
                    "queried_island": island,
                    "islands_all": all_islands,
                    "islands": [],
                    "targets": [],
                    "rows": [],
                    "overlap": {},
                }

        if selected_island is not None:
            keep = selected_island["member_indices"]
            shown_targets = [enriched_targets[i] for i in keep]
            shown_islands = [selected_island]
        else:
            keep = list(range(len(enriched_targets)))
            shown_targets = enriched_targets
            shown_islands = all_islands

        def _submatrix(mat: Any, idxs: List[int]) -> List[List[Any]]:
            if not isinstance(mat, list):
                return []
            out_m: List[List[Any]] = []
            for r in idxs:
                if r < len(mat) and isinstance(mat[r], list):
                    out_m.append([mat[r][c] for c in idxs if c < len(mat[r])])
            return out_m

        target_names = [str(enriched_targets[i].get("name") or "") for i in keep]
        short_names = [self._short_decl_name(nm) for nm in target_names]
        island_tags = [str(enriched_targets[i].get("island_id") or "") for i in keep]
        overlap_out = {
            "target_names": target_names,
            "short_names": short_names,
            "island_ids": island_tags,
            "project_decls_matrix": _submatrix(overlap.get("project_decls_matrix"), keep),
            "project_jaccard_matrix": _submatrix(overlap.get("project_jaccard_matrix"), keep),
            "external_decls_matrix": _submatrix(overlap.get("external_decls_matrix"), keep),
            "union_summary": overlap.get("union_summary") or {},
        }

        pins_in = data.get("pins") if isinstance(data.get("pins"), dict) else {}
        safe_pins = {
            str(k): v
            for k, v in pins_in.items()
            if isinstance(v, (str, int, float, bool)) and not str(v).startswith("/")
        }
        standalone_cnt = sum(
            1 for t in enriched_targets if str((t.get("contamination") or {}).get("tier") or "") == "standalone-ready"
        )
        scoped_cnt = sum(
            1 for t in enriched_targets if str((t.get("contamination") or {}).get("tier") or "") == "scoped"
        )
        union_sum = overlap.get("union_summary") or {}
        return {
            "state": "ready",
            "source": src,
            "provenance": "L",
            "schema": str(data.get("schema") or "leanre.portability/1"),
            "found": True,
            "queried_island": island,
            "pins": safe_pins,
            "summary": {
                "targets_count": len(enriched_targets),
                "islands_count": len(all_islands),
                "pairwise_disjoint_islands": sum(1 for isl in all_islands if isl["pairwise_disjoint"]),
                "standalone_ready_count": standalone_cnt,
                "scoped_count": scoped_cnt,
                "union_total_decls": union_sum.get("union_total_decls"),
                "union_project_decls": union_sum.get("union_project_decls"),
                "union_external_decls": union_sum.get("union_external_decls"),
                "union_module_count": union_sum.get("union_module_count"),
            },
            "islands_all": all_islands,
            "islands": shown_islands,
            "targets": shown_targets,
            "overlap": overlap_out,
        }

    # ------------------------------------------------------------------ live kernel hygiene
    def hygiene_audit(
        self,
        decl: str,
        cone_depth: int = 0,
        only: str = "all",
        max_decls: int = 25,
    ) -> Dict[str, Any]:
        decl = (decl or "").strip()
        if not decl:
            raise phase3.ApiError(400, "parameter 'decl' is required")
        if ".." in decl or "/" in decl or "\\" in decl or not HYGIENE_DECL_RE.fullmatch(decl):
            raise phase3.ApiError(400, "invalid declaration name for 'decl'")
        if cone_depth < 0 or cone_depth > HYGIENE_MAX_CONE_DEPTH:
            raise phase3.ApiError(400, "parameter 'cone_depth' must be between 0 and %d" % HYGIENE_MAX_CONE_DEPTH)
        only = phase3.one_of(only, ["all", "dropped", "true_slot", "tuple_unread"], "all", "only")
        max_decls = max(1, min(int(max_decls), HYGIENE_MAX_DECLS))

        kdb_path = self.outputs_dir / "kernel" / "kernel.db"
        src_lbl = "leanre/kernel.py + " + self._rel(kdb_path)
        if not kdb_path.is_file() or kdb_path.stat().st_size == 0:
            return phase3.absent(src_lbl, "kernel", "the live proof-hygiene auditor")

        st = kdb_path.stat()
        src_root_path = self._resolve_src_root()
        src_root_str = str(src_root_path) if src_root_path is not None else None
        cache_key = (st.st_ino, st.st_mtime_ns, st.st_size, decl, cone_depth, only, max_decls, src_root_str or "")
        with self._hygiene_lock:
            cached = self._hygiene_cache.get(cache_key)
            if cached is not None:
                self._hygiene_cache.move_to_end(cache_key)
                return cached

        root_str = str(self.project_root)
        if root_str not in sys.path:
            sys.path.insert(0, root_str)
        try:
            from leanre import kernel as kernel_mod
        except Exception:
            return phase3.absent(src_lbl, "kernel", "the live proof-hygiene auditor")

        try:
            rep = kernel_mod.hygiene_decls(
                kernel_db_path=str(kdb_path),
                decls=[decl],
                src_root=src_root_str,
                cone_depth=cone_depth,
                only=only,
                max_decls=max_decls,
                max_callers=30,
                continue_on_error=False,
            )
        except LookupError:
            sugg: List[Dict[str, Any]] = []
            k = self.p3.kernel()
            if k is not None and k.state == "ready":
                conn = k._connect()
                try:
                    sugg = [
                        {"name": r["name"], "kind": r["kind"]}
                        for r in conn.execute(
                            "SELECT name, kind FROM decls WHERE name LIKE ? ESCAPE '\\' ORDER BY fan_in DESC LIMIT 12",
                            ("%" + phase3.like_escape(decl) + "%",),
                        )
                    ]
                finally:
                    conn.close()
            return {
                "state": "ready",
                "source": src_lbl,
                "provenance": "L+heuristic_source",
                "found": False,
                "queried": decl,
                "cone_depth": cone_depth,
                "only": only,
                "suggestions": sugg,
                "summary": {
                    "decls_audited": 0,
                    "decls_with_findings": 0,
                    "total_findings": 0,
                    "by_category": {"dropped": 0, "true_slot": 0, "tuple_unread": 0},
                },
                "decls": [],
            }
        except ValueError as err:
            raise phase3.ApiError(400, str(err))

        safe_src_root = str(rep.get("src_root") or "")
        if safe_src_root.startswith("/"):
            safe_src_root = Path(safe_src_root).name

        out = {
            "state": "ready",
            "source": src_lbl,
            "provenance": "L+heuristic_source",
            "schema": rep.get("schema") or "leanre.kernel.hygiene/1",
            "found": True,
            "queried": decl,
            "kernel_db": rep.get("kernel_db") or "kernel.db",
            "src_root": safe_src_root,
            "elapsed_s": rep.get("elapsed_s"),
            "params": rep.get("params") or {"decls": [decl], "cone_depth": cone_depth, "only": only, "max_decls": max_decls},
            "truncated": bool(rep.get("truncated")),
            "summary": rep.get("summary") or {},
            "decls": rep.get("decls") or [],
        }
        with self._hygiene_lock:
            self._hygiene_cache[cache_key] = out
            while len(self._hygiene_cache) > HYGIENE_CACHE_MAX:
                self._hygiene_cache.popitem(last=False)
        return out

    # ------------------------------------------------------------------ 3-level Proof Circuit (leanre/circuit.py)
    def _circuit_presets(self, kdb_path: Path) -> List[Dict[str, Any]]:
        st = kdb_path.stat()
        ver = (st.st_ino, st.st_mtime_ns, st.st_size)
        with self._circuit_lock:
            if self._circuit_presets_data is not None and self._circuit_presets_ver == ver:
                return list(self._circuit_presets_data)

        presets: List[Dict[str, Any]] = [
            {
                "id": "macro",
                "mode": "macro",
                "target": "",
                "label": "Macro Repo",
                "tag": "Zoom 0",
                "exact_case": False,
            }
        ]
        conn = phase3.ro_connect(kdb_path)
        try:
            rh_names = [row[0] for row in CIRCUIT_RH_SHOWCASE]
            ph = ",".join("?" for _ in rh_names)
            present = {
                str(r["name"])
                for r in conn.execute("SELECT name FROM decls WHERE name IN (" + ph + ")", rh_names)
            }
            if present:
                for fqn, pmode, plabel, ptag, pexact in CIRCUIT_RH_SHOWCASE:
                    if fqn in present:
                        presets.append({
                            "id": pmode + ":" + plabel,
                            "mode": pmode,
                            "target": fqn,
                            "label": plabel,
                            "tag": ptag,
                            "exact_case": pexact,
                        })
            else:
                # Generic project presets (e.g., examples/tiny_demo): discover live inductives & headline roots
                tables = {
                    str(r[0])
                    for r in conn.execute("SELECT name FROM sqlite_master WHERE type='table'")
                }
                seen_targets: Set[Tuple[str, str]] = set()
                if "decl_module" in tables:
                    ind_rows = conn.execute(
                        "SELECT d.name, d.fan_in FROM decls d JOIN decl_module dm ON dm.decl_id = d.id "
                        "WHERE d.kind = 'inductive' AND d.live_mask != 0 ORDER BY d.fan_in DESC, d.id ASC LIMIT 3"
                    ).fetchall()
                else:
                    ind_rows = conn.execute(
                        "SELECT name, fan_in FROM decls WHERE kind = 'inductive' AND live_mask != 0 "
                        "ORDER BY fan_in DESC, id ASC LIMIT 3"
                    ).fetchall()
                for r in ind_rows:
                    nm = str(r["name"])
                    if ("bundle", nm) not in seen_targets:
                        seen_targets.add(("bundle", nm))
                        presets.append({
                            "id": "bundle:" + nm,
                            "mode": "bundle",
                            "target": nm,
                            "label": self._short_decl_name(nm),
                            "tag": "bundle",
                            "exact_case": True,
                        })
                root_names: List[str] = []
                if "roots" in tables:
                    root_names = [
                        str(r["name"])
                        for r in conn.execute("SELECT name FROM roots ORDER BY id ASC LIMIT 4")
                    ]
                if not root_names:
                    for hr in (self.project_config.get("headline_roots") or [])[:4]:
                        if isinstance(hr, str) and hr.strip():
                            root_names.append(hr.strip())
                if not root_names:
                    root_names = [
                        str(r["name"])
                        for r in conn.execute(
                            "SELECT name FROM decls WHERE kind IN ('thm', 'def') AND live_mask != 0 "
                            "ORDER BY fan_in DESC, value_nodes DESC, id ASC LIMIT 4"
                        )
                    ]
                for nm in root_names[:4]:
                    if ("theorem", nm) not in seen_targets:
                        seen_targets.add(("theorem", nm))
                        presets.append({
                            "id": "theorem:" + nm,
                            "mode": "theorem",
                            "target": nm,
                            "label": self._short_decl_name(nm),
                            "tag": "theorem",
                            "exact_case": True,
                        })
        finally:
            conn.close()

        with self._circuit_lock:
            self._circuit_presets_ver = ver
            self._circuit_presets_data = list(presets)
        return presets

    def circuit_view(
        self,
        mode: str = "macro",
        target: str = "",
        theme: str = "dark",
        raw_max_nodes: str = "",
        fmt: str = "json",
        exact_case: bool = False,
        download: bool = False,
    ) -> Any:
        mode = phase3.one_of(mode, ["macro", "bundle", "theorem"], "macro", "mode")
        theme = phase3.one_of(theme, ["dark", "light"], "dark", "theme")
        fmt = phase3.one_of(fmt, ["json", "svg", "html"], "json", "format")

        if len(target) > 256:
            raise phase3.ApiError(400, "parameter 'target' exceeds 256 characters")
        target = target.strip()
        if mode in ("bundle", "theorem") and not target:
            raise phase3.ApiError(400, "parameter 'target' is required for mode '%s'" % mode)
        if target:
            if ".." in target or "/" in target or "\\" in target or not CIRCUIT_TARGET_RE.fullmatch(target):
                raise phase3.ApiError(400, "invalid declaration/structure name for 'target'")

        default_max = 12 if mode == "macro" else (16 if mode == "bundle" else 32)
        if raw_max_nodes == "":
            max_nodes = default_max
        elif not re.fullmatch(r"-?\d{1,9}", raw_max_nodes):
            raise phase3.ApiError(400, "parameter 'max_nodes' must be an integer")
        else:
            max_nodes = int(raw_max_nodes)
            if max_nodes < CIRCUIT_MAX_NODES_MIN or max_nodes > CIRCUIT_MAX_NODES_MAX:
                raise phase3.ApiError(
                    400,
                    "parameter 'max_nodes' must be between %d and %d" % (CIRCUIT_MAX_NODES_MIN, CIRCUIT_MAX_NODES_MAX),
                )

        kdb_path = self.outputs_dir / "kernel" / "kernel.db"
        src_lbl = "leanre/circuit.py + " + self._rel(kdb_path)
        if not kdb_path.is_file() or kdb_path.stat().st_size == 0:
            if fmt != "json":
                raise phase3.ApiError(404, "kernel.db not built yet")
            return phase3.absent(src_lbl, "circuit", "the 3-level Proof Circuit visualizer")

        root_str = str(self.project_root)
        if root_str not in sys.path:
            sys.path.insert(0, root_str)
        try:
            from leanre import circuit as circuit_mod
        except Exception:
            if fmt != "json":
                raise phase3.ApiError(404, "leanre.circuit module unavailable")
            return phase3.absent(src_lbl, "circuit", "the 3-level Proof Circuit visualizer")

        st = kdb_path.stat()
        src_root_path = self._resolve_src_root()
        src_root_str = str(src_root_path) if src_root_path is not None else None
        port_path = self.outputs_dir / "portability_gems.json"
        port_str = str(port_path) if (port_path.is_file() and not port_path.is_symlink()) else None
        port_ver: Any = None
        if port_str is not None:
            pst = port_path.stat()
            port_ver = (pst.st_ino, pst.st_mtime_ns, pst.st_size)

        eff_target = "" if mode == "macro" else target
        cache_key = (
            st.st_ino,
            st.st_mtime_ns,
            st.st_size,
            src_root_str or "",
            port_ver,
            mode,
            eff_target,
            max_nodes,
            bool(exact_case),
        )

        payload: Optional[Dict[str, Any]] = None
        with self._circuit_lock:
            cached = self._circuit_cache.get(cache_key)
            if cached is not None:
                self._circuit_cache.move_to_end(cache_key)
                payload = cached

        presets = self._circuit_presets(kdb_path)
        if payload is None:
            try:
                if mode == "macro":
                    payload = circuit_mod.build_macro_circuit(
                        kernel_db_path=str(kdb_path),
                        src_root=src_root_str,
                        portability_json=port_str,
                        max_nodes=max_nodes,
                    )
                elif mode == "bundle":
                    payload = circuit_mod.build_bundle_circuit(
                        kernel_db_path=str(kdb_path),
                        target=eff_target,
                        src_root=src_root_str,
                        max_nodes=max_nodes,
                        exact_case=exact_case,
                    )
                else:
                    payload = circuit_mod.build_theorem_circuit(
                        kernel_db_path=str(kdb_path),
                        decl=eff_target,
                        src_root=src_root_str,
                        max_nodes=max_nodes,
                        exact_case=exact_case,
                    )
            except LookupError as err:
                if fmt != "json":
                    raise phase3.ApiError(404, str(err))
                sugg: List[Dict[str, Any]] = []
                conn = phase3.ro_connect(kdb_path)
                try:
                    like_pat = "%" + phase3.like_escape(eff_target) + "%"
                    if mode == "bundle":
                        sugg = [
                            {"name": str(r["name"]), "kind": str(r["kind"])}
                            for r in conn.execute(
                                "SELECT name, kind FROM decls WHERE kind IN ('inductive', 'def') AND name LIKE ? ESCAPE '\\' "
                                "ORDER BY CASE WHEN kind='inductive' THEN 0 ELSE 1 END, fan_in DESC LIMIT 12",
                                (like_pat,),
                            )
                        ]
                    else:
                        sugg = [
                            {"name": str(r["name"]), "kind": str(r["kind"])}
                            for r in conn.execute(
                                "SELECT name, kind FROM decls WHERE name LIKE ? ESCAPE '\\' ORDER BY fan_in DESC LIMIT 12",
                                (like_pat,),
                            )
                        ]
                finally:
                    conn.close()
                return {
                    "state": "ready",
                    "source": src_lbl,
                    "provenance": "L",
                    "found": False,
                    "mode": mode,
                    "theme": theme,
                    "queried": eff_target,
                    "message": str(err),
                    "suggestions": sugg,
                    "presets": presets,
                }
            except ValueError as err:
                raise phase3.ApiError(400, str(err))

            with self._circuit_lock:
                self._circuit_cache[cache_key] = payload
                while len(self._circuit_cache) > CIRCUIT_CACHE_MAX:
                    self._circuit_cache.popitem(last=False)

        svg_key = (cache_key, theme)
        svg_text: Optional[str] = None
        with self._circuit_lock:
            svg_text = self._circuit_svg_cache.get(svg_key)
            if svg_text is not None:
                self._circuit_svg_cache.move_to_end(svg_key)
        if svg_text is None:
            svg_text = circuit_mod.render_circuit_svg(payload, theme=theme)
            with self._circuit_lock:
                self._circuit_svg_cache[svg_key] = svg_text
                while len(self._circuit_svg_cache) > CIRCUIT_CACHE_MAX * 2:
                    self._circuit_svg_cache.popitem(last=False)

        if fmt == "svg":
            fname = ""
            if download:
                slug_base = self._short_decl_name(str(payload.get("target") or mode))
                safe_slug = re.sub(r"[^A-Za-z0-9._-]+", "_", slug_base).strip("_")[:64] or mode
                fname = "leanre_circuit_%s_%s.svg" % (mode, safe_slug)
            return phase3.RawResponse(svg_text.encode("utf-8"), "image/svg+xml; charset=utf-8", filename=fname)

        if fmt == "html":
            html_text = circuit_mod.render_circuit_html(payload, theme=theme)
            return phase3.RawResponse(html_text.encode("utf-8"), "text/html; charset=utf-8", filename="")

        return {
            "state": "ready",
            "source": src_lbl,
            "provenance": "L",
            "found": True,
            "mode": mode,
            "theme": theme,
            "max_nodes": max_nodes,
            "payload": payload,
            "svg": svg_text,
            "presets": presets,
        }

    # ------------------------------------------------------------------ GET dispatch
    def handle_get(self, path: str, q1: Callable[..., str]) -> Optional[Any]:
        if path == "/api/p4/status":
            return self.status()
        if path == "/api/circuit":
            raw_target = q1("target")
            raw_mode = q1("mode")
            raw_theme = q1("theme")
            raw_fmt = q1("format")
            raw_max = q1("max_nodes")
            raw_exact = q1("exact_case")
            raw_dl = q1("download")
            if len(raw_mode) > 32 or len(raw_theme) > 32 or len(raw_fmt) > 32 or len(raw_max) > 16:
                raise phase3.ApiError(400, "query parameter exceeds allowed length")
            exact_case = phase3.one_of(raw_exact, ["0", "1"], "0", "exact_case") == "1"
            download = phase3.one_of(raw_dl, ["0", "1"], "0", "download") == "1"
            return self.circuit_view(
                mode=raw_mode or "macro",
                target=raw_target,
                theme=raw_theme or "dark",
                raw_max_nodes=raw_max,
                fmt=raw_fmt or "json",
                exact_case=exact_case,
                download=download,
            )
        if path == "/api/trim":
            return self.trim_report()
        if path == "/api/portability":
            return self.portability_gems(island=q1("island")[:160])
        if path == "/api/hygiene":
            raw_cd = q1("cone_depth")
            if raw_cd == "":
                cone_depth = 0
            elif not re.fullmatch(r"-?\d{1,9}", raw_cd):
                raise phase3.ApiError(400, "parameter 'cone_depth' must be an integer")
            else:
                cone_depth = int(raw_cd)
                if cone_depth < 0 or cone_depth > HYGIENE_MAX_CONE_DEPTH:
                    raise phase3.ApiError(400, "parameter 'cone_depth' must be between 0 and %d" % HYGIENE_MAX_CONE_DEPTH)
            max_decls = phase3.clamp_int(q1("max_decls"), 25, 1, HYGIENE_MAX_DECLS, "max_decls")
            return self.hygiene_audit(
                decl=q1("decl")[:256],
                cone_depth=cone_depth,
                only=q1("only")[:32] or "all",
                max_decls=max_decls,
            )
        if path == "/api/bundles":
            limit = phase3.clamp_int(q1("limit"), 50, 1, phase3.MAX_LIMIT, "limit")
            offset = phase3.clamp_int(q1("offset"), 0, 0, 10 ** 8, "offset")
            return self.bundles_audit(
                only=q1("only")[:32] or "all",
                sort_by=q1("sort")[:32] or "score",
                q=q1("q")[:256],
                limit=limit,
                offset=offset,
            )
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
        if path == "/api/flirt/atlas":
            limit = phase3.clamp_int(q1("limit"), 150, 1, phase3.MAX_LIMIT, "limit")
            offset = phase3.clamp_int(q1("offset"), 0, 0, 10 ** 8, "offset")
            return self.flirt_atlas(
                status_f=q1("status")[:32] or "all",
                severity_f=q1("severity")[:32] or "all",
                pillar_f=q1("pillar")[:64] or "all",
                q=q1("q")[:256],
                limit=limit,
                offset=offset,
            )
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
        if path.startswith(("/api/p4/", "/api/decomp/", "/api/trim", "/api/bundles", "/api/portability", "/api/hygiene", "/api/circuit")):
            raise phase3.ApiError(404, "unknown Phase 4 route")
        return None
