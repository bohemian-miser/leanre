#!/usr/bin/env python3
"""leanre.atlas -- Structural Atlas over Lean 4 kernel graphs.

Implements three scalable structural diagnostics over read-only `kernel.db`
(and optional `tier2.db` cross-corpus signature index):

  1. `alien_twins` ("Same-Theorem, Alien-Proof Splitter"):
     Buckets non-trivial theorems (`type_nodes > 3`) by exact kernel signature
     hash (`k1n`), extracts each theorem's proof-value dependency set `E_V`
     (`edges.kind IN (2, 3)`), skips direct/transitive wrapper relays when
     ranking independent twins, and partitions pairs by Jaccard similarity
     `J(A, B) = |E_V(A) & E_V(B)| / |E_V(A) | E_V(B)|` into:
       - `clone`       (`J >= 0.70`)
       - `variant`     (`0.20 <= J < 0.70`)
       - `alien_proof` (`J < 0.20`)

  2. `hic_matrix` ("Dominator-DFS Hi-C Contact Matrix"):
     Orders all live declarations in `ALL` dominator-tree (`tree_id=0`) DFS
     order, records spine/pillar boundary intervals, streams all kernel edges
     into `256x256` integer count grids (`type_only`, `value_only`, `both`),
     computes total log-coupling `log1p(count)` and diverging log-ratio
     `log((E_T + 1) / (E_V + 1))`, emits `128x128` quantized tiles for HTML5
     `<canvas>`, and renders a crisp `512x512` RGB preview PNG via a pure
     stdlib (`zlib` + `struct`) encoder.

  3. `synteny` ("Cross-Library Structural Synteny Dot-Plot"):
     Projects `k1n` / `k1a` library matches (from `tier2.db` when present, or
     library-vs-project signature collisions inside `kernel.db`) onto
     `(project_dfs_idx, library_order_idx)` coordinates, extracts collinear
     diagonal streaks and blank "terra incognita" novel bands, and renders a
     `512x512` RGB dot-plot preview PNG.

Guardrails:
  - Generic Python 3.11+ with optional `numpy` acceleration and exact pure
    stdlib fallback (`np = None`).
  - Strictly read-only SQLite access (`mode=ro` + `PRAGMA query_only=1`).
  - Zero `.lean` proof bodies and zero workstation absolute paths in outputs.
"""
from __future__ import annotations

import argparse
import collections
import contextlib
import json
import math
import multiprocessing as mp
import os
import re
import sqlite3
import struct
import sys
import time
import zlib
from typing import Any, Dict, Iterable, Iterator, List, Optional, Sequence, Set, Tuple
from urllib.request import pathname2url

try:
    import numpy as np  # type: ignore[import-not-found]
except ImportError:  # pragma: no cover
    np = None  # type: ignore[assignment]

SCHEMA_VERSION = "leanre.atlas/1"

_HERE = os.path.dirname(os.path.abspath(__file__))
_REPO_ROOT = os.path.abspath(os.path.join(_HERE, ".."))

DEFAULT_KERNEL_DB = "outputs/kernel/kernel.db"
DEFAULT_TIER2_DB = "outputs/flirt/tier2.db"
DEFAULT_OUT_JSON = "outputs/atlas_summary.json"

# Edge role constants in `kernel.db`
EDGE_TYPE_ONLY = 1
EDGE_VALUE_ONLY = 2
EDGE_BOTH = 3

# Jaccard thresholds for Same-Theorem, Alien-Proof Splitter
JACCARD_CLONE_MIN = 0.70
JACCARD_VARIANT_MIN = 0.20

# Compiler-generated / tactic-auxiliary theorem name patterns
_AUX_NAME_RE = re.compile(
    r"(?:\._proof_|\._simp_|\._eq_|\._congr_|\._unfold|\._sunfold"
    r"|\._cstage|\._hyg|\.match_\d+|\._unary|\._mutual|\._lambda_"
    r"|\._abel_|\._ring_|\._omega_|\._linarith_|\._norm_num_|\._positivity_|\._gcongr_|\._decide_)"
)

# Known external/stdlib/Mathlib top-level namespace prefixes when `decl_module` is absent
_EXTERNAL_TOP_PREFIXES = frozenset({
    "Init", "Lean", "Std", "Batteries", "Mathlib", "Aesop", "Qq", "ProofWidgets",
    "Nat", "Int", "Rat", "Real", "Complex", "NNReal", "ENNReal", "EReal", "Float",
    "Fin", "Finset", "Fintype", "Multiset", "Set", "List", "Array", "Vector", "ByteArray",
    "BitVec", "String", "Substring", "Char", "Bool", "Prop", "Sort", "Unit", "PUnit",
    "Option", "Except", "Sum", "Prod", "Sigma", "Subtype", "ULift", "PLift",
    "Eq", "HEq", "And", "Or", "Not", "Iff", "Exists", "True", "False", "Classical",
    "Decidable", "Quot", "Function", "Pi", "Equiv", "Filter", "Topology",
    "TopologicalSpace", "UniformSpace", "Metric", "MeasureTheory", "CategoryTheory",
    "AlgebraicGeometry", "NumberTheory", "Combinatorics", "Analysis", "LinearAlgebra",
    "RepresentationTheory", "Polynomial", "MvPolynomial", "PowerSeries", "Matrix",
    "LinearMap", "LinearEquiv", "Module", "Submodule", "Algebra", "RingHom", "MonoidHom",
    "Ideal", "Subring", "Subgroup", "Group", "AddGroup", "CommGroup", "Monoid", "Ring",
    "CommRing", "Semiring", "Field", "Order", "Lattice", "DirichletCharacter", "LSeries",
    "ZMod", "MulChar", "Units", "Padic", "PadicInt", "RiemannHypothesis", "riemannZeta",
})

# Canonical RH spine/pillar landmarks (gracefully skipped on other corpora if absent)
DEFAULT_LANDMARKS: Tuple[Tuple[str, str, str], ...] = (
    ("allChi", "allChi (Waist)", "allChi"),
    ("everyCharacter", "everyCharacter", "UpperTheory.FinalTheorems.everyCharacter"),
    ("everyCharacter_of_row", "everyCharacter_of_row", "UpperTheory.FinalTheorems.everyCharacter_of_row"),
    ("pillar_a", "Pillar A (Theta / Local Matching)", "UpperTheory.Lit.every_character_of_theta_integrals_local_matching"),
    ("pillar_d", "Pillar D (Arakelov Covolume)", "SelfIntersectionVolumeEstimates.topCovolSlim2_use_alt_alt"),
    ("pillar_c", "Pillar C (Automorphic Window)", "UpperTheory.One.vwin_of_row"),
    ("pillar_b", "Pillar B (Galois Local-Global)", "UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter"),
)

# Compact 5x7 bitmap font for PNG axis annotations (zero external font dependencies)
_FONT_5X7: Dict[str, Tuple[int, ...]] = {
    "A": (0b01110, 0b10001, 0b10001, 0b11111, 0b10001, 0b10001, 0b10001),
    "B": (0b11110, 0b10001, 0b10001, 0b11110, 0b10001, 0b10001, 0b11110),
    "C": (0b01110, 0b10001, 0b10000, 0b10000, 0b10000, 0b10001, 0b01110),
    "D": (0b11100, 0b10010, 0b10001, 0b10001, 0b10001, 0b10010, 0b11100),
    "E": (0b11111, 0b10000, 0b10000, 0b11110, 0b10000, 0b10000, 0b11111),
    "G": (0b01110, 0b10001, 0b10000, 0b10111, 0b10001, 0b10001, 0b01110),
    "H": (0b10001, 0b10001, 0b10001, 0b11111, 0b10001, 0b10001, 0b10001),
    "I": (0b01110, 0b00100, 0b00100, 0b00100, 0b00100, 0b00100, 0b01110),
    "L": (0b10000, 0b10000, 0b10000, 0b10000, 0b10000, 0b10000, 0b11111),
    "M": (0b10001, 0b11011, 0b10101, 0b10101, 0b10001, 0b10001, 0b10001),
    "N": (0b10001, 0b11001, 0b10101, 0b10011, 0b10001, 0b10001, 0b10001),
    "O": (0b01110, 0b10001, 0b10001, 0b10001, 0b10001, 0b10001, 0b01110),
    "P": (0b11110, 0b10001, 0b10001, 0b11110, 0b10000, 0b10000, 0b10000),
    "R": (0b11110, 0b10001, 0b10001, 0b11110, 0b10100, 0b10010, 0b10001),
    "S": (0b01111, 0b10000, 0b10000, 0b01110, 0b00001, 0b00001, 0b11110),
    "T": (0b11111, 0b00100, 0b00100, 0b00100, 0b00100, 0b00100, 0b00100),
    "V": (0b10001, 0b10001, 0b10001, 0b10001, 0b10001, 0b01010, 0b00100),
    "Y": (0b10001, 0b10001, 0b01010, 0b00100, 0b00100, 0b00100, 0b00100),
    "-": (0b00000, 0b00000, 0b00000, 0b11111, 0b00000, 0b00000, 0b00000),
    " ": (0b00000, 0b00000, 0b00000, 0b00000, 0b00000, 0b00000, 0b00000),
}


# ---------------------------------------------------------------------------
# Read-only SQLite & Path Hygiene Helpers
# ---------------------------------------------------------------------------

def connect_ro(db_path: str, mmap_bytes: int = 0) -> sqlite3.Connection:
    """Open `db_path` strictly read-only (`mode=ro` + `PRAGMA query_only=1`)."""
    real = os.path.realpath(db_path)
    if not os.path.isfile(real):
        raise FileNotFoundError(f"SQLite database not found: {os.path.basename(db_path)}")
    uri = f"file:{pathname2url(real)}?mode=ro"
    con = sqlite3.connect(uri, uri=True)
    con.execute("PRAGMA query_only=1")
    if mmap_bytes > 0:
        try:
            con.execute(f"PRAGMA mmap_size={int(mmap_bytes)}")
        except sqlite3.DatabaseError:
            pass
    return con


def safe_display_path(path: Optional[str], repo_root: str = _REPO_ROOT) -> Optional[str]:
    """Convert a path into a safe repo-relative or basename label (never absolute)."""
    if not path:
        return None
    abs_p = os.path.abspath(path)
    abs_r = os.path.abspath(repo_root)
    try:
        rel = os.path.relpath(abs_p, abs_r)
        if not rel.startswith("..") and not os.path.isabs(rel):
            return rel.replace(os.sep, "/")
    except ValueError:
        pass
    return os.path.basename(abs_p)


def _table_exists(con: sqlite3.Connection, table_name: str) -> bool:
    row = con.execute(
        "SELECT 1 FROM sqlite_master WHERE type IN ('table', 'view') AND name=?",
        (table_name,),
    ).fetchone()
    return row is not None


def _table_columns(con: sqlite3.Connection, table_name: str) -> Set[str]:
    return {r[1] for r in con.execute(f"PRAGMA table_info({table_name})")}


def is_aux_decl_name(name: str) -> bool:
    """Return True if `name` is a compiler/tactic auxiliary or `_private.` theorem."""
    return bool(_AUX_NAME_RE.search(name)) or name.startswith("_private.")


def top_namespace(name: str, parts_keep: int = 2) -> str:
    """Extract normalized leading namespace prefix (up to `parts_keep` segments)."""
    s = name[7:] if name.startswith("_root_.") else name
    parts = s.split(".")
    if len(parts) <= 1:
        return "<root>"
    return ".".join(parts[: min(parts_keep, len(parts) - 1)])


def classify_decl_origin(
    name: str,
    module: Optional[str],
    method: Optional[str],
    explicit_repo: Optional[str] = None,
) -> str:
    """Classify a declaration into `'project'` or a library corpus (`'mathlib4'`, `'lean4'`, etc.)."""
    if explicit_repo:
        return explicit_repo
    m = method or ""
    if m.startswith(("unmatched:challenge_library", "unmatched:library", "unmatched:external")):
        return _infer_library_corpus(name)
    if module is not None or any(
        tok in m for tok in ("project", "source_rescan", "leanre_db", "private_module", "CutCptCopy")
    ):
        return "project"
    if m:
        return _infer_library_corpus(name)
    # Fallback when `decl_module` is absent (generic/synthetic DB)
    clean = name[7:] if name.startswith("_root_.") else name
    if clean.startswith("_private."):
        rest = clean[len("_private."):]
        first = rest.split(".", 1)[0]
    else:
        first = clean.split(".", 1)[0]
    if first in ("Init", "Lean", "Std"):
        return "lean4"
    if first == "Batteries":
        return "batteries"
    if first in _EXTERNAL_TOP_PREFIXES:
        return "mathlib4"
    return "project"


def _infer_library_corpus(name: str) -> str:
    if name.startswith(("Init.", "Lean.", "Std.", "_private.Init.", "_private.Lean.", "_private.Std.")):
        return "lean4"
    if name.startswith(("Batteries.", "_private.Batteries.")):
        return "batteries"
    return "mathlib4"


# ---------------------------------------------------------------------------
# Dominator-Tree (`tree_id=0`) Deterministic DFS Ordering
# ---------------------------------------------------------------------------

def compute_dom_dfs(
    con: sqlite3.Connection,
    tree_id: int = 0,
    n_bins: int = 256,
    landmarks: Sequence[Tuple[str, str, str]] = DEFAULT_LANDMARKS,
) -> Dict[str, Any]:
    """Order all live declarations in `dom` (`tree_id=0`) deterministic DFS order.

    Children of every dominator node (and roots with `idom IS NULL`) are ordered by
    `(-subtree_size, decl_id)`, matching the `dom_idom` index and grouping the
    shared diamond and external/bridge roots into contiguous intervals.
    """
    max_row = con.execute("SELECT MAX(id), COUNT(*) FROM decls").fetchone()
    max_decl_id = int(max_row[0]) if (max_row and max_row[0] is not None) else -1
    total_decls = int(max_row[1]) if max_row else 0
    if max_decl_id < 0:
        return {
            "tree_id": tree_id,
            "n_live": 0,
            "total_decls": 0,
            "max_decl_id": -1,
            "dfs_order": [],
            "tin_by_id": [],
            "bin_by_id": [],
            "pillar_ticks": [],
            "regions": [],
        }

    children: Dict[int, List[int]] = collections.defaultdict(list)
    roots_dom: List[int] = []
    sub_sz: Dict[int, int] = {}

    if _table_exists(con, "dom"):
        rows = con.execute(
            "SELECT decl_id, idom, subtree_size FROM dom WHERE tree_id=? "
            "ORDER BY idom, subtree_size DESC, decl_id ASC",
            (tree_id,),
        ).fetchall()
    else:
        rows = []

    if rows:
        for did, idom, ssz in rows:
            d_i = int(did)
            s_i = int(ssz)
            sub_sz[d_i] = s_i
            if idom is None:
                roots_dom.append(d_i)
            else:
                children[int(idom)].append(d_i)
        # Ensure deterministic root and child ordering even if index order varies
        roots_dom.sort(key=lambda d: (-sub_sz[d], d))
        for p_id, ch_list in children.items():
            ch_list.sort(key=lambda d: (-sub_sz[d], d))
    else:
        # Fallback if `dom` is empty: order live declarations by id
        for (did,) in con.execute("SELECT id FROM decls WHERE live_mask != 0 ORDER BY id ASC"):
            d_i = int(did)
            sub_sz[d_i] = 1
            roots_dom.append(d_i)

    dfs_order: List[int] = []
    tin: Dict[int, int] = {}
    tout: Dict[int, int] = {}
    stack: List[Tuple[int, int]] = [(r, 0) for r in reversed(roots_dom)]
    while stack:
        u, state = stack.pop()
        if state == 0:
            tin[u] = len(dfs_order)
            dfs_order.append(u)
            stack.append((u, 1))
            ch = children.get(u)
            if ch:
                for v in reversed(ch):
                    stack.append((v, 0))
        else:
            tout[u] = len(dfs_order)

    n_live = len(dfs_order)
    tin_by_id = [-1] * (max_decl_id + 1)
    bin_by_id = [-1] * (max_decl_id + 1)
    if n_live > 0:
        for idx, did in enumerate(dfs_order):
            tin_by_id[did] = idx
            bin_by_id[did] = (idx * n_bins) // n_live

    # Resolve landmarks and derived intervals (shared_diamond, bridge)
    name_to_id: Dict[str, int] = {}
    if landmarks:
        qmarks = ",".join("?" for _ in landmarks)
        lnames = [lm[2] for lm in landmarks]
        for did, dname in con.execute(f"SELECT id, name FROM decls WHERE name IN ({qmarks})", lnames):
            name_to_id[str(dname)] = int(did)

    def _mk_tick(key: str, label: str, decl_name: Optional[str], did: Optional[int], s: int, e: int) -> Dict[str, Any]:
        denom = max(1, n_live)
        return {
            "key": key,
            "label": label,
            "decl_name": decl_name,
            "decl_id": did,
            "dfs_start": s,
            "dfs_end": e,
            "dfs_count": max(0, e - s),
            "share_pct": round(100.0 * max(0, e - s) / denom, 3),
            "bin256_start": round((s * 256.0) / denom, 3),
            "bin256_end": round((e * 256.0) / denom, 3),
            "bin128_start": round((s * 128.0) / denom, 3),
            "bin128_end": round((e * 128.0) / denom, 3),
        }

    pillar_ticks: List[Dict[str, Any]] = []
    for key, label, dname in landmarks:
        did = name_to_id.get(dname)
        if did is not None and did in tin:
            pillar_ticks.append(_mk_tick(key, label, dname, did, tin[did], tout[did]))

    # Derived Shared Diamond & Bridge intervals when RH waist landmarks exist
    ec_id = name_to_id.get("UpperTheory.FinalTheorems.everyCharacter")
    ecr_id = name_to_id.get("UpperTheory.FinalTheorems.everyCharacter_of_row")
    pb_id = name_to_id.get("UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter")
    allchi_id = name_to_id.get("allChi")

    if ec_id in tin and ecr_id in tin and pb_id in tin:
        # Children of everyCharacter after everyCharacter_of_row and Pillar B form Shared Diamond
        dm_start = max(tout[ecr_id], tout[pb_id])
        dm_end = tout[ec_id]
        if dm_end > dm_start:
            pillar_ticks.append(_mk_tick("shared_diamond", "Shared Diamond", None, None, dm_start, dm_end))

    if allchi_id in tin and tout[allchi_id] < n_live:
        pillar_ticks.append(
            _mk_tick("bridge", "Bridge & External Roots", None, None, tout[allchi_id], n_live)
        )

    # Build a clean partition of [0, n_live) into non-overlapping regions for exact block summaries
    regions = _build_disjoint_regions(n_live, pillar_ticks)

    return {
        "tree_id": tree_id,
        "n_live": n_live,
        "total_decls": total_decls,
        "max_decl_id": max_decl_id,
        "dfs_order": dfs_order,
        "tin_by_id": tin_by_id,
        "bin_by_id": bin_by_id,
        "pillar_ticks": pillar_ticks,
        "regions": regions,
    }


def _build_disjoint_regions(n_live: int, pillar_ticks: Sequence[Dict[str, Any]]) -> List[Dict[str, Any]]:
    """Partition `[0, n_live)` into disjoint sequential blocks aligned with major pillars."""
    if n_live <= 0:
        return []
    by_key = {t["key"]: t for t in pillar_ticks}
    primary_keys = ("pillar_a", "pillar_d", "pillar_c", "pillar_b", "shared_diamond", "bridge")
    chosen = [by_key[k] for k in primary_keys if k in by_key]
    if not chosen:
        # Generic fallback: 4 equal quartiles
        out: List[Dict[str, Any]] = []
        for q in range(4):
            s = (q * n_live) // 4
            e = ((q + 1) * n_live) // 4
            if e > s:
                out.append({"key": f"q{q + 1}", "label": f"DFS Quartile {q + 1}", "dfs_start": s, "dfs_end": e})
        return out

    chosen.sort(key=lambda x: (x["dfs_start"], x["dfs_end"]))
    regions: List[Dict[str, Any]] = []
    cur = 0
    glue_idx = 1
    for t in chosen:
        s, e = int(t["dfs_start"]), int(t["dfs_end"])
        if s > cur:
            cnt = s - cur
            lbl = "Spine Waist" if cur == 0 and cnt <= 16 else f"Spine / Lit Glue {glue_idx}"
            if not (cur == 0 and cnt <= 16):
                glue_idx += 1
            regions.append({"key": f"spine_{cur}", "label": lbl, "dfs_start": cur, "dfs_end": s})
        if e > max(cur, s):
            regions.append({"key": t["key"], "label": t["label"], "dfs_start": max(cur, s), "dfs_end": e})
            cur = e
    if cur < n_live:
        regions.append({"key": f"tail_{cur}", "label": "Remaining Roots", "dfs_start": cur, "dfs_end": n_live})
    return regions


# ---------------------------------------------------------------------------
# Fused Parallel / Stdlib Edge Streamer (Hi-C 256x256 + Alien-Proof E_V Sets)
# ---------------------------------------------------------------------------

# Fork-shared globals (Linux COW) to avoid pickling multi-MB lookup tables
_SHARED_DB_PATH: str = ""
_SHARED_BIN_ARR: Any = None
_SHARED_REG_ARR: Any = None
_SHARED_N_BINS: int = 256
_SHARED_N_REGS: int = 0
_SHARED_CAND_MASK: Any = None
_SHARED_CAN_PACK64: bool = False


def _fused_edge_worker(bounds: Tuple[int, int]) -> Tuple[int, int, Any, Any, Any, Any, Dict[int, Tuple[int, ...]]]:
    """Scan `edges` in `[lo, hi)` and return `(total_edges, live_edges, g1, g2, g3, reg_counts, ev_dict)`."""
    lo, hi = bounds
    n_bins = _SHARED_N_BINS
    n_cells = n_bins * n_bins
    n_regs = _SHARED_N_REGS
    cand_mask = _SHARED_CAND_MASK

    with contextlib.closing(connect_ro(_SHARED_DB_PATH, mmap_bytes=8_589_934_592)) as con:
        if np is not None and _SHARED_CAN_PACK64:
            g1 = np.zeros(n_cells, dtype=np.int64)
            g2 = np.zeros(n_cells, dtype=np.int64)
            g3 = np.zeros(n_cells, dtype=np.int64)
            reg_mat = np.zeros((n_regs * n_regs, 3), dtype=np.int64) if n_regs > 0 else None
            ev_lists: Dict[int, List[int]] = collections.defaultdict(list)
            total_edges = 0
            live_edges = 0
            bmap = _SHARED_BIN_ARR
            rmap = _SHARED_REG_ARR

            cur = con.execute(
                "SELECT ((src << 32) | (dst << 2) | kind) FROM edges WHERE src >= ? AND src < ?",
                (lo, hi),
            )
            while True:
                rows = cur.fetchmany(250_000)
                if not rows:
                    break
                cnt = len(rows)
                total_edges += cnt
                packed = np.fromiter((r[0] for r in rows), dtype=np.int64, count=cnt)
                src = packed >> 32
                dst = (packed >> 2) & 0x3FFFFFFF
                kind = packed & 3

                if cand_mask is not None:
                    v_keep = (kind >= 2) & cand_mask[src]
                    if np.any(v_keep):
                        s_v = src[v_keep].tolist()
                        d_v = dst[v_keep].tolist()
                        for u_id, v_id in zip(s_v, d_v):
                            ev_lists[u_id].append(v_id)

                bs = bmap[src]
                bd = bmap[dst]
                valid = (bs >= 0) & (bd >= 0)
                if not np.all(valid):
                    s_live = src[valid]
                    d_live = dst[valid]
                    bs = bs[valid]
                    bd = bd[valid]
                    k_live = kind[valid]
                else:
                    s_live = src
                    d_live = dst
                    k_live = kind

                live_edges += int(bs.shape[0])
                cell = bs * n_bins + bd
                m1 = k_live == EDGE_TYPE_ONLY
                m2 = k_live == EDGE_VALUE_ONLY
                m3 = k_live == EDGE_BOTH
                if np.any(m1):
                    g1 += np.bincount(cell[m1], minlength=n_cells)
                if np.any(m2):
                    g2 += np.bincount(cell[m2], minlength=n_cells)
                if np.any(m3):
                    g3 += np.bincount(cell[m3], minlength=n_cells)

                if reg_mat is not None and rmap is not None and s_live.shape[0] > 0:
                    rcell = rmap[s_live] * n_regs + rmap[d_live]
                    if np.any(m1):
                        reg_mat[:, 0] += np.bincount(rcell[m1], minlength=n_regs * n_regs)
                    if np.any(m2):
                        reg_mat[:, 1] += np.bincount(rcell[m2], minlength=n_regs * n_regs)
                    if np.any(m3):
                        reg_mat[:, 2] += np.bincount(rcell[m3], minlength=n_regs * n_regs)

            ev_compact = {k: tuple(v) for k, v in ev_lists.items()}
            return total_edges, live_edges, g1, g2, g3, reg_mat, ev_compact

        # Pure Python stdlib fallback (also handles gigantic > 2^30 IDs)
        g1_py = [0] * n_cells
        g2_py = [0] * n_cells
        g3_py = [0] * n_cells
        reg_py = [[0, 0, 0] for _ in range(n_regs * n_regs)] if n_regs > 0 else None
        ev_py: Dict[int, List[int]] = collections.defaultdict(list)
        total_edges = 0
        live_edges = 0
        bmap_py = _SHARED_BIN_ARR
        rmap_py = _SHARED_REG_ARR
        max_b = len(bmap_py)

        cur = con.execute(
            "SELECT src, dst, kind FROM edges WHERE src >= ? AND src < ?",
            (lo, hi),
        )
        while True:
            rows = cur.fetchmany(100_000)
            if not rows:
                break
            total_edges += len(rows)
            for s_id, d_id, k_id in rows:
                if cand_mask is not None and k_id >= 2 and 0 <= s_id < len(cand_mask) and cand_mask[s_id]:
                    ev_py[s_id].append(d_id)
                if 0 <= s_id < max_b and 0 <= d_id < max_b:
                    bs_i = bmap_py[s_id]
                    bd_i = bmap_py[d_id]
                    if bs_i >= 0 and bd_i >= 0:
                        live_edges += 1
                        c_idx = bs_i * n_bins + bd_i
                        if k_id == EDGE_TYPE_ONLY:
                            g1_py[c_idx] += 1
                        elif k_id == EDGE_VALUE_ONLY:
                            g2_py[c_idx] += 1
                        elif k_id == EDGE_BOTH:
                            g3_py[c_idx] += 1
                        if reg_py is not None and rmap_py is not None:
                            r_idx = rmap_py[s_id] * n_regs + rmap_py[d_id]
                            if 1 <= k_id <= 3:
                                reg_py[r_idx][k_id - 1] += 1

        ev_compact_py = {k: tuple(v) for k, v in ev_py.items()}
        return total_edges, live_edges, g1_py, g2_py, g3_py, reg_py, ev_compact_py


def stream_edges_hic_and_ev(
    db_path: str,
    max_decl_id: int,
    bin_by_id: Sequence[int],
    dfs_order: Sequence[int],
    regions: Sequence[Dict[str, Any]],
    n_bins: int = 256,
    candidate_ids: Optional[Set[int]] = None,
    workers: int = 0,
) -> Dict[str, Any]:
    """Stream all `edges` once to build `256x256` Hi-C matrices + candidate `E_V` sets."""
    global _SHARED_DB_PATH, _SHARED_BIN_ARR, _SHARED_REG_ARR
    global _SHARED_N_BINS, _SHARED_N_REGS, _SHARED_CAND_MASK, _SHARED_CAN_PACK64

    n_cells = n_bins * n_bins
    n_regs = len(regions)
    if max_decl_id < 0:
        empty_2d = [[0] * n_bins for _ in range(n_bins)]
        return {
            "total_edges": 0,
            "live_edges": 0,
            "unmapped_edges": 0,
            "grid_type_only": empty_2d,
            "grid_value_only": empty_2d,
            "grid_both": empty_2d,
            "region_matrix": [],
            "ev_sets": {},
        }

    # Build region lookup per decl_id
    reg_by_id = [-1] * (max_decl_id + 1)
    for r_idx, reg in enumerate(regions):
        s_pos, e_pos = int(reg["dfs_start"]), int(reg["dfs_end"])
        for pos in range(s_pos, e_pos):
            reg_by_id[dfs_order[pos]] = r_idx

    can_pack64 = (np is not None) and (max_decl_id < (1 << 30))
    if np is not None and can_pack64:
        bin_arr: Any = np.asarray(bin_by_id, dtype=np.int32)
        reg_arr: Any = np.asarray(reg_by_id, dtype=np.int32) if n_regs > 0 else None
        if candidate_ids is not None:
            cand_arr: Any = np.zeros(max_decl_id + 1, dtype=bool)
            valid_cands = [cid for cid in candidate_ids if 0 <= cid <= max_decl_id]
            if valid_cands:
                cand_arr[valid_cands] = True
        else:
            cand_arr = None
    else:
        bin_arr = list(bin_by_id)
        reg_arr = reg_by_id if n_regs > 0 else None
        if candidate_ids is not None:
            cand_arr = [False] * (max_decl_id + 1)
            for cid in candidate_ids:
                if 0 <= cid <= max_decl_id:
                    cand_arr[cid] = True
        else:
            cand_arr = None

    _SHARED_DB_PATH = db_path
    _SHARED_BIN_ARR = bin_arr
    _SHARED_REG_ARR = reg_arr
    _SHARED_N_BINS = n_bins
    _SHARED_N_REGS = n_regs
    _SHARED_CAND_MASK = cand_arr
    _SHARED_CAN_PACK64 = can_pack64

    if workers <= 0:
        workers = min(24, os.cpu_count() or 4)

    use_mp = (
        workers > 1
        and max_decl_id >= 50_000
        and np is not None
        and can_pack64
        and "fork" in mp.get_all_start_methods()
    )

    if use_mp:
        step = (max_decl_id + 1 + workers - 1) // workers
        shards = [(i * step, min(max_decl_id + 1, (i + 1) * step)) for i in range(workers)]
        shards = [s for s in shards if s[0] < s[1]]
        ctx = mp.get_context("fork")
        with ctx.Pool(len(shards)) as pool:
            parts = pool.map(_fused_edge_worker, shards)
    else:
        parts = [_fused_edge_worker((0, max_decl_id + 1))]

    total_edges = sum(p[0] for p in parts)
    live_edges = sum(p[1] for p in parts)

    if np is not None and can_pack64:
        g1_flat = np.zeros(n_cells, dtype=np.int64)
        g2_flat = np.zeros(n_cells, dtype=np.int64)
        g3_flat = np.zeros(n_cells, dtype=np.int64)
        reg_sum = np.zeros((n_regs * n_regs, 3), dtype=np.int64) if n_regs > 0 else None
        for p in parts:
            g1_flat += p[2]
            g2_flat += p[3]
            g3_flat += p[4]
            if reg_sum is not None and p[5] is not None:
                reg_sum += p[5]
        g1_2d = g1_flat.reshape((n_bins, n_bins)).tolist()
        g2_2d = g2_flat.reshape((n_bins, n_bins)).tolist()
        g3_2d = g3_flat.reshape((n_bins, n_bins)).tolist()
        reg_list = reg_sum.tolist() if reg_sum is not None else []
    else:
        g1_py = [0] * n_cells
        g2_py = [0] * n_cells
        g3_py = [0] * n_cells
        reg_list = [[0, 0, 0] for _ in range(n_regs * n_regs)] if n_regs > 0 else []
        for p in parts:
            for idx in range(n_cells):
                g1_py[idx] += p[2][idx]
                g2_py[idx] += p[3][idx]
                g3_py[idx] += p[4][idx]
            if n_regs > 0 and p[5] is not None:
                for r_i in range(n_regs * n_regs):
                    reg_list[r_i][0] += p[5][r_i][0]
                    reg_list[r_i][1] += p[5][r_i][1]
                    reg_list[r_i][2] += p[5][r_i][2]
        g1_2d = [g1_py[r * n_bins : (r + 1) * n_bins] for r in range(n_bins)]
        g2_2d = [g2_py[r * n_bins : (r + 1) * n_bins] for r in range(n_bins)]
        g3_2d = [g3_py[r * n_bins : (r + 1) * n_bins] for r in range(n_bins)]

    ev_sets: Dict[int, FrozenSetType] = {}
    for p in parts:
        for k_id, vals in p[6].items():
            ev_sets[k_id] = frozenset(vals)

    # Clear shared globals promptly
    _SHARED_BIN_ARR = None
    _SHARED_REG_ARR = None
    _SHARED_CAND_MASK = None

    return {
        "total_edges": int(total_edges),
        "live_edges": int(live_edges),
        "unmapped_edges": int(total_edges - live_edges),
        "grid_type_only": g1_2d,
        "grid_value_only": g2_2d,
        "grid_both": g3_2d,
        "region_matrix": reg_list,
        "ev_sets": ev_sets,
    }


FrozenSetType = frozenset[int]


# ---------------------------------------------------------------------------
# 1. Same-Theorem, Alien-Proof Splitter (`alien_twins`)
# ---------------------------------------------------------------------------

def prepare_alien_candidates(
    con: sqlite3.Connection,
    tier2_con: Optional[sqlite3.Connection] = None,
    min_type_nodes: int = 4,
    max_named_reps: int = 16,
    max_aux_reps: int = 4,
) -> Dict[str, Any]:
    """Scan `decls`/`consts` `k1n` collision buckets and select deterministic representatives."""
    mod_map: Dict[int, Optional[str]] = {}
    method_map: Dict[int, str] = {}
    if _table_exists(con, "decl_module"):
        for did, mod, meth in con.execute("SELECT decl_id, module, method FROM decl_module"):
            mod_map[int(did)] = mod
            method_map[int(did)] = str(meth)

    decl_cols = _table_columns(con, "decls")
    has_src_repo = "src_repo" in decl_cols

    # Optional cross-corpus enrichment from tier2.db
    t2_lib_repo: Dict[int, Tuple[str, str]] = {}
    if tier2_con is not None and _table_exists(tier2_con, "kernel_matches"):
        for did, lconst, lrepo, lorig in tier2_con.execute(
            "SELECT decl_id, lib_const_name, lib_repo, lib_origin FROM kernel_matches WHERE variant='k1n'"
        ):
            t2_lib_repo[int(did)] = (str(lrepo or lorig), str(lconst))

    # Fallback sighash lookup from `consts` if `decls.sighash` is unpopulated
    const_sighash: Dict[int, str] = {}
    if _table_exists(con, "consts"):
        null_cnt = con.execute("SELECT COUNT(*) FROM decls WHERE kind='thm' AND sighash IS NULL").fetchone()[0]
        if null_cnt > 0:
            for did, csh in con.execute(
                "SELECT decl_id, sighash FROM consts WHERE ckind='thm' AND sighash IS NOT NULL"
            ):
                const_sighash[int(did)] = str(csh)

    buckets: Dict[str, List[Tuple[int, str, int, int, int, str, Optional[str]]]] = collections.defaultdict(list)
    total_thm_decls = 0
    excluded_trivial = 0

    sql = (
        "SELECT id, name, type_nodes, value_nodes, live_mask, sighash, src_repo FROM decls WHERE kind='thm'"
        if has_src_repo
        else "SELECT id, name, type_nodes, value_nodes, live_mask, sighash, NULL FROM decls WHERE kind='thm'"
    )
    for did, name, tnodes, vnodes, live, sh, srepo in con.execute(sql):
        total_thm_decls += 1
        d_i = int(did)
        tn_i = int(tnodes)
        sh_s = str(sh) if sh is not None else const_sighash.get(d_i)
        if not sh_s:
            continue
        if tn_i < min_type_nodes:
            excluded_trivial += 1
            continue
        orig = classify_decl_origin(str(name), mod_map.get(d_i), method_map.get(d_i), str(srepo) if srepo else None)
        buckets[sh_s].append((d_i, str(name), tn_i, int(vnodes), int(live), orig, mod_map.get(d_i)))

    multi_buckets = {sh: mems for sh, mems in buckets.items() if len(mems) >= 2}

    selected_buckets: Dict[str, List[Tuple[int, str, int, int, int, str, Optional[str]]]] = {}
    cand_ids: Set[int] = set()
    n_named_buckets = 0
    n_cross_repo_buckets = 0
    bucket_sizes: Dict[str, int] = {}

    for sh in sorted(multi_buckets.keys()):
        mems = multi_buckets[sh]
        bucket_sizes[sh] = len(mems)
        has_named = any(not is_aux_decl_name(m[1]) for m in mems)
        if has_named:
            n_named_buckets += 1
        origins = {m[5] for m in mems}
        if len(origins) >= 2:
            n_cross_repo_buckets += 1

        cap = max_named_reps if has_named else max_aux_reps
        if len(mems) <= cap:
            chosen = sorted(mems, key=lambda x: x[0])
        else:
            scored = sorted(
                mems,
                key=lambda x: (
                    1 if is_aux_decl_name(x[1]) else 0,
                    0 if x[5] != "project" else 1,
                    -x[3],
                    x[0],
                ),
            )
            chosen_list: List[Tuple[int, str, int, int, int, str, Optional[str]]] = []
            seen_scope: Set[Tuple[str, str]] = set()
            rest: List[Tuple[int, str, int, int, int, str, Optional[str]]] = []
            for item in scored:
                scope_key = (item[5], item[6] or top_namespace(item[1]))
                if scope_key not in seen_scope and len(chosen_list) < cap:
                    seen_scope.add(scope_key)
                    chosen_list.append(item)
                else:
                    rest.append(item)
            if len(chosen_list) < cap:
                chosen_list.extend(rest[: cap - len(chosen_list)])
            chosen = sorted(chosen_list, key=lambda x: x[0])

        selected_buckets[sh] = chosen
        for item in chosen:
            cand_ids.add(item[0])

    return {
        "total_thm_decls": total_thm_decls,
        "excluded_trivial_thms": excluded_trivial,
        "min_type_nodes": min_type_nodes,
        "nontrivial_collision_buckets": len(multi_buckets),
        "named_collision_buckets": n_named_buckets,
        "cross_repo_collision_buckets": n_cross_repo_buckets,
        "selected_buckets": selected_buckets,
        "bucket_sizes": bucket_sizes,
        "candidate_ids": cand_ids,
        "t2_lib_repo": t2_lib_repo,
    }


def _has_back_edges(con: sqlite3.Connection) -> bool:
    row = con.execute("SELECT 1 FROM edges WHERE src < 50000 AND src <= dst LIMIT 1").fetchone()
    if row is not None:
        return True
    row2 = con.execute("SELECT 1 FROM edges WHERE src <= dst LIMIT 1").fetchone()
    return row2 is not None


def _is_transitively_independent(
    con: sqlite3.Connection,
    u: int,
    v: int,
    dag_topological: bool,
) -> bool:
    """Return True iff neither `u` reaches `v` nor `v` reaches `u` across any edge path."""
    for start, target in ((u, v), (v, u)):
        if dag_topological and start < target:
            continue
        visited = {start}
        frontier = [start]
        while frontier:
            batch = frontier[:400]
            frontier = frontier[400:]
            qmarks = ",".join("?" for _ in batch)
            if dag_topological:
                rows = con.execute(
                    f"SELECT dst FROM edges WHERE src IN ({qmarks}) AND dst >= ?",
                    (*batch, target),
                ).fetchall()
            else:
                rows = con.execute(
                    f"SELECT dst FROM edges WHERE src IN ({qmarks})",
                    batch,
                ).fetchall()
            for (dst,) in rows:
                d_i = int(dst)
                if d_i == target:
                    return False
                if d_i not in visited:
                    visited.add(d_i)
                    frontier.append(d_i)
    return True


def _resolve_module_lines(
    leanre_db_path: Optional[str],
    decl_names: Set[str],
) -> Dict[str, Tuple[str, int]]:
    """Lookup `(module, line_no)` from `outputs/leanre.db` if available (read-only)."""
    if not leanre_db_path or not os.path.isfile(os.path.realpath(leanre_db_path)) or not decl_names:
        return {}
    out: Dict[str, Tuple[str, int]] = {}
    try:
        with contextlib.closing(connect_ro(leanre_db_path)) as ldb:
            if not _table_exists(ldb, "declarations"):
                return {}
            names_list = sorted(decl_names)
            for i in range(0, len(names_list), 400):
                chunk = names_list[i : i + 400]
                qmarks = ",".join("?" for _ in chunk)
                for nm, mod, lno in ldb.execute(
                    f"SELECT name, module, line_no FROM declarations WHERE name IN ({qmarks})",
                    chunk,
                ):
                    s_nm = str(nm)
                    if s_nm not in out:
                        out[s_nm] = (str(mod), int(lno))
    except OSError:
        return {}
    return out


def finalize_alien_twins(
    con: sqlite3.Connection,
    prep: Dict[str, Any],
    ev_sets: Dict[int, FrozenSetType],
    min_spot_value_nodes: int = 15,
    top_k: int = 12,
    leanre_db_path: Optional[str] = None,
) -> Dict[str, Any]:
    """Compute Jaccard partitions (`clone`, `variant`, `alien_proof`) and rank top twins."""
    selected_buckets = prep["selected_buckets"]
    bucket_sizes = prep["bucket_sizes"]

    partition_all = {"clone": 0, "variant": 0, "alien_proof": 0}
    partition_diff_scope = {"clone": 0, "variant": 0, "alien_proof": 0}
    partition_named_diff_scope = {"clone": 0, "variant": 0, "alien_proof": 0}
    partition_cross_repo = {"clone": 0, "variant": 0, "alien_proof": 0}
    direct_delegates_skipped = 0
    jaccard_hist_20 = [0] * 20

    raw_cross_cands: List[Tuple[Any, ...]] = []
    raw_intra_cands: List[Tuple[Any, ...]] = []
    bucket_summaries: List[Tuple[int, str, int, Dict[str, int], str]] = []

    for sh, mems in selected_buckets.items():
        b_counts = {"clone": 0, "variant": 0, "alien_proof": 0}
        n = len(mems)
        for i in range(n):
            id_a, name_a, tn_a, vn_a, live_a, orig_a, mod_a = mems[i]
            scope_a = mod_a or top_namespace(name_a)
            aux_a = is_aux_decl_name(name_a)
            ev_a = ev_sets.get(id_a, frozenset())

            for j in range(i + 1, n):
                id_b, name_b, tn_b, vn_b, live_b, orig_b, mod_b = mems[j]
                scope_b = mod_b or top_namespace(name_b)
                aux_b = is_aux_decl_name(name_b)
                ev_b = ev_sets.get(id_b, frozenset())

                if (id_b in ev_a) or (id_a in ev_b):
                    direct_delegates_skipped += 1
                    continue

                u_len = len(ev_a | ev_b)
                inter_len = len(ev_a & ev_b)
                jac = 1.0 if u_len == 0 else (inter_len / u_len)

                if jac >= JACCARD_CLONE_MIN:
                    cat = "clone"
                elif jac >= JACCARD_VARIANT_MIN:
                    cat = "variant"
                else:
                    cat = "alien_proof"

                partition_all[cat] += 1
                b_counts[cat] += 1
                h_bin = min(19, int(jac * 20.0))
                jaccard_hist_20[h_bin] += 1

                diff_scope = (orig_a != orig_b) or (scope_a != scope_b)
                if diff_scope:
                    partition_diff_scope[cat] += 1
                    if not aux_a and not aux_b:
                        partition_named_diff_scope[cat] += 1
                if orig_a != orig_b:
                    partition_cross_repo[cat] += 1

                is_proj_vs_lib = (orig_a == "project") != (orig_b == "project")
                is_both_proj = (orig_a == "project") and (orig_b == "project")
                if (
                    cat == "alien_proof"
                    and diff_scope
                    and (is_proj_vs_lib or is_both_proj)
                    and not aux_a
                    and not aux_b
                    and vn_a >= min_spot_value_nodes
                    and vn_b >= min_spot_value_nodes
                    and len(ev_a) >= 2
                    and len(ev_b) >= 2
                ):
                    rec = (
                        jac,
                        -min(tn_a, tn_b),
                        -min(vn_a, vn_b),
                        id_a,
                        id_b,
                        sh,
                        mems[i],
                        len(ev_a),
                        mems[j],
                        len(ev_b),
                        inter_len,
                        u_len,
                    )
                    if is_proj_vs_lib:
                        raw_cross_cands.append(rec)
                    else:
                        raw_intra_cands.append(rec)

        if sum(b_counts.values()) > 0:
            rep_name = next((m[1] for m in mems if not is_aux_decl_name(m[1])), mems[0][1])
            bucket_summaries.append((bucket_sizes[sh], sh, mems[0][2], b_counts, rep_name))

    raw_cross_cands.sort()
    raw_intra_cands.sort()
    bucket_summaries.sort(key=lambda x: (-x[0], x[1]))

    dag_topological = not _has_back_edges(con)

    def _select_verified_top(cands: Sequence[Tuple[Any, ...]], limit: int) -> List[Dict[str, Any]]:
        out: List[Dict[str, Any]] = []
        seen_sh: Set[str] = set()
        for rec in cands:
            jac, _ntn, _nvn, id_a, id_b, sh, ma, eva_n, mb, evb_n, inter_n, u_n = rec
            if sh in seen_sh:
                continue
            # Prefer genuinely live declarations when available
            if not _is_transitively_independent(con, id_a, id_b, dag_topological):
                continue
            seen_sh.add(sh)
            out.append({
                "sighash": sh,
                "jaccard": round(float(jac), 6),
                "shared_ev_count": int(inter_n),
                "union_ev_count": int(u_n),
                "type_nodes": int(ma[2]),
                "bucket_size": int(bucket_sizes.get(sh, 2)),
                "pair_scope": "cross_repo" if ma[5] != mb[5] else "intra_project",
                "thm_a": {
                    "decl_id": int(ma[0]),
                    "name": ma[1],
                    "origin": ma[5],
                    "module": ma[6],
                    "value_nodes": int(ma[3]),
                    "ev_size": int(eva_n),
                    "live": bool(ma[4] != 0),
                },
                "thm_b": {
                    "decl_id": int(mb[0]),
                    "name": mb[1],
                    "origin": mb[5],
                    "module": mb[6],
                    "value_nodes": int(mb[3]),
                    "ev_size": int(evb_n),
                    "live": bool(mb[4] != 0),
                },
            })
            if len(out) >= limit:
                break
        return out

    top_cross = _select_verified_top(raw_cross_cands, top_k)
    top_intra = _select_verified_top(raw_intra_cands, top_k)

    # Enrich top pairs with line numbers from `leanre.db` if available
    need_lines: Set[str] = set()
    for p in top_cross + top_intra:
        for side in ("thm_a", "thm_b"):
            if p[side]["origin"] == "project":
                need_lines.add(p[side]["name"])
                if p[side]["name"].startswith("_root_."):
                    need_lines.add(p[side]["name"][7:])
    line_lookup = _resolve_module_lines(leanre_db_path, need_lines)
    for p in top_cross + top_intra:
        for side in ("thm_a", "thm_b"):
            nm = p[side]["name"]
            hit = line_lookup.get(nm) or line_lookup.get(nm[7:] if nm.startswith("_root_.") else nm)
            if hit is not None:
                if not p[side]["module"]:
                    p[side]["module"] = hit[0]
                p[side]["line_no"] = hit[1]
            if p[side]["module"]:
                p[side]["src_rel_path"] = "src/" + p[side]["module"].replace(".", "/") + ".lean"

    # Build combined top-10 lowest-J non-trivial alien_proof showcase (balanced intra + cross-repo)
    combined = sorted(
        top_intra + top_cross,
        key=lambda r: (r["jaccard"], -min(r["thm_a"]["value_nodes"], r["thm_b"]["value_nodes"]), r["sighash"]),
    )
    seen_comb: Set[str] = set()
    top_combined: List[Dict[str, Any]] = []
    for item in combined:
        if item["sighash"] not in seen_comb:
            seen_comb.add(item["sighash"])
            top_combined.append(item)
        if len(top_combined) >= top_k:
            break

    top_buckets_out = [
        {
            "sighash": sh,
            "size": int(sz),
            "type_nodes": int(tn),
            "representative": rep,
            "sampled_pairs": cnts,
        }
        for sz, sh, tn, cnts, rep in bucket_summaries[:15]
    ]

    return {
        "thresholds": {
            "clone_min_jaccard": JACCARD_CLONE_MIN,
            "variant_min_jaccard": JACCARD_VARIANT_MIN,
            "min_type_nodes": prep["min_type_nodes"],
            "min_spot_value_nodes": min_spot_value_nodes,
        },
        "counts": {
            "total_thm_decls": prep["total_thm_decls"],
            "excluded_trivial_thms": prep["excluded_trivial_thms"],
            "nontrivial_collision_buckets": prep["nontrivial_collision_buckets"],
            "named_collision_buckets": prep["named_collision_buckets"],
            "cross_repo_collision_buckets": prep["cross_repo_collision_buckets"],
            "candidate_thms_sampled": len(prep["candidate_ids"]),
            "sampled_pairs_evaluated": sum(partition_all.values()),
            "direct_delegates_skipped": direct_delegates_skipped,
        },
        "partitions": {
            "all_sampled_pairs": partition_all,
            "diff_scope_pairs": partition_diff_scope,
            "named_diff_scope_pairs": partition_named_diff_scope,
            "cross_repo_pairs": partition_cross_repo,
        },
        "jaccard_histogram_20bins": jaccard_hist_20,
        "top_alien_pairs": top_combined,
        "top_alien_pairs_intra": top_intra,
        "top_alien_pairs_cross_repo": top_cross,
        "top_collision_buckets": top_buckets_out,
    }


def compute_alien_twins(
    kernel_db_path: str,
    tier2_db_path: Optional[str] = None,
    leanre_db_path: Optional[str] = None,
    min_type_nodes: int = 4,
    min_spot_value_nodes: int = 15,
    workers: int = 0,
) -> Dict[str, Any]:
    """Standalone entry point for `Same-Theorem, Alien-Proof Splitter`."""
    t0 = time.perf_counter()
    t2_con = (
        connect_ro(tier2_db_path)
        if (tier2_db_path and os.path.isfile(os.path.realpath(tier2_db_path)))
        else None
    )
    try:
        with contextlib.closing(connect_ro(kernel_db_path)) as con:
            max_row = con.execute("SELECT MAX(id) FROM decls").fetchone()
            max_id = int(max_row[0]) if (max_row and max_row[0] is not None) else -1
            prep = prepare_alien_candidates(con, tier2_con=t2_con, min_type_nodes=min_type_nodes)
            dummy_bins = [0] * (max_id + 1) if max_id >= 0 else []
            stream = stream_edges_hic_and_ev(
                kernel_db_path,
                max_decl_id=max_id,
                bin_by_id=dummy_bins,
                dfs_order=[],
                regions=[],
                n_bins=1,
                candidate_ids=prep["candidate_ids"],
                workers=workers,
            )
            res = finalize_alien_twins(
                con,
                prep,
                stream["ev_sets"],
                min_spot_value_nodes=min_spot_value_nodes,
                leanre_db_path=leanre_db_path,
            )
            res["runtime_sec"] = round(time.perf_counter() - t0, 3)
            return res
    finally:
        if t2_con is not None:
            t2_con.close()


# ---------------------------------------------------------------------------
# 2. Hi-C Contact Matrix Post-Processing & Quantization (`hic_matrix`)
# ---------------------------------------------------------------------------

def _downsample_grid(grid: Sequence[Sequence[int]], out_size: int) -> List[List[int]]:
    in_size = len(grid)
    if in_size == 0 or out_size <= 0:
        return []
    if in_size == out_size:
        return [list(row) for row in grid]
    out = [[0] * out_size for _ in range(out_size)]
    for r in range(in_size):
        orow = (r * out_size) // in_size
        grow = grid[r]
        out_r = out[orow]
        for c in range(in_size):
            out_r[(c * out_size) // in_size] += grow[c]
    return out


def summarize_hic_matrix(
    dom_info: Dict[str, Any],
    edge_stream: Dict[str, Any],
    n_bins: int = 256,
    tile_size: int = 128,
    ratio_clip_nat: float = 3.5,
) -> Dict[str, Any]:
    """Compute `log1p(count)`, diverging `log((E_T+1)/(E_V+1))`, and `128x128` `<canvas>` tiles."""
    g_t = edge_stream["grid_type_only"]
    g_v = edge_stream["grid_value_only"]
    g_b = edge_stream["grid_both"]

    sum_t = sum(sum(r) for r in g_t)
    sum_v = sum(sum(r) for r in g_v)
    sum_b = sum(sum(r) for r in g_b)

    # Downsample 256x256 -> 128x128 for compact HTML5 <canvas> rendering and 32x32 for exact counts
    t_128 = _downsample_grid(g_t, tile_size)
    v_128 = _downsample_grid(g_v, tile_size)
    b_128 = _downsample_grid(g_b, tile_size)

    t_32 = _downsample_grid(g_t, 32)
    v_32 = _downsample_grid(g_v, 32)
    b_32 = _downsample_grid(g_b, 32)

    # Quantize 128x128 `log1p(total)` and diverging `log((E_T+1)/(E_V+1))` into uint8 [0..255]
    # Note: E_T = type_only + both, E_V = value_only + both
    max_log1p = 0.0
    log_totals: List[List[float]] = []
    ratios: List[List[float]] = []
    nonzero_cells_128 = 0
    type_dominant_cells_128 = 0
    value_dominant_cells_128 = 0

    for r in range(tile_size):
        lt_row: List[float] = []
        rt_row: List[float] = []
        for c in range(tile_size):
            ct = t_128[r][c]
            cv = v_128[r][c]
            cb = b_128[r][c]
            tot = ct + cv + cb
            if tot > 0:
                nonzero_cells_128 += 1
            lv = math.log1p(tot)
            if lv > max_log1p:
                max_log1p = lv
            et = ct + cb
            ev = cv + cb
            lr = math.log((et + 1.0) / (ev + 1.0))
            if tot > 0:
                if lr > 0.25:
                    type_dominant_cells_128 += 1
                elif lr < -0.25:
                    value_dominant_cells_128 += 1
            lt_row.append(lv)
            rt_row.append(lr)
        log_totals.append(lt_row)
        ratios.append(rt_row)

    denom_log = max_log1p if max_log1p > 0.0 else 1.0
    total_q8: List[List[int]] = []
    ratio_q8: List[List[int]] = []
    for r in range(tile_size):
        tq_row: List[int] = []
        rq_row: List[int] = []
        for c in range(tile_size):
            lv = log_totals[r][c]
            if lv <= 0.0:
                tq_row.append(0)
                rq_row.append(128)
            else:
                q_t = max(1, min(255, int(round(255.0 * (lv / denom_log)))))
                clipped = max(-ratio_clip_nat, min(ratio_clip_nat, ratios[r][c]))
                q_r = max(0, min(255, int(round(128.0 + 127.0 * (clipped / ratio_clip_nat)))))
                tq_row.append(q_t)
                rq_row.append(q_r)
        total_q8.append(tq_row)
        ratio_q8.append(rq_row)

    # Compute 256x256 cell statistics as well
    nonzero_256 = 0
    diag_edges = 0
    max_cell_256 = 0
    for r in range(n_bins):
        for c in range(n_bins):
            tot = g_t[r][c] + g_v[r][c] + g_b[r][c]
            if tot > 0:
                nonzero_256 += 1
                if tot > max_cell_256:
                    max_cell_256 = tot
                if r == c:
                    diag_edges += tot

    # Format region-to-region block coupling table
    regions = dom_info["regions"]
    n_regs = len(regions)
    reg_raw = edge_stream["region_matrix"]
    region_couplings: List[Dict[str, Any]] = []
    if n_regs > 0 and reg_raw:
        for i in range(n_regs):
            for j in range(n_regs):
                t_c, v_c, b_c = reg_raw[i * n_regs + j]
                tot_c = t_c + v_c + b_c
                if tot_c == 0:
                    continue
                et = t_c + b_c
                ev = v_c + b_c
                region_couplings.append({
                    "src_region": regions[i]["key"],
                    "src_label": regions[i]["label"],
                    "dst_region": regions[j]["key"],
                    "dst_label": regions[j]["label"],
                    "type_only": int(t_c),
                    "value_only": int(v_c),
                    "both": int(b_c),
                    "total": int(tot_c),
                    "log_ratio_et_ev": round(math.log((et + 1.0) / (ev + 1.0)), 4),
                })

    return {
        "tree_id": dom_info["tree_id"],
        "n_live_decls": dom_info["n_live"],
        "total_decls_in_db": dom_info["total_decls"],
        "grid_bins": n_bins,
        "edge_totals": {
            "total_streamed": edge_stream["total_edges"],
            "live_binned": edge_stream["live_edges"],
            "unmapped_nonlive": edge_stream["unmapped_edges"],
            "type_only": int(sum_t),
            "value_only": int(sum_v),
            "both": int(sum_b),
            "diagonal_256_bin_edges": int(diag_edges),
            "diagonal_256_share_pct": round(100.0 * diag_edges / max(1, edge_stream["live_edges"]), 3),
            "nonzero_cells_256": int(nonzero_256),
            "max_cell_edges_256": int(max_cell_256),
        },
        "pillar_ticks": dom_info["pillar_ticks"],
        "regions": regions,
        "region_couplings": region_couplings,
        "coarse_32": {
            "size": 32,
            "type_only": t_32,
            "value_only": v_32,
            "both": b_32,
        },
        "tile_128": {
            "size": tile_size,
            "encoding": "uint8_2d",
            "max_log1p": round(max_log1p, 6),
            "ratio_clip_nat": ratio_clip_nat,
            "neutral_ratio_q8": 128,
            "nonzero_cells": nonzero_cells_128,
            "type_dominant_cells": type_dominant_cells_128,
            "value_dominant_cells": value_dominant_cells_128,
            "palette_hint": {
                "type_dominant": "cyan (#1ed7ff)",
                "balanced": "silver-white (#dce2f7)",
                "value_dominant": "amber (#ffaa23)",
                "empty": "obsidian (#0a0c12)",
            },
            "total_log1p_q8": total_q8,
            "ratio_diverging_q8": ratio_q8,
        },
    }


# ---------------------------------------------------------------------------
# 3. Cross-Library Structural Synteny Dot-Plot (`synteny`)
# ---------------------------------------------------------------------------

def compute_synteny(
    con: sqlite3.Connection,
    dom_info: Dict[str, Any],
    tier2_con: Optional[sqlite3.Connection] = None,
    min_type_nodes: int = 4,
    grid_size: int = 128,
    dfs_bins: int = 256,
) -> Dict[str, Any]:
    """Compute cross-library `(project_dfs_idx, library_order_idx)` synteny & novel bands."""
    t0 = time.perf_counter()
    n_live = dom_info["n_live"]
    tin_by_id = dom_info["tin_by_id"]
    pillar_ticks = dom_info["pillar_ticks"]

    mod_map: Dict[int, Optional[str]] = {}
    method_map: Dict[int, str] = {}
    if _table_exists(con, "decl_module"):
        for did, mod, meth in con.execute("SELECT decl_id, module, method FROM decl_module"):
            mod_map[int(did)] = mod
            method_map[int(did)] = str(meth)

    decl_cols = _table_columns(con, "decls")
    has_src_repo = "src_repo" in decl_cols
    sql_decls = (
        "SELECT id, name, kind, type_nodes, sighash, sighash_anon, src_repo FROM decls ORDER BY id ASC"
        if has_src_repo
        else "SELECT id, name, kind, type_nodes, sighash, sighash_anon, NULL FROM decls ORDER BY id ASC"
    )

    lib_decls: List[Tuple[int, str, str, int, Optional[str], Optional[str], str]] = []
    proj_decls: List[Tuple[int, str, str, int, Optional[str], Optional[str]]] = []
    for did, name, kind, tnodes, sh_n, sh_a, srepo in con.execute(sql_decls):
        d_i = int(did)
        s_name = str(name)
        s_kind = str(kind)
        tn_i = int(tnodes)
        orig = classify_decl_origin(s_name, mod_map.get(d_i), method_map.get(d_i), str(srepo) if srepo else None)
        if orig != "project":
            lib_decls.append((d_i, s_name, s_kind, tn_i, sh_n, sh_a, orig))
        else:
            proj_decls.append((d_i, s_name, s_kind, tn_i, sh_n, sh_a))

    n_lib = len(lib_decls)
    lib_rank_by_id = {d[0]: idx for idx, d in enumerate(lib_decls)}

    # Build 8 Y-axis library strata summaries
    library_strata: List[Dict[str, Any]] = []
    if n_lib > 0:
        n_strata = min(8, n_lib)
        for s_idx in range(n_strata):
            lo = (s_idx * n_lib) // n_strata
            hi = ((s_idx + 1) * n_lib) // n_strata
            pref_counter: collections.Counter[str] = collections.Counter()
            for item in lib_decls[lo:hi]:
                nm = item[1]
                if nm.startswith("_private."):
                    segs = nm[len("_private."):].split(".")
                    p_tok = segs[0] if segs else "private"
                else:
                    p_tok = nm.split(".", 1)[0]
                pref_counter[p_tok] += 1
            top_prefs = [k for k, _ in pref_counter.most_common(3)]
            library_strata.append({
                "stratum": s_idx,
                "lib_idx_start": lo,
                "lib_idx_end": hi,
                "count": hi - lo,
                "top_namespaces": top_prefs,
            })

    repos_order = ["mathlib4", "lean4", "batteries", "PrimeNumberTheoremAnd", "FLT", "carleson", "SpherePacking", "library_other"]
    repo_to_idx = {r: i for i, r in enumerate(repos_order)}

    # Collect (proj_dfs_idx, lib_order_idx, is_aux, kind, repo, type_nodes, channel) hits
    hits: List[Tuple[int, int, bool, str, str, int, str]] = []
    source_used = "kernel_db_fallback"
    external_source_hits: Dict[str, int] = collections.Counter()

    # Build library k1n/k1a indexes so both tier2 and fallback capture net-new k1a anonymized hits
    lib_by_k1n: Dict[str, Tuple[int, str]] = {}
    lib_by_k1a: Dict[str, Tuple[int, str]] = {}
    for d_i, _nm, _kd, tn_i, sh_n, sh_a, orig in lib_decls:
        if tn_i < min_type_nodes:
            continue
        l_rank = lib_rank_by_id[d_i]
        if sh_n and str(sh_n) not in lib_by_k1n:
            lib_by_k1n[str(sh_n)] = (l_rank, orig)
        if sh_a and str(sh_a) not in lib_by_k1a:
            lib_by_k1a[str(sh_a)] = (l_rank, orig)

    seen_decl_ids: Set[int] = set()
    if tier2_con is not None and _table_exists(tier2_con, "kernel_matches"):
        source_used = "tier2_db"
        const_to_decl: Dict[str, int] = {}
        if _table_exists(con, "consts"):
            for cname, cid in con.execute("SELECT name, decl_id FROM consts"):
                const_to_decl[str(cname)] = int(cid)
        else:
            for item in lib_decls:
                const_to_decl[item[1]] = item[0]

        # Priority 1: exact `k1n`, Priority 2: anonymized `k1a` from tier2
        for variant in ("k1n", "k1a"):
            for did, cname, ckind, is_aux, lconst, lrepo, lorig, tnodes in tier2_con.execute(
                "SELECT decl_id, const_name, ckind, is_aux, lib_const_name, lib_repo, lib_origin, type_nodes "
                "FROM kernel_matches WHERE variant=? AND type_nodes >= ?",
                (variant, min_type_nodes),
            ):
                d_i = int(did)
                if d_i in seen_decl_ids or d_i < 0 or d_i >= len(tin_by_id):
                    continue
                px = tin_by_id[d_i]
                if px < 0:
                    continue
                lid = const_to_decl.get(str(lconst))
                if lid is None or lid not in lib_rank_by_id:
                    continue
                seen_decl_ids.add(d_i)
                repo_s = str(lrepo or lorig or "mathlib4")
                external_source_hits[repo_s] += 1
                hits.append((px, lib_rank_by_id[lid], bool(is_aux), str(ckind), repo_s, int(tnodes), variant))

        # Supplement with net-new anonymized `k1a` matches from `kernel.db` (where project-local types anonymized)
        for d_i, s_name, s_kind, tn_i, _sh_n, sh_a in proj_decls:
            if d_i in seen_decl_ids or tn_i < min_type_nodes or d_i >= len(tin_by_id):
                continue
            px = tin_by_id[d_i]
            if px < 0:
                continue
            if sh_a and str(sh_a) in lib_by_k1a:
                seen_decl_ids.add(d_i)
                l_rank, orig = lib_by_k1a[str(sh_a)]
                external_source_hits[orig] += 1
                hits.append((px, l_rank, is_aux_decl_name(s_name), s_kind, orig, tn_i, "k1a"))

        # Also record strong cross-repo source matches (`FLT`, `PrimeNumberTheoremAnd`, `carleson`, `SpherePacking`)
        if _table_exists(tier2_con, "matches"):
            for repo_s, cnt in tier2_con.execute(
                "SELECT repo, COUNT(*) FROM matches WHERE grade='strong' GROUP BY repo"
            ):
                external_source_hits[f"strong_src:{repo_s}"] = int(cnt)
    else:
        # Pure `kernel.db` synteny: match library decls vs project decls by `k1n` then `k1a`
        for d_i, s_name, s_kind, tn_i, sh_n, sh_a in proj_decls:
            if tn_i < min_type_nodes or d_i >= len(tin_by_id):
                continue
            px = tin_by_id[d_i]
            if px < 0:
                continue
            aux = is_aux_decl_name(s_name)
            if sh_n and str(sh_n) in lib_by_k1n:
                l_rank, orig = lib_by_k1n[str(sh_n)]
                external_source_hits[orig] += 1
                hits.append((px, l_rank, aux, s_kind, orig, tn_i, "k1n"))
            elif sh_a and str(sh_a) in lib_by_k1a:
                l_rank, orig = lib_by_k1a[str(sh_a)]
                external_source_hits[orig] += 1
                hits.append((px, l_rank, aux, s_kind, orig, tn_i, "k1a"))

    # Bin hits into `grid_size x grid_size` for JSON `<canvas>` scatter & `256 x 256` for PNG
    denom_x = max(1, n_live)
    denom_y = max(1, n_lib)

    cell_tot: Dict[Tuple[int, int], int] = collections.Counter()
    cell_named: Dict[Tuple[int, int], int] = collections.Counter()
    cell_repos: Dict[Tuple[int, int], collections.Counter[int]] = collections.defaultdict(collections.Counter)

    png_tot = [[0] * 256 for _ in range(256)]
    png_named = [[0] * 256 for _ in range(256)]

    dfs_named_256 = [0] * dfs_bins
    dfs_aux_256 = [0] * dfs_bins
    dfs_proj_256 = [0] * dfs_bins
    for d_i, *_rest in proj_decls:
        if 0 <= d_i < len(tin_by_id) and tin_by_id[d_i] >= 0:
            dfs_proj_256[min(dfs_bins - 1, (tin_by_id[d_i] * dfs_bins) // denom_x)] += 1

    named_points: List[Tuple[int, int, str, str, int]] = []
    n_named_hits = 0
    n_k1n_hits = 0

    for px, ly, aux, ckind, repo_s, tn_i, chan in hits:
        if chan == "k1n":
            n_k1n_hits += 1
        bx = min(grid_size - 1, (px * grid_size) // denom_x)
        by = min(grid_size - 1, (ly * grid_size) // denom_y)
        cell_tot[(bx, by)] += 1
        r_idx = repo_to_idx.get(repo_s, len(repos_order) - 1)
        cell_repos[(bx, by)][r_idx] += 1

        px256 = min(255, (px * 256) // denom_x)
        py256 = min(255, (ly * 256) // denom_y)
        png_tot[py256][px256] += 1

        dbin = min(dfs_bins - 1, (px * dfs_bins) // denom_x)
        if not aux:
            n_named_hits += 1
            cell_named[(bx, by)] += 1
            png_named[py256][px256] += 1
            dfs_named_256[dbin] += 1
            named_points.append((px, ly, ckind, repo_s, tn_i))
        else:
            dfs_aux_256[dbin] += 1

    # Sort binned cells deterministically; if > 3,200 cells, keep top 3,200 by (named_hits > 0, total_hits)
    # so `outputs/atlas_summary.json` stays compact well below 400 KB!
    all_bins_sorted = sorted(
        cell_tot.keys(),
        key=lambda kv: (1 if cell_named[kv] > 0 else 0, cell_tot[kv], -kv[0], -kv[1]),
        reverse=True,
    )
    kept_keys = sorted(all_bins_sorted[:3200])
    binned_points = [
        [bx, by, int(cell_tot[(bx, by)]), int(cell_named[(bx, by)]), int(cell_repos[(bx, by)].most_common(1)[0][0])]
        for (bx, by) in kept_keys
    ]

    # Sample up to 400 highest-complexity named points for interactive tooltip inspection
    named_points.sort(key=lambda x: (-x[4], x[0], x[1]))
    kind_list = ["thm", "def", "induct", "ctor", "other"]
    kind_to_idx = {k: i for i, k in enumerate(kind_list)}
    named_scatter = [
        [
            int(px),
            int(ly),
            kind_to_idx.get(ck, 4),
            repo_to_idx.get(rp, len(repos_order) - 1),
            int(tn),
        ]
        for px, ly, ck, rp, tn in sorted(named_points[:400], key=lambda z: (z[0], z[1]))
    ]

    # Extract collinear diagonal streaks on `grid_size x grid_size` (`(+1, +1)` and `(+1, -1)`)
    streaks = _extract_diagonal_streaks(
        cell_tot, cell_named, grid_size, n_live, n_lib, pillar_ticks, library_strata
    )

    # Identify blank "terra incognita" novel bands along the 256-bin project DFS axis
    terra_bands = _extract_terra_incognita_bands(
        dfs_named_256, dfs_aux_256, dfs_proj_256, dfs_bins, n_live, pillar_ticks
    )

    return {
        "source": source_used,
        "n_live_decls": n_live,
        "n_library_decls": n_lib,
        "min_type_nodes": min_type_nodes,
        "hit_totals": {
            "total_matches": len(hits),
            "named_matches": n_named_hits,
            "aux_matches": len(hits) - n_named_hits,
            "exact_k1n_matches": n_k1n_hits,
            "anon_only_k1a_matches": len(hits) - n_k1n_hits,
            "by_corpus": dict(sorted(external_source_hits.items())),
        },
        "grid_meta": {
            "grid_size": grid_size,
            "total_nonzero_bins": len(cell_tot),
            "emitted_bins": len(binned_points),
            "repos": repos_order,
            "kinds": kind_list,
            "tuple_schema": ["proj_bin", "lib_bin", "total_hits", "named_hits", "dominant_repo_idx"],
            "named_scatter_schema": ["proj_dfs_idx", "lib_order_idx", "kind_idx", "repo_idx", "type_nodes"],
        },
        "library_strata": library_strata,
        "diagonal_streaks": streaks,
        "terra_incognita_bands": terra_bands,
        "dfs_256_named_hits": dfs_named_256,
        "dfs_256_total_hits": [dfs_named_256[i] + dfs_aux_256[i] for i in range(dfs_bins)],
        "binned_points": binned_points,
        "named_scatter": named_scatter,
        "runtime_sec": round(time.perf_counter() - t0, 3),
        "_png_256": {
            "tot": png_tot,
            "named": png_named,
        },
    }


def _pillar_for_dfs_range(s_dfs: int, e_dfs: int, pillar_ticks: Sequence[Dict[str, Any]]) -> str:
    mid = (s_dfs + e_dfs) // 2
    best_label = "Project DFS"
    best_span = 1 << 60
    for t in pillar_ticks:
        if t["key"] in ("allChi", "everyCharacter"):
            continue
        ts, te = int(t["dfs_start"]), int(t["dfs_end"])
        if ts <= mid < te and (te - ts) < best_span:
            best_span = te - ts
            best_label = str(t["label"])
    return best_label


def _extract_diagonal_streaks(
    cell_tot: Dict[Tuple[int, int], int],
    cell_named: Dict[Tuple[int, int], int],
    grid_size: int,
    n_live: int,
    n_lib: int,
    pillar_ticks: Sequence[Dict[str, Any]],
    library_strata: Sequence[Dict[str, Any]],
) -> List[Dict[str, Any]]:
    """Detect collinear ascending `(+1,+1)` and inverted `(+1,-1)` enriched synteny streaks."""
    if not cell_tot:
        return []
    vals = sorted(cell_tot.values())
    p85_val = vals[min(len(vals) - 1, int(0.85 * len(vals)))]
    # Focus on named twins or strongly enriched synteny cells to avoid dense aux noise
    active = {
        k for k, v in cell_tot.items()
        if cell_named.get(k, 0) > 0 or (v >= max(2, p85_val))
    }
    if len(active) < 3:
        active = {k for k, v in cell_tot.items() if v > 0}
    streaks_raw: List[Tuple[int, int, int, str, List[Tuple[int, int]]]] = []

    for dy, dir_name in ((1, "co_linear"), (-1, "inverted_dfs")):
        for (bx, by) in sorted(active):
            if (bx - 1, by - dy) in active:
                continue
            pts = [(bx, by)]
            cx, cy = bx + 1, by + dy
            while 0 <= cx < grid_size and 0 <= cy < grid_size and (cx, cy) in active:
                pts.append((cx, cy))
                cx += 1
                cy += dy
            if len(pts) >= 3:
                tot_h = sum(cell_tot[p] for p in pts)
                nam_h = sum(cell_named[p] for p in pts)
                streaks_raw.append((len(pts), nam_h, tot_h, dir_name, pts))

    streaks_raw.sort(key=lambda x: (x[1] > 0, x[0], x[1], x[2]), reverse=True)
    out: List[Dict[str, Any]] = []
    for length, nam_h, tot_h, dir_name, pts in streaks_raw[:12]:
        x0, y0 = pts[0]
        x1, y1 = pts[-1]
        dfs_s = (x0 * n_live) // grid_size
        dfs_e = ((x1 + 1) * n_live) // grid_size
        ymin, ymax = min(y0, y1), max(y0, y1)
        lib_s = (ymin * n_lib) // grid_size
        lib_e = ((ymax + 1) * n_lib) // grid_size
        dom_stratum = ""
        if library_strata and n_lib > 0:
            s_i = min(len(library_strata) - 1, (((ymin + ymax) // 2) * len(library_strata)) // grid_size)
            dom_stratum = "/".join(library_strata[s_i]["top_namespaces"][:2])
        out.append({
            "direction": dir_name,
            "length_bins": int(length),
            "proj_bin_range": [int(x0), int(x1)],
            "lib_bin_range": [int(y0), int(y1)],
            "dfs_range": [int(dfs_s), int(dfs_e)],
            "lib_idx_range": [int(lib_s), int(lib_e)],
            "total_hits": int(tot_h),
            "named_hits": int(nam_h),
            "pillar": _pillar_for_dfs_range(dfs_s, dfs_e, pillar_ticks),
            "library_domain": dom_stratum,
        })
    return out


def _extract_terra_incognita_bands(
    dfs_named_256: Sequence[int],
    dfs_aux_256: Sequence[int],
    dfs_proj_256: Sequence[int],
    dfs_bins: int,
    n_live: int,
    pillar_ticks: Sequence[Dict[str, Any]],
) -> Dict[str, Any]:
    """Identify contiguous zero-named-match 'terra incognita' novel project bands along DFS order."""
    total_proj = sum(dfs_proj_256)
    min_proj_in_bin = max(1, total_proj // (dfs_bins * 8)) if total_proj >= dfs_bins else 1
    proj_eligible_bins = sum(1 for p in dfs_proj_256 if p >= min_proj_in_bin)
    zero_named_bins = sum(
        1 for b in range(dfs_bins) if dfs_proj_256[b] >= min_proj_in_bin and dfs_named_256[b] == 0
    )
    runs: List[Tuple[int, int, int]] = []
    start: Optional[int] = None
    for b in range(dfs_bins):
        is_novel_proj = (dfs_proj_256[b] >= min_proj_in_bin) and (dfs_named_256[b] == 0)
        if is_novel_proj:
            if start is None:
                start = b
        elif start is not None:
            runs.append((b - start, start, b))
            start = None
    if start is not None:
        runs.append((dfs_bins - start, start, dfs_bins))

    runs.sort(key=lambda x: (x[0], -x[1]), reverse=True)
    bands: List[Dict[str, Any]] = []
    for length, b0, b1 in runs[:12]:
        dfs_s = (b0 * n_live) // dfs_bins
        dfs_e = (b1 * n_live) // dfs_bins
        proj_span = sum(dfs_proj_256[b0:b1])
        aux_sum = sum(dfs_aux_256[b0:b1])
        bands.append({
            "bin256_start": int(b0),
            "bin256_end": int(b1),
            "width_bins": int(length),
            "dfs_start": int(dfs_s),
            "dfs_end": int(dfs_e),
            "decl_count": int(dfs_e - dfs_s),
            "project_decls": int(proj_span),
            "named_matches": 0,
            "aux_matches": int(aux_sum),
            "aux_per_1k_decls": round(1000.0 * aux_sum / max(1, proj_span), 2),
            "pillar": _pillar_for_dfs_range(dfs_s, dfs_e, pillar_ticks),
        })

    return {
        "eligible_project_bins_256": int(proj_eligible_bins),
        "zero_named_match_bins_256": int(zero_named_bins),
        "zero_named_share_pct": round(100.0 * zero_named_bins / max(1, proj_eligible_bins), 2),
        "bands": bands,
    }


# ---------------------------------------------------------------------------
# Pure-Python Zero-Dependency PNG Encoder (`zlib` + `struct`) & Renderers
# ---------------------------------------------------------------------------

def encode_png_rgb(width: int, height: int, rgb_rows: Sequence[bytes]) -> bytes:
    """Encode `height` rows of `width * 3` RGB bytes into a standard 8-bit RGB PNG."""
    if len(rgb_rows) != height:
        raise ValueError(f"Expected {height} RGB rows, got {len(rgb_rows)}")
    row_bytes = width * 3
    raw = bytearray()
    for row in rgb_rows:
        if len(row) != row_bytes:
            raise ValueError(f"Expected row byte length {row_bytes}, got {len(row)}")
        raw.append(0)  # PNG filter type 0 (None)
        raw.extend(row)

    def _chunk(tag: bytes, payload: bytes) -> bytes:
        crc = zlib.crc32(tag)
        crc = zlib.crc32(payload, crc) & 0xFFFFFFFF
        return struct.pack(">I", len(payload)) + tag + payload + struct.pack(">I", crc)

    ihdr = struct.pack(">IIBBBBB", width, height, 8, 2, 0, 0, 0)
    compressed = zlib.compress(bytes(raw), level=6)
    return b"\x89PNG\r\n\x1a\n" + _chunk(b"IHDR", ihdr) + _chunk(b"IDAT", compressed) + _chunk(b"IEND", b"")


def _draw_text_5x7(
    canvas: List[bytearray],
    width: int,
    height: int,
    x: int,
    y: int,
    text: str,
    color: Tuple[int, int, int],
) -> None:
    r_c, g_c, b_c = color
    cx = x
    for ch in text.upper():
        glyph = _FONT_5X7.get(ch)
        if glyph is not None:
            for gy in range(7):
                py = y + gy
                if 0 <= py < height:
                    bits = glyph[gy]
                    row = canvas[py]
                    for gx in range(5):
                        if (bits >> (4 - gx)) & 1:
                            px = cx + gx
                            if 0 <= px < width:
                                off = px * 3
                                row[off] = r_c
                                row[off + 1] = g_c
                                row[off + 2] = b_c
        cx += 6


def _blend_pixel(row: bytearray, px: int, width: int, rgb: Tuple[int, int, int], alpha: float) -> None:
    if 0 <= px < width:
        off = px * 3
        inv = 1.0 - alpha
        row[off] = int(row[off] * inv + rgb[0] * alpha)
        row[off + 1] = int(row[off + 1] * inv + rgb[1] * alpha)
        row[off + 2] = int(row[off + 2] * inv + rgb[2] * alpha)


def render_hic_png(
    edge_stream: Dict[str, Any],
    dom_info: Dict[str, Any],
    out_path: str,
    upscale: int = 2,
) -> Dict[str, Any]:
    """Render a crisp `512x512` (`256*upscale`) Hi-C contact matrix PNG."""
    g_t = edge_stream["grid_type_only"]
    g_v = edge_stream["grid_value_only"]
    g_b = edge_stream["grid_both"]
    n_bins = len(g_t)
    if n_bins == 0:
        n_bins = 256
        g_t = [[0] * n_bins for _ in range(n_bins)]
        g_v = [[0] * n_bins for _ in range(n_bins)]
        g_b = [[0] * n_bins for _ in range(n_bins)]

    width = n_bins * upscale
    height = n_bins * upscale

    # Collect non-zero log1p values and global E_T / E_V baseline for crisp diverging contrast
    logs_nz: List[float] = []
    tot_et_all = 0
    tot_ev_all = 0
    for r in range(n_bins):
        for c in range(n_bins):
            ct = g_t[r][c]
            cv = g_v[r][c]
            cb = g_b[r][c]
            tot = ct + cv + cb
            if tot > 0:
                logs_nz.append(math.log1p(tot))
                tot_et_all += ct + cb
                tot_ev_all += cv + cb
    if logs_nz:
        logs_nz.sort()
        p_idx = min(len(logs_nz) - 1, int(0.997 * len(logs_nz)))
        ceil_log = max(1.0, logs_nz[p_idx])
    else:
        ceil_log = 1.0
    baseline_lr = (
        0.58 * math.log((tot_et_all + 1.0) / (tot_ev_all + 1.0))
        if (tot_et_all + tot_ev_all) >= 1000
        else 0.0
    )

    bg = (10, 12, 18)
    canvas: List[bytearray] = [bytearray(width * 3) for _ in range(height)]

    for r in range(n_bins):
        row_buf = bytearray(width * 3)
        for c in range(n_bins):
            ct = g_t[r][c]
            cv = g_v[r][c]
            cb = g_b[r][c]
            tot = ct + cv + cb
            if tot <= 0:
                rc, gc, bc = bg
            else:
                inten = min(1.0, math.log1p(tot) / ceil_log) ** 0.72
                # Ensure even a 1-edge long-range coupling has crisp visibility
                inten = 0.16 + 0.84 * inten
                et = ct + cb
                ev = cv + cb
                s = math.tanh((math.log((et + 1.0) / (ev + 1.0)) - baseline_lr) / 0.85)
                if s >= 0.0:
                    # Balanced silver-white -> Electric Cyan conceptual type coupling
                    base_r = 215.0 * (1.0 - s) + 20.0 * s
                    base_g = 224.0 * (1.0 - s) + 228.0 * s
                    base_b = 248.0 * (1.0 - s) + 255.0 * s
                else:
                    # Balanced silver-white -> Amber computational proof-value factory
                    w = -s
                    base_r = 215.0 * (1.0 - w) + 255.0 * w
                    base_g = 224.0 * (1.0 - w) + 162.0 * w
                    base_b = 248.0 * (1.0 - w) + 28.0 * w
                # Hot-core highlight at peak intensity
                glow = max(0.0, (inten - 0.82) / 0.18) * 38.0
                rc = min(255, int(bg[0] * (1.0 - inten) + base_r * inten + glow))
                gc = min(255, int(bg[1] * (1.0 - inten) + base_g * inten + glow))
                bc = min(255, int(bg[2] * (1.0 - inten) + base_b * inten + glow))

            base_off = c * upscale * 3
            for u_x in range(upscale):
                off = base_off + u_x * 3
                row_buf[off] = rc
                row_buf[off + 1] = gc
                row_buf[off + 2] = bc

        for u_y in range(upscale):
            canvas[r * upscale + u_y][:] = row_buf

    # Overlay subtle pillar boundary hairlines and compact corner tags
    short_tag = {
        "pillar_a": "A",
        "pillar_d": "D",
        "pillar_c": "C",
        "pillar_b": "B",
        "shared_diamond": "DM",
        "bridge": "BR",
    }
    n_live = max(1, dom_info.get("n_live", 1))
    hairline_positions: Set[int] = set()
    for tick in dom_info.get("pillar_ticks", []):
        key = tick["key"]
        if key not in short_tag:
            continue
        p_start = min(width - 1, max(0, int(round((tick["dfs_start"] * width) / n_live))))
        p_end = min(width - 1, max(0, int(round((tick["dfs_end"] * width) / n_live))))
        if p_start > 2:
            hairline_positions.add(p_start)
        if key in ("pillar_d", "pillar_c") and 2 < p_end < width - 2:
            hairline_positions.add(p_end)
        if p_end - p_start >= 16:
            _draw_text_5x7(canvas, width, height, p_start + 3, 4, short_tag[key], (230, 238, 255))

    for hp in sorted(hairline_positions):
        for py in range(height):
            if (py % 4) < 2:
                _blend_pixel(canvas[py], hp, width, (120, 145, 185), 0.34)
        row_h = canvas[hp]
        for px in range(width):
            if (px % 4) < 2:
                _blend_pixel(row_h, px, width, (120, 145, 185), 0.34)

    png_bytes = encode_png_rgb(width, height, canvas)
    os.makedirs(os.path.dirname(os.path.abspath(out_path)), exist_ok=True)
    with open(out_path, "wb") as f:
        f.write(png_bytes)
    return {"width": width, "height": height, "bytes": len(png_bytes)}


def render_synteny_png(
    synteny_info: Dict[str, Any],
    dom_info: Dict[str, Any],
    out_path: str,
    upscale: int = 2,
) -> Dict[str, Any]:
    """Render a crisp `512x512` Cross-Library Structural Synteny Dot-Plot PNG."""
    png_256 = synteny_info.get("_png_256")
    if png_256 is not None:
        tot_256 = png_256["tot"]
        nam_256 = png_256["named"]
    else:
        tot_256 = [[0] * 256 for _ in range(256)]
        nam_256 = [[0] * 256 for _ in range(256)]
        for bx, by, th, nh, _rp in synteny_info.get("binned_points", []):
            x2 = min(255, bx * 2)
            y2 = min(255, by * 2)
            tot_256[y2][x2] += th
            nam_256[y2][x2] += nh

    width = 256 * upscale
    height = 256 * upscale
    bg = (10, 12, 18)
    terra_bg = (24, 14, 28)

    zero_x = [False] * 256
    for band in synteny_info.get("terra_incognita_bands", {}).get("bands", []):
        for b_i in range(max(0, band["bin256_start"]), min(256, band["bin256_end"])):
            zero_x[b_i] = True

    canvas: List[bytearray] = [bytearray(width * 3) for _ in range(height)]
    for py in range(height):
        row = canvas[py]
        for bx in range(256):
            c_rgb = terra_bg if zero_x[bx] else bg
            base = bx * upscale * 3
            for ux in range(upscale):
                off = base + ux * 3
                row[off] = c_rgb[0]
                row[off + 1] = c_rgb[1]
                row[off + 2] = c_rgb[2]

    # Subtle horizontal library strata gridlines (every 64px)
    for gy in range(64, height, 64):
        row = canvas[gy]
        for px in range(width):
            if (px % 6) < 3:
                _blend_pixel(row, px, width, (65, 76, 102), 0.35)

    # Vertical pillar hairlines + labels at top
    short_tag = {
        "pillar_a": "A",
        "pillar_d": "D",
        "pillar_c": "C",
        "pillar_b": "B",
        "shared_diamond": "DM",
        "bridge": "BR",
    }
    n_live = max(1, dom_info.get("n_live", 1))
    for tick in dom_info.get("pillar_ticks", []):
        key = tick["key"]
        if key not in short_tag:
            continue
        p_start = min(width - 1, max(0, int(round((tick["dfs_start"] * width) / n_live))))
        if p_start > 2:
            for py in range(height):
                if (py % 4) < 2:
                    _blend_pixel(canvas[py], p_start, width, (110, 130, 170), 0.35)

    # Max auxiliary density for contrast normalization
    max_log_tot = 1.0
    for by in range(256):
        for bx in range(256):
            if tot_256[by][bx] > 0:
                lv = math.log1p(tot_256[by][bx])
                if lv > max_log_tot:
                    max_log_tot = lv

    # Plot auxiliary k1a/k1n scaffold density in indigo/violet (Y=0 at bottom -> row 255 - by)
    for by in range(256):
        inv_y = 255 - by
        for bx in range(256):
            th = tot_256[by][bx]
            nh = nam_256[by][bx]
            if th <= 0:
                continue
            t_norm = (math.log1p(th) / max_log_tot) ** 0.75
            inten = 0.24 + 0.76 * t_norm
            rc = min(255, int(18 + 115 * inten))
            gc = min(255, int(22 + 92 * inten))
            bc = min(255, int(45 + 205 * inten))
            for uy in range(upscale):
                row = canvas[inv_y * upscale + uy]
                for ux in range(upscale):
                    off = (bx * upscale + ux) * 3
                    row[off] = rc
                    row[off + 1] = gc
                    row[off + 2] = bc

    # Highlight collinear diagonal streaks in warm gold
    g_sz = max(1, synteny_info.get("grid_meta", {}).get("grid_size", 128))
    for st in synteny_info.get("diagonal_streaks", [])[:8]:
        x0, x1 = st["proj_bin_range"]
        y0, y1 = st["lib_bin_range"]
        steps = max(1, abs(x1 - x0))
        dy_step = 1 if y1 >= y0 else -1
        for k in range(steps + 1):
            gx = x0 + k
            gy = y0 + k * dy_step
            px = min(width - 2, int((gx + 0.5) * width / g_sz))
            py = min(height - 2, height - 1 - int((gy + 0.5) * height / g_sz))
            for oy in (-1, 0, 1):
                if 0 <= py + oy < height:
                    for ox in (-1, 0, 1):
                        _blend_pixel(canvas[py + oy], px + ox, width, (255, 200, 60), 0.55)

    # Plot named (`is_aux=0`) exact/anon library twins as bright emerald-cyan 3x3 beacons
    for by in range(256):
        inv_y = 255 - by
        for bx in range(256):
            nh = nam_256[by][bx]
            if nh <= 0:
                continue
            cx = bx * upscale
            cy = inv_y * upscale
            core = (90, 255, 210) if nh == 1 else (210, 255, 245)
            halo = (20, 210, 175)
            for oy in range(-1, upscale + 1):
                py = cy + oy
                if 0 <= py < height:
                    row = canvas[py]
                    for ox in range(-1, upscale + 1):
                        px = cx + ox
                        if 0 <= ox < upscale and 0 <= oy < upscale:
                            _blend_pixel(row, px, width, core, 0.96)
                        else:
                            _blend_pixel(row, px, width, halo, 0.45)

    for tick in dom_info.get("pillar_ticks", []):
        key = tick["key"]
        if key in short_tag:
            p_start = min(width - 1, max(0, int(round((tick["dfs_start"] * width) / n_live))))
            p_end = min(width, int(round((tick["dfs_end"] * width) / n_live)))
            if p_end - p_start >= 16:
                _draw_text_5x7(canvas, width, height, p_start + 3, 4, short_tag[key], (230, 238, 255))

    png_bytes = encode_png_rgb(width, height, canvas)
    os.makedirs(os.path.dirname(os.path.abspath(out_path)), exist_ok=True)
    with open(out_path, "wb") as f:
        f.write(png_bytes)
    return {"width": width, "height": height, "bytes": len(png_bytes)}


# ---------------------------------------------------------------------------
# Unified Orchestrator & CLI
# ---------------------------------------------------------------------------

def run_atlas(
    kernel_db_path: str,
    tier2_db_path: Optional[str] = None,
    leanre_db_path: Optional[str] = None,
    out_json_path: Optional[str] = None,
    hic_png_path: Optional[str] = None,
    synteny_png_path: Optional[str] = None,
    min_type_nodes: int = 4,
    min_spot_value_nodes: int = 15,
    workers: int = 0,
) -> Dict[str, Any]:
    """Run all three Atlas analyses in a single fused pass over `kernel.db`."""
    t_start = time.perf_counter()
    has_t2 = bool(tier2_db_path and os.path.isfile(os.path.realpath(tier2_db_path)))
    t2_con = connect_ro(tier2_db_path) if (has_t2 and tier2_db_path) else None

    try:
        with contextlib.closing(connect_ro(kernel_db_path)) as con:
            t_dom0 = time.perf_counter()
            dom_info = compute_dom_dfs(con, tree_id=0, n_bins=256)
            dt_dom = time.perf_counter() - t_dom0

            t_prep0 = time.perf_counter()
            alien_prep = prepare_alien_candidates(
                con,
                tier2_con=t2_con,
                min_type_nodes=min_type_nodes,
            )
            dt_prep = time.perf_counter() - t_prep0

            t_stream0 = time.perf_counter()
            edge_stream = stream_edges_hic_and_ev(
                kernel_db_path,
                max_decl_id=dom_info["max_decl_id"],
                bin_by_id=dom_info["bin_by_id"],
                dfs_order=dom_info["dfs_order"],
                regions=dom_info["regions"],
                n_bins=256,
                candidate_ids=alien_prep["candidate_ids"],
                workers=workers,
            )
            dt_stream = time.perf_counter() - t_stream0

            t_hic0 = time.perf_counter()
            hic_summary = summarize_hic_matrix(dom_info, edge_stream, n_bins=256, tile_size=128)
            if hic_png_path:
                render_hic_png(edge_stream, dom_info, hic_png_path, upscale=2)
            hic_summary["runtime_sec"] = round(dt_dom + dt_stream + (time.perf_counter() - t_hic0), 3)

            t_twins0 = time.perf_counter()
            alien_summary = finalize_alien_twins(
                con,
                alien_prep,
                edge_stream["ev_sets"],
                min_spot_value_nodes=min_spot_value_nodes,
                leanre_db_path=leanre_db_path,
            )
            alien_summary["runtime_sec"] = round(dt_prep + (time.perf_counter() - t_twins0), 3)

            synteny_summary = compute_synteny(
                con,
                dom_info,
                tier2_con=t2_con,
                min_type_nodes=min_type_nodes,
                grid_size=128,
                dfs_bins=256,
            )
            if synteny_png_path:
                render_synteny_png(synteny_summary, dom_info, synteny_png_path, upscale=2)
            synteny_summary.pop("_png_256", None)

            summary: Dict[str, Any] = {
                "schema": SCHEMA_VERSION,
                "inputs": {
                    "kernel_db": safe_display_path(kernel_db_path),
                    "tier2_db": safe_display_path(tier2_db_path) if has_t2 else None,
                    "numpy_accelerated": bool(np is not None),
                },
                "runtime_sec": round(time.perf_counter() - t_start, 3),
                "alien_twins": alien_summary,
                "hic_matrix": hic_summary,
                "synteny": synteny_summary,
            }

            if out_json_path:
                os.makedirs(os.path.dirname(os.path.abspath(out_json_path)), exist_ok=True)
                payload = json.dumps(summary, separators=(",", ":"), ensure_ascii=False)
                with open(out_json_path, "w", encoding="utf-8") as f:
                    f.write(payload)
                    f.write("\n")

            return summary
    finally:
        if t2_con is not None:
            t2_con.close()


def build_arg_parser() -> argparse.ArgumentParser:
    ap = argparse.ArgumentParser(
        prog="python3 leanre/atlas.py",
        description="Compute Hi-C contact matrix, cross-library synteny dot-plot, and alien-proof twin splitter.",
    )
    ap.add_argument("--kernel-db", default=DEFAULT_KERNEL_DB, help="Path to read-only kernel.db")
    ap.add_argument("--tier2-db", default=DEFAULT_TIER2_DB, help="Optional path to read-only tier2.db")
    ap.add_argument("--leanre-db", default="outputs/leanre.db", help="Optional path to leanre.db for line anchors")
    ap.add_argument("--out", default=DEFAULT_OUT_JSON, help="Output JSON summary path (<= 400 KB)")
    ap.add_argument("--hic-png", default=None, help="Optional path to write 512x512 Hi-C preview PNG")
    ap.add_argument("--synteny-png", default=None, help="Optional path to write 512x512 Synteny preview PNG")
    ap.add_argument("--min-type-nodes", type=int, default=4, help="Minimum type_nodes to exclude trivial shells")
    ap.add_argument("--min-value-nodes", type=int, default=15, help="Minimum value_nodes for spot-checked alien twins")
    ap.add_argument("--workers", type=int, default=0, help="Worker processes for edge streaming (0 = auto)")
    return ap


def main(argv: Optional[Sequence[str]] = None) -> int:
    args = build_arg_parser().parse_args(argv)
    summary = run_atlas(
        kernel_db_path=args.kernel_db,
        tier2_db_path=args.tier2_db,
        leanre_db_path=args.leanre_db,
        out_json_path=args.out,
        hic_png_path=args.hic_png,
        synteny_png_path=args.synteny_png,
        min_type_nodes=args.min_type_nodes,
        min_spot_value_nodes=args.min_value_nodes,
        workers=args.workers,
    )
    tw = summary["alien_twins"]
    hc = summary["hic_matrix"]
    sy = summary["synteny"]
    out_bytes = os.path.getsize(args.out) if (args.out and os.path.isfile(args.out)) else 0
    print(
        f"[atlas] done in {summary['runtime_sec']:.2f}s | "
        f"Hi-C edges={hc['edge_totals']['total_streamed']:,} ({hc['n_live_decls']:,} live decls) | "
        f"alien_proof={tw['partitions']['all_sampled_pairs']['alien_proof']:,} "
        f"(named diff-scope={tw['partitions']['named_diff_scope_pairs']['alien_proof']:,}, "
        f"cross-repo={tw['partitions']['cross_repo_pairs']['alien_proof']:,}) | "
        f"synteny hits={sy['hit_totals']['total_matches']:,} (named={sy['hit_totals']['named_matches']:,}) | "
        f"json={out_bytes:,} B"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
