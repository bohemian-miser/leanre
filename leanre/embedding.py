#!/usr/bin/env python3
"""leanre.embedding -- 2D TF-IDF + Randomized SVD + k-NN UMAP-style Proof Map.

Builds an interactive two-granularity 2D embedding over read-only `kernel.db`
(and optional `leanre.db`, `cluster_labels_141.json`, `portability_gems.json`):

  1. `clusters_141`: Dominator-frontier blueprint clusters (`~141` on RH, or
     adaptive subtree/namespace clusters on smaller/synthetic corpora),
     represented by TF-IDF vectors of outgoing library/core constants.
  2. `landmarks`: Up to `~1,800` live named declarations (ALL `dom >= 1,000`
     hubs, cluster roots, portability targets, top `structure`/`class` hubs,
     and high-centrality project declarations), represented by bounded multi-hop
     TF-IDF bags of outgoing library/core dependencies plus structural type
     features (`kind`, `log1p(dom)`, `log1p(type_nodes)`, `log1p(value_nodes)`,
     `type_ratio = E_T / (E_T + E_V)`).

Both layers run:
  - Truncated randomized SVD (`k = 24`) on L2-normalized feature vectors.
  - `pca2`: Isotropic linear projection onto top-2 singular coordinates in `[-1, 1]`.
  - `knn2`: Deterministic (`seed = 42`) 180-step UMAP-style 2D attraction-repulsion
    graph embedding over `k = 15` cosine neighbors in the 24-dim SVD space.
  - Real `15`-NN preservation, trustworthiness `T(15)`, and `10`-NN namespace-drift
    metrics across source directories.

Guardrails:
  - Generic Python 3.11+ + `numpy` (no `scikit-learn` / `umap-learn` / `scipy`).
  - Strictly read-only SQLite access (`mode=ro` + `PRAGMA query_only=1`).
  - Zero `.lean` proof bodies and zero workstation absolute paths in outputs.
"""
from __future__ import annotations

import argparse
import array
import collections
import contextlib
import json
import math
import multiprocessing as mp
import os
import re
import sqlite3
import sys
import time
from typing import Any, Dict, Iterable, List, Optional, Sequence, Set, Tuple

import numpy as np  # type: ignore[import-not-found]

try:
    from leanre import atlas  # type: ignore[import-not-found]
except ImportError:  # pragma: no cover
    import atlas  # type: ignore[no-redef]

SCHEMA_VERSION = "leanre.embedding_2d/1"

_HERE = os.path.dirname(os.path.abspath(__file__))
_REPO_ROOT = os.path.abspath(os.path.join(_HERE, ".."))

DEFAULT_KERNEL_DB = "outputs/kernel/kernel.db"
DEFAULT_LEANRE_DB = "outputs/leanre.db"
DEFAULT_CLUSTER_LABELS = "outputs/flirt/cluster_labels_141.json"
DEFAULT_PORTABILITY = "outputs/portability_gems.json"
DEFAULT_OUT_JSON = "outputs/embedding_2d.json"

# Compiler-generated auxiliary declarations (keep `_private.` user decls!)
_COMPILER_AUX_RE = re.compile(
    r"(?:\._proof_|\._simp_|\._eq_|\._congr_|\._unfold|\._sunfold"
    r"|\._cstage|\._hyg|\.match_\d+|\._unary|\._mutual|\._lambda_"
    r"|\._abel_|\._ring_|\._omega_|\._linarith_|\._norm_num_|\._positivity_|\._gcongr_|\._decide_)"
)

# Ubiquitous Lean kernel / algebraic coercion primitives excluded from TF-IDF vocabulary
_STOP_EXACT = frozenset({
    "Eq", "Eq.refl", "Eq.ndrec", "Eq.mpr", "Eq.mp", "Eq.symm", "Eq.trans",
    "HEq", "HEq.refl", "HEq.symm", "HEq.trans",
    "True", "True.intro", "False", "False.elim", "absurd",
    "And", "And.intro", "And.left", "And.right",
    "Or", "Or.inl", "Or.inr", "Or.elim",
    "Not", "Iff", "Iff.intro", "Iff.mp", "Iff.mpr",
    "Exists", "Exists.intro", "Exists.elim",
    "Prop", "Sort", "Nat", "Nat.zero", "Nat.succ",
    "Bool", "Bool.true", "Bool.false",
    "PUnit", "PUnit.unit", "Unit", "Unit.unit",
    "OfNat.ofNat", "Zero.zero", "One.one",
    "id", "Function.comp", "congrArg", "congrFun", "funext", "propext",
    "Classical.choice", "Classical.propDecidable", "Classical.em", "Quot.sound",
    "Membership.mem", "DFunLike.coe", "AutoParam", "optParam", "outParam",
    "Subtype", "Subtype.mk", "Subtype.val", "Sigma", "Sigma.mk", "Prod", "Prod.mk",
    "decide", "of_decide_eq_true", "Lean.ofReduceBool",
    "CommSemiring.toSemiring", "Semiring.toNonAssocSemiring", "CommRing.toCommSemiring",
    "Ring.toSemiring", "AddCommMonoid.toAddMonoid", "AddCommGroup.toAddCommMonoid",
    "CommMonoid.toMonoid", "CommGroup.toGroup", "Field.toCommRing",
    "HMul.hMul", "HAdd.hAdd", "HSub.hSub", "HDiv.hDiv", "HPow.hPow",
    "Neg.neg", "Inv.inv", "LE.le", "LT.lt", "GE.ge", "GT.gt",
    "Coe.coe", "CoeTC.coe", "CoeT.coe", "CoeHTCT.coe",
})

# Pillar palette (distinct high-contrast dark-mode RGB colors)
_PILLAR_RGB: Dict[str, Tuple[int, int, int]] = {
    "A": (56, 189, 248),     # cyan-sky (Theta / Local Matching)
    "B": (251, 146, 60),     # orange (Galois Local-Global)
    "C": (192, 132, 252),    # violet (Automorphic Window)
    "D": (244, 63, 94),      # rose-crimson (Arakelov Covolume)
    "DM": (52, 211, 153),    # emerald (Shared Diamond)
    "LIT": (250, 204, 21),   # gold (Literature / Spine)
    "BR": (148, 163, 184),   # slate (Bridge & External Roots)
    "MAIN": (56, 189, 248),
    "LIB": (148, 163, 184),
}

_PILLAR_ROOT_NAMES: Dict[str, str] = {
    "UpperTheory.Lit.every_character_of_theta_integrals_local_matching": "pillar_theta",
    "UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter": "pillar_galois",
    "UpperTheory.One.vwin_of_row": "pillar_window",
    "UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin": "pillar_volume_lit",
    "allChi": "shared_diamond",
}


def is_compiler_aux(name: str) -> bool:
    """Return True for compiler/tactic auxiliary decls (keeps `_private.` user decls)."""
    return bool(_COMPILER_AUX_RE.search(name))


def short_decl_name(name: str) -> str:
    """Extract a readable short leaf name for UI labels."""
    clean = name[7:] if name.startswith("_root_.") else name
    if clean.startswith("_private.") and ".0." in clean:
        clean = clean.split(".0.", 1)[1]
    parts = clean.split(".")
    if len(parts) >= 2 and parts[-1] in ("mk", "rec", "recOn", "casesOn", "toFun", "inj", "ext", "0"):
        return ".".join(parts[-2:])
    return parts[-1]


def dir_top_from_module(name: str, module: Optional[str]) -> str:
    """Return normalized top-2 directory/module prefix (`dir_top`)."""
    if module:
        parts = module.split(".")
        return ".".join(parts[:2]) if len(parts) >= 2 else parts[0]
    clean = name[7:] if name.startswith("_root_.") else name
    if clean.startswith("_private."):
        rest = clean[len("_private.") :]
        if ".0." in rest:
            mod_part = rest.split(".0.", 1)[0]
            parts = mod_part.split(".")
            return ".".join(parts[:2]) if len(parts) >= 2 else parts[0]
    return atlas.top_namespace(clean, parts_keep=2)


def _pillar_code_for_region(region_key: str, decl_name: str = "") -> str:
    """Map an `atlas` DFS region key to a short pillar code (`A`/`B`/`C`/`D`/`DM`/`BR`/`LIT`)."""
    if region_key == "pillar_a":
        return "A"
    if region_key == "pillar_b":
        return "B"
    if region_key == "pillar_c":
        return "C"
    if region_key == "pillar_d":
        return "D"
    if region_key == "shared_diamond":
        return "DM"
    if region_key == "bridge":
        return "BR"
    if region_key == "spine_0":
        if decl_name in ("allChi", "UpperTheory.FinalTheorems.everyCharacter", "UpperTheory.FinalTheorems.everyCharacter_of_row"):
            return "DM"
        return "LIT"
    if region_key.startswith(("spine_", "tail_")):
        return "LIT"
    if region_key.startswith("q"):
        return region_key.upper()
    return "MAIN"


# ---------------------------------------------------------------------------
# Truncated Randomized SVD, k-NN UMAP-style Projection & Evaluation Metrics
# ---------------------------------------------------------------------------

def randomized_svd(
    X: np.ndarray,
    k: int = 24,
    seed: int = 42,
    n_iter: int = 5,
) -> Tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Compute deterministic truncated randomized SVD (`U, S, Vt`) using pure `numpy`."""
    n, d = X.shape
    k_eff = min(int(k), n, d)
    if k_eff <= 0 or n == 0 or d == 0:
        return (
            np.zeros((n, 0), dtype=np.float64),
            np.zeros((0,), dtype=np.float64),
            np.zeros((0, d), dtype=np.float64),
        )

    X64 = np.asarray(X, dtype=np.float64)
    # Use exact SVD directly when matrix is tiny (fast and zero stochastic error)
    if min(n, d) <= max(64, k_eff + 8):
        U, S, Vt = np.linalg.svd(X64, full_matrices=False)
        U = U[:, :k_eff].copy()
        S = S[:k_eff].copy()
        Vt = Vt[:k_eff, :].copy()
    else:
        rng = np.random.default_rng(seed)
        oversample = min(12, min(n, d) - k_eff)
        q_dim = k_eff + oversample
        omega = rng.standard_normal((d, q_dim))
        Y = X64 @ omega
        for _ in range(n_iter):
            Q, _ = np.linalg.qr(Y, mode="reduced")
            Z, _ = np.linalg.qr(X64.T @ Q, mode="reduced")
            Y = X64 @ Z
        Q, _ = np.linalg.qr(Y, mode="reduced")
        B = Q.T @ X64
        Ub, S_all, Vt_all = np.linalg.svd(B, full_matrices=False)
        U = (Q @ Ub)[:, :k_eff].copy()
        S = S_all[:k_eff].copy()
        Vt = Vt_all[:k_eff, :].copy()

    # Deterministic column sign convention
    for j in range(k_eff):
        col = U[:, j]
        idx = int(np.argmax(np.abs(col)))
        if col[idx] < 0.0:
            U[:, j] = -col
            Vt[j, :] = -Vt[j, :]
    return U, S, Vt


def normalize_2d_isotropic(coords: np.ndarray) -> np.ndarray:
    """Isotropically scale 2D coordinates into `[-1, 1]^2` preserving aspect & Euclidean metric."""
    n = coords.shape[0]
    if n == 0:
        return np.zeros((0, 2), dtype=np.float64)
    c = np.asarray(coords, dtype=np.float64)
    if c.shape[1] == 1:
        c = np.hstack([c, np.zeros((n, 1), dtype=np.float64)])
    elif c.shape[1] == 0:
        return np.zeros((n, 2), dtype=np.float64)
    mins = c.min(axis=0)
    maxs = c.max(axis=0)
    mid = 0.5 * (mins + maxs)
    half_span = float(max(1e-9, 0.5 * float(np.max(maxs - mins))))
    out = (c - mid[None, :]) / half_span
    return np.clip(out, -1.0, 1.0)


def compute_cosine_knn(Z: np.ndarray, k_nn: int = 15) -> Tuple[np.ndarray, np.ndarray]:
    """Compute exact top-`k_nn` cosine neighbors `(nn_idx, nn_sim)` in high-dim SVD space."""
    n = Z.shape[0]
    if n <= 1:
        return np.zeros((n, 0), dtype=np.int32), np.zeros((n, 0), dtype=np.float64)
    k_eff = min(int(k_nn), n - 1)
    Z64 = np.asarray(Z, dtype=np.float64)
    norms = np.linalg.norm(Z64, axis=1, keepdims=True)
    Zn = Z64 / np.maximum(norms, 1e-12)
    sim = np.clip(Zn @ Zn.T, -1.0, 1.0)
    np.fill_diagonal(sim, -2.0)

    if k_eff == n - 1:
        nn_idx = np.argsort(-sim, axis=1)[:, :k_eff]
        rows = np.arange(n)[:, None]
        nn_sim = sim[rows, nn_idx]
        return nn_idx.astype(np.int32), nn_sim

    nn_idx = np.argpartition(-sim, kth=k_eff - 1, axis=1)[:, :k_eff]
    rows = np.arange(n)[:, None]
    nn_sim = sim[rows, nn_idx]
    order = np.argsort(-nn_sim, axis=1)
    nn_idx = nn_idx[rows, order]
    nn_sim = nn_sim[rows, order]
    return nn_idx.astype(np.int32), nn_sim


def knn2_umap_embedding(
    Z_svd: np.ndarray,
    pca2: np.ndarray,
    k_nn: int = 15,
    n_steps: int = 180,
    seed: int = 42,
    a: float = 1.6,
    b: float = 0.9,
    n_neg: int = 16,
    rep_scale: float = 0.25,
    alpha0: float = 1.4,
) -> Tuple[np.ndarray, np.ndarray]:
    """Run deterministic vectorized UMAP-style 2D k-NN attraction-repulsion embedding."""
    n = Z_svd.shape[0]
    if n <= 2:
        nn_idx, _ = compute_cosine_knn(Z_svd, k_nn=k_nn)
        return normalize_2d_isotropic(pca2), nn_idx

    nn_idx, nn_sim = compute_cosine_knn(Z_svd, k_nn=k_nn)
    k_eff = nn_idx.shape[1]

    # Fuzzy simplicial directed probabilities -> symmetric edge weights
    dists = np.sqrt(np.maximum(0.0, 2.0 * (1.0 - nn_sim)))
    rho = dists[:, 0:1]
    sigma = np.maximum(1e-3, np.mean(dists - rho, axis=1, keepdims=True))
    p_cond = np.exp(-np.maximum(0.0, dists - rho) / sigma)

    edge_w: Dict[Tuple[int, int], float] = {}
    for i in range(n):
        for pos in range(k_eff):
            j = int(nn_idx[i, pos])
            w_ij = float(p_cond[i, pos])
            key = (i, j) if i < j else (j, i)
            prev = edge_w.get(key)
            if prev is None:
                edge_w[key] = w_ij
            else:
                edge_w[key] = prev + w_ij - prev * w_ij

    u_arr = np.fromiter((k[0] for k in edge_w), dtype=np.int32, count=len(edge_w))
    v_arr = np.fromiter((k[1] for k in edge_w), dtype=np.int32, count=len(edge_w))
    w_arr = np.fromiter(edge_w.values(), dtype=np.float64, count=len(edge_w))

    # Initialize from spectral pca2 coordinates
    Y = np.asarray(pca2, dtype=np.float64).copy()
    if Y.shape[1] < 2:
        Y = np.hstack([Y, np.zeros((n, 2 - Y.shape[1]), dtype=np.float64)])
    Y -= Y.mean(axis=0, keepdims=True)
    sd = float(np.std(Y))
    if sd > 1e-12:
        Y /= sd
    else:
        rng_init = np.random.default_rng(seed)
        Y = rng_init.normal(0.0, 0.5, size=(n, 2))

    rng = np.random.default_rng(seed)
    n_neg_eff = min(int(n_neg), max(1, n - 1))

    for step in range(n_steps):
        lr = alpha0 * (1.0 - step / float(max(1, n_steps)))
        grad = np.zeros_like(Y)

        # Attractive force along k-NN edges
        diff = Y[u_arr] - Y[v_arr]
        d2 = np.sum(diff * diff, axis=1) + 1e-6
        db = d2 ** b
        coeff_a = (-2.0 * a * b * (d2 ** (b - 1.0)) / (1.0 + a * db)) * w_arr
        f_a = coeff_a[:, None] * diff
        np.add.at(grad, u_arr, f_a)
        np.add.at(grad, v_arr, -f_a)

        # Repulsive force on deterministically sampled negative pairs
        neg_u = np.repeat(np.arange(n, dtype=np.int32), n_neg_eff)
        neg_v = rng.integers(0, n, size=n * n_neg_eff, dtype=np.int32)
        same = neg_v == neg_u
        if np.any(same):
            neg_v[same] = (neg_v[same] + 1) % n
        diff_n = Y[neg_u] - Y[neg_v]
        d2_n = np.sum(diff_n * diff_n, axis=1) + 1e-4
        db_n = d2_n ** b
        coeff_r = (2.0 * b / ((0.03 + d2_n) * (1.0 + a * db_n))) * rep_scale
        f_r = coeff_r[:, None] * diff_n
        np.add.at(grad, neg_u, f_r)

        gnorm = np.linalg.norm(grad, axis=1, keepdims=True)
        clip = np.minimum(1.0, 4.0 / np.maximum(gnorm, 1e-12))
        Y += lr * grad * clip
        Y -= Y.mean(axis=0, keepdims=True)

    return normalize_2d_isotropic(Y), nn_idx


def evaluate_embedding_quality(
    Z_svd: np.ndarray,
    Y2: np.ndarray,
    nn_hi: np.ndarray,
) -> Dict[str, float]:
    """Measure exact `k`-NN neighborhood preservation and trustworthiness `T(k)`."""
    n = Z_svd.shape[0]
    k = nn_hi.shape[1]
    if n <= 2 or k <= 0:
        return {"knn_preservation": 1.0, "trustworthiness": 1.0}

    sq = np.sum(Y2 * Y2, axis=1, keepdims=True)
    d2 = np.maximum(0.0, sq + sq.T - 2.0 * (Y2 @ Y2.T))
    np.fill_diagonal(d2, np.inf)
    if k == n - 1:
        nn_lo = np.argsort(d2, axis=1)[:, :k]
    else:
        nn_lo = np.argpartition(d2, kth=k - 1, axis=1)[:, :k]

    overlap_sum = 0.0
    for i in range(n):
        s_hi = set(nn_hi[i].tolist())
        s_lo = set(nn_lo[i].tolist())
        overlap_sum += len(s_hi & s_lo) / float(k)
    knn_pres = overlap_sum / float(n)

    # Trustworthiness T(k): penalize false 2D neighbors by excess high-dim rank
    denom = n * k * (2 * n - 3 * k - 1)
    if denom <= 0:
        trust = 1.0
    else:
        Zn = Z_svd / np.maximum(np.linalg.norm(Z_svd, axis=1, keepdims=True), 1e-12)
        sim = Zn @ Zn.T
        np.fill_diagonal(sim, 2.0)
        ranks = np.argsort(np.argsort(-sim, axis=1), axis=1)
        t_sum = 0.0
        for i in range(n):
            s_hi = set(nn_hi[i].tolist())
            for j in nn_lo[i]:
                j_i = int(j)
                if j_i not in s_hi:
                    t_sum += max(0, int(ranks[i, j_i]) - k)
        trust = max(0.0, min(1.0, 1.0 - (2.0 * t_sum / float(denom))))

    return {
        "knn_preservation": round(float(knn_pres), 4),
        "trustworthiness": round(float(trust), 4),
    }


def compute_namespace_drift(
    nn_hi: np.ndarray,
    dir_tops: Sequence[str],
    is_dom1k: Sequence[bool],
    k_drift: int = 10,
) -> Tuple[List[float], Dict[str, Any]]:
    """Compute per-point fraction of `k_drift` nearest math neighbors from a different directory."""
    n = len(dir_tops)
    if n <= 1 or nn_hi.shape[1] == 0:
        return [0.0] * n, {
            "k_neighbors": 0,
            "mean_drift_all": 0.0,
            "mean_drift_dom1k": 0.0,
            "dom1k_count": int(sum(1 for x in is_dom1k if x)),
            "dom1k_nn1_diff_folder_pct": 0.0,
        }

    k_eff = min(int(k_drift), nn_hi.shape[1])
    drifts: List[float] = []
    dom1k_drifts: List[float] = []
    dom1k_nn1_diff = 0
    dom1k_cnt = 0

    for i in range(n):
        d_i = dir_tops[i]
        nbrs = nn_hi[i, :k_eff]
        diff_cnt = sum(1 for j in nbrs if dir_tops[int(j)] != d_i)
        frac = round(diff_cnt / float(k_eff), 4)
        drifts.append(frac)
        if is_dom1k[i]:
            dom1k_cnt += 1
            dom1k_drifts.append(frac)
            if dir_tops[int(nn_hi[i, 0])] != d_i:
                dom1k_nn1_diff += 1

    return drifts, {
        "k_neighbors": k_eff,
        "mean_drift_all": round(sum(drifts) / float(n), 4),
        "mean_drift_dom1k": round(sum(dom1k_drifts) / float(max(1, dom1k_cnt)), 4),
        "dom1k_count": int(dom1k_cnt),
        "dom1k_nn1_diff_folder_pct": round(100.0 * dom1k_nn1_diff / float(max(1, dom1k_cnt)), 2),
    }


# ---------------------------------------------------------------------------
# Cluster Partition Reconstruction & Parallel Outgoing-Dependency Aggregation
# ---------------------------------------------------------------------------

_SH_EMB_DB: str = ""
_SH_EMB_CL: Any = None
_SH_EMB_EXT: Any = None
_SH_EMB_NCL: int = 0
_SH_EMB_NEXT: int = 0


def _cluster_edge_worker(bounds: Tuple[int, int]) -> np.ndarray:
    """Count `(cluster_idx, ext_vocab_idx)` outgoing edges for `src in [lo, hi)`."""
    lo, hi = bounds
    ncl = _SH_EMB_NCL
    next_v = _SH_EMB_NEXT
    cl_arr = _SH_EMB_CL
    ex_arr = _SH_EMB_EXT
    counts = np.zeros(ncl * next_v, dtype=np.int64)
    can_pack = int(cl_arr.shape[0]) < (1 << 30)

    with contextlib.closing(atlas.connect_ro(_SH_EMB_DB, mmap_bytes=8_589_934_592)) as con:
        if can_pack:
            cur = con.execute(
                "SELECT ((src << 32) | dst) FROM edges WHERE src >= ? AND src < ?",
                (lo, hi),
            )
            while True:
                rows = cur.fetchmany(250_000)
                if not rows:
                    break
                packed = np.fromiter((r[0] for r in rows), dtype=np.int64, count=len(rows))
                src = packed >> 32
                dst = packed & 0xFFFFFFFF
                c = cl_arr[src]
                v = ex_arr[dst]
                mask = (c >= 0) & (v >= 0)
                if np.any(mask):
                    idx = c[mask].astype(np.int64) * next_v + v[mask].astype(np.int64)
                    counts += np.bincount(idx, minlength=ncl * next_v)
        else:
            max_id = int(cl_arr.shape[0])
            cur = con.execute(
                "SELECT src, dst FROM edges WHERE src >= ? AND src < ?",
                (lo, hi),
            )
            while True:
                rows = cur.fetchmany(100_000)
                if not rows:
                    break
                for s_i, d_i in rows:
                    if 0 <= s_i < max_id and 0 <= d_i < max_id:
                        c_i = int(cl_arr[s_i])
                        v_i = int(ex_arr[d_i])
                        if c_i >= 0 and v_i >= 0:
                            counts[c_i * next_v + v_i] += 1
    return counts


def _build_cluster_partition(
    con: sqlite3.Connection,
    n_total: int,
    name_of: Sequence[str],
    kind_of: Sequence[str],
    live_of: Sequence[int],
    fan_in_of: Sequence[int],
    mod_of: Sequence[Optional[str]],
    sub_sz: Sequence[int],
    children: Dict[int, List[int]],
    dom_roots_top: Sequence[int],
    tin_by_id: Sequence[int],
    reg_by_dfs: Sequence[str],
    cluster_labels_map: Dict[str, Dict[str, Any]],
) -> Tuple[List[Dict[str, Any]], np.ndarray]:
    """Deterministically partition live declarations into coarse blueprint clusters."""
    n_live = int(sum(live_of))
    name_to_id = {name_of[i]: i for i in range(n_total) if name_of[i]}

    if n_live >= 5000:
        split_threshold = 25000
        min_dom_cluster = 1500
        min_residual_cluster = 1500
    else:
        split_threshold = max(4, n_live // 6)
        min_dom_cluster = max(2, n_live // 12)
        min_residual_cluster = 1

    pillar_id_map = {name_to_id[nm]: pil for nm, pil in _PILLAR_ROOT_NAMES.items() if nm in name_to_id}
    roots_sorted = sorted(dom_roots_top, key=lambda r: (-sub_sz[r], r))
    primary_root = roots_sorted[0] if roots_sorted else -1

    pillar_of: Dict[int, str] = {}
    for r in roots_sorted:
        start_pil = pillar_id_map.get(r, "tcb_mathlib_core" if r != primary_root else "shared_diamond")
        st = [(r, start_pil)]
        while st:
            u, pil = st.pop()
            cp = pillar_id_map.get(u, pil)
            pillar_of[u] = cp
            for ch in children.get(u, ()):
                st.append((ch, cp))

    def _collect_subtree(root_u: int) -> List[int]:
        out: List[int] = []
        st = [root_u]
        while st:
            x = st.pop()
            out.append(x)
            st.extend(children.get(x, ()))
        return out

    dom_cluster_roots: List[int] = []
    residual_nodes: List[int] = []
    tcb_nodes: List[int] = []

    def _walk(u: int) -> None:
        ch = sorted(children.get(u, ()), key=lambda c: (-sub_sz[c], c))
        big = [c for c in ch if sub_sz[c] >= min_dom_cluster]
        if sub_sz[u] >= split_threshold and big:
            residual_nodes.append(u)
            for c in ch:
                if sub_sz[c] < min_dom_cluster:
                    residual_nodes.extend(_collect_subtree(c))
            for c in big:
                _walk(c)
        else:
            dom_cluster_roots.append(u)

    for r in roots_sorted:
        if sub_sz[r] >= min_dom_cluster:
            _walk(r)
        else:
            tcb_nodes.extend(_collect_subtree(r))

    raw_clusters: List[Dict[str, Any]] = []
    for u in dom_cluster_roots:
        mems = _collect_subtree(u)
        raw_clusters.append({
            "kind": "dom_subtree",
            "flirt_pillar": pillar_of.get(u, "shared_diamond"),
            "root_decl_id": u,
            "root_decl": name_of[u],
            "members": mems,
            "title_hint": name_of[u],
        })

    res_groups: Dict[Tuple[str, str], List[int]] = collections.defaultdict(list)
    for did in residual_nodes:
        pil = pillar_of.get(did, "shared_diamond")
        dt = dir_top_from_module(name_of[did], mod_of[did]) if mod_of[did] else "<library_or_unmatched>"
        res_groups[(pil, dt)].append(did)

    small_tails: Dict[str, List[int]] = collections.defaultdict(list)
    for (pil, fl2), mems in sorted(res_groups.items(), key=lambda kv: (-len(kv[1]), kv[0])):
        if len(mems) >= min_residual_cluster:
            rep = max(mems, key=lambda x: (sub_sz[x], fan_in_of[x], -x))
            raw_clusters.append({
                "kind": "residual_neighborhood",
                "flirt_pillar": pil,
                "root_decl_id": rep,
                "root_decl": name_of[rep],
                "members": mems,
                "title_hint": f"{pil}::{fl2}",
            })
        else:
            small_tails[pil].extend(mems)

    for pil, mems in sorted(small_tails.items()):
        if not mems:
            continue
        rep = max(mems, key=lambda x: (sub_sz[x], fan_in_of[x], -x))
        raw_clusters.append({
            "kind": "residual_tail",
            "flirt_pillar": pil,
            "root_decl_id": rep,
            "root_decl": name_of[rep],
            "members": mems,
            "title_hint": f"{pil}::<residual_tail>",
        })

    if tcb_nodes:
        rep = max(tcb_nodes, key=lambda x: (fan_in_of[x], sub_sz[x], -x))
        raw_clusters.append({
            "kind": "tcb_library_root",
            "flirt_pillar": "tcb_mathlib_core",
            "root_decl_id": rep,
            "root_decl": name_of[rep],
            "members": tcb_nodes,
            "title_hint": "TCB & Shared Mathlib/Core Library",
        })

    raw_clusters.sort(key=lambda c: (-len(c["members"]), c["flirt_pillar"], c["title_hint"]))

    cluster_idx_of = np.full(n_total, -1, dtype=np.int32)
    for idx, cl in enumerate(raw_clusters):
        cid = f"BP{idx + 1:03d}"
        cl["cluster_id"] = cid
        for did in cl["members"]:
            cluster_idx_of[did] = idx

        # Dominant folder, pillar, and label
        rep_id = int(cl["root_decl_id"])
        tin = tin_by_id[rep_id] if 0 <= rep_id < len(tin_by_id) else -1
        reg_key = reg_by_dfs[tin] if (0 <= tin < len(reg_by_dfs)) else ""
        if cl["flirt_pillar"] == "tcb_mathlib_core":
            pil_code = "BR"
        elif reg_key:
            pil_code = _pillar_code_for_region(reg_key, cl["root_decl"])
        else:
            pil_code = "MAIN"
        cl["pillar"] = pil_code

        dir_ctr: collections.Counter[str] = collections.Counter()
        for did in cl["members"]:
            if mod_of[did]:
                dir_ctr[dir_top_from_module(name_of[did], mod_of[did])] += 1
        cl["dir_top"] = (
            dir_ctr.most_common(1)[0][0]
            if dir_ctr
            else dir_top_from_module(cl["root_decl"], mod_of[rep_id])
        )
        lbl_meta = cluster_labels_map.get(cid, {})
        blind = lbl_meta.get("blinded_label") if isinstance(lbl_meta.get("blinded_label"), dict) else {}
        cl["label"] = str(blind.get("label") or cl["title_hint"])
        cl["root_kind"] = kind_of[rep_id]
        cl["root_mod"] = mod_of[rep_id]

    return raw_clusters, cluster_idx_of


def _build_clusters_layer(
    kernel_db_path: str,
    raw_clusters: Sequence[Dict[str, Any]],
    cluster_idx_of: np.ndarray,
    cand_ext_ids: Sequence[int],
    n_total: int,
    name_of: Sequence[str],
    type_ratio_of: Sequence[float],
    line_of_id: Dict[int, int],
    max_vocab: int = 768,
    k_svd: int = 24,
    k_nn: int = 15,
    n_steps: int = 180,
    seed: int = 42,
    workers: int = 0,
) -> Dict[str, Any]:
    """Compute TF-IDF + SVD(k=24) + `pca2` + `knn2` over the blueprint clusters."""
    global _SH_EMB_DB, _SH_EMB_CL, _SH_EMB_EXT, _SH_EMB_NCL, _SH_EMB_NEXT
    m_cl = len(raw_clusters)
    n_cand = len(cand_ext_ids)

    if m_cl == 0:
        return {
            "count": 0,
            "svd_explained_variance_ratios": [],
            "svd_explained_variance_sum": 0.0,
            "metrics": {
                "pca2": {"knn_preservation": 1.0, "trustworthiness": 1.0},
                "knn2": {"knn_preservation": 1.0, "trustworthiness": 1.0},
                "drift": {"k_neighbors": 0, "mean_drift_all": 0.0, "mean_drift_dom1k": 0.0, "dom1k_count": 0, "dom1k_nn1_diff_folder_pct": 0.0},
            },
            "tables": {"pillars": [], "dirs": [], "kinds": [], "vocab_terms": []},
            "fields": ["id", "name", "short", "label", "kind_idx", "dom", "pillar_idx", "dir_idx", "mod", "line", "px", "py", "ux", "uy", "top_term_idxs", "nn_idx", "drift", "type_ratio"],
            "points": [],
            "_decoded": [],
        }

    ext_arr = np.full(n_total, -1, dtype=np.int32)
    for j, did in enumerate(cand_ext_ids):
        ext_arr[did] = j

    _SH_EMB_DB = kernel_db_path
    _SH_EMB_CL = cluster_idx_of
    _SH_EMB_EXT = ext_arr
    _SH_EMB_NCL = m_cl
    _SH_EMB_NEXT = n_cand

    if workers <= 0:
        workers = min(16, os.cpu_count() or 4)
    use_mp = (
        workers > 1
        and n_total >= 50_000
        and n_cand > 0
        and "fork" in mp.get_all_start_methods()
    )
    if n_cand == 0:
        mat = np.zeros((m_cl, 0), dtype=np.int64)
    elif use_mp:
        step = (n_total + workers - 1) // workers
        shards = [(i * step, min(n_total, (i + 1) * step)) for i in range(workers)]
        shards = [s for s in shards if s[0] < s[1]]
        with mp.get_context("fork").Pool(len(shards)) as pool:
            parts = pool.map(_cluster_edge_worker, shards)
        mat = sum(parts).reshape((m_cl, n_cand))
    else:
        mat = _cluster_edge_worker((0, n_total)).reshape((m_cl, n_cand))

    _SH_EMB_CL = None
    _SH_EMB_EXT = None

    if n_cand > 0:
        df = np.sum(mat > 0, axis=0)
        min_df = 2 if m_cl >= 10 else 1
        max_df = int(0.85 * m_cl) if m_cl >= 6 else m_cl
        keep = (df >= min_df) & (df <= max_df)
        if not np.any(keep):
            keep = df >= 1
        idf = np.log((1.0 + m_cl) / (1.0 + df))
        tf_log = np.log1p(mat.astype(np.float64))
        energy = np.sum((tf_log * idf[None, :]) ** 2, axis=0) * keep
        v_take = min(int(max_vocab), int(np.count_nonzero(keep)))
        if v_take > 0:
            top_cols = np.argsort(-energy)[:v_take]
            vocab_ids = [int(cand_ext_ids[int(j)]) for j in top_cols]
            X_tf = tf_log[:, top_cols] * idf[None, top_cols]
        else:
            vocab_ids = []
            X_tf = np.zeros((m_cl, 0), dtype=np.float64)
    else:
        vocab_ids = []
        X_tf = np.zeros((m_cl, 0), dtype=np.float64)

    # Smooth fallback features if a cluster has zero TF-IDF terms
    row_norms = np.linalg.norm(X_tf, axis=1, keepdims=True)
    if X_tf.shape[1] == 0:
        X = np.ones((m_cl, 2), dtype=np.float64) / math.sqrt(2.0)
    else:
        X = X_tf / np.maximum(row_norms, 1e-12)

    U, S, _Vt = randomized_svd(X, k=k_svd, seed=seed)
    Z_svd = U * S[None, :] if S.size > 0 else np.zeros((m_cl, 2), dtype=np.float64)
    tot_ss = float(np.sum(X * X))
    exp_ratios = [round(float(sv * sv / tot_ss), 5) for sv in S] if tot_ss > 0 else []
    exp_sum = round(float(sum(exp_ratios)), 4)

    pca2 = normalize_2d_isotropic(Z_svd[:, :2] if Z_svd.shape[1] >= 2 else Z_svd)
    knn2, nn_hi = knn2_umap_embedding(Z_svd, pca2, k_nn=k_nn, n_steps=n_steps, seed=seed)

    m_pca = evaluate_embedding_quality(Z_svd, pca2, nn_hi)
    m_knn = evaluate_embedding_quality(Z_svd, knn2, nn_hi)

    dir_tops = [str(c["dir_top"]) for c in raw_clusters]
    is_dom1k = [True] * m_cl
    drifts, drift_stats = compute_namespace_drift(nn_hi, dir_tops, is_dom1k, k_drift=10)

    # Intern compact lookup tables
    pillars_tbl = sorted({str(c["pillar"]) for c in raw_clusters})
    dirs_tbl = sorted(set(dir_tops))
    kinds_tbl = sorted({str(c["root_kind"]) for c in raw_clusters})
    pil_map = {v: i for i, v in enumerate(pillars_tbl)}
    dir_map = {v: i for i, v in enumerate(dirs_tbl)}
    knd_map = {v: i for i, v in enumerate(kinds_tbl)}
    vocab_terms = [name_of[did] for did in vocab_ids]

    points_compact: List[List[Any]] = []
    decoded: List[Dict[str, Any]] = []
    for i, cl in enumerate(raw_clusters):
        if X_tf.shape[1] > 0 and float(row_norms[i, 0]) > 1e-12:
            top_j = [int(j) for j in np.argsort(-X_tf[i])[:4] if X_tf[i, j] > 0.0]
        else:
            top_j = []
        nbr5 = [int(j) for j in nn_hi[i, :5]]
        rep_id = int(cl["root_decl_id"])
        line_no = line_of_id.get(rep_id)
        # Compute mean cluster type_ratio
        et_s, ev_s = 0, 0
        # Use root/cluster ratio stored on cl if set
        tr_val = round(float(cl.get("type_ratio", 0.5)), 4)
        px, py = round(float(pca2[i, 0]), 4), round(float(pca2[i, 1]), 4)
        ux, uy = round(float(knn2[i, 0]), 4), round(float(knn2[i, 1]), 4)
        short = short_decl_name(cl["root_decl"])

        points_compact.append([
            cl["cluster_id"],
            cl["root_decl"],
            short,
            cl["label"],
            knd_map[str(cl["root_kind"])],
            len(cl["members"]),
            pil_map[str(cl["pillar"])],
            dir_map[dir_tops[i]],
            cl["root_mod"],
            line_no,
            px, py,
            ux, uy,
            top_j,
            nbr5,
            drifts[i],
            tr_val,
        ])
        decoded.append({
            "id": cl["cluster_id"],
            "name": cl["root_decl"],
            "short": short,
            "label": cl["label"],
            "kind": str(cl["root_kind"]),
            "dom": len(cl["members"]),
            "pillar": str(cl["pillar"]),
            "dir_top": dir_tops[i],
            "mod": cl["root_mod"],
            "line": line_no,
            "px": px,
            "py": py,
            "ux": ux,
            "uy": uy,
            "top_terms": [vocab_terms[j] for j in top_j],
            "nn_idx": nbr5,
            "drift": drifts[i],
            "type_ratio": tr_val,
        })

    return {
        "count": m_cl,
        "svd_explained_variance_ratios": exp_ratios,
        "svd_explained_variance_sum": exp_sum,
        "metrics": {
            "pca2": m_pca,
            "knn2": m_knn,
            "drift": drift_stats,
        },
        "tables": {
            "pillars": pillars_tbl,
            "dirs": dirs_tbl,
            "kinds": kinds_tbl,
            "vocab_terms": vocab_terms,
        },
        "fields": [
            "id", "name", "short", "label", "kind_idx", "dom",
            "pillar_idx", "dir_idx", "mod", "line",
            "px", "py", "ux", "uy",
            "top_term_idxs", "nn_idx", "drift", "type_ratio",
        ],
        "points": points_compact,
        "_decoded": decoded,
    }


# ---------------------------------------------------------------------------
# Landmarks Selection & Bounded Multi-Hop TF-IDF Embedding
# ---------------------------------------------------------------------------

def _select_landmarks(
    n_total: int,
    name_of: Sequence[str],
    kind_of: Sequence[str],
    live_of: Sequence[int],
    fan_in_of: Sequence[int],
    tn_of: Sequence[int],
    sub_sz: Sequence[int],
    mod_of: Sequence[Optional[str]],
    origin_of: Sequence[str],
    raw_clusters: Sequence[Dict[str, Any]],
    lean_kind_by_id: Dict[int, str],
    portability_ids: Sequence[int],
    max_landmarks: int = 1800,
) -> Tuple[List[int], Set[int]]:
    """Select `~1,500–2,000` live named declarations covering hubs, structures & islands."""
    selected: List[int] = []
    seen: Set[int] = set()
    dom1k_set: Set[int] = set()
    name_to_id = {name_of[i]: i for i in range(n_total) if name_of[i]}

    def _add(did: int) -> None:
        if 0 <= did < n_total and did not in seen and live_of[did] and not is_compiler_aux(name_of[did]):
            seen.add(did)
            selected.append(did)

    # 1. ALL live non-compiler-aux `dom >= 1,000` declarations
    dom1k_cands = [
        (-sub_sz[did], did)
        for did in range(n_total)
        if live_of[did] and sub_sz[did] >= 1000 and not is_compiler_aux(name_of[did])
    ]
    dom1k_cands.sort()
    for _, did in dom1k_cands:
        _add(did)
        dom1k_set.add(did)

    # 2. Curated showcase landmarks, cluster roots, and standalone portability gems
    for _, _, dname in atlas.DEFAULT_LANDMARKS:
        did = name_to_id.get(dname)
        if did is not None:
            _add(did)
    for cl in raw_clusters:
        _add(int(cl["root_decl_id"]))
    for pid in portability_ids:
        _add(int(pid))

    # 3. Top `structure` / `class` (or `inductive`) hubs by fan_in
    struct_cands = [
        (-fan_in_of[did], -sub_sz[did], did)
        for did in range(n_total)
        if live_of[did]
        and did not in seen
        and origin_of[did] == "project"
        and not is_compiler_aux(name_of[did])
        and (lean_kind_by_id.get(did) in ("structure", "class") or kind_of[did] == "inductive")
    ]
    struct_cands.sort()
    struct_cap = max(20, min(350, max_landmarks // 5))
    for _, _, did in struct_cands[:struct_cap]:
        if len(selected) >= max_landmarks:
            break
        _add(did)

    # 4. Fill remaining slots with top live named project decls (subtree + fan_in + type_nodes)
    proj_cands = [
        (-(sub_sz[did] * 2 + fan_in_of[did] + tn_of[did]), did)
        for did in range(n_total)
        if live_of[did]
        and did not in seen
        and origin_of[did] == "project"
        and mod_of[did] is not None
        and not is_compiler_aux(name_of[did])
    ]
    proj_cands.sort()
    for _, did in proj_cands:
        if len(selected) >= max_landmarks:
            break
        _add(did)

    # Fallback on tiny DBs where `mod_of` may be sparse: allow remaining live named decls
    if len(selected) < min(max_landmarks, 32):
        any_cands = [
            (-(sub_sz[did] * 2 + fan_in_of[did] + tn_of[did]), did)
            for did in range(n_total)
            if live_of[did] and did not in seen and not is_compiler_aux(name_of[did])
        ]
        any_cands.sort()
        for _, did in any_cands:
            if len(selected) >= max_landmarks:
                break
            _add(did)

    return selected, dom1k_set


def _build_landmarks_layer(
    con: sqlite3.Connection,
    selected: Sequence[int],
    dom1k_set: Set[int],
    ext_vocab_set: Set[int],
    n_total: int,
    name_of: Sequence[str],
    kind_of: Sequence[str],
    tn_of: Sequence[int],
    vn_of: Sequence[int],
    et_of: Sequence[int],
    ev_of: Sequence[int],
    sub_sz: Sequence[int],
    mod_of: Sequence[Optional[str]],
    origin_of: Sequence[str],
    tin_by_id: Sequence[int],
    reg_by_dfs: Sequence[str],
    cluster_idx_of: np.ndarray,
    raw_clusters: Sequence[Dict[str, Any]],
    lean_kind_by_id: Dict[int, str],
    line_of_id: Dict[int, int],
    max_vocab: int = 1024,
    k_svd: int = 24,
    k_nn: int = 15,
    n_steps: int = 180,
    seed: int = 42,
) -> Dict[str, Any]:
    """Build TF-IDF + structural type embedding over landmark declarations."""
    n = len(selected)
    if n == 0:
        return {
            "count": 0,
            "svd_explained_variance_ratios": [],
            "svd_explained_variance_sum": 0.0,
            "metrics": {
                "pca2": {"knn_preservation": 1.0, "trustworthiness": 1.0},
                "knn2": {"knn_preservation": 1.0, "trustworthiness": 1.0},
                "drift": {"k_neighbors": 0, "mean_drift_all": 0.0, "mean_drift_dom1k": 0.0, "dom1k_count": 0, "dom1k_nn1_diff_folder_pct": 0.0},
            },
            "tables": {"pillars": [], "dirs": [], "kinds": [], "clusters": [], "mods": [], "vocab_terms": []},
            "fields": ["name", "short", "kind_idx", "dom", "pillar_idx", "dir_idx", "cluster_idx", "mod_idx", "line", "px", "py", "ux", "uy", "top_term_idxs", "nn_idx", "drift", "type_ratio"],
            "points": [],
            "_decoded": [],
        }

    # Bounded multi-hop outgoing dependency bag per landmark
    bags: List[Dict[int, float]] = []
    df_ctr: collections.Counter[int] = collections.Counter()

    for did in selected:
        bag: Dict[int, float] = collections.defaultdict(float)
        visited_proj: Set[int] = {did}
        frontier = [did]
        weights = (1.0, 0.5, 0.25, 0.125)
        for hop, w in enumerate(weights):
            if not frontier:
                break
            if hop >= 2 and len(bag) >= 12:
                break
            next_frontier: List[int] = []
            # Query in chunks for speed (uses PRIMARY KEY(src, dst))
            for u in frontier[:160]:
                for (dst,) in con.execute("SELECT dst FROM edges WHERE src=?", (u,)):
                    d_i = int(dst)
                    if d_i in ext_vocab_set and d_i != did:
                        bag[d_i] += w
                    elif 0 <= d_i < n_total and origin_of[d_i] == "project" and d_i not in visited_proj:
                        visited_proj.add(d_i)
                        next_frontier.append(d_i)
            frontier = next_frontier

        bags.append(bag)
        for tid in bag:
            df_ctr[tid] += 1

    # Select top discriminating vocabulary via smooth TF-IDF energy
    min_df = 3 if n >= 60 else 1
    max_df = int(0.80 * n) if n >= 10 else n
    term_score: Dict[int, float] = {}
    for tid, df in df_ctr.items():
        if df < min_df or df > max_df:
            continue
        idf = math.log((1.0 + n) / (1.0 + df))
        term_score[tid] = idf * df * (1.0 - df / float(max(1, n)))

    if not term_score and df_ctr:
        for tid, df in df_ctr.items():
            term_score[tid] = math.log((1.0 + n) / (1.0 + df)) * df

    vocab_ids = [tid for tid, _ in sorted(term_score.items(), key=lambda x: (-x[1], x[0]))[:max_vocab]]
    v_map = {tid: j for j, tid in enumerate(vocab_ids)}
    V = len(vocab_ids)

    X_tf = np.zeros((n, V), dtype=np.float64)
    if V > 0:
        idf_vec = np.array([math.log((1.0 + n) / (1.0 + df_ctr[tid])) for tid in vocab_ids], dtype=np.float64)
        for i, bag in enumerate(bags):
            for tid, w in bag.items():
                j = v_map.get(tid)
                if j is not None:
                    X_tf[i, j] = math.log1p(w) * idf_vec[j]
        tf_norms = np.linalg.norm(X_tf, axis=1, keepdims=True)
        X_tf_norm = X_tf / np.maximum(tf_norms, 1e-12)
    else:
        X_tf_norm = X_tf

    # Structural type features: kind one-hot, log(dom), type_nodes, value_nodes, type_ratio
    kind_cats = {"thm": 0, "theorem": 0, "lemma": 0, "def": 1, "abbrev": 1, "instance": 1}
    S_feat = np.zeros((n, 7), dtype=np.float64)
    type_ratios: List[float] = []
    display_kinds: List[str] = []
    for i, did in enumerate(selected):
        lk = lean_kind_by_id.get(did) or kind_of[did]
        display_kinds.append(lk)
        k_col = kind_cats.get(lk, 2)
        S_feat[i, k_col] = 1.0
        S_feat[i, 3] = math.log1p(max(1, sub_sz[did]))
        S_feat[i, 4] = math.log1p(max(0, tn_of[did]))
        S_feat[i, 5] = math.log1p(max(0, vn_of[did]))
        et_v, ev_v = et_of[did], ev_of[did]
        tr = et_v / float(max(1, et_v + ev_v))
        S_feat[i, 6] = tr
        type_ratios.append(round(tr, 4))

    for col in range(3, 7):
        mu = float(S_feat[:, col].mean())
        sd = float(S_feat[:, col].std())
        if sd > 1e-9:
            S_feat[:, col] = (S_feat[:, col] - mu) / sd
    S_feat *= 0.12

    X = np.hstack([X_tf_norm, S_feat]) if V > 0 else S_feat
    X = X / np.maximum(np.linalg.norm(X, axis=1, keepdims=True), 1e-12)

    U, S, _Vt = randomized_svd(X, k=k_svd, seed=seed)
    Z_svd = U * S[None, :] if S.size > 0 else np.zeros((n, 2), dtype=np.float64)
    tot_ss = float(np.sum(X * X))
    exp_ratios = [round(float(sv * sv / tot_ss), 5) for sv in S] if tot_ss > 0 else []
    exp_sum = round(float(sum(exp_ratios)), 4)

    pca2 = normalize_2d_isotropic(Z_svd[:, :2] if Z_svd.shape[1] >= 2 else Z_svd)
    knn2, nn_hi = knn2_umap_embedding(Z_svd, pca2, k_nn=k_nn, n_steps=n_steps, seed=seed)

    m_pca = evaluate_embedding_quality(Z_svd, pca2, nn_hi)
    m_knn = evaluate_embedding_quality(Z_svd, knn2, nn_hi)

    dir_tops = [dir_top_from_module(name_of[did], mod_of[did]) for did in selected]
    is_dom1k = [did in dom1k_set for did in selected]
    drifts, drift_stats = compute_namespace_drift(nn_hi, dir_tops, is_dom1k, k_drift=10)

    pillars_list: List[str] = []
    for did in selected:
        if origin_of[did] != "project":
            pillars_list.append("BR")
        else:
            tin = tin_by_id[did] if 0 <= did < len(tin_by_id) else -1
            rk = reg_by_dfs[tin] if (0 <= tin < len(reg_by_dfs)) else ""
            pillars_list.append(_pillar_code_for_region(rk, name_of[did]) if rk else "MAIN")

    pillars_tbl = sorted(set(pillars_list))
    dirs_tbl = sorted(set(dir_tops))
    kinds_tbl = sorted(set(display_kinds))
    clusters_tbl = [str(c["cluster_id"]) for c in raw_clusters]
    mods_tbl = sorted({str(mod_of[did]) for did in selected if mod_of[did] is not None})

    pil_map = {v: i for i, v in enumerate(pillars_tbl)}
    dir_map = {v: i for i, v in enumerate(dirs_tbl)}
    knd_map = {v: i for i, v in enumerate(kinds_tbl)}
    mod_map_idx = {v: i for i, v in enumerate(mods_tbl)}
    vocab_terms = [name_of[did] for did in vocab_ids]

    points_compact: List[List[Any]] = []
    decoded: List[Dict[str, Any]] = []
    for i, did in enumerate(selected):
        top_j = (
            [int(j) for j in np.argsort(-X_tf[i])[:4] if X_tf[i, j] > 0.0]
            if V > 0
            else []
        )
        nbr5 = [int(j) for j in nn_hi[i, :5]]
        cl_i = int(cluster_idx_of[did]) if 0 <= did < len(cluster_idx_of) else -1
        cl_id = clusters_tbl[cl_i] if 0 <= cl_i < len(clusters_tbl) else None
        mod_s = mod_of[did]
        mod_i = mod_map_idx[mod_s] if mod_s is not None else -1
        line_no = line_of_id.get(did)
        px, py = round(float(pca2[i, 0]), 4), round(float(pca2[i, 1]), 4)
        ux, uy = round(float(knn2[i, 0]), 4), round(float(knn2[i, 1]), 4)
        short = short_decl_name(name_of[did])
        dom_v = int(sub_sz[did]) if sub_sz[did] > 0 else 1

        points_compact.append([
            name_of[did],
            short,
            knd_map[display_kinds[i]],
            dom_v,
            pil_map[pillars_list[i]],
            dir_map[dir_tops[i]],
            cl_i,
            mod_i,
            line_no,
            px, py,
            ux, uy,
            top_j,
            nbr5,
            drifts[i],
            type_ratios[i],
        ])
        decoded.append({
            "name": name_of[did],
            "short": short,
            "kind": display_kinds[i],
            "dom": dom_v,
            "pillar": pillars_list[i],
            "dir_top": dir_tops[i],
            "cluster_id": cl_id,
            "mod": mod_s,
            "line": line_no,
            "px": px,
            "py": py,
            "ux": ux,
            "uy": uy,
            "top_terms": [vocab_terms[j] for j in top_j],
            "nn_idx": nbr5,
            "drift": drifts[i],
            "type_ratio": type_ratios[i],
        })

    return {
        "count": n,
        "svd_explained_variance_ratios": exp_ratios,
        "svd_explained_variance_sum": exp_sum,
        "metrics": {
            "pca2": m_pca,
            "knn2": m_knn,
            "drift": drift_stats,
        },
        "tables": {
            "pillars": pillars_tbl,
            "dirs": dirs_tbl,
            "kinds": kinds_tbl,
            "clusters": clusters_tbl,
            "mods": mods_tbl,
            "vocab_terms": vocab_terms,
        },
        "fields": [
            "name", "short", "kind_idx", "dom", "pillar_idx", "dir_idx",
            "cluster_idx", "mod_idx", "line", "px", "py", "ux", "uy",
            "top_term_idxs", "nn_idx", "drift", "type_ratio",
        ],
        "points": points_compact,
        "_decoded": decoded,
    }


def decode_layer_points(layer: Dict[str, Any]) -> List[Dict[str, Any]]:
    """Expand compact columnar/indexed rows of a layer into plain dicts."""
    tables = layer.get("tables", {})
    fields = layer.get("fields", [])
    pillars = tables.get("pillars", [])
    dirs = tables.get("dirs", [])
    kinds = tables.get("kinds", [])
    clusters = tables.get("clusters", [])
    mods = tables.get("mods", [])
    vocab = tables.get("vocab_terms", [])

    out: List[Dict[str, Any]] = []
    for row in layer.get("points", []):
        raw = dict(zip(fields, row))
        cl_i = raw.get("cluster_idx", -1)
        mod_i = raw.get("mod_idx", -1)
        item: Dict[str, Any] = {
            "name": raw["name"],
            "short": raw["short"],
            "kind": kinds[raw["kind_idx"]] if 0 <= raw.get("kind_idx", -1) < len(kinds) else "other",
            "dom": raw["dom"],
            "pillar": pillars[raw["pillar_idx"]] if 0 <= raw.get("pillar_idx", -1) < len(pillars) else "MAIN",
            "dir_top": dirs[raw["dir_idx"]] if 0 <= raw.get("dir_idx", -1) < len(dirs) else "<root>",
            "cluster_id": clusters[cl_i] if (0 <= cl_i < len(clusters)) else None,
            "mod": raw["mod"] if "mod" in raw else (mods[mod_i] if 0 <= mod_i < len(mods) else None),
            "line": raw.get("line"),
            "px": raw["px"],
            "py": raw["py"],
            "ux": raw["ux"],
            "uy": raw["uy"],
            "top_terms": [vocab[j] for j in raw.get("top_term_idxs", []) if 0 <= j < len(vocab)],
            "nn_idx": list(raw.get("nn_idx", [])),
            "drift": raw["drift"],
            "type_ratio": raw["type_ratio"],
        }
        if "id" in raw:
            item["id"] = raw["id"]
        if "label" in raw:
            item["label"] = raw["label"]
        out.append(item)
    return out


# ---------------------------------------------------------------------------
# Pure-Python 512x512 Preview PNG Renderer
# ---------------------------------------------------------------------------

def _draw_line_aa(
    canvas: List[bytearray],
    width: int,
    height: int,
    x0: float,
    y0: float,
    x1: float,
    y1: float,
    rgb: Tuple[int, int, int],
    alpha: float,
) -> None:
    steps = max(1, int(math.hypot(x1 - x0, y1 - y0)))
    for s in range(steps + 1):
        t = s / float(steps)
        px = int(round(x0 + (x1 - x0) * t))
        py = int(round(y0 + (y1 - y0) * t))
        if 0 <= py < height:
            atlas._blend_pixel(canvas[py], px, width, rgb, alpha)


def _draw_disc(
    canvas: List[bytearray],
    width: int,
    height: int,
    cx: float,
    cy: float,
    radius: float,
    rgb: Tuple[int, int, int],
    alpha: float = 0.90,
) -> None:
    r_ceil = int(math.ceil(radius + 0.5))
    ix, iy = int(round(cx)), int(round(cy))
    for dy in range(-r_ceil, r_ceil + 1):
        py = iy + dy
        if not (0 <= py < height):
            continue
        row = canvas[py]
        for dx in range(-r_ceil, r_ceil + 1):
            px = ix + dx
            if not (0 <= px < width):
                continue
            d = math.hypot((px - cx), (py - cy))
            if d <= radius + 0.4:
                edge_a = alpha * min(1.0, max(0.0, (radius + 0.4 - d) / 0.9))
                atlas._blend_pixel(row, px, width, rgb, edge_a)


def render_embedding_png(
    embedding_doc: Dict[str, Any],
    out_path: str,
    width: int = 512,
    height: int = 512,
) -> Dict[str, Any]:
    """Render a crisp `512x512` `knn2` preview PNG colored by proof pillar."""
    bg = (10, 12, 18)
    canvas: List[bytearray] = [
        bytearray([bg[0], bg[1], bg[2]] * width) for _ in range(height)
    ]

    # Subtle crosshair grid
    mid_x, mid_y = width // 2, height // 2
    for px in range(width):
        if (px % 4) < 2:
            atlas._blend_pixel(canvas[mid_y], px, width, (70, 82, 110), 0.35)
    for py in range(height):
        if (py % 4) < 2:
            atlas._blend_pixel(canvas[py], mid_x, width, (70, 82, 110), 0.35)

    lm_layer = embedding_doc.get("layers", {}).get("landmarks", {})
    pts = decode_layer_points(lm_layer)
    if not pts:
        pts = decode_layer_points(embedding_doc.get("layers", {}).get("clusters_141", {}))

    pad = 24
    span_x = width - 2 * pad
    span_y = height - 2 * pad

    def _to_px(ux: float, uy: float) -> Tuple[float, float]:
        return pad + 0.5 * (ux + 1.0) * span_x, pad + 0.5 * (1.0 - uy) * span_y

    # Faint nearest-neighbor threads for top hubs
    top_hubs = sorted(range(len(pts)), key=lambda i: (-pts[i]["dom"], i))[:60]
    for i in top_hubs:
        x0, y0 = _to_px(pts[i]["ux"], pts[i]["uy"])
        rgb = _PILLAR_RGB.get(pts[i]["pillar"], (160, 180, 210))
        for j in pts[i].get("nn_idx", [])[:2]:
            if 0 <= j < len(pts):
                x1, y1 = _to_px(pts[j]["ux"], pts[j]["uy"])
                _draw_line_aa(canvas, width, height, x0, y0, x1, y1, rgb, 0.14)

    # Scatter dots (smaller background first, larger hubs on top)
    order = sorted(range(len(pts)), key=lambda i: (pts[i]["dom"], i))
    for i in order:
        p = pts[i]
        cx, cy = _to_px(p["ux"], p["uy"])
        rgb = _PILLAR_RGB.get(p["pillar"], (180, 195, 220))
        r = 1.6 if p["dom"] < 1000 else (2.4 if p["dom"] < 10000 else 3.8)
        alpha = 0.78 if p["dom"] < 1000 else 0.92
        _draw_disc(canvas, width, height, cx, cy, r, rgb, alpha=alpha)

    # Top-left compact legend
    legend_tags = ["A", "D", "C", "B", "DM", "LIT", "BR"]
    present_pils = {p["pillar"] for p in pts}
    lx = 10
    for tag in legend_tags:
        if tag in present_pils:
            rgb = _PILLAR_RGB.get(tag, (200, 210, 230))
            _draw_disc(canvas, width, height, lx + 3, 11, 3.0, rgb, 0.95)
            atlas._draw_text_5x7(canvas, width, height, lx + 9, 8, tag, (230, 238, 255))
            lx += 14 + len(tag) * 6

    png_bytes = atlas.encode_png_rgb(width, height, canvas)
    os.makedirs(os.path.dirname(os.path.abspath(out_path)), exist_ok=True)
    with open(out_path, "wb") as f:
        f.write(png_bytes)
    return {"width": width, "height": height, "bytes": len(png_bytes)}


# ---------------------------------------------------------------------------
# Unified Orchestrator & CLI
# ---------------------------------------------------------------------------

def run_embedding(
    kernel_db_path: str,
    leanre_db_path: Optional[str] = None,
    cluster_labels_path: Optional[str] = None,
    portability_path: Optional[str] = None,
    out_json_path: Optional[str] = None,
    png_path: Optional[str] = None,
    max_landmarks: int = 1800,
    svd_dim: int = 24,
    knn_k: int = 15,
    knn_steps: int = 180,
    seed: int = 42,
    workers: int = 0,
) -> Dict[str, Any]:
    """Compute the 2-layer TF-IDF + SVD(k=24) + `pca2`/`knn2` proof map."""
    t0 = time.perf_counter()

    cluster_labels_map: Dict[str, Dict[str, Any]] = {}
    if cluster_labels_path and os.path.isfile(os.path.realpath(cluster_labels_path)):
        with open(cluster_labels_path, "r", encoding="utf-8") as f:
            c141_doc = json.load(f)
        for item in c141_doc.get("clusters", []):
            cid = item.get("cluster_id")
            if cid:
                cluster_labels_map[str(cid)] = item

    portability_ids: List[int] = []
    if portability_path and os.path.isfile(os.path.realpath(portability_path)):
        with open(portability_path, "r", encoding="utf-8") as f:
            pg_doc = json.load(f)
        for item in pg_doc.get("targets", []):
            if item.get("decl_id") is not None:
                portability_ids.append(int(item["decl_id"]))

    with contextlib.closing(atlas.connect_ro(kernel_db_path, mmap_bytes=8_589_934_592)) as con:
        dom_info = atlas.compute_dom_dfs(con, tree_id=0, n_bins=256)
        max_id = dom_info["max_decl_id"]
        n_total = max_id + 1 if max_id >= 0 else 0

        if n_total == 0:
            empty_doc: Dict[str, Any] = {
                "schema": SCHEMA_VERSION,
                "inputs": {"kernel_db": atlas.safe_display_path(kernel_db_path)},
                "runtime_sec": round(time.perf_counter() - t0, 3),
                "svd_dim": svd_dim,
                "knn_k": knn_k,
                "knn_steps": knn_steps,
                "seed": seed,
                "layers": {
                    "clusters_141": _build_clusters_layer(
                        kernel_db_path, [], np.zeros(0, dtype=np.int32), [], 0, [], [], {},
                    ),
                    "landmarks": _build_landmarks_layer(
                        con, [], set(), set(), 0, [], [], [], [], [], [], [], [], [], [], [], np.zeros(0, dtype=np.int32), [], {}, {},
                    ),
                },
            }
            if out_json_path:
                _write_compact_json(empty_doc, out_json_path)
            return empty_doc

        name_of: List[str] = [""] * n_total
        kind_of: List[str] = [""] * n_total
        tn_of = array.array("I", [0]) * n_total
        vn_of = array.array("I", [0]) * n_total
        fi_of = array.array("I", [0]) * n_total
        et_of = array.array("I", [0]) * n_total
        ev_of = array.array("I", [0]) * n_total
        live_of = bytearray(n_total)

        for did, nm, kd, tn, vn, fi, fot, fov, lm in con.execute(
            "SELECT id, name, kind, type_nodes, value_nodes, fan_in, fan_out_type, fan_out_value, live_mask FROM decls"
        ):
            d_i = int(did)
            name_of[d_i] = str(nm)
            kind_of[d_i] = str(kd)
            tn_of[d_i] = int(tn)
            vn_of[d_i] = int(vn)
            fi_of[d_i] = int(fi)
            et_of[d_i] = int(fot)
            ev_of[d_i] = int(fov)
            live_of[d_i] = 1 if lm != 0 else 0

        mod_of: List[Optional[str]] = [None] * n_total
        meth_of: List[Optional[str]] = [None] * n_total
        src_id_of = array.array("i", [-1]) * n_total
        if atlas._table_exists(con, "decl_module"):
            for did, mod, meth, sid in con.execute(
                "SELECT decl_id, module, method, src_decl_id FROM decl_module"
            ):
                d_i = int(did)
                if 0 <= d_i < n_total:
                    mod_of[d_i] = mod
                    meth_of[d_i] = meth
                    if sid is not None:
                        src_id_of[d_i] = int(sid)

        has_src_repo = "src_repo" in atlas._table_columns(con, "decls")
        srepo_map: Dict[int, str] = {}
        if has_src_repo:
            for did, sr in con.execute("SELECT id, src_repo FROM decls WHERE src_repo IS NOT NULL"):
                srepo_map[int(did)] = str(sr)

        origin_of: List[str] = ["project"] * n_total
        for d_i in range(n_total):
            if name_of[d_i]:
                origin_of[d_i] = atlas.classify_decl_origin(
                    name_of[d_i], mod_of[d_i], meth_of[d_i], srepo_map.get(d_i)
                )

        # Load dom (tree_id=0)
        children: Dict[int, List[int]] = collections.defaultdict(list)
        sub_sz = array.array("I", [0]) * n_total
        dom_roots_top: List[int] = []
        if atlas._table_exists(con, "dom"):
            dom_rows = con.execute(
                "SELECT decl_id, idom, subtree_size FROM dom WHERE tree_id=0"
            ).fetchall()
        else:
            dom_rows = []

        if dom_rows:
            for did, idom, sz in dom_rows:
                d_i = int(did)
                sub_sz[d_i] = int(sz)
                if idom is None:
                    dom_roots_top.append(d_i)
                else:
                    children[int(idom)].append(d_i)
        else:
            for d_i in range(n_total):
                if live_of[d_i]:
                    sub_sz[d_i] = 1
                    dom_roots_top.append(d_i)

        # Map DFS index -> atlas region key
        reg_by_dfs = [""] * max(0, dom_info["n_live"])
        for reg in dom_info["regions"]:
            rk = str(reg["key"])
            for pos in range(int(reg["dfs_start"]), int(reg["dfs_end"])):
                reg_by_dfs[pos] = rk

        raw_clusters, cluster_idx_of = _build_cluster_partition(
            con=con,
            n_total=n_total,
            name_of=name_of,
            kind_of=kind_of,
            live_of=live_of,
            fan_in_of=fi_of,
            mod_of=mod_of,
            sub_sz=sub_sz,
            children=children,
            dom_roots_top=dom_roots_top,
            tin_by_id=dom_info["tin_by_id"],
            reg_by_dfs=reg_by_dfs,
            cluster_labels_map=cluster_labels_map,
        )

        # Compute per-cluster average type_ratio from member fan_out_type / fan_out_value
        for cl in raw_clusters:
            et_sum = 0
            ev_sum = 0
            for d_i in cl["members"]:
                et_sum += et_of[d_i]
                ev_sum += ev_of[d_i]
            cl["type_ratio"] = et_sum / float(max(1, et_sum + ev_sum))

        # External / library vocabulary pool
        ext_ids = [
            d_i
            for d_i in range(n_total)
            if name_of[d_i]
            and origin_of[d_i] != "project"
            and not is_compiler_aux(name_of[d_i])
            and not name_of[d_i].startswith("_private.")
            and name_of[d_i] not in _STOP_EXACT
        ]
        if len(ext_ids) < 12:
            # Small/synthetic corpus fallback: include all non-aux declarations
            ext_ids = [
                d_i
                for d_i in range(n_total)
                if name_of[d_i] and not is_compiler_aux(name_of[d_i]) and name_of[d_i] not in _STOP_EXACT
            ]
        ext_vocab_set = set(ext_ids)

        # Top external candidates for cluster-level matrix (fast O(1) lookup array)
        ext_ranked = sorted(ext_ids, key=lambda d: (-fi_of[d], d))
        cluster_cand_ext = ext_ranked[:3000]

        # Optional `leanre.db` enrichment (structures + line numbers)
        lean_kind_by_id: Dict[int, str] = {}
        line_of_id: Dict[int, int] = {}
        has_ldb = bool(leanre_db_path and os.path.isfile(os.path.realpath(leanre_db_path)))
        if has_ldb and leanre_db_path:
            with contextlib.closing(atlas.connect_ro(leanre_db_path)) as ldb:
                if atlas._table_exists(ldb, "declarations"):
                    struct_sids = {
                        int(r[0])
                        for r in ldb.execute("SELECT id FROM declarations WHERE kind IN ('structure', 'class')")
                    }
                    struct_names = {
                        str(r[0]): str(r[1])
                        for r in ldb.execute("SELECT name, kind FROM declarations WHERE kind IN ('structure', 'class')")
                    }
                    for d_i in range(n_total):
                        sid = int(src_id_of[d_i])
                        if sid >= 0 and sid in struct_sids:
                            lean_kind_by_id[d_i] = "structure"
                        elif name_of[d_i] in struct_names:
                            lean_kind_by_id[d_i] = struct_names[name_of[d_i]]
                    # Defer line number lookup until landmarks + cluster roots are selected!
                    selected, dom1k_set = _select_landmarks(
                        n_total=n_total,
                        name_of=name_of,
                        kind_of=kind_of,
                        live_of=live_of,
                        fan_in_of=fi_of,
                        tn_of=tn_of,
                        sub_sz=sub_sz,
                        mod_of=mod_of,
                        origin_of=origin_of,
                        raw_clusters=raw_clusters,
                        lean_kind_by_id=lean_kind_by_id,
                        portability_ids=portability_ids,
                        max_landmarks=max_landmarks,
                    )
                    need_ids = set(selected) | {int(c["root_decl_id"]) for c in raw_clusters}
                    sid_to_did: Dict[int, List[int]] = collections.defaultdict(list)
                    fallback_names: Dict[str, List[int]] = collections.defaultdict(list)
                    for d_i in need_ids:
                        if 0 <= d_i < n_total:
                            sid = int(src_id_of[d_i])
                            if sid >= 0:
                                sid_to_did[sid].append(d_i)
                            else:
                                fallback_names[name_of[d_i]].append(d_i)
                    sids_list = sorted(sid_to_did.keys())
                    for i in range(0, len(sids_list), 400):
                        chunk = sids_list[i : i + 400]
                        qm = ",".join("?" for _ in chunk)
                        for sid_v, kd_v, lno_v in ldb.execute(
                            f"SELECT id, kind, line_no FROM declarations WHERE id IN ({qm})", chunk
                        ):
                            for d_i in sid_to_did[int(sid_v)]:
                                line_of_id[d_i] = int(lno_v)
                                if str(kd_v) in ("structure", "class"):
                                    lean_kind_by_id[d_i] = str(kd_v)
                    fnames = sorted(fallback_names.keys())
                    for i in range(0, len(fnames), 400):
                        chunk = fnames[i : i + 400]
                        qm = ",".join("?" for _ in chunk)
                        for nm_v, kd_v, lno_v in ldb.execute(
                            f"SELECT name, kind, line_no FROM declarations WHERE name IN ({qm})", chunk
                        ):
                            for d_i in fallback_names[str(nm_v)]:
                                line_of_id.setdefault(d_i, int(lno_v))
                                if str(kd_v) in ("structure", "class"):
                                    lean_kind_by_id[d_i] = str(kd_v)
        else:
            selected, dom1k_set = _select_landmarks(
                n_total=n_total,
                name_of=name_of,
                kind_of=kind_of,
                live_of=live_of,
                fan_in_of=fi_of,
                tn_of=tn_of,
                sub_sz=sub_sz,
                mod_of=mod_of,
                origin_of=origin_of,
                raw_clusters=raw_clusters,
                lean_kind_by_id=lean_kind_by_id,
                portability_ids=portability_ids,
                max_landmarks=max_landmarks,
            )

        clusters_layer = _build_clusters_layer(
            kernel_db_path=kernel_db_path,
            raw_clusters=raw_clusters,
            cluster_idx_of=cluster_idx_of,
            cand_ext_ids=cluster_cand_ext,
            n_total=n_total,
            name_of=name_of,
            type_ratio_of=[0.0] * n_total,
            line_of_id=line_of_id,
            max_vocab=768,
            k_svd=svd_dim,
            k_nn=knn_k,
            n_steps=knn_steps,
            seed=seed,
            workers=workers,
        )
        landmarks_layer = _build_landmarks_layer(
            con=con,
            selected=selected,
            dom1k_set=dom1k_set,
            ext_vocab_set=ext_vocab_set,
            n_total=n_total,
            name_of=name_of,
            kind_of=kind_of,
            tn_of=tn_of,
            vn_of=vn_of,
            et_of=et_of,
            ev_of=ev_of,
            sub_sz=sub_sz,
            mod_of=mod_of,
            origin_of=origin_of,
            tin_by_id=dom_info["tin_by_id"],
            reg_by_dfs=reg_by_dfs,
            cluster_idx_of=cluster_idx_of,
            raw_clusters=raw_clusters,
            lean_kind_by_id=lean_kind_by_id,
            line_of_id=line_of_id,
            max_vocab=1024,
            k_svd=svd_dim,
            k_nn=knn_k,
            n_steps=knn_steps,
            seed=seed,
        )

    # Pop internal `_decoded` before JSON serialization (keep for optional PNG render)
    cl_decoded = clusters_layer.pop("_decoded", [])
    lm_decoded = landmarks_layer.pop("_decoded", [])

    doc: Dict[str, Any] = {
        "schema": SCHEMA_VERSION,
        "inputs": {
            "kernel_db": atlas.safe_display_path(kernel_db_path),
            "leanre_db": atlas.safe_display_path(leanre_db_path) if has_ldb else None,
            "numpy_version": str(np.__version__),
        },
        "runtime_sec": round(time.perf_counter() - t0, 3),
        "svd_dim": int(svd_dim),
        "knn_k": int(knn_k),
        "knn_steps": int(knn_steps),
        "seed": int(seed),
        "layers": {
            "clusters_141": clusters_layer,
            "landmarks": landmarks_layer,
        },
    }

    if out_json_path:
        _write_compact_json(doc, out_json_path)

    if png_path:
        render_embedding_png(doc, png_path, width=512, height=512)

    # Keep decoded accessible in Python return value only? No, keep return value identical to JSON!
    _ = (cl_decoded, lm_decoded)
    return doc


def _write_compact_json(doc: Dict[str, Any], out_path: str) -> None:
    os.makedirs(os.path.dirname(os.path.abspath(out_path)), exist_ok=True)
    payload = json.dumps(doc, separators=(",", ":"), ensure_ascii=False)
    with open(out_path, "w", encoding="utf-8") as f:
        f.write(payload)
        f.write("\n")


def build_arg_parser() -> argparse.ArgumentParser:
    ap = argparse.ArgumentParser(
        prog="python3 leanre/embedding.py",
        description="Build 2D TF-IDF + SVD(k=24) + pca2/knn2 embedding map over read-only kernel.db.",
    )
    ap.add_argument("--kernel-db", default=DEFAULT_KERNEL_DB, help="Path to read-only kernel.db")
    ap.add_argument("--leanre-db", default=DEFAULT_LEANRE_DB, help="Optional path to leanre.db")
    ap.add_argument("--cluster-labels", default=DEFAULT_CLUSTER_LABELS, help="Optional cluster_labels_141.json")
    ap.add_argument("--portability", default=DEFAULT_PORTABILITY, help="Optional portability_gems.json")
    ap.add_argument("--out", default=DEFAULT_OUT_JSON, help="Output JSON path (<= 650 KB)")
    ap.add_argument("--png", default=None, help="Optional path to write 512x512 preview PNG")
    ap.add_argument("--max-landmarks", type=int, default=1800, help="Target landmark count")
    ap.add_argument("--svd-dim", type=int, default=24, help="Truncated SVD rank")
    ap.add_argument("--knn-k", type=int, default=15, help="k-NN neighbors in SVD space")
    ap.add_argument("--knn-steps", type=int, default=180, help="Gradient steps for knn2")
    ap.add_argument("--seed", type=int, default=42, help="Deterministic RNG seed")
    ap.add_argument("--workers", type=int, default=0, help="Worker processes (0 = auto)")
    return ap


def main(argv: Optional[Sequence[str]] = None) -> int:
    args = build_arg_parser().parse_args(argv)
    doc = run_embedding(
        kernel_db_path=args.kernel_db,
        leanre_db_path=args.leanre_db,
        cluster_labels_path=args.cluster_labels,
        portability_path=args.portability,
        out_json_path=args.out,
        png_path=args.png,
        max_landmarks=args.max_landmarks,
        svd_dim=args.svd_dim,
        knn_k=args.knn_k,
        knn_steps=args.knn_steps,
        seed=args.seed,
        workers=args.workers,
    )
    cl = doc["layers"]["clusters_141"]
    lm = doc["layers"]["landmarks"]
    out_bytes = os.path.getsize(args.out) if (args.out and os.path.isfile(args.out)) else 0
    print(
        f"[embedding] done in {doc['runtime_sec']:.2f}s | "
        f"clusters={cl['count']} (knn15={cl['metrics']['knn2']['knn_preservation']:.4f}, "
        f"trust={cl['metrics']['knn2']['trustworthiness']:.4f}) | "
        f"landmarks={lm['count']} (pca15={lm['metrics']['pca2']['knn_preservation']:.4f}, "
        f"knn15={lm['metrics']['knn2']['knn_preservation']:.4f}, "
        f"trust={lm['metrics']['knn2']['trustworthiness']:.4f}, "
        f"dom1k_nn1_diff={lm['metrics']['drift']['dom1k_nn1_diff_folder_pct']:.2f}%) | "
        f"json={out_bytes:,} B"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
