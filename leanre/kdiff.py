#!/usr/bin/env python3
"""leanre.kdiff -- Kernel-exact BinDiff for Lean 4 `kernel.db` snapshots.

Compares two SQLite snapshots produced by `leanre kernel` (`leanre-kernel`)
strictly in read-only mode (`mode=ro`, `PRAGMA query_only=1`) and NEVER joins
across snapshots on numeric `decl_id`.

Alignment priority tiers:
  1. Exact name match:
     - `unchanged`     : same `k1n` (`sighash`), same `value_nodes`, same `kind`
     - `proof_changed` : same `k1n`, changed `value_nodes` or `kind`
     - `type_changed`  : different `k1n` (`sighash`)
  2. Exact `k1n` (`sighash`) rename/move on remaining unmatched decls
     (1:1 clean rename; `N:M` multiplicity flagged as ambiguous without guessing)
  3. Exact `k1a` (`sighash_anon`) alpha/structural match on remaining unmatched decls
     (1:1 clean alpha match; `N:M` multiplicity flagged as ambiguous without guessing)
  4. `added` (in B only) and `removed` (in A only)

Also tracks security/TCB regressions (newly introduced `sorryAx`,
`ofReduceBool`/`native_decide`, `ofReduceNat`, `trustCompiler`, custom axioms,
newly live `decide_kernel`), root cone swings, top `dom` (`tree_id=0`) /
`value_nodes` / `type_nodes` movers, and optional read-only `--annot-dir`
reanchor impact previews.

Stdlib only (Python 3.11+).
"""
from __future__ import annotations

import argparse
import collections
import heapq
import json
import os
import re
import sqlite3
import sys
import tempfile
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable, Dict, Iterable, List, Optional, Sequence, Set, Tuple

_HERE = os.path.dirname(os.path.abspath(__file__))
_REPO_ROOT = os.path.abspath(os.path.join(_HERE, ".."))
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)

SCHEMA_VERSION = "leanre.kdiff/1"

# Kernel-pattern flags matching `leanre/kernel.py` and `leanre/kernel-rs/src/walk.rs`
F_REFL_TRUE = 1
F_OF_DECIDE = 2
F_REDUCE_BOOL = 4
F_REDUCE_NAT = 8
F_SORRY = 16
F_TRUST_COMPILER = 32

# Declaration attribute bits matching `leanre/kernel-rs/src/parse.rs`
ATTR_UNSAFE = 1
ATTR_PARTIAL = 2

FLAG_NAMES: Tuple[Tuple[int, str], ...] = (
    (F_REFL_TRUE, "refl_true"),
    (F_OF_DECIDE, "decide_kernel"),
    (F_REDUCE_BOOL, "ofReduceBool"),
    (F_REDUCE_NAT, "ofReduceNat"),
    (F_SORRY, "sorryAx"),
    (F_TRUST_COMPILER, "trustCompiler"),
)

STANDARD_AXIOMS = frozenset({"propext", "Quot.sound", "Classical.choice"})

REGRESSION_CATEGORIES = (
    "new_sorry",
    "new_reduce_bool",
    "new_reduce_nat",
    "new_trust_compiler",
    "new_custom_axiom",
    "newly_live_decide_kernel",
)


def decode_flags(flags: int) -> List[str]:
    return [name for bit, name in FLAG_NAMES if flags & bit]


def connect_ro(path: str) -> sqlite3.Connection:
    """Open an existing SQLite database strictly in read-only URI mode."""
    real = os.path.realpath(path)
    if not os.path.isfile(real):
        raise FileNotFoundError(f"Missing SQLite database: {path}")
    uri = Path(real).as_uri() + "?mode=ro"
    conn = sqlite3.connect(uri, uri=True)
    conn.execute("PRAGMA query_only=1")
    return conn


def _safe_write_text(out_path: str, content: str) -> None:
    """Atomically write text to `out_path`, refusing symlink targets."""
    if os.path.islink(out_path):
        raise ValueError(f"Refusing to write through symlink: {out_path}")
    abs_out = os.path.abspath(out_path)
    parent = os.path.dirname(abs_out)
    if parent:
        os.makedirs(parent, exist_ok=True)
    fd, tmp_path = tempfile.mkstemp(prefix=".kdiff-", suffix=".tmp", dir=parent or ".")
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as f:
            f.write(content)
        if os.path.islink(out_path):
            raise ValueError(f"Refusing to write through symlink: {out_path}")
        os.replace(tmp_path, abs_out)
    except BaseException:
        if os.path.exists(tmp_path):
            os.unlink(tmp_path)
        raise


def _rel_label(path: Optional[str]) -> Optional[str]:
    """Return repo-relative path or basename so local home paths never leak."""
    if not path:
        return None
    ap = os.path.abspath(path)
    try:
        rel = os.path.relpath(ap, _REPO_ROOT)
        if not rel.startswith(".."):
            return rel.replace(os.sep, "/")
    except ValueError:
        pass
    return os.path.basename(ap)


def _compile_filter(pattern: Optional[str]) -> Optional[Callable[[str], bool]]:
    if not pattern:
        return None
    try:
        rx = re.compile(pattern)
        return lambda s: bool(rx.search(s))
    except re.error:
        return lambda s: pattern in s


def _matches_pair(flt: Optional[Callable[[str], bool]], a_name: Optional[str], b_name: Optional[str]) -> bool:
    if flt is None:
        return True
    return bool((a_name and flt(a_name)) or (b_name and flt(b_name)))


def _matches_any(flt: Optional[Callable[[str], bool]], names: Iterable[str]) -> bool:
    if flt is None:
        return True
    return any(flt(n) for n in names)


@dataclass(frozen=True, slots=True)
class DeclRec:
    kind: str
    type_nodes: int
    value_nodes: int
    flags: int
    live_mask: int
    stmt_mask: int
    attrs: int
    sighash: Optional[str]
    sighash_anon: Optional[str]
    dom_subtree: Optional[int]


def _get_tables(conn: sqlite3.Connection) -> Set[str]:
    return {
        row[0]
        for row in conn.execute(
            "SELECT name FROM sqlite_master WHERE type IN ('table', 'view')"
        )
    }


def _decls_select_sql(conn: sqlite3.Connection) -> Tuple[str, Dict[str, int]]:
    cols = [row[1] for row in conn.execute("PRAGMA table_info(decls)")]
    col_set = set(cols)
    if "id" not in col_set or "name" not in col_set or "kind" not in col_set:
        raise ValueError("Invalid kernel.db: `decls` table missing required columns")
    want = [
        ("id", "id"),
        ("name", "name"),
        ("kind", "kind"),
        ("type_nodes", "type_nodes"),
        ("value_nodes", "value_nodes"),
        ("flags", "flags"),
        ("live_mask", "live_mask"),
        ("stmt_mask", "stmt_mask"),
        ("attrs", "attrs"),
        ("sighash", "sighash"),
        ("sighash_anon", "sighash_anon"),
    ]
    exprs: List[str] = []
    idx: Dict[str, int] = {}
    for pos, (c, alias) in enumerate(want):
        idx[alias] = pos
        if c in col_set:
            exprs.append(c)
        elif c in ("sighash", "sighash_anon"):
            exprs.append("NULL")
        else:
            exprs.append("0")
    return f"SELECT {', '.join(exprs)} FROM decls", idx


def _load_dom0_and_roots(
    conn: sqlite3.Connection, tables: Set[str]
) -> Tuple[Dict[int, int], List[Dict[str, Any]], Optional[int], Dict[str, int]]:
    """Read within-DB `dom(tree_id=0)` (keyed by local decl_id) and `roots`."""
    dom_by_id: Dict[int, int] = {}
    dom_tree0_nodes: Optional[int] = None
    root_tree_nodes: Dict[str, int] = {}

    if "dom_trees" in tables:
        for tid, label, n_nodes in conn.execute("SELECT id, label, n_nodes FROM dom_trees"):
            if int(tid) == 0:
                dom_tree0_nodes = int(n_nodes)
            elif isinstance(label, str) and label.startswith("ROOT:"):
                root_tree_nodes[label[5:]] = int(n_nodes)

    if "dom" in tables:
        for did, sz in conn.execute("SELECT decl_id, subtree_size FROM dom WHERE tree_id = 0"):
            dom_by_id[int(did)] = int(sz)
        if dom_tree0_nodes is None and dom_by_id:
            dom_tree0_nodes = len(dom_by_id)

    roots: List[Dict[str, Any]] = []
    if "roots" in tables:
        for rid, rname, decl_id, grp in conn.execute(
            "SELECT id, name, decl_id, grp FROM roots ORDER BY id"
        ):
            roots.append(
                {
                    "bit": int(rid),
                    "name": rname,
                    "group": grp,
                    "dom_subtree": dom_by_id.get(int(decl_id)),
                    "dom_tree_nodes": root_tree_nodes.get(rname),
                }
            )
    return dom_by_id, roots, dom_tree0_nodes, root_tree_nodes


def _load_db_a(
    path: str,
) -> Tuple[Dict[str, DeclRec], List[Dict[str, Any]], Optional[int], Dict[int, int], Dict[int, int], int]:
    conn = connect_ro(path)
    try:
        tables = _get_tables(conn)
        if "decls" not in tables:
            raise ValueError(f"Invalid kernel.db (missing `decls` table): {path}")
        dom_by_id, roots, dom0_nodes, _ = _load_dom0_and_roots(conn, tables)
        sql, _ = _decls_select_sql(conn)

        live_counts: Dict[int, int] = collections.Counter()
        stmt_counts: Dict[int, int] = collections.Counter()
        root_bits = [r["bit"] for r in roots if 0 <= r["bit"] < 64]

        a_map: Dict[str, DeclRec] = {}
        n_decls = 0
        intern = sys.intern
        for did, name, kind, tn, vn, fl, lm, sm, at, sh, sha in conn.execute(sql):
            n_decls += 1
            lm_i = int(lm)
            sm_i = int(sm)
            for b in root_bits:
                bit = 1 << b
                if lm_i & bit:
                    live_counts[b] += 1
                if sm_i & bit:
                    stmt_counts[b] += 1
            a_map[name] = DeclRec(
                kind=intern(kind),
                type_nodes=int(tn),
                value_nodes=int(vn),
                flags=int(fl),
                live_mask=lm_i,
                stmt_mask=sm_i,
                attrs=int(at),
                sighash=sh or None,
                sighash_anon=sha or None,
                dom_subtree=dom_by_id.get(int(did)),
            )
        return a_map, roots, dom0_nodes, dict(live_counts), dict(stmt_counts), n_decls
    finally:
        conn.close()


def _detect_pair_regressions(
    a_name: Optional[str],
    ra: Optional[DeclRec],
    b_name: str,
    rb: DeclRec,
    tier: str,
) -> Tuple[List[Tuple[str, Dict[str, Any]]], List[Tuple[str, Dict[str, Any]]]]:
    """Return `(regressions, improvements)` for a `(ra, rb)` pair (or `ra=None` for added)."""
    regs: List[Tuple[str, Dict[str, Any]]] = []
    imps: List[Tuple[str, Dict[str, Any]]] = []

    fl_a = ra.flags if ra is not None else 0
    fl_b = rb.flags
    lm_a = ra.live_mask if ra is not None else 0
    lm_b = rb.live_mask

    def mk(cat: str, detail: str) -> Dict[str, Any]:
        return {
            "category": cat,
            "name": b_name,
            "a_name": a_name,
            "tier": tier,
            "kind": rb.kind,
            "flags_a": fl_a,
            "flags_b": fl_b,
            "flag_names_b": decode_flags(fl_b),
            "live_mask_a": lm_a,
            "live_mask_b": lm_b,
            "live_b": lm_b != 0,
            "value_nodes_b": rb.value_nodes,
            "type_nodes_b": rb.type_nodes,
            "detail": detail,
        }

    # 1. sorryAx (F_SORRY or sorryAx constant newly added/live)
    has_sorry_a = (fl_a & F_SORRY) != 0 or (a_name == "sorryAx" and lm_a != 0)
    has_sorry_b = (fl_b & F_SORRY) != 0 or (b_name == "sorryAx" and (ra is None or lm_b != 0))
    if has_sorry_b and not has_sorry_a:
        regs.append(("new_sorry", mk("new_sorry", "newly introduced sorryAx reference")))
    elif has_sorry_a and not has_sorry_b and ra is not None:
        imps.append(("resolved_sorry", mk("resolved_sorry", "sorryAx reference removed")))

    # 2. ofReduceBool / native_decide (F_REDUCE_BOOL)
    has_rb_a = (fl_a & F_REDUCE_BOOL) != 0 or (a_name in ("Lean.ofReduceBool", "Lean.reduceBool") and lm_a != 0)
    has_rb_b = (fl_b & F_REDUCE_BOOL) != 0 or (b_name in ("Lean.ofReduceBool", "Lean.reduceBool") and lm_b != 0)
    if has_rb_b and not has_rb_a:
        regs.append(("new_reduce_bool", mk("new_reduce_bool", "newly introduced ofReduceBool / native_decide")))
    elif has_rb_a and not has_rb_b and ra is not None:
        imps.append(("resolved_reduce_bool", mk("resolved_reduce_bool", "ofReduceBool removed")))

    # 3. ofReduceNat (F_REDUCE_NAT)
    has_rn_a = (fl_a & F_REDUCE_NAT) != 0 or (a_name in ("Lean.ofReduceNat", "Lean.reduceNat") and lm_a != 0)
    has_rn_b = (fl_b & F_REDUCE_NAT) != 0 or (b_name in ("Lean.ofReduceNat", "Lean.reduceNat") and lm_b != 0)
    if has_rn_b and not has_rn_a:
        regs.append(("new_reduce_nat", mk("new_reduce_nat", "newly introduced ofReduceNat")))
    elif has_rn_a and not has_rn_b and ra is not None:
        imps.append(("resolved_reduce_nat", mk("resolved_reduce_nat", "ofReduceNat removed")))

    # 4. trustCompiler (F_TRUST_COMPILER)
    has_tc_a = (fl_a & F_TRUST_COMPILER) != 0 or (a_name == "Lean.trustCompiler" and lm_a != 0)
    has_tc_b = (fl_b & F_TRUST_COMPILER) != 0 or (b_name == "Lean.trustCompiler" and lm_b != 0)
    if has_tc_b and not has_tc_a:
        regs.append(("new_trust_compiler", mk("new_trust_compiler", "newly introduced trustCompiler")))
    elif has_tc_a and not has_tc_b and ra is not None:
        imps.append(("resolved_trust_compiler", mk("resolved_trust_compiler", "trustCompiler removed")))

    # 5. Custom axioms (kind == 'axiom' outside standard axioms)
    is_cax_a = ra is not None and ra.kind == "axiom" and (a_name not in STANDARD_AXIOMS)
    is_cax_b = rb.kind == "axiom" and (b_name not in STANDARD_AXIOMS)
    if is_cax_b and not is_cax_a:
        regs.append(("new_custom_axiom", mk("new_custom_axiom", "newly introduced custom axiom")))
    elif is_cax_a and not is_cax_b and ra is not None:
        imps.append(("removed_custom_axiom", mk("removed_custom_axiom", "custom axiom eliminated or converted")))

    # 6. Newly live decide_kernel (F_OF_DECIDE with live_mask != 0)
    live_dk_a = (fl_a & F_OF_DECIDE) != 0 and lm_a != 0
    live_dk_b = (fl_b & F_OF_DECIDE) != 0 and lm_b != 0
    if live_dk_b and not live_dk_a:
        detail = (
            "decide_kernel transitioned dead -> live"
            if (ra is not None and (fl_a & F_OF_DECIDE) != 0)
            else "newly live decide_kernel (F_OF_DECIDE)"
        )
        regs.append(("newly_live_decide_kernel", mk("newly_live_decide_kernel", detail)))
    elif live_dk_a and not live_dk_b and ra is not None:
        imps.append(("deadened_decide_kernel", mk("deadened_decide_kernel", "decide_kernel no longer live")))

    return regs, imps


class _TopK:
    """Bounded min-heap tracking the top-K entries by `(abs_delta, max_val, key)`."""

    def __init__(self, k: int) -> None:
        self.k = k
        self._heap: List[Tuple[int, int, str, Dict[str, Any]]] = []
        self._all: List[Tuple[int, int, str, Dict[str, Any]]] = []

    def push(self, abs_delta: int, max_val: int, name: str, item: Dict[str, Any]) -> None:
        entry = (abs_delta, max_val, name, item)
        if self.k <= 0:
            self._all.append(entry)
            return
        if len(self._heap) < self.k:
            heapq.heappush(self._heap, entry)
        elif entry > self._heap[0]:
            heapq.heapreplace(self._heap, entry)

    def sorted_items(self) -> List[Dict[str, Any]]:
        src = self._all if self.k <= 0 else self._heap
        return [
            e[3]
            for e in sorted(src, key=lambda x: (-x[0], -x[1], x[2]))
        ]


class _SampleCollector:
    """Bounded deterministic collector (keeps sorted smallest-by-key up to `limit`, or all if `limit <= 0`)."""

    def __init__(self, limit: int) -> None:
        self.limit = limit
        self.total = 0
        self.items: List[Dict[str, Any]] = []

    def add(self, item: Dict[str, Any], sort_key: str) -> None:
        self.total += 1
        if self.limit <= 0:
            self.items.append(item)
            return
        if len(self.items) < self.limit:
            self.items.append(item)
            if len(self.items) == self.limit:
                self.items.sort(key=lambda x: x["_sk"])
        else:
            if sort_key < self.items[-1]["_sk"]:
                self.items.pop()
                self.items.append(item)
                self.items.sort(key=lambda x: x["_sk"])

    def finish(self) -> List[Dict[str, Any]]:
        self.items.sort(key=lambda x: x["_sk"])
        for it in self.items:
            it.pop("_sk", None)
        return self.items


def _pair_entry(
    a_name: str,
    ra: DeclRec,
    b_name: str,
    rb: DeclRec,
    tier: str,
) -> Dict[str, Any]:
    dom_a = ra.dom_subtree
    dom_b = rb.dom_subtree
    dom_delta = (dom_b - dom_a) if (dom_a is not None and dom_b is not None) else None
    return {
        "_sk": f"{b_name}\0{a_name}",
        "name": b_name,
        "a_name": a_name,
        "tier": tier,
        "kind_a": ra.kind,
        "kind_b": rb.kind,
        "type_nodes_a": ra.type_nodes,
        "type_nodes_b": rb.type_nodes,
        "type_nodes_delta": rb.type_nodes - ra.type_nodes,
        "value_nodes_a": ra.value_nodes,
        "value_nodes_b": rb.value_nodes,
        "value_nodes_delta": rb.value_nodes - ra.value_nodes,
        "flags_a": ra.flags,
        "flags_b": rb.flags,
        "live_a": ra.live_mask != 0,
        "live_b": rb.live_mask != 0,
        "sighash_a": ra.sighash,
        "sighash_b": rb.sighash,
        "sighash_anon_a": ra.sighash_anon,
        "sighash_anon_b": rb.sighash_anon,
        "dom_subtree_a": dom_a,
        "dom_subtree_b": dom_b,
        "dom_subtree_delta": dom_delta,
    }


def _single_entry(name: str, r: DeclRec, side: str) -> Dict[str, Any]:
    return {
        "_sk": name,
        "name": name,
        "side": side,
        "kind": r.kind,
        "type_nodes": r.type_nodes,
        "value_nodes": r.value_nodes,
        "flags": r.flags,
        "flag_names": decode_flags(r.flags),
        "live_mask": r.live_mask,
        "live": r.live_mask != 0,
        "attrs": r.attrs,
        "sighash": r.sighash,
        "sighash_anon": r.sighash_anon,
        "dom_subtree": r.dom_subtree,
    }


def _load_annot_pack(annot_path: str):
    import annot as _annot  # sibling module

    if os.path.isdir(annot_path):
        pack, issues = _annot.PackStore(annot_path).load()
        errs = _annot.errors_of(issues)
        if errs:
            raise _annot.PackError(errs)
        return pack, _annot
    if os.path.isfile(annot_path):
        return _annot.load(annot_path), _annot
    raise FileNotFoundError(f"Annotation path not found: {annot_path}")


def _build_graph_index_ro(b_path: str, pack: Any, _annot: Any):
    """Build `annot.GraphIndex` from B strictly read-only (`consts` if present, else `decls`)."""
    conn = connect_ro(b_path)
    try:
        tables = _get_tables(conn)
        table = "consts" if "consts" in tables else "decls"
        cols = {row[1] for row in conn.execute(f"PRAGMA table_info({table})")}
        sh_col = "sighash" if "sighash" in cols else "NULL"
        sha_col = "sighash_anon" if "sighash_anon" in cols else "NULL"
        want_n = sorted({k[2] for k in pack.annots if k[1] == "decl"})
        want_h = sorted({h for r in pack.annots.values() for h in _annot.record_hashes(r)})
        seen: Dict[str, Tuple[Any, ...]] = {}
        for col, vals in (("name", want_n), (sh_col, want_h), (sha_col, want_h)):
            if col == "NULL" or not vals:
                continue
            for i in range(0, len(vals), 500):
                part = vals[i : i + 500]
                qs = ",".join("?" * len(part))
                sql = f"SELECT name, {sh_col}, {sha_col} FROM {table} WHERE {col} IN ({qs})"
                for row in conn.execute(sql, part):
                    seen[row[0]] = row
        return _annot.GraphIndex(seen.values(), label=_rel_label(b_path) or b_path, restrict_to=pack)
    finally:
        conn.close()


def _preview_annotations(
    annot_dir: str,
    b_path: str,
    flt: Optional[Callable[[str], bool]],
    top: int,
) -> Dict[str, Any]:
    pack, _annot = _load_annot_pack(annot_dir)
    graph_b = _build_graph_index_ro(b_path, pack, _annot)
    rep = _annot.reanchor(pack, graph_b)

    buckets: Dict[str, List[Dict[str, Any]]] = {
        "exact": [],
        "moved_renamed": [],
        "needs_review": [],
        "orphaned": [],
        "unchecked": [],
    }
    counts: Dict[str, int] = {k: 0 for k in buckets}

    for e in rep["entries"]:
        if flt is not None and not _matches_pair(flt, e.get("name"), e.get("resolved_name")):
            continue
        st = e["status"]
        reason = e.get("reason")
        if st == _annot.STATUS_EXACT:
            bucket = "exact"
        elif st == _annot.STATUS_HASH_ONLY and e.get("unique"):
            bucket = "moved_renamed"
        elif st == _annot.STATUS_ORPHAN:
            bucket = "orphaned"
        elif st == _annot.STATUS_UNCHECKED or (st == _annot.STATUS_NAME_ONLY and reason == "non_decl_target"):
            bucket = "unchecked"
        else:
            bucket = "needs_review"

        counts[bucket] += 1
        item: Dict[str, Any] = {
            "id": e["id"],
            "layer": e["layer"],
            "target": e["target"],
            "name": e["name"],
            "sighash": e.get("sighash"),
            "annot_status": st,
        }
        if reason:
            item["reason"] = reason
        if "resolved_name" in e:
            item["resolved_name"] = e["resolved_name"]
        if "via" in e:
            item["via"] = e["via"]
            item["via_primary"] = e.get("via_primary")
        if "candidate_count" in e:
            item["candidate_count"] = e["candidate_count"]
            item["candidates"] = e.get("candidates", [])[:5]
        buckets[bucket].append(item)

    cap = top if top > 0 else None
    samples = {k: (v[:cap] if cap is not None else v) for k, v in buckets.items()}
    return {
        "annot_path": _rel_label(annot_dir),
        "total_records": sum(counts.values()),
        "decl_records": sum(counts[k] for k in ("exact", "moved_renamed", "needs_review", "orphaned")),
        "counts": counts,
        "samples": samples,
    }


def run_kdiff(
    a_db: str,
    b_db: str,
    *,
    top: int = 20,
    filter_pattern: Optional[str] = None,
    annot_dir: Optional[str] = None,
) -> Dict[str, Any]:
    """Compute a kernel-exact BinDiff report comparing `a_db` -> `b_db`."""
    t0 = time.perf_counter()
    flt = _compile_filter(filter_pattern)

    # 1. Load DB A
    a_map, roots_a, dom0_a, live_a_bits, stmt_a_bits, n_decls_a = _load_db_a(a_db)

    # 2. Stream DB B and perform Tier 1 (exact name match) inline
    cb = connect_ro(b_db)
    n_decls_b = 0
    unmatched_b: List[Tuple[str, DeclRec]] = []

    tier_counts = {
        "unchanged": 0,
        "proof_changed": 0,
        "type_changed": 0,
        "renamed_k1n": 0,
        "alpha_k1a": 0,
        "ambiguous_k1n_groups": 0,
        "ambiguous_k1n_a_decls": 0,
        "ambiguous_k1n_b_decls": 0,
        "ambiguous_k1a_groups": 0,
        "ambiguous_k1a_a_decls": 0,
        "ambiguous_k1a_b_decls": 0,
        "added": 0,
        "removed": 0,
    }
    filtered_counts = dict(tier_counts)

    sample_proof = _SampleCollector(top)
    sample_type = _SampleCollector(top)
    sample_k1n = _SampleCollector(top)
    sample_k1a = _SampleCollector(top)
    sample_ambig_k1n = _SampleCollector(top)
    sample_ambig_k1a = _SampleCollector(top)
    sample_added = _SampleCollector(top)
    sample_removed = _SampleCollector(top)

    top_dom = _TopK(top)
    top_vn = _TopK(top)
    top_tn = _TopK(top)

    reg_counts: Dict[str, int] = {c: 0 for c in REGRESSION_CATEGORIES}
    reg_items: Dict[str, List[Dict[str, Any]]] = {c: [] for c in REGRESSION_CATEGORIES}
    imp_counts: Dict[str, int] = collections.Counter()
    informational_counts: Dict[str, int] = collections.Counter()

    def record_pair(a_name: str, ra: DeclRec, b_name: str, rb: DeclRec, tier: str) -> None:
        matched_flt = _matches_pair(flt, a_name, b_name)
        regs, imps = _detect_pair_regressions(a_name, ra, b_name, rb, tier)
        if (rb.flags & F_OF_DECIDE) != 0 and rb.live_mask == 0 and (ra.flags & F_OF_DECIDE) == 0:
            if matched_flt:
                informational_counts["new_decide_kernel_dead"] += 1
        if (rb.attrs & ATTR_UNSAFE) != 0 and rb.live_mask != 0 and (
            (ra.attrs & ATTR_UNSAFE) == 0 or ra.live_mask == 0
        ):
            if matched_flt:
                informational_counts["newly_live_unsafe"] += 1

        if matched_flt:
            for cat, item in regs:
                reg_counts[cat] += 1
                reg_items[cat].append(item)
            for cat, _item in imps:
                imp_counts[cat] += 1

            # Track movers
            if ra.dom_subtree is not None or rb.dom_subtree is not None:
                da = ra.dom_subtree or 0
                db = rb.dom_subtree or 0
                if da != db:
                    top_dom.push(
                        abs(db - da),
                        max(da, db),
                        b_name,
                        {
                            "name": b_name,
                            "a_name": a_name,
                            "tier": tier,
                            "dom_subtree_a": ra.dom_subtree,
                            "dom_subtree_b": rb.dom_subtree,
                            "delta": db - da,
                        },
                    )
            if ra.value_nodes != rb.value_nodes:
                top_vn.push(
                    abs(rb.value_nodes - ra.value_nodes),
                    max(ra.value_nodes, rb.value_nodes),
                    b_name,
                    {
                        "name": b_name,
                        "a_name": a_name,
                        "tier": tier,
                        "value_nodes_a": ra.value_nodes,
                        "value_nodes_b": rb.value_nodes,
                        "delta": rb.value_nodes - ra.value_nodes,
                    },
                )
            if ra.type_nodes != rb.type_nodes:
                top_tn.push(
                    abs(rb.type_nodes - ra.type_nodes),
                    max(ra.type_nodes, rb.type_nodes),
                    b_name,
                    {
                        "name": b_name,
                        "a_name": a_name,
                        "tier": tier,
                        "type_nodes_a": ra.type_nodes,
                        "type_nodes_b": rb.type_nodes,
                        "delta": rb.type_nodes - ra.type_nodes,
                    },
                )

    try:
        tables_b = _get_tables(cb)
        if "decls" not in tables_b:
            raise ValueError(f"Invalid kernel.db (missing `decls` table): {b_db}")
        dom_by_id_b, roots_b, dom0_b, _ = _load_dom0_and_roots(cb, tables_b)
        sql_b, _ = _decls_select_sql(cb)

        live_b_bits: Dict[int, int] = collections.Counter()
        stmt_b_bits: Dict[int, int] = collections.Counter()
        root_bits_b = [r["bit"] for r in roots_b if 0 <= r["bit"] < 64]
        intern = sys.intern

        for did, name, kind, tn, vn, fl, lm, sm, at, sh, sha in cb.execute(sql_b):
            n_decls_b += 1
            lm_i = int(lm)
            sm_i = int(sm)
            for b in root_bits_b:
                bit = 1 << b
                if lm_i & bit:
                    live_b_bits[b] += 1
                if sm_i & bit:
                    stmt_b_bits[b] += 1

            rb = DeclRec(
                kind=intern(kind),
                type_nodes=int(tn),
                value_nodes=int(vn),
                flags=int(fl),
                live_mask=lm_i,
                stmt_mask=sm_i,
                attrs=int(at),
                sighash=sh or None,
                sighash_anon=sha or None,
                dom_subtree=dom_by_id_b.get(int(did)),
            )
            ra = a_map.pop(name, None)
            if ra is not None:
                # Tier 1: exact name match
                if ra.sighash is not None and rb.sighash is not None:
                    sig_same = ra.sighash == rb.sighash
                elif ra.sighash is None and rb.sighash is None:
                    sig_same = ra.type_nodes == rb.type_nodes
                else:
                    sig_same = False

                if not sig_same:
                    tier = "type_changed"
                elif ra.value_nodes == rb.value_nodes and ra.kind == rb.kind:
                    tier = "unchanged"
                else:
                    tier = "proof_changed"

                tier_counts[tier] += 1
                matched_flt = flt is None or flt(name)
                if matched_flt:
                    filtered_counts[tier] += 1

                if tier == "unchanged":
                    # Fast path: only check regressions/movers if flags/live/attrs/dom/type_nodes changed
                    if (
                        ra.flags != rb.flags
                        or ra.live_mask != rb.live_mask
                        or ra.attrs != rb.attrs
                        or ra.dom_subtree != rb.dom_subtree
                        or ra.type_nodes != rb.type_nodes
                    ):
                        record_pair(name, ra, name, rb, tier)
                else:
                    record_pair(name, ra, name, rb, tier)
                    if matched_flt:
                        pe = _pair_entry(name, ra, name, rb, tier)
                        if tier == "proof_changed":
                            sample_proof.add(pe, pe["_sk"])
                        else:
                            sample_type.add(pe, pe["_sk"])
            else:
                unmatched_b.append((name, rb))
        del dom_by_id_b
    finally:
        cb.close()

    # 3. Tier 2: exact k1n (sighash) rename/move on remaining unmatched A and B
    unmatched_a = a_map  # Dict[str, DeclRec]
    a_by_k1n: Dict[str, List[str]] = collections.defaultdict(list)
    b_by_k1n: Dict[str, List[int]] = collections.defaultdict(list)
    for name, ra in unmatched_a.items():
        if ra.sighash:
            a_by_k1n[ra.sighash].append(name)
    for idx, (_name, rb) in enumerate(unmatched_b):
        if rb.sighash:
            b_by_k1n[rb.sighash].append(idx)

    resolved_a: Set[str] = set()
    resolved_b: Set[int] = set()

    for k1n in sorted(set(a_by_k1n) & set(b_by_k1n)):
        a_names = sorted(a_by_k1n[k1n])
        b_idxs = b_by_k1n[k1n]
        b_names = sorted(unmatched_b[i][0] for i in b_idxs)
        if len(a_names) == 1 and len(b_idxs) == 1:
            an = a_names[0]
            bi = b_idxs[0]
            bn, rb = unmatched_b[bi]
            ra = unmatched_a[an]
            resolved_a.add(an)
            resolved_b.add(bi)
            tier_counts["renamed_k1n"] += 1
            if _matches_pair(flt, an, bn):
                filtered_counts["renamed_k1n"] += 1
                pe = _pair_entry(an, ra, bn, rb, "renamed_k1n")
                sample_k1n.add(pe, pe["_sk"])
            record_pair(an, ra, bn, rb, "renamed_k1n")
        else:
            # Ambiguous N:M multiplicity -- flag cleanly without guessing
            for an in a_names:
                resolved_a.add(an)
            for bi in b_idxs:
                resolved_b.add(bi)
            tier_counts["ambiguous_k1n_groups"] += 1
            tier_counts["ambiguous_k1n_a_decls"] += len(a_names)
            tier_counts["ambiguous_k1n_b_decls"] += len(b_names)
            matched_flt = _matches_any(flt, a_names) or _matches_any(flt, b_names)
            if matched_flt:
                filtered_counts["ambiguous_k1n_groups"] += 1
                filtered_counts["ambiguous_k1n_a_decls"] += len(a_names)
                filtered_counts["ambiguous_k1n_b_decls"] += len(b_names)
                sample_ambig_k1n.add(
                    {
                        "_sk": f"{k1n}\0{b_names[0]}",
                        "sighash": k1n,
                        "multiplicity": f"{len(a_names)}:{len(b_names)}",
                        "a_names": a_names,
                        "b_names": b_names,
                    },
                    k1n,
                )
            # Check group-level regressions without guessing 1:1 pairing
            _check_ambiguous_group_regressions(
                a_names, unmatched_a, b_idxs, unmatched_b, "ambiguous_k1n", flt, reg_counts, reg_items
            )

    # 4. Tier 3: exact k1a (sighash_anon) alpha/structural match on remaining unmatched
    a_by_k1a: Dict[str, List[str]] = collections.defaultdict(list)
    b_by_k1a: Dict[str, List[int]] = collections.defaultdict(list)
    for name, ra in unmatched_a.items():
        if name not in resolved_a and ra.sighash_anon:
            a_by_k1a[ra.sighash_anon].append(name)
    for idx, (_name, rb) in enumerate(unmatched_b):
        if idx not in resolved_b and rb.sighash_anon:
            b_by_k1a[rb.sighash_anon].append(idx)

    for k1a in sorted(set(a_by_k1a) & set(b_by_k1a)):
        a_names = sorted(a_by_k1a[k1a])
        b_idxs = b_by_k1a[k1a]
        b_names = sorted(unmatched_b[i][0] for i in b_idxs)
        if len(a_names) == 1 and len(b_idxs) == 1:
            an = a_names[0]
            bi = b_idxs[0]
            bn, rb = unmatched_b[bi]
            ra = unmatched_a[an]
            resolved_a.add(an)
            resolved_b.add(bi)
            tier_counts["alpha_k1a"] += 1
            if _matches_pair(flt, an, bn):
                filtered_counts["alpha_k1a"] += 1
                pe = _pair_entry(an, ra, bn, rb, "alpha_k1a")
                sample_k1a.add(pe, pe["_sk"])
            record_pair(an, ra, bn, rb, "alpha_k1a")
        else:
            for an in a_names:
                resolved_a.add(an)
            for bi in b_idxs:
                resolved_b.add(bi)
            tier_counts["ambiguous_k1a_groups"] += 1
            tier_counts["ambiguous_k1a_a_decls"] += len(a_names)
            tier_counts["ambiguous_k1a_b_decls"] += len(b_names)
            matched_flt = _matches_any(flt, a_names) or _matches_any(flt, b_names)
            if matched_flt:
                filtered_counts["ambiguous_k1a_groups"] += 1
                filtered_counts["ambiguous_k1a_a_decls"] += len(a_names)
                filtered_counts["ambiguous_k1a_b_decls"] += len(b_names)
                sample_ambig_k1a.add(
                    {
                        "_sk": f"{k1a}\0{b_names[0]}",
                        "sighash_anon": k1a,
                        "multiplicity": f"{len(a_names)}:{len(b_names)}",
                        "a_names": a_names,
                        "b_names": b_names,
                    },
                    k1a,
                )
            _check_ambiguous_group_regressions(
                a_names, unmatched_a, b_idxs, unmatched_b, "ambiguous_k1a", flt, reg_counts, reg_items
            )

    # 5. Tier 4: Added (B only) and Removed (A only)
    for name, ra in unmatched_a.items():
        if name in resolved_a:
            continue
        tier_counts["removed"] += 1
        if flt is None or flt(name):
            filtered_counts["removed"] += 1
            se = _single_entry(name, ra, "A")
            sample_removed.add(se, se["_sk"])
            if (ra.flags & F_SORRY) != 0:
                imp_counts["resolved_sorry"] += 1
            if (ra.flags & F_REDUCE_BOOL) != 0:
                imp_counts["resolved_reduce_bool"] += 1
            if (ra.flags & F_REDUCE_NAT) != 0:
                imp_counts["resolved_reduce_nat"] += 1
            if (ra.flags & F_TRUST_COMPILER) != 0:
                imp_counts["resolved_trust_compiler"] += 1
            if ra.kind == "axiom" and name not in STANDARD_AXIOMS:
                imp_counts["removed_custom_axiom"] += 1

    for idx, (name, rb) in enumerate(unmatched_b):
        if idx in resolved_b:
            continue
        tier_counts["added"] += 1
        matched_flt = flt is None or flt(name)
        if matched_flt:
            filtered_counts["added"] += 1
            se = _single_entry(name, rb, "B")
            sample_added.add(se, se["_sk"])
            regs, _ = _detect_pair_regressions(None, None, name, rb, "added")
            for cat, item in regs:
                reg_counts[cat] += 1
                reg_items[cat].append(item)
            if (rb.flags & F_OF_DECIDE) != 0 and rb.live_mask == 0:
                informational_counts["new_decide_kernel_dead"] += 1
            if (rb.attrs & ATTR_UNSAFE) != 0 and rb.live_mask != 0:
                informational_counts["newly_live_unsafe"] += 1

    # 6. Root cone comparisons (joined by root name, never by numeric id)
    ra_by_name = {r["name"]: r for r in roots_a}
    rb_by_name = {r["name"]: r for r in roots_b}
    root_cones: List[Dict[str, Any]] = []
    for rname in sorted(set(ra_by_name) | set(rb_by_name)):
        if flt is not None and not flt(rname):
            continue
        r_a = ra_by_name.get(rname)
        r_b = rb_by_name.get(rname)
        live_a = live_a_bits.get(r_a["bit"], 0) if r_a else None
        live_b = live_b_bits.get(r_b["bit"], 0) if r_b else None
        stmt_a = stmt_a_bits.get(r_a["bit"], 0) if r_a else None
        stmt_b = stmt_b_bits.get(r_b["bit"], 0) if r_b else None
        dom_a = r_a["dom_subtree"] if r_a else None
        dom_b = r_b["dom_subtree"] if r_b else None
        root_cones.append(
            {
                "name": rname,
                "status": "both" if (r_a and r_b) else ("added" if r_b else "removed"),
                "group_a": r_a["group"] if r_a else None,
                "group_b": r_b["group"] if r_b else None,
                "live_a": live_a,
                "live_b": live_b,
                "live_delta": (live_b - live_a) if (live_a is not None and live_b is not None) else None,
                "stmt_a": stmt_a,
                "stmt_b": stmt_b,
                "stmt_delta": (stmt_b - stmt_a) if (stmt_a is not None and stmt_b is not None) else None,
                "dom_subtree_a": dom_a,
                "dom_subtree_b": dom_b,
                "dom_subtree_delta": (dom_b - dom_a) if (dom_a is not None and dom_b is not None) else None,
                "dom_tree_nodes_a": r_a["dom_tree_nodes"] if r_a else None,
                "dom_tree_nodes_b": r_b["dom_tree_nodes"] if r_b else None,
            }
        )

    # Sort regression items deterministically
    for cat in REGRESSION_CATEGORIES:
        reg_items[cat].sort(key=lambda x: x["name"])

    total_regressions = sum(reg_counts.values())

    annot_preview = (
        _preview_annotations(annot_dir, b_db, flt, top) if annot_dir else None
    )

    elapsed_s = round(time.perf_counter() - t0, 3)
    summary: Dict[str, Any] = {
        "decls_a": n_decls_a,
        "decls_b": n_decls_b,
        "decls_delta": n_decls_b - n_decls_a,
        **tier_counts,
        "dom_tree0_nodes_a": dom0_a,
        "dom_tree0_nodes_b": dom0_b,
        "dom_tree0_nodes_delta": (dom0_b - dom0_a) if (dom0_a is not None and dom0_b is not None) else None,
        "regression_count": total_regressions,
        "has_regression": total_regressions > 0,
    }

    report: Dict[str, Any] = {
        "schema_version": SCHEMA_VERSION,
        "inputs": {
            "a": _rel_label(a_db),
            "b": _rel_label(b_db),
            "filter": filter_pattern,
            "top": top,
        },
        "summary": summary,
        "regressions": {
            "total": total_regressions,
            "has_regression": total_regressions > 0,
            "counts": reg_counts,
            "items": reg_items,
            "informational": dict(sorted(informational_counts.items())),
        },
        "improvements": dict(sorted(imp_counts.items())),
        "root_cones": root_cones,
        "top_dom_movers": top_dom.sorted_items(),
        "top_value_movers": top_vn.sorted_items(),
        "top_type_movers": top_tn.sorted_items(),
        "tiers": {
            "proof_changed": sample_proof.finish(),
            "type_changed": sample_type.finish(),
            "renamed_k1n": sample_k1n.finish(),
            "alpha_k1a": sample_k1a.finish(),
            "ambiguous_k1n": sample_ambig_k1n.finish(),
            "ambiguous_k1a": sample_ambig_k1a.finish(),
            "added": sample_added.finish(),
            "removed": sample_removed.finish(),
        },
        "annot_preview": annot_preview,
        "timing_s": elapsed_s,
    }
    if filter_pattern:
        report["filtered_summary"] = filtered_counts
    return report


def _check_ambiguous_group_regressions(
    a_names: Sequence[str],
    unmatched_a: Dict[str, DeclRec],
    b_idxs: Sequence[int],
    unmatched_b: Sequence[Tuple[str, DeclRec]],
    tier: str,
    flt: Optional[Callable[[str], bool]],
    reg_counts: Dict[str, int],
    reg_items: Dict[str, List[Dict[str, Any]]],
) -> None:
    """Detect newly introduced TCB hazards in N:M ambiguous collision groups without guessing 1:1."""
    any_a_sorry = any((unmatched_a[an].flags & F_SORRY) != 0 for an in a_names)
    any_a_rb = any((unmatched_a[an].flags & F_REDUCE_BOOL) != 0 for an in a_names)
    any_a_rn = any((unmatched_a[an].flags & F_REDUCE_NAT) != 0 for an in a_names)
    any_a_tc = any((unmatched_a[an].flags & F_TRUST_COMPILER) != 0 for an in a_names)
    any_a_cax = any(unmatched_a[an].kind == "axiom" and an not in STANDARD_AXIOMS for an in a_names)
    any_a_ldk = any((unmatched_a[an].flags & F_OF_DECIDE) != 0 and unmatched_a[an].live_mask != 0 for an in a_names)

    for bi in b_idxs:
        bn, rb = unmatched_b[bi]
        if flt is not None and not flt(bn):
            continue
        checks = [
            ("new_sorry", (rb.flags & F_SORRY) != 0 and not any_a_sorry, "sorryAx in ambiguous group"),
            ("new_reduce_bool", (rb.flags & F_REDUCE_BOOL) != 0 and not any_a_rb, "ofReduceBool in ambiguous group"),
            ("new_reduce_nat", (rb.flags & F_REDUCE_NAT) != 0 and not any_a_rn, "ofReduceNat in ambiguous group"),
            ("new_trust_compiler", (rb.flags & F_TRUST_COMPILER) != 0 and not any_a_tc, "trustCompiler in ambiguous group"),
            (
                "new_custom_axiom",
                rb.kind == "axiom" and bn not in STANDARD_AXIOMS and not any_a_cax,
                "custom axiom in ambiguous group",
            ),
            (
                "newly_live_decide_kernel",
                (rb.flags & F_OF_DECIDE) != 0 and rb.live_mask != 0 and not any_a_ldk,
                "live decide_kernel in ambiguous group",
            ),
        ]
        for cat, cond, detail in checks:
            if cond:
                reg_counts[cat] += 1
                reg_items[cat].append(
                    {
                        "category": cat,
                        "name": bn,
                        "a_name": None,
                        "tier": tier,
                        "kind": rb.kind,
                        "flags_a": None,
                        "flags_b": rb.flags,
                        "flag_names_b": decode_flags(rb.flags),
                        "live_mask_a": None,
                        "live_mask_b": rb.live_mask,
                        "live_b": rb.live_mask != 0,
                        "value_nodes_b": rb.value_nodes,
                        "type_nodes_b": rb.type_nodes,
                        "detail": detail,
                    }
                )


def _fmt_delta(v: Optional[int]) -> str:
    if v is None:
        return "n/a"
    return f"{v:+,}"


def format_kdiff_text(rep: Dict[str, Any]) -> str:
    s = rep["summary"]
    inp = rep["inputs"]
    reg = rep["regressions"]
    lines: List[str] = []
    lines.append(f"leanre kdiff ({rep['schema_version']}): {inp['a']} -> {inp['b']}  [{rep['timing_s']:.2f}s]")
    if inp.get("filter"):
        lines.append(f"Filter: {inp['filter']} (top={inp['top']})")
    lines.append(
        f"Declarations: A={s['decls_a']:,}  B={s['decls_b']:,}  delta={s['decls_delta']:+,}"
    )
    if s["dom_tree0_nodes_a"] is not None or s["dom_tree0_nodes_b"] is not None:
        lines.append(
            f"dom(tree_id=0) nodes: A={s['dom_tree0_nodes_a'] or 0:,}  "
            f"B={s['dom_tree0_nodes_b'] or 0:,}  delta={_fmt_delta(s['dom_tree0_nodes_delta'])}"
        )
    lines.append("")
    lines.append("Alignment tiers:")
    lines.append(f"  unchanged      : {s['unchanged']:,}")
    lines.append(f"  proof_changed  : {s['proof_changed']:,}")
    lines.append(f"  type_changed   : {s['type_changed']:,}")
    lines.append(f"  renamed_k1n    : {s['renamed_k1n']:,}")
    lines.append(f"  alpha_k1a      : {s['alpha_k1a']:,}")
    lines.append(
        f"  ambiguous_k1n  : {s['ambiguous_k1n_groups']:,} groups "
        f"(A={s['ambiguous_k1n_a_decls']:,}, B={s['ambiguous_k1n_b_decls']:,})"
    )
    lines.append(
        f"  ambiguous_k1a  : {s['ambiguous_k1a_groups']:,} groups "
        f"(A={s['ambiguous_k1a_a_decls']:,}, B={s['ambiguous_k1a_b_decls']:,})"
    )
    lines.append(f"  added          : {s['added']:,}")
    lines.append(f"  removed        : {s['removed']:,}")

    if "filtered_summary" in rep:
        fs = rep["filtered_summary"]
        lines.append("")
        lines.append(
            "Filtered matches: "
            + ", ".join(
                f"{k}={fs[k]:,}"
                for k in (
                    "unchanged",
                    "proof_changed",
                    "type_changed",
                    "renamed_k1n",
                    "alpha_k1a",
                    "ambiguous_k1n_groups",
                    "ambiguous_k1a_groups",
                    "added",
                    "removed",
                )
            )
        )

    lines.append("")
    if reg["has_regression"]:
        lines.append(f"!!! SECURITY / TCB REGRESSIONS DETECTED: {reg['total']} !!!")
        for cat in REGRESSION_CATEGORIES:
            cnt = reg["counts"][cat]
            if cnt == 0:
                continue
            lines.append(f"  [{cat}] {cnt}:")
            for item in reg["items"][cat][:20]:
                live_tag = "LIVE" if item["live_b"] else "dead"
                lines.append(f"    - {item['name']} ({item['tier']}, {live_tag}): {item['detail']}")
            if cnt > 20:
                lines.append(f"    ... +{cnt - 20} more")
    else:
        lines.append("Security / TCB regressions: NONE (0)")

    if rep["improvements"]:
        lines.append("TCB improvements: " + ", ".join(f"{k}={v}" for k, v in rep["improvements"].items()))

    if rep["root_cones"]:
        lines.append("")
        lines.append("Root cones:")
        lines.append(f"  {'Root':<44} {'Live A':>10} {'Live B':>10} {'Delta':>9} {'DomSub A':>10} {'DomSub B':>10} {'Delta':>9}")
        for rc in rep["root_cones"]:
            la = f"{rc['live_a']:,}" if rc["live_a"] is not None else "-"
            lb = f"{rc['live_b']:,}" if rc["live_b"] is not None else "-"
            da = f"{rc['dom_subtree_a']:,}" if rc["dom_subtree_a"] is not None else "-"
            db = f"{rc['dom_subtree_b']:,}" if rc["dom_subtree_b"] is not None else "-"
            lines.append(
                f"  {rc['name']:<44} {la:>10} {lb:>10} {_fmt_delta(rc['live_delta']):>9} "
                f"{da:>10} {db:>10} {_fmt_delta(rc['dom_subtree_delta']):>9}"
            )

    for title, key, a_k, b_k in (
        ("Top dom(tree_id=0) subtree_size movers", "top_dom_movers", "dom_subtree_a", "dom_subtree_b"),
        ("Top value_nodes movers", "top_value_movers", "value_nodes_a", "value_nodes_b"),
        ("Top type_nodes movers", "top_type_movers", "type_nodes_a", "type_nodes_b"),
    ):
        items = rep[key]
        if items:
            lines.append("")
            lines.append(f"{title} ({len(items)}):")
            for m in items:
                va = m[a_k] if m[a_k] is not None else 0
                vb = m[b_k] if m[b_k] is not None else 0
                rename_note = f" <- {m['a_name']}" if m["a_name"] != m["name"] else ""
                lines.append(f"  {m['delta']:>+10,}  ({va:,} -> {vb:,})  {m['name']}{rename_note} [{m['tier']}]")

    tiers = rep["tiers"]
    for label, tk in (
        ("Type changes", "type_changed"),
        ("Proof changes", "proof_changed"),
        ("k1n renames", "renamed_k1n"),
        ("k1a alpha matches", "alpha_k1a"),
        ("Added", "added"),
        ("Removed", "removed"),
    ):
        arr = tiers[tk]
        if arr:
            lines.append("")
            lines.append(f"{label} (showing {len(arr)}):")
            for item in arr:
                if tk in ("added", "removed"):
                    lines.append(f"  [{item['kind']}] {item['name']} (vn={item['value_nodes']:,}, tn={item['type_nodes']:,})")
                elif tk in ("renamed_k1n", "alpha_k1a"):
                    lines.append(f"  {item['a_name']} -> {item['name']} (vn {item['value_nodes_a']:,}->{item['value_nodes_b']:,})")
                else:
                    lines.append(
                        f"  {item['name']} (vn {item['value_nodes_a']:,}->{item['value_nodes_b']:,}, "
                        f"tn {item['type_nodes_a']:,}->{item['type_nodes_b']:,})"
                    )

    for label, tk, hk in (
        ("Ambiguous k1n collisions", "ambiguous_k1n", "sighash"),
        ("Ambiguous k1a collisions", "ambiguous_k1a", "sighash_anon"),
    ):
        arr = tiers[tk]
        if arr:
            lines.append("")
            lines.append(f"{label} (showing {len(arr)}):")
            for item in arr:
                lines.append(
                    f"  {item[hk]} [{item['multiplicity']}] "
                    f"A={item['a_names'][:3]} B={item['b_names'][:3]}"
                )

    if rep["annot_preview"] is not None:
        ap = rep["annot_preview"]
        c = ap["counts"]
        lines.append("")
        lines.append(
            f"Annotation reanchor preview ({ap['annot_path']}, {ap['total_records']} records): "
            f"exact={c['exact']}, moved/renamed={c['moved_renamed']}, "
            f"needs-review={c['needs_review']}, orphaned={c['orphaned']}, unchecked={c['unchecked']}"
        )
        for bk, lbl in (("moved_renamed", "Moved/Renamed"), ("needs_review", "Needs review"), ("orphaned", "Orphaned")):
            for it in ap["samples"][bk][:10]:
                extra = f" -> {it['resolved_name']}" if "resolved_name" in it else (f" ({it.get('reason')})" if it.get("reason") else "")
                lines.append(f"  [{lbl}] {it['layer']} {it['name']}{extra}")

    return "\n".join(lines)


def format_kdiff_markdown(rep: Dict[str, Any]) -> str:
    s = rep["summary"]
    inp = rep["inputs"]
    reg = rep["regressions"]
    lines: List[str] = []
    lines.append(f"# Kernel BinDiff (`{rep['schema_version']}`)")
    lines.append("")
    lines.append(f"- **A:** `{inp['a']}` ({s['decls_a']:,} decls)")
    lines.append(f"- **B:** `{inp['b']}` ({s['decls_b']:,} decls, delta `{s['decls_delta']:+,}`)")
    if inp.get("filter"):
        lines.append(f"- **Filter:** `{inp['filter']}`")
    lines.append(f"- **Runtime:** `{rep['timing_s']:.2f}s`")
    lines.append("")
    lines.append("## Alignment Summary")
    lines.append("")
    lines.append("| Tier | Count |")
    lines.append("|---|---:|")
    for k in ("unchanged", "proof_changed", "type_changed", "renamed_k1n", "alpha_k1a", "added", "removed"):
        lines.append(f"| `{k}` | {s[k]:,} |")
    lines.append(
        f"| `ambiguous_k1n` | {s['ambiguous_k1n_groups']:,} groups (A={s['ambiguous_k1n_a_decls']:,}, B={s['ambiguous_k1n_b_decls']:,}) |"
    )
    lines.append(
        f"| `ambiguous_k1a` | {s['ambiguous_k1a_groups']:,} groups (A={s['ambiguous_k1a_a_decls']:,}, B={s['ambiguous_k1a_b_decls']:,}) |"
    )

    lines.append("")
    lines.append("## Security & TCB Regressions")
    lines.append("")
    if reg["has_regression"]:
        lines.append(f"> [!WARNING]\n> **{reg['total']} TCB regression(s) detected.**")
        lines.append("")
        lines.append("| Category | Count | Sample Declarations |")
        lines.append("|---|---:|---|")
        for cat in REGRESSION_CATEGORIES:
            cnt = reg["counts"][cat]
            if cnt:
                sample = ", ".join(f"`{x['name']}`" for x in reg["items"][cat][:5])
                lines.append(f"| `{cat}` | {cnt:,} | {sample} |")
    else:
        lines.append("No security or TCB regressions detected (`0`).")

    if rep["root_cones"]:
        lines.append("")
        lines.append("## Root Cone Swings")
        lines.append("")
        lines.append("| Root | Live A | Live B | Live Delta | `dom` Subtree A | `dom` Subtree B | `dom` Delta |")
        lines.append("|---|---:|---:|---:|---:|---:|---:|")
        for rc in rep["root_cones"]:
            la = f"{rc['live_a']:,}" if rc["live_a"] is not None else "-"
            lb = f"{rc['live_b']:,}" if rc["live_b"] is not None else "-"
            da = f"{rc['dom_subtree_a']:,}" if rc["dom_subtree_a"] is not None else "-"
            db = f"{rc['dom_subtree_b']:,}" if rc["dom_subtree_b"] is not None else "-"
            lines.append(
                f"| `{rc['name']}` | {la} | {lb} | {_fmt_delta(rc['live_delta'])} | "
                f"{da} | {db} | {_fmt_delta(rc['dom_subtree_delta'])} |"
            )

    for title, key, a_k, b_k in (
        ("Top `dom(tree_id=0)` `subtree_size` Movers", "top_dom_movers", "dom_subtree_a", "dom_subtree_b"),
        ("Top `value_nodes` Movers", "top_value_movers", "value_nodes_a", "value_nodes_b"),
        ("Top `type_nodes` Movers", "top_type_movers", "type_nodes_a", "type_nodes_b"),
    ):
        items = rep[key]
        if items:
            lines.append("")
            lines.append(f"## {title}")
            lines.append("")
            lines.append("| Declaration | Tier | A | B | Delta |")
            lines.append("|---|---|---:|---:|---:|")
            for m in items:
                va = m[a_k] if m[a_k] is not None else 0
                vb = m[b_k] if m[b_k] is not None else 0
                nm = f"`{m['name']}`" if m["a_name"] == m["name"] else f"`{m['a_name']}` -> `{m['name']}`"
                lines.append(f"| {nm} | `{m['tier']}` | {va:,} | {vb:,} | {m['delta']:+,} |")

    if rep["annot_preview"] is not None:
        ap = rep["annot_preview"]
        c = ap["counts"]
        lines.append("")
        lines.append("## Annotation Reanchor Preview")
        lines.append("")
        lines.append(f"Pack: `{ap['annot_path']}` (`{ap['total_records']}` records)")
        lines.append("")
        lines.append("| Status | Count |")
        lines.append("|---|---:|")
        lines.append(f"| `exact` | {c['exact']:,} |")
        lines.append(f"| `moved/renamed` | {c['moved_renamed']:,} |")
        lines.append(f"| `needs-review` | {c['needs_review']:,} |")
        lines.append(f"| `orphaned` | {c['orphaned']:,} |")
        lines.append(f"| `unchecked` | {c['unchecked']:,} |")

    return "\n".join(lines)


def format_kdiff(rep: Dict[str, Any], fmt: str) -> str:
    if fmt == "json":
        return json.dumps(rep, indent=2, ensure_ascii=False) + "\n"
    if fmt == "markdown":
        return format_kdiff_markdown(rep) + "\n"
    return format_kdiff_text(rep) + "\n"


def cmd_kdiff(args: argparse.Namespace) -> int:
    try:
        rep = run_kdiff(
            args.a_db,
            args.b_db,
            top=args.top,
            filter_pattern=args.filter,
            annot_dir=args.annot_dir,
        )
    except (FileNotFoundError, ValueError, sqlite3.DatabaseError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1

    rendered = format_kdiff(rep, args.format)

    if args.out and args.out != "-":
        try:
            _safe_write_text(args.out, rendered)
        except ValueError as exc:
            print(f"error: {exc}", file=sys.stderr)
            return 1
    else:
        sys.stdout.write(rendered)

    if args.fail_on_regression and rep["regressions"]["has_regression"]:
        return 2
    return 0


def add_kdiff_parser(sub: Any, dest: str = "kdiff_func") -> argparse.ArgumentParser:
    """Attach `leanre kdiff` subcommand to `leanre/leanre.py` argparse subparsers."""
    p = sub.add_parser(
        "kdiff",
        help="Kernel-exact BinDiff between two kernel.db snapshots (read-only)",
    )
    p.add_argument("a_db", help="Baseline kernel.db snapshot (opened strictly mode=ro)")
    p.add_argument("b_db", help="Target kernel.db snapshot (opened strictly mode=ro)")
    p.add_argument(
        "--format",
        choices=("text", "markdown", "json"),
        default="text",
        help="Output format: text (default), markdown, or json",
    )
    p.add_argument(
        "--out",
        default=None,
        help="Optional output file path (atomic write; refuses symlinks)",
    )
    p.add_argument(
        "--top",
        type=int,
        default=20,
        help="Maximum items per mover/tier list (0 for unlimited; default: 20)",
    )
    p.add_argument(
        "--filter",
        default=None,
        help="Optional regex or substring filter on declaration names",
    )
    p.add_argument(
        "--annot-dir",
        default=None,
        help="Optional annotations directory or .jsonl file for read-only reanchor preview",
    )
    p.add_argument(
        "--fail-on-regression",
        action="store_true",
        help="Exit with code 2 if any security/TCB regression is detected",
    )
    p.set_defaults(**{dest: cmd_kdiff})
    return p


register_cli = add_kdiff_parser


def main(argv: Optional[Sequence[str]] = None) -> int:
    ap = argparse.ArgumentParser(
        prog="leanre-kdiff",
        description="Kernel-exact BinDiff for Lean 4 kernel.db snapshots",
    )
    sub = ap.add_subparsers(dest="cmd", required=True)
    add_kdiff_parser(sub, dest="kdiff_func")
    argv_list = list(sys.argv[1:] if argv is None else argv)
    if argv_list and argv_list[0] not in ("kdiff", "-h", "--help"):
        argv_list = ["kdiff"] + argv_list
    elif not argv_list:
        argv_list = ["kdiff"]
    args = ap.parse_args(argv_list)
    return int(args.kdiff_func(args))


if __name__ == "__main__":
    sys.exit(main())
