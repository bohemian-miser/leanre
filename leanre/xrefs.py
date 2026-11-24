#!/usr/bin/env python3
"""leanre.xrefs — Canonical LXRF v1 static full-graph binary cross-reference exporter.

Exports complete declaration dependency graphs (forward `depends_on` + reverse `used_by`,
mega-hub split, compact metadata shards, and UTF-16-sorted name index shards) into a
zero-server static directory of gzip-9 `.lxrf` files + `manifest.json`.

Supports two modes sharing the exact same `leanre.xrefs/1` schema:
  - Kernel mode: reads `kernel.db` (+ optional `leanre.db` for source line numbers),
    automatically invoking the compiled C99+OpenMP `xref_fast` engine when available
    with an exact pure-Python fallback.
  - Source mode: reads `leanre.db` (or scans a Lean 4 source directory via `scanner`)
    and exports modules + declarations + import/membership edges in the identical schema.

License: AGPL-3.0-or-later
"""
from __future__ import annotations

import argparse
import bisect
import gzip
import hashlib
import json
import math
import os
import random
import shutil
import sqlite3
import struct
import subprocess
import sys
import tempfile
import time
from typing import Any, Dict, Iterable, List, Optional, Sequence, Tuple

_HERE = os.path.dirname(os.path.abspath(__file__))
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)

SCHEMA = "leanre.xrefs/1"
MAGIC = b"LXRF"
FORMAT_VERSION = 1

DIR_FWD = 0
DIR_REV = 1
DIR_REV_HUB = 2

HUB_SENTINEL = 0xFFFFFFFF

KIND_TYPE = 1
KIND_VALUE = 2
KIND_BOTH = 3

DEFAULT_SHARD_SIZE = 4096
DEFAULT_META_SHARD_SIZE = 16384
DEFAULT_NAME_SHARDS = 256
DEFAULT_HUB_THRESHOLD = 16384

META_COLUMNS = [
    "name",
    "kind_idx",
    "fan_in",
    "fan_out",
    "fan_out_type",
    "fan_out_value",
    "mod_idx",
    "line_no",
    "live_mask",
    "dom_size",
    "type_nodes",
    "value_nodes",
]

NAME_COLUMNS = [
    "name",
    "decl_id",
    "kind_idx",
    "fan_in",
    "fan_out",
    "mod_idx",
    "line_no",
]

DEFAULT_PATHS = {
    "fwd": "fwd/{s}.lxrf",
    "rev": "rev/{s}.lxrf",
    "rev_hub": "rev_hub/{id}.lxrf",
    "meta": "meta/{m}.lxrf",
    "names": "names/{n}.lxrf",
}

DEFAULT_PAD = {
    "fwd": 0,
    "rev": 0,
    "rev_hub": 0,
    "meta": 0,
    "names": 0,
}

_HEADER_STRUCT = struct.Struct("<4sBBHII")


# ---------------------------------------------------------------------------
# UTF-16 ordering (exact match with JS `a < b ? -1 : a > b ? 1 : 0`)
# ---------------------------------------------------------------------------

def utf16_key(s: str) -> bytes:
    """Return big-endian UTF-16 bytes so Python `<` matches JS UTF-16 code-unit `<`."""
    return s.encode("utf-16-be")


def cmp_utf16(a: str, b: str) -> int:
    ka = a.encode("utf-16-be")
    kb = b.encode("utf-16-be")
    if ka < kb:
        return -1
    if ka > kb:
        return 1
    return 0


def _sanitize_tsv_field(s: str) -> str:
    if "\t" in s or "\n" in s or "\r" in s:
        return s.replace("\t", " ").replace("\n", " ").replace("\r", " ")
    return s


# ---------------------------------------------------------------------------
# Gzip helpers (raw gzip-9 bytes for `.lxrf` files)
# ---------------------------------------------------------------------------

def is_gzip(data: bytes) -> bool:
    return len(data) >= 2 and data[0] == 0x1F and data[1] == 0x8B


def gzip_compress_bytes(raw: bytes) -> bytes:
    return gzip.compress(raw, compresslevel=9, mtime=0)


def maybe_gunzip(data: bytes) -> bytes:
    if is_gzip(data):
        return gzip.decompress(data)
    return data


def _safe_write_bytes(path: str, data: bytes) -> int:
    if os.path.islink(path):
        raise ValueError(f"Refusing to write through symlink: {path}")
    parent = os.path.dirname(os.path.abspath(path))
    if parent:
        os.makedirs(parent, exist_ok=True)
    with open(path, "wb") as f:
        f.write(data)
    return len(data)


def _open_ro(path: str) -> sqlite3.Connection:
    real = os.path.realpath(path)
    if not os.path.isfile(real):
        raise FileNotFoundError(f"SQLite database not found: {path}")
    conn = sqlite3.connect(f"file:{real}?mode=ro", uri=True)
    conn.execute("PRAGMA query_only=1")
    return conn


def _table_exists(conn: sqlite3.Connection, name: str) -> bool:
    row = conn.execute(
        "SELECT 1 FROM sqlite_master WHERE type='table' AND name=? LIMIT 1",
        (name,),
    ).fetchone()
    return row is not None


# ---------------------------------------------------------------------------
# LXRF v1 Binary Adjacency Shard Codec (Encoder + Strict Decoder)
# ---------------------------------------------------------------------------

def _append_uleb128(buf: bytearray, v: int) -> None:
    if v < 0:
        raise ValueError(f"Negative LEB128 value: {v}")
    while v >= 0x80:
        buf.append((v & 0x7F) | 0x80)
        v >>= 7
    buf.append(v)


def encode_adj_shard(
    direction: int,
    start_id: int,
    adj_lists: Sequence[Optional[Sequence[Tuple[int, int]]]],
) -> bytes:
    """Encode an LXRF v1 adjacency shard to raw (uncompressed) bytes.

    Args:
        direction: DIR_FWD (0), DIR_REV (1), or DIR_REV_HUB (2).
        start_id: First decl_id in shard (for DIR_REV_HUB, the hub decl_id).
        adj_lists: Sequence of length `count` (must be 1 for DIR_REV_HUB).
            Each entry is a strictly ascending sequence of `(target_id, kind)` pairs
            with `kind in {1, 2, 3}`, OR `None` (only valid when `direction == DIR_REV`)
            to emit the `0xFFFFFFFF` mega-hub sentinel.
    """
    if direction not in (DIR_FWD, DIR_REV, DIR_REV_HUB):
        raise ValueError(f"Invalid LXRF direction: {direction}")
    count = len(adj_lists)
    if direction == DIR_REV_HUB and count != 1:
        raise ValueError(f"DIR_REV_HUB shard must have count==1, got {count}")

    out = bytearray()
    out.extend(_HEADER_STRUCT.pack(MAGIC, FORMAT_VERSION, direction, 0, start_id, count))

    total_edges = 0
    for idx, edges in enumerate(adj_lists):
        if edges is None:
            if direction != DIR_REV:
                raise ValueError("HUB_SENTINEL (None) is only valid in DIR_REV shards")
            out.extend(struct.pack("<I", HUB_SENTINEL))
        else:
            deg = len(edges)
            if deg >= HUB_SENTINEL:
                raise ValueError(f"Degree {deg} collides with HUB_SENTINEL at row {idx}")
            out.extend(struct.pack("<I", deg))
            total_edges += deg

    # Stream 1: unsigned LEB128 target deltas
    for idx, edges in enumerate(adj_lists):
        if not edges:
            continue
        prev = edges[0][0]
        if prev < 0:
            raise ValueError(f"Negative target id {prev} at row {idx}")
        _append_uleb128(out, prev)
        for k in range(1, len(edges)):
            cur = edges[k][0]
            if cur <= prev:
                raise ValueError(
                    f"Targets not strictly ascending at row {idx} (decl {start_id + idx}): {cur} <= {prev}"
                )
            _append_uleb128(out, cur - prev - 1)
            prev = cur

    # Stream 2: 2-bit packed kinds, LSB-first
    kind_bytes = (total_edges + 3) >> 2
    if kind_bytes:
        kbuf = bytearray(kind_bytes)
        e_idx = 0
        for edges in adj_lists:
            if not edges:
                continue
            for _, kd in edges:
                if kd not in (KIND_TYPE, KIND_VALUE, KIND_BOTH):
                    raise ValueError(f"Invalid edge kind {kd} (expected 1, 2, or 3)")
                kbuf[e_idx >> 2] |= (kd & 3) << ((e_idx & 3) * 2)
                e_idx += 1
        out.extend(kbuf)

    return bytes(out)


def decode_adj_shard(data: bytes) -> Dict[str, Any]:
    """Strictly decode an LXRF v1 adjacency shard (gzipped or raw).

    Verifies header fields, degree table, strictly ascending LEB128 deltas,
    valid 2-bit edge kinds (1..3), zero padding bits, and exact end-of-buffer invariant.
    """
    raw = maybe_gunzip(data)
    n_bytes = len(raw)
    if n_bytes < 16:
        raise ValueError(f"LXRF shard too short for 16-byte header: {n_bytes} bytes")

    magic, version, direction, flags, start_id, count = _HEADER_STRUCT.unpack_from(raw, 0)
    if magic != MAGIC:
        raise ValueError(f"Bad LXRF magic: {magic!r}")
    if version != FORMAT_VERSION:
        raise ValueError(f"Unsupported LXRF version: {version}")
    if direction not in (DIR_FWD, DIR_REV, DIR_REV_HUB):
        raise ValueError(f"Invalid LXRF direction: {direction}")
    if flags != 0:
        raise ValueError(f"Unexpected LXRF flags: {flags}")
    if direction == DIR_REV_HUB and count != 1:
        raise ValueError(f"DIR_REV_HUB shard must have count=1, got {count}")

    pos = 16
    deg_end = pos + count * 4
    if deg_end > n_bytes:
        raise ValueError(f"Truncated degree table: need {deg_end}, have {n_bytes}")

    degrees = list(struct.unpack_from(f"<{count}I", raw, pos)) if count else []
    pos = deg_end

    total_edges = 0
    for i, d in enumerate(degrees):
        if d == HUB_SENTINEL:
            if direction != DIR_REV:
                raise ValueError(f"HUB_SENTINEL found in non-rev shard (dir={direction}, row={i})")
        else:
            total_edges += d

    kind_bytes = (total_edges + 3) >> 2
    # Reserve space for kind bytes at the tail so we check bounds before reading deltas
    if pos + kind_bytes > n_bytes:
        raise ValueError(f"Truncated shard body: pos={pos}, kind_bytes={kind_bytes}, len={n_bytes}")

    delta_limit = n_bytes - kind_bytes

    # Decode Stream 1 (deltas)
    targets_per_row: List[Optional[List[int]]] = []
    for i, d in enumerate(degrees):
        if d == HUB_SENTINEL:
            targets_per_row.append(None)
            continue
        if d == 0:
            targets_per_row.append([])
            continue
        row_targets: List[int] = [0] * d
        prev = 0
        for k in range(d):
            val = 0
            shift = 0
            while True:
                if pos >= delta_limit:
                    raise ValueError(f"Truncated LEB128 delta at row {i} edge {k}")
                b = raw[pos]
                pos += 1
                val |= (b & 0x7F) << shift
                if (b & 0x80) == 0:
                    break
                shift += 7
                if shift > 35:
                    raise ValueError(f"Overlong LEB128 varint at row {i} edge {k}")
            if k == 0:
                prev = val
            else:
                prev = prev + val + 1
            row_targets[k] = prev
        targets_per_row.append(row_targets)

    # Exact boundary invariant between Stream 1 and Stream 2
    if pos != delta_limit:
        raise ValueError(
            f"LXRF end-of-buffer invariant failed: deltas ended at {pos}, expected {delta_limit} "
            f"(total len={n_bytes}, kind_bytes={kind_bytes})"
        )

    # Decode Stream 2 (2-bit packed kinds)
    adj: List[Optional[List[Tuple[int, int]]]] = []
    e_idx = 0
    for row_targets in targets_per_row:
        if row_targets is None:
            adj.append(None)
            continue
        row_pairs: List[Tuple[int, int]] = []
        for tgt in row_targets:
            kd = (raw[pos + (e_idx >> 2)] >> ((e_idx & 3) * 2)) & 3
            if kd == 0:
                raise ValueError(f"Invalid edge kind 0 at edge stream index {e_idx}")
            row_pairs.append((tgt, kd))
            e_idx += 1
        adj.append(row_pairs)

    # Verify unused trailing bits in last kind byte are 0
    if total_edges & 3:
        used_bits = (total_edges & 3) * 2
        tail_byte = raw[pos + kind_bytes - 1]
        if (tail_byte >> used_bits) != 0:
            raise ValueError(f"Non-zero padding bits in final kind byte: 0x{tail_byte:02x}")

    pos += kind_bytes
    if pos != n_bytes:
        raise ValueError(f"Trailing bytes after LXRF kind stream: pos={pos}, len={n_bytes}")

    return {
        "version": version,
        "dir": direction,
        "flags": flags,
        "start_id": start_id,
        "count": count,
        "degrees": degrees,
        "adj": adj,
        "total_edges": total_edges,
    }


# ---------------------------------------------------------------------------
# Meta, Name, and Module Shard Codecs
# ---------------------------------------------------------------------------

def encode_meta_shard(rows: Sequence[Tuple[Any, ...]]) -> bytes:
    """Encode meta rows (12 columns per decl) to UTF-8 TSV bytes."""
    lines = []
    for r in rows:
        nm = _sanitize_tsv_field(str(r[0]))
        lines.append(
            f"{nm}\t{r[1]}\t{r[2]}\t{r[3]}\t{r[4]}\t{r[5]}\t{r[6]}\t{r[7]}\t{r[8]}\t{r[9]}\t{r[10]}\t{r[11]}\n"
        )
    return "".join(lines).encode("utf-8")


def decode_meta_shard(data: bytes) -> List[Dict[str, Any]]:
    text = maybe_gunzip(data).decode("utf-8")
    out: List[Dict[str, Any]] = []
    if not text:
        return out
    for line in text.splitlines():
        parts = line.split("\t")
        if len(parts) != 12:
            raise ValueError(f"Expected 12 TSV columns in meta shard, got {len(parts)}: {line[:80]!r}")
        out.append({
            "name": parts[0],
            "kind_idx": int(parts[1]),
            "fan_in": int(parts[2]),
            "fan_out": int(parts[3]),
            "fan_out_type": int(parts[4]),
            "fan_out_value": int(parts[5]),
            "mod_idx": int(parts[6]),
            "line_no": int(parts[7]),
            "live_mask": int(parts[8]),
            "dom_size": int(parts[9]),
            "type_nodes": int(parts[10]),
            "value_nodes": int(parts[11]),
        })
    return out


def encode_name_shard(rows: Sequence[Tuple[Any, ...]]) -> bytes:
    """Encode name index rows (7 columns per decl) to UTF-8 TSV bytes."""
    lines = []
    for r in rows:
        nm = _sanitize_tsv_field(str(r[0]))
        lines.append(f"{nm}\t{r[1]}\t{r[2]}\t{r[3]}\t{r[4]}\t{r[5]}\t{r[6]}\n")
    return "".join(lines).encode("utf-8")


def decode_name_shard(data: bytes) -> List[Dict[str, Any]]:
    text = maybe_gunzip(data).decode("utf-8")
    out: List[Dict[str, Any]] = []
    if not text:
        return out
    for line in text.splitlines():
        parts = line.split("\t")
        if len(parts) != 7:
            raise ValueError(f"Expected 7 TSV columns in name shard, got {len(parts)}: {line[:80]!r}")
        out.append({
            "name": parts[0],
            "decl_id": int(parts[1]),
            "kind_idx": int(parts[2]),
            "fan_in": int(parts[3]),
            "fan_out": int(parts[4]),
            "mod_idx": int(parts[5]),
            "line_no": int(parts[6]),
        })
    return out


def encode_modules(modules: Sequence[str]) -> bytes:
    if not modules:
        return b""
    return ("\n".join(_sanitize_tsv_field(m) for m in modules) + "\n").encode("utf-8")


def decode_modules(data: bytes) -> List[str]:
    text = maybe_gunzip(data).decode("utf-8")
    if not text:
        return []
    return text.splitlines()


# ---------------------------------------------------------------------------
# Path Formatting & Random-Access Reader (`XrefStore`)
# ---------------------------------------------------------------------------

def _fmt_shard_path(manifest: Dict[str, Any], key: str, idx: int) -> str:
    tmpl = manifest["paths"][key]
    pad = int(manifest.get("pad", {}).get(key, 0))
    tok = f"{idx:0{pad}d}" if pad > 0 else str(idx)
    return tmpl.replace("{s}", tok).replace("{id}", tok).replace("{m}", tok).replace("{n}", tok)


class XrefStore:
    """Random-access reader for an exported LXRF v1 directory (mirrors browser logic)."""

    def __init__(self, out_dir: str) -> None:
        self.out_dir = os.path.abspath(out_dir)
        with open(os.path.join(self.out_dir, "manifest.json"), "r", encoding="utf-8") as f:
            self.manifest: Dict[str, Any] = json.load(f)
        if self.manifest.get("schema") != SCHEMA:
            raise ValueError(f"Unexpected manifest schema: {self.manifest.get('schema')}")
        self._modules: Optional[List[str]] = None
        self._fwd_cache: Dict[int, Dict[str, Any]] = {}
        self._rev_cache: Dict[int, Dict[str, Any]] = {}
        self._hub_cache: Dict[int, Dict[str, Any]] = {}
        self._meta_cache: Dict[int, List[Dict[str, Any]]] = {}
        self._name_cache: Dict[int, List[Dict[str, Any]]] = {}
        self._range_last_keys: List[bytes] = [
            utf16_key(r[1]) for r in self.manifest.get("name_ranges", [])
        ]
        self._range_first_keys: List[bytes] = [
            utf16_key(r[0]) for r in self.manifest.get("name_ranges", [])
        ]

    @property
    def modules(self) -> List[str]:
        if self._modules is None:
            mpath = os.path.join(self.out_dir, self.manifest["modules_url"])
            with open(mpath, "rb") as f:
                self._modules = decode_modules(f.read())
        return self._modules

    def _read_file(self, rel: str) -> bytes:
        with open(os.path.join(self.out_dir, rel), "rb") as f:
            return f.read()

    def get_meta(self, decl_id: int) -> Dict[str, Any]:
        if decl_id < 0 or decl_id >= self.manifest["n_decls"]:
            raise IndexError(f"decl_id out of range: {decl_id}")
        msz = self.manifest["meta_shard_size"]
        m = decl_id // msz
        row = decl_id % msz
        if m not in self._meta_cache:
            rel = _fmt_shard_path(self.manifest, "meta", m)
            self._meta_cache[m] = decode_meta_shard(self._read_file(rel))
        rec = dict(self._meta_cache[m][row])
        rec["decl_id"] = decl_id
        klabels = self.manifest["kind_labels"]
        rec["kind"] = klabels[rec["kind_idx"]] if 0 <= rec["kind_idx"] < len(klabels) else ""
        rec["module"] = self.modules[rec["mod_idx"]] if rec["mod_idx"] >= 0 else None
        return rec

    def get_fwd(self, decl_id: int) -> List[Tuple[int, int]]:
        if decl_id < 0 or decl_id >= self.manifest["n_decls"]:
            raise IndexError(f"decl_id out of range: {decl_id}")
        ssz = self.manifest["shard_size"]
        s = decl_id // ssz
        off = decl_id % ssz
        if s not in self._fwd_cache:
            rel = _fmt_shard_path(self.manifest, "fwd", s)
            self._fwd_cache[s] = decode_adj_shard(self._read_file(rel))
        edges = self._fwd_cache[s]["adj"][off]
        assert edges is not None
        return edges

    def get_rev(self, decl_id: int) -> List[Tuple[int, int]]:
        if decl_id < 0 or decl_id >= self.manifest["n_decls"]:
            raise IndexError(f"decl_id out of range: {decl_id}")
        ssz = self.manifest["shard_size"]
        s = decl_id // ssz
        off = decl_id % ssz
        if s not in self._rev_cache:
            rel = _fmt_shard_path(self.manifest, "rev", s)
            self._rev_cache[s] = decode_adj_shard(self._read_file(rel))
        edges = self._rev_cache[s]["adj"][off]
        if edges is None:
            if decl_id not in self._hub_cache:
                rel = _fmt_shard_path(self.manifest, "rev_hub", decl_id)
                self._hub_cache[decl_id] = decode_adj_shard(self._read_file(rel))
            hub_edges = self._hub_cache[decl_id]["adj"][0]
            assert hub_edges is not None
            return hub_edges
        return edges

    def _get_name_shard(self, idx: int) -> List[Dict[str, Any]]:
        if idx not in self._name_cache:
            rel = _fmt_shard_path(self.manifest, "names", idx)
            self._name_cache[idx] = decode_name_shard(self._read_file(rel))
        return self._name_cache[idx]

    def lookup_name(self, name: str) -> Optional[Dict[str, Any]]:
        """Exact `name -> entry` lookup via UTF-16 binary search (1 shard fetch)."""
        n_shards = len(self._range_last_keys)
        if n_shards == 0:
            return None
        q = utf16_key(name)
        s = bisect.bisect_left(self._range_last_keys, q)
        if s >= n_shards or self._range_first_keys[s] > q:
            return None
        rows = self._get_name_shard(s)
        lo, hi = 0, len(rows)
        while lo < hi:
            mid = (lo + hi) >> 1
            mk = utf16_key(rows[mid]["name"])
            if mk < q:
                lo = mid + 1
            else:
                hi = mid
        if lo < len(rows) and rows[lo]["name"] == name:
            return rows[lo]
        return None

    def prefix_search(self, prefix: str, limit: int = 50) -> List[Dict[str, Any]]:
        """UTF-16 prefix search across sorted name shards."""
        n_shards = len(self._range_last_keys)
        if n_shards == 0 or limit <= 0:
            return []
        q = utf16_key(prefix)
        s = bisect.bisect_left(self._range_last_keys, q)
        results: List[Dict[str, Any]] = []
        while s < n_shards and len(results) < limit:
            rows = self._get_name_shard(s)
            lo, hi = 0, len(rows)
            while lo < hi:
                mid = (lo + hi) >> 1
                if utf16_key(rows[mid]["name"]) < q:
                    lo = mid + 1
                else:
                    hi = mid
            while lo < len(rows) and len(results) < limit:
                if rows[lo]["name"].startswith(prefix):
                    results.append(rows[lo])
                    lo += 1
                else:
                    return results
            s += 1
        return results


# ---------------------------------------------------------------------------
# Fast C Engine Discovery & On-Demand Compilation
# ---------------------------------------------------------------------------

def compile_fast_binary(force: bool = False) -> Optional[str]:
    """Locate or compile `leanre/xref_fast.c` into a temporary cache path.

    Never writes ELF binaries into the git worktree.
    """
    env_bin = os.environ.get("LEANRE_XREF_FAST")
    if env_bin and os.path.isfile(env_bin) and os.access(env_bin, os.X_OK):
        return env_bin

    src_path = os.path.join(_HERE, "xref_fast.c")
    if not os.path.isfile(src_path):
        return None

    with open(src_path, "rb") as f:
        src_hash = hashlib.sha256(f.read()).hexdigest()[:12]

    cache_bin = os.path.join(tempfile.gettempdir(), f"leanre_xref_fast_{src_hash}")
    if not force and os.path.isfile(cache_bin) and os.access(cache_bin, os.X_OK):
        return cache_bin

    cc = shutil.which("gcc") or shutil.which("cc")
    if not cc:
        return None

    tmp_bin = f"{cache_bin}.tmp.{os.getpid()}"
    cmd = [
        cc,
        "-O3",
        "-Wall",
        "-Wextra",
        "-Werror",
        "-std=c99",
        "-fopenmp",
        src_path,
        "-lsqlite3",
        "-lz",
        "-o",
        tmp_bin,
    ]
    try:
        res = subprocess.run(cmd, capture_output=True, text=True, check=False)
        if res.returncode != 0:
            if os.path.exists(tmp_bin):
                os.unlink(tmp_bin)
            return None
        os.replace(tmp_bin, cache_bin)
        os.chmod(cache_bin, 0o755)
        return cache_bin
    except OSError:
        if os.path.exists(tmp_bin):
            try:
                os.unlink(tmp_bin)
            except OSError:
                pass
        return None


# ---------------------------------------------------------------------------
# Canonical Pure-Python Exporter (Shared by Kernel Fallback & Source Mode)
# ---------------------------------------------------------------------------

def _auto_name_shards(n_decls: int, name_shards: Optional[int]) -> int:
    if n_decls <= 0:
        return 0
    if name_shards is None or name_shards <= 0:
        return min(DEFAULT_NAME_SHARDS, max(1, (n_decls + 255) // 256))
    return min(int(name_shards), n_decls)


def write_lxrf_dataset(
    out_dir: str,
    *,
    mode: str,
    names: Sequence[str],
    kind_labels: Sequence[str],
    kind_indices: Sequence[int],
    modules: Sequence[str],
    mod_indices: Sequence[int],
    line_nos: Sequence[int],
    live_masks: Sequence[int],
    dom_sizes: Sequence[int],
    type_nodes: Sequence[int],
    value_nodes: Sequence[int],
    fwd_adj: Sequence[Sequence[Tuple[int, int]]],
    shard_size: int = DEFAULT_SHARD_SIZE,
    meta_shard_size: int = DEFAULT_META_SHARD_SIZE,
    name_shards: Optional[int] = None,
    hub_threshold: int = DEFAULT_HUB_THRESHOLD,
) -> Dict[str, Any]:
    """Write a complete LXRF v1 directory from in-memory graph arrays (pure Python)."""
    if mode not in ("kernel", "source"):
        raise ValueError(f"Unsupported mode: {mode}")
    n_decls = len(names)
    if shard_size <= 0 or meta_shard_size <= 0:
        raise ValueError("shard_size and meta_shard_size must be positive")

    out_dir = os.path.abspath(out_dir)
    for sub in ("", "fwd", "rev", "rev_hub", "meta", "names"):
        os.makedirs(os.path.join(out_dir, sub) if sub else out_dir, exist_ok=True)

    # Build exact reverse adjacency (ascending src order automatically!) and exact counts
    rev_adj: List[List[Tuple[int, int]]] = [[] for _ in range(n_decls)]
    fwd_deg = [0] * n_decls
    fwd_type_deg = [0] * n_decls
    fwd_val_deg = [0] * n_decls
    kind_counts = {KIND_TYPE: 0, KIND_VALUE: 0, KIND_BOTH: 0}
    n_edges = 0

    for src, edges in enumerate(fwd_adj):
        fwd_deg[src] = len(edges)
        prev = -1
        for dst, kd in edges:
            if dst <= prev:
                raise ValueError(f"fwd_adj[{src}] not strictly ascending: {dst} <= {prev}")
            if kd not in kind_counts:
                raise ValueError(f"Invalid edge kind {kd} for ({src}, {dst})")
            prev = dst
            rev_adj[dst].append((src, kd))
            if kd & 1:
                fwd_type_deg[src] += 1
            if kd & 2:
                fwd_val_deg[src] += 1
            kind_counts[kd] += 1
            n_edges += 1

    rev_deg = [len(lst) for lst in rev_adj]
    rev_hub_ids = [i for i, d in enumerate(rev_deg) if d >= hub_threshold]

    total_bytes = 0
    file_count = 0
    max_shard_bytes = 0
    max_shard_path = "modules.lxrf"

    def _record(rel: str, raw: bytes) -> None:
        nonlocal total_bytes, file_count, max_shard_bytes, max_shard_path
        gz = gzip_compress_bytes(raw)
        sz = _safe_write_bytes(os.path.join(out_dir, rel), gz)
        total_bytes += sz
        file_count += 1
        if sz > max_shard_bytes:
            max_shard_bytes = sz
            max_shard_path = rel

    # 1. modules.lxrf
    _record("modules.lxrf", encode_modules(modules))

    n_shards = math.ceil(n_decls / shard_size) if n_decls else 0
    n_meta_shards = math.ceil(n_decls / meta_shard_size) if n_decls else 0
    eff_name_shards = _auto_name_shards(n_decls, name_shards)

    # 2. fwd shards
    for s in range(n_shards):
        start_id = s * shard_size
        end_id = min(n_decls, start_id + shard_size)
        raw = encode_adj_shard(DIR_FWD, start_id, fwd_adj[start_id:end_id])
        _record(f"fwd/{s}.lxrf", raw)

    # 3. rev shards (with HUB_SENTINEL for mega-hubs)
    for s in range(n_shards):
        start_id = s * shard_size
        end_id = min(n_decls, start_id + shard_size)
        slice_lists: List[Optional[Sequence[Tuple[int, int]]]] = [
            None if rev_deg[i] >= hub_threshold else rev_adj[i]
            for i in range(start_id, end_id)
        ]
        raw = encode_adj_shard(DIR_REV, start_id, slice_lists)
        _record(f"rev/{s}.lxrf", raw)

    # 4. rev_hub shards
    for hub_id in rev_hub_ids:
        raw = encode_adj_shard(DIR_REV_HUB, hub_id, [rev_adj[hub_id]])
        _record(f"rev_hub/{hub_id}.lxrf", raw)

    # 5. meta shards
    for m in range(n_meta_shards):
        start_id = m * meta_shard_size
        end_id = min(n_decls, start_id + meta_shard_size)
        rows = [
            (
                names[i],
                kind_indices[i],
                rev_deg[i],
                fwd_deg[i],
                fwd_type_deg[i],
                fwd_val_deg[i],
                mod_indices[i],
                line_nos[i],
                live_masks[i],
                dom_sizes[i],
                type_nodes[i],
                value_nodes[i],
            )
            for i in range(start_id, end_id)
        ]
        _record(f"meta/{m}.lxrf", encode_meta_shard(rows))

    # 6. sorted name index shards (exact UTF-16 order matching JS)
    clean_names = [_sanitize_tsv_field(nm) for nm in names]
    sorted_ids = sorted(range(n_decls), key=lambda i: (utf16_key(clean_names[i]), i))
    name_ranges: List[List[Any]] = []
    for n in range(eff_name_shards):
        lo = (n * n_decls) // eff_name_shards
        hi = ((n + 1) * n_decls) // eff_name_shards
        chunk_ids = sorted_ids[lo:hi]
        rows = [
            (
                clean_names[i],
                i,
                kind_indices[i],
                rev_deg[i],
                fwd_deg[i],
                mod_indices[i],
                line_nos[i],
            )
            for i in chunk_ids
        ]
        _record(f"names/{n}.lxrf", encode_name_shard(rows))
        name_ranges.append([clean_names[chunk_ids[0]], clean_names[chunk_ids[-1]], len(chunk_ids)])

    manifest: Dict[str, Any] = {
        "schema": SCHEMA,
        "mode": mode,
        "n_decls": n_decls,
        "n_edges": n_edges,
        "edge_kind_counts": {
            "type": kind_counts[KIND_TYPE],
            "value": kind_counts[KIND_VALUE],
            "both": kind_counts[KIND_BOTH],
        },
        "shard_size": shard_size,
        "n_shards": n_shards,
        "meta_shard_size": meta_shard_size,
        "n_meta_shards": n_meta_shards,
        "name_shards": eff_name_shards,
        "name_order": "utf16",
        "name_ranges": name_ranges,
        "hub_threshold": hub_threshold,
        "rev_hub_ids": rev_hub_ids,
        "kind_labels": list(kind_labels),
        "modules_url": "modules.lxrf",
        "n_modules": len(modules),
        "paths": dict(DEFAULT_PATHS),
        "pad": dict(DEFAULT_PAD),
        "meta_columns": list(META_COLUMNS),
        "name_columns": list(NAME_COLUMNS),
        "stats": {
            "total_bytes": total_bytes,
            "file_count": file_count,
            "max_shard_bytes": max_shard_bytes,
            "max_shard_path": max_shard_path,
        },
    }
    _safe_write_bytes(
        os.path.join(out_dir, "manifest.json"),
        (json.dumps(manifest, ensure_ascii=False, indent=2) + "\n").encode("utf-8"),
    )
    return manifest


# ---------------------------------------------------------------------------
# Kernel Mode Exporter (C Engine + Exact Pure-Python Fallback)
# ---------------------------------------------------------------------------

def export_kernel_python(
    kernel_db: str,
    out_dir: str,
    *,
    leanre_db: Optional[str] = None,
    shard_size: int = DEFAULT_SHARD_SIZE,
    meta_shard_size: int = DEFAULT_META_SHARD_SIZE,
    name_shards: Optional[int] = None,
    hub_threshold: int = DEFAULT_HUB_THRESHOLD,
) -> Dict[str, Any]:
    """Pure-Python LXRF v1 kernel exporter (exact portable reference implementation)."""
    kconn = _open_ro(kernel_db)
    try:
        kind_labels = sorted(
            (r[0] or "") for r in kconn.execute("SELECT DISTINCT kind FROM decls")
        )
        kind_to_idx = {k: i for i, k in enumerate(kind_labels)}

        names: List[str] = []
        kind_indices: List[int] = []
        live_masks: List[int] = []
        type_nodes: List[int] = []
        value_nodes: List[int] = []
        for expected, row in enumerate(
            kconn.execute(
                "SELECT id, name, kind, live_mask, type_nodes, value_nodes FROM decls ORDER BY id"
            )
        ):
            if row[0] != expected:
                raise ValueError(f"decls.id must be contiguous 0..N-1 (got {row[0]}, expected {expected})")
            names.append(_sanitize_tsv_field(row[1] or ""))
            kind_indices.append(kind_to_idx[row[2] or ""])
            live_masks.append(int(row[3]))
            type_nodes.append(int(row[4]))
            value_nodes.append(int(row[5]))

        n_decls = len(names)
        dom_sizes = [0] * n_decls
        if _table_exists(kconn, "dom"):
            for did, sz in kconn.execute("SELECT decl_id, subtree_size FROM dom WHERE tree_id = 0"):
                if 0 <= did < n_decls and sz is not None:
                    dom_sizes[did] = int(sz)

        src_line_map: Dict[int, int] = {}
        if leanre_db:
            lconn = _open_ro(leanre_db)
            try:
                if _table_exists(lconn, "declarations"):
                    for sid, lno in lconn.execute("SELECT id, line_no FROM declarations"):
                        src_line_map[int(sid)] = int(lno)
            finally:
                lconn.close()

        modules: List[str] = []
        mod_indices = [-1] * n_decls
        line_nos = [0] * n_decls
        if _table_exists(kconn, "decl_module"):
            modules = sorted(
                (r[0] for r in kconn.execute(
                    "SELECT DISTINCT module FROM decl_module WHERE module IS NOT NULL AND module != ''"
                )),
                key=lambda s: s.encode("utf-8"),
            )
            mod_to_idx = {m: i for i, m in enumerate(modules)}
            for did, mod, sid in kconn.execute("SELECT decl_id, module, src_decl_id FROM decl_module"):
                if 0 <= did < n_decls:
                    if mod:
                        mod_indices[did] = mod_to_idx[mod]
                    if sid is not None and int(sid) in src_line_map:
                        line_nos[did] = src_line_map[int(sid)]

        fwd_adj: List[List[Tuple[int, int]]] = [[] for _ in range(n_decls)]
        for src, dst, kd in kconn.execute("SELECT src, dst, kind FROM edges ORDER BY src, dst"):
            fwd_adj[src].append((dst, kd))
    finally:
        kconn.close()

    return write_lxrf_dataset(
        out_dir,
        mode="kernel",
        names=names,
        kind_labels=kind_labels,
        kind_indices=kind_indices,
        modules=modules,
        mod_indices=mod_indices,
        line_nos=line_nos,
        live_masks=live_masks,
        dom_sizes=dom_sizes,
        type_nodes=type_nodes,
        value_nodes=value_nodes,
        fwd_adj=fwd_adj,
        shard_size=shard_size,
        meta_shard_size=meta_shard_size,
        name_shards=name_shards,
        hub_threshold=hub_threshold,
    )


def export_kernel(
    kernel_db: str,
    out_dir: str,
    *,
    leanre_db: Optional[str] = None,
    shard_size: int = DEFAULT_SHARD_SIZE,
    meta_shard_size: int = DEFAULT_META_SHARD_SIZE,
    name_shards: Optional[int] = None,
    hub_threshold: int = DEFAULT_HUB_THRESHOLD,
    use_c: bool = True,
    threads: Optional[int] = None,
    verbose: bool = False,
) -> Dict[str, Any]:
    """Export `kernel.db` -> `out_dir/` in LXRF v1 format (C engine with Python fallback)."""
    kdb_real = os.path.realpath(kernel_db)
    if not os.path.isfile(kdb_real):
        raise FileNotFoundError(f"Missing kernel.db: {kernel_db}")
    ldb_real = os.path.realpath(leanre_db) if leanre_db else None
    if ldb_real and not os.path.isfile(ldb_real):
        raise FileNotFoundError(f"Missing leanre.db: {leanre_db}")

    if use_c:
        fast_bin = compile_fast_binary()
        if fast_bin:
            cmd = [
                fast_bin,
                "--kernel-db", kdb_real,
                "--out-dir", os.path.abspath(out_dir),
                "--shard-size", str(shard_size),
                "--meta-shard-size", str(meta_shard_size),
                "--name-shards", str(int(name_shards) if name_shards else 0),
                "--hub-threshold", str(hub_threshold),
            ]
            if ldb_real:
                cmd.extend(["--leanre-db", ldb_real])
            if threads:
                cmd.extend(["--threads", str(threads)])
            if not verbose:
                cmd.append("--quiet")
            res = subprocess.run(cmd, check=False)
            if res.returncode != 0:
                raise RuntimeError(f"xref_fast exited with status {res.returncode}")
            with open(os.path.join(out_dir, "manifest.json"), "r", encoding="utf-8") as f:
                return json.load(f)

    return export_kernel_python(
        kdb_real,
        out_dir,
        leanre_db=ldb_real,
        shard_size=shard_size,
        meta_shard_size=meta_shard_size,
        name_shards=name_shards,
        hub_threshold=hub_threshold,
    )


# ---------------------------------------------------------------------------
# Source Mode Exporter (leanre.db OR directory scan via scanner.py)
# ---------------------------------------------------------------------------

def export_source(
    out_dir: str,
    *,
    leanre_db: Optional[str] = None,
    src_dir: Optional[str] = None,
    shard_size: int = DEFAULT_SHARD_SIZE,
    meta_shard_size: int = DEFAULT_META_SHARD_SIZE,
    name_shards: Optional[int] = None,
    hub_threshold: int = DEFAULT_HUB_THRESHOLD,
    verbose: bool = False,
) -> Dict[str, Any]:
    """Export a source-only Lean 4 repo (`leanre.db` or `src_dir`) in LXRF v1 format.

    Nodes:
      - Every scanned module (`kind = "module"`), IDs `0 .. n_modules - 1`
      - Every scanned declaration (`kind = decl.kind`), IDs `n_modules .. N - 1`
    Edges:
      - Module imports (`module_edges`): `mod_src -> mod_dst` with `kind = 1` (type/import)
      - Declaration membership: `decl_id -> mod_node_id` with `kind = 2` (value/defined-in)
    """
    if not leanre_db and not src_dir:
        raise ValueError("export_source requires either leanre_db or src_dir")

    tmp_ctx = None
    db_path = leanre_db
    if not db_path:
        import scanner as _scanner
        tmp_ctx = tempfile.TemporaryDirectory(prefix="leanre_xref_src_")
        db_path = os.path.join(tmp_ctx.name, "leanre.db")
        _scanner.run_scan(src_dir, db_path, verbose=verbose)

    try:
        conn = _open_ro(db_path)
        try:
            mod_rows = list(
                conn.execute(
                    "SELECT name, lines, decl_count, dom_subtree_size FROM modules ORDER BY name"
                )
            )
            modules = [str(r[0]) for r in mod_rows]
            modules.sort(key=lambda s: s.encode("utf-8"))
            mod_info = {str(r[0]): (int(r[1]), int(r[2]), int(r[3])) for r in mod_rows}
            mod_to_id = {m: i for i, m in enumerate(modules)}

            decl_rows = list(
                conn.execute(
                    "SELECT name, kind, module, line_no FROM declarations "
                    "ORDER BY module, line_no, name, id"
                )
            )

            kind_set = set()
            if modules:
                kind_set.add("module")
            for r in decl_rows:
                kind_set.add(str(r[1] or "decl"))
            kind_labels = sorted(kind_set, key=lambda s: s.encode("utf-8"))
            kind_to_idx = {k: i for i, k in enumerate(kind_labels)}

            names: List[str] = []
            kind_indices: List[int] = []
            mod_indices: List[int] = []
            line_nos: List[int] = []
            live_masks: List[int] = []
            dom_sizes: List[int] = []
            type_nodes: List[int] = []
            value_nodes: List[int] = []

            for idx, m in enumerate(modules):
                lines_cnt, decl_cnt, dom_sz = mod_info[m]
                names.append(_sanitize_tsv_field(m))
                kind_indices.append(kind_to_idx["module"])
                mod_indices.append(idx)
                line_nos.append(1)
                live_masks.append(1 if dom_sz > 0 else 0)
                dom_sizes.append(dom_sz)
                type_nodes.append(lines_cnt)
                value_nodes.append(decl_cnt)

            for nm, kd, mod, lno in decl_rows:
                names.append(_sanitize_tsv_field(str(nm or "")))
                kind_indices.append(kind_to_idx[str(kd or "decl")])
                midx = mod_to_id.get(str(mod), -1) if mod else -1
                mod_indices.append(midx)
                line_nos.append(int(lno or 0))
                live_masks.append(0)
                dom_sizes.append(0)
                type_nodes.append(0)
                value_nodes.append(0)

            n_decls = len(names)
            edge_maps: List[Dict[int, int]] = [{} for _ in range(n_decls)]

            # Module import edges -> kind = 1 (type/import)
            if _table_exists(conn, "module_edges"):
                for src_m, dst_m in conn.execute("SELECT src, dst FROM module_edges"):
                    sid = mod_to_id.get(str(src_m))
                    did = mod_to_id.get(str(dst_m))
                    if sid is not None and did is not None and sid != did:
                        edge_maps[sid][did] = edge_maps[sid].get(did, 0) | KIND_TYPE

            # Declaration -> containing module edges -> kind = 2 (value/defined-in)
            n_mods = len(modules)
            for row_i in range(len(decl_rows)):
                did = n_mods + row_i
                midx = mod_indices[did]
                if midx >= 0 and did != midx:
                    edge_maps[did][midx] = edge_maps[did].get(midx, 0) | KIND_VALUE

            fwd_adj = [sorted(em.items()) for em in edge_maps]
        finally:
            conn.close()
    finally:
        if tmp_ctx is not None:
            tmp_ctx.cleanup()

    return write_lxrf_dataset(
        out_dir,
        mode="source",
        names=names,
        kind_labels=kind_labels,
        kind_indices=kind_indices,
        modules=modules,
        mod_indices=mod_indices,
        line_nos=line_nos,
        live_masks=live_masks,
        dom_sizes=dom_sizes,
        type_nodes=type_nodes,
        value_nodes=value_nodes,
        fwd_adj=fwd_adj,
        shard_size=shard_size,
        meta_shard_size=meta_shard_size,
        name_shards=name_shards,
        hub_threshold=hub_threshold,
    )


# ---------------------------------------------------------------------------
# Full Structural & Round-Trip Verifier
# ---------------------------------------------------------------------------

def verify_xrefs(
    out_dir: str,
    *,
    kernel_db: Optional[str] = None,
    leanre_db: Optional[str] = None,
    sample_decls: int = 500,
    sample_names: int = 1000,
    seed: int = 42,
    max_shard_mb: float = 5.0,
) -> Dict[str, Any]:
    """Exhaustively verify an exported LXRF v1 directory (+ optional DB round-trip)."""
    t0 = time.monotonic()
    store = XrefStore(out_dir)
    mf = store.manifest
    n_decls = int(mf["n_decls"])
    n_edges = int(mf["n_edges"])
    shard_size = int(mf["shard_size"])
    meta_shard_size = int(mf["meta_shard_size"])
    hub_threshold = int(mf["hub_threshold"])
    max_allowed_bytes = int(max_shard_mb * 1024 * 1024)

    total_disk_bytes = 0
    max_seen_bytes = 0
    max_seen_path = ""
    lxrf_files = 0

    def _read_checked_lxrf(rel: str) -> bytes:
        nonlocal total_disk_bytes, max_seen_bytes, max_seen_path, lxrf_files
        full = os.path.join(out_dir, rel)
        with open(full, "rb") as f:
            raw_gz = f.read()
        if not is_gzip(raw_gz):
            raise AssertionError(f"{rel} does not start with gzip magic 0x1f 0x8b")
        sz = len(raw_gz)
        if sz > max_allowed_bytes:
            raise AssertionError(f"{rel} exceeds max_shard_mb ({sz} > {max_allowed_bytes})")
        total_disk_bytes += sz
        lxrf_files += 1
        if sz > max_seen_bytes:
            max_seen_bytes = sz
            max_seen_path = rel
        return raw_gz

    # 1. Verify modules.lxrf
    mods = decode_modules(_read_checked_lxrf(mf["modules_url"]))
    if len(mods) != int(mf["n_modules"]):
        raise AssertionError(f"n_modules mismatch: {len(mods)} vs {mf['n_modules']}")

    # 2. Verify every fwd shard
    fwd_total = 0
    fwd_kind_counts = {1: 0, 2: 0, 3: 0}
    fwd_deg = [0] * n_decls
    n_shards = int(mf["n_shards"])
    for s in range(n_shards):
        rel = _fmt_shard_path(mf, "fwd", s)
        dec = decode_adj_shard(_read_checked_lxrf(rel))
        exp_start = s * shard_size
        exp_cnt = min(shard_size, n_decls - exp_start)
        if dec["dir"] != DIR_FWD or dec["start_id"] != exp_start or dec["count"] != exp_cnt:
            raise AssertionError(f"Header mismatch in {rel}")
        for i, edges in enumerate(dec["adj"]):
            assert edges is not None
            fwd_deg[exp_start + i] = len(edges)
            for tgt, kd in edges:
                if tgt >= n_decls:
                    raise AssertionError(f"Out-of-range fwd target {tgt} in {rel}")
                fwd_kind_counts[kd] += 1
            fwd_total += len(edges)

    # 3. Verify every rev shard + rev_hub shard
    rev_total = 0
    rev_kind_counts = {1: 0, 2: 0, 3: 0}
    rev_deg = [0] * n_decls
    seen_hubs: List[int] = []
    for s in range(n_shards):
        rel = _fmt_shard_path(mf, "rev", s)
        dec = decode_adj_shard(_read_checked_lxrf(rel))
        exp_start = s * shard_size
        exp_cnt = min(shard_size, n_decls - exp_start)
        if dec["dir"] != DIR_REV or dec["start_id"] != exp_start or dec["count"] != exp_cnt:
            raise AssertionError(f"Header mismatch in {rel}")
        for i, edges in enumerate(dec["adj"]):
            did = exp_start + i
            if edges is None:
                seen_hubs.append(did)
            else:
                if len(edges) >= hub_threshold:
                    raise AssertionError(f"Non-split hub decl {did} (deg={len(edges)}) in {rel}")
                rev_deg[did] = len(edges)
                for src, kd in edges:
                    if src >= n_decls:
                        raise AssertionError(f"Out-of-range rev src {src} in {rel}")
                    rev_kind_counts[kd] += 1
                rev_total += len(edges)

    if seen_hubs != list(mf["rev_hub_ids"]):
        raise AssertionError(
            f"rev_hub_ids mismatch: saw {len(seen_hubs)} sentinels vs {len(mf['rev_hub_ids'])} in manifest"
        )

    for hub_id in seen_hubs:
        rel = _fmt_shard_path(mf, "rev_hub", hub_id)
        dec = decode_adj_shard(_read_checked_lxrf(rel))
        if dec["dir"] != DIR_REV_HUB or dec["start_id"] != hub_id or dec["count"] != 1:
            raise AssertionError(f"Header mismatch in {rel}")
        edges = dec["adj"][0]
        assert edges is not None
        if len(edges) < hub_threshold:
            raise AssertionError(f"Hub {hub_id} has deg {len(edges)} < threshold {hub_threshold}")
        rev_deg[hub_id] = len(edges)
        for src, kd in edges:
            if src >= n_decls:
                raise AssertionError(f"Out-of-range rev_hub src {src} in {rel}")
            rev_kind_counts[kd] += 1
        rev_total += len(edges)

    if fwd_total != n_edges or rev_total != n_edges:
        raise AssertionError(f"Edge total mismatch: fwd={fwd_total}, rev={rev_total}, manifest={n_edges}")
    exp_kc = {
        1: int(mf["edge_kind_counts"]["type"]),
        2: int(mf["edge_kind_counts"]["value"]),
        3: int(mf["edge_kind_counts"]["both"]),
    }
    if fwd_kind_counts != exp_kc or rev_kind_counts != exp_kc:
        raise AssertionError(
            f"Edge kind count mismatch: fwd={fwd_kind_counts}, rev={rev_kind_counts}, manifest={exp_kc}"
        )

    # 4. Verify every meta shard
    meta_rows_seen = 0
    for m in range(int(mf["n_meta_shards"])):
        rel = _fmt_shard_path(mf, "meta", m)
        rows = decode_meta_shard(_read_checked_lxrf(rel))
        exp_start = m * meta_shard_size
        exp_cnt = min(meta_shard_size, n_decls - exp_start)
        if len(rows) != exp_cnt:
            raise AssertionError(f"Meta shard {rel} row count {len(rows)} != {exp_cnt}")
        for i, r in enumerate(rows):
            did = exp_start + i
            if r["fan_in"] != rev_deg[did] or r["fan_out"] != fwd_deg[did]:
                raise AssertionError(
                    f"Meta degree mismatch for decl {did}: meta=({r['fan_in']},{r['fan_out']}) "
                    f"actual=({rev_deg[did]},{fwd_deg[did]})"
                )
        meta_rows_seen += len(rows)
    if meta_rows_seen != n_decls:
        raise AssertionError(f"Meta total rows {meta_rows_seen} != n_decls {n_decls}")

    # 5. Verify every name shard ordering + ranges
    name_rows_seen = 0
    prev_global_key: Optional[Tuple[bytes, int]] = None
    name_ranges = mf["name_ranges"]
    if len(name_ranges) != int(mf["name_shards"]):
        raise AssertionError("name_ranges length != name_shards")
    for n in range(int(mf["name_shards"])):
        rel = _fmt_shard_path(mf, "names", n)
        rows = decode_name_shard(_read_checked_lxrf(rel))
        r_first, r_last, r_cnt = name_ranges[n]
        if len(rows) != r_cnt or len(rows) == 0:
            raise AssertionError(f"Name shard {rel} count {len(rows)} != {r_cnt}")
        if rows[0]["name"] != r_first or rows[-1]["name"] != r_last:
            raise AssertionError(f"Name shard {rel} range mismatch")
        for r in rows:
            cur_key = (utf16_key(r["name"]), r["decl_id"])
            if prev_global_key is not None and cur_key <= prev_global_key:
                raise AssertionError(
                    f"Name shard {rel} out of UTF-16 order at {r['name']!r} (id={r['decl_id']})"
                )
            prev_global_key = cur_key
        name_rows_seen += len(rows)
    if name_rows_seen != n_decls:
        raise AssertionError(f"Name shard total rows {name_rows_seen} != n_decls {n_decls}")

    # Verify manifest stats
    if total_disk_bytes != int(mf["stats"]["total_bytes"]) or lxrf_files != int(mf["stats"]["file_count"]):
        raise AssertionError(
            f"Manifest stats mismatch: counted ({total_disk_bytes} B, {lxrf_files} files) "
            f"vs manifest ({mf['stats']['total_bytes']} B, {mf['stats']['file_count']} files)"
        )

    # 6. Optional exact round-trip against kernel.db (+ leanre.db)
    checked_decls = 0
    checked_names = 0
    if kernel_db and n_decls > 0:
        rng = random.Random(seed)
        kconn = _open_ro(kernel_db)
        lconn = _open_ro(leanre_db) if leanre_db else None
        try:
            mandatory: List[int] = [0]
            for special_name in ("Eq", "Nat", "allChi", "UpperTheory.FinalTheorems.everyCharacter"):
                row = kconn.execute("SELECT id FROM decls WHERE name=?", (special_name,)).fetchone()
                if row:
                    mandatory.append(int(row[0]))
            # Zero fan_out, zero fan_in, mega-hubs, Unicode & non-BMP names
            for sql in (
                "SELECT id FROM decls WHERE fan_out=0 LIMIT 5",
                "SELECT id FROM decls WHERE fan_in=0 LIMIT 5",
                "SELECT id FROM decls WHERE fan_in>=? ORDER BY fan_in DESC LIMIT 3",
                "SELECT id FROM decls WHERE name GLOB '*[^ -~]*' LIMIT 15",
            ):
                rows_q = kconn.execute(sql, (hub_threshold,)) if "?" in sql else kconn.execute(sql)
                for (did,) in rows_q:
                    mandatory.append(int(did))
            # Pick random decls
            chosen_set = set(d for d in mandatory if 0 <= d < n_decls)
            target_n = min(n_decls, max(len(chosen_set), sample_decls))
            while len(chosen_set) < target_n:
                chosen_set.add(rng.randrange(n_decls))
            chosen = sorted(chosen_set)

            has_dom = _table_exists(kconn, "dom")
            has_dm = _table_exists(kconn, "decl_module")
            has_ldecls = lconn is not None and _table_exists(lconn, "declarations")

            for did in chosen:
                meta = store.get_meta(did)
                drow = kconn.execute(
                    "SELECT name, kind, fan_in, fan_out, fan_out_type, fan_out_value, "
                    "live_mask, type_nodes, value_nodes FROM decls WHERE id=?",
                    (did,),
                ).fetchone()
                assert drow is not None
                exp_name = _sanitize_tsv_field(drow[0] or "")
                if (
                    meta["name"] != exp_name
                    or meta["kind"] != drow[1]
                    or meta["fan_in"] != drow[2]
                    or meta["fan_out"] != drow[3]
                    or meta["fan_out_type"] != drow[4]
                    or meta["fan_out_value"] != drow[5]
                    or meta["live_mask"] != drow[6]
                    or meta["type_nodes"] != drow[7]
                    or meta["value_nodes"] != drow[8]
                ):
                    raise AssertionError(f"Meta mismatch vs kernel.db for decl {did}: {meta} vs {drow}")

                if has_dom:
                    dom_r = kconn.execute(
                        "SELECT subtree_size FROM dom WHERE tree_id=0 AND decl_id=?", (did,)
                    ).fetchone()
                    exp_dom = int(dom_r[0]) if dom_r else 0
                    if meta["dom_size"] != exp_dom:
                        raise AssertionError(f"dom_size mismatch for decl {did}: {meta['dom_size']} != {exp_dom}")

                if has_dm:
                    dm_r = kconn.execute(
                        "SELECT module, src_decl_id FROM decl_module WHERE decl_id=?", (did,)
                    ).fetchone()
                    exp_mod = dm_r[0] if (dm_r and dm_r[0]) else None
                    if meta["module"] != exp_mod:
                        raise AssertionError(f"module mismatch for decl {did}: {meta['module']} != {exp_mod}")
                    if has_ldecls and dm_r and dm_r[1] is not None:
                        lr = lconn.execute(
                            "SELECT line_no FROM declarations WHERE id=?", (int(dm_r[1]),)
                        ).fetchone()
                        exp_lno = int(lr[0]) if lr else 0
                        if meta["line_no"] != exp_lno:
                            raise AssertionError(f"line_no mismatch for decl {did}: {meta['line_no']} != {exp_lno}")

                # Exact fwd edges check
                db_fwd = list(kconn.execute("SELECT dst, kind FROM edges WHERE src=? ORDER BY dst", (did,)))
                xr_fwd = store.get_fwd(did)
                if xr_fwd != db_fwd:
                    raise AssertionError(
                        f"fwd edge mismatch for decl {did}: len {len(xr_fwd)} vs {len(db_fwd)}"
                    )

                # Exact rev edges check
                db_rev = list(kconn.execute("SELECT src, kind FROM edges WHERE dst=? ORDER BY src", (did,)))
                xr_rev = store.get_rev(did)
                if xr_rev != db_rev:
                    raise AssertionError(
                        f"rev edge mismatch for decl {did}: len {len(xr_rev)} vs {len(db_rev)}"
                    )
                checked_decls += 1

            # Exact name -> decl_id lookup check (incl. Unicode & non-BMP names)
            name_ids = set(chosen[: min(100, len(chosen))])
            for (did,) in kconn.execute("SELECT id FROM decls WHERE name GLOB '*[^ -~]*' LIMIT 200"):
                name_ids.add(int(did))
            # Also explicitly include any non-BMP names if present
            if len(name_ids) < min(n_decls, sample_names):
                while len(name_ids) < min(n_decls, sample_names):
                    name_ids.add(rng.randrange(n_decls))
            for did in sorted(name_ids):
                (nm,) = kconn.execute("SELECT name FROM decls WHERE id=?", (did,)).fetchone()
                clean_nm = _sanitize_tsv_field(nm or "")
                hit = store.lookup_name(clean_nm)
                if hit is None or hit["decl_id"] != did:
                    raise AssertionError(f"lookup_name({clean_nm!r}) failed: got {hit}, expected id={did}")
                checked_names += 1
        finally:
            kconn.close()
            if lconn is not None:
                lconn.close()

    manifest_size = os.path.getsize(os.path.join(out_dir, "manifest.json"))
    elapsed = time.monotonic() - t0
    return {
        "ok": True,
        "mode": mf["mode"],
        "n_decls": n_decls,
        "n_edges": n_edges,
        "edge_kind_counts": mf["edge_kind_counts"],
        "lxrf_files": lxrf_files,
        "total_lxrf_bytes": total_disk_bytes,
        "manifest_bytes": manifest_size,
        "total_dir_bytes": total_disk_bytes + manifest_size,
        "max_shard_bytes": max_seen_bytes,
        "max_shard_path": max_seen_path,
        "rev_hub_count": len(seen_hubs),
        "checked_decls": checked_decls,
        "checked_names": checked_names,
        "verify_seconds": round(elapsed, 3),
    }


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main(argv: Optional[Sequence[str]] = None) -> int:
    ap = argparse.ArgumentParser(
        prog="leanre-xrefs",
        description="LXRF v1 static full-graph binary cross-reference exporter & verifier",
    )
    sub = ap.add_subparsers(dest="cmd", required=True)

    p_k = sub.add_parser("kernel", help="Export LXRF v1 shards from kernel.db (+ optional leanre.db)")
    p_k.add_argument("--kernel-db", required=True, help="Path to kernel.db (read-only)")
    p_k.add_argument("--leanre-db", default=None, help="Optional path to leanre.db for line numbers")
    p_k.add_argument("--out-dir", required=True, help="Output directory for manifest.json + .lxrf shards")
    p_k.add_argument("--shard-size", type=int, default=DEFAULT_SHARD_SIZE)
    p_k.add_argument("--meta-shard-size", type=int, default=DEFAULT_META_SHARD_SIZE)
    p_k.add_argument("--name-shards", type=int, default=None)
    p_k.add_argument("--hub-threshold", type=int, default=DEFAULT_HUB_THRESHOLD)
    p_k.add_argument("--no-c", action="store_true", help="Force pure-Python exporter instead of xref_fast")
    p_k.add_argument("--threads", type=int, default=None, help="OpenMP threads for xref_fast")
    p_k.add_argument("--verbose", action="store_true")

    p_s = sub.add_parser("source", help="Export LXRF v1 shards from leanre.db or a Lean 4 source directory")
    p_s.add_argument("--leanre-db", default=None, help="Path to leanre.db (read-only)")
    p_s.add_argument("--src-dir", default=None, help="Path to Lean 4 source directory (auto-scanned)")
    p_s.add_argument("--out-dir", required=True, help="Output directory for manifest.json + .lxrf shards")
    p_s.add_argument("--shard-size", type=int, default=DEFAULT_SHARD_SIZE)
    p_s.add_argument("--meta-shard-size", type=int, default=DEFAULT_META_SHARD_SIZE)
    p_s.add_argument("--name-shards", type=int, default=None)
    p_s.add_argument("--hub-threshold", type=int, default=DEFAULT_HUB_THRESHOLD)
    p_s.add_argument("--verbose", action="store_true")

    p_v = sub.add_parser("verify", help="Verify an exported LXRF v1 directory")
    p_v.add_argument("out_dir", help="Path to exported LXRF directory")
    p_v.add_argument("--kernel-db", default=None, help="Optional kernel.db for exact round-trip check")
    p_v.add_argument("--leanre-db", default=None, help="Optional leanre.db for line_no check")
    p_v.add_argument("--sample-decls", type=int, default=500)
    p_v.add_argument("--sample-names", type=int, default=1000)
    p_v.add_argument("--seed", type=int, default=42)
    p_v.add_argument("--max-shard-mb", type=float, default=5.0)

    p_q = sub.add_parser("query", help="Query an exported LXRF v1 directory")
    p_q.add_argument("out_dir", help="Path to exported LXRF directory")
    p_q.add_argument("--id", type=int, default=None, help="Lookup declaration by numeric ID")
    p_q.add_argument("--name", default=None, help="Exact declaration name lookup")
    p_q.add_argument("--prefix", default=None, help="Prefix search on declaration names")
    p_q.add_argument("--limit", type=int, default=20)

    args = ap.parse_args(argv)
    t0 = time.monotonic()

    if args.cmd == "kernel":
        mf = export_kernel(
            args.kernel_db,
            args.out_dir,
            leanre_db=args.leanre_db,
            shard_size=args.shard_size,
            meta_shard_size=args.meta_shard_size,
            name_shards=args.name_shards,
            hub_threshold=args.hub_threshold,
            use_c=not args.no_c,
            threads=args.threads,
            verbose=args.verbose,
        )
        elapsed = time.monotonic() - t0
        summary = {
            "mode": mf["mode"],
            "n_decls": mf["n_decls"],
            "n_edges": mf["n_edges"],
            "edge_kind_counts": mf["edge_kind_counts"],
            "stats": mf["stats"],
            "rev_hubs": len(mf["rev_hub_ids"]),
            "seconds": round(elapsed, 3),
        }
        print(json.dumps(summary, indent=2))
        return 0

    if args.cmd == "source":
        mf = export_source(
            args.out_dir,
            leanre_db=args.leanre_db,
            src_dir=args.src_dir,
            shard_size=args.shard_size,
            meta_shard_size=args.meta_shard_size,
            name_shards=args.name_shards,
            hub_threshold=args.hub_threshold,
            verbose=args.verbose,
        )
        elapsed = time.monotonic() - t0
        summary = {
            "mode": mf["mode"],
            "n_decls": mf["n_decls"],
            "n_edges": mf["n_edges"],
            "edge_kind_counts": mf["edge_kind_counts"],
            "stats": mf["stats"],
            "seconds": round(elapsed, 3),
        }
        print(json.dumps(summary, indent=2))
        return 0

    if args.cmd == "verify":
        rep = verify_xrefs(
            args.out_dir,
            kernel_db=args.kernel_db,
            leanre_db=args.leanre_db,
            sample_decls=args.sample_decls,
            sample_names=args.sample_names,
            seed=args.seed,
            max_shard_mb=args.max_shard_mb,
        )
        print(json.dumps(rep, indent=2))
        return 0

    if args.cmd == "query":
        store = XrefStore(args.out_dir)
        if args.prefix is not None:
            hits = store.prefix_search(args.prefix, limit=args.limit)
            print(json.dumps(hits, ensure_ascii=False, indent=2))
            return 0
        did = args.id
        if did is None and args.name is not None:
            hit = store.lookup_name(args.name)
            if hit is None:
                print(json.dumps({"found": False, "name": args.name}))
                return 1
            did = hit["decl_id"]
        if did is None:
            print("Provide --id, --name, or --prefix", file=sys.stderr)
            return 2
        meta = store.get_meta(did)
        fwd = store.get_fwd(did)
        rev = store.get_rev(did)
        print(
            json.dumps(
                {
                    "meta": meta,
                    "fwd_count": len(fwd),
                    "fwd_sample": fwd[: args.limit],
                    "rev_count": len(rev),
                    "rev_sample": rev[: args.limit],
                },
                ensure_ascii=False,
                indent=2,
            )
        )
        return 0

    return 2


if __name__ == "__main__":
    raise SystemExit(main())
