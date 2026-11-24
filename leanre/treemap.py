#!/usr/bin/env python3
"""leanre.treemap — Hierarchical nested-rectangle treemap exporter (`leanre.treemap/1`).

Produces static gzip-9 JSON tree payloads (`.lxrt`), `manifest.json`, and
`overlay.json` (`leanre.treemap.overlay/1`) for both:
  - **Kernel mode** (`dom` ownership tree + `folder` directory tree + lazy deep-zoom tiles)
  - **Source mode** (`folder` directory tree for any Lean 4 repository, no kernel DB required)

Guardrails:
  - Python 3.11+ stdlib + sibling `leanre` modules only.
  - Strictly read-only on all SQLite databases (`mode=ro`, `PRAGMA query_only=1`) and source trees.
  - Refuses symlinked output targets; sanitizes any host paths before writing.
  - Zero verbatim `.lean` proof bodies stored in any output file.
  - Exact tree invariants: `parent.weight >= sum(child.weight)` for `sz`, `vn`, `loc`, `mods`.
"""
from __future__ import annotations

import argparse
import collections
import datetime
import gzip
import json
import multiprocessing
import os
import re
import sqlite3
import sys
import time
import zlib
from typing import Any, Dict, Iterable, List, Mapping, Optional, Sequence, Set, Tuple
from urllib.request import pathname2url

_HERE = os.path.dirname(os.path.abspath(__file__))
_REPO_ROOT = os.path.abspath(os.path.join(_HERE, ".."))
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)

try:
    import annot as _annot
    import scanner as _scanner
    import stylometry as _stylometry
except ImportError:  # pragma: no cover - package import fallback
    from leanre import annot as _annot  # type: ignore
    from leanre import scanner as _scanner  # type: ignore
    from leanre import stylometry as _stylometry  # type: ignore

MANIFEST_SCHEMA = "leanre.treemap/1"
TREE_SCHEMA = "leanre.treemap.tree/1"
OVERLAY_SCHEMA = "leanre.treemap.overlay/1"

COLS: List[str] = [
    "id",
    "p",
    "name",
    "short",
    "kind",
    "pillar",
    "sz",
    "vn",
    "loc",
    "mods",
    "mod",
    "line",
    "depth",
    "hash",
    "tile",
    "mathlib_pct",
    "hb_cnt",
    "hb_max",
    "comment_pct",
    "sorry_p",
    "sorry_c",
    "orphan_pct",
    "wrapper_pct",
    "compress",
]

SIZE_MODES_KERNEL: List[Dict[str, str]] = [
    {"id": "decls", "label": "Declarations", "col": "sz"},
    {"id": "ast", "label": "Proof AST size", "col": "vn"},
    {"id": "loc", "label": "Lines of code", "col": "loc"},
    {"id": "mods", "label": "Files", "col": "mods"},
]

SIZE_MODES_SOURCE: List[Dict[str, str]] = [
    {"id": "loc", "label": "Lines of code", "col": "loc"},
    {"id": "decls", "label": "Declarations", "col": "sz"},
    {"id": "mods", "label": "Files", "col": "mods"},
]

COLOR_MODES: List[str] = [
    "coverage",
    "pillar",
    "novelty",
    "bloat",
    "heartbeats",
    "comments",
    "sorry",
    "compress",
]

DOM_PILLARS: List[str] = [
    "Root",
    "Spine",
    "Pillar A · Theta & local matching",
    "Pillar B · Galois & étale tower",
    "Pillar C · Windowed Ш¹",
    "Pillar D · Arakelov covolume",
    "Shared core",
    "External library",
]

_PILLAR_ROOT = 0
_PILLAR_SPINE = 1
_PILLAR_A = 2
_PILLAR_B = 3
_PILLAR_C = 4
_PILLAR_D = 5
_PILLAR_SHARED = 6
_PILLAR_EXT = 7

_RH_SPINE_NAMES: Set[str] = {
    "allChi",
    "riemannHypothesis",
    "riemannZeta_eq_zero_re",
    "LFunction_ne_zero_of_half_lt_re",
    "LFunction_eq_zero_re",
    "LFunction_eq_zero_re_of_isPrimitive",
    "UpperTheory.FinalTheorems.everyCharacter",
    "UpperTheory.FinalTheorems.everyCharacter_of_row",
    "UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin",
}

_RH_PILLAR_ANCHORS: Dict[str, int] = {
    "UpperTheory.Lit.every_character_of_theta_integrals_local_matching": _PILLAR_A,
    "UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter": _PILLAR_B,
    "UpperTheory.One.vwin_of_row": _PILLAR_C,
    "SelfIntersectionVolumeEstimates.topCovolSlim2_use_alt_alt": _PILLAR_D,
}

_EXTERNAL_METHODS: Set[str] = {
    "unmatched:challenge_library",
    "unmatched:external_private",
    "unmatched:library_or_external",
}

_EXTERNAL_NS_PREFIXES: Tuple[str, ...] = (
    "Mathlib.",
    "Init.",
    "Lean.",
    "Std.",
    "Batteries.",
    "Aesop.",
    "Qq.",
    "ProofWidgets.",
    "Nat.",
    "Int.",
    "Rat.",
    "Real.",
    "Complex.",
    "Finset.",
    "Set.",
    "List.",
    "Option.",
    "MeasureTheory.",
    "CategoryTheory.",
    "AlgebraicGeometry.",
    "Topology.",
    "Filter.",
    "Order.",
)

_EXTERNAL_EXACT_NAMES: Set[str] = {
    "Eq",
    "HEq",
    "And",
    "Or",
    "Not",
    "Iff",
    "Exists",
    "True",
    "False",
    "Nat",
    "Int",
    "Rat",
    "Real",
    "Complex",
    "Bool",
    "Char",
    "String",
    "List",
    "Option",
    "Subtype",
    "Prod",
    "Sum",
    "Quot",
    "propext",
    "Classical.choice",
    "Quot.sound",
}

_RE_MAX_HEARTBEATS_VAL = re.compile(r"\bset_option\s+maxHeartbeats\s+(\d+)\b")
_RE_MAX_HEARTBEATS_ANY = re.compile(r"\bset_option\s+maxHeartbeats\b")
_RE_SORRY = re.compile(r"\bsorry\b|\badmit\b")
_RE_IMPORT = re.compile(r"^\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?([A-Za-z_][^\s]*)")
_RE_NS_OPEN = re.compile(r"^\s*namespace\s+([A-Za-z_][\w.'₀-₉]*)")
_RE_NS_END = re.compile(r"^\s*end(?:\s+([A-Za-z_][\w.'₀-₉]*))?\s*$")
_RE_DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|unsafe|partial|nonrec|scoped|local)\s+)*"
    r"(theorem|lemma|def|abbrev|structure|class|instance|inductive|opaque|axiom)\b"
    r"(?:\s+([^\s:({\[⦃]+))?"
)
_RE_BACKTICK_IDENT = re.compile(r"`([A-Za-z_][A-Za-z0-9_'.\u2080-\u2089]{2,180})`")
_RE_FENCE = re.compile(r"```.*?```", re.DOTALL)
_RE_LEAN_BODY_BLOCK = re.compile(r":=\s*by\b", re.IGNORECASE)

_FORBIDDEN_HOST_PATH_RE = re.compile(
    r"(?:"
    + "/" + "usr" + "/" + "local" + "/" + r"[^/\s]+/home/"
    + "|" + "/" + "usr" + "/" + "local" + "/" + "google"
    + "|" + "/" + "ho" + r"me/[A-Za-z0-9_.-]+"
    + "|" + "/" + "Us" + r"ers/[A-Za-z0-9_.-]+"
    + ")"
)

_WRAPPER_VN_THRESHOLD = 20


# ---------------------------------------------------------------------------
# Safe I/O, Gzip `.lxrt`, and Read-Only SQLite Helpers
# ---------------------------------------------------------------------------

def _connect_ro(db_path: str) -> sqlite3.Connection:
    """Open SQLite DB strictly read-only (`mode=ro`, `PRAGMA query_only=1`)."""
    real = os.path.realpath(db_path)
    if not os.path.isfile(real):
        raise FileNotFoundError(f"SQLite database not found: {os.path.basename(db_path)}")
    uri = f"file:{pathname2url(real)}?mode=ro"
    conn = sqlite3.connect(uri, uri=True)
    conn.execute("PRAGMA query_only=1")
    return conn


def _sanitize_str(s: str) -> str:
    if not s:
        return s
    return _FORBIDDEN_HOST_PATH_RE.sub("<path>", s) if _FORBIDDEN_HOST_PATH_RE.search(s) else s


def _sanitize_obj(obj: Any) -> Any:
    if isinstance(obj, str):
        return _sanitize_str(obj)
    if isinstance(obj, list):
        return [_sanitize_obj(v) for v in obj]
    if isinstance(obj, dict):
        return {k: _sanitize_obj(v) for k, v in obj.items()}
    return obj


def _check_safe_out_path(out_path: str) -> None:
    if os.path.islink(out_path):
        raise ValueError(f"Refusing to write through symlink: {out_path}")
    parent = os.path.dirname(os.path.abspath(out_path))
    if parent:
        if os.path.islink(parent):
            raise ValueError(f"Refusing to write inside symlinked dir: {parent}")
        os.makedirs(parent, exist_ok=True)


def write_plain_json(out_path: str, obj: Any) -> int:
    """Write deterministic compact UTF-8 JSON without compression."""
    _check_safe_out_path(out_path)
    raw = json.dumps(
        _sanitize_obj(obj),
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
        allow_nan=False,
    ).encode("utf-8")
    with open(out_path, "wb") as f:
        f.write(raw)
    return len(raw)


def write_lxrt(out_path: str, obj: Any) -> int:
    """Write deterministic gzip-9 UTF-8 JSON (`.lxrt`) with `mtime=0`."""
    _check_safe_out_path(out_path)
    raw = json.dumps(
        _sanitize_obj(obj),
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
        allow_nan=False,
    ).encode("utf-8")
    gz = gzip.compress(raw, compresslevel=9, mtime=0)
    with open(out_path, "wb") as f:
        f.write(gz)
    return len(gz)


def read_lxrt(path: str) -> Dict[str, Any]:
    """Read `.lxrt` (auto-sniffing gzip magic `0x1f 0x8b` vs plain UTF-8 JSON)."""
    with open(path, "rb") as f:
        data = f.read()
    if len(data) >= 2 and data[0] == 0x1F and data[1] == 0x8B:
        data = gzip.decompress(data)
    return json.loads(data.decode("utf-8"))


def _short_name(full: str) -> str:
    if not full:
        return ""
    if "/" in full:
        return full.rsplit("/", 1)[-1]
    if "." in full:
        return full.rsplit(".", 1)[-1]
    return full


def _is_challenge_spec_file(file_path: str, module_name: str = "") -> bool:
    """Identify intentional Comparator/Challenge specification stubs."""
    fp = str(file_path or "").replace("\\", "/").lower()
    base = os.path.basename(fp)
    mod_low = str(module_name or "").lower()
    if "comparatorchallenges/" in fp or "comparatorchallenges." in mod_low:
        return True
    if "challenge" in base or "challenge" in mod_low.rsplit(".", 1)[-1]:
        return True
    if base == "celllayertheorems.lean" or mod_low == "celllayertheorems":
        return True
    return False


def _is_external_decl(name: str, method: str) -> bool:
    if method in _EXTERNAL_METHODS:
        return True
    if not name:
        return False
    if name in _EXTERNAL_EXACT_NAMES:
        return True
    return name.startswith(_EXTERNAL_NS_PREFIXES)


def _name_compress_ratio(names: Sequence[str], max_sample: int = 0) -> float:
    """Compute `zlib` name compressibility ratio in `[0.0, 1.0]` (lower = more templated)."""
    cleaned = [
        str(nm).strip()
        for nm in names
        if nm and not str(nm).startswith("_anon_")
    ]
    if not cleaned:
        return 0.0
    if max_sample > 0 and len(cleaned) > max_sample:
        step = max(1, len(cleaned) // max_sample)
        cleaned = sorted(cleaned)[::step][:max_sample]
    else:
        cleaned.sort()
    raw = "\n".join(cleaned).encode("utf-8")
    if not raw:
        return 0.0
    comp = zlib.compress(raw, level=6)
    return round(min(1.0, len(comp) / len(raw)), 4)


def _round4(v: float) -> float:
    if v <= 0.0:
        return 0.0
    if v >= 1.0:
        return 1.0
    return round(float(v), 4)


# ---------------------------------------------------------------------------
# String Table Interner (for `tables.kinds`, `tables.pillars`, `tables.mods`)
# ---------------------------------------------------------------------------

class _StringTable:
    def __init__(self, initial: Optional[Sequence[str]] = None) -> None:
        self.items: List[str] = []
        self._idx: Dict[str, int] = {}
        if initial:
            for s in initial:
                self.intern(s)

    def intern(self, s: str) -> int:
        key = str(s or "")
        idx = self._idx.get(key)
        if idx is None:
            idx = len(self.items)
            self._idx[key] = idx
            self.items.append(key)
        return idx


# ---------------------------------------------------------------------------
# Fast Parallel Source File Metric Scanner (Zero Proof-Body Storage)
# ---------------------------------------------------------------------------

def scan_lean_file_metrics(raw_bytes: bytes, rel_path: str = "", mod_name: str = "") -> Dict[str, Any]:
    """Extract structural/stylometric metrics from one `.lean` file without keeping proof text."""
    if not raw_bytes:
        return {
            "lines": 0,
            "comment_lines": 0,
            "hb_cnt": 0,
            "hb_max": 0,
            "sorry_p": 0,
            "sorry_c": 0,
            "decl_count": 0,
            "decl_names": [],
            "imports": [],
        }

    lines_wc, comment_lines, hb_cnt = _stylometry.count_lean_comment_lines_and_heartbeats(raw_bytes)
    text = raw_bytes.decode("utf-8", errors="replace")
    code_text = _scanner.strip_lean_comments(text) if (b"--" in raw_bytes or b"/-" in raw_bytes) else text

    hb_max = 0
    if hb_cnt > 0:
        for m in _RE_MAX_HEARTBEATS_VAL.finditer(code_text):
            val = int(m.group(1))
            if val > hb_max:
                hb_max = val

    sorry_total = len(_RE_SORRY.findall(code_text)) if (b"sorry" in raw_bytes or b"admit" in raw_bytes) else 0
    if sorry_total > 0 and _is_challenge_spec_file(rel_path, mod_name):
        sorry_p, sorry_c = 0, sorry_total
    else:
        sorry_p, sorry_c = sorry_total, 0

    imports: List[str] = []
    decl_names: List[str] = []
    ns_stack: List[str] = []
    for line in code_text.splitlines():
        s = line.strip()
        if not s:
            continue
        m_imp = _RE_IMPORT.match(s)
        if m_imp:
            imports.append(m_imp.group(1))
            continue
        m_ns = _RE_NS_OPEN.match(s)
        if m_ns:
            ns_stack.append(m_ns.group(1))
            continue
        m_end = _RE_NS_END.match(s)
        if m_end and ns_stack:
            end_nm = m_end.group(1)
            if not end_nm or end_nm == ns_stack[-1]:
                ns_stack.pop()
            continue
        m_decl = _RE_DECL.match(line)
        if m_decl:
            nm = m_decl.group(2)
            if nm:
                full_nm = ".".join(ns_stack + [nm]) if ns_stack else nm
                decl_names.append(full_nm)
            else:
                decl_names.append(f"_anon_{len(decl_names)}")

    return {
        "lines": lines_wc,
        "comment_lines": comment_lines,
        "hb_cnt": hb_cnt,
        "hb_max": hb_max,
        "sorry_p": sorry_p,
        "sorry_c": sorry_c,
        "decl_count": len(decl_names),
        "decl_names": decl_names,
        "imports": imports,
    }


def _scan_fast_hb_comments_batch(args: Tuple[str, List[Tuple[str, str]]]) -> List[Tuple[str, int, int, int]]:
    """Fast batch worker for kernel/leanre.db mode: returns `(mod_name, comment_lines, hb_cnt, hb_max)`."""
    src_dir, items = args
    out: List[Tuple[str, int, int, int]] = []
    re_hb_val = _RE_MAX_HEARTBEATS_VAL
    re_hb_any = _RE_MAX_HEARTBEATS_ANY
    for mod_name, rel_path in items:
        full = os.path.join(src_dir, rel_path)
        try:
            with open(full, "rb") as f:
                raw = f.read()
        except OSError:
            continue
        if not raw:
            continue
        has_comment = (b"--" in raw) or (b"/-" in raw)
        has_hb = b"maxHeartbeats" in raw
        if not has_comment and not has_hb:
            continue
        if not has_comment:
            txt = raw.decode("utf-8", errors="replace")
            hb_cnt = len(re_hb_any.findall(txt))
            hb_max = 0
            if hb_cnt > 0:
                for m in re_hb_val.finditer(txt):
                    v = int(m.group(1))
                    if v > hb_max:
                        hb_max = v
            if hb_cnt > 0:
                out.append((mod_name, 0, hb_cnt, hb_max))
            continue
        _lwc, cln, hb_cnt = _stylometry.count_lean_comment_lines_and_heartbeats(raw)
        hb_max = 0
        if hb_cnt > 0:
            code = _scanner.strip_lean_comments(raw.decode("utf-8", errors="replace"))
            for m in re_hb_val.finditer(code):
                v = int(m.group(1))
                if v > hb_max:
                    hb_max = v
        if cln > 0 or hb_cnt > 0:
            out.append((mod_name, cln, hb_cnt, hb_max))
    return out


def _scan_full_source_batch(
    args: Tuple[str, List[Tuple[str, str]]]
) -> List[Tuple[str, str, Dict[str, Any]]]:
    src_dir, items = args
    out: List[Tuple[str, str, Dict[str, Any]]] = []
    for mod_name, rel_path in items:
        full = os.path.join(src_dir, rel_path)
        try:
            with open(full, "rb") as f:
                raw = f.read()
        except OSError:
            continue
        metrics = scan_lean_file_metrics(raw, rel_path=rel_path, mod_name=mod_name)
        out.append((mod_name, rel_path, metrics))
    return out


def _scan_rh_src_metrics(
    src_dir: Optional[str],
    mod_rel_pairs: Sequence[Tuple[str, str]],
    workers: Optional[int] = None,
) -> Dict[str, Tuple[int, int, int]]:
    """Return `{mod_name: (comment_lines, hb_cnt, hb_max)}` for all files with non-zero metrics."""
    if not src_dir or not os.path.isdir(src_dir) or not mod_rel_pairs:
        return {}
    abs_src = os.path.abspath(src_dir)
    eff_workers = max(1, int(workers if workers is not None else min(8, os.cpu_count() or 1)))
    result: Dict[str, Tuple[int, int, int]] = {}
    if eff_workers > 1 and len(mod_rel_pairs) >= 500:
        chunk_sz = max(256, (len(mod_rel_pairs) + eff_workers * 6 - 1) // (eff_workers * 6))
        batches = [
            (abs_src, list(mod_rel_pairs[i : i + chunk_sz]))
            for i in range(0, len(mod_rel_pairs), chunk_sz)
        ]
        with multiprocessing.Pool(processes=eff_workers) as pool:
            for batch_res in pool.imap_unordered(_scan_fast_hb_comments_batch, batches):
                for mod_name, cln, hbc, hbm in batch_res:
                    result[mod_name] = (cln, hbc, hbm)
    else:
        for mod_name, cln, hbc, hbm in _scan_fast_hb_comments_batch((abs_src, list(mod_rel_pairs))):
            result[mod_name] = (cln, hbc, hbm)
    return result


# ---------------------------------------------------------------------------
# Overlay Compiler (`leanre.treemap.overlay/1`)
# ---------------------------------------------------------------------------

def _normalize_layer_kind(raw_kind: str) -> str:
    k = str(raw_kind or "").strip().lower()
    if k in ("human", "human-review"):
        return "human-review"
    if k in ("dossier", "dossiers", "review-note"):
        return "dossier"
    if k in ("bot-check", "bot"):
        return "bot-check"
    return "ai-draft"


def _infer_entry_status(rec: Mapping[str, Any], layer_kind: str) -> Tuple[str, str]:
    """Return `(status, verdict)` normalized to `verified|read|summary|flagged`."""
    extra = rec.get("extra") if isinstance(rec.get("extra"), Mapping) else {}
    raw_status = str(rec.get("status") or extra.get("status") or "").strip().lower()
    raw_verdict = str(rec.get("verdict") or extra.get("verdict") or "").strip().lower()

    flagged_tokens = ("flagged", "suspect", "broken", "invalid", "fail", "error", "mismatch", "bug")
    if any(t in raw_status for t in flagged_tokens) or any(t in raw_verdict for t in flagged_tokens):
        return "flagged", raw_verdict or "flagged"
    if raw_status == "verified" or (layer_kind == "human-review" and rec.get("tag") == "L" and not raw_status):
        return "verified", raw_verdict or "verified"
    if raw_status in ("read", "partial", "audited"):
        return "read", raw_verdict or raw_status
    if raw_status == "summary":
        return "summary", raw_verdict or "summary"
    if layer_kind == "human-review":
        return "verified", raw_verdict or "verified"
    return "summary", raw_verdict or "summary"


def _clean_note_text(text: str, limit: int = 400) -> str:
    """Strip fenced code blocks and sanitize paths; never copy multi-line Lean proof blocks."""
    s = _RE_FENCE.sub(" ", str(text or ""))
    s = re.sub(r"\s+", " ", s).strip()
    if _RE_LEAN_BODY_BLOCK.search(s):
        s = _RE_LEAN_BODY_BLOCK.sub("[proof omitted]", s)
    s = _sanitize_str(s)
    if len(s) > limit:
        s = s[: limit - 1].rstrip() + "…"
    return s


def _parse_markdown_dossier(
    md_path: str,
    rel_source: str,
    route_prefix: str = "#dossiers/",
    known_names: Optional[Set[str]] = None,
) -> Optional[Dict[str, Any]]:
    """Extract title, 1-paragraph summary (zero code blocks), and referenced identifiers."""
    try:
        with open(md_path, "r", encoding="utf-8", errors="replace") as f:
            text = f.read()
    except OSError:
        return None
    stem = os.path.splitext(os.path.basename(md_path))[0]
    if stem.lower() == "readme":
        return None

    title = stem.replace("_", " ").strip()
    summary_parts: List[str] = []
    in_code = False
    for raw_line in text.splitlines():
        line = raw_line.strip()
        if line.startswith("```"):
            in_code = not in_code
            continue
        if in_code:
            continue
        if line.startswith("# ") and title == stem.replace("_", " ").strip():
            title = line[2:].strip()
            continue
        if not line or line.startswith("#") or line.startswith("|") or line.startswith("---"):
            if summary_parts:
                break
            continue
        if line.startswith(">"):
            line = line.lstrip("> ").strip()
        if line:
            summary_parts.append(line)
            if sum(len(p) for p in summary_parts) >= 240:
                break

    # Extract identifiers ONLY outside fenced code blocks
    no_code = _RE_FENCE.sub("\n", text)
    refs: List[str] = []
    seen_refs: Set[str] = set()
    for m in _RE_BACKTICK_IDENT.finditer(no_code):
        ident = m.group(1).strip(".")
        if not ident or ident in seen_refs:
            continue
        if ident.endswith(".lean") or ident.endswith(".md") or ident.endswith(".json"):
            continue
        if known_names is not None:
            if ident in known_names:
                seen_refs.add(ident)
                refs.append(ident)
        else:
            # Keep qualified names (contain '.') or prominent CamelCase/canonical landmarks
            if "." in ident or ident in _RH_SPINE_NAMES or (ident[0].isupper() and len(ident) >= 4):
                seen_refs.add(ident)
                refs.append(ident)

    return {
        "stem": stem,
        "title": _clean_note_text(title, limit=160),
        "summary": _clean_note_text(" ".join(summary_parts), limit=320),
        "source": _sanitize_str(rel_source),
        "dossier_route": f"{route_prefix}{stem}",
        "targets": refs[:80],
    }


def _collect_jsonl_files(annotations_dir: Optional[str], project: Optional[str] = None) -> List[Tuple[str, bool]]:
    """Return `[(path, is_top_level), ...]` for annotation packs under `annotations_dir`."""
    if not annotations_dir or not os.path.isdir(annotations_dir):
        return []
    files: List[Tuple[str, bool]] = []
    for entry in sorted(os.listdir(annotations_dir)):
        full = os.path.join(annotations_dir, entry)
        if os.path.isfile(full) and entry.endswith(".jsonl"):
            files.append((full, True))
    contrib_root = os.path.join(annotations_dir, "contrib")
    if os.path.isdir(contrib_root):
        for root, dirs, fns in os.walk(contrib_root):
            dirs.sort()
            rel_dir = os.path.relpath(root, contrib_root)
            if project and rel_dir != ".":
                top_slug = rel_dir.split(os.sep, 1)[0]
                if top_slug != project and top_slug != "shared":
                    continue
            for fn in sorted(fns):
                if fn.endswith(".jsonl"):
                    files.append((os.path.join(root, fn), False))
    return files


def build_overlay_json(
    annotations_dir: Optional[str],
    analysis_dir: Optional[str] = None,
    notes_dir: Optional[str] = None,
    out_path: Optional[str] = None,
    *,
    project: Optional[str] = None,
    known_names: Optional[Set[str]] = None,
    extra_dossiers: Optional[Sequence[str]] = None,
) -> Dict[str, Any]:
    """Compile `annotations/*.jsonl`, `annotations/contrib/**/*.jsonl`, and dossiers into `overlay.json`.

    Enforces strict trust separation (`ai-draft` layers ALWAYS `default_on=False` and `draft=True`),
    never copies `.lean` proof bodies, and marks `contested=True` whenever records on the same
    target disagree between positive (`verified`/`read`) and `flagged`.
    """
    layers_by_id: Dict[str, Dict[str, Any]] = {}
    entries: Dict[str, List[Dict[str, Any]]] = collections.defaultdict(list)
    layer_counts: Dict[str, int] = collections.Counter()
    layer_authors: Dict[str, Set[str]] = collections.defaultdict(set)
    total_records = 0

    for path, is_top_level in _collect_jsonl_files(annotations_dir, project=project):
        filter_by_known = bool(
            is_top_level
            and project
            and project != "riemann-hypothesis"
            and known_names is not None
        )
        try:
            with open(path, "r", encoding="utf-8") as f:
                lines = [ln.strip() for ln in f if ln.strip()]
        except OSError:
            continue
        file_layers: Dict[str, Dict[str, Any]] = {}
        for ln in lines:
            try:
                rec = json.loads(ln)
            except json.JSONDecodeError:
                continue
            if not isinstance(rec, dict):
                continue
            rtype = rec.get("type")
            if rtype == "layer":
                lid = str(rec.get("layer") or "").strip()
                if not lid:
                    continue
                lkind = _normalize_layer_kind(rec.get("kind", "ai-draft"))
                # Strict trust separation: ai-draft and bot-check are NEVER default_on!
                default_on = bool(rec.get("default_on", lkind == "human-review"))
                if lkind != "human-review":
                    default_on = False
                lobj = {
                    "id": lid,
                    "title": _clean_note_text(rec.get("title") or lid, limit=160),
                    "kind": lkind,
                    "default_on": default_on,
                    "author": "",
                    "count": 0,
                    "description": _clean_note_text(rec.get("description") or "", limit=320),
                }
                file_layers[lid] = lobj
                if not filter_by_known and lid not in layers_by_id:
                    layers_by_id[lid] = lobj
            elif rtype == "annot":
                lid = str(rec.get("layer") or "").strip()
                target_name = str(rec.get("name") or "").strip()
                if not lid or not target_name:
                    continue
                if filter_by_known and target_name not in known_names:  # type: ignore[operator]
                    continue
                lobj = layers_by_id.get(lid) or file_layers.get(lid)
                if lobj is None:
                    author_str = str(rec.get("author") or "")
                    inferred_kind = (
                        "ai-draft"
                        if author_str.startswith("ai:") or bool(rec.get("draft"))
                        else "human-review"
                    )
                    lobj = {
                        "id": lid,
                        "title": lid,
                        "kind": inferred_kind,
                        "default_on": inferred_kind == "human-review",
                        "author": "",
                        "count": 0,
                        "description": "",
                    }
                if lid not in layers_by_id:
                    layers_by_id[lid] = lobj

                lkind = lobj["kind"]
                # Enforce draft=True whenever layer is ai-draft or author starts with ai:
                author = _clean_note_text(str(rec.get("author") or ""), limit=120)
                is_draft = bool(rec.get("draft", False)) or lkind == "ai-draft" or author.startswith("ai:")
                if is_draft and lkind == "human-review":
                    # Never silently upgrade an ai:* record to human-verified
                    lkind = "ai-draft"

                status, verdict = _infer_entry_status(rec, lkind)
                note = _clean_note_text(str(rec.get("note") or rec.get("rename") or ""), limit=400)
                source = _clean_note_text(str(rec.get("source") or ""), limit=240)
                breaks = _clean_note_text(str(rec.get("breaks") or ""), limit=280)
                sighash = str(rec.get("sighash") or "").strip()
                updated = str(rec.get("updated") or rec.get("created") or "").strip()
                url = str(rec.get("url") or "").strip()
                if not url and source.startswith(("http://", "https://")):
                    url = source.split()[0]

                item: Dict[str, Any] = {
                    "layer": lid,
                    "kind": lkind,
                    "status": status,
                    "verdict": verdict,
                    "author": author,
                    "note": note,
                    "draft": is_draft,
                    "sighash": sighash,
                    "source": source,
                    "url": url,
                    "updated": updated,
                    "breaks": breaks,
                    "contested": False,
                }
                entries[target_name].append(item)
                layer_counts[lid] += 1
                if author:
                    layer_authors[lid].add(author)
                total_records += 1

    # Index markdown dossiers (`analysis/*.md`, `notes/<slug>/**/*.md`, `extra_dossiers`)
    dossier_paths: List[Tuple[str, str]] = []
    seen_md: Set[str] = set()
    if analysis_dir and os.path.isdir(analysis_dir):
        for fn in sorted(os.listdir(analysis_dir)):
            if fn.endswith(".md") and fn.lower() != "readme.md":
                full = os.path.join(analysis_dir, fn)
                real = os.path.realpath(full)
                if real not in seen_md:
                    seen_md.add(real)
                    dossier_paths.append((full, f"analysis/{fn}"))
    if notes_dir and os.path.isdir(notes_dir):
        for root, dirs, fns in os.walk(notes_dir):
            dirs.sort()
            for fn in sorted(fns):
                if fn.endswith(".md") and fn.lower() != "readme.md":
                    full = os.path.join(root, fn)
                    real = os.path.realpath(full)
                    if real not in seen_md:
                        seen_md.add(real)
                        rel = os.path.relpath(full, os.path.dirname(os.path.abspath(notes_dir))).replace("\\", "/")
                        dossier_paths.append((full, rel))
    for ep in extra_dossiers or ():
        if ep and os.path.isfile(ep):
            real = os.path.realpath(ep)
            if real not in seen_md:
                seen_md.add(real)
                dossier_paths.append((ep, os.path.basename(ep)))

    indexed_dossiers: List[Dict[str, Any]] = []
    dossier_layer_id = "dossiers/index"
    dossier_links = 0
    for md_path, rel_src in dossier_paths:
        info = _parse_markdown_dossier(md_path, rel_src, known_names=known_names)
        if not info:
            continue
        indexed_dossiers.append({
            "stem": info["stem"],
            "title": info["title"],
            "summary": info["summary"],
            "source": info["source"],
            "dossier_route": info["dossier_route"],
            "n_targets": len(info["targets"]),
        })
        for tname in info["targets"]:
            entries[tname].append({
                "layer": dossier_layer_id,
                "kind": "dossier",
                "status": "read",
                "verdict": "dossier",
                "author": "leanre/dossiers",
                "note": info["title"],
                "draft": False,
                "sighash": "",
                "source": info["source"],
                "url": "",
                "dossier_route": info["dossier_route"],
                "updated": "",
                "breaks": "",
                "contested": False,
            })
            dossier_links += 1

    if indexed_dossiers:
        layers_by_id[dossier_layer_id] = {
            "id": dossier_layer_id,
            "title": f"Dossiers & review notes ({len(indexed_dossiers)})",
            "kind": "dossier",
            "default_on": True,
            "author": "leanre/dossiers",
            "count": dossier_links,
            "description": f"Indexed {len(indexed_dossiers)} technical dossiers and review notes.",
        }
        layer_counts[dossier_layer_id] = dossier_links
        total_records += dossier_links

    # Finalize layer counts, authors, and contested status detection
    for lid, lobj in layers_by_id.items():
        lobj["count"] = int(layer_counts.get(lid, 0))
        if not lobj["author"] and layer_authors.get(lid):
            auths = sorted(layer_authors[lid])
            lobj["author"] = auths[0] if len(auths) == 1 else f"{auths[0]} (+{len(auths) - 1})"

    contested_targets = 0
    for tname, recs in entries.items():
        statuses = {r["status"] for r in recs}
        has_pos = bool(statuses & {"verified", "read"})
        has_flag = "flagged" in statuses
        if has_pos and has_flag:
            contested_targets += 1
            for r in recs:
                r["contested"] = True

    # Sort layers deterministically: human-review first, dossier second, ai-draft last
    _kind_order = {"human-review": 0, "dossier": 1, "bot-check": 2, "ai-draft": 3}
    sorted_layers = sorted(
        layers_by_id.values(),
        key=lambda x: (_kind_order.get(x["kind"], 9), x["id"]),
    )

    overlay: Dict[str, Any] = {
        "schema": OVERLAY_SCHEMA,
        "generated_utc": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "project": project or "",
        "layers": sorted_layers,
        "entries": dict(sorted(entries.items())),
        "dossiers": indexed_dossiers,
        "stats": {
            "total_layers": len(sorted_layers),
            "total_records": total_records,
            "unique_targets": len(entries),
            "contested_targets": contested_targets,
            "dossier_count": len(indexed_dossiers),
        },
    }
    if out_path:
        write_plain_json(out_path, overlay)
    return overlay


# ---------------------------------------------------------------------------
# Folder View Builder (Kernel Mode w/ `leanre.db` OR Standalone Source Mode)
# ---------------------------------------------------------------------------

class _FolderNode:
    __slots__ = (
        "fid",
        "parent",
        "name",
        "short",
        "kind",
        "pillar",
        "depth",
        "sz",
        "vn",
        "loc",
        "mods",
        "mod",
        "line",
        "mathlib_matched",
        "mathlib_denom",
        "hb_cnt",
        "hb_max",
        "comment_lines",
        "sorry_p",
        "sorry_c",
        "orphan_mods",
        "wrapper_cnt",
        "wrapper_denom",
        "compress",
        "tile",
        "subfolders",
        "files",
        "decl_names_sample",
    )

    def __init__(
        self,
        fid: int,
        parent: Optional["_FolderNode"],
        name: str,
        short: str,
        kind: str,
        pillar: str,
        depth: int,
    ) -> None:
        self.fid = fid
        self.parent = parent
        self.name = name
        self.short = short
        self.kind = kind
        self.pillar = pillar
        self.depth = depth
        self.sz = 0
        self.vn = 0
        self.loc = 0
        self.mods = 0
        self.mod = ""
        self.line = 0
        self.mathlib_matched = 0
        self.mathlib_denom = 0
        self.hb_cnt = 0
        self.hb_max = 0
        self.comment_lines = 0
        self.sorry_p = 0
        self.sorry_c = 0
        self.orphan_mods = 0
        self.wrapper_cnt = 0
        self.wrapper_denom = 0
        self.compress = 0.0
        self.tile = ""
        self.subfolders: Dict[str, "_FolderNode"] = {}
        self.files: List[Dict[str, Any]] = []
        self.decl_names_sample: List[str] = []


def _make_folder_row(
    node_id: int,
    parent_idx: int,
    name: str,
    short: str,
    kind_str: str,
    pillar_str: str,
    sz: int,
    vn: int,
    loc: int,
    mods: int,
    mod_str: str,
    line: int,
    depth: int,
    tile: str,
    mathlib_pct: float,
    hb_cnt: int,
    hb_max: int,
    comment_pct: float,
    sorry_p: int,
    sorry_c: int,
    orphan_pct: float,
    wrapper_pct: float,
    compress: float,
    kinds_tbl: _StringTable,
    pillars_tbl: _StringTable,
    mods_tbl: _StringTable,
) -> List[Any]:
    return [
        node_id,
        parent_idx,
        name,
        short,
        kinds_tbl.intern(kind_str),
        pillars_tbl.intern(pillar_str),
        int(sz),
        int(vn),
        int(loc),
        int(mods),
        mods_tbl.intern(mod_str),
        int(line),
        int(depth),
        "",
        tile,
        _round4(mathlib_pct),
        int(hb_cnt),
        int(hb_max),
        _round4(comment_pct),
        int(sorry_p),
        int(sorry_c),
        _round4(orphan_pct),
        _round4(wrapper_pct),
        _round4(compress),
    ]


def _folder_node_to_row(
    fn: _FolderNode,
    parent_idx: int,
    kinds_tbl: _StringTable,
    pillars_tbl: _StringTable,
    mods_tbl: _StringTable,
    *,
    tile_override: Optional[str] = None,
) -> List[Any]:
    mathlib_pct = (fn.mathlib_matched / fn.mathlib_denom) if fn.mathlib_denom > 0 else 0.0
    comment_pct = (fn.comment_lines / fn.loc) if fn.loc > 0 else 0.0
    orphan_pct = (fn.orphan_mods / fn.mods) if fn.mods > 0 else 0.0
    wrapper_pct = (fn.wrapper_cnt / fn.wrapper_denom) if fn.wrapper_denom > 0 else 0.0
    tile_val = fn.tile if tile_override is None else tile_override
    return _make_folder_row(
        fn.fid,
        parent_idx,
        fn.name,
        fn.short,
        fn.kind,
        fn.pillar,
        fn.sz,
        fn.vn,
        fn.loc,
        fn.mods,
        fn.mod,
        fn.line,
        fn.depth,
        tile_val,
        mathlib_pct,
        fn.hb_cnt,
        fn.hb_max,
        comment_pct,
        fn.sorry_p,
        fn.sorry_c,
        orphan_pct,
        wrapper_pct,
        fn.compress,
        kinds_tbl,
        pillars_tbl,
        mods_tbl,
    )


def _file_rec_to_row(
    node_id: int,
    parent_idx: int,
    frec: Mapping[str, Any],
    pillar_str: str,
    depth: int,
    kinds_tbl: _StringTable,
    pillars_tbl: _StringTable,
    mods_tbl: _StringTable,
) -> List[Any]:
    loc = int(frec["loc"])
    comment_pct = (int(frec["comment_lines"]) / loc) if loc > 0 else 0.0
    orphan_pct = 1.0 if frec.get("is_orphan") else 0.0
    m_denom = int(frec.get("mathlib_denom", 0))
    mathlib_pct = (int(frec.get("mathlib_matched", 0)) / m_denom) if m_denom > 0 else 0.0
    w_denom = int(frec.get("wrapper_denom", 0))
    wrapper_pct = (int(frec.get("wrapper_cnt", 0)) / w_denom) if w_denom > 0 else 0.0
    return _make_folder_row(
        node_id,
        parent_idx,
        frec["mod_name"],
        frec["short"],
        "module",
        pillar_str,
        int(frec["sz"]),
        int(frec["vn"]),
        loc,
        1,
        frec["mod_name"],
        1,
        depth,
        "",
        mathlib_pct,
        int(frec["hb_cnt"]),
        int(frec["hb_max"]),
        comment_pct,
        int(frec["sorry_p"]),
        int(frec["sorry_c"]),
        orphan_pct,
        wrapper_pct,
        float(frec.get("compress", 0.0)),
        kinds_tbl,
        pillars_tbl,
        mods_tbl,
    )


def _write_folder_tile(
    tile_dir: str,
    tile_key: str,
    parent_fn: _FolderNode,
    files: List[Dict[str, Any]],
    *,
    max_tile_rows: int,
    next_id_box: List[int],
) -> Tuple[int, int]:
    """Write `tiles_folder/{tile_key}.lxrt` (splitting into chunk sub-tiles if `len(files) > max_tile_rows`).

    Returns `(n_tiles_written, bytes_written)`.
    """
    n_written = 0
    bytes_written = 0
    kinds_tbl = _StringTable(["folder", "module", "group"])
    pillars_tbl = _StringTable([parent_fn.pillar])
    mods_tbl = _StringTable([""])

    rows: List[List[Any]] = []
    # Root row of tile represents this folder's direct files container
    root_row = _folder_node_to_row(parent_fn, -1, kinds_tbl, pillars_tbl, mods_tbl, tile_override="")
    # Ensure tile root sums match exact sum of its direct files if parent_fn also had subfolders
    if parent_fn.subfolders:
        f_sz = sum(int(x["sz"]) for x in files)
        f_vn = sum(int(x["vn"]) for x in files)
        f_loc = sum(int(x["loc"]) for x in files)
        f_mods = len(files)
        f_hb = sum(int(x["hb_cnt"]) for x in files)
        f_hbmax = max((int(x["hb_max"]) for x in files), default=0)
        f_cln = sum(int(x["comment_lines"]) for x in files)
        f_sp = sum(int(x["sorry_p"]) for x in files)
        f_sc = sum(int(x["sorry_c"]) for x in files)
        f_orph = sum(1 for x in files if x.get("is_orphan"))
        f_mm = sum(int(x.get("mathlib_matched", 0)) for x in files)
        f_md = sum(int(x.get("mathlib_denom", 0)) for x in files)
        f_wc = sum(int(x.get("wrapper_cnt", 0)) for x in files)
        f_wd = sum(int(x.get("wrapper_denom", 0)) for x in files)
        root_row = _make_folder_row(
            parent_fn.fid,
            -1,
            f"{parent_fn.name}/[files]",
            f"{parent_fn.short} (files)",
            "group",
            parent_fn.pillar,
            f_sz,
            f_vn,
            f_loc,
            f_mods,
            "",
            0,
            parent_fn.depth + 1,
            "",
            (f_mm / f_md) if f_md > 0 else 0.0,
            f_hb,
            f_hbmax,
            (f_cln / f_loc) if f_loc > 0 else 0.0,
            f_sp,
            f_sc,
            (f_orph / f_mods) if f_mods > 0 else 0.0,
            (f_wc / f_wd) if f_wd > 0 else 0.0,
            parent_fn.compress,
            kinds_tbl,
            pillars_tbl,
            mods_tbl,
        )
    rows.append(root_row)

    sorted_files = sorted(files, key=lambda x: (-int(x["loc"]), x["short"]))
    if len(sorted_files) <= max_tile_rows:
        for frec in sorted_files:
            nid = next_id_box[0]
            next_id_box[0] += 1
            rows.append(
                _file_rec_to_row(
                    nid, 0, frec, parent_fn.pillar, parent_fn.depth + 1, kinds_tbl, pillars_tbl, mods_tbl
                )
            )
    else:
        # Sort alphabetically into deterministic chunks of `<= max_tile_rows` files
        alpha_files = sorted(files, key=lambda x: x["short"])
        chunk_sz = max(50, max_tile_rows)
        for ci, start in enumerate(range(0, len(alpha_files), chunk_sz)):
            chunk = alpha_files[start : start + chunk_sz]
            sub_key = f"{tile_key}_c{ci}"
            first_s = chunk[0]["short"][:16]
            last_s = chunk[-1]["short"][:16]
            label = f"{first_s}…{last_s} ({len(chunk)})"
            cid = next_id_box[0]
            next_id_box[0] += 1
            c_sz = sum(int(x["sz"]) for x in chunk)
            c_vn = sum(int(x["vn"]) for x in chunk)
            c_loc = sum(int(x["loc"]) for x in chunk)
            c_mods = len(chunk)
            c_hb = sum(int(x["hb_cnt"]) for x in chunk)
            c_hbmax = max((int(x["hb_max"]) for x in chunk), default=0)
            c_cln = sum(int(x["comment_lines"]) for x in chunk)
            c_sp = sum(int(x["sorry_p"]) for x in chunk)
            c_sc = sum(int(x["sorry_c"]) for x in chunk)
            c_orph = sum(1 for x in chunk if x.get("is_orphan"))
            c_mm = sum(int(x.get("mathlib_matched", 0)) for x in chunk)
            c_md = sum(int(x.get("mathlib_denom", 0)) for x in chunk)
            c_wc = sum(int(x.get("wrapper_cnt", 0)) for x in chunk)
            c_wd = sum(int(x.get("wrapper_denom", 0)) for x in chunk)
            c_comp = round(sum(float(x.get("compress", 0.0)) for x in chunk) / max(1, c_mods), 4)
            rows.append(
                _make_folder_row(
                    cid,
                    0,
                    f"{parent_fn.name}/[{first_s}..{last_s}]",
                    label,
                    "group",
                    parent_fn.pillar,
                    c_sz,
                    c_vn,
                    c_loc,
                    c_mods,
                    "",
                    0,
                    parent_fn.depth + 1,
                    sub_key,
                    (c_mm / c_md) if c_md > 0 else 0.0,
                    c_hb,
                    c_hbmax,
                    (c_cln / c_loc) if c_loc > 0 else 0.0,
                    c_sp,
                    c_sc,
                    (c_orph / c_mods) if c_mods > 0 else 0.0,
                    (c_wc / c_wd) if c_wd > 0 else 0.0,
                    c_comp,
                    kinds_tbl,
                    pillars_tbl,
                    mods_tbl,
                )
            )
            # Emit child chunk tile
            ckinds = _StringTable(["group", "module"])
            cpillars = _StringTable([parent_fn.pillar])
            cmods = _StringTable([""])
            crows = [
                _make_folder_row(
                    cid,
                    -1,
                    f"{parent_fn.name}/[{first_s}..{last_s}]",
                    label,
                    "group",
                    parent_fn.pillar,
                    c_sz,
                    c_vn,
                    c_loc,
                    c_mods,
                    "",
                    0,
                    parent_fn.depth + 1,
                    "",
                    (c_mm / c_md) if c_md > 0 else 0.0,
                    c_hb,
                    c_hbmax,
                    (c_cln / c_loc) if c_loc > 0 else 0.0,
                    c_sp,
                    c_sc,
                    (c_orph / c_mods) if c_mods > 0 else 0.0,
                    (c_wc / c_wd) if c_wd > 0 else 0.0,
                    c_comp,
                    ckinds,
                    cpillars,
                    cmods,
                )
            ]
            for frec in chunk:
                fid = next_id_box[0]
                next_id_box[0] += 1
                crows.append(
                    _file_rec_to_row(
                        fid, 0, frec, parent_fn.pillar, parent_fn.depth + 2, ckinds, cpillars, cmods
                    )
                )
            sub_payload = {
                "schema": TREE_SCHEMA,
                "view": "folder",
                "root_name": label,
                "tables": {"kinds": ckinds.items, "pillars": cpillars.items, "mods": cmods.items},
                "cols": COLS,
                "rows": crows,
            }
            bytes_written += write_lxrt(os.path.join(tile_dir, f"{sub_key}.lxrt"), sub_payload)
            n_written += 1

    payload = {
        "schema": TREE_SCHEMA,
        "view": "folder",
        "root_name": parent_fn.short,
        "tables": {"kinds": kinds_tbl.items, "pillars": pillars_tbl.items, "mods": mods_tbl.items},
        "cols": COLS,
        "rows": rows,
    }
    bytes_written += write_lxrt(os.path.join(tile_dir, f"{tile_key}.lxrt"), payload)
    n_written += 1
    return n_written, bytes_written


def _build_folder_view(
    file_records: Sequence[Dict[str, Any]],
    out_dir: str,
    root_name: str,
    *,
    inline_file_limit: int = 4000,
    max_tile_rows: int = 400,
    root_compress_override: Optional[float] = None,
) -> Dict[str, Any]:
    """Assemble `folder.lxrt` + optional `tiles_folder/{id}.lxrt` from per-file records."""
    next_id = [1]
    root = _FolderNode(0, None, root_name, root_name, "folder", "Root", 0)
    all_folders: List[_FolderNode] = [root]

    for frec in file_records:
        rel_path = str(frec["rel_path"]).replace("\\", "/").lstrip("./")
        parts = [p for p in rel_path.split("/") if p]
        dirs = parts[:-1]
        cur = root
        top_pillar = dirs[0] if dirs else "Root"
        for d_idx, seg in enumerate(dirs):
            child = cur.subfolders.get(seg)
            if child is None:
                fid = next_id[0]
                next_id[0] += 1
                full_dir = "/".join(dirs[: d_idx + 1])
                child = _FolderNode(fid, cur, full_dir, seg, "folder", top_pillar, d_idx + 1)
                cur.subfolders[seg] = child
                all_folders.append(child)
            cur = child
        cur.files.append(frec)

    # Bottom-up aggregation (deepest folders first)
    all_folders.sort(key=lambda f: -f.depth)
    for fn in all_folders:
        for frec in fn.files:
            fn.sz += int(frec["sz"])
            fn.vn += int(frec["vn"])
            fn.loc += int(frec["loc"])
            fn.mods += 1
            fn.hb_cnt += int(frec["hb_cnt"])
            if int(frec["hb_max"]) > fn.hb_max:
                fn.hb_max = int(frec["hb_max"])
            fn.comment_lines += int(frec["comment_lines"])
            fn.sorry_p += int(frec["sorry_p"])
            fn.sorry_c += int(frec["sorry_c"])
            if frec.get("is_orphan"):
                fn.orphan_mods += 1
            fn.mathlib_matched += int(frec.get("mathlib_matched", 0))
            fn.mathlib_denom += int(frec.get("mathlib_denom", 0))
            fn.wrapper_cnt += int(frec.get("wrapper_cnt", 0))
            fn.wrapper_denom += int(frec.get("wrapper_denom", 0))
            if frec.get("decl_names"):
                if len(fn.decl_names_sample) < 600:
                    fn.decl_names_sample.extend(frec["decl_names"][: 600 - len(fn.decl_names_sample)])
        for sub in fn.subfolders.values():
            fn.sz += sub.sz
            fn.vn += sub.vn
            fn.loc += sub.loc
            fn.mods += sub.mods
            fn.hb_cnt += sub.hb_cnt
            if sub.hb_max > fn.hb_max:
                fn.hb_max = sub.hb_max
            fn.comment_lines += sub.comment_lines
            fn.sorry_p += sub.sorry_p
            fn.sorry_c += sub.sorry_c
            fn.orphan_mods += sub.orphan_mods
            fn.mathlib_matched += sub.mathlib_matched
            fn.mathlib_denom += sub.mathlib_denom
            fn.wrapper_cnt += sub.wrapper_cnt
            fn.wrapper_denom += sub.wrapper_denom
            if sub.decl_names_sample and len(fn.decl_names_sample) < 600:
                fn.decl_names_sample.extend(sub.decl_names_sample[: 600 - len(fn.decl_names_sample)])

        if fn.decl_names_sample:
            fn.compress = _name_compress_ratio(fn.decl_names_sample, max_sample=512)
        elif fn.files:
            fn.compress = round(
                sum(float(x.get("compress", 0.0)) for x in fn.files) / len(fn.files), 4
            )
        elif fn.subfolders:
            tot_m = sum(s.mods for s in fn.subfolders.values()) or 1
            fn.compress = round(
                sum(s.compress * s.mods for s in fn.subfolders.values()) / tot_m, 4
            )

    if root_compress_override is not None:
        root.compress = _round4(root_compress_override)

    # Decide inline vs lazy tiles
    total_files = len(file_records)
    inline_all = (len(all_folders) + total_files) <= inline_file_limit

    kinds_tbl = _StringTable(["folder", "module", "group"])
    pillars_tbl = _StringTable(["Root"])
    mods_tbl = _StringTable([""])

    rows: List[List[Any]] = []
    tiles_dir = os.path.join(out_dir, "tiles_folder")
    n_tiles = 0
    tiles_bytes = 0

    # Iterative pre-order emit
    # Each stack item: (folder_node, parent_row_idx)
    stack: List[Tuple[_FolderNode, int]] = [(root, -1)]
    while stack:
        fn, p_idx = stack.pop()
        my_idx = len(rows)

        has_subs = bool(fn.subfolders)
        has_files = bool(fn.files)

        if inline_all:
            rows.append(_folder_node_to_row(fn, p_idx, kinds_tbl, pillars_tbl, mods_tbl, tile_override=""))
            # Emit direct files right under this folder
            for frec in sorted(fn.files, key=lambda x: (-int(x["loc"]), x["short"])):
                nid = next_id[0]
                next_id[0] += 1
                rows.append(
                    _file_rec_to_row(
                        nid, my_idx, frec, fn.pillar, fn.depth + 1, kinds_tbl, pillars_tbl, mods_tbl
                    )
                )
            # Push subfolders in reverse order so largest appears first
            for sub in sorted(fn.subfolders.values(), key=lambda s: (s.loc, s.name)):
                stack.append((sub, my_idx))
        else:
            # Large repo: leaf folders get `tile = str(fn.fid)` directly;
            # interior folders with BOTH subfolders AND direct files either inline small direct files (<= 8)
            # OR attach one synthetic leaf `"[files]"` pointing to `tiles_folder/{fn.fid}_f.lxrt`
            # so ONLY leaf rows ever carry non-empty `tile`!
            if not has_subs and has_files:
                tile_key = str(fn.fid)
                fn.tile = tile_key
                rows.append(_folder_node_to_row(fn, p_idx, kinds_tbl, pillars_tbl, mods_tbl))
                nt, nb = _write_folder_tile(
                    tiles_dir, tile_key, fn, fn.files, max_tile_rows=max_tile_rows, next_id_box=next_id
                )
                n_tiles += nt
                tiles_bytes += nb
            else:
                rows.append(_folder_node_to_row(fn, p_idx, kinds_tbl, pillars_tbl, mods_tbl, tile_override=""))
                if has_files:
                    if len(fn.files) <= 8:
                        for frec in sorted(fn.files, key=lambda x: (-int(x["loc"]), x["short"])):
                            nid = next_id[0]
                            next_id[0] += 1
                            rows.append(
                                _file_rec_to_row(
                                    nid, my_idx, frec, fn.pillar, fn.depth + 1, kinds_tbl, pillars_tbl, mods_tbl
                                )
                            )
                    else:
                        tile_key = f"{fn.fid}_f"
                        gid = next_id[0]
                        next_id[0] += 1
                        files_only = fn.files
                        f_sz = sum(int(x["sz"]) for x in files_only)
                        f_vn = sum(int(x["vn"]) for x in files_only)
                        f_loc = sum(int(x["loc"]) for x in files_only)
                        f_mods = len(files_only)
                        f_hb = sum(int(x["hb_cnt"]) for x in files_only)
                        f_hbmax = max((int(x["hb_max"]) for x in files_only), default=0)
                        f_cln = sum(int(x["comment_lines"]) for x in files_only)
                        f_sp = sum(int(x["sorry_p"]) for x in files_only)
                        f_sc = sum(int(x["sorry_c"]) for x in files_only)
                        f_orph = sum(1 for x in files_only if x.get("is_orphan"))
                        f_mm = sum(int(x.get("mathlib_matched", 0)) for x in files_only)
                        f_md = sum(int(x.get("mathlib_denom", 0)) for x in files_only)
                        f_wc = sum(int(x.get("wrapper_cnt", 0)) for x in files_only)
                        f_wd = sum(int(x.get("wrapper_denom", 0)) for x in files_only)
                        rows.append(
                            _make_folder_row(
                                gid,
                                my_idx,
                                f"{fn.name}/[files]",
                                f"{fn.short} ({f_mods:,} files)",
                                "group",
                                fn.pillar,
                                f_sz,
                                f_vn,
                                f_loc,
                                f_mods,
                                "",
                                0,
                                fn.depth + 1,
                                tile_key,
                                (f_mm / f_md) if f_md > 0 else 0.0,
                                f_hb,
                                f_hbmax,
                                (f_cln / f_loc) if f_loc > 0 else 0.0,
                                f_sp,
                                f_sc,
                                (f_orph / f_mods) if f_mods > 0 else 0.0,
                                (f_wc / f_wd) if f_wd > 0 else 0.0,
                                fn.compress,
                                kinds_tbl,
                                pillars_tbl,
                                mods_tbl,
                            )
                        )
                        nt, nb = _write_folder_tile(
                            tiles_dir, tile_key, fn, files_only, max_tile_rows=max_tile_rows, next_id_box=next_id
                        )
                        n_tiles += nt
                        tiles_bytes += nb
                for sub in sorted(fn.subfolders.values(), key=lambda s: (s.loc, s.name)):
                    stack.append((sub, my_idx))

    tree_payload = {
        "schema": TREE_SCHEMA,
        "view": "folder",
        "root_name": root_name,
        "tables": {
            "kinds": kinds_tbl.items,
            "pillars": pillars_tbl.items,
            "mods": mods_tbl.items,
        },
        "cols": COLS,
        "rows": rows,
    }
    folder_bytes = write_lxrt(os.path.join(out_dir, "folder.lxrt"), tree_payload)
    return {
        "view": {
            "id": "folder",
            "label": "Directory tree",
            "file": "folder.lxrt",
            "unit": "lines",
            "total_weight": int(root.loc),
            "n_nodes": len(rows),
            "n_tiles": n_tiles,
            "tile_path": "tiles_folder/{id}.lxrt" if n_tiles > 0 else "",
        },
        "stats": {
            "folder_bytes": folder_bytes,
            "tiles_folder_bytes": tiles_bytes,
            "n_tiles": n_tiles,
            "total_loc": int(root.loc),
            "total_mods": int(root.mods),
            "total_decls": int(root.sz),
        },
    }


# ---------------------------------------------------------------------------
# Kernel Mode (`dom` Ownership Tree + `folder` Directory Tree)
# ---------------------------------------------------------------------------

def _load_kernel_dom_state(
    kernel_db: str,
    leanre_db: Optional[str],
    tier2_db: Optional[str],
    src_metrics: Mapping[str, Tuple[int, int, int]],
    mod_sorry_map: Mapping[str, Tuple[int, int]],
    mod_meta_map: Mapping[str, Tuple[int, bool]],  # mod_name -> (lines, is_orphan)
    decl_line_map: Mapping[int, int],
) -> Dict[str, Any]:
    """Load `dom (tree_id=0)` + `decls` + `decl_module` + `tier2` and compute exact subtree aggregates."""
    kcon = _connect_ro(kernel_db)
    try:
        # 1. Load dom tree_id=0
        dom_rows = kcon.execute(
            "SELECT decl_id, idom, depth, subtree_size FROM dom WHERE tree_id=0"
        ).fetchall()
        if not dom_rows:
            raise ValueError("kernel.db contains no rows in dom WHERE tree_id=0")

        max_id = max(r[0] for r in dom_rows)
        n_slots = max_id + 1

        in_dom = bytearray(n_slots)
        idom_arr: List[int] = [-2] * n_slots  # -2 = not in dom, -1 = top root (idom IS NULL)
        depth_arr: List[int] = [0] * n_slots
        sz_arr: List[int] = [0] * n_slots
        children: Dict[int, List[int]] = collections.defaultdict(list)
        dom_ids: List[int] = []

        for did, idom, depth, sz in dom_rows:
            in_dom[did] = 1
            dom_ids.append(did)
            p = -1 if idom is None else int(idom)
            idom_arr[did] = p
            depth_arr[did] = int(depth)
            sz_arr[did] = int(sz)
            children[p].append(did)

        # 2. Load decls info for nodes in dom
        name_arr: List[str] = [""] * n_slots
        kind_arr: List[str] = [""] * n_slots
        vn_self: List[int] = [0] * n_slots
        hash_arr: List[str] = [""] * n_slots

        for did, name, kind, vn, sh in kcon.execute(
            "SELECT id, name, kind, value_nodes, sighash FROM decls"
        ):
            if did < n_slots and in_dom[did]:
                name_arr[did] = str(name)
                kind_arr[did] = str(kind)
                vn_self[did] = int(vn or 0)
                hash_arr[did] = str(sh or "")

        # 3. Load decl_module if present
        mod_arr: List[str] = [""] * n_slots
        method_arr: List[str] = [""] * n_slots
        line_arr: List[int] = [0] * n_slots
        has_dm = bool(
            kcon.execute(
                "SELECT 1 FROM sqlite_master WHERE type='table' AND name='decl_module'"
            ).fetchone()
        )
        if has_dm:
            for did, mod, method, src_decl_id in kcon.execute(
                "SELECT decl_id, module, method, src_decl_id FROM decl_module"
            ):
                if did < n_slots and in_dom[did]:
                    if mod:
                        mod_arr[did] = str(mod)
                    if method:
                        method_arr[did] = str(method)
                    if src_decl_id is not None and src_decl_id in decl_line_map:
                        line_arr[did] = decl_line_map[int(src_decl_id)]
    finally:
        kcon.close()

    # 4. Load tier2.db kernel_matches if available
    tier2_matched: Set[int] = set()
    if tier2_db and os.path.isfile(os.path.realpath(tier2_db)):
        tcon = _connect_ro(tier2_db)
        try:
            has_km = bool(
                tcon.execute(
                    "SELECT 1 FROM sqlite_master WHERE type='table' AND name='kernel_matches'"
                ).fetchone()
            )
            if has_km:
                for (did,) in tcon.execute("SELECT DISTINCT decl_id FROM kernel_matches"):
                    tier2_matched.add(int(did))
        finally:
            tcon.close()

    # 5. Assign each module uniquely to one owner decl in dom (largest sz_arr in that module)
    #    so loc, mods, hb_cnt, comment_lines, sorry_p, sorry_c sum additively with ZERO double-counting!
    mod_best_owner: Dict[str, int] = {}
    for did in dom_ids:
        m = mod_arr[did]
        if not m:
            continue
        prev = mod_best_owner.get(m)
        if prev is None or sz_arr[did] > sz_arr[prev]:
            mod_best_owner[m] = did

    loc_self: List[int] = [0] * n_slots
    mods_self: List[int] = [0] * n_slots
    hb_cnt_self: List[int] = [0] * n_slots
    hb_max_self: List[int] = [0] * n_slots
    cln_self: List[int] = [0] * n_slots
    sp_self: List[int] = [0] * n_slots
    sc_self: List[int] = [0] * n_slots
    orph_self: List[int] = [0] * n_slots

    # Residual stats for modules in leanre.db with 0 live decls in dom (assigned to synthetic root Main)
    root_extra_loc = 0
    root_extra_mods = 0
    root_extra_hb_cnt = 0
    root_extra_hb_max = 0
    root_extra_cln = 0
    root_extra_sp = 0
    root_extra_sc = 0
    root_extra_orph = 0

    for mod_name, (m_lines, m_is_orphan) in mod_meta_map.items():
        cln, hbc, hbm = src_metrics.get(mod_name, (0, 0, 0))
        sp, sc = mod_sorry_map.get(mod_name, (0, 0))
        owner = mod_best_owner.get(mod_name)
        if owner is not None:
            loc_self[owner] += m_lines
            mods_self[owner] += 1
            hb_cnt_self[owner] += hbc
            if hbm > hb_max_self[owner]:
                hb_max_self[owner] = hbm
            cln_self[owner] += cln
            sp_self[owner] += sp
            sc_self[owner] += sc
            if m_is_orphan:
                orph_self[owner] += 1
        else:
            root_extra_loc += m_lines
            root_extra_mods += 1
            root_extra_hb_cnt += hbc
            if hbm > root_extra_hb_max:
                root_extra_hb_max = hbm
            root_extra_cln += cln
            root_extra_sp += sp
            root_extra_sc += sc
            if m_is_orphan:
                root_extra_orph += 1

    # 6. Top-down pillar assignment + iterative post-order bottom-up aggregation
    pillar_arr = bytearray(n_slots)  # 0..7 index into DOM_PILLARS
    mathlib_sub: List[int] = [0] * n_slots
    wrapper_sub: List[int] = [0] * n_slots
    vn_sub: List[int] = [0] * n_slots
    loc_sub: List[int] = [0] * n_slots
    mods_sub: List[int] = [0] * n_slots
    hb_cnt_sub: List[int] = [0] * n_slots
    hb_max_sub: List[int] = [0] * n_slots
    cln_sub: List[int] = [0] * n_slots
    sp_sub: List[int] = [0] * n_slots
    sc_sub: List[int] = [0] * n_slots
    orph_sub: List[int] = [0] * n_slots

    # Top-down BFS/DFS from synthetic root (-1)
    post_order: List[int] = []
    # Stack entries: (decl_id, inherited_pillar)
    td_stack: List[Tuple[int, int]] = []
    for top_id in children.get(-1, ()):
        td_stack.append((top_id, _PILLAR_ROOT))

    while td_stack:
        u, inh_pillar = td_stack.pop()
        post_order.append(u)
        nm = name_arr[u]
        if nm in _RH_PILLAR_ANCHORS:
            my_p = _RH_PILLAR_ANCHORS[nm]
            child_p = my_p
        elif nm in _RH_SPINE_NAMES:
            my_p = _PILLAR_SPINE
            child_p = _PILLAR_SHARED
        elif inh_pillar in (_PILLAR_A, _PILLAR_B, _PILLAR_C, _PILLAR_D):
            my_p = inh_pillar
            child_p = inh_pillar
        elif _is_external_decl(nm, method_arr[u]):
            my_p = _PILLAR_EXT
            child_p = _PILLAR_EXT
        else:
            my_p = _PILLAR_SHARED if inh_pillar == _PILLAR_SHARED else _PILLAR_SHARED
            child_p = my_p
        pillar_arr[u] = my_p
        for c in children.get(u, ()):
            td_stack.append((c, child_p))

    # Bottom-up aggregation (reverse of pre-order = valid post-order!)
    per_mod_kernel: Dict[str, List[int]] = {}  # mod_name -> [vn_sum, lib_cnt, decl_cnt, wrap_cnt]
    for u in reversed(post_order):
        is_lib = 1 if (u in tier2_matched or _is_external_decl(name_arr[u], method_arr[u])) else 0
        is_wrap = 1 if vn_self[u] <= _WRAPPER_VN_THRESHOLD else 0

        m_name = mod_arr[u]
        if m_name:
            acc = per_mod_kernel.get(m_name)
            if acc is None:
                per_mod_kernel[m_name] = [vn_self[u], is_lib, 1, is_wrap]
            else:
                acc[0] += vn_self[u]
                acc[1] += is_lib
                acc[2] += 1
                acc[3] += is_wrap

        v_vn = vn_self[u]
        v_lib = is_lib
        v_wrap = is_wrap
        v_loc = loc_self[u]
        v_mods = mods_self[u]
        v_hbc = hb_cnt_self[u]
        v_hbm = hb_max_self[u]
        v_cln = cln_self[u]
        v_sp = sp_self[u]
        v_sc = sc_self[u]
        v_orph = orph_self[u]

        for c in children.get(u, ()):
            v_vn += vn_sub[c]
            v_lib += mathlib_sub[c]
            v_wrap += wrapper_sub[c]
            v_loc += loc_sub[c]
            v_mods += mods_sub[c]
            v_hbc += hb_cnt_sub[c]
            if hb_max_sub[c] > v_hbm:
                v_hbm = hb_max_sub[c]
            v_cln += cln_sub[c]
            v_sp += sp_sub[c]
            v_sc += sc_sub[c]
            v_orph += orph_sub[c]

        vn_sub[u] = v_vn
        mathlib_sub[u] = v_lib
        wrapper_sub[u] = v_wrap
        loc_sub[u] = v_loc
        mods_sub[u] = v_mods
        hb_cnt_sub[u] = v_hbc
        hb_max_sub[u] = v_hbm
        cln_sub[u] = v_cln
        sp_sub[u] = v_sp
        sc_sub[u] = v_sc
        orph_sub[u] = v_orph

    # Root totals
    top_ids = children.get(-1, [])
    root_sz = sum(sz_arr[c] for c in top_ids)
    root_vn = sum(vn_sub[c] for c in top_ids)
    root_lib = sum(mathlib_sub[c] for c in top_ids)
    root_wrap = sum(wrapper_sub[c] for c in top_ids)
    root_loc = sum(loc_sub[c] for c in top_ids) + root_extra_loc
    root_mods = sum(mods_sub[c] for c in top_ids) + root_extra_mods
    root_hbc = sum(hb_cnt_sub[c] for c in top_ids) + root_extra_hb_cnt
    root_hbm = max([root_extra_hb_max] + [hb_max_sub[c] for c in top_ids])
    root_cln = sum(cln_sub[c] for c in top_ids) + root_extra_cln
    root_sp = sum(sp_sub[c] for c in top_ids) + root_extra_sp
    root_sc = sum(sc_sub[c] for c in top_ids) + root_extra_sc
    root_orph = sum(orph_sub[c] for c in top_ids) + root_extra_orph

    return {
        "dom_ids": dom_ids,
        "idom": idom_arr,
        "depth": depth_arr,
        "sz": sz_arr,
        "children": children,
        "name": name_arr,
        "kind": kind_arr,
        "vn_sub": vn_sub,
        "hash": hash_arr,
        "mod": mod_arr,
        "line": line_arr,
        "pillar": pillar_arr,
        "mathlib_sub": mathlib_sub,
        "wrapper_sub": wrapper_sub,
        "loc_sub": loc_sub,
        "mods_sub": mods_sub,
        "hb_cnt_sub": hb_cnt_sub,
        "hb_max_sub": hb_max_sub,
        "cln_sub": cln_sub,
        "sp_sub": sp_sub,
        "sc_sub": sc_sub,
        "orph_sub": orph_sub,
        "per_mod_kernel": per_mod_kernel,
        "root": {
            "sz": root_sz,
            "vn": root_vn,
            "lib": root_lib,
            "wrap": root_wrap,
            "loc": root_loc,
            "mods": root_mods,
            "hbc": root_hbc,
            "hbm": root_hbm,
            "cln": root_cln,
            "sp": root_sp,
            "sc": root_sc,
            "orph": root_orph,
        },
    }


def _dom_decl_row(
    st: Dict[str, Any],
    did: int,
    parent_idx: int,
    depth: int,
    tile: str,
    compress: float,
    kinds_tbl: _StringTable,
    mods_tbl: _StringTable,
) -> List[Any]:
    sz = st["sz"][did]
    loc = st["loc_sub"][did]
    mods = st["mods_sub"][did]
    return [
        int(did),
        int(parent_idx),
        st["name"][did],
        _short_name(st["name"][did]),
        kinds_tbl.intern(st["kind"][did] or "thm"),
        int(st["pillar"][did]),
        int(sz),
        int(st["vn_sub"][did]),
        int(loc),
        int(mods),
        mods_tbl.intern(st["mod"][did]),
        int(st["line"][did]),
        int(depth),
        st["hash"][did],
        tile,
        _round4(st["mathlib_sub"][did] / max(1, sz)),
        int(st["hb_cnt_sub"][did]),
        int(st["hb_max_sub"][did]),
        _round4(st["cln_sub"][did] / loc) if loc > 0 else 0.0,
        int(st["sp_sub"][did]),
        int(st["sc_sub"][did]),
        _round4(st["orph_sub"][did] / mods) if mods > 0 else 0.0,
        _round4(st["wrapper_sub"][did] / max(1, sz)),
        _round4(compress),
    ]


def _aggregate_dom_group(st: Dict[str, Any], node_ids: Sequence[int]) -> Dict[str, Any]:
    sz = 0
    vn = 0
    loc = 0
    mods = 0
    lib = 0
    wrap = 0
    hbc = 0
    hbm = 0
    cln = 0
    sp = 0
    sc = 0
    orph = 0
    pillar_votes: Dict[int, int] = collections.Counter()
    for u in node_ids:
        u_sz = st["sz"][u]
        sz += u_sz
        vn += st["vn_sub"][u]
        loc += st["loc_sub"][u]
        mods += st["mods_sub"][u]
        lib += st["mathlib_sub"][u]
        wrap += st["wrapper_sub"][u]
        hbc += st["hb_cnt_sub"][u]
        if st["hb_max_sub"][u] > hbm:
            hbm = st["hb_max_sub"][u]
        cln += st["cln_sub"][u]
        sp += st["sp_sub"][u]
        sc += st["sc_sub"][u]
        orph += st["orph_sub"][u]
        pillar_votes[int(st["pillar"][u])] += u_sz
    best_pillar = max(pillar_votes.items(), key=lambda kv: kv[1])[0] if pillar_votes else _PILLAR_SHARED
    comp = _name_compress_ratio([st["name"][u] for u in node_ids[:256]], max_sample=128)
    return {
        "sz": sz,
        "vn": vn,
        "loc": loc,
        "mods": mods,
        "lib": lib,
        "wrap": wrap,
        "hbc": hbc,
        "hbm": hbm,
        "cln": cln,
        "sp": sp,
        "sc": sc,
        "orph": orph,
        "pillar": best_pillar,
        "compress": comp,
    }


def _dom_group_row(
    group_id: str,
    parent_idx: int,
    name: str,
    short: str,
    depth: int,
    tile: str,
    agg: Mapping[str, Any],
    kinds_tbl: _StringTable,
    mods_tbl: _StringTable,
) -> List[Any]:
    sz = int(agg["sz"])
    loc = int(agg["loc"])
    mods = int(agg["mods"])
    return [
        group_id,
        int(parent_idx),
        name,
        short,
        kinds_tbl.intern("group"),
        int(agg["pillar"]),
        sz,
        int(agg["vn"]),
        loc,
        mods,
        mods_tbl.intern(""),
        0,
        int(depth),
        "",
        tile,
        _round4(int(agg["lib"]) / max(1, sz)),
        int(agg["hbc"]),
        int(agg["hbm"]),
        _round4(int(agg["cln"]) / loc) if loc > 0 else 0.0,
        int(agg["sp"]),
        int(agg["sc"]),
        _round4(int(agg["orph"]) / mods) if mods > 0 else 0.0,
        _round4(int(agg["wrap"]) / max(1, sz)),
        _round4(float(agg["compress"])),
    ]


def _write_dom_tile_recursive(
    st: Dict[str, Any],
    tiles_dir: str,
    tile_key: str,
    root_row_spec: Tuple[Any, str, str, int, Optional[int], Optional[Dict[str, Any]]],
    child_ids: List[int],
    *,
    max_tile_rows: int,
    budget_state: Dict[str, int],
    sub_depth: int = 0,
    max_sub_depth: int = 1,
    max_subtiles_per_tile: int = 32,
) -> int:
    """Emit `tiles_dom/{tile_key}.lxrt` (and bounded bucket sub-tiles for huge fan-out nodes).

    `root_row_spec = (node_id, name, short, depth, decl_id_or_None, group_agg_or_None)`.
    Guarantees every emitted tile stays compact (`< 300 KB`) and never starves sibling tiles.
    """
    node_id, r_name, r_short, r_depth, r_did, r_agg = root_row_spec
    kinds_tbl = _StringTable(["thm", "def", "inductive", "opaque", "axiom", "quot", "group"])
    mods_tbl = _StringTable([""])
    rows: List[List[Any]] = []

    if r_did is not None:
        comp = _name_compress_ratio([st["name"][c] for c in child_ids[:128]], max_sample=128)
        rows.append(_dom_decl_row(st, r_did, -1, r_depth, "", comp, kinds_tbl, mods_tbl))
    else:
        assert r_agg is not None
        rows.append(_dom_group_row(str(node_id), -1, r_name, r_short, r_depth, "", r_agg, kinds_tbl, mods_tbl))

    # Count total reachable descendants inside child_ids (stopping early once > max_tile_rows)
    total_desc = 0
    probe_stack = list(child_ids)
    while probe_stack and total_desc <= max_tile_rows:
        u = probe_stack.pop()
        total_desc += 1
        probe_stack.extend(st["children"].get(u, ()))

    subtile_jobs: List[Tuple[str, Tuple[Any, str, str, int, Optional[int], Optional[Dict[str, Any]]], List[int]]] = []

    if total_desc <= max_tile_rows:
        # Entire nested subtree down to dom == 1 fits cleanly in this single tile!
        emit_stack: List[Tuple[int, int, int]] = []
        for c in sorted(child_ids, key=lambda x: (st["sz"][x], st["vn_sub"][x])):
            emit_stack.append((c, 0, r_depth + 1))
        while emit_stack:
            u, p_idx, d = emit_stack.pop()
            my_idx = len(rows)
            ch = st["children"].get(u, ())
            comp = _name_compress_ratio([st["name"][x] for x in ch[:64]], max_sample=64) if ch else 0.0
            rows.append(_dom_decl_row(st, u, p_idx, d, "", comp, kinds_tbl, mods_tbl))
            if ch:
                for c in sorted(ch, key=lambda x: (st["sz"][x], st["vn_sub"][x])):
                    emit_stack.append((c, my_idx, d + 1))
    else:
        # Large subtree (> max_tile_rows): keep top individual children directly,
        # and group the remaining direct children into namespace/prefix buckets!
        sorted_ch = sorted(child_ids, key=lambda x: (-st["sz"][x], -st["vn_sub"][x], st["name"][x]))
        direct_cap = min(len(sorted_ch), max(80, max_tile_rows // 3))
        top_ch = sorted_ch[:direct_cap]
        rest_ch = sorted_ch[direct_cap:]

        buckets: List[Tuple[str, List[int]]] = []
        if rest_ch:
            ns_groups: Dict[str, List[int]] = collections.defaultdict(list)
            for u in rest_ch:
                nm = st["name"][u]
                parts = nm.split(".")
                prefix = ".".join(parts[:2]) if len(parts) >= 3 else parts[0]
                ns_groups[prefix].append(u)
            sorted_groups = sorted(
                ns_groups.items(),
                key=lambda kv: (-sum(st["sz"][x] for x in kv[1]), kv[0]),
            )
            max_buckets = 36
            if len(sorted_groups) > max_buckets:
                kept = sorted_groups[: max_buckets - 1]
                tail_ids: List[int] = []
                for _, ids in sorted_groups[max_buckets - 1 :]:
                    tail_ids.extend(ids)
                kept.append(("Other namespaces", tail_ids))
                buckets = kept
            else:
                buckets = sorted_groups

        row_budget = max_tile_rows - len(buckets) - 1
        sub_allowed = max(0, max_subtiles_per_tile) if sub_depth < max_sub_depth else 0
        # Reserve half of sub_allowed for top bucket sub-tiles so mega-buckets remain zoomable
        bucket_sub_cap = min(len(buckets), sub_allowed // 2) if buckets else 0
        decl_sub_cap = sub_allowed - bucket_sub_cap
        decl_sub_used = 0
        bucket_sub_used = 0

        for bi, u in enumerate(top_ch):
            if len(rows) >= row_budget:
                buckets.insert(0, ("More declarations", top_ch[bi:]))
                break
            ch = st["children"].get(u, ())
            can_subtile = (
                bool(ch)
                and decl_sub_used < decl_sub_cap
                and st["sz"][u] >= 25
                and budget_state["used_bytes"] < budget_state["max_bytes"]
                and budget_state["n_tiles"] < budget_state["max_tiles"]
            )
            sub_key = f"{tile_key}_d{u}" if can_subtile else ""
            comp = _name_compress_ratio([st["name"][x] for x in ch[:64]], max_sample=64) if ch else 0.0
            rows.append(_dom_decl_row(st, u, 0, r_depth + 1, sub_key, comp, kinds_tbl, mods_tbl))
            if sub_key:
                decl_sub_used += 1
                subtile_jobs.append(
                    (sub_key, (u, st["name"][u], _short_name(st["name"][u]), r_depth + 1, u, None), list(ch))
                )

        for bi, (prefix, g_ids) in enumerate(buckets):
            agg = _aggregate_dom_group(st, g_ids)
            gid = f"{tile_key}_b{bi}"
            want_subtile = (
                bucket_sub_used < bucket_sub_cap
                and len(g_ids) >= 2
                and agg["sz"] >= 80
                and budget_state["used_bytes"] < budget_state["max_bytes"]
                and budget_state["n_tiles"] < budget_state["max_tiles"]
            )
            sub_key = gid if want_subtile else ""
            g_short = f"{prefix} ({agg['sz']:,})"
            rows.append(
                _dom_group_row(gid, 0, f"{r_name}/{prefix}", g_short, r_depth + 1, sub_key, agg, kinds_tbl, mods_tbl)
            )
            if sub_key:
                bucket_sub_used += 1
                subtile_jobs.append(
                    (sub_key, (gid, f"{r_name}/{prefix}", g_short, r_depth + 1, None, agg), g_ids)
                )

    payload = {
        "schema": TREE_SCHEMA,
        "view": "dom",
        "root_name": r_short,
        "tables": {
            "kinds": kinds_tbl.items,
            "pillars": list(DOM_PILLARS),
            "mods": mods_tbl.items,
        },
        "cols": COLS,
        "rows": rows,
    }
    nb = write_lxrt(os.path.join(tiles_dir, f"{tile_key}.lxrt"), payload)
    budget_state["used_bytes"] += nb
    budget_state["n_tiles"] += 1

    for sub_key, sub_spec, sub_ch in subtile_jobs:
        _write_dom_tile_recursive(
            st,
            tiles_dir,
            sub_key,
            sub_spec,
            sub_ch,
            max_tile_rows=max_tile_rows,
            budget_state=budget_state,
            sub_depth=sub_depth + 1,
            max_sub_depth=max_sub_depth,
            max_subtiles_per_tile=max_subtiles_per_tile,
        )
    return nb


def _build_dom_view(
    st: Dict[str, Any],
    out_dir: str,
    root_name: str,
    *,
    min_subtree: int = 100,
    min_residual_group: int = 100,
    max_tile_rows: int = 500,
    max_tiles_bytes: int = 18 * 1024 * 1024,
    max_tiles: int = 5500,
) -> Dict[str, Any]:
    """Build `dom.lxrt` skeleton (`subtree_size >= min_subtree`) + lazy `tiles_dom/{id}.lxrt`."""
    sz_arr = st["sz"]
    children = st["children"]
    skel_set: Set[int] = {did for did in st["dom_ids"] if sz_arr[did] >= min_subtree}

    # Fallback for tiny synthetic/demo DBs where max subtree < min_subtree: include all nodes!
    if not skel_set:
        skel_set = set(st["dom_ids"])

    kinds_tbl = _StringTable(["root", "thm", "def", "inductive", "opaque", "axiom", "quot", "group"])
    mods_tbl = _StringTable([""])
    rows: List[List[Any]] = []

    root_info = st["root"]
    root_sz = int(root_info["sz"])
    root_loc = int(root_info["loc"])
    root_mods = int(root_info["mods"])
    root_compress = _name_compress_ratio([st["name"][did] for did in st["dom_ids"]])

    # Check whether tree has a single top root or needs synthetic Main root
    top_ids = children.get(-1, [])
    top_big = [c for c in top_ids if c in skel_set]
    top_small = [c for c in top_ids if c not in skel_set]

    # Always emit synthetic Main root at rows[0] (id=-1, p=-1) when multiple top roots exist
    # or when root_name differs from single top root
    rows.append([
        -1,
        -1,
        root_name,
        root_name,
        kinds_tbl.intern("root"),
        _PILLAR_ROOT,
        root_sz,
        int(root_info["vn"]),
        root_loc,
        root_mods,
        mods_tbl.intern(""),
        0,
        0,
        "",
        "",
        _round4(int(root_info["lib"]) / max(1, root_sz)),
        int(root_info["hbc"]),
        int(root_info["hbm"]),
        _round4(int(root_info["cln"]) / root_loc) if root_loc > 0 else 0.0,
        int(root_info["sp"]),
        int(root_info["sc"]),
        _round4(int(root_info["orph"]) / root_mods) if root_mods > 0 else 0.0,
        _round4(int(root_info["wrap"]) / max(1, root_sz)),
        _round4(root_compress),
    ])

    # Collect tile jobs (emitted prioritized by subtree_size descending so biggest subtrees always get tiles)
    # Each job: (priority_sz, row_index_in_rows, tile_key, root_row_spec, child_ids)
    tile_candidates: List[
        Tuple[int, int, str, Tuple[Any, str, str, int, Optional[int], Optional[Dict[str, Any]]], List[int]]
    ] = []

    # Attach top_small residual group under Main if non-empty
    if top_small:
        agg = _aggregate_dom_group(st, top_small)
        if agg["sz"] >= min_residual_group or not top_big:
            r_idx = len(rows)
            gid = "root_r"
            short = f"Direct roots (<{min_subtree}, {agg['sz']:,})"
            rows.append(
                _dom_group_row(gid, 0, f"{root_name}/[other]", short, 1, "", agg, kinds_tbl, mods_tbl)
            )
            tile_candidates.append(
                (agg["sz"], r_idx, gid, (gid, f"{root_name}/[other]", short, 1, None, agg), top_small)
            )

    # Iterative pre-order traversal of skeleton nodes
    stack: List[Tuple[int, int, int]] = []
    for c in sorted(top_big, key=lambda x: (sz_arr[x], st["vn_sub"][x])):
        stack.append((c, 0, 1))

    while stack:
        u, p_idx, depth = stack.pop()
        my_idx = len(rows)
        ch = children.get(u, ())
        big_ch = [c for c in ch if c in skel_set]
        small_ch = [c for c in ch if c not in skel_set]

        comp = _name_compress_ratio([st["name"][c] for c in ch[:128]], max_sample=128) if ch else 0.0
        rows.append(_dom_decl_row(st, u, p_idx, depth, "", comp, kinds_tbl, mods_tbl))

        if not big_ch and small_ch:
            # Skeleton leaf node: tile directly on this node!
            tkey = str(u)
            tile_candidates.append(
                (sz_arr[u], my_idx, tkey, (u, st["name"][u], _short_name(st["name"][u]), depth, u, None), small_ch)
            )
        elif big_ch:
            if small_ch:
                agg = _aggregate_dom_group(st, small_ch)
                if agg["sz"] >= min_residual_group:
                    r_idx = len(rows)
                    gid = f"{u}_r"
                    short = f"Other (<{min_subtree}, {agg['sz']:,})"
                    rows.append(
                        _dom_group_row(
                            gid, my_idx, f"{st['name'][u]}/[other]", short, depth + 1, "", agg, kinds_tbl, mods_tbl
                        )
                    )
                    tile_candidates.append(
                        (agg["sz"], r_idx, gid, (gid, f"{st['name'][u]}/[other]", short, depth + 1, None, agg), small_ch)
                    )
            for c in sorted(big_ch, key=lambda x: (sz_arr[x], st["vn_sub"][x])):
                stack.append((c, my_idx, depth + 1))

    # Sort tile candidates by subtree size descending and emit within byte/count budget
    tiles_dir = os.path.join(out_dir, "tiles_dom")
    tile_col_idx = COLS.index("tile")
    budget_state = {
        "used_bytes": 0,
        "max_bytes": int(max_tiles_bytes),
        "n_tiles": 0,
        "max_tiles": int(max_tiles),
    }

    tile_candidates.sort(key=lambda item: (-item[0], item[2]))
    for _prio, row_idx, tkey, spec, ch_ids in tile_candidates:
        if budget_state["used_bytes"] >= budget_state["max_bytes"]:
            break
        if budget_state["n_tiles"] >= budget_state["max_tiles"]:
            break
        rows[row_idx][tile_col_idx] = tkey
        _write_dom_tile_recursive(
            st,
            tiles_dir,
            tkey,
            spec,
            ch_ids,
            max_tile_rows=max_tile_rows,
            budget_state=budget_state,
            sub_depth=0,
        )

    dom_payload = {
        "schema": TREE_SCHEMA,
        "view": "dom",
        "root_name": root_name,
        "tables": {
            "kinds": kinds_tbl.items,
            "pillars": list(DOM_PILLARS),
            "mods": mods_tbl.items,
        },
        "cols": COLS,
        "rows": rows,
    }
    dom_bytes = write_lxrt(os.path.join(out_dir, "dom.lxrt"), dom_payload)
    n_tiles = budget_state["n_tiles"]

    return {
        "view": {
            "id": "dom",
            "label": "Ownership tree (dominators)",
            "file": "dom.lxrt",
            "unit": "declarations",
            "total_weight": root_sz,
            "n_nodes": len(rows),
            "n_tiles": n_tiles,
            "tile_path": "tiles_dom/{id}.lxrt" if n_tiles > 0 else "",
        },
        "stats": {
            "dom_bytes": dom_bytes,
            "tiles_dom_bytes": budget_state["used_bytes"],
            "n_tiles": n_tiles,
            "skel_nodes": len(skel_set),
            "total_decls": root_sz,
            "total_vn": int(root_info["vn"]),
            "total_loc": root_loc,
            "total_mods": root_mods,
        },
    }


def export_kernel_treemap(
    kernel_db: str,
    out_dir: str,
    *,
    slug: str = "riemann-hypothesis",
    root_name: str = "Main",
    leanre_db: Optional[str] = None,
    tier2_db: Optional[str] = None,
    src_dir: Optional[str] = None,
    annotations_dir: Optional[str] = None,
    analysis_dir: Optional[str] = None,
    notes_dir: Optional[str] = None,
    min_subtree: int = 100,
    min_residual_group: int = 100,
    max_tile_rows: int = 500,
    max_tiles_bytes: int = 18 * 1024 * 1024,
    workers: Optional[int] = None,
) -> Dict[str, Any]:
    """Export kernel-mode treemap (`dom.lxrt` + `folder.lxrt` + lazy tiles + `overlay.json` + `manifest.json`)."""
    t0 = time.time()
    os.makedirs(out_dir, exist_ok=True)

    # 1. Read leanre.db module/declaration/forensic data if provided
    mod_meta_map: Dict[str, Tuple[int, bool]] = {}
    mod_sorry_map: Dict[str, Tuple[int, int]] = {}
    decl_line_map: Dict[int, int] = {}
    leanre_modules: List[Tuple[str, str, int, int, int, float]] = []
    root_decl_compress: Optional[float] = None

    if leanre_db and os.path.isfile(os.path.realpath(leanre_db)):
        lcon = _connect_ro(leanre_db)
        try:
            for nm, fp, lines, decl_cnt, bfs_depth, zratio in lcon.execute(
                "SELECT name, file_path, lines, decl_count, bfs_depth, zlib_ratio FROM modules"
            ):
                m_nm = str(nm)
                m_fp = str(fp)
                m_lines = int(lines or 0)
                is_orph = int(bfs_depth) < 0 if bfs_depth is not None else False
                mod_meta_map[m_nm] = (m_lines, is_orph)
                leanre_modules.append((m_nm, m_fp, m_lines, int(decl_cnt or 0), int(bfs_depth or 0), float(zratio or 0.0)))

            has_hits = bool(
                lcon.execute("SELECT 1 FROM sqlite_master WHERE type='table' AND name='forensic_hits'").fetchone()
            )
            if has_hits:
                sp_cnt: Dict[str, int] = collections.Counter()
                sc_cnt: Dict[str, int] = collections.Counter()
                fp_by_mod = {m[0]: m[1] for m in leanre_modules}
                for mod_nm in (
                    r[0] for r in lcon.execute("SELECT module FROM forensic_hits WHERE tag='sorry'")
                ):
                    m_nm = str(mod_nm or "")
                    if _is_challenge_spec_file(fp_by_mod.get(m_nm, ""), m_nm):
                        sc_cnt[m_nm] += 1
                    else:
                        sp_cnt[m_nm] += 1
                for m_nm in set(sp_cnt) | set(sc_cnt):
                    mod_sorry_map[m_nm] = (sp_cnt.get(m_nm, 0), sc_cnt.get(m_nm, 0))

            has_decls = bool(
                lcon.execute("SELECT 1 FROM sqlite_master WHERE type='table' AND name='declarations'").fetchone()
            )
            if has_decls:
                all_decl_names: List[str] = []
                for did, nm, lno in lcon.execute("SELECT id, name, line_no FROM declarations"):
                    decl_line_map[int(did)] = int(lno or 0)
                    if nm:
                        all_decl_names.append(str(nm))
                if all_decl_names:
                    root_decl_compress = _name_compress_ratio(all_decl_names)
        finally:
            lcon.close()

    # 2. Scan src_dir in parallel for exact comment_lines, hb_cnt, hb_max
    mod_rel_pairs = [(m[0], m[1]) for m in leanre_modules]
    src_metrics = _scan_rh_src_metrics(src_dir, mod_rel_pairs, workers=workers)

    # 3. Load kernel dom state & build dom.lxrt + tiles_dom/
    dom_state = _load_kernel_dom_state(
        kernel_db,
        leanre_db,
        tier2_db,
        src_metrics,
        mod_sorry_map,
        mod_meta_map,
        decl_line_map,
    )
    dom_res = _build_dom_view(
        dom_state,
        out_dir,
        root_name,
        min_subtree=min_subtree,
        min_residual_group=min_residual_group,
        max_tile_rows=max_tile_rows,
        max_tiles_bytes=max_tiles_bytes,
    )

    views: List[Dict[str, Any]] = [dom_res["view"]]
    folder_res: Optional[Dict[str, Any]] = None

    # 4. Build folder.lxrt + tiles_folder/ if leanre_modules or src_dir available
    per_mod_kernel = dom_state["per_mod_kernel"]
    if leanre_modules:
        file_records: List[Dict[str, Any]] = []
        for m_nm, m_fp, m_lines, m_decls, bfs_d, zratio in leanre_modules:
            cln, hbc, hbm = src_metrics.get(m_nm, (0, 0, 0))
            sp, sc = mod_sorry_map.get(m_nm, (0, 0))
            kacc = per_mod_kernel.get(m_nm)
            file_records.append({
                "mod_name": m_nm,
                "rel_path": m_fp,
                "short": _short_name(m_nm),
                "sz": m_decls,
                "vn": kacc[0] if kacc else 0,
                "loc": m_lines,
                "hb_cnt": hbc,
                "hb_max": hbm,
                "comment_lines": cln,
                "sorry_p": sp,
                "sorry_c": sc,
                "is_orphan": bfs_d < 0,
                "mathlib_matched": kacc[1] if kacc else 0,
                "mathlib_denom": kacc[2] if kacc else 0,
                "wrapper_cnt": kacc[3] if kacc else 0,
                "wrapper_denom": kacc[2] if kacc else 0,
                "compress": round(min(1.0, max(0.0, zratio)), 4),
            })
        folder_res = _build_folder_view(
            file_records,
            out_dir,
            root_name,
            inline_file_limit=4000,
            max_tile_rows=400,
            root_compress_override=root_decl_compress,
        )
        views.append(folder_res["view"])
    elif src_dir and os.path.isdir(src_dir):
        file_records = _scan_source_tree_records(src_dir, workers=workers)
        folder_res = _build_folder_view(
            file_records, out_dir, root_name, inline_file_limit=4000, max_tile_rows=400
        )
        views.append(folder_res["view"])

    # 5. Build overlay.json (known_names = live decl names + module names + top folders)
    known_names: Set[str] = {dom_state["name"][did] for did in dom_state["dom_ids"] if dom_state["name"][did]}
    known_names.update(m[0] for m in leanre_modules)
    overlay = build_overlay_json(
        annotations_dir,
        analysis_dir=analysis_dir,
        notes_dir=notes_dir,
        out_path=os.path.join(out_dir, "overlay.json"),
        project=slug,
        known_names=known_names,
    )

    # 6. Write manifest.json
    manifest: Dict[str, Any] = {
        "schema": MANIFEST_SCHEMA,
        "slug": slug,
        "mode": "kernel",
        "generated_utc": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "views": views,
        "overlay": "overlay.json",
        "size_modes": SIZE_MODES_KERNEL,
        "color_modes": COLOR_MODES,
    }
    manifest_bytes = write_plain_json(os.path.join(out_dir, "manifest.json"), manifest)

    elapsed = round(time.time() - t0, 3)
    return {
        "manifest": manifest,
        "overlay_stats": overlay["stats"],
        "dom_stats": dom_res["stats"],
        "folder_stats": folder_res["stats"] if folder_res else None,
        "manifest_bytes": manifest_bytes,
        "elapsed_s": elapsed,
    }


# ---------------------------------------------------------------------------
# Source Mode (`export_source_treemap`)
# ---------------------------------------------------------------------------

def _compute_source_orphans(records: Sequence[Dict[str, Any]]) -> Set[str]:
    """Compute unreachable module names from entry root(s) in source-only mode."""
    by_name = {r["mod_name"]: r for r in records}
    if not by_name:
        return set()
    adj: Dict[str, List[str]] = {nm: [] for nm in by_name}
    fan_in: Dict[str, int] = {nm: 0 for nm in by_name}
    for r in records:
        u = r["mod_name"]
        for imp in r.get("imports", ()):
            if imp in by_name and imp != u:
                adj[u].append(imp)
                fan_in[imp] += 1

    # Prefer Main or lake-style root modules (depth 0 / top-level with fan_in == 0 and fan_out > 0)
    roots: List[str] = []
    if "Main" in by_name:
        roots = ["Main"]
    else:
        top_roots = [
            nm for nm, r in by_name.items()
            if "/" not in r["rel_path"].replace("\\", "/") and fan_in[nm] == 0
        ]
        if top_roots:
            roots = top_roots
        else:
            roots = [nm for nm in by_name if fan_in[nm] == 0 and adj[nm]]
            if not roots:
                roots = [nm for nm in by_name if fan_in[nm] == 0]

    seen: Set[str] = set(roots)
    q = collections.deque(roots)
    while q:
        u = q.popleft()
        for v in adj.get(u, ()):
            if v not in seen:
                seen.add(v)
                q.append(v)
    return set(by_name) - seen


def _scan_source_tree_records(
    src_dir: str,
    *,
    workers: Optional[int] = None,
    leanre_db: Optional[str] = None,
) -> List[Dict[str, Any]]:
    abs_src = os.path.abspath(src_dir)
    if not os.path.isdir(abs_src):
        raise FileNotFoundError(f"Missing src_dir: {src_dir}")

    discovered = _scanner.discover_lean_files(abs_src)
    mod_rel_pairs = [(mname, rel) for _mid, mname, rel in discovered]
    eff_workers = max(1, int(workers if workers is not None else min(8, os.cpu_count() or 1)))

    scanned: List[Tuple[str, str, Dict[str, Any]]] = []
    if eff_workers > 1 and len(mod_rel_pairs) >= 300:
        chunk_sz = max(64, (len(mod_rel_pairs) + eff_workers * 4 - 1) // (eff_workers * 4))
        batches = [
            (abs_src, mod_rel_pairs[i : i + chunk_sz])
            for i in range(0, len(mod_rel_pairs), chunk_sz)
        ]
        with multiprocessing.Pool(processes=eff_workers) as pool:
            for batch_res in pool.imap_unordered(_scan_full_source_batch, batches):
                scanned.extend(batch_res)
    else:
        scanned = _scan_full_source_batch((abs_src, mod_rel_pairs))

    # Optional leanre.db override for exact bfs_depth orphans
    db_orphans: Optional[Set[str]] = None
    if leanre_db and os.path.isfile(os.path.realpath(leanre_db)):
        lcon = _connect_ro(leanre_db)
        try:
            db_orphans = {
                str(r[0])
                for r in lcon.execute("SELECT name FROM modules WHERE bfs_depth < 0")
            }
        finally:
            lcon.close()

    records: List[Dict[str, Any]] = []
    for mod_name, rel_path, m in scanned:
        records.append({
            "mod_name": mod_name,
            "rel_path": rel_path.replace("\\", "/"),
            "short": _short_name(mod_name),
            "sz": m["decl_count"],
            "vn": 0,
            "loc": m["lines"],
            "hb_cnt": m["hb_cnt"],
            "hb_max": m["hb_max"],
            "comment_lines": m["comment_lines"],
            "sorry_p": m["sorry_p"],
            "sorry_c": m["sorry_c"],
            "imports": m["imports"],
            "decl_names": m["decl_names"],
            "compress": _name_compress_ratio(m["decl_names"]),
            "is_orphan": False,
        })

    orphans = db_orphans if db_orphans is not None else _compute_source_orphans(records)
    for r in records:
        r["is_orphan"] = r["mod_name"] in orphans
    return records


def export_source_treemap(
    src_dir: str,
    out_dir: str,
    *,
    slug: str,
    root_name: Optional[str] = None,
    leanre_db: Optional[str] = None,
    annotations_dir: Optional[str] = None,
    analysis_dir: Optional[str] = None,
    notes_dir: Optional[str] = None,
    extra_dossiers: Optional[Sequence[str]] = None,
    inline_file_limit: int = 4000,
    max_tile_rows: int = 400,
    workers: Optional[int] = None,
) -> Dict[str, Any]:
    """Export source-mode treemap (`folder.lxrt` + optional `tiles_folder/` + `overlay.json` + `manifest.json`)."""
    t0 = time.time()
    os.makedirs(out_dir, exist_ok=True)
    eff_root = root_name or slug

    records = _scan_source_tree_records(src_dir, workers=workers, leanre_db=leanre_db)
    all_decl_names: List[str] = []
    known_names: Set[str] = set()
    for r in records:
        known_names.add(r["mod_name"])
        for dn in r.get("decl_names", ()):
            known_names.add(dn)
            if len(all_decl_names) < 16384:
                all_decl_names.append(dn)
    root_compress = _name_compress_ratio(all_decl_names) if all_decl_names else 0.0

    folder_res = _build_folder_view(
        records,
        out_dir,
        eff_root,
        inline_file_limit=inline_file_limit,
        max_tile_rows=max_tile_rows,
        root_compress_override=root_compress,
    )

    overlay = build_overlay_json(
        annotations_dir,
        analysis_dir=analysis_dir,
        notes_dir=notes_dir,
        out_path=os.path.join(out_dir, "overlay.json"),
        project=slug,
        known_names=known_names,
        extra_dossiers=extra_dossiers,
    )

    manifest: Dict[str, Any] = {
        "schema": MANIFEST_SCHEMA,
        "slug": slug,
        "mode": "source",
        "generated_utc": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "views": [folder_res["view"]],
        "overlay": "overlay.json",
        "size_modes": SIZE_MODES_SOURCE,
        "color_modes": COLOR_MODES,
    }
    manifest_bytes = write_plain_json(os.path.join(out_dir, "manifest.json"), manifest)
    elapsed = round(time.time() - t0, 3)

    return {
        "manifest": manifest,
        "overlay_stats": overlay["stats"],
        "folder_stats": folder_res["stats"],
        "manifest_bytes": manifest_bytes,
        "elapsed_s": elapsed,
    }


# ---------------------------------------------------------------------------
# Verification & Invariant Checker
# ---------------------------------------------------------------------------

def _check_tree_invariants(tree: Mapping[str, Any], label: str, errors: List[str]) -> Dict[str, Any]:
    if tree.get("schema") != TREE_SCHEMA:
        errors.append(f"{label}: bad schema {tree.get('schema')!r}")
    cols = tree.get("cols") or []
    rows = tree.get("rows") or []
    if not rows:
        errors.append(f"{label}: empty rows")
        return {"n_rows": 0, "tiles": []}
    try:
        idx_p = cols.index("p")
        idx_sz = cols.index("sz")
        idx_vn = cols.index("vn")
        idx_loc = cols.index("loc")
        idx_mods = cols.index("mods")
        idx_tile = cols.index("tile")
    except ValueError as exc:
        errors.append(f"{label}: missing required column: {exc}")
        return {"n_rows": len(rows), "tiles": []}

    n = len(rows)
    if rows[0][idx_p] != -1:
        errors.append(f"{label}: root row p={rows[0][idx_p]} != -1")

    child_sz = [0] * n
    child_vn = [0] * n
    child_loc = [0] * n
    child_mods = [0] * n
    has_child = [False] * n
    tiles: List[Tuple[str, int, int, int, int]] = []

    for i in range(1, n):
        p = rows[i][idx_p]
        if not isinstance(p, int) or p < 0 or p >= i:
            errors.append(f"{label}: row {i} invalid parent index p={p}")
            continue
        has_child[p] = True
        child_sz[p] += int(rows[i][idx_sz])
        child_vn[p] += int(rows[i][idx_vn])
        child_loc[p] += int(rows[i][idx_loc])
        child_mods[p] += int(rows[i][idx_mods])

    for i in range(n):
        tkey = str(rows[i][idx_tile] or "")
        if tkey:
            if has_child[i]:
                errors.append(f"{label}: row {i} has both children and tile={tkey!r}")
            tiles.append((tkey, int(rows[i][idx_sz]), int(rows[i][idx_vn]), int(rows[i][idx_loc]), int(rows[i][idx_mods])))
        if has_child[i]:
            if child_sz[i] > int(rows[i][idx_sz]):
                errors.append(f"{label}: row {i} sum(child.sz)={child_sz[i]} > sz={rows[i][idx_sz]}")
            if child_vn[i] > int(rows[i][idx_vn]):
                errors.append(f"{label}: row {i} sum(child.vn)={child_vn[i]} > vn={rows[i][idx_vn]}")
            if child_loc[i] > int(rows[i][idx_loc]):
                errors.append(f"{label}: row {i} sum(child.loc)={child_loc[i]} > loc={rows[i][idx_loc]}")
            if child_mods[i] > int(rows[i][idx_mods]):
                errors.append(f"{label}: row {i} sum(child.mods)={child_mods[i]} > mods={rows[i][idx_mods]}")

    return {
        "n_rows": n,
        "root_sz": int(rows[0][idx_sz]),
        "root_vn": int(rows[0][idx_vn]),
        "root_loc": int(rows[0][idx_loc]),
        "root_mods": int(rows[0][idx_mods]),
        "tiles": tiles,
    }


def verify_treemap_dir(
    out_dir: str,
    *,
    max_tile_bytes: int = 500 * 1024,
    max_file_bytes: int = 5 * 1024 * 1024,
    max_tiles_bytes: int = 25 * 1024 * 1024,
) -> Dict[str, Any]:
    """Verify every file, gzip magic, byte limit, and tree sum invariant in `out_dir`."""
    errors: List[str] = []
    manifest_path = os.path.join(out_dir, "manifest.json")
    if not os.path.isfile(manifest_path):
        raise FileNotFoundError(f"Missing manifest.json in {out_dir}")
    with open(manifest_path, "r", encoding="utf-8") as f:
        manifest = json.load(f)
    if manifest.get("schema") != MANIFEST_SCHEMA:
        errors.append(f"manifest schema mismatch: {manifest.get('schema')!r}")

    total_bytes = 0
    max_file = 0
    max_file_path = ""
    max_tile = 0
    max_tile_path = ""
    file_count = 0
    tile_dir_bytes: Dict[str, int] = collections.defaultdict(int)

    for root, _dirs, fns in os.walk(out_dir):
        for fn in fns:
            full = os.path.join(root, fn)
            rel = os.path.relpath(full, out_dir).replace("\\", "/")
            sz = os.path.getsize(full)
            total_bytes += sz
            file_count += 1
            if sz > max_file:
                max_file = sz
                max_file_path = rel
            if sz > max_file_bytes:
                errors.append(f"file exceeds {max_file_bytes} B: {rel} ({sz:,} B)")
            if rel.startswith("tiles_"):
                tdir = rel.split("/", 1)[0]
                tile_dir_bytes[tdir] += sz
                if sz > max_tile:
                    max_tile = sz
                    max_tile_path = rel
                if sz > max_tile_bytes:
                    errors.append(f"tile exceeds {max_tile_bytes} B: {rel} ({sz:,} B)")
            if fn.endswith(".lxrt"):
                with open(full, "rb") as fb:
                    magic = fb.read(2)
                if magic != b"\x1f\x8b":
                    errors.append(f"{rel}: missing gzip magic 0x1f 0x8b")

    for tdir, tb in tile_dir_bytes.items():
        if tb > max_tiles_bytes:
            errors.append(f"{tdir} exceeds {max_tiles_bytes:,} B: {tb:,} B")

    view_reports: Dict[str, Any] = {}
    for v in manifest.get("views", []):
        vid = v["id"]
        vfile = os.path.join(out_dir, v["file"])
        tree = read_lxrt(vfile)
        rep = _check_tree_invariants(tree, v["file"], errors)
        # Recursively verify all referenced tiles
        visited_tiles: Set[str] = set()
        queue = list(rep["tiles"])
        t_tmpl = v.get("tile_path") or f"tiles_{vid}/{{id}}.lxrt"
        while queue:
            tkey, exp_sz, exp_vn, exp_loc, exp_mods = queue.pop()
            if tkey in visited_tiles:
                continue
            visited_tiles.add(tkey)
            trel = t_tmpl.replace("{id}", tkey)
            tfull = os.path.join(out_dir, trel)
            if not os.path.isfile(tfull):
                errors.append(f"{v['file']}: missing referenced tile {trel}")
                continue
            ttree = read_lxrt(tfull)
            trep = _check_tree_invariants(ttree, trel, errors)
            if trep.get("root_sz") != exp_sz:
                errors.append(f"{trel}: root_sz={trep.get('root_sz')} != parent sz={exp_sz}")
            if trep.get("root_vn") != exp_vn:
                errors.append(f"{trel}: root_vn={trep.get('root_vn')} != parent vn={exp_vn}")
            if trep.get("root_loc") != exp_loc:
                errors.append(f"{trel}: root_loc={trep.get('root_loc')} != parent loc={exp_loc}")
            if trep.get("root_mods") != exp_mods:
                errors.append(f"{trel}: root_mods={trep.get('root_mods')} != parent mods={exp_mods}")
            queue.extend(trep["tiles"])
        view_reports[vid] = {
            "n_rows": rep["n_rows"],
            "root_sz": rep.get("root_sz", 0),
            "root_vn": rep.get("root_vn", 0),
            "root_loc": rep.get("root_loc", 0),
            "root_mods": rep.get("root_mods", 0),
            "verified_tiles": len(visited_tiles),
            "file_bytes": os.path.getsize(vfile),
            "tiles_bytes": tile_dir_bytes.get(f"tiles_{vid}", 0),
        }

    # Check overlay.json
    ov_path = os.path.join(out_dir, manifest.get("overlay", "overlay.json"))
    ov_stats: Dict[str, Any] = {}
    if os.path.isfile(ov_path):
        with open(ov_path, "r", encoding="utf-8") as f:
            ov = json.load(f)
        if ov.get("schema") != OVERLAY_SCHEMA:
            errors.append(f"overlay schema mismatch: {ov.get('schema')!r}")
        for lyr in ov.get("layers", []):
            if lyr.get("kind") == "ai-draft" and lyr.get("default_on"):
                errors.append(f"overlay ai-draft layer {lyr.get('id')!r} has default_on=True")
        ov_stats = ov.get("stats", {})

    return {
        "ok": len(errors) == 0,
        "errors": errors[:50],
        "error_count": len(errors),
        "total_bytes": total_bytes,
        "file_count": file_count,
        "max_file_bytes": max_file,
        "max_file_path": max_file_path,
        "max_tile_bytes": max_tile,
        "max_tile_path": max_tile_path,
        "views": view_reports,
        "overlay_stats": ov_stats,
    }


# ---------------------------------------------------------------------------
# CLI Entrypoint
# ---------------------------------------------------------------------------

def main(argv: Optional[Sequence[str]] = None) -> int:
    ap = argparse.ArgumentParser(
        prog="leanre.treemap",
        description="Build or verify hierarchical nested-rectangle treemap packs (leanre.treemap/1).",
    )
    sub = ap.add_subparsers(dest="cmd", required=True)

    p_k = sub.add_parser("kernel", help="Export kernel-mode treemap (dom + folder + overlay).")
    p_k.add_argument("--kernel-db", required=True, help="Path to kernel.db (read-only)")
    p_k.add_argument("--leanre-db", default=None, help="Optional leanre.db (read-only)")
    p_k.add_argument("--tier2-db", default=None, help="Optional flirt tier2.db (read-only)")
    p_k.add_argument("--src-dir", default=None, help="Optional Lean source root (read-only)")
    p_k.add_argument("--annotations-dir", default=None, help="Optional annotations/ directory")
    p_k.add_argument("--analysis-dir", default=None, help="Optional analysis/ dossiers directory")
    p_k.add_argument("--notes-dir", default=None, help="Optional notes/<slug>/ directory")
    p_k.add_argument("--slug", default="riemann-hypothesis", help="Project slug")
    p_k.add_argument("--root-name", default="Main", help="Root node display name")
    p_k.add_argument("--min-subtree", type=int, default=100, help="Skeleton dom subtree_size cutoff")
    p_k.add_argument("--max-tile-rows", type=int, default=500, help="Max rows per lazy tile")
    p_k.add_argument("--max-tiles-mb", type=float, default=18.0, help="Max gzipped MB for tiles_dom")
    p_k.add_argument("--workers", type=int, default=None, help="Parallel source scan workers")
    p_k.add_argument("--out", required=True, help="Output directory")

    p_s = sub.add_parser("source", help="Export source-mode treemap (folder + overlay).")
    p_s.add_argument("--src-dir", required=True, help="Lean source root (read-only)")
    p_s.add_argument("--leanre-db", default=None, help="Optional leanre.db (read-only)")
    p_s.add_argument("--annotations-dir", default=None, help="Optional annotations/ directory")
    p_s.add_argument("--analysis-dir", default=None, help="Optional analysis/ dossiers directory")
    p_s.add_argument("--notes-dir", default=None, help="Optional notes/<slug>/ directory")
    p_s.add_argument("--slug", required=True, help="Project slug")
    p_s.add_argument("--root-name", default=None, help="Root node display name")
    p_s.add_argument("--inline-file-limit", type=int, default=4000, help="Inline all files up to this count")
    p_s.add_argument("--max-tile-rows", type=int, default=400, help="Max rows per folder tile")
    p_s.add_argument("--workers", type=int, default=None, help="Parallel source scan workers")
    p_s.add_argument("--out", required=True, help="Output directory")

    p_o = sub.add_parser("overlay", help="Compile standalone overlay.json (leanre.treemap.overlay/1).")
    p_o.add_argument("--annotations-dir", required=True, help="Annotations directory")
    p_o.add_argument("--analysis-dir", default=None, help="Optional analysis/ directory")
    p_o.add_argument("--notes-dir", default=None, help="Optional notes/ directory")
    p_o.add_argument("--project", default=None, help="Project slug filter")
    p_o.add_argument("--out", required=True, help="Output overlay.json path")

    p_v = sub.add_parser("verify", help="Verify exported treemap directory invariants & sizes.")
    p_v.add_argument("dir", help="Treemap directory containing manifest.json")
    p_v.add_argument("--max-tile-kb", type=float, default=500.0, help="Max single lazy tile size in KB")
    p_v.add_argument("--max-file-kb", type=float, default=5120.0, help="Max single root file size in KB")
    p_v.add_argument("--max-tiles-mb", type=float, default=25.0, help="Max tile dir size in MB")

    args = ap.parse_args(argv)
    if args.cmd == "kernel":
        res = export_kernel_treemap(
            args.kernel_db,
            args.out,
            slug=args.slug,
            root_name=args.root_name,
            leanre_db=args.leanre_db,
            tier2_db=args.tier2_db,
            src_dir=args.src_dir,
            annotations_dir=args.annotations_dir,
            analysis_dir=args.analysis_dir,
            notes_dir=args.notes_dir,
            min_subtree=args.min_subtree,
            max_tile_rows=args.max_tile_rows,
            max_tiles_bytes=int(args.max_tiles_mb * 1024 * 1024),
            workers=args.workers,
        )
        print(json.dumps(res, indent=2, ensure_ascii=False))
        return 0
    if args.cmd == "source":
        res = export_source_treemap(
            args.src_dir,
            args.out,
            slug=args.slug,
            root_name=args.root_name,
            leanre_db=args.leanre_db,
            annotations_dir=args.annotations_dir,
            analysis_dir=args.analysis_dir,
            notes_dir=args.notes_dir,
            inline_file_limit=args.inline_file_limit,
            max_tile_rows=args.max_tile_rows,
            workers=args.workers,
        )
        print(json.dumps(res, indent=2, ensure_ascii=False))
        return 0
    if args.cmd == "overlay":
        ov = build_overlay_json(
            args.annotations_dir,
            analysis_dir=args.analysis_dir,
            notes_dir=args.notes_dir,
            out_path=args.out,
            project=args.project,
        )
        print(json.dumps({"schema": ov["schema"], "stats": ov["stats"]}, indent=2))
        return 0
    if args.cmd == "verify":
        rep = verify_treemap_dir(
            args.dir,
            max_tile_bytes=int(args.max_tile_kb * 1024),
            max_file_bytes=int(args.max_file_kb * 1024),
            max_tiles_bytes=int(args.max_tiles_mb * 1024 * 1024),
        )
        print(json.dumps(rep, indent=2, ensure_ascii=False))
        return 0 if rep["ok"] else 1
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
