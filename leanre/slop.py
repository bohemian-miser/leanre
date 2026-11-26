#!/usr/bin/env python3
"""leanre.slop — Ground-Truth Calibrated Lean Slopscore (0–100), Diff & Gap Engine.

Scores Lean 4 modules, directories, and full repositories on a 0–100 scale
(lower = cleaner / more Mathlib-idiomatic; <= 15 passes; 100 = maximally
glued-together / brute-forced / against-the-grain).

Calibrated empirically against BOTH:
  - 4 human Mathlib-style baselines (SpherePacking, Carleson, FLT, PNT), AND
  - 668 real merged refactor PRs on leanprover-community/riemann-hypothesis
    (reuse/Mathlib alignment, thin wrapper collapse inside clump files,
    redundant `attribute [local instance]`, twin structure unification,
    unused imports/fields, and brute-force tactic removal).

Five weighted pillars (formatting/hygiene hard-capped at <= 5 pts):
  1. library_grain (0–25): Blanket `import Mathlib`, bloated import preambles
     (>= 25 imports), `attribute [local instance]` / `attribute [-instance]`
     typeclass workarounds, custom macro/notation hacks, low library reuse.
  2. fragmentation (0–25): Inline & file-level thin forwarding wrappers
     (`first | exact`, `vn == 1` renaming shells, `clump:auto` uncollapsed
     wrappers), cross-repo duplicate theorem statements, twin copy-paste
     structures sharing >= 50% field names, sibling `zdict` boilerplate repeat.
  3. brute_force   (0–25): `maxHeartbeats` hammering, `exact_by_kernel` /
     `Kernel.isDefEq` / `run_tac` bypasses, kernel AST / `type_nodes` blowups,
     numbered `have h1..hN` soup, giant unsegmented `have` walls, deep
     positional `⟨_,_,_,_,_⟩` unpacking, `erw`/`convert`/`change`/`simp [*]`
     type-fighting, numeric tables & `decide +kernel`.
  4. scaffolding   (0–20): Zero-live-kernel modules & dead intra-file decls,
     over-bundled `structure`s (>= 10 fields + unread fields), oversized
     signatures (>= 10 lines), `UnusedSlot*`/`*junk*`/`:= True`/placeholder
     stubs, dropped hypotheses, `set_option linter.* false`.
  5. hygiene        (0–5): Hard-capped light context & line-width signal.

Schemas:
  - `leanre.slop/1`       (per-project report: `data/slop.json`)
  - `leanre.slop_diff/1`  (commit-vs-commit or audit-round diff: `data/cleanup_diff.json`)
  - `leanre.audits/1`     (PR-extensible blind audit-round ledger: `notes/audits/`)
"""
from __future__ import annotations

import argparse
import collections
import datetime
import hashlib
import json
import math
import multiprocessing
import os
import re
import sqlite3
import statistics
import subprocess
import sys
import time
import zlib
from typing import Any, Dict, List, Mapping, Optional, Sequence, Set, Tuple

_HERE = os.path.dirname(os.path.abspath(__file__))
_REPO_ROOT = os.path.abspath(os.path.join(_HERE, ".."))
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)

try:
    import pulse as _pulse
except ImportError:  # pragma: no cover
    from leanre import pulse as _pulse  # type: ignore

SLOP_SCHEMA = "leanre.slop/1"
SLOP_DIFF_SCHEMA = "leanre.slop_diff/1"
AUDITS_SCHEMA = "leanre.audits/1"
EVOLUTION_SCHEMA = "leanre.rh_evolution/1"

PILLAR_CAPS: Dict[str, int] = {
    "library_grain": 25,
    "fragmentation": 25,
    "brute_force": 25,
    "scaffolding": 20,
    "hygiene": 5,
}

_FORBIDDEN_HOST_PATH_RE = re.compile(
    r"(?:"
    + "/" + "usr" + "/" + "local" + "/" + r"[^/\s]+/home/"
    + "|" + "/" + "usr" + "/" + "local" + "/" + "google"
    + "|" + "/" + "ho" + r"me/[A-Za-z0-9_.-]+"
    + "|" + "/" + "Us" + r"ers/[A-Za-z0-9_.-]+"
    + ")"
)

_RE_IMPORT = re.compile(r"^[ \t]*(?:public\s+)?import\s+([^\s;]+)", re.M)
_RE_MATHLIB_WHOLE = re.compile(r"^[ \t]*(?:public\s+)?import\s+Mathlib[ \t]*$", re.M)
_RE_DECL = re.compile(
    r"^[ \t]*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|unsafe|partial|scoped|local)\s+)*"
    r"(theorem|lemma|def|abbrev|structure|class|inductive|instance)\b(?:\s+([A-Za-z_][A-Za-z0-9_.'₀-₉]*))?",
    re.M,
)
_RE_HB = re.compile(r"\bset_option\s+maxHeartbeats\s+(\d+)")
_RE_NEG_INST = re.compile(r"\battribute\s*\[\s*-instance\b")
_RE_ATTR_LOCAL_INST = re.compile(r"\battribute\s*\[\s*local\s+instance\b")
_RE_LINTER_OFF = re.compile(r"\bset_option\s+linter\.[A-Za-z0-9_.]+\s+false\b")
_RE_KERNEL_TAC = re.compile(r"\b(?:exact_by_kernel|Kernel\.isDefEq|run_tac)\b")
_RE_RESTATE = re.compile(r":=\s*by\s+first\s*\|\s*exact\b")
_RE_THIN_WRAP_BODY = re.compile(
    r"^:=\s*(?:by\s+(?:first\s*\|\s*exact|exact|simpa\s+using|apply)\s+[^\n;]+|"
    r"[A-Za-z_][A-Za-z0-9_.']*(?:\s+[A-Za-z0-9_.'()]+){0,6})\s*$"
)
_RE_NUM_HAVE = re.compile(r"\bhave\s+h[a-zA-Z]?[0-9]+\b")
_RE_ANY_HAVE = re.compile(r"\bhave\b")
_RE_ANON_TUP5 = re.compile(r"⟨[^⟩\n]{0,200},[^⟩\n]{0,200},[^⟩\n]{0,200},[^⟩\n]{0,200},[^⟩\n]{0,200}⟩")
_RE_TYPE_FIGHT = re.compile(r"\b(?:erw|convert|change)\b|\bsimp\s*\[\s*\*\s*\]")
_RE_DECIDE_KERNEL = re.compile(r"\bdecide\s*\+\s*kernel\b|\bkernel_decide\b")
_RE_MACRO = re.compile(
    r"^[ \t]*(?:(?:local|scoped)\s+)?(?:macro|macro_rules|syntax|elab|elab_rules|declare_syntax_cat)\b",
    re.M,
)
_RE_NOTATION = re.compile(
    r"^[ \t]*(?:@\[[^\]]*\]\s*)*(local|scoped)?\s*(?:infix[lr]?|prefix|postfix|notation)\b",
    re.M,
)
_RE_STUB_ARTIFACT = re.compile(
    r"\b(?:UnusedSlot\d+|junkEx|divXFl|cfJunk|cxJunk|mdlJunk|geoDegenerate|"
    r"[A-Za-z0-9_]*Placeholder\b|trivialMember|toyZeroLatticeDatum|toyRowsOfNumberField)\b"
    r"|:\s*Prop\s*:=\s*True\b"
    r"|:=\s*fun\s+(?:_\s+){2,}=>\s*True\b"
)
_RE_DROP_BINDER = re.compile(r"\bintro\s+_(?:\s+_)*\b|\bfun\s+(?:[A-Za-z0-9_]+\s+)*_(?:\s+_){2,}\s*=>")
_RE_FIELD_NAME = re.compile(r"^[ \t]*([A-Za-z_][A-Za-z0-9_']*)\s*:")
_RE_WS = re.compile(r"\s+")
_RE_BINDER_NORM = re.compile(r"([({\[])\s*[A-Za-z_][A-Za-z0-9_']*(?:\s+[A-Za-z_][A-Za-z0-9_']*)*\s*:")
_RE_DIGIT_LIT = re.compile(r"(?<![A-Za-z0-9_'])\d+(?:\.\d+)?(?![A-Za-z0-9_'])")
_RE_OPEN_PR_SCOPE = re.compile(r"\(([^)]{3,120})\)")
_RE_NUM_VARIANT = re.compile(r"^([A-Za-z_][A-Za-z0-9_]{3,}?)(?:[2-9]|Alt\d*|Aux\d*|Prime|Bis|Ter)$")

_SCORE_BINS: Tuple[Tuple[str, int, int], ...] = (
    ("0–15", 0, 15),
    ("16–30", 16, 30),
    ("31–45", 31, 45),
    ("46–60", 46, 60),
    ("61–75", 61, 75),
    ("76–100", 76, 100),
)

_TUP_MARK = "⟨".encode("utf-8")


def _sanitize_json(obj: Any) -> Any:
    if isinstance(obj, str):
        return _FORBIDDEN_HOST_PATH_RE.sub("<path>", obj) if _FORBIDDEN_HOST_PATH_RE.search(obj) else obj
    if isinstance(obj, list):
        return [_sanitize_json(v) for v in obj]
    if isinstance(obj, dict):
        return {k: _sanitize_json(v) for k, v in obj.items()}
    return obj


def _safe_write_json(out_path: str, obj: Any) -> int:
    if os.path.islink(out_path):
        raise ValueError(f"Refusing to write through symlink: {out_path}")
    parent = os.path.dirname(os.path.abspath(out_path))
    if parent:
        os.makedirs(parent, exist_ok=True)
    raw = json.dumps(_sanitize_json(obj), ensure_ascii=False, separators=(",", ":")).encode("utf-8")
    tmp = out_path + f".tmp.{os.getpid()}"
    with open(tmp, "wb") as f:
        f.write(raw)
    os.replace(tmp, out_path)
    return len(raw)


def _open_ro(path: str) -> sqlite3.Connection:
    real = os.path.realpath(path)
    if not os.path.isfile(real):
        raise FileNotFoundError(f"Missing SQLite database: {path}")
    conn = sqlite3.connect(f"file:{real}?mode=ro", uri=True)
    conn.execute("PRAGMA query_only=1")
    return conn


def _norm_stmt_hash(stmt_text: str) -> str:
    s = _RE_WS.sub(" ", stmt_text).strip()
    if len(s) < 24:
        return ""
    s_norm = _RE_BINDER_NORM.sub(r"\1:", s)
    return hashlib.sha1(s_norm.encode("utf-8", errors="ignore")).hexdigest()[:12]


def _struct_field_sig(fields: Sequence[str]) -> str:
    """Hash sorted field-name set for structures with >= 5 fields to spot twin copy-paste records."""
    if len(fields) < 5:
        return ""
    raw = ",".join(sorted(set(fields)))
    return hashlib.sha1(raw.encode("utf-8", errors="ignore")).hexdigest()[:10]


def extract_file_features(
    raw_bytes: bytes,
    rel_path: str = "",
    *,
    prev_zdict: Optional[bytes] = None,
) -> Dict[str, Any]:
    """Extract deterministic architectural-slop features from one `.lean` file."""
    if not raw_bytes:
        return {
            "lines": 0, "bytes": 0, "rep_pct": -1.0, "whole_mathlib": False,
            "imports": [], "import_cnt": 0, "mathlib_import_cnt": 0,
            "decl_count": 0, "thm_count": 0, "restate": False,
            "thin_wrap_cnt": 0, "is_clump": False, "twin_name_cnt": 0,
            "hb_cnt": 0, "hb_max": 0, "neg_inst": 0, "attr_local_inst": 0,
            "linter_off": 0, "kernel_tac": 0, "num_have": 0,
            "max_have_in_decl": 0, "anon_tup5": 0, "type_fight": 0,
            "decide_kernel": False, "macro_cnt": 0, "local_not": 0,
            "scoped_not": 0, "global_not": 0, "max_struct_fields": 0,
            "big_struct_cnt": 0, "struct_sigs": [], "max_decl_lines": 0,
            "max_sig_lines": 0, "big_sig_cnt": 0, "stub_hits": 0,
            "drop_binders": 0, "doc_decls": 0, "comment_pct": 0.0,
            "wide_line_pct": 0.0, "max_line_len": 0, "digit_pct": 0.0,
            "stmt_hashes": [], "ncr": 1.0,
        }

    text = raw_bytes.decode("utf-8", errors="replace")
    raw_lines = text.splitlines()
    n_lines = len(raw_lines)
    n_bytes = len(raw_bytes)
    is_clump = (b"clump:auto" in raw_bytes) or (b"scripts/clump.py" in raw_bytes)

    if (b"--" in raw_bytes) or (b"/-" in raw_bytes) or (b'"' in raw_bytes):
        code_text, comment_chars = _pulse.strip_lean_comments_and_strings(text)
    else:
        code_text, comment_chars = text, 0
    comment_pct = round(100.0 * comment_chars / max(1, len(text)), 2)

    rep_pct = -1.0
    if prev_zdict is not None and n_bytes <= 200_000:
        z_self = len(zlib.compress(raw_bytes, 4))
        if z_self > 0:
            co = zlib.compressobj(level=4, zdict=prev_zdict)
            z_with = len(co.compress(raw_bytes) + co.flush())
            rep_pct = max(0.0, min(100.0, 100.0 * (1.0 - z_with / z_self)))

    whole_mathlib = (b"import Mathlib" in raw_bytes) and bool(_RE_MATHLIB_WHOLE.search(code_text))
    imports = _RE_IMPORT.findall(code_text) if b"import " in raw_bytes else []
    import_cnt = len(imports)
    mathlib_import_cnt = sum(1 for imp in imports if imp.startswith("Mathlib."))

    hb_cnt = hb_max = 0
    if b"maxHeartbeats" in raw_bytes:
        hb_vals = [int(m.group(1)) for m in _RE_HB.finditer(code_text)]
        hb_cnt = len(hb_vals)
        hb_max = max(hb_vals) if hb_vals else 0

    neg_inst = len(_RE_NEG_INST.findall(code_text)) if b"-instance" in raw_bytes else 0
    attr_local_inst = len(_RE_ATTR_LOCAL_INST.findall(code_text)) if b"local instance" in raw_bytes else 0
    linter_off = len(_RE_LINTER_OFF.findall(code_text)) if b"linter." in raw_bytes else 0
    kernel_tac = (
        len(_RE_KERNEL_TAC.findall(code_text))
        if (b"exact_by_kernel" in raw_bytes or b"isDefEq" in raw_bytes or b"run_tac" in raw_bytes)
        else 0
    )

    num_have = len(_RE_NUM_HAVE.findall(code_text)) if b"have h" in raw_bytes else 0
    anon_tup5 = len(_RE_ANON_TUP5.findall(code_text)) if _TUP_MARK in raw_bytes else 0
    type_fight = (
        len(_RE_TYPE_FIGHT.findall(code_text))
        if (b"erw" in raw_bytes or b"convert" in raw_bytes or b"change" in raw_bytes or b"simp" in raw_bytes)
        else 0
    )
    decide_kernel = (b"decide" in raw_bytes) and bool(_RE_DECIDE_KERNEL.search(code_text))
    macro_cnt = (
        len(_RE_MACRO.findall(code_text))
        if (b"macro" in raw_bytes or b"syntax" in raw_bytes or b"elab" in raw_bytes)
        else 0
    )

    local_not = scoped_not = global_not = 0
    if b"notation" in raw_bytes or b"infix" in raw_bytes or b"prefix" in raw_bytes or b"postfix" in raw_bytes:
        for nm in _RE_NOTATION.finditer(code_text):
            sc = (nm.group(1) or "").strip()
            if sc == "local":
                local_not += 1
            elif sc == "scoped":
                scoped_not += 1
            else:
                global_not += 1

    decl_matches = list(_RE_DECL.finditer(code_text))
    decl_count = len(decl_matches)
    thm_count = 0
    thin_wrap_cnt = 0
    max_decl_lines = 0
    max_sig_lines = 0
    big_sig_cnt = 0
    max_struct_fields = 0
    big_struct_cnt = 0
    struct_sigs: List[str] = []
    max_have_in_decl = 0
    decl_names: List[str] = []
    stmt_hashes: List[str] = []

    for i, dm in enumerate(decl_matches):
        dkind = dm.group(1)
        dname = dm.group(2) or ""
        if dname:
            decl_names.append(dname)
        if dkind in ("theorem", "lemma"):
            thm_count += 1
        end_pos = decl_matches[i + 1].start() if i + 1 < decl_count else len(code_text)
        span = code_text[dm.start():end_pos]
        dl = span.count("\n") + 1
        if dl > max_decl_lines:
            max_decl_lines = dl

        if dkind == "structure":
            s_lines = span.splitlines()[1:]
            f_names: List[str] = []
            for sln in s_lines:
                st = sln.lstrip()
                if not st:
                    continue
                if st.startswith(("end ", "namespace ", "section ", "end")):
                    break
                if ":" in sln and not st.startswith(("where", "|", "deriving", "extends", "attribute")):
                    fm = _RE_FIELD_NAME.match(sln)
                    if fm:
                        f_names.append(fm.group(1))
            f_cnt = len(f_names)
            if f_cnt > max_struct_fields:
                max_struct_fields = f_cnt
            if f_cnt >= 10:
                big_struct_cnt += 1
            ssig = _struct_field_sig(f_names)
            if ssig:
                struct_sigs.append(ssig)
        else:
            if dl >= 40 and "have " in span:
                hc = len(_RE_ANY_HAVE.findall(span))
                if hc > max_have_in_decl:
                    max_have_in_decl = hc
            ci = span.find(":=")
            if ci > 0:
                sig = span[:ci]
                body = span[ci:].strip()
                sl = sig.count("\n") + 1
                if sl > max_sig_lines:
                    max_sig_lines = sl
                if sl >= 10:
                    big_sig_cnt += 1
                if dkind in ("theorem", "lemma"):
                    # Inline `first | exact` restate shims (catches uncollapsed wrappers inside clump files
                    # without false-positiving on idiomatic Mathlib 1-line term proofs or specializations!)
                    if "first | exact" in body:
                        thin_wrap_cnt += 1
                    colon_idx = sig.find(":")
                    if colon_idx >= 0:
                        sh = _norm_stmt_hash(sig[colon_idx + 1:])
                        if sh:
                            stmt_hashes.append(sh)

    # Detect numbered/variant twin definitions in same file (e.g. chainDesc + chainDesc4, Foo + FooAlt)
    name_set = {nm.rsplit(".", 1)[-1] for nm in decl_names}
    twin_name_cnt = 0
    for nm in name_set:
        vm = _RE_NUM_VARIANT.match(nm)
        if vm and vm.group(1) in name_set:
            twin_name_cnt += 1

    doc_decls = min(decl_count, text.count("/--")) if (b"/--" in raw_bytes and decl_count > 0) else 0
    restate = decl_count == 1 and thm_count == 1 and (b"first" in raw_bytes) and bool(_RE_RESTATE.search(code_text))
    stub_hits = len(_RE_STUB_ARTIFACT.findall(code_text)) if (
        b"UnusedSlot" in raw_bytes or b"Junk" in raw_bytes or b"junk" in raw_bytes
        or b"Placeholder" in raw_bytes or b"toy" in raw_bytes or b":= True" in raw_bytes or b"=> True" in raw_bytes
    ) else 0
    drop_binders = len(_RE_DROP_BINDER.findall(code_text)) if (b"intro _" in raw_bytes or b"_ _" in raw_bytes) else 0

    max_line_len = 0
    wide_cnt = 0
    for ln in raw_lines:
        ll = len(ln)
        if ll > max_line_len:
            max_line_len = ll
        if ll > 120:
            wide_cnt += 1
    wide_line_pct = round(100.0 * wide_cnt / max(1, n_lines), 1)

    digit_pct = 0.0
    if n_lines >= 40:
        nonspace = len(code_text) - code_text.count(" ") - code_text.count("\n") - code_text.count("\t")
        if nonspace > 0:
            dig_chars = sum(len(m.group(0)) for m in _RE_DIGIT_LIT.finditer(code_text))
            digit_pct = round(100.0 * dig_chars / nonspace, 1)

    ncr = 1.0
    if len(decl_names) >= 6:
        raw_nm = "\n".join(sorted(decl_names)).encode("utf-8")
        if raw_nm:
            ncr = round(min(1.0, len(zlib.compress(raw_nm, 4)) / len(raw_nm)), 4)

    return {
        "lines": n_lines,
        "bytes": n_bytes,
        "rep_pct": round(rep_pct, 1) if rep_pct >= 0 else -1.0,
        "whole_mathlib": whole_mathlib,
        "imports": imports,
        "import_cnt": import_cnt,
        "mathlib_import_cnt": mathlib_import_cnt,
        "decl_count": decl_count,
        "thm_count": thm_count,
        "restate": restate,
        "thin_wrap_cnt": thin_wrap_cnt,
        "is_clump": is_clump,
        "twin_name_cnt": twin_name_cnt,
        "hb_cnt": hb_cnt,
        "hb_max": hb_max,
        "neg_inst": neg_inst,
        "attr_local_inst": attr_local_inst,
        "linter_off": linter_off,
        "kernel_tac": kernel_tac,
        "num_have": num_have,
        "max_have_in_decl": max_have_in_decl,
        "anon_tup5": anon_tup5,
        "type_fight": type_fight,
        "decide_kernel": decide_kernel,
        "macro_cnt": macro_cnt,
        "local_not": local_not,
        "scoped_not": scoped_not,
        "global_not": global_not,
        "max_struct_fields": max_struct_fields,
        "big_struct_cnt": big_struct_cnt,
        "struct_sigs": struct_sigs,
        "max_decl_lines": max_decl_lines,
        "max_sig_lines": max_sig_lines,
        "big_sig_cnt": big_sig_cnt,
        "stub_hits": stub_hits,
        "drop_binders": drop_binders,
        "doc_decls": doc_decls,
        "comment_pct": comment_pct,
        "wide_line_pct": wide_line_pct,
        "max_line_len": max_line_len,
        "digit_pct": digit_pct,
        "stmt_hashes": stmt_hashes,
        "ncr": ncr,
    }


def score_features(
    feat: Mapping[str, Any],
    *,
    dup_max_mult: int = 1,
    dup_thm_cnt: int = 0,
    twin_struct_cnt: int = 0,
    kernel_live_decls: Optional[int] = None,
    kernel_dead_decls: int = 0,
    kernel_vn_per_line: float = 0.0,
    kernel_max_type_nodes: int = 0,
    kernel_mathlib_pct: Optional[float] = None,
    kernel_vn1_ratio: float = 0.0,
    kernel_unread_fields: int = 0,
) -> Dict[str, Any]:
    """Compute ground-truth calibrated 0–100 Against-the-Grain Lean Slopscore.

    Design invariants calibrated on 4 human Mathlib baselines + 668 merged RH PRs:
      - Human Mathlib baselines (SpherePacking, Carleson, FLT) stay cleanly <= 15.
      - Merged deslop PRs (wrapper collapse, deduplication, redundant local instance
        removal, Mathlib reuse, heartbeat removal, unused field pruning) measurably
        reduce module score.
      - Formatting / comments never exceed 5 pts.
    """
    reasons: List[str] = []
    n_lines = int(feat.get("lines") or 0)
    decl_count = int(feat.get("decl_count") or 0)
    thm_count = int(feat.get("thm_count") or 0)

    # 1. Library Grain (0–25): blanket Mathlib, bloated import walls, local/neg instance hacks, custom macros
    lib_pts = 0.0
    if feat.get("whole_mathlib"):
        lib_pts += 12.0
        reasons.append("blanket import Mathlib")
    else:
        mi = int(feat.get("mathlib_import_cnt") or 0)
        ti = int(feat.get("import_cnt") or 0)
        if mi >= 25 or (ti >= 35 and n_lines < 400):
            lib_pts += min(10.0, 4.0 + (max(mi, ti) - 25) * 0.25)
            reasons.append(f"bloated imports ({ti})")
    ni = int(feat.get("neg_inst") or 0)
    ali = int(feat.get("attr_local_inst") or 0)
    if ni > 0:
        lib_pts += min(14.0, 10.0 + ni * 2.0)
        reasons.append(f"attribute [-instance] ({ni})")
    if ali > 0:
        lib_pts += min(12.0, 5.0 + ali * 2.5)
        reasons.append(f"attribute [local instance] ({ali})")
    if kernel_mathlib_pct is not None and (kernel_live_decls or 0) >= 8 and kernel_mathlib_pct < 0.15:
        add = min(10.0, round(10.0 * (0.15 - kernel_mathlib_pct) / 0.15, 1))
        lib_pts += add
        if add >= 4.0:
            reasons.append(f"low library reuse ({round(kernel_mathlib_pct * 100)}%)")
    macro_cnt = int(feat.get("macro_cnt") or 0)
    if macro_cnt > 0:
        lib_pts += min(9.0, macro_cnt * 4.0)
        reasons.append(f"{macro_cnt} custom macro/syntax")
    g_not = int(feat.get("global_not") or 0)
    ls_not = int(feat.get("local_not") or 0) + int(feat.get("scoped_not") or 0)
    if g_not > 0:
        lib_pts += min(8.0, g_not * 5.0)
        reasons.append(f"{g_not} global notation")
    elif ls_not >= 3:
        lib_pts += min(5.0, ls_not * 1.2)
        reasons.append(f"{ls_not} local/scoped notations")
    lib_pts = min(25.0, lib_pts)

    # 2. Fragmentation & Gluing (0–25): thin wrappers (file & inline clump), dup statements, twin structs/variants
    frag_pts = 0.0
    tw_cnt = int(feat.get("thin_wrap_cnt") or 0)
    tw_ratio = tw_cnt / max(1, thm_count)
    if feat.get("restate"):
        frag_pts += 20.0
        reasons.append("restate shim (first | exact)")
    elif kernel_vn1_ratio >= 0.6 and (kernel_live_decls or 0) >= 1:
        frag_pts += 18.0
        reasons.append("1-node renaming shell")
    elif tw_cnt >= 3 and tw_ratio >= 0.25:
        frag_pts += min(16.0, 6.0 + tw_cnt * 0.8 + tw_ratio * 8.0)
        reasons.append(f"{tw_cnt} thin forwarding wrappers")
    elif tw_cnt >= 6:
        frag_pts += min(12.0, 4.0 + tw_cnt * 0.5)
        reasons.append(f"{tw_cnt} thin wrappers in clump")
    if feat.get("is_clump") and tw_cnt >= 2:
        frag_pts += 3.0
    rep_pct = float(feat.get("rep_pct", -1.0))
    if rep_pct >= 50.0:
        add = min(13.0, 13.0 * (rep_pct - 50.0) / 38.0)
        frag_pts += add
        if rep_pct >= 62.0:
            reasons.append(f"{round(rep_pct)}% neighbor repeat")
    if dup_max_mult >= 2:
        if dup_max_mult >= 10:
            frag_pts += 18.0
        elif dup_max_mult >= 4:
            frag_pts += 13.0
        else:
            frag_pts += 8.0
        reasons.append(f"dup statement ×{dup_max_mult}")
    elif dup_thm_cnt >= 2:
        frag_pts += 8.0
        reasons.append(f"{dup_thm_cnt} duplicate statements")
    if twin_struct_cnt >= 1:
        frag_pts += min(10.0, 6.0 + twin_struct_cnt * 2.0)
        reasons.append("twin copy-paste structure")
    tnc = int(feat.get("twin_name_cnt") or 0)
    if tnc >= 2:
        frag_pts += min(8.0, tnc * 2.5)
        reasons.append(f"{tnc} numbered/Alt twin decls")
    ncr = float(feat.get("ncr", 1.0))
    if decl_count >= 8 and ncr < 0.22:
        frag_pts += min(6.0, (0.22 - ncr) * 40.0)
    frag_pts = min(25.0, frag_pts)

    # 3. Compiler Hammering & Brute-Force Proof Terms (0–25)
    bf_pts = 0.0
    hb_cnt = int(feat.get("hb_cnt") or 0)
    hb_max = int(feat.get("hb_max") or 0)
    if hb_cnt > 0:
        mag = math.log10(max(200_000, hb_max)) - math.log10(200_000)
        bf_pts += min(22.0, 11.0 + 5.5 * max(0.0, mag))
        lbl = f"{hb_max // 1_000_000}M" if hb_max >= 1_000_000 else (f"{hb_max // 1_000}k" if hb_max >= 1_000 else str(hb_max))
        reasons.append(f"maxHeartbeats {lbl}")
    ktac = int(feat.get("kernel_tac") or 0)
    if ktac > 0:
        bf_pts += 18.0
        reasons.append("exact_by_kernel / run_tac bypass")
    if kernel_max_type_nodes >= 10_000:
        add = 18.0 if kernel_max_type_nodes >= 50_000 else 11.0
        bf_pts += add
        reasons.append(f"type AST {kernel_max_type_nodes // 1000}k nodes")
    if kernel_vn_per_line >= 500.0:
        add = 16.0 if kernel_vn_per_line >= 2000.0 else 9.0
        bf_pts += add
        reasons.append(f"proof AST {int(kernel_vn_per_line)}/line")
    num_have = int(feat.get("num_have") or 0)
    if num_have >= 4:
        bf_pts += min(15.0, 4.0 + math.log2(num_have) * 2.5)
        reasons.append(f"{num_have} numbered have h1..hN")
    max_hd = int(feat.get("max_have_in_decl") or 0)
    if max_hd >= 20 and float(feat.get("comment_pct") or 0.0) < 2.0:
        bf_pts += min(12.0, 6.0 + (max_hd - 20) * 0.25)
        reasons.append(f"{max_hd}-step have wall")
    anon_tup5 = int(feat.get("anon_tup5") or 0)
    if anon_tup5 >= 2:
        bf_pts += min(8.0, 2.5 + anon_tup5 * 1.4)
        reasons.append(f"{anon_tup5} 5+-tuple unpacks")
    tf_density = (100.0 * int(feat.get("type_fight") or 0)) / max(25, n_lines)
    if tf_density >= 5.0:
        bf_pts += min(10.0, (tf_density - 4.0) * 1.4)
        reasons.append("erw/convert/simp[*] churn")
    max_dl = int(feat.get("max_decl_lines") or 0)
    if max_dl >= 160 and float(feat.get("comment_pct") or 0.0) < 2.0:
        bf_pts += 12.0 if max_dl >= 320 else 7.0
        reasons.append(f"{max_dl}-line monolith decl")
    if feat.get("decide_kernel"):
        bf_pts += 8.0
        reasons.append("decide +kernel")
    if float(feat.get("digit_pct") or 0.0) >= 20.0 and n_lines >= 50:
        bf_pts += 12.0
        reasons.append(f"{feat.get('digit_pct')}% numeric table")
    bf_pts = min(25.0, bf_pts)

    # 4. Leftover Scaffolding & Over-Bundled Contracts (0–20)
    sc_pts = 0.0
    if kernel_live_decls is not None:
        if kernel_live_decls == 0 and decl_count > 0:
            sc_pts += 18.0
            reasons.append("0 live kernel decls")
        elif kernel_dead_decls >= 3:
            dead_rat = kernel_dead_decls / max(1, kernel_live_decls + kernel_dead_decls)
            if dead_rat >= 0.35:
                sc_pts += min(14.0, 16.0 * dead_rat)
                reasons.append(f"{round(dead_rat * 100)}% dead decls")
    lo = int(feat.get("linter_off") or 0)
    if lo >= 2:
        sc_pts += min(10.0, 5.0 + lo * 2.0)
        reasons.append(f"linter disabled ({lo})")
    max_sf = int(feat.get("max_struct_fields") or 0)
    if max_sf >= 10:
        sc_pts += 15.0 if max_sf >= 35 else (10.0 if max_sf >= 18 else 6.0)
        reasons.append(f"{max_sf}-field structure")
    if kernel_unread_fields >= 2:
        sc_pts += min(10.0, 4.0 + kernel_unread_fields * 0.5)
        reasons.append(f"{kernel_unread_fields} unread struct fields")
    max_sl = int(feat.get("max_sig_lines") or 0)
    if max_sl >= 12:
        sc_pts += 9.0 if max_sl >= 24 else 5.0
        reasons.append(f"{max_sl}-line signature")
    stub_hits = int(feat.get("stub_hits") or 0)
    if stub_hits > 0:
        sc_pts += min(14.0, 8.0 + stub_hits * 2.0)
        reasons.append(f"stub/junk artifact ({stub_hits})")
    drop_b = int(feat.get("drop_binders") or 0)
    if drop_b >= 3:
        sc_pts += min(6.0, drop_b * 1.5)
        reasons.append(f"{drop_b} dropped hypotheses")
    sc_pts = min(20.0, sc_pts)

    # 5. Light Hygiene Signal (hard-capped at 5 pts — never dominates structural score!)
    hy_pts = 0.0
    if decl_count >= 2 and int(feat.get("doc_decls") or 0) == 0:
        hy_pts += 2.0
    if n_lines >= 40 and float(feat.get("comment_pct") or 0.0) == 0.0:
        hy_pts += 1.0
    if float(feat.get("wide_line_pct") or 0.0) >= 25.0 or int(feat.get("max_line_len") or 0) >= 220:
        hy_pts += 2.0
    hy_pts = min(5.0, hy_pts)

    raw_sum = lib_pts + frag_pts + bf_pts + sc_pts + hy_pts
    # Boost only when substantial structural against-the-grain signals fire (>= 14 structural pts)
    stretched = raw_sum * 1.32 if (raw_sum - hy_pts) >= 14.0 else raw_sum
    total = int(round(min(100.0, stretched)))
    return {
        "score": total,
        "library_grain": round(lib_pts, 1),
        "fragmentation": round(frag_pts, 1),
        "brute_force": round(bf_pts, 1),
        "scaffolding": round(sc_pts, 1),
        "hygiene": round(hy_pts, 1),
        "reasons": reasons[:6],
    }


def score_lean_bytes_fast(raw_bytes: bytes, rel_path: str = "", *, prev_zdict: Optional[bytes] = None) -> int:
    """Single-file deterministic 0–100 slop score helper for treemap.py."""
    feat = extract_file_features(raw_bytes, rel_path=rel_path, prev_zdict=prev_zdict)
    return int(score_features(feat)["score"])


def _scan_dir_batch(args: Tuple[str, List[Tuple[str, List[Tuple[str, str]]]]]) -> List[Dict[str, Any]]:
    src_dir, dir_groups = args
    out: List[Dict[str, Any]] = []
    for _dir_rel, files in dir_groups:
        prev_raw: Optional[bytes] = None
        for rel_path, mod_name in files:
            full = os.path.join(src_dir, rel_path)
            try:
                with open(full, "rb") as f:
                    raw = f.read()
            except OSError:
                continue
            zdict = prev_raw[:16384] if prev_raw is not None else None
            feat = extract_file_features(raw, rel_path=rel_path, prev_zdict=zdict)
            feat["mod"] = mod_name
            feat["rel"] = rel_path
            out.append(feat)
            prev_raw = raw
    return out


def _load_kernel_module_stats(kernel_db: str) -> Dict[str, Dict[str, Any]]:
    out: Dict[str, Dict[str, Any]] = {}
    conn = _open_ro(kernel_db)
    try:
        tbls = {r[0] for r in conn.execute("SELECT name FROM sqlite_master WHERE type='table'")}
        if "decl_module" not in tbls or "decls" not in tbls:
            return out
        for mod, live_n, dead_n, sum_vn, max_tn, vn1_n in conn.execute(
            """
            SELECT dm.module,
                   SUM(CASE WHEN d.live_mask > 0 THEN 1 ELSE 0 END),
                   SUM(CASE WHEN d.live_mask = 0 THEN 1 ELSE 0 END),
                   SUM(CASE WHEN d.live_mask > 0 THEN COALESCE(d.value_nodes, 0) ELSE 0 END),
                   MAX(CASE WHEN d.live_mask > 0 THEN COALESCE(d.type_nodes, 0) ELSE 0 END),
                   SUM(CASE WHEN d.live_mask > 0 AND d.kind IN ('thm','theorem') AND d.value_nodes = 1 THEN 1 ELSE 0 END)
            FROM decl_module dm
            JOIN decls d ON d.id = dm.decl_id
            WHERE dm.module IS NOT NULL AND dm.module != ''
            GROUP BY dm.module
            """
        ):
            out[str(mod)] = {
                "live": int(live_n or 0),
                "dead": int(dead_n or 0),
                "sum_vn": int(sum_vn or 0),
                "max_tn": int(max_tn or 0),
                "vn1_ratio": round(float(vn1_n or 0) / max(1, int(live_n or 0)), 3),
                "dom_max": 0,
            }
        if "dom" in tbls:
            for mod, dom_max in conn.execute(
                """
                SELECT dm.module, MAX(COALESCE(dm2.subtree_size, 0))
                FROM decl_module dm
                JOIN dom dm2 ON dm2.decl_id = dm.decl_id AND dm2.tree_id = 0
                WHERE dm.module IS NOT NULL AND dm.module != ''
                GROUP BY dm.module
                """
            ):
                rec = out.get(str(mod))
                if rec is not None:
                    rec["dom_max"] = int(dom_max or 0)
    finally:
        conn.close()
    return out


def _git_head_meta(path: str) -> Dict[str, str]:
    for cand in (path, os.path.dirname(os.path.abspath(path))):
        if not cand or not os.path.isdir(cand):
            continue
        r = subprocess.run(
            ["git", "-C", cand, "log", "-1", "--format=%H\t%cI\t%s"],
            capture_output=True, text=True, check=False,
        )
        if r.returncode == 0 and r.stdout.strip():
            parts = r.stdout.strip().split("\t", 2)
            return {
                "commit": parts[0] if len(parts) > 0 else "",
                "date": parts[1][:10] if len(parts) > 1 else "",
                "subject": parts[2][:120] if len(parts) > 2 else "",
            }
    return {"commit": "", "date": "", "subject": ""}


def build_slop_report(
    src_dir: str,
    *,
    slug: str = "project",
    kernel_db: Optional[str] = None,
    workers: int = 0,
    keep_module_scores: bool = False,
) -> Dict[str, Any]:
    """Compute a complete `leanre.slop/1` report for a Lean 4 source directory."""
    t0 = time.monotonic()
    abs_src = os.path.abspath(src_dir)
    if not os.path.isdir(abs_src):
        raise FileNotFoundError(f"Missing src_dir: {src_dir}")

    by_dir: Dict[str, List[Tuple[str, str]]] = collections.defaultdict(list)
    for dp, dns, fns in os.walk(abs_src):
        dns[:] = sorted(d for d in dns if not d.startswith(".") and d != ".lake")
        for fn in sorted(fns):
            if not fn.endswith(".lean"):
                continue
            full = os.path.join(dp, fn)
            if os.path.islink(full):
                continue
            rel = os.path.relpath(full, abs_src).replace("\\", "/")
            mod = rel[:-5].replace("/", ".")
            drel = os.path.dirname(rel)
            by_dir[drel].append((rel, mod))

    dir_items = sorted(by_dir.items())
    n_files = sum(len(v) for _, v in dir_items)
    eff_workers = workers if workers > 0 else min(16, max(1, (os.cpu_count() or 2)))
    if n_files < 200:
        eff_workers = 1

    feats: List[Dict[str, Any]] = []
    if eff_workers <= 1 or len(dir_items) <= 1:
        feats = _scan_dir_batch((abs_src, dir_items))
    else:
        chunks: List[List[Tuple[str, List[Tuple[str, str]]]]] = [[] for _ in range(eff_workers)]
        for i, item in enumerate(dir_items):
            chunks[i % eff_workers].append(item)
        with multiprocessing.Pool(processes=eff_workers) as pool:
            for part in pool.map(_scan_dir_batch, [(abs_src, c) for c in chunks if c]):
                feats.extend(part)

    stmt_freq: Dict[str, int] = collections.Counter()
    struct_freq: Dict[str, int] = collections.Counter()
    mod_set: Set[str] = {f["mod"] for f in feats}
    indeg: Dict[str, int] = collections.Counter()
    for f in feats:
        for sh in set(f["stmt_hashes"]):
            stmt_freq[sh] += 1
        for ss in set(f["struct_sigs"]):
            struct_freq[ss] += 1
        for imp in f["imports"]:
            if imp in mod_set:
                indeg[imp] += 1

    k_stats: Dict[str, Dict[str, Any]] = {}
    has_kernel = False
    if kernel_db and os.path.isfile(kernel_db):
        k_stats = _load_kernel_module_stats(kernel_db)
        has_kernel = bool(k_stats)

    tot_lines = 0
    w_score = 0.0
    w_pillars: Dict[str, float] = {k: 0.0 for k in PILLAR_CAPS}
    mod_scores_list: List[int] = []
    bin_files = [0] * len(_SCORE_BINS)
    bin_lines = [0] * len(_SCORE_BINS)
    clean_lines = 0
    high_lines = 0
    metric_counts: Dict[str, int] = collections.Counter()
    dir_acc: Dict[str, Dict[str, Any]] = {}
    scored_rows: List[Dict[str, Any]] = []
    mod_score_map: Dict[str, int] = {}

    for f in feats:
        mod = f["mod"]
        lines = int(f["lines"])
        tot_lines += lines
        shs = f["stmt_hashes"]
        dup_mult = max((stmt_freq.get(sh, 1) for sh in shs), default=1)
        dup_cnt = sum(1 for sh in shs if stmt_freq.get(sh, 1) >= 2)
        twin_st = sum(1 for ss in f["struct_sigs"] if struct_freq.get(ss, 1) >= 2)

        ks = k_stats.get(mod) if has_kernel else None
        k_live = ks["live"] if ks is not None else (0 if has_kernel else None)
        k_dead = ks["dead"] if ks is not None else 0
        k_vpl = (ks["sum_vn"] / max(1, lines)) if (ks is not None and lines > 0) else 0.0
        k_tn = ks["max_tn"] if ks is not None else 0
        k_vn1 = ks["vn1_ratio"] if ks is not None else 0.0
        dom_max = ks["dom_max"] if ks is not None else 0

        sc = score_features(
            f,
            dup_max_mult=dup_mult,
            dup_thm_cnt=dup_cnt,
            twin_struct_cnt=twin_st,
            kernel_live_decls=k_live,
            kernel_dead_decls=k_dead,
            kernel_vn_per_line=k_vpl,
            kernel_max_type_nodes=k_tn,
            kernel_vn1_ratio=k_vn1,
        )
        s_val = int(sc["score"])
        mod_scores_list.append(s_val)
        if keep_module_scores:
            mod_score_map[mod] = s_val

        wt = max(1, lines)
        w_score += s_val * wt
        for pk in PILLAR_CAPS:
            w_pillars[pk] += float(sc[pk]) * wt
        if s_val <= 15:
            clean_lines += lines
        if s_val >= 50:
            high_lines += lines
        for bi, (_bl, lo, hi) in enumerate(_SCORE_BINS):
            if lo <= s_val <= hi:
                bin_files[bi] += 1
                bin_lines[bi] += lines
                break

        if f["whole_mathlib"]:
            metric_counts["whole_mathlib_files"] += 1
        if f["restate"]:
            metric_counts["restate_files"] += 1
        if f["thin_wrap_cnt"] > 0:
            metric_counts["thin_wrapper_decls"] += int(f["thin_wrap_cnt"])
        if f["is_clump"]:
            metric_counts["clump_files"] += 1
        if f["hb_cnt"] > 0:
            metric_counts["heartbeat_files"] += 1
        if f["neg_inst"] > 0:
            metric_counts["neg_inst_files"] += 1
        if f["attr_local_inst"] > 0:
            metric_counts["attr_local_inst_files"] += 1
        if f["linter_off"] >= 2:
            metric_counts["linter_off_files"] += 1
        if f["kernel_tac"] > 0:
            metric_counts["kernel_tac_files"] += 1
        if f["num_have"] >= 4:
            metric_counts["numbered_have_files"] += 1
        if f["big_struct_cnt"] > 0:
            metric_counts["big_struct_files"] += 1
        if f["big_sig_cnt"] > 0:
            metric_counts["big_sig_files"] += 1
        if f["stub_hits"] > 0:
            metric_counts["stub_files"] += 1
        if dup_mult >= 2:
            metric_counts["dup_stmt_files"] += 1
        if twin_st >= 1:
            metric_counts["twin_struct_files"] += 1
        if has_kernel and k_live == 0:
            metric_counts["zero_live_files"] += 1

        parts = f["rel"].split("/")
        d1 = parts[0] if len(parts) > 1 else "(root)"
        d2 = "/".join(parts[:2]) if len(parts) > 2 else d1
        d3 = "/".join(parts[:3]) if len(parts) > 3 else d2
        for dk in {d1, d2, d3}:
            da = dir_acc.get(dk)
            if da is None:
                da = {
                    "dir": dk, "level": dk.count("/") + (0 if dk == "(root)" else 1),
                    "files": 0, "lines": 0, "w_score": 0.0,
                    "restate": 0, "thin_wraps": 0, "hb": 0, "dups": 0,
                    "attr_linst": 0, "zero_live": 0,
                }
                dir_acc[dk] = da
            da["files"] += 1
            da["lines"] += lines
            da["w_score"] += s_val * wt
            if f["restate"]:
                da["restate"] += 1
            da["thin_wraps"] += int(f["thin_wrap_cnt"])
            if f["hb_cnt"] > 0:
                da["hb"] += 1
            if dup_mult >= 2:
                da["dups"] += 1
            if f["attr_local_inst"] > 0:
                da["attr_linst"] += 1
            if has_kernel and k_live == 0:
                da["zero_live"] += 1

        deg = indeg.get(mod, 0)
        impact = math.log2(2.0 + max(dom_max, deg * 5)) * math.log2(2.0 + lines)
        priority = round(s_val * impact, 1)
        if s_val >= 28 and lines >= 12:
            scored_rows.append({
                "mod": mod,
                "lines": lines,
                "score": s_val,
                "priority": priority,
                "indeg": deg,
                "dom_max": dom_max,
                "live": k_live,
                "pillars": {
                    "lib": sc["library_grain"],
                    "frag": sc["fragmentation"],
                    "bf": sc["brute_force"],
                    "scaf": sc["scaffolding"],
                    "hyg": sc["hygiene"],
                },
                "reasons": sc["reasons"],
            })

    tot_wt = max(1, sum(max(1, int(f["lines"])) for f in feats))
    corpus_score = round(w_score / tot_wt, 1)
    pillar_means = {k: round(w_pillars[k] / tot_wt, 1) for k in PILLAR_CAPS}
    mod_scores_sorted = sorted(mod_scores_list)
    med_score = round(statistics.median(mod_scores_sorted), 1) if mod_scores_sorted else 0.0
    p90_score = mod_scores_sorted[int(0.9 * (len(mod_scores_sorted) - 1))] if mod_scores_sorted else 0

    scored_rows.sort(key=lambda r: (-r["priority"], -r["score"], -r["lines"], r["mod"]))
    worst_pure = sorted(scored_rows, key=lambda r: (-r["score"], -r["lines"], r["mod"]))[:20]

    dir_list = []
    for dk, da in dir_acc.items():
        if da["lines"] <= 0 or da["level"] > 2:
            continue
        dir_list.append({
            "dir": dk,
            "level": da["level"],
            "files": da["files"],
            "lines": da["lines"],
            "score": round(da["w_score"] / max(1, da["lines"]), 1),
            "restate": da["restate"],
            "thin_wraps": da["thin_wraps"],
            "hb": da["hb"],
            "dups": da["dups"],
            "attr_linst": da["attr_linst"],
            "zero_live": da["zero_live"],
        })
    dir_list.sort(key=lambda d: (d["level"], -d["lines"], d["dir"]))

    l3_targets = [
        {
            "dir": da["dir"],
            "files": da["files"],
            "lines": da["lines"],
            "score": round(da["w_score"] / max(1, da["lines"]), 1),
            "restate": da["restate"],
            "thin_wraps": da["thin_wraps"],
            "hb": da["hb"],
            "dups": da["dups"],
            "attr_linst": da["attr_linst"],
        }
        for da in dir_acc.values()
        if da["level"] == 3 and da["lines"] >= 2000
    ]
    l3_targets.sort(key=lambda x: (-x["score"] * math.log2(2 + x["lines"]), -x["score"]))

    dup_clusters = sum(1 for c in stmt_freq.values() if c >= 2)
    dup_excess = sum(c - 1 for c in stmt_freq.values() if c >= 2)

    git_meta = _git_head_meta(abs_src)
    report: Dict[str, Any] = {
        "schema": SLOP_SCHEMA,
        "slug": slug,
        "generated_utc": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "elapsed_s": round(time.monotonic() - t0, 2),
        "has_kernel": has_kernel,
        "git": git_meta,
        "summary": {
            "score": corpus_score,
            "median_module_score": med_score,
            "p90_module_score": int(p90_score),
            "files": len(feats),
            "lines": tot_lines,
            "clean_lines_pct": round(100.0 * clean_lines / max(1, tot_lines), 1),
            "high_slop_lines_pct": round(100.0 * high_lines / max(1, tot_lines), 1),
            "dup_stmt_clusters": dup_clusters,
            "dup_stmt_excess": dup_excess,
            **{k: int(metric_counts[k]) for k in (
                "whole_mathlib_files", "restate_files", "thin_wrapper_decls",
                "clump_files", "heartbeat_files", "neg_inst_files",
                "attr_local_inst_files", "linter_off_files", "kernel_tac_files",
                "numbered_have_files", "big_struct_files", "big_sig_files",
                "stub_files", "dup_stmt_files", "twin_struct_files", "zero_live_files",
            )},
        },
        "pillars": pillar_means,
        "pillar_caps": PILLAR_CAPS,
        "histogram": {
            "labels": [b[0] for b in _SCORE_BINS],
            "files": bin_files,
            "lines": bin_lines,
        },
        "dirs": dir_list[:120],
        "l3_targets": l3_targets[:80],
        "hotspots": scored_rows[:60],
        "worst_modules": worst_pure,
    }
    if keep_module_scores:
        report["module_scores"] = mod_score_map
    return report


def diff_slop_reports(
    before: Mapping[str, Any],
    after: Mapping[str, Any],
    *,
    label_before: str = "",
    label_after: str = "",
    cold_gaps: Optional[List[Dict[str, Any]]] = None,
) -> Dict[str, Any]:
    """Compare two `leanre.slop/1` reports (e.g. original vs community cleanup, or audit round k -> k+1)."""
    bs = before.get("summary") or {}
    as_ = after.get("summary") or {}
    bp = before.get("pillars") or {}
    ap = after.get("pillars") or {}

    def _d(k: str) -> float:
        return round(float(as_.get(k, 0) or 0) - float(bs.get(k, 0) or 0), 1)

    pillar_deltas = {
        k: {
            "before": round(float(bp.get(k, 0) or 0), 1),
            "after": round(float(ap.get(k, 0) or 0), 1),
            "delta": round(float(ap.get(k, 0) or 0) - float(bp.get(k, 0) or 0), 1),
            "cap": PILLAR_CAPS[k],
        }
        for k in PILLAR_CAPS
    }

    b_dirs = {d["dir"]: d for d in (before.get("dirs") or [])}
    a_dirs = {d["dir"]: d for d in (after.get("dirs") or [])}
    all_d = sorted(set(b_dirs) | set(a_dirs))
    dir_diffs: List[Dict[str, Any]] = []
    for dk in all_d:
        bd = b_dirs.get(dk)
        ad = a_dirs.get(dk)
        if not bd and not ad:
            continue
        lvl = (ad or bd).get("level", 1)
        bl = int((bd or {}).get("lines", 0))
        al = int((ad or {}).get("lines", 0))
        bf = int((bd or {}).get("files", 0))
        af = int((ad or {}).get("files", 0))
        bsc = float((bd or {}).get("score", 0.0))
        asc = float((ad or {}).get("score", 0.0))
        dir_diffs.append({
            "dir": dk,
            "level": lvl,
            "files_before": bf,
            "files_after": af,
            "files_delta": af - bf,
            "lines_before": bl,
            "lines_after": al,
            "lines_delta": al - bl,
            "score_before": round(bsc, 1) if bd else None,
            "score_after": round(asc, 1) if ad else None,
            "score_delta": round(asc - bsc, 1) if (bd and ad) else None,
            "restate_delta": int((ad or {}).get("restate", 0)) - int((bd or {}).get("restate", 0)),
            "thin_wraps_delta": int((ad or {}).get("thin_wraps", 0)) - int((bd or {}).get("thin_wraps", 0)),
            "hb_delta": int((ad or {}).get("hb", 0)) - int((bd or {}).get("hb", 0)),
        })

    l1_diffs = sorted([d for d in dir_diffs if d["level"] == 1], key=lambda x: -max(x["lines_before"], x["lines_after"]))
    l2_both = [d for d in dir_diffs if d["level"] == 2 and d["score_delta"] is not None and d["lines_before"] >= 2000]
    most_improved = sorted(l2_both, key=lambda x: (x["score_delta"], x["lines_delta"]))[:12]
    most_regressed = sorted([d for d in l2_both if d["score_delta"] > 0], key=lambda x: (-x["score_delta"], -x["lines_after"]))[:10]

    def _snap(rep: Mapping[str, Any], s: Mapping[str, Any], lbl: str) -> Dict[str, Any]:
        return {
            "slug": rep.get("slug", ""),
            "label": lbl or rep.get("slug", ""),
            "git": rep.get("git") or {},
            "has_kernel": bool(rep.get("has_kernel")),
            "score": float(s.get("score", 0)),
            "files": int(s.get("files", 0)),
            "lines": int(s.get("lines", 0)),
            "clean_lines_pct": float(s.get("clean_lines_pct", 0)),
            "high_slop_lines_pct": float(s.get("high_slop_lines_pct", 0)),
            "restate_files": int(s.get("restate_files", 0)),
            "thin_wrapper_decls": int(s.get("thin_wrapper_decls", 0)),
            "heartbeat_files": int(s.get("heartbeat_files", 0)),
            "whole_mathlib_files": int(s.get("whole_mathlib_files", 0)),
            "neg_inst_files": int(s.get("neg_inst_files", 0)),
            "attr_local_inst_files": int(s.get("attr_local_inst_files", 0)),
            "kernel_tac_files": int(s.get("kernel_tac_files", 0)),
            "dup_stmt_excess": int(s.get("dup_stmt_excess", 0)),
            "big_struct_files": int(s.get("big_struct_files", 0)),
        }

    out = {
        "schema": SLOP_DIFF_SCHEMA,
        "generated_utc": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "before": _snap(before, bs, label_before or "before"),
        "after": _snap(after, as_, label_after or "after"),
        "deltas": {
            "score": _d("score"),
            "files": int(as_.get("files", 0)) - int(bs.get("files", 0)),
            "files_pct": round(100.0 * (int(as_.get("files", 0)) - int(bs.get("files", 0))) / max(1, int(bs.get("files", 0))), 1),
            "lines": int(as_.get("lines", 0)) - int(bs.get("lines", 0)),
            "lines_pct": round(100.0 * (int(as_.get("lines", 0)) - int(bs.get("lines", 0))) / max(1, int(bs.get("lines", 0))), 1),
            "restate_files": int(as_.get("restate_files", 0)) - int(bs.get("restate_files", 0)),
            "thin_wrapper_decls": int(as_.get("thin_wrapper_decls", 0)) - int(bs.get("thin_wrapper_decls", 0)),
            "heartbeat_files": int(as_.get("heartbeat_files", 0)) - int(bs.get("heartbeat_files", 0)),
            "whole_mathlib_files": int(as_.get("whole_mathlib_files", 0)) - int(bs.get("whole_mathlib_files", 0)),
            "neg_inst_files": int(as_.get("neg_inst_files", 0)) - int(bs.get("neg_inst_files", 0)),
            "attr_local_inst_files": int(as_.get("attr_local_inst_files", 0)) - int(bs.get("attr_local_inst_files", 0)),
            "kernel_tac_files": int(as_.get("kernel_tac_files", 0)) - int(bs.get("kernel_tac_files", 0)),
            "dup_stmt_excess": int(as_.get("dup_stmt_excess", 0)) - int(bs.get("dup_stmt_excess", 0)),
        },
        "pillars": pillar_deltas,
        "l1_dirs": l1_diffs,
        "most_improved_dirs": most_improved,
        "most_regressed_dirs": most_regressed,
    }
    if cold_gaps is not None:
        out["cold_gaps"] = cold_gaps
    return out


def compute_cold_gaps(
    slop_report: Mapping[str, Any],
    open_pr_titles: Sequence[str],
    *,
    limit: int = 25,
) -> List[Dict[str, Any]]:
    """Rank high-slop L3 directories with ZERO matching open upstream PRs (low-conflict deslop targets)."""
    hot_tokens: Set[str] = set()
    for title in open_pr_titles:
        t = str(title or "")
        for m in _RE_OPEN_PR_SCOPE.finditer(t):
            sc = m.group(1).strip().strip("/")
            for part in sc.split("/"):
                if len(part) >= 4:
                    hot_tokens.add(part.lower())
            hot_tokens.add(sc.lower())
        for tok in re.findall(r"[A-Za-z][A-Za-z0-9_]{5,}", t):
            hot_tokens.add(tok.lower())

    out: List[Dict[str, Any]] = []
    for d in (slop_report.get("l3_targets") or []):
        dpath = str(d.get("dir") or "")
        segs = [s.lower() for s in dpath.split("/") if s]
        leaf = segs[-1] if segs else ""
        is_hot = (dpath.lower() in hot_tokens) or (leaf in hot_tokens)
        out.append({**d, "open_pr_activity": "active" if is_hot else "cold"})
    cold = [x for x in out if x["open_pr_activity"] == "cold"]
    return cold[:limit]


def fetch_open_pr_titles_gh(repo: str = "leanprover-community/riemann-hypothesis", max_pages: int = 6) -> List[str]:
    titles: List[str] = []
    for page in range(1, max_pages + 1):
        r = subprocess.run(
            ["gh", "api", f"repos/{repo}/pulls?state=open&per_page=100&page={page}", "--jq", ".[].title"],
            capture_output=True, text=True, check=False, timeout=20,
        )
        if r.returncode != 0:
            break
        lines = [ln.strip() for ln in r.stdout.splitlines() if ln.strip()]
        if not lines:
            break
        titles.extend(lines)
        if len(lines) < 100:
            break
    return titles


def load_audits_dir(audits_dir: str) -> Tuple[Dict[str, Any], List[str]]:
    """Load & validate PR-extensible blind audit rounds (`notes/audits/`)."""
    errors: List[str] = []
    rounds: List[Dict[str, Any]] = []
    if not os.path.isdir(audits_dir) or os.path.islink(audits_dir):
        return {"schema": AUDITS_SCHEMA, "rounds": []}, errors

    files: List[str] = []
    base = os.path.join(audits_dir, "rounds.json")
    if os.path.isfile(base) and not os.path.islink(base):
        files.append(base)
    cdir = os.path.join(audits_dir, "contrib")
    if os.path.isdir(cdir) and not os.path.islink(cdir):
        for fn in sorted(os.listdir(cdir)):
            if fn.endswith(".json"):
                fp = os.path.join(cdir, fn)
                if os.path.isfile(fp) and not os.path.islink(fp):
                    files.append(fp)

    seen_ids: Set[str] = set()
    for fp in files:
        try:
            with open(fp, "r", encoding="utf-8") as f:
                raw = json.load(f)
        except (OSError, json.JSONDecodeError) as e:
            errors.append(f"{os.path.basename(fp)}: {e}")
            continue
        items = raw.get("rounds", []) if isinstance(raw, dict) and "rounds" in raw else ([raw] if isinstance(raw, dict) else [])
        for it in items:
            if not isinstance(it, dict):
                errors.append(f"{os.path.basename(fp)}: non-object audit round")
                continue
            rid = str(it.get("id") or "").strip()
            if not rid or rid in seen_ids:
                errors.append(f"{os.path.basename(fp)}: missing or duplicate id {rid!r}")
                continue
            seen_ids.add(rid)
            for req in ("project", "target", "author", "date", "summary"):
                if not str(it.get(req) or "").strip():
                    errors.append(f"{rid}: missing required field {req!r}")
            for sk in ("static_slop", "blind_slop"):
                if it.get(sk) is not None:
                    v = float(it[sk])
                    if not (0.0 <= v <= 100.0):
                        errors.append(f"{rid}: {sk} out of 0..100 ({v})")
            rounds.append(it)
    rounds.sort(key=lambda r: (str(r.get("date") or ""), int(r.get("round") or 0), str(r.get("id") or "")), reverse=True)
    return {"schema": AUDITS_SCHEMA, "rounds": rounds}, errors


_GRH_LIB_TOPICS: Dict[str, str] = {
    "Weil": "Weil representation, dual pairs, mixed/Fock models & periods",
    "Shimura": "Unitary Shimura varieties, integral models, deformation & congruence relations",
    "General": "Algebra, linear algebra, geometry, measure, analysis & number theory gaps",
    "Adelic": "Adeles, quotient measures, automorphic forms & simple trace formula",
    "DiscreteSeries": "Discrete series, Flensted-Jensen, Bruhat cells, characters & Bessel functions",
    "ClassField": "Global/local class field theory, Galois cohomology, Greenberg-Wiles & Hecke L-values",
    "Cohomology": "Etale & Hodge cohomology, proper base change, Woods Hole & projective line",
    "GaloisRep": "Attached Galois representations, base change & local-global compatibility",
    "PadicHodge": "Period rings, crystalline representations & Kisin modules",
    "SiegelWeil": "Siegel-Weil & Rallis formulas, theta towers & one-vector bounds",
    "PadicComparison": "p-adic Hodge-Tate comparison & descent",
    "LocalGL": "Local GL_n representation theory, Iwahori-Hecke, Green characters & Shintani",
    "CM": "CM fields, Chowla-Selberg formula & integrality",
    "GLn": "GL_n Schur modules & polynomial representations",
    "Cyclotomic": "Cyclotomic fields, Kolyvagin Euler systems & odd class-group bounds",
    "Analytic": "Primes in arithmetic progressions & Polya-Vinogradov quadratic twists",
}

_GRH_NEW_CHAPTERS: Tuple[Tuple[int, str, str, str], ...] = (
    (1, "Reduction", "chapter", "From one-sided bound to zeros, twisted lattices, heights & main inequality"),
    (2, "Derivatives", "chapter", "Prime-counting theta derivatives, formal groups, integral vacuum & sharpness"),
    (3, "UpperBound", "chapter", "Composite theta lifts, seesaw identity, divisibility & elementary divisors"),
    (4, "Spanning", "chapter", "Petersson-type second moment, unfolding, Bessel frames & spanning theorem"),
    (5, "Determinant", "chapter", "Regular twist families, exchange identity & norm of a chain of lifts"),
    (6, "OneLift", "chapter", "Single-lift volume height, comparison operator, false lifts & Hecke L-values"),
    (7, "Congruences", "chapter", "Galois congruences, Ribet-type first-order ties, Selmer bounds & crystalline lifting"),
    (8, "Appendix", "supplement", "Discrete series with a large spectral gap"),
)


def _count_code_nonblank_comment(raw_bytes: bytes) -> Tuple[int, int, int, int]:
    """Return `(total_lines, nonblank_lines, code_lines, comment_lines)` for one `.lean` file."""
    if not raw_bytes:
        return 0, 0, 0, 0
    text = raw_bytes.decode("utf-8", errors="replace")
    raw_lines = text.splitlines()
    total_lines = len(raw_lines)
    nonblank_lines = sum(1 for ln in raw_lines if ln.strip())
    if (b"--" in raw_bytes) or (b"/-" in raw_bytes):
        code_text, _ = _pulse.strip_lean_comments_and_strings(text)
        code_lines = sum(1 for ln in code_text.splitlines() if ln.strip())
        # Count lines containing any comment using stylometry's exact line tracker
        try:
            import stylometry as _stylo
            _, comment_lines, _ = _stylo.count_lean_comment_lines_and_heartbeats(raw_bytes)
        except Exception:
            comment_lines = max(0, nonblank_lines - code_lines)
    else:
        code_lines = nonblank_lines
        comment_lines = 0
    return total_lines, nonblank_lines, code_lines, comment_lines


def _evolution_line_worker(args: Tuple[str, List[str]]) -> Tuple[int, int, int, int, int, List[int]]:
    src_dir, rel_paths = args
    tot = nb = code = comm = hb = 0
    per_file: List[int] = []
    for rel in rel_paths:
        full = os.path.join(src_dir, rel)
        try:
            with open(full, "rb") as f:
                raw = f.read()
        except OSError:
            continue
        t_l, nb_l, c_l, cm_l = _count_code_nonblank_comment(raw)
        tot += t_l
        nb += nb_l
        code += c_l
        comm += cm_l
        if b"maxHeartbeats" in raw:
            if (b"--" in raw) or (b"/-" in raw):
                ct, _ = _pulse.strip_lean_comments_and_strings(raw.decode("utf-8", errors="replace"))
            else:
                ct = raw.decode("utf-8", errors="replace")
            hb += len(_RE_HB.findall(ct))
        per_file.append(t_l)
    return tot, nb, code, comm, hb, per_file


def _scan_stage_line_stats(src_dir: str, workers: int = 0) -> Dict[str, Any]:
    """Compute exact total, nonblank, code-only, comment lines and maxHeartbeats count."""
    abs_src = os.path.abspath(src_dir)
    rels: List[str] = []
    for dp, dn, fn in os.walk(abs_src):
        dn[:] = sorted(d for d in dn if d not in (".git", ".lake", "build", "__pycache__"))
        for f in sorted(fn):
            if f.endswith(".lean"):
                rels.append(os.path.relpath(os.path.join(dp, f), abs_src).replace(os.sep, "/"))
    eff_w = workers if workers > 0 else min(12, os.cpu_count() or 4)
    tot = nb = code = comm = hb = 0
    per_file: List[int] = []
    if eff_w > 1 and len(rels) >= 400:
        chunk = max(128, (len(rels) + eff_w * 4 - 1) // (eff_w * 4))
        batches = [(abs_src, rels[i : i + chunk]) for i in range(0, len(rels), chunk)]
        with multiprocessing.Pool(processes=eff_w) as pool:
            for t_l, nb_l, c_l, cm_l, hb_l, pf in pool.imap_unordered(_evolution_line_worker, batches):
                tot += t_l
                nb += nb_l
                code += c_l
                comm += cm_l
                hb += hb_l
                per_file.extend(pf)
    else:
        tot, nb, code, comm, hb, per_file = _evolution_line_worker((abs_src, rels))
    med = round(float(statistics.median(per_file)), 1) if per_file else 0.0
    return {
        "files": len(per_file),
        "lines": tot,
        "nonblank_lines": nb,
        "code_lines": code,
        "comment_lines": comm,
        "comment_pct": round(100.0 * comm / max(1, tot), 2),
        "max_heartbeats_overrides": hb,
        "median_file_lines": med,
    }


def _analyze_lib_new_boundary(
    src_dir: str,
    slop_report: Mapping[str, Any],
    *,
    slug: str,
    detailed: bool = True,
) -> Dict[str, Any]:
    """Compute exact `src/Lib` vs `src/New` architectural boundary metrics and domain/chapter rollups."""
    abs_src = os.path.abspath(src_dir)
    dir_scores = {
        str(d.get("dir") or ""): float(d.get("score") or 0.0)
        for d in (slop_report.get("dirs") or [])
        if isinstance(d, dict)
    }

    def _new_acc() -> Dict[str, Any]:
        return {
            "files": 0,
            "lines": 0,
            "nonblank_lines": 0,
            "code_lines": 0,
            "comment_lines": 0,
            "decls": 0,
            "mathlib_imports": 0,
            "mathlib_set": set(),
            "lib_imports": 0,
            "new_imports": 0,
            "total_imports": 0,
        }

    top_acc: Dict[str, Dict[str, Any]] = {"Lib": _new_acc(), "New": _new_acc(), "(root)": _new_acc()}
    l2_acc: Dict[str, Dict[str, Any]] = {}
    root_names: List[str] = []
    lib_root_files = 0
    lib_root_lines = 0
    new_root_files = 0
    new_root_lines = 0

    for dp, dn, fn in os.walk(abs_src):
        dn[:] = sorted(d for d in dn if d not in (".git", ".lake", "build", "__pycache__"))
        for f in sorted(fn):
            if not f.endswith(".lean"):
                continue
            full = os.path.join(dp, f)
            rel = os.path.relpath(full, abs_src).replace(os.sep, "/")
            parts = rel.split("/")
            try:
                with open(full, "rb") as fh:
                    raw = fh.read()
            except OSError:
                continue
            t_l, nb_l, c_l, cm_l = _count_code_nonblank_comment(raw)
            text = raw.decode("utf-8", errors="replace")
            if (b"--" in raw) or (b"/-" in raw) or (b'"' in raw):
                code_text, _ = _pulse.strip_lean_comments_and_strings(text)
            else:
                code_text = text
            imports = _RE_IMPORT.findall(code_text) if b"import " in raw else []
            decls = len(_RE_DECL.findall(code_text))
            m_imps = [imp for imp in imports if imp == "Mathlib" or imp.startswith("Mathlib.")]
            l_imps = [imp for imp in imports if imp == "Lib" or imp.startswith("Lib.")]
            n_imps = [imp for imp in imports if imp == "New" or imp.startswith("New.")]

            if len(parts) == 1:
                top_key = "(root)"
                root_names.append(parts[0])
                l2_key = ""
            else:
                top_key = parts[0] if parts[0] in ("Lib", "New") else "(root)"
                if len(parts) >= 3 and parts[0] in ("Lib", "New"):
                    l2_key = f"{parts[0]}/{parts[1]}"
                else:
                    l2_key = ""
                    if parts[0] == "Lib":
                        lib_root_files += 1
                        lib_root_lines += t_l
                    elif parts[0] == "New":
                        new_root_files += 1
                        new_root_lines += t_l

            for bucket_key, store in ((top_key, top_acc), (l2_key, l2_acc)):
                if not bucket_key:
                    continue
                acc = store.setdefault(bucket_key, _new_acc())
                acc["files"] += 1
                acc["lines"] += t_l
                acc["nonblank_lines"] += nb_l
                acc["code_lines"] += c_l
                acc["comment_lines"] += cm_l
                acc["decls"] += decls
                acc["total_imports"] += len(imports)
                acc["mathlib_imports"] += len(m_imps)
                acc["mathlib_set"].update(m_imps)
                acc["lib_imports"] += len(l_imps)
                acc["new_imports"] += len(n_imps)

    tot_files = sum(a["files"] for a in top_acc.values())
    tot_lines = max(1, sum(a["lines"] for a in top_acc.values()))
    tot_code = max(1, sum(a["code_lines"] for a in top_acc.values()))

    def _fmt_top(key: str, label: str) -> Dict[str, Any]:
        a = top_acc[key]
        return {
            "dir": key,
            "label": label,
            "files": a["files"],
            "lines": a["lines"],
            "nonblank_lines": a["nonblank_lines"],
            "code_lines": a["code_lines"],
            "comment_lines": a["comment_lines"],
            "comment_pct": round(100.0 * a["comment_lines"] / max(1, a["lines"]), 1),
            "share_lines_pct": round(100.0 * a["lines"] / tot_lines, 1),
            "share_code_pct": round(100.0 * a["code_lines"] / tot_code, 1),
            "slop_score": round(dir_scores.get(key, 0.0), 1),
            "decls": a["decls"],
            "total_imports": a["total_imports"],
            "mathlib_imports": a["mathlib_imports"],
            "distinct_mathlib_imports": len(a["mathlib_set"]),
            "lib_imports": a["lib_imports"],
            "new_imports": a["new_imports"],
        }

    lib_obj = _fmt_top("Lib", "Background results missing from Mathlib")
    new_obj = _fmt_top("New", "RH & Dirichlet GRH proof argument")
    root_obj = _fmt_top("(root)", "Headline statements & entry point")
    root_obj["names"] = sorted(root_names)

    lib_l2_keys = sorted(k for k in l2_acc if k.startswith("Lib/"))
    new_l2_keys = sorted(k for k in l2_acc if k.startswith("New/"))
    lib_obj["domain_count"] = len(lib_l2_keys)
    lib_obj["root_files_count"] = lib_root_files
    lib_obj["root_files_lines"] = lib_root_lines
    new_obj["folder_count"] = len(new_l2_keys)
    new_obj["root_files_count"] = new_root_files
    new_obj["root_files_lines"] = new_root_lines

    out: Dict[str, Any] = {
        "slug": slug,
        "total_files": tot_files,
        "total_lines": sum(a["lines"] for a in top_acc.values()),
        "total_code_lines": sum(a["code_lines"] for a in top_acc.values()),
        "lib": lib_obj,
        "new": new_obj,
        "root": root_obj,
    }

    if detailed:
        lib_domains: List[Dict[str, Any]] = []
        for dk in lib_l2_keys:
            name = dk.split("/", 1)[1]
            a = l2_acc[dk]
            lib_domains.append({
                "name": name,
                "dir": dk,
                "topic": _GRH_LIB_TOPICS.get(name, f"Reusable {name} background library"),
                "files": a["files"],
                "lines": a["lines"],
                "code_lines": a["code_lines"],
                "comment_pct": round(100.0 * a["comment_lines"] / max(1, a["lines"]), 1),
                "slop_score": round(dir_scores.get(dk, 0.0), 1),
                "decls": a["decls"],
                "mathlib_imports": a["mathlib_imports"],
                "distinct_mathlib_imports": len(a["mathlib_set"]),
                "new_imports": a["new_imports"],
            })
        lib_domains.sort(key=lambda x: (-x["lines"], x["name"]))
        out["lib_domains"] = lib_domains

        chapter_order = {nm: (ord_n, role, topic) for ord_n, nm, role, topic in _GRH_NEW_CHAPTERS}
        new_chapters: List[Dict[str, Any]] = []
        for dk in new_l2_keys:
            name = dk.split("/", 1)[1]
            a = l2_acc[dk]
            ord_n, role, topic = chapter_order.get(name, (99, "chapter", f"Proof section {name}"))
            new_chapters.append({
                "order": ord_n,
                "name": name,
                "dir": dk,
                "role": role,
                "topic": topic,
                "files": a["files"],
                "lines": a["lines"],
                "code_lines": a["code_lines"],
                "comment_pct": round(100.0 * a["comment_lines"] / max(1, a["lines"]), 1),
                "slop_score": round(dir_scores.get(dk, 0.0), 1),
                "decls": a["decls"],
                "lib_imports": a["lib_imports"],
                "mathlib_imports": a["mathlib_imports"],
            })
        new_chapters.sort(key=lambda x: (x["order"], -x["lines"], x["name"]))
        out["new_chapters"] = new_chapters
        new_obj["chapter_count"] = sum(1 for c in new_chapters if c["role"] == "chapter")
        new_obj["has_appendix"] = any(c["role"] == "supplement" for c in new_chapters)

    return out


def build_rh_evolution(
    stage_specs: Sequence[Mapping[str, Any]],
    *,
    workers: int = 0,
) -> Dict[str, Any]:
    """Build the 4-stage RH proof evolution telemetry (`leanre.rh_evolution/1`).

    Each entry in `stage_specs` supplies:
      - `stage_num`, `slug`, `label`, `short_label`, `branch`, `repo_url`, `license`
      - `src_dir`: local path to Lean source tree (read-only)
      - `slop_json`: optional precomputed `leanre.slop/1` report path (scanned if absent)
      - `slop_src_json`: optional source-only `leanre.slop/1` report path (for stage 1 apples-to-apples)
      - `is_current_main`: optional bool
      - `boundary_mode`: `"detailed"` | `"summary"` | `""`
    """
    stages_out: List[Dict[str, Any]] = []
    grh_boundary: Optional[Dict[str, Any]] = None
    compact_boundary: Optional[Dict[str, Any]] = None
    orig_ref: Optional[Dict[str, Any]] = None

    for idx, spec in enumerate(stage_specs, 1):
        src_dir = str(spec["src_dir"])
        slug = str(spec["slug"])
        slop_path = spec.get("slop_json")
        if slop_path and os.path.isfile(str(slop_path)):
            with open(str(slop_path), "r", encoding="utf-8") as fh:
                srep = json.load(fh)
        else:
            srep = build_slop_report(src_dir, slug=slug, workers=workers)

        slop_src_score: Optional[float] = None
        src_slop_path = spec.get("slop_src_json")
        if src_slop_path and os.path.isfile(str(src_slop_path)):
            with open(str(src_slop_path), "r", encoding="utf-8") as fh:
                srep_src = json.load(fh)
            slop_src_score = round(float((srep_src.get("summary") or {}).get("score") or 0.0), 1)

        lstats = _scan_stage_line_stats(src_dir, workers=workers)
        ssum = srep.get("summary") or {}
        spil = srep.get("pillars") or {}
        git_info = srep.get("git") or {}
        score_val = round(float(ssum.get("score") or 0.0), 1)

        st_obj: Dict[str, Any] = {
            "stage_num": int(spec.get("stage_num") or idx),
            "slug": slug,
            "label": str(spec.get("label") or slug),
            "short_label": str(spec.get("short_label") or spec.get("label") or slug),
            "branch": str(spec.get("branch") or ""),
            "repo_url": str(spec.get("repo_url") or ""),
            "commit": str(spec.get("commit") or git_info.get("commit") or ""),
            "date": str(spec.get("date") or git_info.get("date") or ""),
            "license": str(spec.get("license") or "None"),
            "is_current_main": bool(spec.get("is_current_main", False)),
            "has_kernel": bool(srep.get("has_kernel", False)),
            "files": int(ssum.get("files") or lstats["files"]),
            "lines": int(ssum.get("lines") or lstats["lines"]),
            "nonblank_lines": int(lstats["nonblank_lines"]),
            "code_lines": int(lstats["code_lines"]),
            "comment_lines": int(lstats["comment_lines"]),
            "comment_pct": float(lstats["comment_pct"]),
            "median_file_lines": float(lstats["median_file_lines"]),
            "slop_score": score_val,
            "slop_score_src": slop_src_score if slop_src_score is not None else score_val,
            "median_module_score": round(float(ssum.get("median_module_score") or 0.0), 1),
            "p90_module_score": int(ssum.get("p90_module_score") or 0),
            "clean_lines_pct": round(float(ssum.get("clean_lines_pct") or 0.0), 1),
            "high_slop_lines_pct": round(float(ssum.get("high_slop_lines_pct") or 0.0), 1),
            "pillars": {k: round(float(spil.get(k) or 0.0), 1) for k in PILLAR_CAPS},
            "metrics": {
                "whole_mathlib_files": int(ssum.get("whole_mathlib_files") or 0),
                "heartbeat_files": int(ssum.get("heartbeat_files") or 0),
                "max_heartbeats_overrides": int(lstats["max_heartbeats_overrides"]),
                "restate_files": int(ssum.get("restate_files") or 0),
                "thin_wrapper_decls": int(ssum.get("thin_wrapper_decls") or 0),
                "attr_local_inst_files": int(ssum.get("attr_local_inst_files") or 0),
                "dup_stmt_excess": int(ssum.get("dup_stmt_excess") or 0),
                "big_struct_files": int(ssum.get("big_struct_files") or 0),
                "numbered_have_files": int(ssum.get("numbered_have_files") or 0),
            },
        }
        if orig_ref is None:
            orig_ref = st_obj
            st_obj["vs_orig"] = {
                "files_pct": 0.0,
                "lines_pct": 0.0,
                "code_lines_pct": 0.0,
                "files_x": 1.0,
                "lines_x": 1.0,
                "code_lines_x": 1.0,
                "slop_delta": 0.0,
            }
        else:
            o_f = max(1, orig_ref["files"])
            o_l = max(1, orig_ref["lines"])
            o_c = max(1, orig_ref["code_lines"])
            st_obj["vs_orig"] = {
                "files_pct": round(100.0 * (st_obj["files"] - o_f) / o_f, 1),
                "lines_pct": round(100.0 * (st_obj["lines"] - o_l) / o_l, 1),
                "code_lines_pct": round(100.0 * (st_obj["code_lines"] - o_c) / o_c, 1),
                "files_x": round(o_f / max(1, st_obj["files"]), 1),
                "lines_x": round(o_l / max(1, st_obj["lines"]), 1),
                "code_lines_x": round(o_c / max(1, st_obj["code_lines"]), 1),
                "slop_delta": round(st_obj["slop_score_src"] - orig_ref["slop_score_src"], 1),
            }
        stages_out.append(st_obj)

        bmode = str(spec.get("boundary_mode") or "")
        if bmode == "detailed":
            grh_boundary = _analyze_lib_new_boundary(src_dir, srep, slug=slug, detailed=True)
        elif bmode == "summary":
            compact_boundary = _analyze_lib_new_boundary(src_dir, srep, slug=slug, detailed=False)

    doc: Dict[str, Any] = {
        "schema": EVOLUTION_SCHEMA,
        "generated_utc": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "headline": "17.37M → 14.56M → 300k → 76k",
        "stages": stages_out,
        "pillar_caps": PILLAR_CAPS,
    }
    if grh_boundary is not None:
        doc["grh_boundary"] = grh_boundary
    if compact_boundary is not None:
        doc["compact_boundary"] = compact_boundary
    return _sanitize_json(doc)


def _main(argv: Optional[Sequence[str]] = None) -> int:
    ap = argparse.ArgumentParser(prog="leanre slop", description="Ground-truth calibrated 0–100 Lean Slopscore, diff & cold-gap engine")
    sub = ap.add_subparsers(dest="cmd")

    p_scan = sub.add_parser("scan", help="Compute 0–100 slop score for a Lean 4 source directory")
    p_scan.add_argument("src_dir", help="Path to Lean 4 source root")
    p_scan.add_argument("--slug", default="project")
    p_scan.add_argument("--kernel-db", default=None)
    p_scan.add_argument("--workers", type=int, default=0)
    p_scan.add_argument("--out", default=None, help="Output JSON path")

    p_diff = sub.add_parser("diff", help="Compare two leanre.slop/1 JSON reports")
    p_diff.add_argument("before_json")
    p_diff.add_argument("after_json")
    p_diff.add_argument("--label-before", default="")
    p_diff.add_argument("--label-after", default="")
    p_diff.add_argument("--gh-repo", default="", help="Optional GitHub owner/repo to annotate cold gaps against open PRs")
    p_diff.add_argument("--out", default=None)

    p_aud = sub.add_parser("audits", help="Validate PR-extensible blind audit rounds directory")
    p_aud.add_argument("--dir", default="notes/audits")

    p_evo = sub.add_parser("evolution", help="Generate 4-stage RH proof evolution telemetry (leanre.rh_evolution/1)")
    p_evo.add_argument("--orig-src", default=os.path.join(_REPO_ROOT, "data", "rh_mirror", "src"))
    p_evo.add_argument("--orig-slop", default=os.path.join(_REPO_ROOT, "outputs", "slop_rh_orig.json"))
    p_evo.add_argument("--orig-slop-src", default=os.path.join(_REPO_ROOT, "outputs", "slop_rh_orig_src.json"))
    p_evo.add_argument("--cleanup-src", default=os.path.join(_REPO_ROOT, "data", "rh_cleanup", "src"))
    p_evo.add_argument("--cleanup-slop", default=os.path.join(_REPO_ROOT, "outputs", "slop_rh_cleanup.json"))
    p_evo.add_argument("--grh-src", default=os.path.join(_REPO_ROOT, "data", "rh_grh", "src"))
    p_evo.add_argument("--grh-slop", default=os.path.join(_REPO_ROOT, "outputs", "slop_rh_grh.json"))
    p_evo.add_argument("--compact-src", default=os.path.join(_REPO_ROOT, "data", "grh_lean", "grh-compact", "src"))
    p_evo.add_argument("--compact-slop", default=os.path.join(_REPO_ROOT, "outputs", "slop_rh_compact.json"))
    p_evo.add_argument("--workers", type=int, default=0)
    p_evo.add_argument("--out", default=os.path.join(_REPO_ROOT, "outputs", "rh_evolution.json"))

    args = ap.parse_args(list(argv) if argv is not None else None)
    if args.cmd == "audits":
        bundle, errs = load_audits_dir(args.dir)
        if errs:
            for e in errs:
                print(f"ERROR: {e}", file=sys.stderr)
            return 1
        print(f"OK: {len(bundle['rounds'])} valid audit round(s)")
        return 0
    if args.cmd == "evolution":
        specs = [
            {
                "stage_num": 1,
                "slug": "riemann-hypothesis",
                "label": "Original Archive (40e56bab)",
                "short_label": "Original Archive",
                "branch": "original",
                "repo_url": "https://github.com/leanprover-community/riemann-hypothesis",
                "commit": "40e56bab026552e089d7afcfeff08d2defb9c005",
                "date": "2026-11-20",
                "license": "None",
                "src_dir": args.orig_src,
                "slop_json": args.orig_slop,
                "slop_src_json": args.orig_slop_src,
            },
            {
                "stage_num": 2,
                "slug": "riemann-hypothesis-cleanup",
                "label": "Community Cleanup (alpoge)",
                "short_label": "Cleanup (alpoge)",
                "branch": "alpoge",
                "repo_url": "https://github.com/leanprover-community/riemann-hypothesis",
                "license": "None",
                "src_dir": args.cleanup_src,
                "slop_json": args.cleanup_slop,
            },
            {
                "stage_num": 3,
                "slug": "riemann-hypothesis-grh",
                "label": "Readable Edition (grh / main)",
                "short_label": "Readable (grh)",
                "branch": "main",
                "repo_url": "https://github.com/leanprover-community/riemann-hypothesis",
                "license": "Apache-2.0",
                "is_current_main": True,
                "src_dir": args.grh_src,
                "slop_json": args.grh_slop,
                "boundary_mode": "detailed",
            },
            {
                "stage_num": 4,
                "slug": "riemann-hypothesis-compact",
                "label": "Compact Edition (76k)",
                "short_label": "Compact (76k)",
                "branch": "main (grh-compact/)",
                "repo_url": "https://github.com/lsernau/grh-lean",
                "license": "Apache-2.0",
                "src_dir": args.compact_src,
                "slop_json": args.compact_slop,
                "boundary_mode": "summary",
            },
        ]
        doc = build_rh_evolution(specs, workers=args.workers)
        if args.out:
            _safe_write_json(args.out, doc)
            summary_bits = ", ".join(
                f"{st['short_label']}={st['files']:,}f/{st['code_lines']:,}loc/{st['slop_score']}"
                for st in doc["stages"]
            )
            print(f"evolution: {summary_bits} -> {args.out}")
        else:
            print(json.dumps(doc, indent=2, ensure_ascii=False))
        return 0
    if args.cmd == "diff":
        with open(args.before_json, "r", encoding="utf-8") as f:
            b = json.load(f)
        with open(args.after_json, "r", encoding="utf-8") as f:
            a = json.load(f)
        gaps = None
        if args.gh_repo:
            prs = fetch_open_pr_titles_gh(args.gh_repo)
            gaps = compute_cold_gaps(a, prs)
        d = diff_slop_reports(b, a, label_before=args.label_before, label_after=args.label_after, cold_gaps=gaps)
        if args.out:
            _safe_write_json(args.out, d)
        else:
            print(json.dumps(d, indent=2, ensure_ascii=False))
        return 0
    if args.cmd == "scan":
        rep = build_slop_report(args.src_dir, slug=args.slug, kernel_db=args.kernel_db, workers=args.workers)
        if args.out:
            _safe_write_json(args.out, rep)
            s = rep["summary"]
            print(f"slop({rep['slug']}): score={s['score']}/100 files={s['files']:,} lines={s['lines']:,} pillars={rep['pillars']} -> {args.out}")
        else:
            print(json.dumps(rep, indent=2, ensure_ascii=False))
        return 0
    ap.print_help()
    return 1


if __name__ == "__main__":
    raise SystemExit(_main())
