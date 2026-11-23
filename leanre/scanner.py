#!/usr/bin/env python3
"""Parallel 14-core scanner for all 175,187 Lean 4 source files in Alpoge's RH/GRH release.

Extracts:
- Exact module import graph + drew2apps acceptance gate metrics
- Cooper-Harvey-Kennedy dominator tree + retained module/line counts + exact rev_reach
- Whole-corpus declaration headers (fair-use 1-line signatures <=240 chars, zero proof bodies)
- Whole-corpus dependency-injection Horn skeleton (REQUIRES A & B => PROVES C)
- Namespace/directory mislabeling statistics (depth 1 & 2 + actual inner decl namespaces)
- Forensic hotspots (kexactB, kcopy, CutCptCopy, addDecl, run_tac, decide +kernel,
  positivity_ext, BuildAid, OpenLiteratureStatements, slow_con_leche, lean4lean_timeout,
  sorry, axiom, native_decide, unsafe, implemented_by) + shortest paths to Main
- Clone/boilerplate fingerprints (alpha-renamed blake2b signature + zlib compression ratio)
"""
from __future__ import annotations

import argparse
import collections
import hashlib
import json
import multiprocessing
import os
import re
import sys
import time
import zlib
from typing import Any, Dict, List, Optional, Sequence, Set, Tuple

try:
    from config import _SKIP_DIRS as CONFIG_SKIP_DIRS, coerce_config, find_local_config, parse_lakefile
    from db import (
        FORENSIC_FLAGS,
        FORENSIC_SEVERITY,
        INDEX_SQL_SCAN,
        finalize_db,
        flags_to_bitmask,
        open_db,
        set_meta,
    )
    from graph import (
        bfs_shortest_paths,
        bottom_depths_dag,
        compute_rev_reach_exact,
        dominators_chk,
        reconstruct_path_to_root,
    )
except ImportError:  # pragma: no cover - package-style import fallback
    from leanre.config import _SKIP_DIRS as CONFIG_SKIP_DIRS, coerce_config, find_local_config, parse_lakefile
    from leanre.db import (
        FORENSIC_FLAGS,
        FORENSIC_SEVERITY,
        INDEX_SQL_SCAN,
        finalize_db,
        flags_to_bitmask,
        open_db,
        set_meta,
    )
    from leanre.graph import (
        bfs_shortest_paths,
        bottom_depths_dag,
        compute_rev_reach_exact,
        dominators_chk,
        reconstruct_path_to_root,
    )

# ---------------------------------------------------------------------------
# Known verified external checker hotspots (from Sutherland logs & recon #21)
# ---------------------------------------------------------------------------
LEAN4LEAN_TIMEOUT_MODULES: Set[str] = {
    "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DyadicPrimeIntervals.Run1",
    "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DyadicPrimeIntervals.Run2",
    "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DyadicPrimeIntervals.Run3",
    "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DyadicPrimeIntervals.Run4",
    "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChebyshevPrimeBounds.SmallLoop",
}

SLOW_CON_LECHE_TARGETS: Dict[str, Dict[str, Any]] = {
    "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LamCopy": {
        "decl": "lam_copy",
        "full_decl": "GlobalTheory.HeightCounting.SideCopy.LamCopy.lam_copy",
        "seconds": 55.2,
    },
    "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingSpecNormalisedCharacterEq": {
        "decl": "sigSpan_copy",
        "full_decl": "sigSpan_copy",
        "seconds": 40.3,
    },
    "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChebyshevPrimeBounds.SmallLoop": {
        "decl": "loop_run",
        "full_decl": "PI.PC.loop_run._proof_1_1",
        "seconds": 35.1,
    },
    "Formalism.PadicSubsetSums.StableGradedCounts.IRRPrimeRecipSum": {
        "decl": "factorial_ladder_one_forty_one",
        "full_decl": "Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.PrimeCountingLemmas.factorial_ladder_one_forty_one._proof_1_1",
        "seconds": 25.0,
    },
    "Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvFiveLogLeSumInvPrimes": {
        "decl": "table_ok",
        "full_decl": "GlobalTheory.PrimeRecip.table_ok._proof_1_1",
        "seconds": 17.2,
    },
}

# ---------------------------------------------------------------------------
# Compiled regexes (shared across worker processes via fork on macOS/POSIX)
# ---------------------------------------------------------------------------
_RE_IMPORT = re.compile(
    r"^\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?([A-Za-z_][^\s]*)"
)
_RE_NS_OPEN = re.compile(r"^\s*namespace\s+([A-Za-z_][\w.'₀-₉]*)")
_RE_NS_END = re.compile(r"^\s*end(?:\s+([A-Za-z_][\w.'₀-₉]*))?\s*$")
_RE_DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|unsafe|partial|nonrec|scoped|local)\s+)*"
    r"(theorem|lemma|def|abbrev|structure|class|instance|inductive|opaque|axiom)\b"
    r"(?:\s+([^\s:({\[⦃]+))?"
)

# Forensic hotspot line regexes
_FORENSIC_REGEXES: List[Tuple[str, re.Pattern]] = [
    ("kexactB", re.compile(r"\bkexactB\b|\bkc%|\bkq%|\bkd%|\btr_via\b|\btr_clause\b")),
    ("kcopy", re.compile(r"\bkcopy\b|#kcopy_probe\b")),
    ("CutCptCopy", re.compile(r"\bCutCptCopy\b|\bcutCptCopy\b|\bcopy_decl\b")),
    ("addDecl", re.compile(r"\baddDecl\b|\baddAndCompile\b")),
    ("run_tac", re.compile(r"\brun_tac\b|\brun_cmd\b|\brun_elab\b")),
    ("decide_kernel", re.compile(r"\bdecide\s*\+kernel\b")),
    ("positivity_ext", re.compile(r"@\[positivity\b")),
    ("OpenLiteratureStatements", re.compile(r"\bOpenLiteratureStatements\b")),
    ("sorry", re.compile(r"\bsorry\b|\badmit\b")),
    ("axiom", re.compile(r"^\s*(?:private\s+|protected\s+)?axiom\b")),
    ("native_decide", re.compile(r"\bnative_decide\b|\bofReduceBool\b|\bdecide\s*\+native\b")),
    ("unsafe", re.compile(r"^\s*unsafe\b|\bunsafe\s+(?:def|theorem|axiom|inductive|instance)\b")),
    ("implemented_by", re.compile(r"\bimplemented_by\b|@\[extern\b|\bcsimp\b")),
]

# Clone normalization
_LEAN_KEYWORDS: Set[str] = set(
    """simp only at exact rw intro intros have by nlinarith refine obtain apply norm_num linarith
    rcases with field_simp ring_nf positivity gcongr omega constructor ext push_cast exact_mod_cast
    by_cases calc ring funext congr unfold show filter_upwards specialize induction zero succ simpa
    using ih this subst cases theorem lemma def instance structure fun trans aesop tauto decide
    import open namespace end variable section noncomputable private protected abbrev class where
    match if then else do let in return for pure classical by_contra contradiction exfalso
    left right use refine' exact? apply? simp_all dsimp change clear revert generalize rfl
    rwa erw linear_combination polyrith abel group module norm_cast cast exact_mod_cast
    conv lhs rhs arg enter pattern repeat try first all_goals any_goals focus swap rotate_left
    trivial assumption done sorry admit axiom opaque inductive mutual deriving extends""".split()
)
_RE_NORM_TOK = re.compile(r"[A-Za-z_][\w.'₀-₉]*|\d+")

# Horn-skeleton signature parsing
_OPEN_BR = "([{⦃⟨"
_CLOSE_BR = ")]}⦄⟩"
_RE_REL = re.compile(r"[=<>≤≥≠∧∨↔∀∃¬∈∣+\-*/^]")
_RE_HEAD = re.compile(r"[A-Za-z_][\w.'₀-₉]*")

# Type-level / data / typeclass heads that are NOT logical propositions in Horn clauses
_NON_PROP_HEADS: Set[str] = {
    "Prop", "Type", "Sort", "Nat", "Int", "Rat", "Real", "Complex", "NNReal", "ENNReal",
    "Bool", "Char", "String", "Unit", "PUnit", "Empty", "PEmpty", "True", "False",
    "List", "Array", "Option", "Fin", "Finset", "Fintype", "Multiset", "Set", "Subtype",
    "Prod", "PProd", "Sum", "PSum", "Sigma", "PSigma", "Equiv", "Function", "Matrix",
    "Polynomial", "MvPolynomial", "PowerSeries", "ZMod", "Padic", "PadicInt",
    "DirichletCharacter", "MulChar", "AddChar", "ArithmeticFunction", "LSeries",
    "Ring", "CommRing", "Semiring", "CommSemiring", "Field", "DivisionRing", "Group",
    "CommGroup", "AddGroup", "AddCommGroup", "Monoid", "CommMonoid", "Module", "Algebra",
    "Submodule", "Ideal", "Subgroup", "Subring", "Subfield", "Units", "RingHom", "MonoidHom",
    "LinearMap", "LinearEquiv", "AlgHom", "AlgEquiv", "ContinuousLinearMap",
    "NumberField", "IsFractionRing", "IsIntegralClosure", "IsDedekindDomain", "IsDomain",
    "CharZero", "NeZero", "Nontrivial", "Unique", "Inhabited", "Decidable", "DecidableEq",
    "DecidablePred", "LinearOrder", "PartialOrder", "Preorder", "Lattice", "CompleteLattice",
    "TopologicalSpace", "MetricSpace", "UniformSpace", "NormedSpace", "NormedField",
    "NormedRing", "NormedAddCommGroup", "InnerProductSpace", "CompleteSpace", "T2Space",
    "CompactSpace", "LocallyCompactSpace", "SecondCountableTopology", "MeasurableSpace",
    "Measure", "MeasureTheory", "Filter", "Tendsto", "Continuous", "ContinuousOn",
    "Differentiable", "DifferentiableOn", "AnalyticAt", "AnalyticOn", "Integrable",
    "Measurable", "AEMeasurable", "AEStronglyMeasurable", "LocallyIntegrable",
    "IsOpen", "IsClosed", "IsCompact", "Finite", "Countable", "Infinite",
    "Eq", "Ne", "Iff", "And", "Or", "Not", "Exists", "HEq", "LE", "LT", "GE", "GT",
    "PChar", "Add", "Mul", "Sub", "Div", "Pow", "Neg", "Inv", "Zero", "One",
}


def strip_lean_comments(text: str) -> str:
    """Fast comment stripper for Lean 4 (-- line comments and nested /- ... -/ blocks).
    Short-circuits immediately when neither `--` nor `/-` appears (true for 100% of Alpoge's archive).
    """
    if "--" not in text and "/-" not in text:
        return text
    out: List[str] = []
    i = 0
    n = len(text)
    in_str = False
    depth = 0
    while i < n:
        ch = text[i]
        if depth > 0:
            if ch == "/" and i + 1 < n and text[i + 1] == "-":
                depth += 1
                i += 2
            elif ch == "-" and i + 1 < n and text[i + 1] == "/":
                depth -= 1
                i += 2
            else:
                if ch == "\n":
                    out.append("\n")
                i += 1
        elif in_str:
            out.append(ch)
            if ch == "\\" and i + 1 < n:
                out.append(text[i + 1])
                i += 2
            elif ch == '"':
                in_str = False
                i += 1
            else:
                i += 1
        else:
            if ch == '"':
                in_str = True
                out.append(ch)
                i += 1
            elif ch == "/" and i + 1 < n and text[i + 1] == "-":
                depth = 1
                i += 2
            elif ch == "-" and i + 1 < n and text[i + 1] == "-":
                j = text.find("\n", i)
                if j == -1:
                    break
                out.append("\n")
                i = j + 1
            else:
                out.append(ch)
                i += 1
    return "".join(out)


def _extract_named_prop(expr: str) -> Optional[str]:
    """Return head proposition identifier if `expr` looks like an application of a named
    proposition (UpperCamelCase tail, no top-level relation/connective). Unwraps `Nonempty (...)`.
    """
    s = expr.strip()
    while s.startswith("(") and s.endswith(")"):
        # Only strip matching outer parens
        depth = 0
        matched = True
        for k, ch in enumerate(s):
            if ch in _OPEN_BR:
                depth += 1
            elif ch in _CLOSE_BR:
                depth -= 1
                if depth == 0 and k < len(s) - 1:
                    matched = False
                    break
        if matched and depth == 0:
            s = s[1:-1].strip()
        else:
            break
    if not s:
        return None
    m = _RE_HEAD.match(s)
    if not m:
        return None
    head = m.group(0)
    rest = s[m.end():]
    if head == "Nonempty":
        return _extract_named_prop(rest)
    # Check that there are no top-level relations/operators/arrows outside brackets
    flat: List[str] = []
    depth = 0
    rest_clean = rest.replace("=>", "  ").replace("↦", " ")
    for ch in rest_clean:
        if ch in _OPEN_BR:
            depth += 1
        elif ch in _CLOSE_BR:
            depth -= 1
        elif depth == 0:
            if ch == "→":
                return None
            flat.append(ch)
    if _RE_REL.search("".join(flat)):
        return None
    tail = head.split(".")[-1]
    if not tail or not tail[0].isupper():
        return None
    if tail in _NON_PROP_HEADS or head in _NON_PROP_HEADS:
        return None
    return head


def _split_top_arrows(expr: str) -> List[str]:
    """Split a Lean type expression on top-level `→` / `->` outside brackets."""
    parts: List[str] = []
    buf: List[str] = []
    depth = 0
    i = 0
    n = len(expr)
    while i < n:
        ch = expr[i]
        if ch in _OPEN_BR:
            depth += 1
            buf.append(ch)
            i += 1
        elif ch in _CLOSE_BR:
            depth = max(0, depth - 1)
            buf.append(ch)
            i += 1
        elif depth == 0 and ch == "→":
            parts.append("".join(buf).strip())
            buf = []
            i += 1
        elif depth == 0 and ch == "-" and i + 1 < n and expr[i + 1] == ">":
            parts.append("".join(buf).strip())
            buf = []
            i += 2
        else:
            buf.append(ch)
            i += 1
    tail = "".join(buf).strip()
    if tail:
        parts.append(tail)
    return parts


def parse_horn_header(header_text: str) -> Tuple[List[str], Optional[str]]:
    """Extract (required_named_props, proved_named_prop) from a theorem/lemma header
    (everything after `theorem <name>` up to `:=`).
    """
    n = len(header_text)
    i = 0
    depth = 0
    binders: List[str] = []
    cur: List[str] = []
    colon_pos = -1

    while i < n:
        ch = header_text[i]
        if ch in _OPEN_BR:
            depth += 1
            cur.append(ch)
        elif ch in _CLOSE_BR:
            cur.append(ch)
            depth -= 1
            if depth == 0:
                binders.append("".join(cur))
                cur = []
            elif depth < 0:
                depth = 0
                cur = []
        elif depth > 0:
            cur.append(ch)
        elif ch == ":":
            colon_pos = i
            break
        i += 1

    if colon_pos == -1:
        return [], None

    ret_text = header_text[colon_pos + 1:].strip()
    requires: List[str] = []
    seen_req: Set[str] = set()

    for b in binders:
        if not b or b[0] != "(" or ":" not in b:
            continue
        inner = b[1:-1]
        # Split on first top-level ':' inside binder
        cpos = inner.find(":")
        if cpos == -1:
            continue
        bnames = inner[:cpos].strip().split()
        bty = inner[cpos + 1:].strip()
        if not bnames:
            continue
        # Check if hypothesis binder (h*, or named proposition head directly)
        prop = _extract_named_prop(bty)
        if prop is not None:
            if prop not in seen_req:
                seen_req.add(prop)
                requires.append(prop)

    # Split return type on top-level `→` to capture anonymous implication premises too
    arrow_parts = _split_top_arrows(ret_text)
    concl: Optional[str] = None
    if arrow_parts:
        for ant in arrow_parts[:-1]:
            p = _extract_named_prop(ant)
            if p is not None and p not in seen_req:
                seen_req.add(p)
                requires.append(p)
        concl = _extract_named_prop(arrow_parts[-1])

    # Don't record trivial self-loops if concl == req unless there are other props
    return requires, concl


def normalize_for_clone(lines: List[str]) -> str:
    """Alpha-rename identifiers & numeric literals in non-import body lines for clone clustering."""
    def _sub(m: re.Match) -> str:
        tok = m.group(0)
        if tok[0].isdigit():
            return "0"
        return tok if tok in _LEAN_KEYWORDS else "x"

    norm_lines = [_RE_NORM_TOK.sub(_sub, ln.strip()) for ln in lines if ln.strip()]
    return "\n".join(norm_lines)


def _scan_batch(
    args: Tuple[Any, ...]
) -> List[Dict[str, Any]]:
    """Worker function: scan a batch of ``(mod_id, mod_name, rel_path)`` files.

    Accepts either ``(src_dir, items)`` or
    ``(src_dir, items, timeout_modules, slow_targets, extra_regex_specs)``.
    Timeout/slow target maps default to empty so generic repos have no
    RH-specific taint rules injected unless supplied via ``leanre.toml``.
    """
    if len(args) == 2:
        src_root, items = args
        timeout_modules: Set[str] = set()
        slow_targets: Dict[str, Dict[str, Any]] = {}
        extra_regex_specs: Sequence[Tuple[str, str]] = ()
        max_hits_per_tag = 50
    elif len(args) == 5:
        src_root, items, timeout_modules, slow_targets, extra_regex_specs = args
        max_hits_per_tag = 50
    else:
        src_root, items, timeout_modules, slow_targets, extra_regex_specs, max_hits_per_tag = args

    compiled_extra: List[Tuple[str, re.Pattern[str]]] = []
    if extra_regex_specs:
        base_tags = {tag for tag, _ in _FORENSIC_REGEXES}
        for tag, pat in extra_regex_specs:
            if tag not in base_tags:
                compiled_extra.append((tag, re.compile(pat)))
    active_regexes = _FORENSIC_REGEXES + compiled_extra

    results: List[Dict[str, Any]] = []

    for mod_id, mod_name, rel_path in items:
        abs_path = os.path.join(src_root, rel_path)
        with open(abs_path, "rb") as f:
            raw_bytes = f.read()

        n_bytes = len(raw_bytes)
        lines_wc = raw_bytes.count(b"\n")
        trailing_nl = 1 if (n_bytes > 0 and raw_bytes[-1] == 10) else 0
        lines_eof = lines_wc + (0 if (trailing_nl or n_bytes == 0) else 1)

        text = raw_bytes.decode("utf-8", errors="replace")
        clean_text = strip_lean_comments(text)
        raw_lines = text.split("\n")
        clean_lines = clean_text.split("\n")

        # 1. Imports & shim detection
        raw_imports: List[str] = []
        imports_mathlib = 0
        body_lines: List[str] = []
        has_non_import_code = False

        for ln in clean_lines:
            s = ln.strip()
            if not s:
                continue
            m_imp = _RE_IMPORT.match(ln)
            if m_imp:
                imp_name = m_imp.group(1)
                raw_imports.append(imp_name)
                if imp_name == "Mathlib":
                    imports_mathlib = 1
            else:
                has_non_import_code = True
                body_lines.append(ln)

        dup_imports_all = len(raw_imports) - len(set(raw_imports))
        # Track exact duplicates by module name so parent process can split project vs Mathlib dups
        imp_counts = collections.Counter(raw_imports)
        dup_import_targets = {k: v - 1 for k, v in imp_counts.items() if v > 1}
        distinct_imports = sorted(imp_counts.keys())
        is_shim = 1 if (raw_imports and not has_non_import_code) else 0

        # 2. Declarations & Horn skeleton
        ns_stack: List[str] = []
        decls_out: List[Tuple[str, str, int, str, List[str], Optional[str], List[str]]] = []
        thm_count = 0
        def_count = 0
        decl_kind_counts: collections.Counter = collections.Counter()
        inner_decl_prefixes: List[str] = []

        n_cl = len(clean_lines)
        line_idx = 0
        current_decl_by_line: List[Tuple[int, str]] = []  # (line_no, decl_name)

        slow_info = slow_targets.get(mod_name)
        is_timeout_mod = mod_name in timeout_modules

        while line_idx < n_cl:
            ln = clean_lines[line_idx]
            if not ln or ln[0] == " " or ln[0] == "\t":
                line_idx += 1
                continue
            m_ns = _RE_NS_OPEN.match(ln)
            if m_ns:
                ns_stack.append(m_ns.group(1))
                line_idx += 1
                continue
            m_end = _RE_NS_END.match(ln)
            if m_end:
                if ns_stack:
                    end_nm = m_end.group(1)
                    if end_nm is None or ns_stack[-1] == end_nm:
                        ns_stack.pop()
                line_idx += 1
                continue

            m_decl = _RE_DECL.match(ln)
            if m_decl:
                kind = m_decl.group(1)
                raw_name = m_decl.group(2) or f"_anon_{line_idx + 1}"
                decl_kind_counts[kind] += 1
                if kind in ("theorem", "lemma"):
                    thm_count += 1
                else:
                    def_count += 1

                # Qualify with active namespace stack if unqualified or relative
                if ns_stack and not raw_name.startswith(ns_stack[0] + "."):
                    full_name = ".".join(ns_stack) + "." + raw_name
                else:
                    full_name = raw_name

                parts_fn = full_name.split(".")
                if len(parts_fn) >= 2:
                    inner_decl_prefixes.append(f"{parts_fn[0]}.{parts_fn[1]}")
                else:
                    inner_decl_prefixes.append(parts_fn[0])

                # Collect multi-line header up to top-level `:=` or `where` (max 16 lines)
                hdr_parts = [ln]
                j = line_idx
                found_assign = ":=" in ln or (kind in ("structure", "class", "inductive") and " where" in ln)
                while not found_assign and j + 1 < n_cl and (j - line_idx) < 16:
                    j += 1
                    nxt = clean_lines[j]
                    if nxt and nxt[0] not in (" ", "\t"):
                        # Hit next top-level item before finding :=
                        if _RE_DECL.match(nxt) or _RE_NS_OPEN.match(nxt) or _RE_NS_END.match(nxt):
                            break
                    hdr_parts.append(nxt)
                    if ":=" in nxt or (kind in ("structure", "class", "inductive") and " where" in nxt):
                        found_assign = True
                        break

                hdr_joined = " ".join(p.strip() for p in hdr_parts if p.strip())
                # Cut strictly before `:=` (or `where` for structs) to ensure ZERO proof body!
                cut_idx = hdr_joined.find(":=")
                if cut_idx != -1:
                    sig_full = hdr_joined[:cut_idx].strip()
                else:
                    sig_full = hdr_joined.strip()

                sig_snippet = sig_full if len(sig_full) <= 240 else (sig_full[:237] + "...")

                horn_reqs: List[str] = []
                horn_prov: Optional[str] = None
                if kind in ("theorem", "lemma"):
                    # Parse header text AFTER `theorem <name>`
                    after_name_pos = sig_full.find(raw_name)
                    if after_name_pos != -1:
                        after_hdr = sig_full[after_name_pos + len(raw_name):]
                        horn_reqs, horn_prov = parse_horn_header(after_hdr)

                d_tags: List[str] = []
                if slow_info and (raw_name == slow_info["decl"] or full_name.endswith("." + slow_info["decl"])):
                    d_tags.append("slow_con_leche")
                if is_timeout_mod and raw_name in ("run1", "run2", "run3", "run4", "loop_run"):
                    d_tags.append("lean4lean_timeout")

                decls_out.append((full_name, kind, line_idx + 1, sig_snippet, horn_reqs, horn_prov, d_tags))
                current_decl_by_line.append((line_idx + 1, full_name))
            line_idx += 1

        # 3. Forensic hotspot scanning
        mod_flags: Set[str] = set()
        hits_out: List[Tuple[str, int, Optional[str], str]] = []
        tag_total_counts: collections.Counter = collections.Counter()
        tag_truncated_counts: collections.Counter = collections.Counter()

        if mod_name.startswith("BuildAid.") or mod_name == "BuildAid":
            mod_flags.add("BuildAid")
            tag_total_counts["BuildAid"] += 1
            hits_out.append(("BuildAid", 1, None, (raw_lines[0].strip() if raw_lines else "")[:200]))

        if mod_name.endswith(".CutCptCopy"):
            mod_flags.add("CutCptCopy")
            tag_total_counts["CutCptCopy"] += 1
            hits_out.append(("CutCptCopy", 1, None, "CutCptCopy metaprogramming declaration copier (uses addDecl)"))

        if is_timeout_mod:
            mod_flags.add("lean4lean_timeout")
            tag_total_counts["lean4lean_timeout"] += 1
            t_decl = None
            t_line = 1
            for dl, dn in current_decl_by_line:
                if dn.split(".")[-1] in ("run1", "run2", "run3", "run4", "loop_run"):
                    t_line, t_decl = dl, dn
                    break
            snip = raw_lines[t_line - 1].strip()[:200] if t_line <= len(raw_lines) else ""
            hits_out.append(("lean4lean_timeout", t_line, t_decl, snip))

        if slow_info is not None:
            mod_flags.add("slow_con_leche")
            tag_total_counts["slow_con_leche"] += 1
            s_decl = slow_info["full_decl"]
            s_line = 1
            for dl, dn in current_decl_by_line:
                if dn.split(".")[-1] == slow_info["decl"]:
                    s_line, s_decl = dl, dn
                    break
            snip = raw_lines[s_line - 1].strip()[:200] if s_line <= len(raw_lines) else ""
            hits_out.append(("slow_con_leche", s_line, s_decl, f"[{slow_info['seconds']}s] {snip}"[:200]))

        # Fast whole-file pre-check before line-by-line forensic scan
        if compiled_extra or (
            "kexactB" in clean_text
            or "kc%" in clean_text
            or "kq%" in clean_text
            or "kd%" in clean_text
            or "tr_via" in clean_text
            or "tr_clause" in clean_text
            or "kcopy" in clean_text
            or "CutCptCopy" in clean_text
            or "cutCptCopy" in clean_text
            or "addDecl" in clean_text
            or "addAndCompile" in clean_text
            or "run_tac" in clean_text
            or "run_cmd" in clean_text
            or "run_elab" in clean_text
            or "+kernel" in clean_text
            or "positivity" in clean_text
            or "OpenLiteratureStatements" in clean_text
            or "sorry" in clean_text
            or "admit" in clean_text
            or "axiom" in clean_text
            or "native_decide" in clean_text
            or "ofReduceBool" in clean_text
            or "+native" in clean_text
            or "unsafe" in clean_text
            or "implemented_by" in clean_text
            or "@[extern" in clean_text
            or "csimp" in clean_text
        ):
            cur_decl_ptr = 0
            cur_decl_nm: Optional[str] = None
            n_cd = len(current_decl_by_line)
            per_tag_count: collections.Counter = collections.Counter()
            for idx_l, cln in enumerate(clean_lines):
                lno = idx_l + 1
                while cur_decl_ptr < n_cd and current_decl_by_line[cur_decl_ptr][0] <= lno:
                    cur_decl_nm = current_decl_by_line[cur_decl_ptr][1]
                    cur_decl_ptr += 1
                for tag, rx in active_regexes:
                    if rx.search(cln):
                        mod_flags.add(tag)
                        tag_total_counts[tag] += 1
                        if max_hits_per_tag <= 0 or per_tag_count[tag] < max_hits_per_tag:
                            per_tag_count[tag] += 1
                            hits_out.append((tag, lno, cur_decl_nm, raw_lines[idx_l].strip()[:200]))
                        else:
                            tag_truncated_counts[tag] += 1

        # 4. Boilerplate / clone fingerprint & zlib ratio
        if body_lines:
            body_bytes = "\n".join(body_lines).encode("utf-8")
            zlib_ratio = round(len(zlib.compress(body_bytes, 1)) / max(1, len(body_bytes)), 4)
            norm_str = normalize_for_clone(body_lines)
            clone_sig = hashlib.blake2b(norm_str.encode("utf-8"), digest_size=8).hexdigest()
        else:
            zlib_ratio = 0.0
            clone_sig = "shim_empty"

        results.append({
            "id": mod_id,
            "name": mod_name,
            "file_path": rel_path,
            "lines": lines_eof,
            "lines_wc": lines_wc,
            "bytes": n_bytes,
            "trailing_nl": trailing_nl,
            "decl_count": thm_count + def_count,
            "thm_count": thm_count,
            "def_count": def_count,
            "decl_kind_counts": dict(decl_kind_counts),
            "distinct_imports": distinct_imports,
            "imports_mathlib": imports_mathlib,
            "is_shim": is_shim,
            "dup_imports_all": dup_imports_all,
            "dup_import_targets": dup_import_targets,
            "clone_sig": clone_sig,
            "zlib_ratio": zlib_ratio,
            "flags": sorted(mod_flags),
            "decls": decls_out,
            "hits": hits_out,
            "tag_total_counts": dict(tag_total_counts),
            "tag_truncated_counts": dict(tag_truncated_counts),
            "inner_decl_prefixes": inner_decl_prefixes,
        })
    return results


def discover_lean_files(
    src_dir: str,
    *,
    skip_dirs: Optional[Set[str]] = None,
    whitelist_dirs: Optional[Set[str]] = None,
) -> List[Tuple[int, str, str]]:
    """Walk `src_dir` deterministically and return [(id, module_name, rel_path), ...].

    Skips non-library helper trees (`.lake`, `.git`, `build`, `blueprint*`,
    `scripts`, `examples`, `docs`, `paper`, `test`, `tests`, etc.) unless
    explicitly whitelisted via `whitelist_dirs` or targeted directly as `src_dir`.
    Also skips a top-level `lakefile.lean` build script.
    """
    eff_skip = set(CONFIG_SKIP_DIRS) if skip_dirs is None else set(skip_dirs)
    wl = set(whitelist_dirs or ())
    src_abs = os.path.abspath(src_dir)
    items: List[Tuple[str, str]] = []
    for dirpath, dirnames, filenames in os.walk(src_dir):
        at_root = os.path.abspath(dirpath) == src_abs
        dirnames[:] = sorted(
            d
            for d in dirnames
            if d in wl or (d not in eff_skip and not d.startswith("blueprint"))
        )
        for fn in sorted(filenames):
            if not fn.endswith(".lean"):
                continue
            if at_root and fn == "lakefile.lean":
                continue
            full = os.path.join(dirpath, fn)
            rel = os.path.relpath(full, src_dir)
            mod = rel[:-5].replace(os.sep, ".")
            items.append((mod, rel))
    items.sort(key=lambda x: x[0])
    return [(i, mod, rel) for i, (mod, rel) in enumerate(items)]


def _load_lake_hints(src_dir: str) -> Optional[Dict[str, Any]]:
    """Consult `lakefile.toml`/`lakefile.lean` in `src_dir` (or parent if `srcDir` matches)."""
    info = parse_lakefile(src_dir)
    if info is not None:
        return info
    abs_src = os.path.abspath(src_dir)
    parent = os.path.dirname(abs_src)
    if parent and parent != abs_src:
        pinfo = parse_lakefile(parent)
        if pinfo is not None:
            declared = (pinfo.get("srcDir") or "").strip("/")
            if declared and os.path.abspath(os.path.join(parent, declared)) == abs_src:
                return pinfo
            if not declared and os.path.basename(abs_src) == "src":
                return pinfo
    return None


def _select_auto_root(
    src_dir: str,
    name_to_id: Dict[str, int],
    id_to_name: List[str],
    adj: List[List[int]],
    radj: List[List[int]],
    cfg: Optional[Any],
    lake_info: Optional[Dict[str, Any]],
) -> str:
    """Resolve `--root auto` using leanre.toml -> lakefile -> Main -> repo name -> top hub."""
    if cfg is not None and cfg.root_module in name_to_id:
        return cfg.root_module

    if lake_info is not None:
        # 1) Explicit defaultTargets (e.g. FLT -> ["FLT"], PNT+ -> ["PrimeNumberTheoremAnd"])
        for t in lake_info.get("defaultTargets") or []:
            cand = str(t).strip().removesuffix(".*")
            if cand in name_to_id:
                return cand
        # 2) Declared lean_lib names / globs / roots (preferring non-*Test libraries)
        non_test_cands: List[str] = []
        test_cands: List[str] = []
        for lib in lake_info.get("lean_libs") or []:
            lname = str(lib.get("name", "")).strip()
            bucket = test_cands if lname.lower().endswith("test") else non_test_cands
            for raw in [lname, *(lib.get("globs") or []), *(lib.get("roots") or [])]:
                cand = str(raw).strip().removesuffix(".*")
                if cand in name_to_id and cand not in bucket:
                    bucket.append(cand)
        for cand in (*non_test_cands, *test_cands):
            if cand in name_to_id:
                return cand
        # 3) Declared lean_exe root modules
        for exe in lake_info.get("lean_exes") or []:
            cand = str(exe.get("root") or exe.get("name") or "").strip().removesuffix(".*")
            if cand in name_to_id:
                return cand

    if "Main" in name_to_id:
        return "Main"

    dir_base = os.path.basename(os.path.abspath(src_dir))
    if dir_base in name_to_id:
        return dir_base

    # Fallback: prefer top-level entry module with imports (highest fan-out, then fan-in == 0)
    n = len(id_to_name)
    best_id = max(
        range(n),
        key=lambda u: (
            "." not in id_to_name[u],
            len(adj[u]) > 0,
            len(adj[u]),
            len(radj[u]) == 0,
            -u,
        ),
    )
    return id_to_name[best_id]


def run_scan(
    src_dir: str,
    db_path: str,
    root_module: Optional[str] = "auto",
    workers: Optional[int] = None,
    verbose: bool = True,
    config: Optional[Any] = None,
    timeout_modules: Optional[Set[str]] = None,
    slow_targets: Optional[Dict[str, Dict[str, Any]]] = None,
    extra_forensic_regexes: Optional[Sequence[Tuple[str, str]]] = None,
    max_hits_per_tag: int = 50,
) -> Dict[str, Any]:
    """Scan all `.lean` files under `src_dir` in parallel, run graph passes, populate SQLite.

    Timeout/slow target maps come from ``config`` (``leanre.toml``) or explicit
    keyword overrides, defaulting to empty for generic repositories.
    """
    t_total = time.time()
    if config is not None:
        cfg = coerce_config(config)
    else:
        local_cfg = find_local_config(src_dir)
        cfg = coerce_config(local_cfg) if local_cfg is not None else None
    lake_info = _load_lake_hints(src_dir)

    whitelist_dirs: Set[str] = set()
    if cfg is not None:
        for sr in cfg.source_roots:
            seg = sr.strip("/").split("/")[0]
            if seg and seg != ".":
                whitelist_dirs.add(seg)
    if lake_info is not None:
        for lib in lake_info.get("lean_libs") or []:
            for cand in (lib.get("name", ""), lib.get("srcDir", "")):
                seg = str(cand).strip("/").split("/")[0]
                if seg and seg != ".":
                    whitelist_dirs.add(seg)

    eff_timeout_modules: Set[str] = (
        set(timeout_modules)
        if timeout_modules is not None
        else (set(cfg.timeout_modules) if cfg is not None else set())
    )
    eff_slow_targets: Dict[str, Dict[str, Any]] = (
        dict(slow_targets)
        if slow_targets is not None
        else (dict(cfg.slow_targets) if cfg is not None else {})
    )
    eff_extra_regexes: List[Tuple[str, str]] = (
        list(extra_forensic_regexes)
        if extra_forensic_regexes is not None
        else ([(r.tag, r.pattern) for r in cfg.extra_regexes] if cfg is not None else [])
    )

    files = discover_lean_files(src_dir, whitelist_dirs=whitelist_dirs)
    n = len(files)
    if verbose:
        print(f"[scan] discovered {n:,} .lean files under {src_dir} in {time.time() - t_total:.2f}s")
    if n == 0:
        raise ValueError(f"No .lean files found under {src_dir}")

    name_to_id: Dict[str, int] = {mod: mid for mid, mod, _ in files}
    id_to_name: List[str] = [mod for _, mod, _ in files]

    # Parallel file parse
    t_parse = time.time()
    n_workers = workers or min(12, max(1, (os.cpu_count() or 4) - 2))
    chunk_size = max(50, min(800, (n + n_workers * 8 - 1) // (n_workers * 8)))
    batches = [
        (src_dir, files[i:i + chunk_size], eff_timeout_modules, eff_slow_targets, eff_extra_regexes, int(max_hits_per_tag))
        for i in range(0, n, chunk_size)
    ]

    parsed: List[Optional[Dict[str, Any]]] = [None] * n
    if n_workers == 1 or n < 200:
        for b in batches:
            for rec in _scan_batch(b):
                parsed[rec["id"]] = rec
    else:
        with multiprocessing.Pool(processes=n_workers) as pool:
            for batch_res in pool.imap_unordered(_scan_batch, batches, chunksize=2):
                for rec in batch_res:
                    parsed[rec["id"]] = rec

    if verbose:
        print(f"[scan] parsed {n:,} files on {n_workers} workers in {time.time() - t_parse:.2f}s")

    # Build project-to-project import graph
    t_graph = time.time()
    adj: List[List[int]] = [[] for _ in range(n)]
    radj: List[List[int]] = [[] for _ in range(n)]
    edge_rows: List[Tuple[str, str]] = []
    lines_arr = [0] * n
    clone_counts: collections.Counter = collections.Counter()

    for rec in parsed:
        assert rec is not None
        u = rec["id"]
        lines_arr[u] = rec["lines"]
        clone_counts[rec["clone_sig"]] += 1
        proj_imps: List[int] = []
        for imp in rec["distinct_imports"]:
            v = name_to_id.get(imp)
            if v is not None and v != u:
                proj_imps.append(v)
        adj[u] = proj_imps
        for v in proj_imps:
            radj[v].append(u)
            edge_rows.append((rec["name"], id_to_name[v]))

    project_edges_count = len(edge_rows)
    eff_root_module = root_module
    if eff_root_module in (None, "", "auto"):
        eff_root_module = _select_auto_root(src_dir, name_to_id, id_to_name, adj, radj, cfg, lake_info)
    elif eff_root_module == "Main" and "Main" not in name_to_id and cfg is not None and cfg.root_module in name_to_id:
        eff_root_module = cfg.root_module

    root_id = name_to_id.get(eff_root_module)
    if root_id is None:
        raise ValueError(f"Root module {eff_root_module!r} not found under {src_dir}")

    # BFS shortest paths from root, bottom depths, CHK dominators, exact rev_reach
    bfs_depth, parent_to_main = bfs_shortest_paths([root_id], adj, n)
    b_depth = bottom_depths_dag(adj, n)
    idom, rpo, dom_size, dom_lines, dom_children = dominators_chk(root_id, adj, radj, n, weights=lines_arr)
    rev_reach = compute_rev_reach_exact(adj, n, batch_size=4096)

    if verbose:
        print(
            f"[scan] graph passes ({project_edges_count:,} edges, reach={len(rpo):,}, max_depth={max(b_depth) if b_depth else 0}) in {time.time() - t_graph:.2f}s"
        )

    # Identify hub & top-level single-entry components
    hub_id = root_id
    if dom_children.get(root_id):
        heavy_child = max(dom_children[root_id], key=lambda c: dom_size[c])
        if dom_size[heavy_child] > 0.9 * len(rpo):
            hub_id = heavy_child

    top_comp_ids = dom_children.get(hub_id, [])
    top_comp_sizes = [dom_size[c] for c in top_comp_ids]
    singleton_comps = sum(1 for sz in top_comp_sizes if sz == 1)
    comp_buckets = {
        "1000+": {"components": 0, "modules": 0, "lines": 0},
        "100-999": {"components": 0, "modules": 0, "lines": 0},
        "10-99": {"components": 0, "modules": 0, "lines": 0},
        "2-9": {"components": 0, "modules": 0, "lines": 0},
        "1": {"components": 0, "modules": 0, "lines": 0},
    }
    for c in top_comp_ids:
        sz = dom_size[c]
        ln = dom_lines[c]
        bk = "1000+" if sz >= 1000 else ("100-999" if sz >= 100 else ("10-99" if sz >= 10 else ("2-9" if sz >= 2 else "1")))
        comp_buckets[bk]["components"] += 1
        comp_buckets[bk]["modules"] += sz
        comp_buckets[bk]["lines"] += ln

    largest_components = [
        {
            "entry": id_to_name[c],
            "modules": dom_size[c],
            "lines": dom_lines[c],
            "namespace_top": id_to_name[c].split(".")[0],
        }
        for c in sorted(top_comp_ids, key=lambda c: -dom_size[c])[:20]
    ]

    # Aggregate SQLite rows, namespace stats, forensic hits, declarations, horn_edges
    t_agg = time.time()
    module_rows: List[Tuple[Any, ...]] = []
    decl_rows: List[Tuple[Any, ...]] = []
    horn_edge_rows: List[Tuple[Any, ...]] = []
    forensic_hit_rows: List[Tuple[Any, ...]] = []

    ns_agg: Dict[str, Dict[str, Any]] = {}
    ns_inner_decl_ctr: Dict[str, collections.Counter] = collections.defaultdict(collections.Counter)

    total_lines_wc = 0
    total_lines_eof = 0
    total_bytes = 0
    total_trailing_nl = 0
    total_decls = 0
    total_thms = 0
    total_defs = 0
    total_shims = 0
    total_dup_proj_imports = 0
    total_dup_mathlib_imports = 0
    total_dup_all_imports = 0
    total_mathlib_imports = 0
    zero_proj_imports = 0
    forensic_tag_modules: collections.Counter = collections.Counter()
    forensic_tag_hits: collections.Counter = collections.Counter()
    forensic_tag_total_hits: collections.Counter = collections.Counter()
    forensic_tag_truncated_hits: collections.Counter = collections.Counter()
    forensic_tag_truncated_modules: collections.Counter = collections.Counter()
    decl_kind_totals: collections.Counter = collections.Counter()
    decl_id_seq = 0
    horn_id_seq = 0
    hit_id_seq = 0

    def _ensure_ns(prefix: str, depth: int, parent: Optional[str]) -> Dict[str, Any]:
        d = ns_agg.get(prefix)
        if d is None:
            d = {
                "prefix": prefix,
                "depth": depth,
                "parent": parent,
                "module_count": 0,
                "lines_wc": 0,
                "lines_eof": 0,
                "bytes": 0,
                "decl_count": 0,
                "thm_count": 0,
                "def_count": 0,
                "shim_count": 0,
                "mathlib_import_count": 0,
                "forensic_hit_count": 0,
            }
            ns_agg[prefix] = d
        return d

    for rec in parsed:
        assert rec is not None
        u = rec["id"]
        mname = rec["name"]
        parts = mname.split(".")
        ns_top = parts[0]
        ns_l2 = f"{parts[0]}.{parts[1]}" if len(parts) >= 2 else parts[0]

        total_lines_wc += rec["lines_wc"]
        total_lines_eof += rec["lines"]
        total_bytes += rec["bytes"]
        total_trailing_nl += rec["trailing_nl"]
        total_decls += rec["decl_count"]
        total_thms += rec["thm_count"]
        total_defs += rec["def_count"]
        for dk, dcnt in rec.get("decl_kind_counts", {}).items():
            decl_kind_totals[dk] += dcnt
        for tg, tcnt in rec.get("tag_total_counts", {}).items():
            forensic_tag_total_hits[tg] += tcnt
        for tg, ttrunc in rec.get("tag_truncated_counts", {}).items():
            if ttrunc > 0:
                forensic_tag_truncated_hits[tg] += ttrunc
                forensic_tag_truncated_modules[tg] += 1
        total_shims += rec["is_shim"]
        proj_dups = sum(c for k, c in rec["dup_import_targets"].items() if k in name_to_id)
        ml_dups = rec["dup_import_targets"].get("Mathlib", 0)
        total_dup_proj_imports += proj_dups
        total_dup_mathlib_imports += ml_dups
        total_dup_all_imports += rec["dup_imports_all"]
        total_mathlib_imports += rec["imports_mathlib"]
        if len(adj[u]) == 0:
            zero_proj_imports += 1

        flags = rec["flags"]
        bitmask = flags_to_bitmask(flags)
        for fl in flags:
            forensic_tag_modules[fl] += 1

        p_main_name = id_to_name[parent_to_main[u]] if parent_to_main[u] != -1 else None
        dom_p_name = id_to_name[idom[u]] if (idom[u] != -1 and u != root_id) else None
        csig = rec["clone_sig"]
        csize = clone_counts[csig] if csig != "shim_empty" else 1

        module_rows.append((
            u + 1,
            mname,
            rec["file_path"],
            ns_top,
            ns_l2,
            rec["lines"],
            rec["lines_wc"],
            rec["bytes"],
            rec["trailing_nl"],
            rec["decl_count"],
            rec["thm_count"],
            rec["def_count"],
            len(adj[u]),
            rec["imports_mathlib"],
            len(radj[u]),
            len(adj[u]),
            bfs_depth[u],
            b_depth[u],
            p_main_name,
            dom_p_name,
            dom_size[u],
            dom_lines[u],
            rev_reach[u],
            rec["is_shim"],
            proj_dups,
            csig,
            csize,
            rec["zlib_ratio"],
            bitmask,
            json.dumps(flags, ensure_ascii=False),
        ))

        # Namespace stats (depth 1 and depth 2)
        ns1 = _ensure_ns(ns_top, 1, None)
        ns_targets = [ns1]
        if ns_l2 != ns_top:
            ns_targets.append(_ensure_ns(ns_l2, 2, ns_top))
        n_hits_mod = len(rec["hits"])
        for nsd in ns_targets:
            nsd["module_count"] += 1
            nsd["lines_wc"] += rec["lines_wc"]
            nsd["lines_eof"] += rec["lines"]
            nsd["bytes"] += rec["bytes"]
            nsd["decl_count"] += rec["decl_count"]
            nsd["thm_count"] += rec["thm_count"]
            nsd["def_count"] += rec["def_count"]
            nsd["shim_count"] += rec["is_shim"]
            nsd["mathlib_import_count"] += rec["imports_mathlib"]
            nsd["forensic_hit_count"] += n_hits_mod
            ctr = ns_inner_decl_ctr[nsd["prefix"]]
            for ip in rec["inner_decl_prefixes"]:
                ctr[ip] += 1

        # Declarations & Horn edges
        for full_name, kind, lno, sig_snip, h_reqs, h_prov, d_tags in rec["decls"]:
            decl_id_seq += 1
            decl_rows.append((
                decl_id_seq,
                full_name,
                kind,
                mname,
                lno,
                sig_snip,
                json.dumps(h_reqs, ensure_ascii=False),
                h_prov,
                json.dumps(d_tags, ensure_ascii=False),
            ))
            if h_prov and h_reqs:
                for rq in h_reqs:
                    if rq != h_prov:
                        horn_id_seq += 1
                        horn_edge_rows.append((
                            horn_id_seq,
                            rq,
                            h_prov,
                            decl_id_seq,
                            full_name,
                            mname,
                            lno,
                        ))

        # Forensic hits + shortest path to Main
        if rec["hits"]:
            path_ids = reconstruct_path_to_root(u, parent_to_main)
            path_names = [id_to_name[x] for x in path_ids]
            path_json = json.dumps(path_names, ensure_ascii=False)
            hops = bfs_depth[u]
            for tag, lno, dname, snip in rec["hits"]:
                hit_id_seq += 1
                forensic_tag_hits[tag] += 1
                forensic_hit_rows.append((
                    hit_id_seq,
                    tag,
                    FORENSIC_SEVERITY.get(tag, "info"),
                    mname,
                    lno,
                    dname,
                    snip,
                    hops,
                    path_json,
                ))

    ns_rows: List[Tuple[Any, ...]] = []
    ns_list_for_json: List[Dict[str, Any]] = []
    for pref, d in sorted(ns_agg.items(), key=lambda kv: (kv[1]["depth"], -kv[1]["module_count"])):
        top_inner = [
            {"prefix": k, "count": v}
            for k, v in ns_inner_decl_ctr[pref].most_common(12)
        ]
        ns_rows.append((
            d["prefix"],
            d["depth"],
            d["parent"],
            d["module_count"],
            d["lines_wc"],
            d["lines_eof"],
            d["bytes"],
            d["decl_count"],
            d["thm_count"],
            d["def_count"],
            d["shim_count"],
            d["mathlib_import_count"],
            d["forensic_hit_count"],
            json.dumps(top_inner, ensure_ascii=False),
        ))
        ns_list_for_json.append({**d, "top_decl_prefixes": top_inner})

    # Clone stats (exact alpha-renamed multi-module clusters)
    multi_clusters = [(sig, cnt) for sig, cnt in clone_counts.items() if cnt >= 2 and sig != "shim_empty"]
    multi_clusters.sort(key=lambda x: -x[1])
    clone_modules_total = sum(cnt for _, cnt in multi_clusters)
    redundant_clone_modules = sum(cnt - 1 for _, cnt in multi_clusters)

    top_imported = [
        {
            "module": id_to_name[v],
            "fan_in": len(radj[v]),
            "rev_reach": rev_reach[v],
            "lines": lines_arr[v],
        }
        for v in sorted(range(n), key=lambda x: -len(radj[x]))[:20]
    ]

    depth_hist = {
        "0": sum(1 for d in b_depth if d == 0),
        "1-5": sum(1 for d in b_depth if 1 <= d <= 5),
        "6-20": sum(1 for d in b_depth if 6 <= d <= 20),
        "21-50": sum(1 for d in b_depth if 21 <= d <= 50),
        "51-100": sum(1 for d in b_depth if 51 <= d <= 100),
        "101+": sum(1 for d in b_depth if d >= 101),
    }

    corpus_stats = {
        "root_module": eff_root_module,
        "modules": n,
        "project_import_edges": project_edges_count,
        "lines_wc": total_lines_wc,
        "lines_eof": total_lines_eof,
        "bytes": total_bytes,
        "trailing_nl_present": total_trailing_nl,
        "trailing_nl_missing": n - total_trailing_nl,
        "declarations": total_decls,
        "theorems": total_thms,
        "definitions": total_defs,
        "decl_counts_by_kind": dict(sorted(decl_kind_totals.items())),
        "horn_edges": len(horn_edge_rows),
        "reachable_from_main": len(rpo),
        "max_bfs_depth": max(bfs_depth) if bfs_depth else 0,
        "max_import_depth": max(b_depth) if b_depth else 0,
        "hub": id_to_name[hub_id],
        "hub_dominates": dom_size[hub_id],
        "hub_strictly_dominates": dom_size[hub_id] - 1,
        "top_level_components": len(top_comp_ids),
        "singleton_components": singleton_comps,
        "top_level_by_size": comp_buckets,
        "modules_with_no_project_imports": zero_proj_imports,
        "import_only_shims": total_shims,
        "duplicate_import_lines": total_dup_proj_imports,
        "duplicate_mathlib_import_lines": total_dup_mathlib_imports,
        "duplicate_all_import_lines": total_dup_all_imports,
        "modules_importing_whole_mathlib": total_mathlib_imports,
        "modules_by_import_depth": depth_hist,
        "largest_components": largest_components,
        "top_imported_modules": top_imported,
        "clone_stats": {
            "multi_module_clusters": len(multi_clusters),
            "modules_in_clusters": clone_modules_total,
            "redundant_modules": redundant_clone_modules,
            "largest_cluster_size": multi_clusters[0][1] if multi_clusters else 0,
        },
        "max_hits_per_tag": int(max_hits_per_tag),
        "forensic_module_counts": dict(forensic_tag_modules),
        "forensic_hit_counts": dict(forensic_tag_hits),
        "forensic_total_hit_counts": dict(forensic_tag_total_hits),
        "forensic_truncated_hit_counts": dict(forensic_tag_truncated_hits),
        "forensic_truncated_module_counts": dict(forensic_tag_truncated_modules),
        "namespaces": ns_list_for_json,
    }
    if cfg is not None and cfg.rh_gates:
        corpus_stats["drew2apps_split_lines_equiv"] = total_lines_wc + n

    if verbose:
        trunc_note = ""
        if forensic_tag_truncated_hits:
            trunc_note = f" (truncated hits by cap={max_hits_per_tag}: {dict(forensic_tag_truncated_hits)})"
        print(
            f"[scan] aggregated {len(decl_rows):,} decls, {len(horn_edge_rows):,} horn_edges, "
            f"{len(forensic_hit_rows):,} forensic_hits{trunc_note} in {time.time() - t_agg:.2f}s"
        )

    # Bulk write SQLite
    t_db = time.time()
    conn = open_db(db_path, bulk_mode=True)
    try:
        for tbl in ("modules", "module_edges", "declarations", "horn_edges", "forensic_hits", "namespace_stats"):
            conn.execute(f"DELETE FROM {tbl};")
        conn.executemany(
            """INSERT INTO modules(
                id, name, file_path, namespace_top, namespace_l2, lines, lines_wc, bytes,
                trailing_nl, decl_count, thm_count, def_count, import_count, imports_mathlib,
                fan_in, fan_out, bfs_depth, bottom_depth, parent_to_main, dom_parent,
                dom_subtree_size, dom_subtree_lines, rev_reach, is_shim, dup_imports,
                clone_sig, clone_cluster_size, zlib_ratio, forensic_flags_bitmask, forensic_flags_json
            ) VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)""",
            module_rows,
        )
        conn.executemany("INSERT INTO module_edges(src, dst) VALUES (?,?)", edge_rows)
        conn.executemany(
            """INSERT INTO declarations(
                id, name, kind, module, line_no, signature_snippet,
                horn_requires_json, horn_proves, forensic_tags
            ) VALUES (?,?,?,?,?,?,?,?,?)""",
            decl_rows,
        )
        conn.executemany(
            """INSERT INTO horn_edges(
                id, req_prop, prov_prop, decl_id, decl_name, module, line_no
            ) VALUES (?,?,?,?,?,?,?)""",
            horn_edge_rows,
        )
        conn.executemany(
            """INSERT INTO forensic_hits(
                id, tag, severity, module, line_no, decl_name, snippet,
                hops_to_main, shortest_path_to_main_json
            ) VALUES (?,?,?,?,?,?,?,?,?)""",
            forensic_hit_rows,
        )
        conn.executemany(
            """INSERT INTO namespace_stats(
                prefix, depth, parent, module_count, lines_wc, lines_eof, bytes,
                decl_count, thm_count, def_count, shim_count, mathlib_import_count,
                forensic_hit_count, top_decl_prefixes_json
            ) VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?)""",
            ns_rows,
        )
        conn.executescript(INDEX_SQL_SCAN)
        set_meta(conn, "corpus_stats", {k: v for k, v in corpus_stats.items() if k != "namespaces"})
        set_meta(conn, "forensic_summary", {
            "module_counts": dict(forensic_tag_modules),
            "hit_counts": dict(forensic_tag_hits),
            "total_hit_counts": dict(forensic_tag_total_hits),
            "truncated_hit_counts": dict(forensic_tag_truncated_hits),
            "max_hits_per_tag": int(max_hits_per_tag),
        })
        finalize_db(conn)
    finally:
        conn.close()

    corpus_stats["elapsed_seconds"] = round(time.time() - t_total, 2)
    if verbose:
        print(f"[scan] wrote SQLite {db_path} in {time.time() - t_db:.2f}s (total {corpus_stats['elapsed_seconds']}s)")
    return corpus_stats


def main(argv: Optional[Sequence[str]] = None) -> int:
    ap = argparse.ArgumentParser(
        prog="leanre-scanner",
        description="Parallel Lean 4 source scanner -> SQLite modules/edges/decls/horn/forensics",
    )
    ap.add_argument("src_pos", nargs="?", default=None, help="Path to Lean source directory")
    ap.add_argument("--src", dest="src_opt", default=None, help="Path to Lean source directory")
    ap.add_argument("--out-db", required=True, help="Output SQLite database path")
    ap.add_argument("--out-json", default=None, help="Optional JSON summary output path")
    ap.add_argument("--root", default="auto", help="Root module name (default: auto / config root_module)")
    ap.add_argument("--config", default=None, help="Optional path to leanre.toml profile")
    ap.add_argument("--workers", type=int, default=None, help="Worker process count")
    ap.add_argument(
        "--max-hits-per-tag",
        type=int,
        default=50,
        help="Max forensic_hits rows per module per tag (0 = unlimited, default: 50)",
    )
    ap.add_argument("--quiet", action="store_true", help="Suppress progress logs")
    args = ap.parse_args(argv)

    cfg = coerce_config(args.config) if args.config else None
    src_dir = args.src_opt or args.src_pos
    if not src_dir:
        if cfg is not None:
            src_dir = cfg.resolve_src_dir()
        else:
            ap.error("a source directory is required (positional or --src)")

    os.makedirs(os.path.dirname(os.path.abspath(args.out_db)), exist_ok=True)
    stats = run_scan(
        src_dir=src_dir,
        db_path=args.out_db,
        root_module=args.root,
        workers=args.workers,
        verbose=not args.quiet,
        config=cfg,
        max_hits_per_tag=args.max_hits_per_tag,
    )
    if args.out_json:
        os.makedirs(os.path.dirname(os.path.abspath(args.out_json)), exist_ok=True)
        with open(args.out_json, "w", encoding="utf-8") as f:
            json.dump(stats, f, indent=2, ensure_ascii=False)
    return 0


if __name__ == "__main__":
    sys.exit(main())
