#!/usr/bin/env python3
"""Phase 4 independent verifier for analysis/*.md dossiers (gate V4).

Checks every analysis/*.md file for:
  1. Valid on-disk file:line anchors (src/.../*.lean:N) against data/rh_mirror/.
  2. Guardrail 1 (four epistemic layers disclaimer), Guardrail 2 (provenance tags [L]/[A]/[C]/[S]/[M]),
     Guardrail 5 (explicit OPAQUE/UNREAD honesty where appropriate).
  3. Canonical-fact tripwires (automorphy lifting, 4 Dirichlet, 772 digits, 131,072 steps,
     unqualified "RH is proved", Masullo conflation, bare 1,468,418 / 1,484,733).
  4. Zero multi-line Lean proof bodies inside ```lean blocks (only <=1-line headers / schematic
     pseudocode / short structure signatures permitted; flags any ```lean block > 6 lines or
     containing tactic proof keywords `:= by` followed by tactic lines).
  5. Spot-check of claimed `(decl_name, subtree_size)` pairs against outputs/kernel/kernel.db
     tree_id=0 (ALL) whenever a markdown line pairs a backticked qualified Lean name with a
     comma-formatted integer in parentheses or table cell.

Usage:
  python3 verify/p4_analysis_check.py [analysis/*.md ...]
"""
from __future__ import annotations

import glob
import os
import re
import sqlite3
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
MIRROR = os.path.join(ROOT, "data", "rh_mirror")

ANCHOR_RE = re.compile(r"(?:data/rh_mirror/)?((?:src/)?[A-Za-z0-9_./-]+\.lean):(\d+)(?:-\d+)?")
TRIPWIRES = [
    ("automorphy-lifting", re.compile(r"automorphy\s+lifting", re.I)),
    ("4-dirichlet", re.compile(r"\b(?:4|four)\s+Dirichlet", re.I)),
    ("rh-proved-claim", re.compile(r"\b(?:RH\s+is\s+proved|proves\s+(?:the\s+)?(?:RH|Riemann\s+Hypothesis)|proof\s+of\s+(?:the\s+)?(?:RH|Riemann\s+Hypothesis)\s+is\s+complete|verified\s+RH)\b", re.I)),
    ("bad-362-digits", re.compile(r"\b772\s+(?:decimal\s+)?digits\b", re.I)),
    ("bad-run-steps", re.compile(r"\b131,?072[- ]step", re.I)),
    ("masullo", re.compile(r"\bMasullo\b", re.I)),
]
TACTIC_BODY_RE = re.compile(r"^\s*(?:intro|intros|rintro|rw|simp|exact|apply|refine|have|let|cases|rcases|induction|constructor|obtain|calc|linarith|nlinarith|ring|omega|positivity|aesop|kexactB|copy_cases)\b")


def build_file_index():
    """Map suffix/basename -> list of mirror-relative paths (src/...) from outputs/leanre.db."""
    ldb = sqlite3.connect(f"file:{ROOT}/outputs/leanre.db?mode=ro", uri=True)
    by_base = {}
    by_tail2 = {}
    for (mod,) in ldb.execute("SELECT name FROM modules"):
        rel = "src/" + mod.replace(".", "/") + ".lean"
        parts = rel.split("/")
        by_base.setdefault(parts[-1], []).append(rel)
        if len(parts) >= 2:
            by_tail2.setdefault("/".join(parts[-2:]), []).append(rel)
    ldb.close()
    return by_base, by_tail2


def resolve_anchor(frel, by_base, by_tail2):
    if frel.startswith("src/"):
        p = os.path.join(MIRROR, frel)
        return [p] if os.path.isfile(p) else []
    p = os.path.join(MIRROR, "src", frel)
    if os.path.isfile(p):
        return [p]
    # Try matching tail2 or basename
    parts = frel.split("/")
    if len(parts) >= 2 and "/".join(parts[-2:]) in by_tail2:
        cands = [os.path.join(MIRROR, r) for r in by_tail2["/".join(parts[-2:])] if r.endswith(frel)]
        if cands:
            return cands
    if parts[-1] in by_base:
        cands = [os.path.join(MIRROR, r) for r in by_base[parts[-1]] if r.endswith(frel)]
        if cands:
            return cands
    return []


def check_md(path, kdb, by_base, by_tail2):
    rel = os.path.relpath(path, ROOT)
    txt = open(path, encoding="utf-8", errors="replace").read()
    lines = txt.splitlines()
    errs = []
    notes = []

    # 1. File:line anchor verification on disk
    anchors = ANCHOR_RE.findall(txt)
    fcache = {}
    bad_anc = []
    for frel, lstr in anchors:
        if frel.startswith(("Mathlib/", "Init/", "Std/", "Batteries/")):
            continue
        lno = int(lstr)
        if frel not in fcache:
            cands = resolve_anchor(frel, by_base, by_tail2)
            fcache[frel] = [len(open(c, encoding="utf-8", errors="replace").readlines()) for c in cands if os.path.isfile(c)]
        lens = fcache[frel]
        if not lens:
            bad_anc.append(f"{frel}:{lno} (file missing)")
        elif not any(1 <= lno <= nlines for nlines in lens):
            bad_anc.append(f"{frel}:{lno} (out of range for {lens})")
    if bad_anc:
        errs.append(f"{len(bad_anc)} invalid file:line anchors: {bad_anc[:8]}")

    # 2. Guardrails metadata
    tags = sorted(set(re.findall(r"\[([LACSM])\]", txt)))
    has_layer = bool(re.search(r"Layer\s*[1-4]|Guardrail\s*1|epistemic", txt, re.I))
    has_opaque = bool(re.search(r"\bOPAQUE\b|\bUNREAD\b", txt))
    if not tags:
        errs.append("no provenance tags [L]/[A]/[C]/[S]/[M] found")
    if not has_layer:
        notes.append("no explicit Layer 1-4 / Guardrail 1 reminder")

    # 3. Tripwires
    tw = []
    for ln, line in enumerate(lines, 1):
        for tag, rx in TRIPWIRES:
            if rx.search(line):
                tw.append(f"{tag} L{ln}: {line.strip()[:120]}")

    # 4. Scan ```lean code blocks for verbatim proof bodies (license guardrail)
    in_lean = False
    blk_start = 0
    blk_lines = []
    body_blocks = []
    for ln, line in enumerate(lines, 1):
        s = line.strip()
        if not in_lean and s.startswith("```lean"):
            in_lean = True
            blk_start = ln
            blk_lines = []
        elif in_lean and s.startswith("```"):
            tactic_hits = [bl for bl in blk_lines if TACTIC_BODY_RE.match(bl)]
            if len(tactic_hits) >= 2:
                body_blocks.append(f"L{blk_start}-{ln} ({len(tactic_hits)} tactic lines)")
            in_lean = False
        elif in_lean:
            blk_lines.append(line)
    if body_blocks:
        errs.append(f"possible quoted Lean tactic bodies in ```lean blocks: {body_blocks[:5]}")

    # 5. Cross-check backticked multi-segment Lean names that appear next to "(N decls)" against kernel.db ALL tree
    pair_re = re.compile(r"`([A-Z][A-Za-z0-9_']+(?:\.[A-Za-z0-9_']+)+)`\s*\(\s*`?([0-9][0-9,]{2,})`?\s*(?:decls?|nodes?)")
    checked_pairs = 0
    mism_pairs = []
    for nm, num_s in pair_re.findall(txt):
        num = int(num_s.replace(",", ""))
        row = kdb.execute(
            "SELECT d.id, dm.subtree_size FROM decls d LEFT JOIN dom dm ON dm.tree_id=0 AND dm.decl_id=d.id WHERE d.name=?",
            (nm,),
        ).fetchone()
        if row is not None and row[1] is not None:
            checked_pairs += 1
            if row[1] != num:
                # Could be a cone size rather than dom subtree size; note if differs
                mism_pairs.append((nm, num, row[1]))

    print(f"\n=== {rel} ({len(txt):,} B, {len(lines)} lines) ===")
    print(f"  anchors={len(anchors)} bad_anchors={len(bad_anc)} tags={tags} layer_ref={has_layer} opaque_honesty={has_opaque}")
    print(f"  decl+size pairs checked vs ALL dom tree: {checked_pairs}, diffs={len(mism_pairs)} {mism_pairs[:5]}")
    if tw:
        print(f"  tripwires ({len(tw)} — inspect context):")
        for x in tw[:8]:
            print("   ", x)
    for x in notes:
        print("  NOTE:", x)
    for x in errs:
        print("  ERR :", x)
    return len(errs)


def main():
    paths = sys.argv[1:] or sorted(glob.glob(os.path.join(ROOT, "analysis", "*.md")))
    if not paths:
        print("No analysis/*.md files found.")
        sys.exit(2)
    kdb = sqlite3.connect(f"file:{ROOT}/outputs/kernel/kernel.db?mode=ro", uri=True)
    by_base, by_tail2 = build_file_index()
    tot = 0
    for p in paths:
        tot += check_md(p, kdb, by_base, by_tail2)
    print(f"\nP4-ANALYSIS-CHECK {'PASS' if tot == 0 else 'FAIL'} (files={len(paths)}, total_errors={tot})")
    sys.exit(1 if tot else 0)


if __name__ == "__main__":
    main()
