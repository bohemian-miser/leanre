#!/usr/bin/env python3
"""R3 Guardrails 1-6 & canonical-facts tripwire scanner (verifier-owned).

Scans Phase 3 docs, workbench UI files, annotations, and committed summary JSONs for:
  - forbidden / disproved phrasings ("automorphy lifting", "4 Dirichlet", "772" digits,
    "131,072" steps, "lacks a trailing newline", unqualified "RH is proved", etc.)
  - bare declaration counts 1,468,418 / 1,484,733 without checker attribution nearby
  - presence of epistemic layer framing & provenance tags in new docs
  - presence of synthetic/fixture banners in UI code

Tripwire hits are printed with file:line context for manual verifier adjudication (not all
hits are violations — e.g. a doc explicitly saying "do NOT say automorphy lifting").
"""
from __future__ import annotations

import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(ROOT)

TRIPWIRES = [
    ("automorphy-lifting", re.compile(r"automorphy\s+lifting", re.I)),
    ("4-dirichlet", re.compile(r"\b(?:4|four)\s+Dirichlet", re.I)),
    ("extended-rh", re.compile(r"\bExtended\s+RH\b|\bERH\b")),
    ("rh-proved-claim", re.compile(r"\b(?:RH\s+is\s+proved|proves\s+(?:the\s+)?(?:RH|Riemann\s+Hypothesis)|proof\s+of\s+(?:the\s+)?(?:RH|Riemann\s+Hypothesis)\s+is\s+complete|verified\s+RH)\b", re.I)),
    ("masullo", re.compile(r"\bMasullo\b", re.I)),
    ("bad-362-digits", re.compile(r"\b772\s+(?:decimal\s+)?digits\b", re.I)),
    ("bad-run-steps", re.compile(r"\b131,?072[- ]step", re.I)),
    ("bad-trailing-nl", re.compile(r"lacks?\s+a\s+trailing\s+newline|missing\s+trailing\s+newline", re.I)),
    ("bare-decl-count", re.compile(r"\b1,?468,?418\b|\b1,?484,?733\b")),
]

SKIP = {"verify/", "research/", "outputs/phase2_verification_report.md", "HANDOFF.md", "docs/PHASE3_GATES.md", "docs/PHASE4_GATES.md"}


def is_text(p):
    try:
        return b"\0" not in open(p, "rb").read(8192)
    except OSError:
        return False


def main():
    tracked = [p for p in subprocess.run(["git", "ls-files", "-z"], capture_output=True, text=True, check=True).stdout.split("\0") if p]
    untracked = [p for p in subprocess.run(["git", "ls-files", "-o", "--exclude-standard", "-z"], capture_output=True, text=True, check=True).stdout.split("\0") if p]
    files = sorted(set(tracked + untracked))

    print("=== R3 Tripwire scan over Phase-3 / non-historical files ===")
    hits = 0
    for p in files:
        if any(p.startswith(s) or p == s for s in SKIP):
            continue
        if not os.path.isfile(p) or os.path.islink(p) or not is_text(p):
            continue
        lines = open(p, encoding="utf-8", errors="replace").readlines()
        for ln, line in enumerate(lines, 1):
            for tag, rx in TRIPWIRES:
                if rx.search(line):
                    if tag == "bare-decl-count":
                        ctx = "".join(lines[max(0, ln - 2):min(len(lines), ln + 2)])
                        if re.search(r"con-leche|nanoda|nasqret|record|constant|fold", ctx, re.I):
                            continue
                    hits += 1
                    print(f"  [{tag}] {p}:{ln}: {line.strip()[:140]}")
    print(f"Tripwire hits to inspect: {hits}\n")

    print("=== R3 Doc checklist (docs/*.md and analysis/*.md excluding PHASE*_GATES.md) ===")
    for p in sorted(f for f in files if (f.startswith("docs/") or f.startswith("analysis/")) and f.endswith(".md") and f not in ("docs/PHASE3_GATES.md", "docs/PHASE4_GATES.md")):
        t = open(p, encoding="utf-8", errors="replace").read()
        tags = sorted(set(re.findall(r"\[([LACSM])\]", t)))
        layers = bool(re.search(r"Layer\s*[1-4]|epistemic|Guardrail", t, re.I))
        limits = bool(re.search(r"limit|is not|not a proof|never|caveat|breaks", t, re.I))
        print(f"  {p}: bytes={len(t):,} tags={tags} layer_or_guardrail_ref={layers} limits_stated={limits}")

    print("\n=== R3 Workbench UI guardrail checks (workbench/*) ===")
    for p in sorted(f for f in files if f.startswith("workbench/") and os.path.isfile(f)):
        t = open(p, encoding="utf-8", errors="replace").read()
        has_synth = bool(re.search(r"SYNTHETIC|FIXTURE|STUB|DEMO|not built yet", t, re.I))
        has_draft = bool(re.search(r"AI[- ]?DRAFT|draft", t, re.I))
        has_tags = sorted(set(re.findall(r"\[([LACSM])\]", t)))
        print(f"  {p}: tags={has_tags} synthetic_or_missing_banner={has_synth} draft_marker={has_draft}")


if __name__ == "__main__":
    main()
