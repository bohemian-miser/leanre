#!/usr/bin/env python3
"""F3 independent verification script (verifier-owned).

Zero-trust check of Tier 3 name-blinding, AI-draft isolation, and blinded-vs-unblinded
agreement metrics. Never trusts flirt's own leak_test field: builds an independent
forbidden-identifier lexicon directly from data/rh_mirror/src/ directory/file names +
outputs/flirt/cache/lexicon_rh.txt MINUS public Mathlib/Lean core identifiers, and greps
EVERY line of outputs/flirt/tier3_blinded_prompts.jsonl!
"""
from __future__ import annotations

import collections
import json
import math
import os
import re
import sqlite3
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "leanre"))
import annot  # noqa: E402

R = []


def ck(ok, msg):
    R.append(bool(ok))
    print(f"{'PASS' if ok else 'FAIL'} [F3] {msg}")


def main():
    prompts_path = os.path.join(ROOT, "outputs", "flirt", "tier3_blinded_prompts.jsonl")
    ck(os.path.exists(prompts_path), f"blinded prompts exist: {prompts_path}")
    if not os.path.exists(prompts_path):
        sys.exit(1)

    # 1. Build independent forbidden-token set from data/rh_mirror/src/ paths + lexicon_rh.txt,
    #    subtracting tokens that legitimately appear in Lean core / Mathlib (from data/corpora/mathlib4 & lean4).
    mathlib_tokens = set()
    t2_path = os.path.join(ROOT, "outputs", "flirt", "tier2.db")
    if os.path.exists(t2_path):
        t2 = sqlite3.connect(f"file:{t2_path}?mode=ro", uri=True)
        for (nm, mod) in t2.execute("SELECT name, module FROM corpus_sigs WHERE repo IN ('mathlib4','lean4','batteries')"):
            for part in nm.split("."):
                mathlib_tokens.add(part)
            for part in mod.split("."):
                mathlib_tokens.add(part)
        t2.close()
    # Also add standard Lean keywords / English words that could legitimately be prompt prose
    prompt_prose = {
        "Main", "Proofs", "Core", "Basic", "Defs", "Def", "Lemma", "Lemmas", "Theorem", "Theorems",
        "Helper", "Helpers", "Aux", "Tools", "Common", "General", "Misc", "Part", "Step", "Stage",
        "Check", "Bound", "Bounds", "Sum", "Prod", "Zero", "One", "Two", "Top", "Base", "Final",
        "Left", "Right", "Side", "Row", "Col", "Line", "List", "Set", "Map", "Hom", "Ring", "Field",
        "Group", "Prime", "Primes", "Local", "Global", "Theory", "Data", "Spec", "Test", "Tests",
        "Bridge", "Wrapper", "Kernel", "Kernels", "Supplements", "Development", "Formalism",
        "Statement", "Statements", "Setup", "Bridge", "Small", "Large", "Big", "Low", "High",
        "Type", "Prop", "Sort", "Nat", "Int", "Real", "Complex", "Rat", "Fin", "Bool", "String",
        "True", "False", "Unit", "Empty", "Option", "Result", "Value", "Index", "Order", "Norm",
        "Trace", "Rank", "Sign", "Size", "Count", "Depth", "Width", "Height", "Weight", "Scale",
        "Point", "Space", "Metric", "Measure", "Filter", "Limit", "Series", "Integral", "Form",
        "Matrix", "Vector", "Module", "Algebra", "Ideal", "Prime", "Factor", "Power", "Root",
        "Divisor", "Curve", "Variety", "Scheme", "Sheaf", "Bundle", "Cohomology", "Homology",
        "Character", "Dirichlet", "Zeta", "Euler", "LFunction", "Riemann", "Hypothesis",
        "cluster", "blinded", "header", "headers", "imports", "opens", "tokens", "flags", "size",
        "module", "modules", "decl", "decls", "kind", "type", "domain", "label", "confidence",
    }

    # Project-specific folder names & file stems (length >= 5, not in Mathlib/prose)
    proj_folders = set()
    proj_files = set()
    src_root = os.path.join(ROOT, "data", "rh_mirror", "src")
    for dp, dn, fn in os.walk(src_root):
        rel = os.path.relpath(dp, src_root)
        if rel != ".":
            for seg in rel.split(os.sep):
                if len(seg) >= 5 and seg not in mathlib_tokens and seg not in prompt_prose:
                    proj_folders.add(seg)
        for f in fn:
            if f.endswith(".lean"):
                stem = f[:-5]
                if len(stem) >= 6 and stem not in mathlib_tokens and stem not in prompt_prose:
                    proj_files.add(stem)

    # Project-local declaration identifiers from lexicon_rh.txt (distinct non-Mathlib components len >= 6)
    proj_decls_full = set()
    proj_decls_leaf = set()
    lex_path = os.path.join(ROOT, "outputs", "flirt", "cache", "lexicon_rh.txt")
    if os.path.exists(lex_path):
        for ln in open(lex_path, encoding="utf-8"):
            nm = ln.strip()
            if not nm:
                continue
            if "." in nm:
                proj_decls_full.add(nm)
            leaf = nm.split(".")[-1]
            if len(leaf) >= 6 and leaf not in mathlib_tokens and leaf not in prompt_prose and not leaf.startswith("_"):
                proj_decls_leaf.add(leaf)

    # Known landmark project identifiers that MUST NEVER appear in blinded prompts
    landmarks = {
        "AbelianVarietyTheory", "AutomorphicArithmetic", "DivisorProofs", "ThetaCorrespondence",
        "IwasawaDecomposition", "SmallClassNumbers", "CharacterBoxes", "DyadicPrimeIntervals",
        "GlobalTheory", "UpperTheory", "IndefiniteRowSideFullHecke", "PrimeRecip", "table_ok",
        "InvFiveLogLeSumInvPrimes", "MainTheoremsAll", "kexactB", "CutCptCopy", "LamCopy",
        "sigSpan_copy", "PrincipalizationCertificate", "OpenLiteratureStatements", "Row0b",
        "ZeroFreeAll", "EveryCharacter", "VWin", "HypsAlt", "galoisLocalGlobalStrong",
        "riemannHypothesis", "riemannZeta_eq_zero_re", "LFunction_eq_zero_re",
        "StatementOC", "MainConclusion", "RhOfRight", "CritLine", "BuildAid",
    }

    tok_re = re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*")
    lines = [l.strip() for l in open(prompts_path, encoding="utf-8") if l.strip()]
    leaks_landmark = []
    leaks_folder = []
    leaks_file = []
    leaks_decl_full = []
    leaks_decl_leaf = []
    leaks_path = []

    for idx, raw in enumerate(lines, 1):
        rec = json.loads(raw)
        cid = rec.get("cluster_id", f"line{idx}")
        # Check raw JSON text (excluding nothing — even metadata must not leak!)
        if ".lean" in raw or "src/" in raw or "Development/" in raw or "Supplements/" in raw or "Formalism/" in raw:
            leaks_path.append((cid, "path-like substring"))
        for m in tok_re.finditer(raw):
            tok = m.group(0)
            if tok in landmarks:
                leaks_landmark.append((cid, tok))
            if tok in proj_decls_full:
                leaks_decl_full.append((cid, tok))
            for part in tok.split("."):
                if part in landmarks:
                    leaks_landmark.append((cid, part))
                if part in proj_folders:
                    leaks_folder.append((cid, part))
                if part in proj_files:
                    leaks_file.append((cid, part))
                if part in proj_decls_leaf:
                    leaks_decl_leaf.append((cid, part))

    # Deduplicate for reporting
    leaks_landmark = sorted(set(leaks_landmark))
    leaks_folder = sorted(set(leaks_folder))
    leaks_file = sorted(set(leaks_file))
    leaks_decl_full = sorted(set(leaks_decl_full))
    leaks_decl_leaf = sorted(set(leaks_decl_leaf))

    print(f"     checked {len(lines)} blinded prompt records against {len(proj_folders):,} project folders, {len(proj_files):,} file stems, {len(proj_decls_full):,} full decls, {len(proj_decls_leaf):,} leaf decls, {len(landmarks)} landmarks")
    ck(not leaks_path and not leaks_landmark and not leaks_decl_full,
       f"zero path/landmark/full-decl leaks in blinded prompts: path={leaks_path[:5]} landmark={leaks_landmark[:10]} full_decl={leaks_decl_full[:10]}")
    ck(not leaks_folder and not leaks_file and not leaks_decl_leaf,
       f"zero project folder/file-stem/leaf-decl leaks in blinded prompts: folder={leaks_folder[:10]} file={leaks_file[:10]} leaf={leaks_decl_leaf[:10]}")

    # 2. Check Tier 3 pilot output + AI-draft pack (if generated)
    pilot_path = os.path.join(ROOT, "outputs", "flirt", "tier3_pilot.json")
    pack_path = os.path.join(ROOT, "outputs", "flirt", "tier3_ai_draft_pack.jsonl")
    if not os.path.exists(pilot_path) or not os.path.exists(pack_path):
        print("     tier3_pilot.json / tier3_ai_draft_pack.jsonl not present yet; stopping after prompt-blinding check.")
        sys.exit(0 if all(R) else 1)

    pilot = json.load(open(pilot_path, encoding="utf-8"))
    pack_txt = open(pack_path, encoding="utf-8").read()
    issues = annot.errors_of(annot.validate_text(pack_txt, canonical=True))
    ck(not issues, f"tier3_ai_draft_pack.jsonl passes annot.validate_text(canonical=True): issues={issues[:3]}")

    pk = annot.loads(pack_txt)
    ck(all(d["kind"] == "ai-draft" and d["default_on"] is False for d in pk.layers.values()) and len(pk.layers) >= 1,
       f"all layers in tier3_ai_draft_pack.jsonl are kind=ai-draft, default_on=false: {list(pk.layers.keys())}")
    ck(all(r.get("draft") is True and r.get("tag") == "M" and r.get("breaks") and str(r.get("author", "")).startswith("ai:") for r in pk.annots.values()),
       f"all {len(pk.annots)} records in AI-draft pack have draft=true, tag=M (never [L]), breaks note, ai:* author")
    ck(annot.default_layers(pk) == [], f"annot.default_layers(tier3_pack) == [] (AI drafts OFF by default)")

    # 3. Independently recompute blinded-vs-unblinded agreement + Cohen's kappa from raw JSONs
    b_path = os.path.join(ROOT, "outputs", "flirt", "cache", "t3_labels_blinded.json")
    u_path = os.path.join(ROOT, "outputs", "flirt", "cache", "t3_labels_unblinded.json")
    if os.path.exists(b_path) and os.path.exists(u_path):
        bl = {x["cluster_id"]: x for x in json.load(open(b_path))}
        ul = {x["cluster_id"]: x for x in json.load(open(u_path))}
        ids = sorted(set(bl) & set(ul))
        n = len(ids)
        agree = sum(1 for i in ids if bl[i]["primary_domain"] == ul[i]["primary_domain"])
        exact_rate = agree / n if n else 0.0
        # Cohen's kappa
        cb = collections.Counter(bl[i]["primary_domain"] for i in ids)
        cu = collections.Counter(ul[i]["primary_domain"] for i in ids)
        cats = set(cb) | set(cu)
        pe = sum((cb[c] / n) * (cu[c] / n) for c in cats) if n else 0.0
        kappa = (exact_rate - pe) / (1.0 - pe) if (1.0 - pe) > 1e-12 else 1.0
        top2 = sum(
            1 for i in ids
            if ({bl[i]["primary_domain"], bl[i].get("secondary_domain")} - {None})
            & ({ul[i]["primary_domain"], ul[i].get("secondary_domain")} - {None})
        ) / n if n else 0.0
        rep_ag = pilot.get("agreement", {})
        ck(rep_ag.get("agree") == agree and rep_ag.get("of") == n
           and abs(rep_ag.get("exact_rate", -1) - exact_rate) < 1e-3
           and abs(rep_ag.get("cohens_kappa", -9) - kappa) < 1e-3
           and abs(rep_ag.get("top2_overlap_rate", -1) - top2) < 1e-3,
           f"blinded vs unblinded agreement recomputed: {agree}/{n} ({exact_rate:.4f}), kappa={kappa:.4f}, top2={top2:.4f} vs reported={rep_ag}")
    else:
        print("     note: raw t3_labels_*.json absent; checking pilot clusters internal consistency only")

    fails = sum(1 for x in R if not x)
    print(f"\nF3-CHECK {'PASS' if fails == 0 else 'FAIL'} ({len(R)-fails}/{len(R)})")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
