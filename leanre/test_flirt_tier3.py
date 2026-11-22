#!/usr/bin/env python3
"""Unit tests for FLIRT Tier 3 (leanre/flirt/tier3.py, Gate F3).

Tests name-blinding airtightness (fail-closed allowlist + adversarial leak injection),
AI-draft-only ingestion via leanre/annot.py (tag M, draft=true, default_on=false),
and blinded-vs-unblinded agreement metrics (exact, Cohen's kappa, top-2, Jaccard).
All fixtures are synthetic.
"""
from __future__ import annotations

import json
import os
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
FLIRT_DIR = os.path.join(HERE, "flirt")
for _p in (HERE, FLIRT_DIR):
    if _p not in sys.path:
        sys.path.insert(0, _p)

import annot  # noqa: E402
import sighash  # noqa: E402
import tier3  # noqa: E402


def _write(root: str, rel: str, content: str) -> None:
    p = os.path.join(root, rel)
    os.makedirs(os.path.dirname(p), exist_ok=True)
    with open(p, "w", encoding="utf-8") as f:
        f.write(content)


class Tier3BlindingAndIngestTests(unittest.TestCase):
    def setUp(self):
        self.td = tempfile.TemporaryDirectory()
        self.src = os.path.join(self.td.name, "src")
        _write(
            self.src,
            "Development/AbelianVarietyTheory/Proofs/DivisorProofs/SecretPrimeHelper.lean",
            """import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OtherSecretMod
open Classical
open GlobalTheory.SecretInternalNs
namespace GlobalTheory.PrimeRecipSecret
def hiddenChecker (p : ℕ) : Bool := true
theorem secret_table_ok (n : ℕ) (h : Nat.Prime n) :
    hiddenChecker n = true ∧ Nat.primeCounting n ≤ n := by
  decide +kernel
end GlobalTheory.PrimeRecipSecret
""",
        )
        self.lex = sighash.Lexicon([
            "GlobalTheory.PrimeRecipSecret.hiddenChecker",
            "GlobalTheory.PrimeRecipSecret.secret_table_ok",
        ])
        self.std_al = tier3.StdAllowlist((), ())

    def tearDown(self):
        self.td.cleanup()

    def test_blinding_removes_all_project_names_and_keeps_mathlib(self):
        b, u, meta = tier3.blind_cluster(
            cluster_id="C01",
            cohort="misfile",
            target_kind="module",
            target_name="Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecretPrimeHelper",
            boundary_modules=["Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecretPrimeHelper"],
            total_cluster_modules=1,
            src_dir=self.src,
            project_lexicon=self.lex,
            std_allowlist=self.std_al,
        )
        # Leak test MUST pass on the generated blinded prompt
        rep = tier3.verify_no_leaks(b, self.std_al, extra_forbidden=meta["all_forbidden_tokens"])
        self.assertTrue(rep["passed"], rep)
        self.assertEqual(rep["leaks"], [])
        self.assertGreater(rep["checked_tokens"], 10)

        blob = json.dumps(b, sort_keys=True)
        # No project folder/file/namespace/declaration names survive!
        for secret in (
            "Development", "AbelianVarietyTheory", "DivisorProofs",
            "SecretPrimeHelper", "OtherSecretMod", "GlobalTheory",
            "SecretInternalNs", "PrimeRecipSecret", "hiddenChecker",
            "secret_table_ok", "decide_kernel",
        ):
            self.assertNotIn(secret, blob)
        # Mathlib/Lean core identifiers & generic flag ARE preserved!
        self.assertIn("Nat.Prime", blob)
        self.assertIn("Nat.primeCounting", blob)
        self.assertIn("Bool", blob)
        self.assertIn("Classical", blob)
        self.assertIn("kernel_decide", blob)
        self.assertIn("D001", blob)
        # Zero proof-body words
        self.assertNotIn("decide +kernel", blob)
        # Unblinded companion DOES carry the real names (still zero proof bodies)
        self.assertEqual(u["target_name"], "Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecretPrimeHelper")
        self.assertFalse(u["blinded"])

    def test_leak_detector_catches_planted_leaks(self):
        b, _, meta = tier3.blind_cluster(
            cluster_id="C01",
            cohort="misfile",
            target_kind="module",
            target_name="Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecretPrimeHelper",
            boundary_modules=["Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecretPrimeHelper"],
            total_cluster_modules=1,
            src_dir=self.src,
            project_lexicon=self.lex,
            std_allowlist=self.std_al,
        )
        # Plant a project-local identifier into a blinded signature -> MUST fail!
        b_bad = json.loads(json.dumps(b))
        b_bad["declarations"][0]["signature_blinded"] += " SecretPrimeHelper"
        rep = tier3.verify_no_leaks(b_bad, self.std_al, extra_forbidden=meta["all_forbidden_tokens"])
        self.assertFalse(rep["passed"])
        self.assertGreaterEqual(len(rep["leaks"]), 1)

        # Plant an unrecognized unknown token -> fail-closed allowlist MUST catch it!
        b_unk = json.loads(json.dumps(b))
        b_unk["declarations"][0]["signature_blinded"] += " sneakyLocalHelper99"
        rep2 = tier3.verify_no_leaks(b_unk, self.std_al)
        self.assertFalse(rep2["passed"])
        self.assertTrue(any(lk["token"] == "sneakyLocalHelper99" for lk in rep2["leaks"]))

    def test_ingest_ai_draft_layer_only_and_agreement_metrics(self):
        manifest = {
            "allowlist_id": "abc123",
            "lexicon_id": "def456",
            "leak_test": {"all_passed": True, "clusters_checked": 2, "total_leaks": 0},
            "clusters": [
                {
                    "cluster_id": "C01",
                    "cohort": "misfile",
                    "target_kind": "module",
                    "target_name": "Dev.AV.Div.ModA",
                    "module_count": 1,
                    "boundary_modules": ["Dev.AV.Div.ModA"],
                    "prompt_sha256": "a" * 64,
                },
                {
                    "cluster_id": "C02",
                    "cohort": "dominator_boundary",
                    "target_kind": "folder",
                    "target_name": "Form.PerInt",
                    "module_count": 120,
                    "boundary_modules": ["Form.PerInt.Root"],
                    "prompt_sha256": "b" * 64,
                },
            ],
        }
        b_labels = [
            {
                "cluster_id": "C01",
                "primary_domain": "prime_elem_arith",
                "secondary_domain": "computational_kernel_check",
                "short_label": "Elementary prime counting kernel check",
                "confidence": 0.92,
                "evidence_tokens": ["Nat.Prime", "Nat.primeCounting"],
                "uncertainty_note": "Headers only; project helper definitions abstracted.",
            },
            {
                "cluster_id": "C02",
                "primary_domain": "measure_integration",
                "secondary_domain": "linear_matrix_rep",
                "short_label": "Haar measure and period integral bounds",
                "confidence": 0.85,
                "evidence_tokens": ["MeasureTheory", "Integrable"],
                "uncertainty_note": "Headers only.",
            },
        ]
        u_labels = [
            {
                "cluster_id": "C01",
                "primary_domain": "algebraic_geometry",
                "secondary_domain": "prime_elem_arith",
                "short_label": "Abelian variety divisor prime lemma",
                "confidence": 0.70,
                "evidence_tokens": ["DivisorProofs"],
                "uncertainty_note": "Folder name suggests algebraic geometry.",
            },
            {
                "cluster_id": "C02",
                "primary_domain": "measure_integration",
                "secondary_domain": None,
                "short_label": "Period integrals and Haar volume estimates",
                "confidence": 0.88,
                "evidence_tokens": ["MeasureTheory"],
                "uncertainty_note": "Headers only.",
            },
        ]

        pack_path = os.path.join(self.td.name, "ai_draft.jsonl")
        pilot_path = os.path.join(self.td.name, "pilot.json")
        pack, pilot = tier3.ingest_labels(
            manifest=manifest,
            blinded_labels=b_labels,
            unblinded_labels=u_labels,
            model_name="test-model-v1",
            out_pack_path=pack_path,
            out_pilot_json=pilot_path,
            now="2026-11-22T03:00:00Z",
        )

        # Pack validates canonically via leanre/annot.py with ZERO issues!
        self.assertEqual(annot.validate_file(pack_path, canonical=True), [])
        # Layer is strictly ai-draft and default_on=False!
        self.assertEqual(list(pack.layers.keys()), [tier3.AI_LAYER_ID])
        layer = pack.layers[tier3.AI_LAYER_ID]
        self.assertEqual(layer["kind"], "ai-draft")
        self.assertFalse(layer["default_on"])
        # Every record is draft=True, tag=M, author=ai:*, has breaks, never tag=L!
        self.assertEqual(len(pack.annots), 2)
        for rec in pack.annots.values():
            self.assertEqual(rec["tag"], "M")
            self.assertTrue(rec["draft"])
            self.assertTrue(rec["author"].startswith("ai:"))
            self.assertTrue(rec["breaks"])

        # Round-trip import into a fresh annot.PackStore works cleanly and keeps layer off by default
        store = annot.PackStore(os.path.join(self.td.name, "annotations"))
        with open(pack_path, encoding="utf-8") as f:
            imp_res = store.import_text(f.read())
        self.assertTrue(imp_res["ok"])
        self.assertEqual(len(imp_res["added"]), 2)
        loaded_pack, issues = store.load()
        self.assertEqual(issues, [])
        self.assertEqual(annot.default_layers(loaded_pack), [])  # ai-draft OFF by default!

        # Agreement metrics check: 1/2 exact (C02 agrees, C01 disagrees due to misfile folder name!)
        ag = pilot["agreement"]
        self.assertEqual(ag["agree"], 1)
        self.assertEqual(ag["of"], 2)
        self.assertAlmostEqual(ag["exact_rate"], 0.5)
        self.assertAlmostEqual(ag["top2_overlap_rate"], 1.0)
        self.assertEqual(ag["by_cohort"]["misfile"]["agree"], 0)
        self.assertEqual(ag["by_cohort"]["dominator_boundary"]["agree"], 1)

    def test_kernel_two_hop_type_unfolding_is_leak_free_and_skips_thm_bodies(self):
        import sqlite3
        kdb = os.path.join(self.td.name, "k.db")
        ck = sqlite3.connect(kdb)
        ck.executescript("""
            CREATE TABLE decls(id INT PRIMARY KEY, name TEXT, kind TEXT);
            CREATE TABLE edges(src INT, dst INT, kind INT);
        """)
        # Boundary thm `GlobalTheory.PrimeRecipSecret.secret_table_ok` (id=1):
        #   - type edge -> project def `GlobalTheory.PrimeRecipSecret.hiddenChecker` (id=2)
        #   - value edge -> proof lemma `SecretProofOnly.shouldNotAppear` (id=5) and Mathlib `Scheme` (id=6)
        # Project def `hiddenChecker` (id=2):
        #   - value edge -> inner project def `GlobalTheory.InnerWrap` (id=3)
        # Inner project def `GlobalTheory.InnerWrap` (id=3):
        #   - value edge -> Mathlib `MeasureTheory.Measure` (id=4) and `DirichletCharacter.LFunction` (id=7)
        ck.executemany("INSERT INTO decls VALUES (?,?,?)", [
            (1, "GlobalTheory.PrimeRecipSecret.secret_table_ok", "thm"),
            (2, "GlobalTheory.PrimeRecipSecret.hiddenChecker", "def"),
            (3, "GlobalTheory.InnerWrap", "def"),
            (4, "MeasureTheory.Measure", "def"),
            (5, "SecretProofOnly.shouldNotAppear", "thm"),
            (6, "AlgebraicGeometry.Scheme", "def"),
            (7, "DirichletCharacter.LFunction", "def"),
        ])
        ck.executemany("INSERT INTO edges VALUES (?,?,?)", [
            (1, 2, 1),  # type edge to def
            (1, 5, 2),  # value edge to proof lemma (MUST NOT unfold!)
            (1, 6, 2),  # value edge to Mathlib Scheme in proof body (MUST NOT unfold!)
            (2, 3, 2),  # def value edge to inner def
            (3, 4, 2),  # hop-2 def value edge to MeasureTheory.Measure
            (3, 7, 1),  # hop-2 def type edge to DirichletCharacter.LFunction
        ])
        ck.commit()
        ck.close()

        lex2 = sighash.Lexicon([
            "GlobalTheory.PrimeRecipSecret.hiddenChecker",
            "GlobalTheory.PrimeRecipSecret.secret_table_ok",
            "GlobalTheory.InnerWrap",
            "SecretProofOnly.shouldNotAppear",
        ])
        unf = tier3.KernelTypeUnfolder(kdb, lex2, self.std_al)
        try:
            b, _, meta = tier3.blind_cluster(
                cluster_id="C01",
                cohort="pillar_dominator",
                target_kind="decl",
                target_name="GlobalTheory.PrimeRecipSecret.secret_table_ok",
                boundary_modules=["Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecretPrimeHelper"],
                total_cluster_modules=1,
                src_dir=self.src,
                project_lexicon=lex2,
                std_allowlist=self.std_al,
                unfolder=unf,
                unfold_hops=2,
            )
        finally:
            unf.close()

        rep = tier3.verify_no_leaks(b, self.std_al, extra_forbidden=meta["all_forbidden_tokens"])
        self.assertTrue(rep["passed"], rep)
        uctx = b["unfolded_type_context"]
        self.assertEqual(uctx["unfold_hops"], 2)
        # Hop-2 Mathlib contract primitives MUST appear!
        self.assertIn("MeasureTheory.Measure", uctx["top_unfolded_mathlib"])
        self.assertIn("DirichletCharacter.LFunction", uctx["top_unfolded_mathlib"])
        # Proof-body-only dependency (`AlgebraicGeometry.Scheme` via value edge of `thm`) MUST NOT appear!
        self.assertNotIn("AlgebraicGeometry.Scheme", uctx["top_unfolded_mathlib"])
        # Zero project names anywhere in unfolded context!
        blob = json.dumps(uctx)
        for bad in ("InnerWrap", "hiddenChecker", "SecretProofOnly", "shouldNotAppear"):
            self.assertNotIn(bad, blob)


if __name__ == "__main__":
    unittest.main(verbosity=2)
