"""Curated, human-read annotations for spine_map.json (gate D1).

Every entry was written after reading the exact header / contract with `leanre decompile contract|unfold|horn`
at rh_mirror@40e56bab.  Tags: [L] = read from pinned Lean/kernel; [S] = standard published math (the
*shape* comparison only); [M] = analogy.  `status`: READ = every project contract in the statement was
unfolded to Mathlib; PARTIAL = statement shape read, some project predicates not unfolded (listed in
`opaque`); OPAQUE = not unfolded.  No proof text is reproduced.
"""
from __future__ import annotations

# id -> (role, status, verdict, tag, summary, opaque_inner)
SPINE: dict[str, tuple[str, str, str, str, str, list[str]]] = {
    # ---------------- 5 headline theorems (Main.lean) ----------------
    "riemannHypothesis": ("theorem", "READ", "real", "L",
        "Main.lean:4. Statement = Mathlib `RiemannHypothesis`; proof term is `rhOfAll`.", []),
    "riemannZeta_eq_zero_re": ("theorem", "READ", "real", "L",
        "Main.lean:6. Statement `RiemannZetaZerosOnLine` (Statements.lean:3: every zero of ζ that is not a trivial "
        "zero −2(n+1) and is ≠1 has Re = 1/2). Proved by the *same* term `rhOfAll : RiemannHypothesis`, so the kernel "
        "accepted the two Props as definitionally equal.", []),
    "LFunction_ne_zero_of_half_lt_re": ("theorem", "READ", "real", "L",
        "Main.lean:8. Statement `DirichletLNonvanishingRightOfHalf` (Statements.lean:6) := `allChi`. Its body is "
        "word-for-word the body of `UpperTheory.EveryCharacter` (EveryCharacter.lean:13): L(χ,s) ≠ 0 for Re s > 1/2 "
        "unless (χ = 1 ∧ s = 1).", []),
    "LFunction_eq_zero_re": ("theorem", "READ", "real", "L",
        "Main.lean:10. Statement `DirichletLZerosOnLine` (all χ mod N, zeros with 0<Re s<1 lie on Re=1/2) := "
        "`claimAll.2.1` (= `Claim.strip allChi`).", []),
    "LFunction_eq_zero_re_of_isPrimitive": ("theorem", "READ", "real", "L",
        "Main.lean:12. Statement `PrimitiveDirichletLZerosOnLine` := `critAll` (= `Formalism.VW.critLine allChi`).", []),
    # ---------------- Statement-level bridge (outside allChi) ----------------
    "rhOfAll": ("bridge", "READ", "real", "L",
        "MainTheorems.lean:9. `Formalism.VW.rh_of_every allChi`.", []),
    "critAll": ("bridge", "READ", "real", "L",
        "MainTheorems.lean:11. `Formalism.VW.critLine allChi …` for primitive χ.", []),
    "claimAll": ("bridge", "READ", "real", "L",
        "MainTheorems.lean:15. ⟨allChi, Claim.strip allChi, Claim.zeta allChi⟩ : HalfPlane ∧ Strip ∧ Zeta; the three "
        "Claim.* Props (HalfPlane.lean:3/6/9) restate the Statements.lean Props verbatim.", []),
    "Formalism.VW.rh_of_every": ("bridge", "READ", "real", "L",
        "CritLine.lean:29. EveryCharacter → RiemannHypothesis: specialise to the trivial character mod 1 "
        "(direct lemma `DirichletCharacter.LFunction_modOne_eq`, i.e. L(1 mod 1,s)=ζ(s)) and call `rh_of_right`. "
        "[S] standard.", []),
    "Formalism.VW.rh_of_right": ("bridge", "READ", "real", "L",
        "RhOfRight.lean:5. (∀ s, 1/2<Re s → s≠1 → ζ(s)≠0) → RH, using only Mathlib (136 direct lemma uses incl. "
        "`riemannZeta_one_sub`, `Complex.Gamma_ne_zero_of_re_pos`, `Complex.cos_eq_zero_iff`): reflect a zero with "
        "Re<1/2 through the functional equation. [S] standard.", []),
    "Formalism.VW.critLine": ("bridge", "READ", "real", "L",
        "CritLine.lean:11. EveryCharacter + χ primitive + 0<Re s<1 + L(χ,s)=0 → Re s = 1/2, via Mathlib's completed "
        "L-function functional equation (`IsPrimitive.completedLFunction_one_sub`, `LFunction_eq_completed_div_gammaFactor`) "
        "and `gammaFactor_ne_zero`. [S] standard.", []),
    "Claim.strip": ("bridge", "READ", "real", "L",
        "ClaimStrip.lean:59. HalfPlane → Strip for all (incl. imprimitive) χ: `prim_zero` (a strip zero of L(χ) is a zero "
        "of L(χ_prim) since every Euler factor 1−ψ(p)p^{−s} ≠ 0 for Re s>0, `factor_ne_zero`) + `prim_reflect` "
        "(functional equation). [S] standard.", []),
    "Claim.zeta": ("bridge", "READ", "real", "L",
        "ClaimStrip.lean:75. HalfPlane → Zeta (via `Claim.strip` at N=1 and `Complex.Gammaℝ_eq_zero_iff` for trivial zeros).", []),
    # ---------------- allChi and the split ----------------
    "allChi": ("theorem", "READ", "real", "L",
        "MainTheorems.lean:7. `allChi : UpperTheory.EveryCharacter := everyCharacter`. Dominates 1,409,557 of the "
        "1,468,414 live decls (96.0%).", []),
    "UpperTheory.EveryCharacter": ("contract", "READ", "real", "L",
        "EveryCharacter.lean:13. ∀ N≠0, χ : DirichletCharacter ℂ N, s : ℂ, 1/2 < Re s → (χ ≠ 1 ∨ s ≠ 1) → "
        "LFunction χ s ≠ 0. All dependencies are Mathlib (DirichletCharacter.LFunction, Complex.re, ZMod…). This is "
        "GRH-to-the-right-of-1/2 for Dirichlet L-functions [S], stated with Mathlib objects only.", []),
    "UpperTheory.FinalTheorems.everyCharacter": ("theorem", "READ", "real", "L",
        "MainConclusion.lean:10. `everyCharacter_of_row galoisLocalGlobalStrong_recParameter`: modus ponens "
        "Row0b(recT) ∧ (Row0b(IsRecT) → EveryCharacter) ⊢ EveryCharacter. 110,900 direct dominator children.", []),
    "UpperTheory.FinalTheorems.everyCharacter_of_row": ("theorem", "READ", "real", "L",
        "MainConclusion.lean:7. (h : Row0b (fun h rc ↦ IsRecT h rc)) → EveryCharacter := "
        "every_character_of_literature_of_vWin ⟨h, recTExists, h⟩ (vwin_of_row h). The `OpenLiteratureStatements` "
        "record is *constructed here* from h and the proved `recTExists` — it is not an assumption [L].", []),
    "UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter": ("theorem", "PARTIAL", "unknown", "L",
        "RowSrc.lean:6. `: Row0b recT` where `recT := fun h rc ↦ IsRecT h rc` (Development.lean:18), hence "
        "definitionally the hypothesis of everyCharacter_of_row. Direct lemmas: galoisRepresentations_of_thetaLift, "
        "tLiftK. Pillar B — owned by `galois` (pillar_galois.json).", []),
    "UpperTheory.GalStar.Row0b": ("contract", "PARTIAL", "unknown", "L",
        "WeightsConjBis.lean:69, with section variable (Rc : RecNotion). Body: ∀ CM number field E, Ω=alg. closure, "
        "prime l, ι : Q̄_l ≃+* ℂ, a ≥ 1, π : CuspSub E a, χ : HChar(E⁺), (CG.mk π).IsRegAlg → PolarizedPair π χ → "
        "∃ r : Gal(Ω/E) →* GL_a(Q̄_l), wt : ℤ, HT, PropsB Rc π ι r wt HT. PropsB fields (WeightsConjBis.lean:54): "
        "cont, ss (IsSSRep), away (local–global compatibility at w∤l against any Rc-local-Langlands map, via AwayB: "
        "same dim / Frobenius-semisimple char-poly agreement under conditions), weights (HT = infinitesimal character "
        "shifted by (a−1)/2), weights_conj, above (crystalline/…-at-l), …. [S] shape = the theorem attaching Galois "
        "representations to regular algebraic polarized cuspidal π of GL_a over CM fields (Harris–Taylor, Shin, "
        "Chenevier–Harris, Caraiani). Inner predicates owned by `galois`.",
        ["UpperTheory.GalStar.CuspSub", "CG.IsRegAlg", "GlobalTheory.ContraPair.PolarizedPair", "IsSSRep",
         "UpperTheory.GalStar.AwayB", "UpperTheory.GalStar.AboveB"]),
    "UpperTheory.Gal.Int.recT": ("contract", "READ", "real", "L",
        "Development.lean:18. `def recT : RecNotion := fun h rc ↦ IsRecT h rc` — a pure alias (eta-expanded IsRecT).", []),
    "UpperTheory.GalStar.RecNotion": ("contract", "READ", "real", "L",
        "WeightsConjAlt.lean:16. abbrev RecNotion : Type 1 := ∀ {E Ω …} {A : ValuationSubring Ω} {w} (h : IsPlaceOver A w), "
        "(IrrGL (E_w) → WD h) → Prop — a predicate on candidate local-Langlands maps.", []),
    "UpperTheory.Zero.LLC.IsRecT": ("contract", "PARTIAL", "unknown", "L",
        "IsRecTOfIsRec.lean:76. IsRecT rc := ∃ a ha, LawsT a ha rc, where a : Weil h →* (E_w)ˣ is a local Artin map. "
        "LawsT (IsRecTOfIsRec.lean:55) has 12 fields: dim, one (characters ↦ Artin-composed characters), langlands "
        "(Zelevinsky segment sums), cusp (cuspidal ↦ irreducible WD), nu (|det|^s twist), absCentral, twist, central, "
        "dual (contragredient), inj, depth (depth-0 ↦ tame), type (TypeLaw). [S] shape = the characterising properties "
        "of the local Langlands correspondence for GL_n (Harris–Taylor, Henniart); note: no surjectivity field [L].",
        ["UpperTheory.Zero.LLC.TypeLaw", "GlobalTheory.LocGL.IrrGL", "GlobalTheory.WeilDeligne.WD"]),
    "UpperTheory.Zero.LLC.RecTExists": ("contract", "READ", "real", "L",
        "IsRecTOfIsRec.lean:78. ∀ number field E, Ω, A, w, h : IsPlaceOver A w, ∃ rc, IsRecT h rc — existence of a "
        "local Langlands map at every finite place.", []),
    "UpperTheory.Zero.LLC.recTExists": ("theorem", "PARTIAL", "unknown", "L",
        "RecTExists.lean:20. Proves RecTExists; only 595 decls dominated (diamond root #35) and 25 direct users. "
        "Size alone is no verdict: whether IsRecT is satisfiable *non-trivially* depends on WD/IrrGL/TypeLaw "
        "(owned by `galois` / `tcb`).", ["UpperTheory.Zero.LLC.TypeLaw"]),
    "UpperTheory.LiteratureTheorems.OpenLiteratureStatements": ("structure", "READ", "real", "L",
        "EveryCharacterOfLiteratureOfVWin.lean:215. structure … : Prop with 3 fields: caraianiLocalGlobalDual : "
        "One.M.Row, localLanglandsExists : Zero.LLC.RecTExists, galoisRepOfPolarizedPairLit : One.M.Row, where "
        "One.M.Row := Row0b (fun h rc ↦ IsRecT h rc) (RecT.lean:6). Built in everyCharacter_of_row, so the 'open "
        "literature' is discharged inside the kernel [L]. Many `*_of_literature (O)` lemmas ignore O and return a "
        "proved project theorem (see stats.literature_O_usage).", []),
    "UpperTheory.One.M.Row": ("contract", "READ", "real", "L",
        "RecT.lean:6. Row := Row0b (fun h rc ↦ IsRecT h rc).", []),
    "UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin": ("theorem", "PARTIAL", "unknown", "L",
        "EveryCharacterOfLiteratureOfVWin.lean:810. (O : OpenLiteratureStatements) (hV : Top.VWin) → EveryCharacter: "
        "feeds every_character_of_theta_integrals_local_matching with published_results_eigen O, published_results_first O, "
        "theta_integrals_agree_and_local_matching_of_literature O (.1,.2), topCovolSlim2_use_alt_alt(…), "
        "local_langlands_gl_recT_exists_of_literature O and hV. Dominates 849,323 decls.", []),
    "UpperTheory.Lit.every_character_of_theta_integrals_local_matching": ("theorem", "OPAQUE", "unknown", "L",
        "SiegelEisensteinSecondTermHypotheses (module). Horn: UnitaryGroupThirdPlaceHypotheses ∧ ThetaLocalInputs ∧ "
        "ThetaIntegralsAgree ∧ LocalMatching ∧ CovolumeBoundOfX ∧ RecTExists ∧ VWin → EveryCharacter. 543,325 decls "
        "(38.5% of allChi). Pillar A — owned by `theta` (pillar_theta.json).",
        ["GlobalTheory.Fc.S0.UnitaryGroupThirdPlaceHypotheses", "GlobalTheory.FunPr.ThetaLocalInputs",
         "GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree",
         "GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching"]),
    "SelfIntersectionVolumeEstimates.topCovolSlim2_use_alt_alt": ("theorem", "OPAQUE", "unknown", "L",
        "TopCovolSlim2Use (module). Curried 15-premise implication (ResolutionCharZero, PrincipalisationCharZero, "
        "PoincareLelongInv, HSUse, MoriwakiBigStatement, FarguesExact, ZarhinStatement, NefRR, …) → CovolumeBoundOfX. "
        "80,720 decls. Pillar C (volume / literature) — owned by `volume`.",
        ["GlobalTheory.CovTop.CovolumeBoundOfX"]),
    "UpperTheory.LiteratureTheorems.theta_integrals_agree_and_local_matching_of_literature": ("lit_wrapper", "OPAQUE",
        "unknown", "L", "OpenLiteratureStatements → ThetaIntegralsAgree ∧ LocalMatching (direct lemmas theoremK_head2, "
        "eis_bl_of_literature, siegel_weil_std_of_literature). 14,173 decls. Owned by `theta`/`volume`.", []),
    "UpperTheory.One.vwin_of_row": ("theorem", "PARTIAL", "unknown", "L",
        "VwinOfRow.lean:4. Row0b(IsRecT) → Top.VWin via One.Join.automorphic_window_of_inputs (OpenImageCondition, "
        "BaseChangeIsobaricN, V.Z.Win.RowT). 92,705 decls. Pillar D — owned by `window`.", []),
    "UpperTheory.Top.VWin": ("contract", "PARTIAL", "unknown", "L",
        "ExistsPageN.lean:49. VWin := ∀ ψ : PChar, VWinAt ψ 401; VWinAt (ExistsPageN.lean:44) is a quantitative "
        "∀ε∈(0,1/52) ∀ page-function e … ∃ J ≥ 1, X0, ∀ X ≥ X0, ∀ WinPair q d, ∃ Y ∈ [X^{1/J}, √X] … VAt ψ ε 401 q d. "
        "PageN / WinPair / VAt not unfolded here (owned by `window`).", ["UpperTheory.Top.VAt", "UpperTheory.Top.PageN"]),
}

# Diamond roots (dominator children of everyCharacter other than the two branches), by subtree size.
DIAMOND: dict[str, tuple[str, str, str, str, str, list[str]]] = {
    "UpperTheory.V.Z.GSp4Splitting.coreG": ("theorem", "PARTIAL", "unknown", "L",
        "CoreG.lean:17 `: CoreG` (HighestVectorsRegularLine.lean:56): for antitone λ ∈ ℤ^n, K-module E, operator T with "
        "IsLefK, and a unitary-group module σ with IsCoreMod, the trace of flipA on the (finite-dim, nonzero) invariants "
        "equals ±2^n. Archimedean representation-theory lemma; inner predicates not unfolded.",
        ["PositivityTheory.RgBcC.RealD.IsCoreMod", "PositivityTheory.RgBcC.RealD.IsLefK"]),
    "GlobalTheory.T.zarhinGeometric_of_semistableReduction": ("theorem", "PARTIAL", "unknown", "L",
        "ZarhinGeometricOfSemistableReductionStatement.lean:14. Conditional: Published.SemistableReductionSt → ZH.ZHGeoSt. "
        "Hypothesis (SemistableReductionSt.lean:15) = for every polarized AV over a finite K/ℚ_p there is a finite K'/K "
        "and a semi-abelian group scheme over O_K' whose generic fibre is the pullback [S: Grothendieck's semistable "
        "reduction theorem]; it is discharged by the proved GlobalTheory.SS.semistableReductionSt [L]. Conclusion "
        "ZHGeoSt (ImmersedBy.lean:109) is a theta-system statement not unfolded.", ["GlobalTheory.ZH.ZHGeoSt"]),
    "GlobalTheory.RgGu.Leib.Hand.leibnizOrd": ("theorem", "PARTIAL", "real", "L",
        "HighestDerivProd.lean:23 `: LeibnizOrd k` (LeibnizOrd.lean:36): for a non-archimedean local field k and smooth "
        "π₁, π₂, the ℓ-th derivative of π₁×π₂ has a filtration whose graded pieces are (twisted) products of derivatives "
        "of π₁ and π₂. [S] = the Bernstein–Zelevinsky Leibniz rule for derivatives. derivB/GRep not unfolded.",
        ["GlobalTheory.RgGu.derivB"]),
    "UpperTheory.HeckeLevelFrameExistence.frameEx_of_fin": ("theorem", "OPAQUE", "unknown", "L",
        "FrameExOfFin.lean:43. USide → CandFin → FrameEx. USide (SimpleTwistedTraceFormulaStable.lean:239) is a "
        "finiteness/exhaustion statement for automorphic reps of unitary groups of given weight and level; FrameEx asks "
        "Nonempty (RunFrame F₀ T). Project-internal 'frame' machinery, not unfolded.", ["PositivityTheory.Rg.BcB.F.RunFrame"]),
    "GlobalTheory.deRham_potentiallySemistable": ("theorem", "PARTIAL", "real", "L",
        "DeRhamPotentiallySemistable.lean:11 `: Published.DeRhamPotSemistable` (DeRhamPotSemistable.lean:13): every "
        "continuous finite-dim ℚ_l-representation of G_K that IsDR is IsPst. [S] = Berger's p-adic monodromy theorem. "
        "5 users on both sides (Gal.Int.Inp.pst, Gal.TP.Sub.pstOfDR, de_rham_pot_semistable_of_literature) [L]. "
        "IsDR/IsPst not unfolded.", ["GlobalTheory.Pst.IsPst", "IsDR"]),
    "GlobalTheory.T.jacquetRallisUnitMatch_all_ranks": ("theorem", "PARTIAL", "unknown", "L",
        "JacquetRallisUnitMatchAllRanksStatement.lean:6 `: ∀ r, UnitMatch r` (FourierMatch.lean:158): for unramified "
        "E/F, Match M (unitG r F) (unitU r F E). [S] shape = Jacquet–Rallis fundamental lemma for the unit element "
        "(Yun; Beuzart-Plessis). Match/Meas not unfolded.", ["GlobalTheory.JR.Match"]),
    "UpperTheory.ConvolutionTheory.GM.gm_of_bcfl": ("theorem", "PARTIAL", "unknown", "L",
        "GmOfBcfl.lean:5. Conditional BCFLUnit → GM. BCFLUnit (InvTransposeGLInvTransposeGL.lean:263) = base-change "
        "fundamental lemma for the unit of the Hecke algebra in unramified cyclic E/k with normalised Haar measures [S: "
        "Kottwitz/Clozel–Labesse shape]; discharged by PositivityTheory.Rg.Tf.Loc.bcflUnit (another diamond root) [L]. "
        "GM (LocHeckeInert.lean:164) is a global side-matching statement, not unfolded.", ["UpperTheory.ConvolutionTheory.GM.GM"]),
    "UpperTheory.BaseChangeIdentities.FrameWordIdentity.frameBound": ("theorem", "OPAQUE", "unknown", "L",
        "FrameBound.lean:42 `: FrameBound` — ∀ ReadLimit, DiagAlg, CM E unramified, automorphic π, frames F₀/F: "
        "(F.toGenIn hD h).Bound. Project-internal, not unfolded.", ["PositivityTheory.Rg.BcB.F.FrameBound"]),
    "PositivityTheory.AdelicQuotientData.rsPole": ("theorem", "PARTIAL", "real", "L",
        "JacquetShalikaRigidity.lean:10 `: RSPole` (CauchyLoc.lean:46): for normalised cuspidal π (GL_m), π' (GL_k) over "
        "totally complex E, partial Rankin–Selberg L^S(s,π×π') has (s−1)·ZS·L^S holomorphic on Re s>0 with ZS non-vanishing "
        "on the line, and Z(1)=0 unless (m,π) = (k,π'). [S] = Jacquet–Shalika / Moeglin–Waldspurger pole criterion. "
        "SatOff/LS not unfolded.", ["PositivityTheory.RgJS.LS", "PositivityTheory.RgJS.SatOff"]),
    "PositivityTheory.RgBcC.wave_existence_speed_multiplicity": ("theorem", "PARTIAL", "unknown", "L",
        "WaveFinal.lean:15 `: WaveEx ∧ WaveSpeed ∧ KerEx ∧ MultAlg` (IsMultZero.lean:106–117): existence of solutions of "
        "a wave equation on GL_n(ℂ)-modules, finite propagation speed, existence of compactly supported multiplier "
        "kernels, and the multiplier algebra laws. 14 direct users. IsWave/IsMult not unfolded.",
        ["PositivityTheory.RgBcC.IsWave", "PositivityTheory.RgBcC.IsMult"]),
    "GroundTheory.Arith.SchemeCoh.finite_H_of_isProper": ("theorem", "PARTIAL", "real", "L",
        "ProperFiniteness.lean:23: X proper over Spec A (A Noetherian), F coherent (IsCoherent = quasi-coherent ∧ "
        "finite on affines, TwistingSheaf.lean:18) → H^p(X,F) is a finite A-module. [S] = EGA III 3.2.1. Sheaf.H is a "
        "project definition (not unfolded).", ["Sheaf.H"]),
    "GlobalTheory.SmoothLift.crystallineSmoothLift_of_relations": ("theorem", "PARTIAL", "unknown", "L",
        "CrystallineSmoothLiftOfRelations.lean:52 `: Published.CrystallineSmoothLift` (BijectiveCechDeRhamComparisonDegreeOne"
        ".lean:130): ∃ isomorphisms H¹,H² (crystalline-type cohomology of `Data`) ≅ de Rham HH¹,HH², cup-product and "
        "pull-back compatible. `Data` not unfolded, so which comparison theorem this is cannot be asserted.", ["GlobalTheory.SmoothLift.Data"]),
    "GlobalTheory.dualAbelianScheme": ("theorem", "PARTIAL", "unknown", "L",
        "DualAbelianSchemeExistsBiduality.lean:29 `: Published.DualAbelianScheme` (ExistsCrystalPairing.lean:25): every "
        "abelian scheme A/S (S : Scheme.{0} arbitrary; IsAbelianScheme = commutative, smooth, proper, geometrically "
        "connected group object) has B, P : LB(A×B) with B abelian, same relative dimension, IsDual A B P ∧ IsDual B A (swap P). "
        "FLAG for tcb/volume: over an arbitrary base the classical dual is in general constructed as an algebraic space "
        "[S, Faltings–Chai I.1]; a scheme-valued statement for every S deserves a check of how weak LB/IsDual are.",
        ["GlobalTheory.IsDual", "LB"]),
    "PositivityTheory.Rg.BcB.CV.ellFormula2J": ("theorem", "PARTIAL", "unknown", "L",
        "EllFormula2J.lean:12 `: EllFormula2J` (QuotIntegralZero.lean:46): ∃ C ≥ 0, for fundamental domains of GL_a(E), "
        "GL_b(E) and test functions of radius r with C(1+r) ≤ τ, the τ-cut trace cutTr2 equals the elliptic sum ellSum2 "
        "(a trace-formula truncation identity). cutTr2/ellSum2 not unfolded.", ["PositivityTheory.Rg.BcB.D4.cutTr2"]),
    "PositivityTheory.RgUd.All.bernsteinUnitaryProductIrreducible": ("theorem", "PARTIAL", "real", "L",
        "BernAll.lean:27 `: Published.BernsteinUnitaryProductIrreducible` (BernsteinUnitaryProductIrreducible.lean:10): "
        "smooth irreducible unitarisable π₁ of GL_r(k), π₂ of GL_t(k) ⇒ prod₂ π₁ π₂ irreducible. [S] = Bernstein (1984). "
        "prod₂/IsUnitarisable not unfolded.", ["prod₂", "IsUnitarisable"]),
    "CategoryTheory.IsGrothendieckAbelian.enoughInjectives": ("glue", "READ", "real", "L",
        "Mathlib: Grothendieck abelian categories have enough injectives. 50+ direct users (sheaf cohomology).", []),
    "GlobalTheory.T.exists_degenerationData_uniformisation_of_torsionCount": ("theorem", "PARTIAL", "unknown", "L",
        "ExistsDegenerationDataUniformisationOfTorsionCouStatement.lean:17. Conditional: (torsion count #A[n] = n^{2g} over "
        "alg. closed fields) → Laws → Laws2 → for every HidaSetting there are degeneration data D and a uniformisation U "
        "matching it. Laws / Laws2 (GlobalSectionsRankAlgClosed.lean:187, SecBaseChangeAnySt.lean:73) are Prop-structures "
        "BUNDLING 14 + 4 named statements (global sections rank, ample, cube, square, rigidity, Weil pairing…) — the "
        "hypothesis-bundling pattern; discharged in GlobalTheory.UU.exists_degData_unif_unconditional [L]. [S] shape = "
        "Mumford/Faltings–Chai degeneration.", ["GlobalTheory.UU.CP", "ReciprocityTheory.ChartRestriction.G.Out.UnifPre"]),
    "GlobalTheory.automorphicFormsFiniteGL": ("theorem", "PARTIAL", "real", "L",
        "AutomorphicFormsFiniteGL.lean:8 `: Published.AutomorphicFormsFiniteGL` (ExistsSpanFormsNeBot.lean:23): for totally "
        "complex E, open L ⊂ GL_a(A_f), continuous finite-dim K∞-type ρ and infinitesimal character c, span(forms L ρ c) "
        "is finite-dimensional. [S] = Harish-Chandra finiteness (restricted here to totally complex E). 39 users. "
        "AutFinGL.forms not unfolded.", ["AutFinGL.forms"]),
    "PositivityTheory.Rg.BcB.G8.global_character_holds": ("theorem", "OPAQUE", "unknown", "L",
        "GlobalCharacterHolds.lean:6 `: G4` (IsTransl.lean:82): ∃ c ≠ 0 relating ellS-type global character sums for "
        "GL_a×GL_b over unramified CM E. Not unfolded.", ["PositivityTheory.Rg.BcB.G8.G4"]),
    "HodgeLocalDeRhamField.HLdR.field_outright": ("theorem", "PARTIAL", "real", "L",
        "Outright.lean:7 `: Published.HeckeLAdicCharacterDeRham` (HeckeLAdicCharacterDeRham.lean:11): the l-adic character "
        "μ attached to an algebraic Hecke character χ of type n is de Rham at every place above l with HT jumps {−n∘ι∘τ}. "
        "[S] = Serre/Weil + Fontaine. IsdRAt/IsJumpsAt/LocBridge not unfolded.", ["IsdRAt", "IsJumpsAt", "LocBridge"]),
}


# Ranks 21–60: drafted by helper `diamond-reader` (board #69/#77) from `leanre decompile contract|unfold`,
# reviewed by spine: status downgraded READ→PARTIAL wherever project predicates were not unfolded to Mathlib
# (verdict `real` = statement *shape* matches the named classical result); #26/#27/#35 notes spot-checked.
DIAMOND.update({
    'PositivityTheory.Rg.Sw.HSt.holLeadB': ('theorem', 'PARTIAL', 'real', 'L',
        'Proves PositivityTheory.SiegelWeilFormula.HolLead: if the j-th derivative at s₀ of an analytic Eisenstein-style family Ê(s,g) vanishes against all singular Schwartz test functions ψ (IsSingTest), then y ↦ ∂_s^j Ê(s₀, g·ι(y)) satisfies the holomorphic weight/domain condition IsHolW p q e.',
        ['PositivityTheory.SiegelWeilFormula.HolLead', 'PositivityTheory.SiegelWeilFormula.IsHolW', 'PositivityTheory.Rg.Sw.IsSingTest']),
    'PositivityTheory.Rg.Cz.kType_holds': ('theorem', 'PARTIAL', 'real', 'L',
        'Proves PositivityTheory.Rg.Cz.KType: for a (𝔤,K)-module M with GL_n relations (IsGK, IsKD), integral quantum-determinant infinitesimal character l, and nonzero Whittaker functional ℓ (IsWh), there exists s : ℤ and a nonzero K-invariant alternating tensor η witnessing the minimal K-type tableau (KTypeData).',
        ['PositivityTheory.Rg.Cz.KType', 'PositivityTheory.Rg.Cz.KTypeData', 'PositivityTheory.Rg.Cz.IsGK']),
    'GlobalTheory.T.unitLemma_lieAlgebra_unitaryGroup_of_jacquetRallis': ('lit_wrapper', 'PARTIAL', 'wrapper', 'L',
        'Deduces both Jacquet-Rallis fundamental-lemma identities on lattices/orbital sums (UnitLemmaLie and UnitLemmaGroup) from the rank-general Fourier-matching statement ∀ r, UnitMatch r. NOTE: Pure *Statement.lean re-export (1 dom child) of GlobalTheory.UnitLemma.unitLemma_lie_and_group (UnitLemmaLieAlgebraUnitaryGroupOfJacquetRallisStatement.lean:8-9); wrapped statements are real (note UnitLemmaGroup requires K.Odd, IsUnit (2 : K.O)).',
        ['GlobalTheory.JR.UnitMatch', 'GlobalTheory.UnitLemma.UnitLemmaLie', 'GlobalTheory.UnitLemma.UnitLemmaGroup']),
    'GlobalTheory.CompanionTheory.SiegelRed.siegelCore': ('theorem', 'PARTIAL', 'real', 'L',
        'Proves PositivityTheory.ThKR.SiegelCore: constructs compact K, Ω ⊆ minParOne, and c > 0 for an adelic unitary group GAd σ J with Witt frame (X,Y), establishing Iwasawa decomposition, GoodPosition, Siegel-set fundamental domain coverage, height bounds, and rapid decay of cuspidal smooth moderate-growth forms.',
        ['PositivityTheory.ThKR.SiegelCore', 'GlobalTheory.SiegelSet.siegelSet', 'GlobalTheory.SiegelSet.IsSmoothModerate']),
    'PositivityTheory.Rg.Sw.lc_of': ('theorem', 'PARTIAL', 'real', 'L',
        'Proves FFT → LC: derives the Howe-duality / Capelli-operator vanishing theorem LC (any linear functional killing differential operators hOp ε c a b vanishes on the null-cone ideal NullSec ε c) from the unitary-group First Fundamental Theorem FFT.',
        ['PositivityTheory.Rg.Sw.FFT', 'PositivityTheory.Rg.Sw.LC', 'PositivityTheory.Rg.Sw.NullSec']),
    'GlobalTheory.PreStabU.geomURat_eq_geomU': ('theorem', 'PARTIAL', 'real', 'L',
        "For an unramified CM field E, section S of places, weight lam, level K', and test function f, equates the rational-point geometric sum geomURat lam (∏_{w∈S} twOrb ...) with the adelic elliptic orbital-integral sum geomU S lam f. NOTE: Separability hypothesis (∃ w ∈ S, ∀ y, f w y ≠ 0 → y.1.val.charpoly.Separable) is bound as `_` (unused) in proof (UnitaryGeometricSideSeparableTest.lean:458) because geomURat/geomU already restrict to separable/elliptic classes.",
        ['GlobalTheory.BCT.geomURat', 'GlobalTheory.BCT.geomU', 'GlobalTheory.BCT.IsSection']),
    'PositivityTheory.SiegelWeilFormula.Fin.whitGenEq': ('theorem', 'PARTIAL', 'real', 'L',
        'Proves Gen.WhitGenEq := WhitGenX (fun M n => M = n ∧ 1 ≤ M) False 2: equal-rank (M = n ≥ 1) unitary Siegel-Weil identity equating the holomorphic value at z = 0 of the regularized Whittaker integral to 2 * meanC (Tamagawa number 2) of the theta integral over {X | gramE σ J X = T}. NOTE: WhitGenX parameterizes (vac → P=1 ∧ uniform ε) with vac=False here so the extra restriction is vacuously discharged (WhitGenLowOf.lean:163,171).',
        ['PositivityTheory.SiegelWeilFormula.Gen.WhitGenEq', 'PositivityTheory.SiegelWeilFormula.Gen.WhitGenX', 'PositivityTheory.SiegelWeilFormula.Gen.Dat0']),
    'UpperTheory.V.Z.Inf.genFE': ('theorem', 'PARTIAL', 'real', 'L',
        "Proves the global Godement-Jacquet functional equation for factorizable matrix coefficients of cusp forms on GL_n(𝔸_K) (n ≥ 2): the completed L-function Λ(s) is entire and satisfies Λ(1-s) = c' * archZeta(φ̂) * (∏_{v∈S} zetaIntegral(Φ̂_v)) * dualPartialL S π s for nonzero constants c, c'. NOTE: Existential constants c, c' ≠ 0 (GenFE.lean:35) rather than explicit global root-number formula; valid for nonvanishing/analytic continuation.",
        ['GroundTheory.Automorphic.AutomorphicForm.cuspForms', 'GroundTheory.Automorphic.GJGlobal.matrixCoeff', 'GroundTheory.Automorphic.GJStandardL.partialL', 'GroundTheory.Automorphic.Spherical.IsSatakeParameter']),
    'UpperTheory.V.Z.GSp4Splitting.lowIso2': ('theorem', 'PARTIAL', 'real', 'L',
        'Proves LowIso: if a unitary (𝔤,K)-module V with infinitesimal character infOf lam (IsLoc) contains a nonzero K-highest-weight vector at weight ν with m0 lam - ν in the positive root cone (inCone), then the K-isotypic component isoSp σ E in V for a Lefschetz K-module E (IsLefK) is nonzero.',
        ['UpperTheory.V.Z.GSp4Splitting.LowIso', 'UpperTheory.V.Z.GSp4Splitting.IsLoc', 'PositivityTheory.RgBcC.Real.IsLefK']),
    'GlobalTheory.SS.exists_neutral_group_model': ('theorem', 'PARTIAL', 'real', 'L',
        'Over a strictly Henselian DVR (R, K) (SH R K), given a projective abelian scheme A over K (IsAbelianScheme A, IsProjBy A.hom), constructs a smooth separated quasi-compact R-model G with commutative group scheme structure SmConn G.Y such that some power c ≥ 1 of every K-point of A extends to an R-point of G.Y.',
        ['GlobalTheory.SS.SH', 'GlobalTheory.SS.Model', 'GlobalTheory.SS.SmConn', 'GlobalTheory.AbLaw.IsProjBy']),
    'GroundTheory.Automorphic.IsExpLieAlgebra.exists_kernel_eq_conv_of_aeval_laplacian': ('theorem', 'PARTIAL', 'real', 'L',
        'Reproducing-kernel theorem for a Lie subgroup G ⊆ 𝔸ˣ (IsExpLieAlgebra G 𝔤): for any monic positive-degree polynomial P and neighborhood U of 1, there exists smooth compactly supported κ with tsupport κ ⊆ U such that every smooth f with P(Δ) f = 0 satisfies f(g) = ∫ f(g y) κ(y) dμ(y).',
        ['GroundTheory.Automorphic.IsExpLieAlgebra', 'GroundTheory.Automorphic.IsExpLieAlgebra.laplacian', 'GroundTheory.Automorphic.IsExpLieAlgebra.smoothFuns']),
    'GlobalTheory.abelianScheme_hom_lifting_nilpotent_dividedPowers': ('theorem', 'PARTIAL', 'real', 'L',
        'Proves GlobalTheory.Published.AbelianLifting: Grothendieck-Messing crystal lifting for abelian schemes (LiftObj: lifting along nilpotent PD thickening R ↠ R₀ corresponds to admissible Hodge filtrations in HdR) and homomorphisms (LiftHom: unique lift preserving Hodge filtration).',
        ['GlobalTheory.Published.AbelianLifting', 'GlobalTheory.Published.GrothendieckMessing.LiftObj', 'GlobalTheory.Published.GrothendieckMessing.LiftHom', 'GlobalTheory.Cris.IsNilDP']),
    'PositivityTheory.RgUd.T.Final.thmT': ('theorem', 'PARTIAL', 'real', 'L',
        'Proves PositivityTheory.RgUd.ThmT k (for characteristic-zero nonarchimedean local field k): any distribution ξ on C_c^∞(M_n(k) × k^n) invariant under Z_G(Z) (Z reduced commutative subalgebra of M_n(k)) and supported on Z_M(Z) × k^n vanishes on all functions supported on {(A, v) | v ≠ 0}.',
        ['PositivityTheory.RgUd.ThmT', 'GroundTheory.Automorphic.Whittaker.supportedIn']),
    'PositivityTheory.SiegelWeilFormula.Gunr.locC': ('theorem', 'PARTIAL', 'real', 'L',
        'Proves PositivityTheory.SiegelWeilFormula.Gunr.LocC: evaluates the local unramified nonarchimedean Siegel-Weil Whittaker integral ∫ whI ∂νv under GoodLoc (self-dual lattice, unimodular J,T, unramified quadratic extension with sign ε) for Re(z) > n^2 as ∏_{i<n} (1 - ε^{M+i} q_v^{-(2z + n - i)}).',
        ['PositivityTheory.SiegelWeilFormula.Gunr.LocC', 'PositivityTheory.SiegelWeilFormula.Gunr.GoodLoc', 'PositivityTheory.SiegelWeilFormula.Gen.whI']),
    'UpperTheory.Zero.LLC.recTExists': ('theorem', 'PARTIAL', 'real', 'L',
        'Proves UpperTheory.Zero.LLC.RecTExists: at every place w of a number field E, there exists a local Langlands map rc : IrrGL(E_w) → WD(h) satisfying the 12 LawsT axioms (dimension, rank-1 LFT, Langlands quotient, cuspidality, twists, central character, dual, Good-injectivity, depth-0 tame, TypeLaw). NOTE: LawsT restricts twist, central, dual, inj, and depth to `Good` representations (IsRecTOfIsRec.lean:65-71), while TypeLaw covers all tame cuspidal inflations (IsRecTOfIsRec.lean:35-53).',
        ['UpperTheory.Zero.LLC.RecTExists', 'UpperTheory.Zero.LLC.IsRecT', 'UpperTheory.Zero.LLC.LawsT']),
    'PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.separation_holds': ('theorem', 'PARTIAL', 'real', 'L',
        'Proves Sep4: for fixed K_∞-type W and finite-adelic level K, finds uniform finite families Ω(M), Θ(M) such that any stable IsAutForm-submodule U with NonPos, CentIm, and simple infinitesimal character generated by TypeB K W vectors maps equivariantly and nontrivially into a good induction tree t : Tr E N.',
        ['PositivityTheory.Rg.BcB.SpectralAccumulation.Sep4', 'PositivityTheory.Rg.BcB.SpectralAccumulation.Tr', 'GlobalTheory.CuspRep.IsAutForm']),
    'UpperTheory.ConvolutionTheory.Sph.ramSph': ('theorem', 'PARTIAL', 'real', 'L',
        'Proves UpperTheory.ConvolutionTheory.Sph.RamSph: for a prime-degree Galois extension M/K of totally complex number fields and cuspidal π, P related by WeakBC, any Satake parameter B of π at w ∩ 𝓞_K lifts to a Satake parameter B of P at ramified places w of M.',
        ['UpperTheory.ConvolutionTheory.Sph.RamSph', 'UpperTheory.V.Published.WeakBC', 'GlobalTheory.CuspRep.CuspSub']),
    'PositivityTheory.Rg.Rs.ascSeed_holds2': ('theorem', 'PARTIAL', 'real', 'L',
        'Proves AscSeed := AscAll ∧ Clause3Asc (Moeglin-Waldspurger residual-spectrum seed): every discrete automorphic representation V with regular integral slice embeds into parabolic induction of a unitary cuspidal π twisted by Speh exponents (AscEmb), and its local components are Speh (IsSpeh).',
        ['PositivityTheory.Rg.Rs.AscSeed', 'PositivityTheory.Rg.Rs.AscAll', 'PositivityTheory.Rg.Rs.AscEmb', 'PositivityTheory.Rg.Rs.Clause3Asc']),
    'GroundTheory.Automorphic.ContragredientTranspose.rank_whittaker_le_one': ('theorem', 'PARTIAL', 'real', 'L',
        "Proves Shalika's local Whittaker multiplicity-one theorem: for any irreducible admissible representation π of GL_n(F) over a nonarchimedean local field F and nontrivial continuous additive character ψ₀, Module.rank ℂ (equivariantFunctionals π psiN(ψ₀)) ≤ 1.",
        ['GroundTheory.Automorphic.IsAdmissible', 'GroundTheory.Automorphic.Whittaker.equivariantFunctionals', 'GroundTheory.Automorphic.Iwasawa.unipotent', 'GroundTheory.Automorphic.Whittaker.psiN']),
    'GlobalTheory.CompanionTheory.SW.finVol_unitaryGroup': ('theorem', 'PARTIAL', 'real', 'L',
        'Proves FinVol F E σ M J: for any CM extension E/F and nondegenerate Hermitian matrix J of size M, Haar measures μ on U(J)(𝔸_F) and fundamental domains 𝓕 for U(J)(F) exist and satisfy μ(𝓕) < ⊤.',
        ['HeckeCharacterZeroLocus.SiegelWeilU.FinVol', 'HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt', 'HeckeCharacterZeroLocus.SiegelWeilU.IsHermND']),
    'CompanionTheory.RgGu.segmentRepresentation': ('theorem', 'PARTIAL', 'real', 'L',
        'Proves GlobalTheory.Published.SegmentRepresentation: over a nonarchimedean local field k, for any irreducible cuspidal σ of GL_d(k) and l ≥ 1, the parabolic induction multiProd (σ, σ|det|, …, σ|det|^{l-1}) has a unique irreducible subrepresentation S, whose normalized Jacquet module is ⨂_{a<l} σ|det|^a.',
        ['GlobalTheory.Published.SegmentRepresentation', 'GlobalTheory.SmGL.multiProd', 'GlobalTheory.SmGL.segTerm', 'GlobalTheory.SmGL.jac']),
    'PositivityTheory.Rg.BcB.E2.orthogonal_keeping_holds': ('theorem', 'PARTIAL', 'real', 'L',
        'Proves E.OrthogonalKeepingOperator: spectral approximation on L^2(H(F)\\H(𝔸))^ι producing continuous, left-invariant, polynomially-weighted L^2 approximate eigenfunctions f_k for a countable *-algebra subset C, while remaining orthogonal to a given sequence g_j ∈ (J K)^⊥ of rapid-decay vectors.',
        ['PositivityTheory.Rg.BcB.E.OrthogonalKeepingOperator', 'PositivityTheory.Rg.BcB.E.Dom', 'PositivityTheory.Rg.BcB.E.WL2']),
    'GroundTheory.ProfCoh.card_cohomology_mul_div_eq': ('theorem', 'PARTIAL', 'real', 'L',
        "Proves Tate's local Euler characteristic formula over a nonarchimedean local field K: for a finite discrete Gal(K_sep/K)-module M with (|M| : K) ≠ 0, |H^0(M)| * |H^2(M)| / |H^1(M)| = |𝒪_K / (|M|)|^{-1}. NOTE: Hypothesis hM : (Nat.card M : K) ≠ 0 (EulerCharGaloisOfCardEq.lean:98) means char(K) ∤ |M|, holding for all finite M when char(K) = 0 and restricting to prime-to-p orders in equal char p.",
        ['GroundTheory.ProfCoh.IsDiscreteRep', 'GroundTheory.ProfCoh.cohomology']),
    'PositivityTheory.Rg.BcB.SpectralAccumulation.eFinal_of': ('theorem', 'PARTIAL', 'real', 'L',
        'Proves Sep4 → FinDisc → LimVec → EFinal: combines tree separation, finite discreteness of bounded-infinitesimal-character automorphic forms, and limit extraction to show converging Hecke-eigenfunction tuples yield a nonzero limit in pairSpace s₁.space s₂.space for untwisted good trees.',
        ['PositivityTheory.Rg.BcB.SpectralAccumulation.EFinal', 'PositivityTheory.Rg.BcB.SpectralAccumulation.FinDisc', 'PositivityTheory.Rg.BcB.SpectralAccumulation.LimVec']),
    'PositivityTheory.SiegelWeilFormula.Fin.whitGenLow': ('theorem', 'PARTIAL', 'real', 'L',
        'Proves Gen.WhitGenLow := WhitGenX (fun M n => M < n ∧ 1 ≤ M) True 0: lower-rank (1 ≤ M < n) Siegel-Weil vanishing identity showing the regularized Whittaker integral has holomorphic value 0 at z = (M - n)/2 when P = 1 and signs ε are uniform. NOTE: Uses vac=True in WhitGenX (WhitGenLowOf.lean:163,173), which activates the hypothesis (∀ i, P i = 1) ∧ ∃ e, ε = fun i _ => e i.',
        ['PositivityTheory.SiegelWeilFormula.Gen.WhitGenLow', 'PositivityTheory.SiegelWeilFormula.Gen.WhitGenX']),
    'GlobalTheory.CongMatch.match_principal_congruence_inert': ('theorem', 'PARTIAL', 'real', 'L',
        'Proves local orbital-integral matching (Match n a b w 1) at an inert non-split place w of an unramified CM field E between the indicator of the principal congruence subgroup K(w^k) ⊆ U(n) and (-q_w^{1/2})^{-kab} times the pullback indicator of K(w^k) along the norm map on GL_a × GL_b.',
        ['GlobalTheory.BCT.Match', 'GlobalTheory.BCT.nrmL', 'GlobalTheory.BCT.Unr']),
    'GlobalTheory.T.theta_measure_nonzero_vectors_bound': ('lit_wrapper', 'PARTIAL', 'wrapper', 'L',
        'Bounds the theta-measure (thetaMeas) of nonzero rational vectors X ∈ E^M with denominator dividing N (N·X_fin ∈ latV) and archimedean norm ≤ r by ENNReal.ofReal(C * (r^{[F:ℚ]M} + r^{2[F:ℚ]M})) for M ≥ 3. NOTE: Pure *Statement.lean re-export (1 dom child) of GlobalTheory.CompanionTheory.SW.MeanCount.mean_count_box (ThetaMeasureNonzeroVectorsBoundStatement.lean:7-8); wrapped statement is real.',
        ['GlobalTheory.CompanionTheory.SW.thetaMeas', 'HeckeCharacterZeroLocus.SiegelWeilU.latV', 'HeckeCharacterZeroLocus.SiegelWeilU.sizeTup']),
    'GlobalTheory.FlagBase.SiegelStep.glVol_step': ('theorem', 'PARTIAL', 'real', 'L',
        'Inductive volume recursion for GL_j(𝔸_E) over a totally complex number field E (j ≥ 2): if glVol E (j-1) < ⊤ then glVol E j = glVol E (j-1) * (vInv E)^{fDeg E * (2j-1)} * ζ_E(j).',
        ['GlobalTheory.FlagMeas.glVol', 'Formalism.HermitianLatticesTheory.vInv', 'GlobalTheory.FlagMeas.zetaE']),
    'PositivityTheory.JacquetShalikaLocal.jacquetShalikaBound': ('theorem', 'PARTIAL', 'real', 'L',
        'Proves GlobalTheory.Published.JacquetShalikaBound: for any unitary cuspidal automorphic representation π : CG E a (E totally complex) and any place w with Satake parameters B (π.HasSat w B), every α ∈ B satisfies q_w^{-1/2} < |α| < q_w^{1/2}.',
        ['GlobalTheory.Published.JacquetShalikaBound', 'GlobalTheory.CuspRep.CG.HasSat', 'GlobalTheory.CuspRep.CG.IsUnitary']),
    'AlgebraicGeometry.isSheaf_type_propQCTopology_iff': ('glue', 'OPAQUE', 'unknown', 'L',
        'OPAQUE: ground Mathlib/external declaration (`unmatched:library_or_external` in kernel.db); source and type signature are absent from data/rh_mirror/src. NOTE: Ground Mathlib/external decl (unmatched:library_or_external in kernel.db); source/type not in data/rh_mirror/src, so statement body not read [L].',
        []),
    'GlobalTheory.SS.semistableReductionSt': ('theorem', 'PARTIAL', 'real', 'L',
        "Proves GlobalTheory.Published.SemistableReductionSt: every principally polarized abelian variety P over a finite extension K/ℚ_p acquires a semi-abelian group-scheme model G (IsSemiAbelian G, with torus-extension fibers over algebraically closed points) over 𝓞_{K'} after a finite extension K'/K.",
        ['GlobalTheory.Published.SemistableReductionSt', 'ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian', 'ReciprocityTheory.ChartRestriction.G.Out.PolAV']),
    'GlobalTheory.GLq.ResCuspProd.main': ('theorem', 'PARTIAL', 'real', 'L',
        'Proves the Mackey/Harish-Chandra restriction formula for parabolic induction of cuspidal characters of GL_n(𝔽_g) (g prime): res a b (hcL L (a+b)) evaluates to the sum over subsets I of L with degree sum a of hcL(I, a) * hcL(Iᶜ, b).',
        ['GlobalTheory.GLq.IsCusp', 'GlobalTheory.GLq.hcL', 'GlobalTheory.GLq.res']),
    'PositivityTheory.Rg.Bc.ArchbcB.B.m1': ('theorem', 'PARTIAL', 'real', 'L',
        'Proves PositivityTheory.Rg.Bc.ArchbcB.B.M1: base change fundamental lemma for the unit element of the spherical Hecke algebra at inert non-split places w of an unramified CM field E (matching 1_{KL n w} with 1_{KGL a × KGL b}).',
        ['PositivityTheory.Rg.Bc.ArchbcB.B.M1', 'GlobalTheory.BCT.Match']),
    'PositivityTheory.SiegelWeilFormula.SwLocFin.locFinX': ('theorem', 'PARTIAL', 'real', 'L',
        'Proves PositivityTheory.SiegelWeilFormula.Gen.LocFinX: for any Schwartz-Bruhat Φ_v with continuous orbital-density function g on regular Hermitian T, the local nonarchimedean Whittaker integral ∫ whI ∂νv converges for Re(z) > t and extends to an entire function W(z) with W((M-n)/2) = g(T).',
        ['PositivityTheory.SiegelWeilFormula.Gen.LocFinX', 'HeckeCharacterZeroLocus.SiegelWeilU.IsContDensityOn', 'PositivityTheory.SiegelWeilFormula.Gen.whI']),
    'GlobalTheory.T.heckeTrace_weightForms_eq_dim_mul_rationalClasses': ('lit_wrapper', 'PARTIAL', 'wrapper', 'L',
        "Equates the trace of the Hecke operator hop S K' f on algebraic-weight automorphic forms forms S lam K' of a definite unitary group to dimW lam * geomURat lam (twOrb ...), assuming separable support at some w ∈ S. NOTE: Pure *Statement.lean re-export (1 dom child) of GlobalTheory.BCT.trOn_forms_hop_eq_geom (HeckeTraceWeightFormsEqDimMulRationalClassesStatement.lean:8-9); wrapped statement is real.",
        ['GlobalTheory.BCT.forms', 'GlobalTheory.BCT.hop', 'GlobalTheory.BCT.dimW', 'GlobalTheory.BCT.geomURat']),
    'UpperTheory.Gal.InertialTypesAlt.G.varTrace': ('theorem', 'PARTIAL', 'real', 'L',
        "Proves UpperTheory.Gal.InertialTypesAlt.G.VarTrace: at a non-split place v of a prime-degree cyclic Galois extension E/F, for local components τ, τ' of a WeakBC-related Galois-invariant cuspidal pair (π, P), matching test functions φ, f with f supported in normSet satisfy HasTwTrace I φ (c * c₁ * z) whenever HasTrace τ f z (c ≠ 0).",
        ['UpperTheory.Gal.InertialTypesAlt.G.VarTrace', 'UpperTheory.Gal.InertialTypesAlt.G.normSet', 'UpperTheory.ConvolutionTheory.C.HasTwTrace']),
    'PositivityTheory.Groth.grothendieckRingPolynomial_of_seg': ('theorem', 'PARTIAL', 'real', 'L',
        'Proves GlobalTheory.Published.SegmentRepresentation → GlobalTheory.Published.GrothendieckRingPolynomial: derives the Bernstein-Zelevinsky isomorphism GrothGL k ≃+ MvPolynomial (Segment k) ℤ (multiplicative under parabolic induction prod₂ and sending segment classes Z Δ to X Δ) from SegmentRepresentation.',
        ['GlobalTheory.Published.GrothendieckRingPolynomial', 'GlobalTheory.Published.SegmentRepresentation', 'GlobalTheory.SmGL.IsSegmentClass']),
    'GlobalTheory.grothendieckRingPolynomial_outright': ('theorem', 'PARTIAL', 'real', 'L',
        'Proves GlobalTheory.Published.GrothendieckRingPolynomial unconditionally by applying grothendieckRingPolynomial_of_seg (#57) to segmentRepresentation (#41). NOTE: 1-line proof composing #57 (grothendieckRingPolynomial_of_seg) with #41 (segmentRepresentation) (GrothendieckRingPolynomialOutright.lean:9-10).',
        ['GlobalTheory.Published.GrothendieckRingPolynomial']),
    'PositivityTheory.Rg.Tf.Loc.bcflUnit': ('theorem', 'PARTIAL', 'real', 'L',
        'Proves PositivityTheory.Rg.Tf.Loc.BCFLUnit (Arthur-Clozel base change fundamental lemma for the unit element): for an unramified cyclic Galois extension E/k of char-0 nonarchimedean local fields, twOrbIntegral(1_{GL_n(𝓞_E)}, δ) = orbIntegral(1_{GL_n(𝓞_k)}, γ) when N(δ) ~ γ, and orbIntegral(1_{GL_n(𝓞_k)}, γ) = 0 when γ is not a norm.',
        ['PositivityTheory.Rg.Tf.Loc.BCFLUnit', 'PositivityTheory.Rg.Tf.Loc.unitFn', 'PositivityTheory.Rg.Tf.Loc.normGL']),
    'PositivityTheory.RgBcC.cxData_model': ('theorem', 'PARTIAL', 'real', 'L',
        'Constructs an explicit Hilbert-space Clifford/Weyl model (lefE, lefFr, lefε, lefι, lefS, lefΓ, lefT) satisfying all axioms of CxData lam for any antitone lam : Fin n → ℤ (smooth GL_n(ℂ)-action extending U(n)-module, CAR relations, Dirac-like involution T, grading Γ, and scaling flow S).',
        ['PositivityTheory.RgBcC.CxData', 'PositivityTheory.RgBcC.lefE', 'PositivityTheory.RgBcC.lefFr']),
})
