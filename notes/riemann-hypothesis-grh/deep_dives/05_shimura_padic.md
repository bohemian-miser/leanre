# Deep Mathematical Comprehension: `Lib/Shimura/`, `Lib/Cohomology/`, and `Lib/PadicComparison/` -> `SeedRepresentation.lean` & `New/Congruences/Lifting/`

Target repository: `/usr/local/google/home/rop/github-personal/leanre/data/rh_grh/src/` (read-only audit of `upstream/main` `grh`).  
Note on path resolution: the prompt referenced `New/Congruences/GaloisRepresentations/SeedRepresentation.lean`, which does not exist on disk; the actual file is `src/Lib/GaloisRep/Main/SeedRepresentation.lean`, which feeds `src/Lib/GaloisRep/Main/{OddRank,SplitCase,AllRanks}.lean` and thence `src/New/Congruences/GaloisRepresentations/{AttachedRepresentations,RowsAndColumnsFromLabels,RowsFromEigensystems}.lean` and `src/New/Congruences/FirstOrder/DenominatorBound.lean`.

---

## 1. Engine Architecture & Entry/Exit Interface

### 1.1 High-level dataflow across the three pillars

```
Lib/Cohomology/                             Lib/PadicComparison/
  Etale/Basic.lean (Abelian.Ext on TestRing)  Descent/{TestCategory,AlmostDescent} (IsCell, PadicTest, Ainf, Bmax)
  ProperBaseChange/ (PlaceSpace, Theorem)     ToricTower (TimesBNat, wangComplex)
  SmoothBaseChange + ProjectiveLine           Duality/{GoodPairs,LineIntegration} (Alexander duality)
  Hodge/FixedPointFormula + PointClass        Primitive/ComparisonTheorem (finite_and_primitive_comparison)
  WoodsHole (ellAdicCohom.woods_hole)         HodgeTate/{Map,PeriodMap} (exists_hasHodgeTateWeight)
          \                                   Crystalline/ComparisonMap + CrystallineFrobenius
           \                                    (ellAdicCohom.isCrystalline_and_linearFrob_rel)
            \                                 /
             v                               v
             Lib/Shimura/
               IntegralModel/PELDataExistence + ThetaModuli/PELThetaTori (PEL, exists_pel)
               Uniformisation/{ModelExists,HolomorphicFamilies} + IntegralModel/BallImmersion
               GoodReduction/{GaussSums,MultiplicativeNorm} + ThetaNormality/NormalGeneration
               ThetaModuli/{FlatClosure,FamilyFromPoints,ThetaFamilyRigidity,UniversalFamily}
               Deformation/{TangentCount,TangentBound} (Drinfeld first-order bound)
               HeckeTower/Model + IntegralModel/TowerExistence + CongruenceRelation/EichlerShimura
               Transfer/{Lefschetz,WeightOccurs} + Eigenspace (Model.exists_galois_rep)
                                  |
                                  v
               Lib/GaloisRep/Main/SeedRepresentation.lean (exists_rep_of_cuspidal_type)
                                  |
                  via OddRank.lean / AllRanks.lean
                                  v
               New/Congruences/GaloisRepresentations/
                 AttachedRepresentations.lean (isLiftSetting_descentPair)
                 RowsFromEigensystems.lean    (abs_descentPair_weight_add_liftWeight_le)
                                  |
                                  v
               Lib/PadicHodge/{Kisin,Crystalline} + Lib/PadicComparison/Descent/TestCategory
                                  |
                                  v
               New/Congruences/Lifting/ (CupOrthogonalityBounds, FewLowJumps, CupProductBound, ...)
               New/Congruences/LocalLoss/CrystallineCocycles.lean (normLength_dualDefect_le_of_crystallineSizes)
```

**Key architectural clarification on `New/Congruences/Lifting/`:**  
Inspection of the imports of `src/New/Congruences/Lifting/*.lean` shows that `Lifting/` imports `Lib.PadicComparison.Descent.TestCategory` (in `CupProductBound.lean:7`, `ExponentLattices.lean:8`, `FewLowJumps.lean:6`, `HodgeExpansion.lean:12`, `TameCharts.lean:8`) **only** for basic `p`-adic period ring definitions (`New.Period.OC`, `OFlat`, `Ainf`, `IsCompleteTorsionFree`, etc.). The Hodge-Tate jump and Kisin-module cup-product orthogonality machinery in `New/Congruences/Lifting/` is directly built on `Lib.PadicHodge.Kisin.{Modules,FrameTheorem,PeriodMatrixBasis}`, `Lib.PadicHodge.Crystalline.Regularity`, and `Lib.PadicHodge.RadiusLemma`. Meanwhile, `Lib/Cohomology/` and the *cohomological* theorems of `Lib/PadicComparison/` (`finite_and_primitive_comparison`, `exists_hasHodgeTateWeight`, `ellAdicCohom.isCrystalline_and_linearFrob_rel`) flow into `src/Lib/Shimura/Eigenspace.lean`, which outputs the geometric Galois representations and their Hodge-Tate / Frobenius jump properties into `SeedRepresentation.lean`, and from there via `AttachedRepresentations.lean` and `RowsFromEigensystems.lean` into `LocalLoss/` and `Lifting/`.  
*(Minor hygiene observation: `RowsAndColumnsFromLabels.lean:11` and `DenominatorBound.lean:15` both `import Lib.PadicComparison.ToricTower`, though grep confirms neither file uses `TimesBNat`, `Wang`, `Koszul`, or `IsLine`.)*

### 1.2 Exported interface table

| Pillar & File | Line | Exported Declaration | Role & Downstream Consumers |
| :--- | :--- | :--- | :--- |
| `Lib/Shimura/ThetaModuli/PELThetaTori.lean` | `:99`, `:171` | `PEL`, `PEL.levelTorsion` | Explicit PEL parameters (`β`, `level`, `ξ`, `rank`, `paddedNorm`, `dualTorsion`, `lagrangian`); constructed via `exists_pel` in `PELDataExistence.lean`, consumed by `UniversalFamily.lean`, `SeedRepresentation.lean:716` |
| `Lib/Shimura/ThetaModuli/UniversalFamily.lean` | `:511-513` | `nonempty_universalFamily : Nonempty (UniversalFamily D R)` | Existence of smooth flat integral model over `R` carrying rigid theta abelian scheme `A`, consumed by `TowerExistence.lean` |
| `Lib/Shimura/IntegralModel/TowerExistence.lean` | `:125-146`, `:198-212` | `GraphClosure.congruenceRelation`, `isTangentPoly_localTerm_of_translate` | Builds `New.Variety.Model` (`HeckeTower/Model.lean:86-165`) with projective covers, congruence relation, and local tangent polynomials; consumed by `Eigenspace.lean` and `SeedRepresentation.lean` |
| `Lib/Shimura/Eigenspace.lean` | `:744-756` | `Model.exists_galois_rep` | Produces `r : Gal(Ω/E) →* GL (Fin N) (PadicAlgCl ℓ)` with crystallinity, Eichler–Shimura at & away from `ℓ`, and Hodge–Tate jump relations (`jumpsRelAt_of_isEigenQuotient`); consumed by `SeedRepresentation.lean` |
| `Lib/GaloisRep/Main/SeedRepresentation.lean` | `:822-845` | `New.GaloisRep.exists_rep_of_cuspidal_type` | Glues per-embedding representations `exists_padicRep_of_pel` (`:514-527`) via `exists_galRep_charpoly_eq_of_forall_embedding` (`:321-336`) to exact rank `a`; consumed by `OddRank.lean` -> `AllRanks.lean` -> `AttachedRepresentations.lean` |
| `Lib/Cohomology/Etale/Basic.lean` | `:105-146` | `AbFunctor`, `HasAbFunctorExt`, `H`, `IsTest` | Presheaf `Ext` cohomology on AIC reduced `TestRing`s; base for all of `Lib/Cohomology/` & `Lib/PadicComparison/` |
| `Lib/Cohomology/ProperBaseChange/Theorem.lean` | `:642-645` | `IsProperOver.proper_base_change` | Proper base change for `TestTheory`; consumed by `WoodsHole.lean` & `PadicComparison` |
| `Lib/Cohomology/SmoothBaseChange.lean` | `:271-275` | `isTestCohomEquiv_baseChangeTransition` | Base-change equivalence for smooth morphisms with open finite-chart covers |
| `Lib/Cohomology/ProjectiveLine/ConstantLineFormula.lean` | `:72-80` | `isLerayHirschBasis_lineBasis_of_basis` | Projective bundle formula `H(ℙ¹ × S) ≅ H(S) ⊕ η·H(S)`; feeds Alexander duality & `WoodsHole.lean` |
| `Lib/Cohomology/WoodsHole.lean` | `:229-241` | `ellAdicCohom.woods_hole` | Half-Woods-Hole vanishing: annihilator relation `∑ b_i λ_h(u_i^* x) = 0` gives `IsNullFamily u b d h` (`∑ local terms = 0`); consumed by `Eigenspace.lean` |
| `Lib/PadicComparison/Primitive/ComparisonTheorem.lean` | `:249-263` | `finite_and_primitive_comparison` | `ℤ_ℓ`- vs `O_C^♭`-"primitive" comparison over `PadicTest`; feeds `HodgeTate` & `Crystalline` |
| `Lib/PadicComparison/HodgeTate/PeriodMap.lean` | `:279-297` | `exists_hasHodgeTateWeight` | Period map identifying geometric `ℓ`-adic cohomology with Hodge cohomology weighted by `t^h`; consumed by `Eigenspace.lean` |
| `Lib/PadicComparison/CrystallineFrobenius.lean` | `:753-769` | `ellAdicCohom.isCrystalline_and_linearFrob_rel` | Proves `ellAdicCohom` of smooth projective `X` is crystalline (`IsCrystalline`) and `linearFrob`-compatible; consumed by `Eigenspace.lean` |
| `New/Congruences/Lifting/CupOrthogonalityBounds.lean` | `:509-516` | `hasCupExponent_of_isTameType` | Bounds Bloch–Kato cup exponent in tame unramified setting (`FewLowJumps` + `CupProductBound`); alongside `dualDefect_eq_zero_and_dualDefect_le` (`:343-359`) & `hasCupExponent_{any_pattern,sparse_thick}` (`:371-412`), feeds `LocalLoss/CrystallineCocycles.lean:583-597` |

---

## 2. Step-by-Step Mathematical Walkthrough

### Part A: How `Lib/Shimura/` Produces `SeedRepresentation.lean` Without Kottwitz PEL Representability

Classical Shimura-variety constructions attach Galois representations by proving that a Kottwitz PEL moduli problem is representable by a smooth quasi-projective scheme over a local ring, analyzing its Dieudonné crystal via Grothendieck–Messing deformation theory, and comparing trace formulas. `Lib/Shimura/` replaces representability with **explicit projective Zariski closure of analytic theta coordinates**, **good reduction from 4th-power Gauss sums**, **flat closure from monomial degree bounds**, and **Drinfeld's finite-group-scheme tangent bound**.

#### Step A1: Fixed explicit PEL datum and complex theta tori
1. **Explicit PEL parameters (`PELThetaTori.lean:99-158`, `PELDataExistence.lean:120`):**  
   Given a CM field `E`, `exists_star_eq_neg_and_im_pos` (assuming `[HasPrimitiveRoot5040 E]`, where `5040 = 7!`) and `exists_pel` produce a `PEL E` structure `D` with:
   - an order element `β : 𝓞 E` with `star β = 1 - β` (`star_beta`), separating embeddings (`emb_beta_eq_of_ne`, `emb_star_beta_ne`) to fix a `(1, n-1)`-style signature at a distinguished place `τ₀`;
   - a purely imaginary element `ξ : E` (`xi_im_pos`, `xi_re_eq_zero`) defining the Hermitian polarization form;
   - a finite torsion group `dualTorsion` of odd cardinality (`odd_card : Odd (Nat.card dualTorsion)`), a Lagrangian subgroup `lagrangian` (`mem_lagrangian`, `torsion_mem_lagrangian`), a level `level : 𝓞 E` with `dualTorsion_le_levelTorsion` (`:175`), and a padding exponent `paddedNorm : ℕ` (`three_le_paddedNorm : 3 ≤ paddedNorm`, `hasPadding_one`, `hasPadding_beta`).
2. **Analytic uniformization (`Uniformisation/ModelExists.lean`):**  
   Any `τ₀`-definite hermitian/automorphic point gives rise to a complex torus `A_ℂ = V / Λ` with `𝓞 E`-action and Hermitian Riemann form matching the adelic polarization via `exists_fourierChar_riemannForm_eq_ψf_xiForm` and `exists_map_eq_and_eq_polarisationForm_of_fourierChar_eq`. Each such torus `x` carries normalized level-`D.levelTorsion` theta coordinates `(θ(ω, ·))` taking values in `ℙ^{#dualTorsion - 1}(ℂ)`.

#### Step A2: Valuation-arc good reduction from Gauss sums and normal generation
To show that the Zariski closure of these complex theta points over `R ⊂ ℂ` defines a *smooth*, *flat* family of **abelian schemes** (never degenerating to semiabelian/toric boundary strata along any prime of `R`), one must prove that along every valuation ring `v.valuationSubring` over a good prime of `R`, each theta torus has **good reduction**: after rescaling each projective point so its maximum valuation is `1`, the reduced theta coordinates in the residue field `k_v` do not all collapse onto an improper degenerate stratum, and generate the homogeneous coordinate ring.

1. **Gauss-sum 4th-power reality (`GoodReduction/GaussSums.lean:71-84, 226, 281-284`):**  
   Let `h : IsHermitianAction L B F β`. On the kernel `h.MulKernel a` (whose cardinality is `(F a).det * conj (F a).det` by `card_mulKernel` at `:226`), the quadratic character `q(z)` satisfies `normShift_sum_eq_char_smul`, and the finite Gauss sum obeys the fourth-power reality identity (`:281-284`):
   `sum_conj_pow_four_eq_sum_pow_four : (∑ z : h.MulKernel κ, conj (q z)) ^ 4 = (∑ z : h.MulKernel κ, q z) ^ 4`.  
   Why 4th powers? Via Lagrange's four-square decomposition `N^2 - 1 = a₁² + a₂² + a₃² + a₄²` and an explicit quaternion matrix acting on four copies of the kernel, the phase mismatch cancels to the fourth power. Thus the absolute value of every nondegenerate theta-shift Gauss sum is rigidly locked to a rational square root of its kernel cardinality (no subtle Archimedean phase cancellation can drive sums abnormally small).
2. **Poincaré-series averaging & multiplicative norm (`GoodReduction/MultiplicativeNorm.lean:271-278, 769-848, 943-949`):**  
   Using `averagedPullback` and `exists_sum_normShift_eq_smul` (`:271-278`), a multiplicative shift inequality (`hasMultiplicativeNorm_of_frequently_hasShiftBound` at `:769-772`, `hasMultiplicativeNorm_of_expanding` at `:842-848`) holds on the ultrametric theta ball: shifting by torsion elements multiplies the valuation norm predictably without hidden cancellations. Consequently, `ThetaTorus.hasGoodReduction_and_val_card_eq_one` (`:943-949`) proves that if `ρ : 𝓞 E →+* K_v` extends `Φ v₀` and `comap ρ (maximalIdeal v.valuationSubring)` is a good prime (`D.IsGoodAt`), then:
   `HasGoodReduction x.automorphyForm x.multiplier v D.paddedNorm ∧ v (Nat.card D.dualTorsion) = 1`.
3. **Peak charts and normal generation (`ThetaNormality/NormalGeneration.lean:644-650, 738-741`, `UniversalFamily.lean:88-154`):**  
   Why does `HasGoodReduction` ensure an honest abelian scheme in `∏ ℙ^{#T - 1}`?
   - Schur orthogonality (`sum_shift_mul_shift`) gives the exact vector-space dimension of degree-`r^j` sections (`finrank_reduction_eq`, `:644-650`) and characterizes vanishing/norm dominance in coordinates (`thetaNorm_lt_iff_coords`, `:738-741`).
   - Peak charts `HasPeakCharts c t` (`UniversalFamily.lean:88-91`: `l + k ∈ [o, -o, s - o]`) hold automatically from good reduction (`hasPeakCharts_of_hasGoodReduction`, `:98-111`), and force the homogeneous vanishing ideal of the reduced torsion fiber to be **cut out in bounded degree** with prescribed Hilbert function (`exists_isCutOutAt_and_hasPeakCharts`, `:143-154`).

#### Step A3: Mumford theta-null Zariski closure & flat abelian family without moduli representability
1. **Explicit closure in `∏ ℙ^N` (`ThetaModuli/UniversalFamily.lean:239-241, 286-292`):**  
   Given a dense set of complex tori `y : B → ...`, define the base scheme `ThetaClosure R y` directly as:
   `ReducedClosure fun (ω : D.levelTorsion) (b : B) ↦ levelPoint R ω (y b)`
   inside the finite product `∏_{ω ∈ D.levelTorsion} ProjSpace D.dualTorsion` over `Spec R`. Because the product of projective spaces is proper, every point `z` of `ThetaClosure R y` specializes to the closed point of a valuation arc `α : Spec v.valuationSubring ⟶ C.scheme.left` coming from a dense complex point over a good prime (`ThetaClosure.exists_arc_isGoodAt`, `:286-292`). By `ThetaTorus.hasGoodReduction_and_val_card_eq_one`, every such arc inherits good reduction and `HasPeakCharts`!
2. **Flatness via monomial degree bounds (`ThetaModuli/FlatClosure.lean:91-98` & `FamilyFromPoints.lean:1052-1069`):**  
   How do we get a *flat* abelian scheme `A → ThetaClosure` without knowing a moduli functor is representable?
   - On affine charts, `FlatClosure.lean` proves a Dickson/monomial-ideal stabilization theorem `eventually_isCutDegree` for `IsCutDegree` (`:91-93`): if a monomial ideal leaves out at most `σ i = thetaRanks T r i` standard monomials in degrees `r^i` for `i ≤ d`, then it does so for *all* `i`.
   - `eq_map_and_flat_of_isCutOut` and `exists_isFlatClosure` turn a collection of `A`-valued ideals specializing at every residue field to `IsCutOutAt` ideals of fixed rank `σ i` into an explicit **flat** closed subscheme over `S` whose geometric fibers are reduced!
   - `Variety.exists_thetaFamily_of_points` (`FamilyFromPoints.lean:1052-1069`) constructs the total space `A` as this `IsFlatClosure` of the theta points of the complex fibers, and uses Riemann's bilinear/theta relations (rational identities already verified on the dense complex fibers) together with flat specialization to extend the addition law `A ×_S A → A`, the `𝓞 E`-endomorphisms, the `PEL.HasClassLaws` line-bundle identities, and the `levelPoints` morphisms over the entire base `S`.
3. **Rigidity over local Noetherian rings (`ThetaModuli/ThetaFamilyRigidity.lean:69-100`):**  
   `ThetaFamily D S τ` packages `total`, `lineBundle : LineBundle total.left D.dualTorsion`, `embeds : lineBundle.IsProjEmbedding total.hom`, `levelPoints`, `theta_law`, `class_laws`, and `signature`. Over any local ring `B`, `HasSpanningCoords` implies two decisive facts: (a) a torsion-kernel criterion in characteristic `l` (`eq_zero_of_pairing_eq_zero`), and (b) `eq_and_comp_toFamily_eq_of_hom` — any homomorphism preserving `𝓞 E`-action, pairing, and level points identifies two `ThetaObject`s and their classifying morphisms into `S`. Thus `ThetaClosure` acts *as cleanly as* a fine moduli scheme on points without ever stating or proving representability of a PEL stack!

#### Step A4: Smoothness via holomorphic ball immersion + Drinfeld's first-order tangent bound
Having a flat family of abelian varieties over `ThetaClosure`, why is `ThetaClosure` **smooth** of relative dimension `n - 1` (`n = Fintype.card D.Index`) over `Spec R`?
1. **Lower bound in characteristic `0` (`IntegralModel/BallImmersion.lean:116-123`, `UniversalFamily.lean:451-454`):**  
   Complex period maps (`PeriodMap.isSignedFrameFor`) provide finite analytic families (`exists_finite_isDenseFamily`, `:451-454`). Because the signature is `(1, n-1)` at `τ₀` (`signature` in `ThetaFamily` / `exists_isLieChart_hasSignature`), `AnalyticFamily.isHolomorphicImmersionAt_of_holomorphicAt` (`BallImmersion.lean:116-123`) embeds an `(n - 1)`-dimensional complex ball holomorphically into `ThetaClosure(ℂ)`, showing `dim ≥ n - 1` on the generic fiber.
2. **Upper bound in mixed/positive characteristic via Drinfeld bases (`Deformation/TangentCount.lean:47-86, 164-210, 366-425`, `Deformation/TangentBound.lean:186-195, 550-558, 746-755`):**  
   Over any field point `y : Spec k ⟶ S` in residue characteristic `q`, one must prove `dim_k T_y(S_k) ≤ n - 1`:
   - **Lifting deformations on `1`-dimensional group schemes (`TangentCount.lean`):** Let `x` be the `𝓞_{E, v₀}`-divisible / finite subgroup scheme (`placeTorsion x`) cut out by the place `v₀` above `q`, with maximal ideal uniformizer `π` and residue size `q`. Take a sufficiently deep level `m` and let `B = Γ_{(o)}` be the universal local ring of the `v₀^m`-torsion (`exists_local_universal_point`, `:78-86`). Using Cartier/algebraic group structure, `exists_isLocalParameter` (`:196-210`) produces a single nilpotent generator `τ` (`IsLocalParameter`, `:164-188`) with `B ≅ k[τ]/(τ^N)` where `N = #ν⁻¹(0)` and `q^n = #ker(ν) · q^{dim placeTorsion(k)}`.
   - **Semilinearity forces `i = q^j` (`TangentCount.lean:47-72, 366-425`):** Consider a `k`-linear space `W` of dual tangent vectors / logarithm functionals compatible with the `𝓞_{E, v₀}`-action on `B`. Any nonzero element `f` has a minimal nonzero `τ^i` term (`f(τ) = ∑ c_i τ^i`), and `π`-semilinearity forces `a ↦ a^i` to be additive (specifically `F`-linear on `k`) for the minimal degree `i`. By `mem_powers_card_of_isLinearMap_pow` (`:47-72`), any field endomorphism/monomial map `a ↦ a^i` that is `F_q`-linear must satisfy `i = q^j`! With `j = 0` accounting for the `d`-dimensional étale quotient and `0 < j < n - d` (`h_lt`, `:425`) for the connected local part (`N = q^{n-d}`), the linearly independent powers `τ^{q^j}` give at most `d + (n - d - 1) = n - 1` independent functionals (`finrank_le_of_placeTorsion`, `:366-380`).
   - **Applying the Drinfeld lift to the tangent space (`TangentBound.lean:186-195, 550-558, 746-755`):** Pull back the universal abelian family `ThetaFamily` over `k ⊕ M*` to `k[ε]` along a tangent vector `l ∈ M`. Because `signature` constrains `(star D.β - b) • Lie(A)` to rank `1` along the structure map, `drinfeld_lift` (`:186-195`, via `AgreeModEps` and `IsInfinitesimal`) lifts the abelian scheme along `l` when the logarithm functional `ω(c • Y y)` vanishes for `c = (star D.β - b) * c`. By Frobenius and Weil-pairing adjointness (`eq_of_lift_star_sub`, `:550-558`), any tangent vector killing these functionals forces the pullback deformation to be trivial (since the level structure is uniquely rigid by `eq_and_comp_toFamily_eq_of_hom`). Thus `Module.finrank k M ≤ Fintype.card D.Index - 1` (`finrank_tangent_le_card_index_sub_one`, `:746-755`).
3. **Assembly (`UniversalFamily.lean:472-480, 511-513`):**  
   `exists_smooth_near_arc` (`:472-480`) combines the holomorphic immersion (characteristic `0` dimension `≥ n - 1`) with the tangent-space upper bound `≤ n - 1` and flatness of the closure to deduce smoothness over a neighborhood of every arc, yielding `nonempty_universalFamily : Nonempty (UniversalFamily D R)` (`:511-513`).

#### Step A5: Hecke tower, congruence relation, eigenspace extraction, and `SeedRepresentation.lean`
1. **Hecke tower & congruence relation (`HeckeTower/Model.lean:86-165`, `IntegralModel/TowerExistence.lean:62-68, 125-146, 198-212`):**  
   Using `nonempty_universalFamily` across varying tame levels `g`, `TowerExistence.lean` builds `New.Variety.Model` (`Model.lean:86-165`): projective varieties `W_i = cover i` over base `Z`, finite Hecke correspondence legs `leg i g`, Galois coverings in characteristic `0`, tangent conditions (`isTangentPoly_localTerm_of_translate`), and the **Eichler–Shimura congruence relation** (`GraphClosure.congruenceRelation`, `:125-146`). Notice the combinatorial clean-up inside `TowerExistence.lean`: Möbius inversion along subgroup lattices (`cancels_moebius_of_factorsThrough_sup`, `:62-68`) removes lower-level fixed points cleanly, and good reduction along valuation arcs verifies the congruence polynomial on reduced models.
2. **Eigenspace projection to Galois representations (`Eigenspace.lean:153-165, 744-756`):**  
   Inside `⨁_{n ≤ 2d} V^n(Z)` (where `V^n(Z)` is the `ℓ`-adic cohomology `ellAdicCohom` from `Lib/Cohomology/`), fix a cuspidal/cohomological Hecke system `θ`. `IsEigenQuotient` (`:153-165`) defines a universal quotient `Q` on which every Hecke operator `T` acts via `θ(T)`. Then `Model.exists_galois_rep` (`:744-756`) constructs `r : Gal(Ω/E) →* GL (Fin N) (PadicAlgCl ℓ)` and proves:
   - **Eichler–Shimura away from `ℓ`**: via `CongruenceRelation/EichlerShimura.lean` (`frobEnd`, `ellAdicPull_frobEnd`, `congruence_relation`), `aeval_heckePoly_eq_zero_of_isEigenQuotient` pins Frobenius characteristic polynomials outside `ℓ`;
   - **Crystallinity & Eichler–Shimura at `ℓ`**: `Lib/PadicComparison/` (`ellAdicCohom.isCrystalline_and_linearFrob_rel`) shows `Q` is crystalline (`isCrystalline`) and `linearFrob` satisfies the Hecke polynomial at `ℓ` (`isKilledBy_heckePoly_of_isEigenQuotient`);
   - **Exact Hodge–Tate jump vanishing / transfer**: `jumpsRelAt_of_isEigenQuotient` combines `ellAdicCohom.woods_hole` (`Lib/Cohomology/WoodsHole.lean`), `exists_hasHodgeTateWeight` (`Lib/PadicComparison/HodgeTate/PeriodMap.lean`), and `Transfer/Lefschetz.lean` + `Transfer/WeightOccurs.lean` (`IsNullHecke`, `OccursInWeight`, `prod_map_tauHecke_mem_spanOn`) to deduce which jumps can occur in the `ℓ`-adic representation from definite algebraic modular forms (`MarkedDefiniteSums`).
3. **Gluing into `SeedRepresentation.lean` (`src/Lib/GaloisRep/Main/SeedRepresentation.lean:47-48, 171-185, 321-336, 514-527, 822-845`):**  
   `New.GaloisRep.exists_rep_of_cuspidal_type` (`:822-845`):
   - Takes an automorphic eigenform `f` on a definite unitary group with a cuspidal type at an auxiliary place `w₀`, and passes to a central character variant `ψ` via `exists_central_eigenform` (`:171-185`).
   - For each infinite embedding `τ₀ : E →+* ℂ`, `exists_padicRep_of_pel` (`:514-527`) constructs a `PEL` datum via `exists_pel`, builds `New.Variety.Model` via `TowerExistence`, and invokes `Model.exists_galois_rep` to get a Galois representation `r_{τ₀}` (whose rank `N` may exceed the target rank `a` by multiplicity, or vary with `τ₀`, while sharing the exact Satake/Hecke parameters at almost all unramified primes!).
   - `exists_galRep_charpoly_eq_of_forall_embedding` (`:321-336`) extracts the irreducible/semisimple summand of exact rank `a` and pins down both the characteristic polynomials and the `p`-adic Hodge-Tate weights across all embeddings using `HasNoSmallRelations` (`:47-48`, an `(n+1)^2` linear-relations bound on polynomial traces/characteristic-polynomial coefficients over Chebotarev-dense Frobenius elements).
   - Downstream, `OddRank.lean` (`IsWeakBaseChange.attached_comp_stepKerInclusion`, `IsWeakBaseChange.descendsAt`) and `AllRanks.lean` strip auxiliary base changes / twists, feeding `New/Congruences/GaloisRepresentations/AttachedRepresentations.lean` (`isLiftSetting_descentPair`) and `RowsFromEigensystems.lean` (`abs_descentPair_weight_add_liftWeight_le`).

---

### Part B: How `Lib/Cohomology/` & `Lib/PadicComparison/` Deliver Crystallinity & Jump Bounds

Classical `p`-adic comparison (`C_cris`, `C_HT`) requires Grothendieck topoi / étale & pro-étale sites (SGA 4), continuous cohomology of sheaves, and Fontaine's `B_cris` with a chosen divided-power structure on `A_inf / ker θ`. `Lib/Cohomology/` and `Lib/PadicComparison/` replace *all* of this with **`Abelian.Ext` on presheaves of abelian groups over AIC test categories**, **`ℙ¹` Alexander duality**, **one-variable `TimesBNat` toric towers**, and **`Bmax` + `pdIdeal`**.

#### Step B1: Presheaf `Abelian.Ext` on `IsTest` and `PadicTest` (no SGA 4 sites!)
1. **Sites replaced by `TestRing` and `IsTest` (`Lib/Cohomology/Etale/Basic.lean:52-54, 105-146`):**  
   Work inside `AbFunctor C := C ⥤ AddCommGrpCat.{1}` where `C` is a category of affine test rings (e.g. `CommAlg k` or `PadicTest`), equipped with `[HasAbFunctorExt C]`. For any `N, F : AbFunctor C`, cohomology is defined directly as:
   `H N F n := Abelian.Ext N F n`.
   A scheme/functor `X : C ⥤ Type 1` enters via `freeAb.obj X` (`A ↦ ℤ[X(A)]`). Why does presheaf `Ext` on test objects equal true étale cohomology (with no sheafification or hypercovers)?
   Because test rings `IsTest` (`:52-54`) are required to be:
   - **reduced**,
   - **absolutely integrally closed** (`IsAbsIntegrallyClosed`, AIC — so every finite étale cover of a point/test ring splits locally into Zariski clopen pieces!), and
   - **idempotent-splitting / comparable** (`HasPartitions`, `HasZariskiDescent`).
   Over AIC test rings, the higher étale cohomology of every coefficient sheaf vanishes on points, so presheaf `Ext(ℤ[X], F)` computes the exact Leray–Cartan hypercohomology of `X`!
2. **Proper Base Change via `placeSpace` and Zorn on AIC subrings (`ProperBaseChange/PlaceSpace.lean:55-66, 89-96, 162-174`; `Theorem.lean:454-645`):**  
   `IsProperOver` (`PlaceSpace.lean:55-66`) encodes properness valuatively via `ValuativeLift` (`:162-174`). To prove `IsProperOver.proper_base_change` (`Theorem.lean:642-645`), consider the poset of AIC subrings `R₀ ⊆ T` over which the fiber/ambient pair is cohomologically equivalent (`IsTestCohomEquiv`), take a maximal subring via Zorn (`exists_cocone_iSup`), and if it is not all of `T`, pick a missing element `x` and cover `Spec T` by the valuation locus `{x ∈ V}` and `{x⁻¹ ∈ V}` (`isAcyclicOver_of_mem_or_inv_mem`). Mayer–Vietoris + Čech descent over finite `ResiduePlace` sets (`exists_isAcyclicOver_placesFiniteOn`, `isTestCohomEquiv_closedFiber_killingPlaces`, `isTestCohomEquiv_closedFiber`) extends the equivalence strictly further — contradiction!
3. **Smooth Base Change & `ℙ¹` Alexander Duality (`SmoothBaseChange.lean:116-123, 271-275`, `ConstantLineFormula.lean:72-80`, `PerfectLine.lean:20-32`, `GoodPairs.lean:697-701`):**  
   - **Projective line formula**: `isLerayHirschBasis_lineBasis_of_basis` (`ConstantLineFormula.lean:72-80`) shows `H(ℙ¹ × S) ≅ H(S) ⊕ η · H(S)` (`etaOneClass`, `comp_pull_etaOneClass_eq_pullbackAlong_oneLocConst`); to prove `η · 1` never vanishes in characteristic `ℓ`, `TiltedLineFormula.lean` passes to a twisted/tilted theory `IdealFamily.ofMaximalIdeal` (`isLerayHirschBasis_of_forall_isField`).
   - **Perfect line in mixed characteristic**: `PerfectLine.lean:20-32` constructs the perfect projective line on `O^♭` from two discs `O^♭[ℚ≥0]` glued along the torus `O^♭[ℚ]` (`gluing : ℤ[torus ⊔ point] → ℤ[two discs]`), showing the cokernel has trivial cohomology (`subsingleton_H_cokernel_gluing`) by splitting Laurent polynomials according to the sign of the exponent in `ℚ`.
   - **Alexander Duality on standard étales**: `GoodPairs.lean:697-701` proves `ComparedTheory.isFiniteLerayHirsch_standard_etale` by embedding a standard étale affine into `(ℙ¹)^d`, isolating its boundary via `multihomogeneousIdeal` (`testUnitLocus`, `affineToLines`), and applying `ℙ¹` Leray–Hirsch + excision.
   - **Globalization**: `SmoothBaseChange.lean` patches local étale charts (`ComparedTheory.mem_of_isClosedClass_of_isCharting`, `isTestCohomEquiv_baseChangeTransition` at `:271-275`) to get finite/smooth base change for `TestTheory`.

#### Step B2: Half-Woods Hole fixed point formula (`Lib/Cohomology/WoodsHole.lean`)
Classical Woods Hole requires Poincaré duality / trace maps to identify the alternating trace on cohomology with local fixed-point terms. For `SeedRepresentation` and `Eigenspace.lean`, **only the vanishing direction ("half-Woods Hole")** is needed: if a `k`-linear combination of endomorphisms `∑ b_i u_i^*` kills a Hodge-Tate / `h`-weight piece `λ_h` on `H^d(X)` (`IsNullHecke`), must the sum of local Jacobian ratios vanish?
1. **Hodge cohomology as presheaf `Ext` (`Hodge/Site.lean`):**  
   Define `HodgeH (freeAb.obj W) q` on `HodgeTest` (square-zero pairs `(A, M)` via `HodgeTest.sqZeroExt`) with coefficients in `exteriorAlg` (`⋀_A M`).
2. **Pullback of the diagonal along a twisted graph (`Hodge/FixedPointFormula.lean:28-55`, `WoodsHole.lean:229-241`):**  
   Given separated smooth `X` with finite atlas and self-maps `u_i, c : W → X` with reduced isolated coincidences (`IsTangentPoly` at each coincidence: `dc` injective, `du = dc ∘ B`, `P(t) = P(0) det(1 - t B)`):
   - Twist the graph by scaling the square-zero tangent module `M` by a formal parameter `t` in the first factor (`scaledGraph t u c`).
   - Pull back the diagonal class `δ` along `scaledGraph` (`exists_diagonal_local_terms` in `FixedPointFormula.lean:36-38`, using Grothendieck symbols `symbolClass` `[dg/g]`): locally at each coincidence `w`, the pullback equals `HasJacobianRatio(t, u, c, w) • pointClass d w`, where `HasJacobianRatio = det((t du - dc)(du - dc)⁻¹) = P(t) / P(1)`.
   - Globally, `map_scaledGraph_baseChange_cross` + `kunneth` expresses the pulled-back diagonal class in `HodgeH(W × 𝔸¹)` as a sum of cup-products of `(u_i)^*` (weighted by powers `t^h`) acting on Künneth components of `δ`.
3. **Bypassing Poincaré duality via `linearIndepOn_hodgeTateMap_pointClass` (`PointClass/LinearIndependence.lean`, `WoodsHole.lean`):**  
   Instead of a trace map, use Noether normalization (`exists_generic_chart`, `IsGenericChart`) to map `X` finitely onto `ℙ^d`, proving that the rational point classes `pointClass d w` map to linearly independent elements under `hodgeTateMap` (`linearIndepOn_hodgeTateMap_pointClass`). Using the polynomial Vandermonde-dual trick `Polynomial.exists_dual_eval_mul_eq_coeff_mul` to isolate the `t^h` coefficient of `P(t)`, the vanishing `∑ b_i λ_h(u_i^* ·) = 0` forces `sum_mul_hodgeTateMap_scaledGraph_eq_zero`, i.e. `IsNullFamily u b d h` (`ellAdicCohom.woods_hole`, `WoodsHole.lean:229-241`).

#### Step B3: Torus-tower `p`-adic and crystalline comparison without SGA 4 sites or `B_cris`
1. **`PadicTest`, `CrysTest`, and almost-perfectoid descent (`Descent/TestCategory.lean:253-272`, `AlmostDescent.lean:98-106, 215-220`):**  
   - `IsCell` (`TestCategory.lean`): a `p`-adically complete AIC valuation domain with `p ≠ 0`.  
   - `PadicTest`: nonempty product of cells equipped with a map from `O_C = New.Period.OC`.  
   - `CrysTest`: `p`-adically complete, `p`-torsion-free rings (`IsCompleteTorsionFree`).  
   - Because faithfully flat covers over `O_C` only split up to `𝔪^♭` (`MaxIdealFlat.exists_smul_eq`, `AlmostDescent.lean:98-106`), `AlmostDescent` puts `almostCoeff` (`𝔪^♭`-multiplication) directly into the *coefficient module* (`isSMulRegular_tensor_witt`, `MaxIdealTensor.isTorsionFree_of_isReduced`), making Čech `v`-descent **exact** for `exists_faithfullyFlat_padicTest` (`:215-220`) without almost-mathematics quotient categories!
2. **One-variable Torus Tower (`ToricTower.lean:89, 119, 166, 236, 252`):**  
   Instead of proving `ℤ_p^d`-Koszul quasi-isomorphisms directly for multidimensional toroidally compactified/framed charts, `ToricTower.lean` introduces `TimesBNat C := C × SingleObj (Multiplicative ℕ)` (`:89`), adjoining one endomorphism `T ↦ T^p` (i.e. extracting `p`-power roots along a single coordinate `T^{1/p^∞}`). The cohomology of passing from finite level to the `p^∞`-tower is governed by `shortExact_wangComplex` (`:166`):
   `0 → ℤ[Y × ℕ] → ℤ[Y × ℕ] → ℤ[Y] → 0`.  
   `IsLine.of_acyclic` (`:252`) inducts one variable at a time, letting `Duality/LineIntegration.lean` (`HasLineFormula`) and `Duality/GoodPairs.lean` (`isFiniteLerayHirsch_standard_etale`) push the comparison from `ℙ¹` and tori up to general standard étale opens (`finite_and_primitive_comparison`, `Primitive/ComparisonTheorem.lean:249-263`).
3. **Hodge–Tate Period Map (`HodgeTate/Map.lean:88-299`, `HodgeTate/GaloisWeight.lean`, `HodgeTate/PeriodMap.lean:182-185, 279-297`):**  
   - `HodgeTatePair` (`Map.lean:88`) pairs a `PadicTest` ring `S` with a square-zero thickening `pairAlg` (`B_{S,M} = B_S ×_T (T ⊕ M)`) via `toSqZero` and `toGeneric`.
   - `contractionCocycle` and `contractionPow` contract exterior forms `⋀^n M` against the Fontaine-like derivation coming from the `O_C`-structure.
   - Under Galois action (`GaloisWeight.lean`: `thickeningOver.mulMu_twist`, `HodgeTatePair.contractionPow_galTwist`), twisting `B_{S,M}` by `μ` multiplies `contractionPow` by the cyclotomic weight!
   - `exists_period_map` (`PeriodMap.lean:182-185`) builds `IsPadicPeriodMap` (`toTwistAlg`, `toTwistPoints`, `ActsAsOnFrobeniusFixed`), and `exists_hasHodgeTateWeight` (`:279-297`) delivers the exact Hodge–Tate decomposition / weight identification on `ellAdicCohom` consumed by `Eigenspace.lean`.
4. **Crystalline Comparison via `pdIdeal` and `σ = φ^{max N 3}` without `B_cris` (`Descent/TestCategory.lean`, `Crystalline/ComparisonMap.lean:119-280`, `CrystallineFrobenius.lean:224-236, 753-769`):**  
   - Rather than constructing the universal divided-power envelope `B_cris = A_cris[1/p]` and proving invariance under choice of PD structure, `TestCategory.lean` defines `pdIdeal := {x | ∀ n, (n! : ℤ) ∣ x^n}` (intrinsic divisibility of powers, no extra PD-structure data!), and `ComparisonMap.lean` constructs `CrysPeriodAlgebra` (`:119-123`) using the twisted Frobenius power `σ = φ^{max N 3}` (`exists_crysPeriodAlgebra`, `:148-155`) from `Amax` / `Bmax = B^+[1/μ]`. Raising `φ` to `max N 3` kills all `p`-torsion / `pdIdeal` denominators up to bound `N` automatically!
   - `HasCrysComparison` (`:280`) via `testToPdReduction` (`:238`) relates `ℤ_p`-cohomology over `PadicTest` to crystalline reduction over `CrysTest`.
   - Finally, `CrystallineFrobenius.lean` cancels high Frobenius powers locally (`exists_cancels_frobPow_locally`, `:224-236`, where `M` is the number of primes above the place), establishes `map_J_tensorAction_eq_pull` (`:550+`) and `sum_linearFrob_apply_eq_zero`, and exports `ellAdicCohom.isCrystalline_and_linearFrob_rel` (`:753-769`) to `Eigenspace.lean`.

#### Step B4: How Hodge–Tate jump conditions feed `New/Congruences/Lifting/` and `LocalLoss/`
Once `SeedRepresentation.lean` -> `AttachedRepresentations.lean` (`isLiftSetting_descentPair`) -> `RowsFromEigensystems.lean` (`abs_descentPair_weight_add_liftWeight_le`) supply a `p`-adic Galois representation `L.ρ` satisfying prescribed Hodge–Tate jump windows (`jumpSet`, `jumpMultiplicity`), `New/Congruences/Lifting/` and `LocalLoss/` prove that the crystalline Selmer dual defect is either zero or tightly bounded:

1. **Kisin exponent lattices & modulo-`p` Frobenius step (`Lib/PadicHodge/Kisin/{Modules,FrameTheorem}`, `New/Congruences/Lifting/ExponentLattices.lean`, `HodgeExpansion.lean`, `FewLowJumps.lean:86-162`):**  
   - On an unramified Kummer chart `k` (`k.E = k.z + p`, `k.e = 1`), the Frobenius lattice of a Kisin module `L` (built via `Lib/PadicHodge/Kisin/`) satisfies `zTau_dvd_sub_one_of_mul_eq_smul_E` and `theta_sub_one_dvd_pow_mul_theta_zTau` (`ExponentLattices.lean`).
   - Using `E^{p^a} ≡ φ^a(E) mod p`, `FewLowJumps.lean:156-162` (`exists_sub_mem_deepElements_of_smul_sub_mem`) pushes elements of `extensionLattice` across `negativeWindowDepth` / `fewLowJumpsDepth` (`:86-94`) whenever jumps avoid the forbidden intermediate window `(η, b_i)` (with gap condition `NoMultipleNear p (6 (a + η + W)) (b i)`).
2. **Cup-product coboundary via `IsSafePath` & cokernel killing (`CupProductBound.lean:1130-1234`, `FewLowJumps.lean:960-1042`):**  
   - `PairingSide` pairs an extension lattice `S` with its dual `T` into `tateDualSide`. A cocycle cup product `(c, d) ↦ c ∪ d` is a continuous coboundary (`P.IsScaledCupCoboundary 0 c d`) if we can choose compatible lattice lifts `(x_i, x'_i)` across all letters `i : Letter` forming a safe walk (`isScaledCupCoboundary_of_stops_at_all_letters`), provided `tateDualSide` has trivial cokernel modulo a bounded power of `E` (`KillsCokernel i 0 a`).
   - `CupProductBound.lean:1146-1175` (`killsCokernel_of_isUnramified`) uses Legendre's formula `(p-1) v_p(b!) ≤ b` to show that when every jump `u ≤ (p - 3)(s + t)` and `p ≥ 5`, `p^s E^t` kills the cokernel (`KillsCokernel i s t`); for ramified charts with `8 e ≤ p^(J+1)`, `killsCokernel_zero_of_jumps_le` (`:1211-1233`) gives an explicit `p^κ` annihilator.
   - `FewLowJumps.lean:960-974` (`exists_relLength_le_and_isScaledCupCoboundary`) combines both: inside `S.paramLattice`, there is a submodule `V` of `ℤ_p`-relative length at most `∑ i, (n i * (8 * a + 1) + r i * (3 * (W + 1)))` on which *every* cup product with the opposite-window side `T` vanishes (`IsScaledCupCoboundary 0 c d`).
3. **Exact dual-defect & cup-exponent bounds (`CupOrthogonalityBounds.lean:226-237, 343-412, 509-516`, `LocalLoss/CrystallineCocycles.lean:86-92, 251-265, 583-597`):**  
   `CupOrthogonalityBounds.lean` translates this directly into Bloch–Kato cohomology bounds:
   - `crysCocycles_le_cupOrthogonal_of_no_small_neg_jump` (`:226-237`): if `S` has no small negative jump and `b_i + W + η ≤ (p - 3) a` (`p ≥ 5`), **all** crystalline cocycles lie in `cupOrthogonal`, i.e., **zero local loss**!
   - `dualDefect_eq_zero_and_dualDefect_le` (`:343-359`): `dualDefect` is `0` when all jumps avoid the negative window, and in general is bounded linearly in the low-window count `m` and total rank `rank L`: `≤ f * (m * (8 * a + 1) + 3 * rank L * (W + 1)) * len(O/p)`.
   - `hasCupExponent_any_pattern` (`:371-380`), `hasCupExponent_sparse_thick` (`:397-412`), and `hasCupExponent_of_isTameType` (`:509-516`) turn these length bounds into explicit `p^C` annihilators (`HasCupExponent`) of the cup-pairing cokernel (in tame, general, and sparse-thick jump configurations).
   - Finally, `LocalLoss/CrystallineCocycles.lean` combines the Bloch–Kato rank identity `finrank_crysCocycles_eq_add_neg_jumps` (`:86-92`) with `CrystallineSizes` (`:251-265`) to export `normLength_dualDefect_le_of_crystallineSizes` (`:583-597`), bounding the normalized length of `dualDefect` by `3200 * rank L * K m + 33 * μ * v` (for `ℓ ≥ 7`), directly feeding the Taylor–Wiles patching / congruence-lifting denominator bounds!

---

## 3. Classical Barriers Bypassed & Tight Constants

### 3.1 Summary of bypassed textbook machinery

| Classical Machinery Skipped | Custom Bypass in `rh_grh` | Core Lean Witness (`src/...:<line>`) |
| :--- | :--- | :--- |
| Kottwitz PEL moduli representability | Zariski closure `ReducedClosure` of complex theta points in `∏ ℙ^{#T-1}` + valuation-arc good reduction + flat closure + rigidity | `ThetaClosure` (`UniversalFamily.lean:239-241`), `nonempty_universalFamily` (`:511-513`), `eq_and_comp_toFamily_eq_of_hom` (`ThetaFamilyRigidity.lean:30-32`) |
| Mumford's quartic theta equations for flatness | Dickson stabilization of monomial ideals `IsCutDegree` + `IsFlatClosure` of cut-out fibers | `FlatClosure.lean:91-93` (`IsCutDegree`), `FamilyFromPoints.lean:1052-1069` (`exists_thetaFamily_of_points`) |
| Dieudonné / Grothendieck–Messing smoothness of Shimura models | Characteristic-`0` holomorphic ball immersion + characteristic-`q` Drinfeld `placeTorsion` parameter `τ^N = 0` semilinearity (`i = q^j`) | `isHolomorphicImmersionAt_of_holomorphicAt` (`BallImmersion.lean:116-123`), `finrank_le_of_placeTorsion` (`TangentCount.lean:366-380`), `finrank_tangent_le_card_index_sub_one` (`TangentBound.lean:746-755`) |
| SGA 4 étale / pro-étale topoi & hypercovers | Presheaf `Abelian.Ext` on `IsTest` (AIC reduced idempotent-splitting) and `PadicTest` (products of complete AIC valuation domains) | `H` (`Etale/Basic.lean:105-146`), `IsCell` / `PadicTest` (`TestCategory.lean:253-272`) |
| Full Grothendieck–Verdier duality & trace map in Woods Hole | Half-Woods Hole: Noether normalization to `ℙ^d` gives linear independence of point classes; polynomial Vandermonde extraction isolates `t^h` | `linearIndepOn_hodgeTateMap_pointClass` (`PointClass/LinearIndependence.lean`), `Polynomial.exists_dual_eval_mul_eq_coeff_mul`, `ellAdicCohom.woods_hole` (`WoodsHole.lean:229-241`) |
| Fontaine's `B_cris` + chosen divided-power envelopes `A_cris` | `Bmax = B^+[1/μ]`, intrinsic `pdIdeal = {x \| ∀ n, n! ∣ x^n}`, and twisted Frobenius `σ = φ^{max N 3}` | `pdIdeal` (`TestCategory.lean`), `exists_crysPeriodAlgebra` (`ComparisonMap.lean:148-155`), `ellAdicCohom.isCrystalline_and_linearFrob_rel` (`CrystallineFrobenius.lean:753-769`) |
| Multidimensional `ℤ_p^d`-Koszul complexes for toric charts | One-variable `TimesBNat` (`C × Bℕ`) and exact `shortExact_wangComplex` inducted variable-by-variable | `TimesBNat` (`ToricTower.lean:89`), `shortExact_wangComplex` (`:166`), `IsLine.of_acyclic` (`:252`) |
| Almost-mathematics quotient category `(Mod / 𝔪^♭)` | Place `almostCoeff` (`𝔪^♭`-multiplication) inside the coefficient functor itself so Čech `v`-descent is strictly exact | `MaxIdealFlat.exists_smul_eq`, `exists_faithfullyFlat_padicTest` (`AlmostDescent.lean:98-106, 215-220`) |

### 3.2 Tight numerical & asymptotic constants

1. **`[HasPrimitiveRoot5040 E]` (`5040 = 7!`, `PELDataExistence.lean:120`):** Needed to construct `PEL` parameters `(β, ξ, lagrangian)` with odd `dualTorsion`, separation of infinite embeddings, and `three_le_paddedNorm : 3 ≤ paddedNorm` (`PELThetaTori.lean:104`).
2. **Gauss-sum 4th power (`sum_conj_pow_four_eq_sum_pow_four`, `GaussSums.lean:281-284`):** Exact exponent `4`, driven directly by Lagrange's four-square identity (`N^2 - 1 = a₁² + a₂² + a₃² + a₄²`); exponent `2` fails in general because of fourth-root-of-unity signs in quadratic Gauss sums.
3. **Drinfeld tangent dimension bound `≤ Fintype.card D.Index - 1` (`TangentCount.lean:366-380`, `TangentBound.lean:746-755`):** **Sharp** — equals the exact relative dimension `n - 1` of the unitary Shimura variety of signature `(1, n-1)`, matching the holomorphic ball immersion lower bound.
4. **Rank-gluing Frobenius-relation bound `(n + 1)^2` (`HasNoSmallRelations`, `SeedRepresentation.lean:47-48`):** Tight linear-algebraic bound from Chebotarev / representation dimension `(n+1)^2` needed to distinguish virtual characters and glue per-embedding representations into exact rank `a`.
5. **Crystalline twisted Frobenius power `σ = φ^{max N 3}` (`ComparisonMap.lean:148-155`):** The minimum threshold `3` (rather than `1` or `2`) absorbs `p`-adic convergence/denominator offsets in `pdIdeal` when `N` is small (`N < 3`).
6. **Unramified cokernel-killing threshold `e * ω ≤ p - 2` (`killsCokernel_zero_zero_of_small_jumps`, `CupProductBound.lean:1131-1139`) & `b_i + W + η ≤ (p - 3) * a` with `p ≥ 5` (`killsCokernel_of_isUnramified` `:1146-1148`, `FewLowJumps.lean:960-965`):**
   - Here `p - 2` and `p - 3` are **tight** from Legendre's formula `(p - 1) v_p(b!) ≤ b` (`:1154`): setting `b + v_p(b!) ≤ s + t` requires `(1 + 1/(p-1)) b ≈ p/(p-1) · e·ω/(p-1)`, leaving room only for `≤ (p - 3)(s + t)` when `p ≥ 5`!
   - The gap constant `6 * (a + η + W) < b_i` (`FewLowJumps.lean:964`) and `NoMultipleNear p (6 (a + η + W)) (b i)` (`:965`) are tuned so `p`-multiples and window widths cannot overlap during the `E^{p^a} ≡ φ^a(E) mod p` walk across letters.
   - Ramified cokernel condition `8 * k.e ≤ p ^ (J + 1)` (`CupProductBound.lean:1214`) feeds `killsCokernel_zero_of_jumps_le` (`:1211-1217`).
7. **Bloch–Kato cup-exponent and `dualDefect` bounds (`CupOrthogonalityBounds.lean`, `LocalLoss/CrystallineCocycles.lean`):**
   - `dualDefect_eq_zero_and_dualDefect_le` (`:343-359`): `≤ f * (m * (8 * a + 1) + 3 * rank L * (W + 1)) * len(O/p)` (linear in `m`, `a`, `rank L`, `W`).
   - `hasCupExponent_any_pattern` (`:371-380`): `p ^ (312 * (5 * K + ⌊log_p(2 * (b + M))⌋) + 13)`.
   - `hasCupExponent_sparse_thick` (`:397-412`): `p ^ (156 * (δ + (J + 1) * M) + 13)`.
   - `hasCupExponent_of_isTameType` (`:509-516`): `p ^ (3 * r^2 * (N + 1)^2 + 8 * η + 2 * W)` for `p > b + η + max η W + r^2 * (N + 1)^2 + 2`.
   - `normLength_dualDefect_le_of_crystallineSizes` (`CrystallineCocycles.lean:251-265, 583-597`): `3200 * rank L * K m + 33 * μ * v` under `CrystallineSizes` (using threshold `99 * ... ≤ ...`) and `ℓ ≥ 7`. *(Note: constants like `312`, `156`, `3200`, `99` are convenient safe linear multiples rather than information-theoretic minima, whereas `(p-2)`, `(p-3)`, `p ≥ 5`, `ℓ ≥ 7` reflect sharp Legendre/Frobenius thresholds.)*

---

## 4. Community & Audit Takeaways

### 4.1 First questions a sceptical number theorist would ask — and exact Lean answers

1. **Q: "Wait — you never proved that a Kottwitz PEL moduli functor is representable! How do you know `ThetaClosure` doesn't accidentally omit points, collapse fibers, or fail to be smooth at residual characteristics?"**  
   - **A:** Every point of `ThetaClosure R y` (`UniversalFamily.lean:239-241`) lies over a valuation arc coming from a dense set of complex theta points at a good prime (`ThetaClosure.exists_arc_isGoodAt`, `:286-292`). Gauss-sum 4th-power reality (`sum_conj_pow_four_eq_sum_pow_four`, `GaussSums.lean:281-284`) forces good reduction of the theta norm (`ThetaTorus.hasGoodReduction_and_val_card_eq_one`, `MultiplicativeNorm.lean:943-949`), so `HasPeakCharts` holds everywhere (`hasPeakCharts_of_hasGoodReduction`). Monomial degree stabilization (`eventually_isCutDegree`, `FlatClosure.lean`) then constructs the flat total space `A` (`exists_thetaFamily_of_points`, `FamilyFromPoints.lean:1052-1069`), rigidity (`eq_and_comp_toFamily_eq_of_hom`, `ThetaFamilyRigidity.lean`) acts as a substitute for fine moduli uniqueness, and smoothness of exact relative dimension `n - 1` comes from `isHolomorphicImmersionAt_of_holomorphicAt` (`≥ n - 1`) + `finrank_tangent_le_card_index_sub_one` (`≤ n - 1`, `TangentBound.lean:746-755`).

2. **Q: "Why does `Abelian.Ext` on presheaves over `TestRing` agree with genuine étale/crystalline cohomology, and where are the site axioms hidden?"**  
   - **A:** They aren't hidden — `IsTest` (`Etale/Basic.lean:52-54`) restricts test objects to *reduced, absolutely integrally closed, idempotent-splitting* rings (`PadicTest` uses products of complete AIC valuation domains `IsCell`, `TestCategory.lean:253-272`). Because AIC rings have no nontrivial finite étale covers, presheaf `Ext(ℤ[X], F)` agrees with sheaf hypercohomology. Proper base change (`IsProperOver.proper_base_change`, `Theorem.lean:642-645`) and smooth base change (`isTestCohomEquiv_baseChangeTransition`, `SmoothBaseChange.lean:271-275`) are proved *directly* for this functor without importing Grothendieck topoi.

3. **Q: "Can you really get Hodge–Tate weights and Woods Hole without Poincaré duality / trace maps, and crystallinity without `B_cris`?"**  
   - **A:** Yes, because `Eigenspace.lean` never needs the full Grothendieck–Lefschetz trace formula: it only needs the **vanishing implication** (`IsNullHecke → IsNullFamily`, `ellAdicCohom.woods_hole` at `WoodsHole.lean:229-241`), proved by pulling back the diagonal on a `t`-twisted square-zero graph (`exists_diagonal_local_terms`, `FixedPointFormula.lean`) and using Noether normalization (`linearIndepOn_hodgeTateMap_pointClass`) instead of a trace pairing. Likewise, `CrysPeriodAlgebra` (`ComparisonMap.lean:119-155`) uses `pdIdeal := {x | ∀ n, n! ∣ x^n}` (no chosen PD structure) and `σ = φ^{max N 3}` inside `Bmax`, which suffices for `ellAdicCohom.isCrystalline_and_linearFrob_rel` (`CrystallineFrobenius.lean:753-769`).

4. **Q: "Do the Hodge–Tate jump bounds in `New/Congruences/Lifting/` actually depend on `Lib/PadicComparison`'s comparison theorems?"**  
   - **A:** Architecturally, `New/Congruences/Lifting/` uses `Lib/PadicComparison/Descent/TestCategory.lean` only for `O_C`, `O^♭`, `A_inf` types, while its jump-window cup-orthogonality engine (`FewLowJumps.lean`, `CupOrthogonalityBounds.lean`) builds on `Lib/PadicHodge/Kisin/` (`FrameTheorem`, `Modules`, `PeriodMatrixBasis`). `Lib/PadicComparison/`'s *comparison* theorems (`exists_hasHodgeTateWeight`, `isCrystalline_and_linearFrob_rel`) enter earlier — into `Lib/Shimura/Eigenspace.lean` (`Model.exists_galois_rep`) -> `SeedRepresentation.lean` (`exists_rep_of_cuspidal_type`) -> `AttachedRepresentations.lean` / `RowsFromEigensystems.lean`, which supply the Galois representations and their jump-window hypotheses to `LocalLoss/` and `Lifting/`.

### 4.2 Extraction Opportunities (`TauCeti` & `ShortGRH`)

`TauCeti` is already an external Lean utility library imported across these pillars (for example `TauCeti.RingTheory.MvPolynomial.{Finrank,Homogeneous,RegularSequence}`, `TauCeti.RingTheory.Perfectoid.Integral.Tilt`, `TauCeti.RingTheory.TrivSqZeroExt`, `TauCeti.Analysis.Normed.Ring.Ultra`, `TauCeti.LinearAlgebra.Trace.Nilpotent`). Four clean extraction targets stand out:

1. **Pure Presheaf Cohomology Core -> `TauCeti`:**  
   `Lib/Cohomology/Etale/Basic.lean`, `ProperBaseChange/{PlaceSpace,Theorem}.lean`, `SmoothBaseChange.lean`, `ProjectiveLine/{ConstantLineFormula,TiltedLineFormula,PerfectLine}.lean`, and `PadicComparison/ToricTower.lean` (`TimesBNat`, `shortExact_wangComplex`, `IsLine.of_acyclic`) contain **zero** Shimura/GRH-specific mathematics. Extracting `TestRing` + `Abelian.Ext` + valuative proper base change + `ℙ¹` / one-variable `TimesBNat` Leray–Hirsch into `TauCeti.AlgebraicGeometry.Cohomology` creates a standalone, topos-free étale cohomology toolkit.
2. **Dickson Monomial Cut-Out Flatness -> `TauCeti`:**  
   `Lib/Shimura/ThetaModuli/FlatClosure.lean` already imports `TauCeti.RingTheory.MvPolynomial.Finrank`, and its core (`IsCutDegree`, `eventually_isCutDegree`, `eq_map_and_flat_of_isCutOut`, `exists_isFlatClosure`) is pure commutative algebra about flat families of ideals cut out by points over reduced bases.
3. **Half-Woods Hole / Diagonal Fixed-Point Pullback -> `TauCeti` or `ShortGRH`:**  
   `Lib/Cohomology/Hodge/{Site,FixedPointFormula}.lean`, `PointClass/LinearIndependence.lean`, and `WoodsHole.lean` prove a general characteristic-0 Jacobian fixed-point vanishing theorem for `Ext`-Hodge cohomology with zero automorphic dependencies — reusable verbatim in any `ShortGRH` or trace-formula formalization.
4. **Lean Dependency Cleanup in `New/Congruences/`:**  
   Remove the unused `import Lib.PadicComparison.ToricTower` lines in `src/New/Congruences/GaloisRepresentations/RowsAndColumnsFromLabels.lean:11` and `src/New/Congruences/FirstOrder/DenominatorBound.lean:15` (neither file references `TimesBNat`, `Wang`, `Koszul`, or `IsLine`), cleanly decoupling first-order/label files from the `ToricTower` proof tree.
