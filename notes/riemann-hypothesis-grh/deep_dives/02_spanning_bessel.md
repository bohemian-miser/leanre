# Deep Mathematical Dive: `src/New/Spanning/` (`SecondMoment/`, `MainTerm/`, `RemainingTerms/`, `Bessel/`, `Frames/`, `Unfolding/`, `Multiplicities/`)

This report dissects the quantitative spanning engine in `src/New/Spanning/` (58,803 lines across 80 files on `upstream/main` `grh`). Its headline export is **Theorem B** (`New.Data.enough_forms` in `src/New/Reduction/ShortAndEnough.lean:399-404`), driven by the second-moment bound **`1 + 9 b⁻⁴`** (`New.Data.sum_hilbertSchmidtNorm_scaledPoincare_sq_le` in `src/New/Spanning/SecondMoment/SpanningTheorem.lean:274-285`) and the quantitative linear-algebraic spread extraction (`New.isSpread_of_second_moment`, `New.IsSpread.exists_few_le_finrank_iSup_range` in `src/New/Spanning/SecondMoment/FewTranslates.lean:333-538`).

---

## 1. Engine Architecture & Entry/Exit Interface

### 1.1 Subdirectory Layout & Conceptual Role

The `src/New/Spanning/` pillar proves that relatively few finite-group translates of ramified Poincaré series built from archimedean discrete-series Bessel functions span at least a $(1 - 4/b^2)$ fraction of the "good" automorphic forms $D.\mathrm{goodForms}(Y_0)$ of dimension $d_T = D.\mathrm{targetDim}$.

| Subdirectory | Role in the Mathematical Pipeline | Peak Definitions / Theorems |
|---|---|---|
| `Bessel/` | Constructs archimedean discrete-series Bessel systems `New.BesselSystem`, proves the left-convolution reproducing Schur bound (`HasSchurBound`), and proves the open-cell $L^2$-contraction via the Sobolev cube inequality (`lintegral_gramSection_integral_le`, `exists_isOpenCellBound`). Packages `New.Data.filling`. | `New.Data.filling` (`Bessel/FillingData.lean:478`), `exists_isOpenCellBound` (`Bessel/OpenCellBound.lean:921`) |
| `Unfolding/` | Defines `New.Filling` (`Setup.lean:71`) and `IsAdmissible` (`Setup.lean:530`); unfolds Petersson products of Poincaré series into block sums $\sum_\gamma \text{amplitude}$ (`petersson_poincare`); proves `IsAmplitudeBlocks` (`HasAmplitudeBlocks`) and bootstraps the subgroup recurrence to lock the total second moment to $(1 + 9 b^{-4})\mathcal{D}_{\mathrm{main}}$ (`sum_secondMoment_le`). | `petersson_poincare` (`Unfolding/PoincareSeries.lean:711`), `sum_secondMoment_le` (`Unfolding/MomentBounds.lean:452`) |
| `Frames/` | Local-place harmonic analysis at both finite places (`FixedLines`, `FiniteDepth`, `FiniteShells`) and $\mathbb{C}$ (`RealBandLimits`, `RealShells`), plus quadric Plancherel (`QuadricPlancherel`), Siegel-style coarea disintegration onto spheres (`TopFloor`, `TopCorrelation`), and wave-transform descent across hyperbolic floors. | `exists_hasLocalBounds_of_isCutBessel` (`Frames/RealBandLimits.lean:693`), `sum_headSumNormSq_le_fiberPairing` (`Frames/TopFloor.lean:239`), `correlation_plancherel` (`Frames/QuadricPlancherel.lean:202`) |
| `MainTerm/` | Evaluates the open-cell main term $\mathcal{D}_{\mathrm{main}}$ (`linkSecondMoment_isOpenElement_le`) by peeling hyperbolic floors $0, \dots, \varrho$ via Poisson summation (`GlobalSieve.sieve`) + finite/archimedean local sieve systems (`FiniteSieveSystem`), landing on the Siegel sphere integral (`SiegelTopBound.siegel_sum_le_lintegral_sphere`), with exact constant **$1 + O(b^{-4})$**; also bounds "bad" residue-field polynomial types (`BadTypes.re_coeff_one_sub_sum_tupleIdem_le`). | `linkSecondMoment_isOpenElement_le` (`MainTerm/EnergyEstimate.lean:640`), `sieve_constant_le` (`MainTerm/EnergyEstimate.lean:282`), `bad_types_rare` via `BadTypes.lean:217` |
| `RemainingTerms/` | Controls all non-main rational terms $\gamma \in \Gamma^*$ (`amplitudeSum .cut`). Uses bordered frame minors (`BorderedDeterminant`), adelic Siegel lemma (`SiegelLemma`), Ostrowski–Taussky & congruence splitting (`Gain.pairDiscriminant_sq_le`), submodule zeta convergence (`Count.sum_pairDiscriminant_inv_le`), and double-coset $U_c^0 \gamma U_{c'}^0$ Eichler shifts (`SchurOrbit`) to crush the tail below $b^{-15}\sqrt{\mathcal{D}_{\mathrm{id}}}$. | `pairDiscriminant_sq_le` (`RemainingTerms/Gain.lean:828`), `sum_pairDiscriminant_inv_le` (`RemainingTerms/Count.lean:194`), `secondMoment_remainingTerms_le` (`RemainingTerms/Sum.lean:688`) |
| `SecondMoment/` | Combines Fourier positive type on $M_{n \times n}(\mathbb{F}_q)$ (`PositiveType.card_mul_sum_det_eq_zero_le`), subgroup bootstrapping, and Hilbert–Schmidt near-isometry geometry (`FewTranslates.isSpread_of_second_moment`, `exists_few_le_finrank_iSup_range`) into `isSpread_goodPoincare`. | `isSpread_goodPoincare` (`SecondMoment/SpanningTheorem.lean:343`), `isSpread_of_second_moment` (`SecondMoment/FewTranslates.lean:333`) |
| `Multiplicities/` | Proves equality of good-form Hecke eigensystem multiplicities (hence equal dimension $d_T$) across all inner forms $Y_0, W_1, \dots, W_m$ (`targetDim_eq_finrank_goodForms_spaceW`). | `finrank_goodForms_inf_eigenPart_eq` (`Multiplicities/EqualMultiplicities.lean:385`), `targetDim_eq_finrank_goodForms_spaceW` (`EqualMultiplicities.lean:419`) |

### 1.2 Exact Exported Interface & All External Callers in `src/`

A repository-wide search for `New.Spanning` outside `src/New/Spanning/` shows **exactly six external call sites**:

1. **`src/New/Reduction/ShortAndEnough.lean:6`** (`public import New.Spanning.SecondMoment.SpanningTheorem`)
   - Consumes `D.goodPoincare`, `D.targetDim`, `D.chosenGL`, `D.isSpread_goodPoincare` (`SpanningTheorem.lean:343`), `D.goodPoincare_apply` (relating `goodPoincare s` to `poincare` translated by `s`), and `targetDim_le_card_mul_besselDegree_mul_mass` (`SpanningTheorem.lean:102-111`) to prove:
     - `New.Data.exists_le_finrank_iSup_range_normalizedPoincare` (`ShortAndEnough.lean:361-392`)
     - **Theorem B** (`New.Data.enough_forms` at `ShortAndEnough.lean:399-404`):
       ```lean
       theorem enough_forms :
           0 < D.targetDim ∧
           ∃ t : Finset D.chosenGL,
             #t * finrank ℂ D.ramifiedSourceForms ≤ 5 * D.targetDim * log (1 + 2 * D.b ^ 2) ∧
             (1 - 4 / D.b ^ 2) * D.targetDim ≤ finrank ℂ ↥(⨆ s ∈ t, (D.normalizedPoincare s).range)
       ```
2. **`src/New/OneLift/ComparisonOperator/GluingMaps.lean:14-15`** (`import New.Spanning.Multiplicities.EqualMultiplicities` and `SpanningTheorem`)
   - Uses `D.targetDim_eq_finrank_goodForms_spaceW` (`EqualMultiplicities.lean:419`) and `D.finrank_targetForms_ne_zero` (`GluingMaps.lean:1080`) to prove `twistFactor_ne_zero` (`GluingMaps.lean:1077`).
3. **`src/New/Determinant/Chain/NormOfChain.lean:5`** (`public import New.Spanning.Multiplicities.EqualMultiplicities`)
   - Uses `D.targetDim_eq_finrank_goodForms_spaceW` (`NormOfChain.lean:140`) to factor the determinant of the theta lift `goodLift` on `W_j` into the determinant of `rallisOnGood` on the target forms `Y_0`.
4. **`src/New/Determinant/Norms/AdjointThetaLift.lean:4`** (`public import New.Spanning.Multiplicities.HeckeEigensystems`)
   - Uses `New.Data.principalForms`, `New.Data.goodForms`, `New.Data.heckeAlgebra`, `New.Data.heckeOnGood` (`HeckeEigensystems.lean`).
5. **`src/New/UpperBound/Size/ArchimedeanSize.lean:6`** (`public import New.Spanning.Unfolding.FillingAdmissible`)
   - Uses `D.goodProjTranslate` (`FillingAdmissible.lean:108-112`) for `lowerChain_goodProjTranslate_apply`.
6. **`src/New/UpperBound/Size/ClassCount.lean:5`** (`import New.Spanning.RemainingTerms.Box`)
   - Reuses the short-basis matrix norm / box counting lemmas from `RemainingTerms/Box.lean` to prove `card_stdClasses_le`.

---

## 2. Step-by-Step Mathematical Walkthrough

The logical proof chain can be read from bottom to top as five interlocking stages:

```text
BesselSystem + Discrete Series Schur (Bessel/) + Filling.IsAdmissible (FillingData / FillingAdmissible)
        │
        ▼
Unfold Petersson Pairing ⟨ρ(s) P φ, P ψ⟩  ──► Block sum ∑_{(c,s,c')} amplitudeSum(Γ)   (Unfolding/PoincareSeries)
        │
        ├──► Bessel subgroup R₀ ────────► r_ψ(s) unitary, error off R₀ ≤ b⁻¹² 𝒟_id     (Unfolding/SquareExpansion)
        │        └─► + BadTypes (p₀, p₁ primitive polys) ─► IsNearIsometry(e₀ P, 5b⁻⁴)  (SpanningTheorem.isNearIsometry_e₀_comp_scaledPoincare)
        │
        ├──► MainTerm (Open elements, s ∈ 𝖦 \ cosets):
        │        Floor-by-floor sieve i = 0..ϱ (QuadricPlancherel + FixedLines + RealBandLimits)
        │        + Siegel sphere top floor i = ϱ+1 (SiegelTopBound + TopFloor)
        │        ══► linkSecondMoment_isOpenElement_le ≤ (1 + b⁻⁴) · b^(-6k|#Sg|) · 𝒟_main · ν²  (MainTerm/EnergyEstimate)
        │
        ├──► RemainingTerms (Cut tail Γ* = remainingTerms):
        │        OpenCell Sobolev+Schur bound (Bessel/) + Eichler orbit shifts (SchurOrbit)
        │        + Bordered determinant / Ostrowski-Taussky gain (RemainingTerms/Gain)
        │        + Adelic Siegel lemma + Submodule zeta convergence (SiegelLemma + Count)
        │        ══► secondMoment_remainingTerms_le ≤ b⁻³⁰ 𝒟_id                            (RemainingTerms/Sum)
        │
        ├──► Subgroup Bootstrapping (Unfolding/MomentBounds.sum_secondMoment_le):
        │        Maximize b^(6k|places|) · fixerMass over fixed places & vectors
        │        Non-open minor=0 cosets ≤ b⁻⁴ · fixerMass via PositiveType Fourier bound (PositiveType)
        │        M ≤ (1 + 4 b⁻⁴) C + b⁻⁴ M  ══►  M ≤ (1 + 9 b⁻⁴) 𝒟_main                   (SpanningTheorem.sum_hilbertSchmidtNorm_scaledPoincare_sq_le)
        │
        ▼
FewTranslates (isSpread_of_second_moment ─► IsSpread ─► exists_few_le_finrank_iSup_range)
        ══► #t · dim(ramifiedSourceForms) ≤ 5 d_T log(1 + 2b²) and rank(⋃_{s∈t} range(P̃_s)) ≥ (1 - 4/b²) d_T  (ShortAndEnough.enough_forms)
```

---

### 2.1 Geometric Setup & Unfolding of the Poincaré Series (`Unfolding/`, `Bessel/FillingData.lean`)

Let $E$ be the CM field with $f = \mathrm{numInfPlaces}(E)$ complex embeddings $\Phi(v) : E \hookrightarrow \mathbb{C}$, different generator $\varpi = \delta_E$, rational split prime $N = \pi\bar\pi \ge 5$, and two distinct auxiliary primes $p_0, p_1$ (`levelPrime : Fin 2 → ℕ`) split in $E$ with disjoint sets of chosen places `chosenPlaces i` of cardinality $f$ and norm $p_i$ containing no conjugate pairs (`Filling` in `src/New/Spanning/Unfolding/Setup.lean:71-155`; constructed in `D.filling` at `src/New/Spanning/Bessel/FillingData.lean:478-538`). Let $M = p_0 p_1$.

1. **The Split Hermitian Space (`Setup.lean:18-49`, `PoincareSeries.lean`):**
   We fix a `Shape` 𝔰 with $\varrho$ hyperbolic planes, a definite hermitian space $X_0$ of dimension $k = |\kappa|$ with diagonal gram matrix $1$, and one anisotropic vector $z$ of norm $h(z,z) = -N$. In the Witt basis (hyperbolic vectors $e_0,\dots,e_{\varrho-1}$, definite basis $X_0$, negative vector $z$, dual isotropic vectors $e^*_{\varrho-1},\dots,e^*_0$), the rational unitary group $S.G(E)$ preserves `ratGram`. The ambient global target space $Y_0 = D.\mathrm{spaceY}\,0$ fits `D.filling` (`D.filling_fits`, `FillingAdmissible.lean:64-97`), with principal congruence subgroup `principalLevel` $K(M) \le K = \mathrm{latticeStabilizer}$ reducing modulo the $2f$ chosen places to $1 \in \mathrm{ResidueGL} = \prod_{i,w} GL_r(\mathbb{F}_{p_i})$, where $r = 2\varrho + k + 1$ (`Setup.lean:210-240`).

2. **Archimedean Scaling & Bessel System (`Setup.lean:252-298`, `Bessel/FillingData.lean:104-435`):**
   At each infinite place $v$, conjugation by the real diagonal scaling `basisScale` turns $Y_0(\mathbb{R}_v)$ into the standardized complex unitary group $\mathfrak{s}.G_1$ with frame $f_0,\dots,f_\varrho$ (`Setup.lean:724-730`). At each $v$, `exists_besselSystem` (`FillingData.lean:356-435`) selects a `BesselSystem 𝔰 D.b f` (`Basic.lean`):
   - An irreducible representation `rep` of $U(\kappa) = U(X_0)$ on $\mathbb{C}^I$ and a continuous discrete-series Bessel vector $W = \mathrm{besselFn}\ \mathrm{.full} : \mathfrak{s}.G_1 \to \mathbb{C}^I$ transformed on the left under the Bessel subgroup $S_{\mathrm{Bes}} = \mathfrak{U} \rtimes U(\kappa)$ (`besselS`), with normalized $L^2(\mathfrak{U}\backslash G_1)$-norm $\|W\|_2^2 = |I|$ (`FillingData.lean:408`).
   - Its smooth cutoff $W^\flat = \mathrm{besselCut}(b, W) = \mathrm{besselFn}\ \mathrm{.cut}$ (`FillingData.lean:402, 428`), supported on `besselLength x ≤ b` (bounded modulo $S_{\mathrm{Bes}}$).
   - A formal degree `deg` $> 0$, with global product `besselDegree` $= \prod_v \deg_v$ (`Setup.lean:499`).

3. **Unfolding `petersson_poincare` (`Unfolding/PoincareSeries.lean:537-772`, `SeriesPeriod.lean:705-750`):**
   Source forms on $X_0$ of level `sourceLevel` $= K(M) \cap U(X_0)$ (`levelX_zero_eq_comap`, `FillingData.lean:551-562`) are evaluated at genus class representatives $h_c$ (`Classes`) in the Bessel coordinates $\mathbb{C}^{S.\mathrm{Classes} \times S.\mathrm{BesselCoord}}$ (`sourceFormCoords`, `FillingAdmissible.lean:101-104`). Pushing this finite-dimensional vector space (of dimension $D_X = S.\mathrm{sourceDim} = |\mathrm{Classes}| \cdot |\mathrm{BesselCoord}|$, `Setup.lean:496`) forward by averaging $W^\flat_{\text{glob}}$ over $\Gamma \backslash G_\infty$ weighted by unipotent-quotient cutoffs $\beta_c = S.\mathrm{classCutoff}\,c$ (`CutoffIntegral.lean:338, 741`) defines `X.poincareMap` (`PoincareSeries.lean:537`). By `poincare_eq_poincareMap_comp` (`SeriesPeriod.lean:748-750`), this coincides with `D.poincare`, the Riesz dual of the Bessel period on $Y_0$.

   Folding the Petersson inner product against a translate $k \in \mathrm{stdLevel}$ whose reduction in `ResidueGL` is $s$ gives `petersson_poincare` (`PoincareSeries.lean:711-722`):
   $$\langle k \cdot \mathcal{P} a', \mathcal{P} a \rangle = \mathrm{vol}(\mathrm{stdPrincipalLevel}) \cdot \text{amplitudeSum}(\mathrm{.full}, \mathrm{univ}, c, s, c')_{i, i'},$$
   where for a set $T \subseteq S.G(E)$ of rational elements, the $(c, s, c')$ matrix block is (`Setup.lean:698-715`, `PoincareSeries.lean:688-693`):
   $$\mathrm{amplitudeSum}(\mathrm{side}, T, c, s, c') = \sum_{\gamma \in T \cap \mathrm{termsOver}(c,s,c')} \int_{G_\infty} \beta_c(y) \beta_{c'}(\gamma^{-1} y) \, W(y) \otimes \overline{W(\gamma^{-1} y)} \, dy.$$
   By `lintegral_classCutoff_eq_unipotentCovolume` (`CutoffIntegral.lean:741`), $\int_{U_c \backslash G_\infty} \beta_c = V_{\mathfrak{U}} = S.\mathrm{unipotentCovolume}$ (`Setup.lean:289`), independent of $c$. Normalizing $P = \mathrm{scaledPoincare}$ by `poincareScale` (`SpanningTheorem.lean:148-158`) cancels $\mathrm{vol}(\mathrm{stdPrincipalLevel})$ and $V_{\mathfrak{U}}$, so every operator block of $P^* \rho(s) P$ at $(c,c')$ is literally $V_{\mathfrak{U}}^{-1}\,\mathrm{amplitudeSum}(.full, \mathrm{univ}, c, s, c')$ (`hasAmplitudeBlocks_scaledPoincare`, `SpanningTheorem.lean:172-182`).

---

### 2.2 Near-Isometry & Positive-Type Subgroup Bootstrapping to $1 + 9 b^{-4}$ (`Moments.lean`, `SquareExpansion.lean`, `MomentBounds.lean`, `PositiveType.lean`, `BadTypes.lean`)

1. **The Bessel Equivariance Operator $r_\psi(s)$ and `HasAmplitudeBlocks` (`Moments.lean:111-676`, `SquareExpansion.lean:645-695`):**
   Let $R_0 = S.\mathrm{reducedImage}(\mathrm{besselS}) \le \mathrm{ResidueGL}$ be the reduction of the Bessel subgroup. On source coordinates, elements $t \in R_0$ act via the unitary operator `besselTranslate t` ($r_\psi(t)$ for `s ∈ R₀`, $0$ otherwise; `Moments.lean:185-189, 268-275`). Crucially, if we restrict amplitudes to rational elements in the Bessel subgroup `besselS`, then `amplitudeSum_besselS_apply` (`SquareExpansion.lean:435-450`) plus the discrete-series reproducing kernel (`Moments.lean`) shows that the `besselS` contribution to $P^* \rho(s) P$ equals $r_\psi(s)$.

   What about $\gamma \notin \mathrm{besselS}$ near $R_0$? At either prime $p_i$ ($i \in \{0,1\}$), any $s \in \mathrm{ResidueGL}$ matching $t \in R_0$ above $p_i$ fixes the isotropic vector $e_0$, forcing `meetNorm s` $\ge p_i^{2f} \ge (M/b)^f$ and excluding all nontrivial scalar cosets $\zeta R_0$ (`avoidsScalarCosets_setOf_exists_apply_eq`, `SquareExpansion.lean:613-624`). Applying the remaining-term bound (`sqrt_secondMoment_compl_besselS_le`) yields `secondMoment_compl_besselS_le` (`SquareExpansion.lean:645-695`):
   $$\sum_{s : s_i \in (R_0)_i} \|P_s - r_\psi(s)\|_{\mathrm{HS}}^2 \le b^{-12}\,\mathcal{D}_{\mathrm{id}}, \qquad \mathcal{D}_{\mathrm{id}} = |R_0| \cdot D_X.$$
   In particular, taking $s = 1$ gives $\|P^* P - I\|_{HS}^2 \le D_X / b^{12}$ (`hilbertSchmidtNorm_sub_one_sq_le`, `Moments.lean:495-497`), so $P$ is already almost an isometry into the full principal-level space!

2. **Filtering Out Bad Polynomial Types (`MainTerm/BadTypes.lean`, `SpanningTheorem.lean:248-268`):**
   The target space is not all of `principalForms Y₀`, only its image under the central idempotent `D.e₀` (`goodIdempotentAbove`) of `D.chosenGL`. Over the $f$ chosen places above each $p_i$, `e₀` projects onto tuples of irreducible/allowed degree-$r$ monic polynomials over $\mathbb{F}_{p_i}$, at least one primitive (`goodTupleFamilies`, `EqualMultiplicities.lean:68-75`).
   - Using character theory / cyclicity of $\mathbb{F}_{p^r}^\times$, `BadTypes.lean:50-187` bounds non-allowed and non-primitive monic polynomials (`card_not_isAllowedPolynomial_le`, `card_not_primitive_mul_le`), proving `re_coeff_one_sub_sum_tupleIdem_le` (`BadTypes.lean:217-261`): the coefficient of $1 - e_0$ at $1 \in \mathrm{chosenGL}$ is at most $\frac{1}{2} b^{-8}$ (`bad_types_rare`, `SpanningTheorem.lean:248-254`).
   - On $R_0$, the mean squared norm of the restricted character is $\le 2$ (`sum_norm_reducedCharMean_sq_le ≤ 2`, `Moments.lean:1003-1034`). Convolving `r_ψ` against `1 - e_0` (`Moments.lean:1045-1219`) applies Cauchy–Schwarz ($\frac{1}{2} b^{-8} \cdot 2 = b^{-8}$) plus the $b^{-12} \mathcal{D}_{\mathrm{id}}$ error from $P_s - r_\psi(s)$, giving
     $$\|(1 - e_0) P\|_{\mathrm{HS}}^2 \le 4 b^{-4} D_X \quad \Longrightarrow \quad \mathrm{IsNearIsometry}(e_0 \circ \mathrm{scaledPoincare},\, 5 b^{-4})$$
     (`isNearIsometry_piTensorElem_comp` at `Moments.lean:1239-1258`, exported as `isNearIsometry_e₀_comp_scaledPoincare` at `SpanningTheorem.lean:261-268`).

3. **Positive-Type Subgroup Bootstrapping (`MomentBounds.lean:214-526`, `PositiveType.lean:116-222`):**
   To bound $\sum_{s \in \mathrm{ResidueGL}} \|P^* \rho(s) P\|_{\mathrm{HS}}^2$ uniformly in the large finite group $\mathrm{ResidueGL}$, `MomentBounds.lean` inducts/maximizes over finite subgroups of stabilizers!
   For any subset $S_g \subseteq \mathrm{chosenPlaces}\,0$ above $p_0$ and vector choice $d : S_g \to (\mathrm{Fin}\,r \to \mathbb{F}_{p_0})$, let `fixer Sg d` (`Climbing.lean:233-235`) be the elements $s \in \mathrm{ResidueGL}$ whose component at each $w \in S_g$ fixes the line $\mathbb{F}_{p_0} d(w)$ up to scalar, and define the stabilized second moment `fixerMass Sg d` $= \sum_{s \in \mathrm{fixer}\,Sg\,d} \mathrm{secondMoment}(s)$. Define
   $$M_{\max} := \max_{S_g,\, d} \; b^{6 k |S_g|} \cdot \mathrm{fixerMass}(S_g, d)$$
   (`sum_secondMoment_le`, `MomentBounds.lean:452-526`). Because $P^* P$ is self-adjoint positive semidefinite, $\beta(s) := \|P^* \rho(s) P\|_{\mathrm{HS}}^2 = \mathrm{tr}\!\left(\rho(s) P P^* \rho(s)^{-1} P P^*\right)$ is a **positive-type function** on $\mathrm{ResidueGL}$: `le_apply_one_of_inner_eq` (`SquareExpansion.lean:82-89`) proves $\beta(s) \le \beta(1) \le 2 D_X$ everywhere, and its group Fourier coefficients on $GL_r(\mathbb{F}_{p_0})$ are nonnegative!

   Now consider the maximizing pair $(S_g, d)$ achieving $M_{\max}$:
   - **Case 1: $S_g = \mathrm{univ}$ (all $f$ places above $p_0$ fixed).** Then `secondMoment_fixer_univ_le` (`MomentBounds.lean:214-218`) bounds:
     - Elements in scalar cosets $\zeta R_0$ inside `fixer univ d`: there are at most $M^f |R_0|$ of them, each contributing $\le \beta(1) \le 2 D_X$ (using positivity of $\beta$!). Meanwhile `mainSecondMoment_le` / `mul_identitySecondMoment_le` forces $M^f \mathcal{D}_{\mathrm{id}}$ to be tiny against $b^{-6 k f} \mathcal{D}_{\mathrm{main}}$.
     - Elements outside scalar cosets (`AvoidsScalarCosets`): have $\mathrm{meetNorm} \ge p_0^{2f} \ge (M/b)^f$, so `RemainingTerms` crushes them below $\frac{1}{2} b^{-6kf} \mathcal{D}_{\mathrm{main}}$.
     - Total when $S_g = \mathrm{univ}$: $\mathrm{fixerMass} \le b^{-6kf} \mathcal{D}_{\mathrm{main}}$, so $M_{\max} \le \mathcal{D}_{\mathrm{main}}$.
   - **Case 2: $S_g \neq \mathrm{univ}$.** Pick an unfixed place $w \notin S_g$. Partition `fixer Sg d` into:
     1. **Open elements** (`IsOpenElement`, `Climbing.lean:259-262`): all $r \times r$ leading principal minors of $s$ and the frame-Gram matrix $Z(s)$ are nonzero modulo every place. By `secondMoment_fixer_isOpenElement_le` (`MomentBounds.lean:276-315`)—calling `MainTerm` (`linkSecondMoment_isOpenElement_le`) + `RemainingTerms` (`secondMoment_remainingTerms_le`)—the open elements contribute at most
        $$(1 + 4 b^{-4})\, b^{-6 k |S_g|}\, \mathcal{D}_{\mathrm{main}}.$$
     2. **Non-open elements** ($\neg\,\mathrm{IsOpenElement}$, i.e., at least one leading minor vanishes at some place $w'$ and index $l < n$):
        - If a minor vanishes at a place outside $w$ (or wait: for $l < \varrho+1$, `sum_leadingMinor_eq_zero_le` at `MomentBounds.lean:341-400` analyzes the Fourier transform of $\beta$ on the abelian additive block of matrices / translations at $w$!). Specifically, `PositiveType.card_mul_sum_det_eq_zero_le` (`PositiveType.lean:166-222`) proves a general discrete abelian harmonic-analysis lemma: for any positive-type $\varphi$ supported on vectors fixed by `vectorFixer` lines, if $\det(A_{\le l}) = 0$, then the minor-zero slice is contained in the union over nonzero row-relations $v \in \mathbb{F}_q^l \setminus \{0\}$ (`card_le_card_filter_vecMul_eq_zero`, `PositiveType.lean:153-158`), and by Parseval on additive characters `re_sum_addChar_dotProduct_mul_le` (`PositiveType.lean:116-149`), each row-relation corresponds to fixing a vector $d_w$, which by **maximality** of $M_{\max}$ satisfies
          $$\mathrm{fixerMass}(S_g \cup \{w\}, d[w \mapsto d_w]) \le b^{-6k}\,\mathrm{fixerMass}(S_g, d)!$$
        - Summing over all indices $l$ and places via `sum_not_isOpenElement_le` (`MomentBounds.lean:410-438`), the extra $p_0^{O(r)}$ factor is annihilated by $b^{-6k}$ via `levelPrime_pow_mul_sqrt_le` (`MomentBounds.lean:319-330`), leaving at most $b^{-4} \cdot \mathrm{fixerMass}(S_g, d)$!

   Combining open and non-open elements gives the scalar bootstrap inequality ($x = b^{-4} \le 1/10$, `le_one_add_nine_mul_of_le_add` at `MomentBounds.lean:441-446`):
   $$M_{\max} \le (1 + 4x)\,\mathcal{D}_{\mathrm{main}} + x\,M_{\max} \quad \Longrightarrow \quad (1 - x) M_{\max} \le (1 + 4x)\,\mathcal{D}_{\mathrm{main}} \quad \Longrightarrow \quad M_{\max} \le (1 + 9x)\,\mathcal{D}_{\mathrm{main}}$$
   since $(1 - x)(1 + 9x) - (1 + 4x) = x(4 - 9x) \ge 0$ for $0 \le x \le 1/10$! Taking $S_g = \emptyset$ immediately gives `sum_hilbertSchmidtNorm_scaledPoincare_sq_le` (`SpanningTheorem.lean:274-285`):
   $$\sum_{s \in \mathrm{chosenGL}} \|P^* \rho(s) P\|_{\mathrm{HS}}^2 \le \left(1 + \frac{9}{b^4}\right) \mathcal{D}_{\mathrm{main}}.$$

---

### 2.3 Main Term = Exact Constant $1$ via Floor-by-Floor Sieve & Siegel Top Floor (`MainTerm/`, `Frames/`)

Why does $\sum_{c,c'} \mathrm{secondMoment}_{\mathrm{open}}(c,s,c')$ evaluate to **$(1 + b^{-4}) \mathcal{D}_{\mathrm{main}}$** with exact leading constant **$1$**? This is proved in `MainTerm/EnergyEstimate.lean` (`linkSecondMoment_isOpenElement_le`, `L640-691`) by reducing the open-cell sum over $s \in \mathrm{fixer}(S_g, d)$ to a global product of local `SieveSystem`s (`MainTerm/GlobalSieve.lean`, `SieveSystem.lean`).

1. **Turning the Second Moment into a Shifted Lattice Energy on $S.\mathrm{ratGram}$ (`GlobalToLocal.lean`, `EnergyEstimate.lean:488-624`):**
   Suppose $s$ is an open element (`IsOpenElement.leadingMinor_ne_zero`, `EnergyEstimate.lean:100-106`). For each pair $(c, c')$, an amplitude term $\gamma \in \mathrm{termsOver}(c,s,c')$ can be folded (via the coset sum over $K(M)$ in `SiegelTopBound.siegel_sum_le_lintegral_sphere` and `mul_sum_norm_sum_cosetAmplitude_sq_le_fiberPairing`, `SiegelTopBound.lean:647-708, 748-822`) into a bilinear form `GlobalSieve.densitySum` evaluated at a lattice-level family of heads $p, q : \mathbb{N} \to \mathbb{A}^\times$ satisfying `SieveSystem` positivity and Fourier decay (`BoundsDecay`, `GlobalSieve.lean:515-518`).

2. **Floor-by-Floor Quadric Plancherel Sieve ($i = 0, \dots, \varrho$) (`Frames/QuadricPlancherel.lean`, `Frames/RealBandLimits.lean`, `Frames/FixedLines.lean`, `MainTerm/GlobalSieve.lean`, `MainTerm/FiniteSieveSystem.lean`):**
   `GlobalSieve.sieve` (`GlobalSieve.lean:1145-1204`) peels off one hyperbolic plane $i \in \{0, \dots, \varrho\}$ at a time (`densitySum_succ_le`, `GlobalSieve.lean:621-645`):
   - **Archimedean place (`Frames/RealBandLimits.lean:693-750`, `Frames/QuadricPlancherel.lean:202-330`):** At floor $i$, pairing two Bessel integrals whose $i$-th diagonal frame-Gram entries differ by $\nu = p_i^{-1} - q_i^{-1}$ is the Fourier `wave` transform of the floor-$(i+1)$ form!
     - `IsCutBessel.integrable_and_integral_wave_mul_floorForm_succ` (`RealBandLimits.lean:675-683`) expresses floor $i$ as $\int_{\mathbb{C}} \mathrm{wave}(\xi c)\, J_{i+1}(p[i\mapsto u(c)], q[i\mapsto u(c)])\,dc$.
     - `correlation_plancherel` (`QuadricPlancherel.lean:202-254`) and `partialCorrelation_weylRatio_heisenbergElem` (`L316-330`) apply Plancherel/Poisson on the quadric Heisenberg fiber to replace the diagonal sum over $p_i, q_i$ with either the zero-shift term ($p_i = q_i$, no loss!) or high-frequency off-diagonal terms ($p_i \ne q_i$), which decay as `dampedPower (k - n^7) ‖ν‖⁻¹` (`IsCutBessel.norm_floorForm_heads_le`, `RealBandLimits.lean:659-667`).
     - At floor $0$, `norm_bot_le` in `exists_hasLocalBounds_of_isCutBessel` (`RealBandLimits.lean:691, 719, 744-745`) bounds the normalized bottom form by $(1 + b^{-10})/\deg_v$!
   - **Finite places (`MainTerm/FiniteSieveSystem.lean:72-339`, `Frames/FixedLines.lean:277-447`):**
     `FiniteSieveSystem.exists_intermediateGroup_sieveSystem` (`L289-339`) packages the finite adelic mass integrals `F.massIntegral Z`.
     - For the full congruence group at a place $w$, `massIntegral_full_le` (`FiniteSieveSystem.lean:72-80`) shows `F.massIntegral K ≤ vol(K) · vol(K(g)) · (1 + b⁻⁶)`.
     - Whenever a place $w \in S_g$ fixes a line $d(w)$ (`fixer Sg d`), passing to the parabolic subgroup $H = \mathrm{vectorFixer}(w, d(w))$ of index `p₀^r - 1` (`index_comap_vectorFixer`, `FixedLines.lean:277-293`) gains the factor **`b^(6k)`** per stabilized place via `massIntegral_mul_le_of_relIndex_eq` (`FixedLines.lean:320-328, 401-447`).
   - Multiplying across places (`GlobalSieve.boundsDecay_prod`, `L819-858`) bounds the global sum over all non-zero frequencies at every floor $i \le \varrho$ by the Poisson-decay constant $b^{2403 n^9 f}\,\mathrm{decayConst}$ (`EnergyEstimate.lean:282-354`).

3. **Siegel Top Floor ($i = \varrho+1$) (`MainTerm/SiegelTopBound.lean:193-976`, `Frames/TopFloor.lean:239-695`):**
   After peeling all $\varrho$ hyperbolic planes, the sieve lands on `lastEntryDensity` (`TopFloor.lean:669-694`): the remaining free variable is a vector $x \in X_0$ together with $t = p_\varrho$ satisfying the quadratic sphere equation $x^* x = |t|^2/N - N$.
   - `IsFillingData.sum_mul_norm_sum_cosetAmplitude_sq_le_lastEntryDensity` (`SiegelTopBound.lean:856-976`) bounds the coset pairing by the sphere integral over `normFiberMeasure` (`fiberPairing`, `TopFloor.lean:68-72, 239-281`).
   - Here `normDensity_indicator_eq_mul` and `IsFillingData.enorm_normDensity_le_mul_lintegral_normFiberMeasure` (`SiegelTopBound.lean:193-233, 433-459`) replace the discrete lattice point sum on $X_0$-spheres (Eisenstein/Siegel-Weil threshold!) by the smooth coarea `normFiberMeasure` integral, incurring at most the zeta tail `idealZeta (Ô E) (3ϱ + 4) ≤ 1 + b⁻⁶` (since $2^{-\varrho} \ll b^{-6}$ for $\varrho \ge 10^5$!).
   - The leading normalization `siegel_constant_eq` and `exists_scaledSiegelConst_eq_and_massRatio_le` (`SiegelTopBound.lean:259-355`) pull out `scaledSiegelConst` (which satisfies `scaledSiegelConst ≤ (1 + b⁻⁹) * ...` by `IsAdmissible.scaledSiegelConst_le`, `Setup.lean:560-563`).

4. **Exact Constant Cancellation (`MainTerm/EnergyEstimate.lean:110-354`):**
   In `prod_poissonConst_eq` (`EnergyEstimate.lean:160-179`) and `sieve_constant_le` (`EnergyEstimate.lean:282-354`), every single global constant—$\mathrm{vol}(\widehat{\mathcal{O}}_E)^n$, `frameScaleProd`, $\prod_v \deg_v^{-1} = \mathrm{besselDegree}^{-1}$, $\mathrm{mass}(E, k)$, $\mathrm{mass}(E, r)$, `unipotentCovolume`, and `scaledSiegelConst`—telescopes cleanly into $\mathcal{D}_{\mathrm{main}} = S.\mathrm{mainSecondMoment}$, leaving:
   $$\mathrm{sieveConstant} \le (1 + b^{-6})\!\left((1 + b^{-9})^2 (1 + b^{-6}) \cdot b^{-6k|S_g|} + b^{-10}\right) \le (1 + b^{-4})\, b^{-6k|S_g|}$$
   (proved elementarily for $u = b^{-1} \le 10^{-3}$ in `one_add_pow_six_mul_add_pow_ten_le_one_add_pow_four`, `EnergyEstimate.lean:126-145`, using `(1 + b⁻¹⁰)^f ≤ 1 + b⁻⁹` from `one_add_inv_pow_ten_pow_le`, `L110-122`). Hence `linkSecondMoment_isOpenElement_le` (`EnergyEstimate.lean:640-691`) achieves the exact leading constant **$1 + O(b^{-4})$**.

---

### 2.4 Off-Main Terms: Bordered-Determinant Discriminant Gain & Open-Cell Sobolev Orbit Bounds (`RemainingTerms/`, `Bessel/`)

Why are all rational elements $\gamma \in \Gamma^* = S.\mathrm{remainingTerms}$ (which excludes elements with $\mathrm{termDisc}(\gamma)=0$ that preserve the isotropic space $A = \langle e_0,\dots,e_{\varrho-1}\rangle$ and agree with `unipotentChar`, `Size.lean:743-756`) bounded by $b^{-30} \mathcal{D}_{\mathrm{id}}$ (`secondMoment_remainingTerms_le`, `Sum.lean:688-748`)? Because cutting $W \mapsto W^\flat$ kills the non-compact tail and separates double cosets into three mechanisms:

1. **Archimedean Open-Cell Bound via Schur Convolution & Cube Sobolev (`Bessel/SchurBound.lean`, `SobolevBound.lean`, `OpenCellBound.lean`):**
   Suppose $\gamma \in \mathfrak{s}.G_1$ has frame-Gram matrix $Z = \mathrm{realFrameGram}\,\gamma$ lying in the open cell $\Omega$: `gramDiscReal Z` $:= |\det Z|^2 - |D_\varrho|^2 > 0$, where $D_\varrho$ is the upper-left $\varrho \times \varrho$ minor (`OpenCellBound.lean:22, 910-925`).
   - **Schur Bound (`SchurBound.lean:302-333`):** Using `exists_derivative_kernels` (`L172-239`) and the discrete-series reproducing identity `convolve F (formalDegree * dsCoeffInFrame) = F` (`FillingData.lean:401`), `IsBesselFunction.hasSchurBound_of_convolve_eq` proves that every right-invariant Lie derivative word $V_w$ of length $|w| \le 2 n^2$ has $L^2(\mathfrak{U}\backslash G_1)$ convolution operator norm at most $P^{|w|} \sqrt{|I|/\deg}$.
   - **Sobolev on the Gram Section (`SobolevBound.lean:690-756`):** Near $Z \in \Omega$, `gramSection Z` pulls $Z$ back smoothly (`gramDiscReal_div_two_le_and_isBoundedInCell`, `OpenCellBound.lean:153-176`). Changing coordinates to $U(\kappa) \times \mathfrak{U}^0$ multiplies Haar measure by `openCellConst * c^{|\kappa|-1}` (`fixerMeasure`, `SobolevBound.lean:688-700`). Applying `sobolev_trace_cube` on a small cube in $\Omega$ replaces pointwise evaluation of $\int \varphi(y) W(\gamma_Z (uh)^{-1} y) dy$ at $Z$ by integrals over $2 n^2$ right-derivatives ($r^4$ letters costing $P^{44}$), yielding `lintegral_gramSection_integral_le` (`SobolevBound.lean:690-701`) with a polynomial price $P^{2000 n^2} D$.
   - **Open-Cell Kernel Contraction (`OpenCellBound.lean:921-952`):** Setting $P = \mathrm{poly}(\rho^n / \mathfrak{g}(Z))$, `New.BesselSystem.exists_isOpenCellBound` produces a finite measure $\nu$ of mass $\le \mathrm{pairingBoundSq} \propto (\rho^{9n}/\mathfrak{g})^{10^5 n^4} |I|^2 / (\deg \cdot \mathfrak{g}^{k-1})$ controlling the averaged double integral over the fixer factors. Notice the crucial exponent **`k - 1`** in the denominator $\mathfrak{g}^{k-1}$: growing rank $k$ beats the polynomial $(10^5 n^4)$ loss!

2. **Double-Coset Orbit Sum via Eichler Shifts (`RemainingTerms/SchurOrbit.lean:216-955`):**
   Every term $\gamma$ in $\Gamma^*$ has a well-defined `cellRank` $j \in \{1, \dots, \varrho+1\}$ (`hasCellRank_cellRank_of_mem`, `Size.lean:736-741`; cell rank $0$ cannot belong to $\Gamma^*$ because `normOnePairOccursFrom` puts it in the scalar cosets of $R_0$, `Size.lean:773-775`).
   - Within a $(U_c^0, U_{c'}^0)$-double coset, shifting by $eichlerShift$ (`SchurOrbit.lean:216-359`) realizes all rational orbit elements $\delta \in U_c^0 \gamma U_{c'}^0$ as lattice translates (`IsLatticeTranslate`, `L234`).
   - Combining Cauchy–Schwarz across $\gamma$ and $\gamma^{-1}$ with the archimedean open-cell bound (for $j = \varrho+1$) and unipotent unfolding (for $1 \le j \le \varrho$), `sq_tsum_amplitudeMajorant_doubleCoset_le` (`SchurOrbit.lean:875-913`) and `tsum_amplitudeMajorant_orbit_le` (`L955`) bound the orbit's total amplitude by $V_{\mathfrak{U}} \cdot \mathrm{termSize}(c, c', \gamma)$, inversely proportional to $(M^{2\min(\varrho,j) f}\,\mathrm{maxGauge})^{k/2}$, where `maxGauge` (`BorderedDeterminant.lean:448, 777`) combines the $j \times j$ leading minor norm `minorNorm` with `termDiscNorm` (bordered determinant) divided by the two torsion/isotropic row indices `isotropicRowsIndex`.

3. **Pairwise Discriminant Gain & Adelic Siegel Lemma (`RemainingTerms/Gain.lean`, `Count.lean`, `SiegelLemma.lean`, `Sum.lean`):**
   To sum `orbitBound` over *all* near double-coset representatives $\gamma$ in $\Gamma^*$ without losing the $k/2$-th power, `Sum.lean` squares the sum (`enorm_amplitudeSum_sq_le`, `L626-680`) and pairs $\gamma, \gamma'$ over $(c, s, c')$!
   - **Links & Pair Lattice (`BorderedDeterminant.lean:167-280`, `Data.lean:50-102`, `Gain.lean:758-859`):** Each $\gamma$ defines a totally isotropic `link γ` in $(A^\perp/A) \oplus (A^\perp/A)$ with positive-definite `linkMetric` on $X_0 \perp E z^+$ (`norm(z^+) = N`), and an integral lattice `termLattice c c' γ`. Intersecting `termLattice c c' γ` and `termLattice c c' γ'` on `commonLink γ γ'` yields `pairLattice c c' γ γ'` of discriminant `pairDiscriminant`.
   - **Bordered Determinant & Ostrowski–Taussky Gain (`Gain.lean:124-342, 828-858`):** `pairDiscriminant_sq_le` proves:
     $$\left(\mathrm{pairDiscriminant}(\gamma, \gamma') \cdot x_{\text{same-link}}\right)^2 \le \left(\frac{2}{M}\right)^{2 c^+ f} \mathrm{levelGauge}_j(\gamma) \cdot \mathrm{levelGauge}_{j'}(\gamma'),$$
     where $c^+ = \mathrm{linkCorank}(\gamma,\gamma') = \dim(\mathrm{link}\,\gamma / (\mathrm{link}\,\gamma \cap \mathrm{link}\,\gamma'))$!
     - If $\mathrm{link}\,\gamma \ne \mathrm{link}\,\gamma'$ ($c^+ \ge 1$), congruence of $\gamma \gamma'^{-1} \equiv 1 \pmod M$ on the class lattice forces a congruence gain of $(2/M)^{2 c^+ f}$ (`LinkSplitting.one_le_mul_linkDiscSq`, `Gain.lean:313-342`) using Ostrowski–Taussky (`abs_norm_det_gram_sub_le`, `Gain.lean:124-159`).
     - If $\mathrm{link}\,\gamma = \mathrm{link}\,\gamma'$ ($c^+ = 0$) and $j = \varrho+1$, `x_{\text{same-link}}` equals $x \le \mathrm{meetNorm}(s)$ (`Gain.lean:832`)—so even diagonal same-link pairs gain by the places where $s$ meets!
   - **Convergence via Adelic Siegel Lemma (`SiegelLemma.lean:528-637`, `Count.lean:132-219`, `Sum.lean:257-494`):** Counting integral full-rank sublattices $L_{12} \subseteq \mathrm{commonLink}$ of discriminant $\le D$ via the adelic `siegel_lemma` (`SiegelLemma.lean:528`) and submodule zeta function (`Discriminants.submoduleZeta_pi_le` at `Discriminants.lean:152-169`) proves `sum_pairDiscriminant_inv_le` (`Count.lean:194-219`): $\sum_{L_{12}} \mathrm{pairDiscriminant}^{-k}$ converges rapidly! Distinguishing `InSameLinkClass` vs not (`Sum.lean:392-494`) yields `secondMoment_remainingTerms_le` (`Sum.lean:688-748`):
     $$\sum_{s \in \Omega} \mathrm{secondMoment}_{\mathrm{cut}}(s) \le b^{-30}\,\mathcal{D}_{\mathrm{id}}$$
     whenever $\Omega$ avoids scalar cosets and $x^{k}$ beats $b^{O(n^3 f)}$.

---

### 2.5 Turning `1 + 9 b⁻⁴` into Near-Full Spanning (`FewTranslates.lean`, `SpanningTheorem.lean`, `ShortAndEnough.lean`)

Now `SpanningTheorem.lean` holds two exact inputs on $W = D.\mathrm{goodForms}(Y_0)$ ($\dim W = d_T$) and $V = D.\mathrm{SourceForm}$ ($\dim V = D_X$):
- `isNearIsometry_e₀_comp_scaledPoincare`: $\mathrm{IsNearIsometry}(B, \varepsilon_0)$ with $B = e_0 \circ \mathrm{scaledPoincare}$ and $\varepsilon_0 = 5 b^{-4}$ (`SpanningTheorem.lean:261-268`), meaning $\|B^* B - I\|_{HS}^2 \le \varepsilon_0^2 \dim V$ (`FewTranslates.lean:164-165`).
- `targetDim_mul_sum_hilbertSchmidtNorm_sq_le`: (`SpanningTheorem.lean:292-307`), obtained by multiplying $d_T \le |G| \cdot \mathrm{besselDegree} \cdot \mathrm{mass}(E, r)$ (`targetDim_le_card_mul_besselDegree_mul_mass`, `L102-111`) with `(1 + 9/b^4) * mainSecondMoment` (`L274-285`) and `card_sq_mul_mass_mul_prod_le` (`FillingAdmissible.lean`):
  $$d_T \sum_{s \in \mathrm{chosenGL}} \|B^* \rho(s) B\|_{\mathrm{HS}}^2 \le |G| \left(1 + \frac{1}{8 b^2}\right) (\dim V)^2 \qquad (\text{with }\varepsilon = (8b^2)^{-1} \ge \varepsilon_0).$$

1. **From Second Moment to `IsSpread` (`FewTranslates.isSpread_of_second_moment`, `FewTranslates.lean:333-393`):**
   Take any proper subspace $F \subsetneq W$ with orthogonal complement $F^\perp$ of dimension $\alpha d_T$ and orthogonal projection $P_{F^\perp} = \mathrm{orthoProj}(F^\perp)$. Let $B_s = \rho(s) B$. Define in the Hilbert–Schmidt inner product space on $\mathrm{End}(W)$:
   $$W_{\mathrm{HS}} := \sum_{s \in G} \mathrm{hilbertSchmidtVector}(B_s B_s^*).$$
   By unitarity of $\rho$ (`hρ`), $\mathrm{re}\,\langle \mathrm{hilbertSchmidtVector}(P_{F^\perp}), W_{\mathrm{HS}} \rangle_{\mathrm{HS}} = \sum_{s \in G} \|P_{F^\perp} B_s\|_{\mathrm{HS}}^2$. Meanwhile, `inner_hilbertSchmidtVector_translate` (`FewTranslates.lean:280-295`) proves the positive-type identity $\langle \mathrm{hsVec}(B_s B_s^*), \mathrm{hsVec}(B_t B_t^*) \rangle = \|B^* \rho(s^{-1} t) B\|_{\mathrm{HS}}^2$, so averaging over $G \times G$ yields $\|W_{\mathrm{HS}}\|^2 = |G| \sum_{s \in G} \|B^* \rho(s) B\|_{\mathrm{HS}}^2$. By `sq_sum_hilbertSchmidtNorm_orthoProj_comp_le` (`FewTranslates.lean:301-325`), Cauchy–Schwarz in $\mathrm{End}(W)$ gives:
   $$\left(\sum_{s \in G} \|P_{F^\perp} B_s\|_{\mathrm{HS}}^2\right)^2 \le \dim(F^\perp) \cdot |G| \sum_{s \in G} \|B^* \rho(s) B\|_{\mathrm{HS}}^2 \le \alpha (1 + \varepsilon) |G|^2 (\dim V)^2.$$
   Taking square roots and using AM–GM $\sqrt{\alpha(1+\varepsilon)} \le \frac{\alpha + 1 + \varepsilon}{2}$, together with `hilbertSchmidtNorm_one_sub_mul_comp_sq_le` (`L229-247`), the average over $s \in G$ of $\|P_F B_s\|_{\mathrm{HS}}^2$ is bounded above so that $\|P_{F^\perp} B_s\|_{\mathrm{HS}}^2$ must be large for some $s$; since `IsNearIsometry B ε₀` controls the discrepancy between trace and Hilbert–Schmidt norm (`IsNearIsometry.proj_comp`, `FewTranslates.lean:252-266`), there exists $s \in G$ whose image $\mathrm{range}(B_s)$ meets $F^\perp$ in large dimension—equivalently:
     $$\dim(\mathrm{comap}(B_s, F)) \le \left(\frac{1 + \alpha}{2} + \eta\right) \dim V, \qquad \eta = \frac{3}{2}\varepsilon = \frac{3}{16 b^2}$$
     (`IsSpread`, `FewTranslates.lean:54-56`, proved in `isSpread_goodPoincare` at `SpanningTheorem.lean:343-370`).

2. **Greedy Rank Growth (`IsSpread.exists_few_le_finrank_iSup_range`, `FewTranslates.lean:419-538`):**
   Starting from $F_0 = \{0\}$ ($\alpha_0 = 1$), at each step `exists_codim_le` (`L419-447`) picks $s_i \in G$ reducing the ambient remaining fractional codimension $\alpha_i = 1 - \frac{\dim F_i}{d_T}$ to $\alpha_{i+1} \le \frac{1+\alpha_i}{2} + \eta$ unless $B_{s_i}$ already has large kernel in $F_i$; each new translate adds $\dim(\mathrm{range}(B_{s_i})/F_i) = \dim V - \dim(\mathrm{comap}(B_{s_i}, F_i))$, so `exists_codim_le_max` (`L453-492`) trades codimension drop against the total number of translates weighted by `rate` $= \frac{2 \dim V}{5 d_T}$ (`L504`). Stopping when $\alpha \le 16\varepsilon = \frac{2}{b^2}$ (`L510-538`) produces $t \subseteq \mathrm{chosenGL}$ with:
   $$\#t \cdot \dim V \le \frac{5}{2}\left(1 + \log\frac{1}{16\varepsilon}\right) d_T = \frac{5}{2}(1 + \log(b^2/2)) d_T, \qquad \dim\!\left(\bigvee_{s \in t} \mathrm{range}(B_s)\right) \ge \left(1 - \frac{2}{b^2}\right) d_T.$$

3. **Restriction to `ramifiedSourceForms` (`ShortAndEnough.lean:344-404`):**
   Passing from `SourceForm` to `ramifiedSourceForms` (which skips trivial/unramified types via the $\tilde{\chi}$-projection) drops the dimension of each translate by at most $\dim(\mathrm{SourceForm}) - \dim(\mathrm{ramifiedSourceForms}) \le b^{-8} \dim(\mathrm{SourceForm})$ (`ShortAndEnough.lean:378-386`). Over all $\#t$ translates, this costs at most $\#t \cdot b^{-8} \dim(\mathrm{SourceForm}) \le \frac{5 \log(1 + 2b^2)}{b^8} d_T \le \frac{2}{b^2} d_T$, giving the final spanning bound in `enough_forms` (`ShortAndEnough.lean:399-404`):
   $$\dim\!\left(\bigvee_{s \in t} \mathrm{range}(\mathrm{normalizedPoincare}\, s)\right) \ge \left(1 - \frac{2}{b^2} - \frac{2}{b^2}\right) d_T = \left(1 - \frac{4}{b^2}\right) d_T.$$

---

## 3. Classical Barriers Bypassed & Tight Constants

### 3.1 Textbook Machinery Deliberately Skipped & Custom Bypass

1. **No Kuznetsov / Arthur–Selberg Spectral Inversion for Matrix Coefficients:**
   Textbook spanning proofs (e.g., Sarnak–Xue, Brumley–Milićević, Marshall) pass through a full spectral expansion of the automorphic kernel (Arthur–Selberg or relative Kuznetsov trace formula) to cancel oscillatory Archimedean orbital integrals against local Plancherel densities. Here, **zero global trace formula is used for the spanning bound** (only a split-cuspidal simple trace comparison in `EqualMultiplicities.lean:17-22` to equate $d_T = \dim \mathrm{goodForms}(W_j)$!). Instead, `PoincareSeries.lean` pairs finite-type discrete-series Bessel vectors directly against compact-level shifts, turning the second moment cleanly into an explicit geometric sum of rational orbital amplitudes.

2. **No Harish-Chandra Asymptotic Expansion / Paley–Wiener Theorem on $U(p,q)$:**
   Analyzing Archimedean Bessel integrals on $U(\varrho+k, \varrho+1)$ via stationary phase, Harish-Chandra $c$-functions, or Knapp–Stein intertwining operators is notoriously fragile at growing rank. Here, `Bessel/` replaces all of Harish-Chandra theory with:
   - the elementary discrete-series convolution reproducing identity `W * (formalDegree * matrixCoeff) = W` (`FillingData.lean:401, 413`, `SchurBound.lean:302-333`), which immediately yields $L^2$-Schur bounds for arbitrarily many right Lie derivatives; and
   - an elementary Euclidean Sobolev inequality (`sobolev_trace_cube` in `SobolevBound.lean:39, 690-756`) on small coordinate balls around `gramSection Z` in the open cell $\Omega$, paying polynomial powers $P^{2000 n^2}$ that are automatically dominated by $\mathfrak{g}(Z)^{k-1}$ once $k \gg n^4$!

3. **No Quantitative Siegel–Weil Formula at the Top Floor:**
   Evaluating the top-floor rational quadratic sphere count in `SiegelTopBound.lean` avoids Siegel's mass formula / Tamagawa measure computations for indefinite orthogonal/unitary groups. Instead, `SiegelTopBound.lean:193-459` bounds discrete lattice sphere sums directly by coarea integrals over `normFiberMeasure` (`TopFloor.lean:643-700`), losing only the local $p$-adic convergence factor `idealZeta (Ô E) (3ϱ + 4) ≤ 1 + b⁻⁶`—making the exact constant $1$ trivial once $\varrho \ge 10^5$!

4. **No Smooth Bump Test Functions / Archimedean Selberg Sieve:**
   Instead of delicate Beurling–Selberg minorants, `MainTerm/GlobalSieve.lean` (`sieve`, `L1145-1204`) uses a simple geometric damping power `dampedPower` (`SieveSystem.lean:65`) propagated floor-by-floor by `QuadricPlancherel` + Fourier `wave` transforms (`RealBandLimits.lean:675-692`), losing at most $O(b^{-10})$ across all non-zero frequencies.

5. **Finite-Group Linear Algebra Instead of Irreducible Representation Classification of $GL_r(\mathbb{F}_q)$:**
   To prevent non-open elements $\det(Z_{\le l}) = 0$ from spiking the second moment, `PositiveType.lean` (`L116-222`) + `MomentBounds.lean` (`sum_leadingMinor_eq_zero_le`, `L341-400`) bypasses Deligne–Lusztig / Green character tables of $GL_r(\mathbb{F}_q)$. It treats `fixer(Sg, d)` strictly by elementary abelian additive characters on $\mathbb{F}_q$-matrix columns plus positive-type Cauchy–Schwarz (`card_mul_sum_det_eq_zero_le`), feeding back into the $b^{-6k}$ subgroup-index bootstrap!

### 3.2 Tight vs. Slack Numerical Constants

| Constant | Exact Value | Origin (`src/...:<line>`) | Tight or Slack? |
|---|---|---|---|
| **Main-term leading factor** | **$1$** | Exact cancellation of $\mathrm{vol}(\widehat{\mathcal{O}}_E)^n$, `frameScaleProd`, `besselDegree`, `mass E k`, `mass E r`, `scaledSiegelConst` (`EnergyEstimate.lean:160-354`, `SiegelTopBound.lean:328-355`) | **Strictly tight!** Any $1 + c$ with $c > 0$ fails `FewTranslates` unless $b$ absorbs it; $1$ is forced by Parseval/Plancherel + `idealZeta ≤ 1 + b⁻⁶`. |
| **Total second moment factor** | **$1 + 9 b^{-4}$** | From $M \le (1 + 4b^{-4}) C + b^{-4} M$ via `le_one_add_nine_mul_of_le_add` (`MomentBounds.lean:441-446`); the $1+4b^{-4}$ comes from `(√(1+b⁻⁴) + b⁻¹⁵)²`, and $1+b^{-4}$ from `one_add_pow_six_mul_add_pow_ten_le_one_add_pow_four` (`EnergyEstimate.lean:126-145`) | **Tight in exponent $b^{-4}$, clean slack in factor $9$.** The exponent $b^{-4}$ is driven by `(1+b⁻⁶)((1+b⁻⁹)²(1+b⁻⁶) + b⁻¹⁰) ≤ 1 + b⁻⁴` and the $(1-b^{-4})^{-1}$ bootstrap denominator; $9$ is convenient algebra ($4x \le 5x \cdot (1 - \dots)$ works for $x \le 1/10$). |
| **Near-isometry error $\varepsilon_0$** | **$5 b^{-4}$** | `‖(1-e₀) P‖² ≤ 4 b⁻⁴ D_X` + `‖P* P - 1‖² ≤ b⁻¹² D_X` (`Moments.lean:1239-1244`, `SpanningTheorem.lean:261-268`) | **Tight up to small constant** ($4$ comes from `sum_norm_reducedCharMean_sq_le ≤ 2` times $\frac{1}{2} b^{-8}$ in `bad_types_rare`, multiplied in L² norm). |
| **Spanning fraction** | **$1 - 4 / b^2$** | `isSpread` stops at $\alpha = 16\varepsilon = 2 / b^2$ (`ShortAndEnough.lean:372-377`), minus $2 / b^2$ from `SourceForm \ ramifiedSourceForms` (`ShortAndEnough.lean:378-392`) | **Tight to $b^{-2}$**! Notice the loss from $b^{-4}$ in second moment to $b^{-2}$ in spanning codimension is *mathematically unavoidable* from Cauchy–Schwarz + AM–GM in `isSpread_of_second_moment` ($\sqrt{\text{variance}} = b^{-2}$)! |
| **Translate count** | **$5\, d_T \log(1 + 2b^2)$** | $\frac{5}{2}(1 + \log(2b^2))$ doubled (`ShortAndEnough.lean:344-352, 399-404`) | **Tight in $d_T \log b$**, small constant slack ($5/2$ vs $\sim 1/\log 2$). |
| **Subgroup stabilizer gain per place** | **$b^{6k}$** | `p₀^r - 1 ≥ (p₀^k / b)` since $p_0 \ge b^{10}$ / `M ≥ b^{19}` (`FillingAdmissible.lean:675-721`, `FixedLines.lean:438-446`) | **Slack in exponent ($6$ vs $\sim 9.5$), calibrated to beat $M \le b^{22}$.** Crucially $b^{6k}$ matches $(M/b^6)^{kf}$ in `mainSecondMoment_le`! |
| **Rank lower bound $\varrho$ (`10⁵` vs `10⁸`)** | **`10^5 ≤ 𝔰.ϱ` vs `10^8 ≤ 𝔰.ϱ`** | `Filling.ten_pow_five_le_varrho : 10^5 ≤ 𝔰.ϱ` (`Setup.lean:126`, `FillingData.lean:518`); **`IsCutBessel` in `RealShells.lean:161-164` requires `10^8 ≤ 𝔰.ϱ`** (`D.realPlaceSizes` in `FillingData.lean:424`)! | **Slack!** Needed so $2^{-\varrho} \ll b^{-6}$ in `idealZeta(3\varrho+4)` (`MainTerm`) and `10^{10} n^4 ≤ s` in `RealShells.mul_pow_four_le_s`. Note that for `Data P`, $\varrho$ grows polynomially in $x$ (`Sizes.lean:22-28`), far exceeding $10^8$. |
| **Cut-cell tail bound** | **$b^{-15}\sqrt{\mathcal{D}_{\mathrm{id}}}$ ($b^{-30}\mathcal{D}_{\mathrm{id}}$)** | `secondMoment_remainingTerms_le` (`Sum.lean:688-748`) and `secondMoment_compl_besselS_le` (`SquareExpansion.lean:645-695`: `b⁻¹² 𝒟_id`) | **Massive polynomial slack** (`3 (k f) ≥ 30` in `SquareExpansion.lean:668`, `k = |\kappa|` beats $n^4$). |

---

## 4. Community & Audit Takeaways

### 4.1 First Questions a Sceptical Number Theorist Will Ask (and the Exact Lean Answers)

1. **"Wait—does the second-moment constant $1 + 9 b^{-4}$ really stay $1 + o(1)$ as the rank $r = 2\varrho + k + 1 \to \infty$? Usually Rankin–Selberg / Saito–Kurokawa / endoscopic CAP forms or unipotent degenerate terms blow up the diagonal by $2^r$ or $|R_0|$!"**
   - **Lean answer:** Look at `SecondMoment/SpanningTheorem.lean:274-285` (`sum_hilbertSchmidtNorm_scaledPoincare_sq_le`), `Unfolding/MomentBounds.lean:452-526` (`sum_secondMoment_le`), and `MainTerm/EnergyEstimate.lean:640-691` (`linkSecondMoment_isOpenElement_le`). All terms with trivial `termDisc` inside the parabolic stabilizer `besselS` equal the **unitary** operator `besselTranslate` (`SquareExpansion.lean:435-450`), so their contribution at $s \in R_0$ is counted *once* in $\mathcal{D}_{\mathrm{main}}$, NOT multiplied by a Weyl group! Every remaining rational $\gamma \in \Gamma^*$ has non-degenerate $k$-rank exponential decay in $M^{-k}$ (`RemainingTerms/Sum.lean:688-748`), while the non-open boundary matrices ($\det Z_{\le l} = 0$) are trapped by `PositiveType.card_mul_sum_det_eq_zero_le` (`PositiveType.lean:166-222`) into fixed-vector subgroups where `massIntegral_mul_le_of_relIndex_eq` (`FixedLines.lean:320-328`) strips off $b^{-6k}$ per fixed place!

2. **"How do you convert a second moment bound $\le (1 + 9b^{-4}) \mathcal{D}_{\mathrm{main}}$ into a *rank/spanning* bound $(1 - 4/b^2) d_T$ without knowing the eigenvalues of $P^* P$ individually?"**
   - **Lean answer:** `SecondMoment/FewTranslates.lean:333-393` (`isSpread_of_second_moment`) and `498-538` (`IsSpread.exists_few_le_finrank_iSup_range`). Because $P$ is a *near-isometry* on $e_0 W$ (`isNearIsometry_e₀_comp_scaledPoincare`, error $5 b^{-4}$), `B_s = e_0 \rho(s) P` cannot concentrate norm in a small-dimensional subspace (`IsNearIsometry.proj_comp`, `FewTranslates.lean:252-266`). Meanwhile $\sum_s \|(I - P_F) B_s\|_{\mathrm{HS}}^2 = \langle I - P_F, W_{\mathrm{HS}}\rangle_{\mathrm{HS}}$ is controlled directly by $\|W_{\mathrm{HS}}\|_{\mathrm{HS}}^2 = |G| \sum_s \|B^* \rho(s) B\|_{\mathrm{HS}}^2$ via a single Cauchy–Schwarz inequality in Hilbert–Schmidt space!

3. **"What prevents the Sobolev exponent $P^{2000 n^2}$ in the open-cell archimedean bound from beating your $p$-adic/discriminant gain when $\mathfrak{g}(Z) \ll 1$?"**
   - **Lean answer:** Compare `Bessel/OpenCellBound.lean:918-925` (`pairingBoundSq`, denominator $(\mathfrak{g}/2)^{k-1}$, numerator $(\rho^{9n}/\mathfrak{g})^{10^5 n^4}$) with `Bessel/FillingData.lean:424` and `Frames/RealShells.lean:160-166` (`hF.pow_seven_le_k : 𝔰.n ^ 7 ≤ 𝔰.k`, `hF.ten_pow_le_varrho : 10 ^ 8 ≤ 𝔰.ϱ`, giving `mul_pow_four_le_s : 10 ^ 10 * 𝔰.n ^ 4 ≤ s`). Because $k$ grows at least like $n^7$, the $(k - 1)$ exponent from the $U(\kappa)$-fiber Jacobian `fixerMeasure = openCellConst * c^{|\kappa|-1}` (`SobolevBound.lean:688-700`) utterly crushes the Sobolev exponent $10^5 n^4$! And whenever $\mathfrak{g}(Z)$ is small at any infinite place, the arithmetic `pairDiscriminant_sq_le` + `IsNear.levelGauge_le` (`RemainingTerms/Gain.lean:828-922`) transfers that smallness via the product formula / Liouville inequality (`BorderedDeterminant.lean:82-107`) into a huge algebraic minor!

4. **"Where does the multiplicity equality $d_T = \dim \mathrm{goodForms}(W_j)$ enter, and doesn't that require full Jacquet–Langlands for unitary groups?"**
   - **Lean answer:** `Multiplicities/EqualMultiplicities.lean:385-421` (`finrank_goodForms_inf_eigenPart_eq`, `targetDim_eq_finrank_goodForms_spaceW`). It does *not* invoke full Jacquet–Langlands or Arthur's endoscopic classification: `Y_0` and `W_j` differ *only* at archimedean places, and the parameter `paramW` has large gap `D.gap` (`HasGap`). A simple trace comparison using a test function that is supercuspidal at a single split auxiliary place (`trace_eq_of_isCuspidalAt`, `EqualMultiplicities.lean:21`) immediately equates traces of all off-level spherical Hecke operators `heckeOnGood`, forcing equality of eigensystem multiplicities and total dimension $d_T$.

5. **"Is there a discrepancy between $\varrho \ge 10^5$ in `Filling` and $\varrho \ge 10^8$ in `Frames`?"**
   - **Lean answer:** Yes, cleanly stratified! `Filling.ten_pow_five_le_varrho : 10^5 ≤ 𝔰.ϱ` (`Unfolding/Setup.lean:126`) is all that `MainTerm/`, `RemainingTerms/`, `Unfolding/`, and `SecondMoment/` require. Only the archimedean `RealShells` / `RealBandLimits` estimate `IsCutBessel.mul_pow_four_le_s` (`Frames/RealShells.lean:160-166`) asks for `10^8 ≤ 𝔰.ϱ` (`hF.ten_pow_le_varrho`), which `Data.filling` satisfies overwhelmingly (`FillingData.lean:424` via `D.realPlaceSizes`).

### 4.2 Architectural & `TauCeti` / `ShortGRH` Extraction Opportunities

Several self-contained sub-engines in `src/New/Spanning/` have zero number-theoretic prerequisites and are prime candidates for extraction into `TauCeti` / `ShortGRH`:

1. **`SecondMoment/FewTranslates.lean` (570 lines):**
   Pure finite-dimensional Hilbert-space geometry (`IsNearIsometry`, `IsSpread`, `isSpread_of_second_moment`, `exists_few_le_finrank_iSup_range`). Takes *any* unitary representation $\rho : G \to U(W)$, orthogonal projection `pr₀`, and near-isometry $B : V \to W$ satisfying the second-moment inequality, and outputs a logarithmic-size subset $t \subseteq G$ spanning $(1 - O(\sqrt{\varepsilon})) \dim W$. Immediately reusable in any spectral-spanning or expander-graph setting.
2. **`SecondMoment/PositiveType.lean` (224 lines):**
   Pure finite-field Fourier bound (`card_mul_sum_det_eq_zero_le`, `L166-222`): for positive-type $\Theta \ge 0$ on a group acting via $n \times n$ matrices over $\mathbb{F}_q$ and two $n \times m$ frames $A_0, A_1$, proves $q \sum_{\det(A_1^\top \pi(s) A_0)=0} \Theta(s) \le 2 \sum_s \Theta(s) + q^{|m| + |n|/2} Y$ from elementary additive characters and stabilizer bounds $Y$. Clean standalone lemma for `TauCeti.Analysis` / `TauCeti.RepresentationTheory`.
3. **`MainTerm/SieveSystem.lean` + `MainTerm/GlobalSieve.lean` (1,511 lines):**
   Abstract multi-floor quadratic sieve (`SieveSystem`, `SieveSystem.pi`, `GlobalSieve.sieve`). Formulated purely for abstract groups/measures `PlaceData` with `wave`-transform descent across floors $0 \le i \le \varrho$ and a top positive-semidefinite form at $\varrho+1$. Completely decoupled from CM fields and unitary groups.
4. **`RemainingTerms/BorderedDeterminant.lean` (parts) & `Bessel/SobolevBound.lean` (`HasDerivWords`):**
   `HasDerivWords` + `sobolev_trace_cube` -> `lintegral_gramSection_integral_le` (`SobolevBound.lean:36-40, 690-756`) is a clean template for converting $L^2(\Gamma \backslash G)$ Schur bounds on Lie-group derivatives into pointwise-in-parameter $L^2$ bounds over submanifolds—only `gramSection` and `openCell` are $U(\varrho+k,\varrho+1)$-specific.
