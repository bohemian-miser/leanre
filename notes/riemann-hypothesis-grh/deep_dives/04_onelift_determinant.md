# Deep Mathematical Comprehension: `New.OneLift` & `New.Determinant`

**Target repository:** `/usr/local/google/home/rop/github-personal/leanre/data/rh_grh/src/` (`upstream/main` `grh`)  
**Scope:** `src/New/OneLift/` and `src/New/Determinant/`

---

## 1. Engine Architecture & Entry/Exit Interface

At the highest level, `src/New/Determinant/` and `src/New/OneLift/` form **Theorem C** of the main inequality (`New.star_inequality` in `src/New/Reduction/MainInequality.lean:93`): given a nearly full-rank linearly independent tuple of target forms $y_1, \dots, y_n \in D.\text{targetForms}$ with $n \ge (1 - 4/b^2) d_T$ ($d_T = D.\text{targetDim}$), index $\le \delta$, and covolume $\le c$, they prove that the untwisted $m$-step theta-lift chain $\Theta_1 : D.\text{targetForms} \to \text{Form}(Y_m)$ cannot shrink covolumes below the main prime-sum amount minus $3 f a \log^4 b$.

### 1.1 Sub-engine Directory Map

| Submodule | Mathematical Role | Key Files |
|---|---|---|
| `New/Determinant/Exchange/` | Rallis/Siegel–Weil exchange identities for matched ramified data on complementary dual pairs | `RemovingPlanes.lean`, `LargeTriple.lean`, `StableSpacesStandardData.lean`, `TheoremForPartners.lean`, `OneSquare.lean` |
| `New/Determinant/Chain/` | Abstract finite square law (`SquareLaw`, `nextDatum`), $m \times m$ triangle of lifts (`IsTriangle`, `HasSquareModuli`), factoring $Z(\vartheta)/Z(1)$ into single stable lifts $\times$ critical $L$-ratios | `SquareLaw.lean`, `TriangleNorms.lean`, `Moduli.lean`, `TriangleLifts.lean`, `ChainNorms.lean`, `NormOfChain.lean` |
| `New/Determinant/Norms/` | Representation-valued theta kernel $\theta_W(g,h)$ and adjointness/Rallis formula for single stable-range lifts $W_j \to V_j$ | `VectorKernel.lean`, `AdjointThetaLift.lean` |
| `New/Determinant/AuxiliaryForms/` | Two-grid path transfer ($\tilde{Y}^m_0 \leftrightarrow Y_m$) turning deep-level short forms on $\tilde{Y}^m_0$ into spanning auxiliary target forms with controlled $\vartheta$-twisted integrality and $\sigma$-norms | `GridPaths.lean`, `PathData.lean`, `GridFirstColumns.lean`, `FirstPath.lean`, `Turns.lean`, `DiagonalTurns.lean`, `DeepLevelVanishing.lean`, `LastPath.lean`, `RegularParameters.lean`, `SpanningForms.lean` |
| `New/Determinant/Twist/` | Arithmetic/height interface (`ClearsProjection`, `IsRegularFamily`, `HasSmallRatios`) and the final Theorem C assembly (`integral_forms_long`) | `FitTwists.lean`, `LongForms.lean` |
| `New/OneLift/ComparisonOperator/` | Mod-$\varpi^2$ lattice gluing, three-exchange twist extraction, sparse-sum approximation (`ProductsSpan`), and the comparison operator $U_\vartheta = n_{\mathrm{Aut}} hk^2 \operatorname{glue}_\vartheta \operatorname{glue}_\vartheta^*$ | `ExchangeData.lean`, `LineCoordinates.lean`, `FirstFactors.lean`, `ThreeExchanges.lean`, `GluedLattices.lean`, `GluedForms.lean`, `ThetaKernelEstimates.lean`, `ProductsSpan.lean`, `GluingMaps.lean` |
| `New/OneLift/FalseLifts/` | Hyperplane-sum + Hecke-root annihilation $\implies$ vanishing of all hyperbolic-tower descents $\implies$ identically zero $U(V^\circ)$-theta periods | `BottomOfTower.lean`, `HyperbolicPlaneStep.lean`, `PeriodsOfFalseLifts.lean` |
| `New/OneLift/HeckeValues/` | Rank-one theta lifts of critical characters, four-block seesaw test forms, and height bounds for $L(z, (\nu \vartheta^s)^{-1})/L(z, \nu^{-1})$ and `heckeValueProd` | `CharacterLift.lean`, `CharacterLiftNorm.lean`, `CentralAction.lean`, `AlgebraicPartIntegrality.lean`, `AlgebraicPartSize.lean`, `PeriodAtOne.lean`, `TwistedRatio.lean`, `TwistedValueHeights.lean` |
| `New/OneLift/` | False-lift norm contraction (`TestedForms.lean`) and the single-lift determinant ratio height bound $Z_j(1)/Z_j(\xi_\iota^j)$ (`LiftVolumeHeight.lean`) | `TestedForms.lean`, `LiftVolumeHeight.lean` |

### 1.2 Exported Interface & External Callers

1. **Primary Theorem C Exit (`New.Data.integral_forms_long`):**
   - Defined at `src/New/Determinant/Twist/LongForms.lean:274` (and unabsorbed version `New.Data.integral_forms_long_with_completion_cost` at `LongForms.lean:223`).
   - **Called by:** `New.star_inequality` (`src/New/Reduction/MainInequality.lean:93`, imported at `:5`).
   - **Statement:** For linearly independent $y : \text{Fin } n \to D.\text{targetForms}$ with $(1 - 4/D.b^2) D.\text{targetDim} \le n$, `D.targetLattice.IndexLe y δ`, and `D.targetLattice.CovolumeLe y c`,
     $$d_T \cdot \bigl(D.\text{mainAmount} - 3 f a \log^4 b\bigr) \le c + 2\delta.$$

2. **Chain Determinant Factorization (`New.Data.exists_chainDeterminant_pos_and_div_chainDeterminant_one_eq` & `New.Data.exists_adjoint_chain_comp_eq_smul_rallisProduct`):**
   - Defined at `src/New/Determinant/Chain/NormOfChain.lean:432` and `:313`.
   - **Called by:** `src/New/Determinant/Twist/LongForms.lean:180`, `src/New/Reduction/IntegralTargetForms.lean:4`, and `src/New/Congruences/FitTwistsExist.lean:11`.
   - Also exports `New.Data.liftDeterminant` (`NormOfChain.lean:83`), `New.Data.chainDeterminant` (`NormOfChain.lean:113`), `New.Data.chainDeterminant_pos` (`NormOfChain.lean:119`), `New.Data.HasSmallRatios.heightLe_inv_rpow_mul_prod_quotientRatio` (`NormOfChain.lean:449`), and `New.Data.range_goodLift_le` (`NormOfChain.lean:494`).

3. **Single-Lift Ratio Height Bound (`New.Data.heightLe_liftDeterminant_ratio`):**
   - Defined at `src/New/OneLift/LiftVolumeHeight.lean:731`, using `New.Data.IsComparisonOperator` (`LiftVolumeHeight.lean:174`), `New.Data.comparisonOp` (`LiftVolumeHeight.lean:202`), and `New.Data.isComparisonOperator_comparisonOp` (`LiftVolumeHeight.lean:556`).
   - **Called by:** `New.Data.exists_hasSmallRatios_heightLe_liftDeterminant_div` (`src/New/Determinant/Twist/LongForms.lean:151`), which consumes `New.exists_isRegularFamily` (`src/New/Congruences/FitTwistsExist.lean:21`, imported at `LongForms.lean:8`).

4. **Twist / Congruence Interface (`New/Determinant/Twist/FitTwists.lean` & `OneLift/TestedForms.lean` & `OneLift/HeckeValues/`):**
   - `New.Data.IsRegularFamily` (`FitTwists.lean:237`), `New.Data.HasDenominatorsLe` (`FitTwists.lean:189`), `New.Data.ClearsProjection` (`FitTwists.lean:173`), `New.Data.CriticalPair.IsMainPair` (`FitTwists.lean:133`), `New.Data.goodLift` (`FitTwists.lean:117`).
   - **Called by:** `src/New/Congruences/FitTwistsExist.lean`, `Selmer/ClassSums.lean`, `Selmer/TwistingTheorem.lean`, `GaloisRepresentations/AttachedRepresentations.lean`, `GaloisRepresentations/RowsFromEigensystems.lean`, `GaloisRepresentations/SelmerHypotheses.lean`.
   - `New.DescentPair.IsTestForm`, `New.DescentPair.IsOrthogonalToFalseLifts`, `New.Rows.pointForm` (`src/New/OneLift/TestedForms.lean:209`), and `New.DescentPair.hyperplaneSum_apply_eq_zero_of_rank_one` (`src/New/OneLift/FalseLifts/BottomOfTower.lean:508`) are imported into `SelmerHypotheses.lean` and `BaseLevelOfLabel.lean`.

5. **Supporting Cross-Pillar Exports:**
   - `New.Data.exists_rpow_neg_localPrimeSumTotal_le_norm_coeff` / `New.DescentPair.vectorKernel` (`src/New/Determinant/Norms/AdjointThetaLift.lean`) is used by `src/New/Spanning/Multiplicities/EqualMultiplicities.lean:8`.
   - `New.Data.exists_span_isAuxiliaryForm_eq_top` (`LongForms.lean:72`) uses `New.Data.exists_span_short_lifts_eq_top` (`SpanningForms.lean:884`).
   - `src/New/UpperBound/Kernels/DefiniteKernelSize.lean:5` imports `DeterminantProducts.lean`, `UpperBound/Seesaw/*` imports `ExchangeData.lean`, `Spanning/Bessel/FillingData.lean:18` imports `DeepLevelPoincarePeriod.lean`, and `Spanning/SecondMoment/SpanningTheorem.lean:7` imports `RegularParameters.lean`.

---

## 2. Step-by-Step Mathematical Walkthrough

The global goal is a **product-formula lower bound** on the twisted lattice `(D.targetForms, D.Θ)` (`New.TwistedLattice.covolume_add_index_nonneg` called in `LongForms.lean:256`):
$$0 \le c + 2\delta + n' (2 x_1^2 b^2 + b) + \text{Height}\!\left(\iota \mapsto \frac{Z(1)}{Z(\xi_\iota)}\right),$$
where $Z(\vartheta) = \det(\Theta_\vartheta^* \Theta_\vartheta)$ (`D.chainDeterminant ϑ` in `NormOfChain.lean:113`), $\xi_\iota \in D.\text{MFoldTwist}$ is a regular family of $m$-fold tame characters supplied by `New.exists_isRegularFamily` (`FitTwistsExist.lean`), and $n' = d_T - n \le 4 d_T / b^2$ is the codimension filled by auxiliary forms.

Below is the exact mathematical chain for every pillar inside `OneLift/` and `Determinant/`.

---

### 2.1 How `Exchange/` + `SquareLaw` + `NormOfChain` Factor $Z(\vartheta)/Z(1)$ Outside the Stable Range

#### The Problem
The chain $\Theta_\vartheta = \iota_\vartheta : \text{Forms}(Y_0) \to \text{Forms}(Y_m)$ (`D.lowerChainAtLevel ϑ` in `NormOfChain.lean:105`) is a composition of $m$ theta lifts
$$Y_0 \xrightarrow{\vartheta} Y_1 \xrightarrow{\vartheta^2} Y_2 \longrightarrow \cdots \longrightarrow Y_m,$$
where $Y_j$ has rank $r_j = r + j t$ ($r = \operatorname{rk} Y_0 = m + k - 1$, $t = 5r$, and $Y_0$ is indefinite with $\varrho$ negative signs where $m = 2\varrho + 2$). Crucially, $Y_0 \to Y_1 \to \dots \to Y_m$ is **not** a composition of $m$ lifts in the convergent/stable range of Rallis's inner product formula: each step increases the target rank by $t$, and the first several steps (especially when $j$ is small compared to the signature or when taking adjoints back down the chain) sit **below/outside the stable range** of $Y_0$, and the twists $\vartheta, \vartheta^2, \dots, \vartheta^m$ sit on different edges! You cannot directly apply Rallis's formula to $\Theta_\vartheta^* \Theta_\vartheta$ as a single lift or even step-by-step naively.

#### Step A: The Exchange Theorem (`New/Determinant/Exchange/`)
For a dual pair $(W, V)$ and a complementary pair $(W, U)$ where $\operatorname{rk} V + \operatorname{rk} U = \operatorname{rk} W$ (or rather the sum of ranks and negative signs of $A$ and $A'$ match $W = U_1 \oplus U_2$ in `OneSquare.lean:879`, with $\operatorname{rk} A = \operatorname{rk} A' + 2t$), classical seesaw/Siegel–Weil says that for **trivial** characters, theta integrals over $[U(A)]$ and $[U(A')]$ agree. For **tamely ramified characters** $\nu$ of $[U(1)]$ with modulus $\mathfrak{m}$ (`IsTameFor`), `TheoremForPartners.lean` (`exists_sum_pairLift_comp_pairTransposedLift_eq_smul` in `OneSquare.lean:758`) proves an explicit ramified **Exchange Identity**:
1. **Descent by removing hyperbolic planes (`RemovingPlanes.lean` & `LargeTriple.lean`):** Starting from a large triple where the theta integral is in the convergent range and unfolded along a parabolic subgroup (`LargeTriple.lean:34`), one descends one hyperbolic plane at a time (`RowColExchangeIdentity.cone` / `dualCone` in `RemovingPlanes.lean:32-34`), tracking the Fourier coefficients and proving that any discrepancy vanishes at self-dual lattices (`StableSpacesStandardData.lean:37`).
2. **Matching finite data (`MatchingPartners.lean` & `OneSquare.lean:758`):** Let $\sigma : n \oplus n' \simeq n_1 \oplus n_2$ split the basis of $W = U_1 \oplus U_2$ into ranks $\operatorname{rk} A' = |n|$ and $\operatorname{rk} A = |n'| = |n| + 2t$. For $\chi$ the residue character mod $\mathfrak{m}$ of $\nu$, a pair of functions $\Phi$ on $\operatorname{Mat}_{n' \times (n_1 \oplus n_2)}(R)$ and $\Psi$ on $\operatorname{Mat}_{(n_1 \oplus n_2) \times n}(R)$ is **matched** (`AreMatched ⊤ σ χ Φ Ψ`, `SquareLaw.lean:33`) if:
   - $\Phi$ is supported on `invLastRows σ k` (the bottom $|n'|$ rows of $k^{-1}$ for $k \in \mathrm{GL}_{n_1+n_2}(R)$),
   - $\Psi$ is supported on `firstCols σ k` (the first $|n|$ columns of $k$), and
   - $\Phi(\text{invLastRows } \sigma\, k) = \chi(\det k)\,\Psi(\text{firstCols } \sigma\, k)$.
3. **One Square Law (`one_square_identity_of_isEdgeFamily`, `OneSquare.lean:983`):** Form the two ways of mapping $\text{Forms}(U_1) \to \text{Forms}(U_2)$:
   - Up through $A$ then down: $\Theta(x) = (\text{pairTransposedLift } U_2, A) \circ (\text{pairLift } U_1, A)$ using column blocks $(x_1 \mid x_2)$ of $x$,
   - Down through $A'$ then up: $\Theta'(y) = (\text{pairLift } A', U_2) \circ (\text{pairTransposedLift } A', U_1)$ using row blocks $(y_1; y_2)$ of $y$.
   
   Under the rank/weight/sign conditions `IsSquare` (`OneSquare.lean:879-891`), there exist constants $C > 0$ and $\kappa \in \mathbb{C}$ **independent of $\nu, \mathfrak{m}$** and a scalar $c \ne 0$ with
   $$\|c\|^2 = C \cdot \text{lValueProd}(S, \nu, t), \qquad \text{lValueProd}(S, \nu, t) := \prod_{w \in S} q_w^{t^2} \prod_{z=1}^{t} |L^S(z, \nu)|^2$$
   (`OneSquare.lean:753, 934-935`), such that for every functional $l$, $L(x) = l(\Theta(x) f)$ and $L'(y) = l(\Theta'(y) f)$ satisfy `Exchange.SquareLaw χ σ (κ / c) L L'` (`OneSquare.lean:1013-1014`):
   - $L(g x) = \chi(\det g) L(x)$, $L'(y g) = \chi(\det g) L'(y)$, and
   - $\sum_y \Psi(y) L'(y) = (\kappa / c) \sum_x \Phi(x) L(x)$ for all matched $(\Phi, \Psi)$.

#### Step B: The Finite Square Law & `nextDatum` (`src/New/Determinant/Chain/SquareLaw.lean`)
Wait: in a chain of $m$ lifts, the lift arrows use the **point datum** $\delta_{(1;0)}$ (`pointDatum`, `SquareLaw.lean:80`), which is *not* matched directly! How do we propagate a datum from one square to the next?
- **`SquareLaw.card_mul_apply_fromRows_eq` (`SquareLaw.lean:161`):** Evaluating `SquareLaw` on block-matched functions supported on `(1; -w)` vs. `(w \mid 1)` yields
  $$|\mathrm{GL}_b(R)| \, L'\!\begin{pmatrix} 1 \\ -w \end{pmatrix} = \frac{\kappa}{c} \, |\mathrm{GL}_a(R)| \, L\!\begin{pmatrix} w & 1 \end{pmatrix}.$$
- **`SquareLaw.sum_eq_nextDatum` (`SquareLaw.lean:194`):** Specialize to $w = (\eta; 0)$, apply left-equivariance of $L$ under the unipotent shear $\begin{pmatrix} 1 & s \\ 0 & 1 \end{pmatrix}$ (det $= 1$), sum against $p(-\eta)$ and average over $s \in \operatorname{Mat}_{n \times b}(R)$:
  $$|\mathrm{GL}_a(R)| \sum_{y} p(y) \, L'\!\begin{pmatrix} y \\ 1 \end{pmatrix} = \frac{\kappa}{c} \, |\mathrm{GL}_{n \oplus b}(R)| \sum_{x} (\text{nextDatum } p)(x) \, L\!\begin{pmatrix} 1 & x \end{pmatrix},$$
  where `nextDatum p` (`SquareLaw.lean:87-89`) is supported on block upper-unitriangular matrices $\begin{pmatrix} \eta & s \\ 0 & 1 \end{pmatrix}$ with value $p(-\eta)/|R|^{nb}$.
- **Crucial feature:** Because $L'$ is evaluated at $(y; 1)$ (so its second arrow is a lift with **point datum** $(1; 0)$!) and $L$ is evaluated at $(1 \mid x)$ (its first arrow is a lift with **point datum** $(1; 0)$!), `nextDatum` pushes a general finite datum $p$ on the transposed-lift arrow *across* a lift arrow with point datum $(1; 0)$!
- **Fourier form (`SquareLaw.exists_sum_matrixFourier_eq_sum_nextDatum`, `SquareLaw.lean:484`):** For the adjoint square (with reversed lifts), taking the finite matrix Fourier transform `matrixFourier ψ (star p)` (`SquareLaw.lean:405, 495-498`) replaces `nextDatum` by a Gaussian/Gauss-sum constant $\gamma$ satisfying $\|\gamma\|^2 |R|^{|T|(|T|+2|N|)} = 1$ (`SquareLaw.lean:490`), i.e., **purely a power of $N(\mathfrak{m})$ with no $L$-values!**

#### Step C: The Triangle of Lifts (`ChainNorms.lean` & `TriangleNorms.lean`)
In `ChainNorms.lean` (`z = false`), build an $m \times m$ triangular array of spaces $F(i, n)$ (`TriangleForm false i n`) attached to intervals $[i+1, i+n]$ (`ChainNorms.lean:23`):
- At the base $(i, 0)$, $F(i, 0)$ is the space $Y_0$ with its form negated $i$ times (`triangleNegEquiv`), so $i = 0$ is $Y_0$ and moving down a row negates $Y_0$ (swapping signatures/characters).
- **Horizontal arrows** $a_{\vartheta, i, n} : F(i, n) \to F(i, n+1)$ (`triangleLift false ϑ i n`): adds block $i+n+1$ of rank $t$ with twist $\vartheta^{i+n+1}$ and **point datum** $(1; 0)$. Row $0$ is literally the chain $Y_0 \to Y_1 \to \dots \to Y_m$!
- **Diagonal-down arrows** $d_{\vartheta, i, n} : F(i, n+1) \to F(i+1, n)$ (`triangleTransposedLift false ϑ i n`): removes the first block $i+1$ (the block of $W_{i+1}$'s dual? More precisely, the first step $(i,0) \to (i,1)$ goes to $Y_0$ plus one block of rank $t$, whose character matches $W_{i+1}$!). Its finite datum is constructed recursively by $e_{\vartheta, i, 0} = \Psi_0$ (the adjoint datum at $n=0$) and $e_{\vartheta, i, n+1} = \text{nextDatum}(e_{\vartheta, i, n})$ (`ChainNorms.lean:597-601`).
- **Two Commutation Relations on every square $(i, n)$ with $i + n + 1 < m$:**
  1. **Square commutation (`exists_triangleLift_triangleTransposedLift_comm`, `ChainNorms.lean:216`):** Moving $d$ past $a$ gives
     $$N_n \, a_{i+1, n} \circ d_{i, n} = \frac{N_{n+2}}{\overline{\beta_\vartheta}} \, d_{i, n+1} \circ a_{i, n+1},$$
     where $N_n = \text{triangleGLCard false }\vartheta\, n$ and $\beta_\vartheta$ satisfies `HasAbsUpToNormPower β (quotientRatio (i+1) (i+1+n+1))` (`ChainNorms.lean:228`). Why `quotientRatio`? Because the characters of the two non-point-datum arrows in the square have quotient equal to $\text{untwistedLiftChar}(i+n+2) / \text{untwistedLiftChar}(i+1)$ twisted by $\vartheta^{n+1}$ (`gridChar_mul_leftPairChar` at `ChainNorms.lean:135`, applied in `exists_squareLaw_triangleTransposedLift` at `:165`), and the rank difference of the auxiliary spaces is $t$ (`:190`), producing $t$ critical $L$-values (`quotientRatio`)!
  2. **Adjoint commutation (`exists_triangleTransposedLift_adjoint_comm`, `ChainNorms.lean:531`):** Taking adjoints converts `triangleTransposedLift` into `triangleReversedLift` with `fourierDatum` and translation by `reversalScalar` (`exists_inner_triangleTransposedLift_eq`, `ChainNorms.lean:403`). Crucially, in the reversed-lift square (`exists_squareLaw_triangleReversedLift`, `ChainNorms.lean:262`), the two middle spaces have **equal rank** (`2 * card (GridIndex false 0 (n+1)) = card (GridIndex 0 n) + card (GridIndex 0 (n+2))`, `:279-281`), so `lValueProd ... 0 = 1` (`:299-302`)! Applying the Fourier Square Law (`exists_triangleLift_triangleReversedLift_comm`, `:322`) produces a scalar $\kappa_\vartheta$ with **`HasAbsUpToNormPower κ 1`**—no $L$-values at all, only a power of $N(Q)$!

- **Induction on the Triangle (`IsTriangle.exists_inner_weightedChain_eq`, `TriangleNorms.lean:403`):**
  Peeling off row $i = 0$ inductively (`inner_weightedChain_succ`, `TriangleNorms.lean:367`): for $u_0 = \text{weightedChain}$ of length $m$ on row $0$,
  $$\langle u_0 x, u_0 y \rangle = \kappa_\vartheta \cdot \frac{N_0 N_1^m}{N_m} \cdot \langle x, (S_{\vartheta,0} \cdots S_{\vartheta,m-1}) y \rangle,$$
  where $S_{\vartheta, i}$ is the Gram operator of the **first arrow** $a_{\vartheta, i, 0}$ of row $i$ (which is a single lift from $Y_0$ to a rank-$(r+t)$ space, whose Gram form by Rallis's formula is `rallisOnGood (spaceY 0) (ϑ^(i+1)) (i+1)`! See `NormOfChain.lean:185-196`), and $|\kappa_\vartheta|$ equals $\prod_{1 \le i < j \le m} \text{quotientRatio } i\, j\, \vartheta$ up to $C \cdot N(Q)^{k/2}$!

#### Step D: Reconciling the Chain with Single Stable Lifts (`NormOfChain.lean`)
1. `inner_lowerChainAtLevel` (`ChainNorms.lean:761`) shows $\langle \Theta_\vartheta x, \Theta_\vartheta y \rangle = [K_0 : J_\vartheta] \cdot \dim(W_{Y_m}) \cdot \langle u_0 x, u_0 y \rangle$.
2. `exists_stdLevelIndex_lastLevel_eq` (`ChainNorms.lean:710`) computes the index $[K_0 : J_\vartheta]$ using `exists_card_parabolic_blockNumber_eq` (`TriangleNorms.lean:105`): the $N_0, N_1^m, N_m$ group orders cancel identically against the parabolic indices, leaving a constant times $N(Q)^k \cdot \text{gramFactor}(\vartheta, 1)^m$.
3. Combining with `gramFactor / matrixCard = chosenFactor * twistFactor` (`NormOfChain.lean:251-253`), `exists_inner_chain_eq` (`NormOfChain.lean:222`) and `exists_adjoint_chain_comp_eq_smul_rallisProduct` (`NormOfChain.lean:313`) yield on $D.\text{targetForms}$:
   $$\Theta_\vartheta^* \Theta_\vartheta = c(\vartheta) \, c_Q^m \prod_{j=1}^m R_{j,\vartheta^j}, \qquad \|c(\vartheta)\| = C \, (Nm\, Q)^{e/2} \prod_{1 \le i < j \le m} \text{quotientRatio}(i, j, \vartheta),$$
   where $c_Q = (D.\text{descentPair }\vartheta\, 1).\text{twistFactor}$ and $R_{j,\vartheta^j} = D.\text{rallisOnGood }(D.\text{spaceY }0)\, (\vartheta^j)\, j$.
4. Meanwhile, for each single **stable-range** lift $W_j \to V_j$ ($\text{rk } V_j = r + t = 6r$), `exists_normDet_goodLift_sq_eq` (`NormOfChain.lean:132`) shows:
   $$Z_j(\vartheta^j) = (A_j c_Q)^{d_T} \det(R_{j, \vartheta^j}),$$
   because `rallisOnGood` is a spherical Hecke operator having the same determinant on $D.\text{targetForms}$ and $D.\text{goodForms}(W_j)$ (`NormOfChain.lean:140`).
5. Taking determinants of $\Theta_\vartheta^* \Theta_\vartheta$ (`exists_chainDeterminant_eq_pow_mul_prod_liftDeterminant`, `NormOfChain.lean:362`), $(c_Q^m)^{d_T}$ cancels against $\prod_{j=1}^m c_Q^{d_T}$, and dividing $\vartheta$ by $1$ cancels all unknown twist-independent constants $C, A_j$ (`exists_div_chainDeterminant_one_eq`, `NormOfChain.lean:407`, inverted at `LongForms.lean:174`):
   $$\frac{Z(1)}{Z(\vartheta)} = \left( (Nm\,Q)^{e/2} \prod_{1 \le i < j \le m} \text{quotientRatio}(i, j, \vartheta) \right)^{-d_T} \prod_{j=1}^m \frac{Z_j(1)}{Z_j(\vartheta^j)}.$$
   Since there are $\le m^2$ pairs $(i,j)$ each contributing $t$ critical $L$-ratios, `heightLe_inv_rpow_mul_prod_quotientRatio` (`NormOfChain.lean:449`) bounds the prefactor height by $m^2 t x_1$ per target dimension, which satisfies $m^2 t x_1 \le b$ (`LongForms.lean:205`)! Thus the entire chain ratio reduces to bounding the $m$ single-lift ratios $Z_j(1)/Z_j(\xi_\iota^j)$.

---

### 2.2 How `OneLift/ComparisonOperator/` Makes $\operatorname{glue}_\vartheta^* \circ \Theta_{j,\vartheta}$ Twist-Independent

Fix $1 \le j \le m$ and let $\Theta_{j,\vartheta} = D.\text{goodLift }\vartheta\, j : D.\text{goodForms}(W_j) \to (D.\text{descentPair }\vartheta\, j).\text{FormV}$, where $W_j$ has rank $r$ and $V_j = I_{r+t}$ ($t = 5r$) is definite. Note that in this section $\vartheta$ denotes a single twist ($D.\text{Twist}$, later specialized to $\xi_\iota^j$).

#### Step A: Splitting $V_j = V'' \oplus V^\circ$ and Mod-$\varpi^2$ Gluing (`GluedLattices.lean`, `GluedForms.lean`, `GluingMaps.lean`)
1. **Basis splitting (`splittingV`, `GluingMaps.lean:186`):** Split the basis of $V_j$ (`D.RowIndex ⊕ Fin D.t`) into:
   - $V''$ (`FirstFactorIndex j`, rank $r + 9m + 1$, `:106`) containing $W_j$'s indices `fixedEmb` plus padding/carrier indices `dividedEmb : CarrierIndex ↪ FirstFactorIndex j` (`:195`), with weight diagram $\mu^+ = \text{colsPlus}$ supported below $\operatorname{rk} V''$ (`hasColumnsBelow_colsPlus`, `:148`);
   - $V^\circ$ (`D.SecondFactorIndex`, rank $t - 9m - 1$, `:134`), with weight diagram $\mu^- = \text{colsMinus}$ supported below $\operatorname{rk} V^\circ$ (`hasColumnsBelow_colsMinus`, `:170`).
2. **Mod-$\varpi^2$ Glued Lattices (`DividedSplitting.exists_isGlued`, `GluedLattices.lean:793`):**
   - The theta lift $\Theta_{j,\vartheta}$ has finite datum at the chosen places $M$ given by the congruence $x \equiv \begin{pmatrix} 1 \\ 0 \end{pmatrix} \pmod{\varpi}$, where $\varpi = D.\text{piM}$ generates $\prod_{w \in M} w$, i.e., $\varpi x \equiv \varpi \iota_{O.\text{incl}} \pmod{\varpi^2}$ (`genResidue_smul_eq_inclMatrix_iff`, `GluedLattices.lean:191`).
   - On the other hand, we want to decouple $V_j$ into $V''$ (which will absorb the twist $\vartheta$) and $V^\circ$ (which will be completely twist-free!). For a choice $i : \text{ChoiceIndex } j$ carrying a matrix $\Lambda = i.1$ mod $\varpi^2$ with rows indexed by `CarrierIndex` ($3m$), we impose on $V''$ the congruence $w\, u \equiv w\, \iota_{\text{fixedEmb}} \pmod{\varpi^2}$ where $w = \begin{pmatrix} \Lambda \\ \varpi \cdot 1 \end{pmatrix}$ (`stackOverGenScalar`), and on $V^\circ$ the congruence $x^\circ \equiv \iota_z \pmod{\varpi^2}$ (`IsBlockNormalized`, `GluedLattices.lean:493`).
   - How do you bridge $x \equiv (1;0) \pmod{\varpi}$ with `IsBlockNormalized` mod $\varpi^2$? By a **lattice change** $\gamma \in G_f(V_j)$ (`DividedLattice`, `glueLattice j ϑ i` chosen once at $\vartheta = 1$, `GluingMaps.lean:223`), constructed via Hermite normal form (`exists_divisor_assoc_stackOverGenScalar`, `GluedLattices.lean:712`) and `glueMatrix` (`GluedLattices.lean:587`) so that $B D = \varpi \cdot 1$ and $\varpi \gamma^{-1} \in \mathrm{Mat}(\hat{\mathcal{O}}_E)$ satisfies:
     $$\bigl(\varpi \gamma^{-1} x \equiv \varpi \iota_{O.\text{incl}} \pmod{\varpi^2}\bigr) \iff \exists! Y \in \text{congruenceGroup},\quad x Y \text{ is } \text{IsBlockNormalized}(s)$$
     (`IsGlued.indicator_eq_sum`, `GluedLattices.lean:530`), where `congruenceGroup` $\bar{J}^1 = \{Y \in \mathrm{GL}_r(\mathcal{O}/\varpi^2) : Y \equiv 1 \pmod{\varpi}\}$ (`GluedLattices.lean:459`).
   - Note that the glued lattice $\gamma$, `congruenceGroup`, and `gluingLevel` on $V''$ **do not depend on $\vartheta$** at the chosen places, and $\gamma = 1$ at all twist places $Q$ (`GluedForms.lean:247`)!
   - Also, the second condition `exists_cols_eq_zero` (`GluedLattices.lean:521`) ensures $\varpi \gamma^{-1}$ is integral on most of $V''$ (except the $3m$ directions `dividedEmb`), bounding the $p$-adic denominator of Cartan products by $\|M\|^{-l_1}$ where $l_1 = \text{denominatorExponent}$ (`GluedForms.lean:38-41`, used in `GluingMaps.lean:607`).

#### Step B: The First Factors & Three Exchanges (`FirstFactors.lean` & `ThreeExchanges.lean`)
1. **Carrier form (`ThreeExchanges.lean:226-305`):**
   For even $m = 2e$, let $S$ be the indefinite space of signature $(2m, m)$ (`CarrierIndex`, rank $3m$). Applying the Exchange Identity **twice** (`exists_mul_stdClassSum_modKernelStdSpace_eq_one` at `:226`, conjugated onto $I_m^-$ via `exists_stdClassSum_modKernelStdSpace_neg_eq_one` at `:268`, and chained into $I_m \oplus S \leftrightarrow I_m^-$ in `exists_mul_stdClassSum_eq_carrierForm` at `:294`), a fixed **twist-free** holomorphic rapidly decreasing form $\varphi^\circ = \text{carrierForm } E\, m$ on $U(S)$ is written as:
   $$\varphi^\circ(x) = \gamma_{1,2}(\vartheta) \sum_{h \in \text{Classes}(I_{3m})} \frac{1}{\#\text{Aut}(h)} \, \text{carrierCoeff}(m, c, h) \cdot \theta^{(S, I_{3m})}_{\upsilon^m, c}[\chi \circ \det, 1](x, h),$$
   where $\|\gamma_{1,2}(\vartheta)\|^2$ is a constant over the product of two `lValueProd` factors (at $z_- = m/2$ and $z_+ = m$).
2. **Third exchange (`exists_mul_thirdExchangeLeftSide_eq_choiceFn`, `GluingMaps.lean:307`, `ThreeExchanges.lean:1034-1060`):**
   Using a fixed polynomial `paddedMinorProd j` (`FirstFactors.lean:81`, `ProductsSpan.lean:94-100`) on $(S, \tilde{W})$ where $\tilde{W} = W_j \oplus (E^j)^- \oplus E^{3m-j}$, and the dual pair $(S \oplus W^\flat, V'')$ with $W^\flat = E^{6m+1}$, the **third exchange** equates a constant multiple $c'_\vartheta$ of `thirdExchangeLeftSide ϑ j i g` with a **twist-free** integral of $\varphi^\circ$ against a theta kernel, `choiceFn j i` ($\mathsf{F}_i$, `ThreeExchanges.lean:1060, 1138`), with $|c'_\vartheta|^2 = C / \text{heckeValueProd } j\, \vartheta$ (`GluingMaps.lean:321`).
   - By `stdClassSum_thirdExchangeKernel_eq_productDatum` (`ThreeExchanges.lean:1034`), `thirdExchangeLeftSide` rewrites as a class sum on $U(V'')$ at level `rowFixingLevel` (`gluingLevel j ϑ i.1`) with the `leftSideSeries` polynomial vector (`FirstFactors.lean:78, 253`).
   - Multiplying by a single constant `firstFactorScale j` ($c'' \ne 0$, independent of $i, \vartheta, h$) makes $\varphi''_{\vartheta, i} = \text{firstFactor } j\, \vartheta\, i$ (`GluingMaps.lean:253`) **integral at all primes $l \nmid Nm(Q)$** (`weylGauge_firstFactor_le_one`, `:339`) and **exponentially bounded at all $\sigma \in \operatorname{Aut}(\mathbb{C})$ for $\vartheta = 1$** (`weylNormSq_firstFactor_le`, `:347`, from `exists_isIntegralAndSmall_leftSideSeries` in `FirstFactors.lean:33`).

#### Step C: The Gluing Map, Seesaw Identity, and Twist Independence (`GluingMaps.lean`)
Define $\text{glue}_\vartheta = \text{glue } j\, \vartheta : \text{FormTuples } j \to (D.\text{descentPair }\vartheta\, j).\text{FormV}$ (`GluingMaps.lean:359`), where `FormTuples j` is $L^2$-tuples $\zeta = (\zeta_{i, h^\circ})$ of vectors of weight $\mu^-$ indexed by $(i, h^\circ) \in \text{ChoiceIndex } j \times D.\text{SecondFactorClasses}$ (`GluingMaps.lean:89`):
$$\text{glue}_\vartheta(\zeta) := M^{l_1} \sum_{i, h^\circ} \text{stdClassSum}_{J_\Lambda}\!\left(h \mapsto \text{productForm}(\text{glueLattice } i, (h, h^\circ), \varphi''_{\vartheta, i}(h), \zeta_{i, h^\circ})\right).$$
Now compute $\langle \zeta, \text{glue}_\vartheta^*(\Theta_{j,\vartheta} y) \rangle$ for any $y \in D.\text{goodForms}(W_j)$ (`inner_adjoint_glue_goodLift_eq_integral`, `GluingMaps.lean:500`, and `conj_normalizedDescent_glue`, `:458`):
1. By adjointness of $\Theta_{j,\vartheta}$ and `normalizedDescent` (`AdjointThetaLift.lean`), $\langle \zeta, \text{glue}_\vartheta^*(\Theta_{j,\vartheta} y) \rangle = \int_{[U(W_j)]} y(g) \overline{\text{normalizedDescent}(\text{glue}_\vartheta \zeta)(g)}\, dg$.
2. Because `glueLattice i` is glued mod $\varpi^2$ (`IsGlued`), `normalizedDescent_stdClassSum_productForm` (`GluingMaps.lean:481`) splits the $(W_j, V_j)$-theta kernel over `congruenceGroup` $\bar{J}^1$ into a product of:
   - the $(W_j, V'')$-theta series $\Xi_{\vartheta, i}(g u) = \text{firstFactorPairing } j\, \vartheta\, i(g u)$ (`GluingMaps.lean:261`), and
   - the **twist-free** $(W_j, V^\circ)$-theta pairing $\langle \zeta_i, \theta^\circ(g u, \cdot) \rangle$ (`thetaKernelPairing`, `ProductsSpan.lean:728`),
   summed over $u \in \bar{J}^1$ (`GluingMaps.lean:458`).
3. Because $y \in D.\text{goodForms}(W_j)$ has principal level $J_M = J(\varpi)$ at the chosen places and $u \in \bar{J}^1$ reduces to $1 \pmod{\varpi}$, $y(g u) = y(g)$ (`goodForm_mul_liftMod_congruenceGroup`, `GluingMaps.lean:441`)! By right-invariance of the Haar measure on $[U(W_j)]$, every $u \in \bar{J}^1$ gives the **exact same integral** (`inner_adjoint_glue_goodLift_eq_sum_integral`, `GluingMaps.lean:539`):
   $$\langle \zeta, \text{glue}_\vartheta^*(\Theta_{j,\vartheta} y) \rangle = \sum_{i} M^{l_1} c_{\mathfrak{g},i} \#\bar{J}^1 \int_{[U(W_j)]} y(g)\, \Xi_{\vartheta, i}(g)\, \langle \zeta_i, \theta^\circ(g, \cdot)\rangle \, dg.$$
4. Multiply by $c'_\vartheta = \text{twistFactor } j\, \vartheta$. By the third exchange (`twistFactor_mul_firstFactorPairing`, `GluingMaps.lean:327`), $c'_\vartheta \, \Xi_{\vartheta, i}(g) = c'' \, \mathsf{F}_i(g)$, where **neither $c''$ nor $\mathsf{F}_i = \text{choiceFn } j\, i$ depends on $\vartheta$**! Therefore (`twistFactor_smul_adjoint_glue_comp`, `GluingMaps.lean:1041`):
   $$c'_\vartheta \cdot \text{glue}_\vartheta^* \circ \Theta_{j,\vartheta} = \Theta^\circ \qquad \bigl(\Theta^\circ := \text{periodLift } j = c'_1 \, \text{glue}_1^* \circ \Theta_{j,1}\bigr),$$
   which is **completely independent of the twist $\vartheta$**!

#### Step D: Why $\Theta^\circ$ Is Injective (`ProductsSpan.lean`) and $U_\vartheta$ Bounds $Z_j(1)/Z_j(\xi_\iota^j)$ (`LiftVolumeHeight.lean`)
1. **Injectivity of $\Theta^\circ$ (`periodLift_injective`, `GluingMaps.lean:1061`):** If $\Theta^\circ y = 0$, testing against tuples supported in copy $i$ kills $\int_{[U(W_j)]} y(g) \mathsf{F}_i(g) \theta^\circ(g, \cdot)\, dg = 0$ for all $i, \zeta$. By `eq_zero_of_integral_choiceFn_thetaKernelPairing` (`ProductsSpan.lean:866`), $y = 0$:
   - If $y \ne 0$, $\bar{y}$ has a peak $g$ whose first minimum $\lambda_1(g) \ge (5 b^{24})^{-1/2}$ (`ProductsSpan.lean:889-895`) avoids the cusp.
   - Near any such non-cuspidal peak, **sparse sums** (`exists_datum_norm_modKernel_sub_polyMatrixCoeff_le`, `ProductsSpan.lean:124`) approximate the real matrix coefficient $c_P$ by a $(S, \tilde{W})$-theta kernel with error $O(b^{-20 n_*})$, so a linear combination $\sum c_i \mathsf{F}_i(x h)$ approximates a fixed nonzero bounded holomorphic function $F_0(h)$ (`exists_choiceFn_approx`, `ProductsSpan.lean:47, 663-703`).
   - Meanwhile, the $(W_j, V^\circ)$ reproducing formula (`reproducing_formula_modKernel`, `ProductsSpan.lean:816`) turns the vanishing pairings into $\int y(x h) (\sum c_i \mathsf{F}_i(x h)) m_{u^\circ}(h)\, dh = 0$ (`integral_mul_sum_choiceFn_eq_zero`, `ProductsSpan.lean:789`), contradicting `norm_apply_one_le_of_forall_isPeak` (`ProductsSpan.lean:898-918`).
   - Consequently $c'_\vartheta \ne 0$ for all $\vartheta$ (`twistFactor_ne_zero`, `GluingMaps.lean:1077`) and $U^\circ := n_{\mathrm{Aut}} hk^2 |c'_1|^{-2} (\Theta^\circ)^* \Theta^\circ$ is positive definite (`LiftVolumeHeight.lean:560-569`).

2. **The Comparison Operator (`comparisonOp`, `LiftVolumeHeight.lean:202`):**
   Define
   $$U_\vartheta := n_{\mathrm{Aut}} \, hk^2 \, \text{glue}_\vartheta \circ \text{glue}_\vartheta^* \in \text{End}_{\mathbb{C}}\bigl((D.\text{descentPair }\vartheta\, j).\text{FormV}\bigr),$$
   where $n_{\mathrm{Aut}} = D.\text{chosenGroupOrder}$ and $hk = \text{hookNumberMinus } j$. It satisfies `IsComparisonOperator j (comparisonOp j)` (`LiftVolumeHeight.lean:556`):
   - **Twist identity:** $\langle \Theta_{j,\vartheta} y', U_\vartheta \Theta_{j,\vartheta} y \rangle = \rho_\vartheta \langle y', U^\circ y \rangle$ (`LiftVolumeHeight.lean:235, 570`), where $\rho_\vartheta = \frac{\text{heckeValueProd } j\, \vartheta}{\text{heckeValueProd } j\, 1} = \frac{|c'_1|^2}{|c'_\vartheta|^2}$ (`heckeValueProd_div_eq`, `:209`).
   - **Determinant factorization (`IsComparisonOperator.exists_normDet_sq_mul_det_eq`, `LiftVolumeHeight.lean:627`):** Using `normDet_sq_mul_det_compression` (`:62`) for $u = \Theta_{j,\vartheta}$ and `pr U_ϑ = liftCompression U ϑ` (`:612`),
     $$Z_j(\vartheta) \cdot \det(\operatorname{pr} U_\vartheta) = \det(U^\circ) \cdot \rho_\vartheta^{d_T} \implies \frac{Z_j(1)}{Z_j(\vartheta)} = \frac{\det(\operatorname{pr} U_\vartheta)}{\det(\operatorname{pr} U_1)} \cdot \rho_\vartheta^{-d_T}$$
     (`heightLe_liftDeterminant_ratio`, `LiftVolumeHeight.lean:777`).
   - **False-lift orthogonality (`isOrthogonalToFalseLifts_comparisonOp`, `LiftVolumeHeight.lean:256`):** Since $U_\vartheta \Theta_{j,\vartheta} y$ is a scalar multiple of $\text{glue}_\vartheta(\Theta^\circ y)$, it is orthogonal to all false lifts (`isOrthogonalToFalseLifts_glue_periodLift`, `GluingMaps.lean:1049`).
   - **$\ell$-adic integrality (`comparisonOp_mem_integralForms`, `LiftVolumeHeight.lean:409`):** Using a tight integral frame $f_a \in \text{FormTuples } j$ (`exists_tight_frame_formTuples`, `:352`, moved by rational $\delta(c)$ to be integral above $\ell$), $U_\vartheta = \sum_a n_{\mathrm{Aut}} \langle \text{glue}_\vartheta(f_a), \cdot \rangle \text{glue}_\vartheta(f_a)$ (`comparisonOp_eq_sum`, `:392`) preserves $\ell$-adic `integralForms` whenever $\ell \nmid Nm(Q)$. Hence, if $\Lambda$ clears the projection $\operatorname{pr}$ on forms integral and orthogonal to false lifts with $|\iota(\det \Lambda)| \ge \exp(-d_T r \beta_\ell)$ (`ClearsProjection`, `FitTwists.lean:173`), then $\Lambda \circ \operatorname{pr} U_\vartheta$ preserves integral lifts, so every eigenvalue has norm $\le 1$ (`norm_padic_det_liftCompression_le`, `LiftVolumeHeight.lean:654`):
     $$|\iota(\det(\operatorname{pr} U_\vartheta))| \le \exp(d_T r \beta_\ell).$$
   - **Archimedean bound at $\vartheta = 1$ (`normSqAt_comparisonOp_le`, `LiftVolumeHeight.lean:487` & `norm_map_det_liftCompression_le`, `:697`):** Because $U_1 z$ is orthogonal to false lifts, `normSqAt_starProjection_range_goodLift_le` (`LiftVolumeHeight.lean:601`, from `normSqAt_starProjection_le` in `TestedForms.lean:604`) shows projecting $U_1 z$ to $\text{range}(\Theta_{j,1})$ does not increase `normSqAt σ` for **any** $\sigma \in \operatorname{Aut}(\mathbb{C})$! Thus every eigenvalue $\alpha$ of $\operatorname{pr} U_1$ satisfies $|\sigma(\alpha)| \le \exp(3 f m b \log^2 b)$, giving $|\sigma(\det(\operatorname{pr} U_1))| \le \exp(3 d_T f m b \log^2 b)$.
   - **Hecke-value ratio height (`TwistedValueHeights.lean:1233`):** `exists_heckeValueProd_eq_mul_prod_ratio` (`:1192`) splits $\text{heckeValueProd } j\, \vartheta / \text{heckeValueProd } j\, 1$ into $Nm(Q)^e$ times the square of $k/2$ `IsMainPair` critical $L$-ratios and $5m$ `IsRamified` ratios. Each `IsMainPair` ratio has height $\le 6 \cdot \text{denominatorBudget} - \text{directionAmount}$ (`heightLe_inv_ratio`, `:1015`) via the **four-block seesaw test form** on $\text{RankOneIndex } p.z = 12 \oplus 4 \oplus 4 \oplus (2z-20)$ (`exists_isTestForm_inner_kernelForm_eq`, `:723`—block $12$ carries the jet derivative giving $-\text{directionAmount}$, block $4$ carries the twist ratio $q_2$, and blocks $4$ and $2z-20$ average over `tameChars` using multiplicative pigeonhole `exists_mul_eq_norm_map_le_norm_map_mul`, `:170` and `exists_norm_le_norm_twisted_classSum`, `:111`), while each of the $5m$ ramified pairs costs $x_1$ (`HasSmallRatios`). Squaring gives $10 m x_1 + k(6\,\text{denominatorBudget} - \text{directionAmount})$ (`heightLe_inv_heckeValueProd_div`, `:1233`).
   - Adding the height of $\det(\operatorname{pr} U_\xi)/\det(\operatorname{pr} U_1)$ to $d_T$ times the height of $\rho_\xi^{-1}$ yields (`heightLe_liftDeterminant_ratio`, `LiftVolumeHeight.lean:731`):
     $$\text{Height}\!\left(\frac{Z_j(1)}{Z_j(\xi_\iota^j)}\right) \le d_T k (\log b \cdot \text{denominatorBudget} - \text{directionAmount}) = d_T \left(\frac{f a \log^4 b}{m} - k \cdot \text{directionAmount}\right).$$

---

### 2.3 Why `FalseLifts/` Have Identically Zero $U(V^\circ)$-Theta Periods, and How `AuxiliaryForms/` Fills the Missing Dimensions

#### Part I: Vanishing of $U(V^\circ)$-Theta Periods of False Lifts (`src/New/OneLift/FalseLifts/`)

Let $\Xi \in O.\text{FormV}$ be a **false lift** at a split place $w \ne \bar{w}$ off the level $O.\text{places}$ (`falseLiftsAt` in `TestedForms.lean:589`), meaning:
1. $\Xi \in \operatorname{range}(O.\text{groupAlgAction } e_0)$ (so `hyperplaneSumsAnnihilate` holds: for any choice of rows $\lambda_v$ at the chosen places not all zero, $\bigotimes_v \sum_{s = 1 + u \lambda_v} \chi_v(\det s)^{-1} s$ kills $\Xi$, `hyperplaneSum_apply_eq_zero` at `GluingMaps.lean:843`),
2. $\Xi \in \operatorname{range}(\Theta_{j,\vartheta})^\perp$, which implies its descent $O.\text{normalizedDescent } \Xi = 0$ (`normalizedDescent_eq_zero_of_mem_orthogonal`, `GluingMaps.lean:873`), and
3. $H_w(X_*) \Xi = 0$, where $X_* = O.\text{liftHeckeRoot } w$ has modulus $|X_*| = (q^{r/2} q^{n - r - 1})^{-1}$ (`PeriodsOfFalseLifts.lean:165`).

Why do the $U(V^\circ)$-theta periods of $\Xi$ vanish identically (`sum_slice_eq_zero_of_mem_falseLiftsAt` at `GluingMaps.lean:905`, `DividedSplitting.stdClassSum_inner_productForm_eq_zero` at `PeriodsOfFalseLifts.lean:701`)?

1. **Step 1 — Bottom of the Tower (`BottomOfTower.lean:1475`):**
   - Because $O.\text{normalizedDescent } \Xi = 0$, the theta descent to $W = O.W$ of the conjugate highest-weight matrix coefficient $y_0 = \overline{\text{algFormCoeff } 1 (\text{gramForm } \zeta_0)\, \Xi}$ vanishes for the harmonic Fock vector and the block datum $\Psi_{\mathrm{bl}}$ (`blockDatum`: $x \equiv (1;0)$ at $M$, $\prod_{v \in Q} \chi_v(\det x')$ at $Q$).
   - By real convolution with a test function $\alpha$ (`lift_polyVector_blockDatum_eq_zero`, `PeriodsOfFalseLifts.lean:95`), vanishing extends from the harmonic polynomial to **all** Fock polynomials $P$.
   - Now `descentsVanish_of_hyperplaneSumsAnnihilate` (`BottomOfTower.lean:1475`) extends vanishing from $\Psi_{\mathrm{bl}}$ to **all** Schwartz–Bruhat finite data $\Psi$ supported on $O.\text{places}$ by testing small coset indicators $1_C$ around any $z \in \text{Mat}_{n \times r}(\mathbb{A}_f)$:
     - **Case 1 (`HasIntegralBlockRatio`, `BottomOfTower.lean:278, 1235`):** $z'$ (rows $O.\text{incl}$) is invertible and $z'' z'^{-1}$ is integral (and $\equiv 0$ mod $M$). Averaging translates of $1_C$ under the level group $O.\text{levelGroup}$ produces a $\Psi_1$ with the same pairing against $y_0$ that is supported in a translate of $\Psi_{\mathrm{bl}}$, hence is a scalar multiple of $\Psi_{\mathrm{bl}}(\cdot A)$, whose pairing is $0$!
     - **Case 2 (`¬HasIntegralBlockRatio`, `BottomOfTower.lean:291, 1446`):** At some place $w_0 \in M \cup Q$, there exists an **annihilating row** $l = (\lambda, \lambda')$ over $\mathcal{O}_{w_0}$ with $l z = 0$, $\lambda \not\equiv 0 \pmod{w_0}$, and $\lambda' \equiv 0 \pmod{w_0}$ if $w_0 \in Q$. For every $s = 1 + v \lambda \in \text{hyperplaneGroup } \lambda$, the integral shear `rowShear` $h_s = \begin{pmatrix} 1 + v \lambda & v \lambda' \\ 0 & 1 \end{pmatrix}$ (`BottomOfTower.lean:136`) fixes $z$ (since $l z = 0$) and acts on $\Xi$ as $\chi_{w_0}(\det s)^{-1} \bar{s}\,\Xi$ (`exists_leftMul_eq_and_blockAction_eq`, `:1385`). Summing over $s \in \text{hyperplaneGroup } \lambda$ kills $\Xi$ by `HyperplaneSumsAnnihilate` (at $M$) or by character orthogonality $\chi_{w_0} \ne 1$ (at $Q$) (`sum_blockAction_eq_zero`, `:1365`). Hence $\#(\text{hyperplaneGroup }\lambda) \cdot B(1_C, \Xi) = 0$.

2. **Step 2 — Climbing the Hyperbolic Tower (`HyperbolicPlaneStep.lean` & `PeriodsOfFalseLifts.lean:141`):**
   We climb from $W$ to $W \oplus \mathbb{H}^N$, where $N = \operatorname{rk} V''$ (`FirstFactorIndex j`) and $l = \operatorname{rk} V^\circ$ (`SecondFactorIndex`), so $n = N + l$. Note the crucial rank check:
   $$2r + 2N + 3 < n \qquad (r + t = 6r,\; N = r + 9m + 1 \implies 2r + 2(r+9m+1) + 3 < 6r \text{ since } 100m < k \le r).$$
   In `descentsVanish_add_planes` (`HyperbolicPlaneStep.lean:26-45`, applied in `descentsVanish_hyperbolicSum` at `PeriodsOfFalseLifts.lean:177`):
   - Inducting one hyperbolic plane at a time from $W_0$ to $W' = W_0 \oplus \mathbb{H}$: by Iwasawa decomposition, the zero term (constant term along the isotropic line $k$) of the theta kernel of $(W', V)$ vanishes because its descents to $W_0$ vanish (`DescentsVanish.integral_homSlice_eq_zero`, `HyperbolicPlaneStep.lean:140`).
   - Away from the zero term, where height $> 2$, Witt's theorem moves a short isotropic vector to $k$ (`exists_col_k_mem_latticeBall`, `:211`), and the difference $\theta - \theta_0$ is uniformly bounded (`exists_norm_theta_sub_zeroTerm_le`, `:284`). Thus every descent $F$ of $y_0$ to $U(W')$ is **bounded** (`DescentsVanish.bddAbove_lift`, `:342`)!
   - By Hecke transfer, $F$ inherits the Hecke equation $H_w(\overline{X_*}) F = 0$ at the split place $w$ off the level (`PeriodsOfFalseLifts.lean:167-178`).
   - **Small-root maximum principle (`eq_zero_of_heckePolyOp_eq_zero`, `HyperbolicPlaneStep.lean:81`):** What is the threshold for $H_w(X) F = 0$ on $U(W')$ of rank $m' = r + N$ to force $F = 0$? We need $q^{m'+1} |X| \le 1$, because then the $q$-binomial theorem bounds the total weight of all nontrivial coset terms $U \ne \perp$ by $\prod_{j=0}^{m'-1} (1 + q^j |X|) - 1 \le \exp(1/2) - 1 < 1$ (`:99-105`), so a bounded function satisfying $F(g) = -\sum_{U \ne \perp} c_U F(g \gamma_U)$ must be $0$ (`maximum_principle`, `:111`)!
   - Check the inequality: $|X_*| = q^{-(n - 1 - r/2)}$, while $q^{m'+1} = q^{r + N + 1}$. We have $q^{r + N + 1} \cdot q^{-(n - 1 - r/2)} \le 1 \iff \frac{3}{2} r + N + 2 \le n$, which is guaranteed by $2r + 2N + 3 < n$!
   - Equivariance of the real Weyl representation moves $y_{\zeta_0}$ across all vectors $\zeta$ (`PeriodsOfFalseLifts.lean:181-197`).

3. **Step 3 — From Vanishing Descents on $W \oplus \mathbb{H}^N$ to Zero $U(V^\circ)$-Periods (`PeriodsOfFalseLifts.lean:237, 338, 701`):**
   - Split $V = I_N \oplus I_l = V'' \oplus V^\circ$. Given a theta kernel $\theta^\circ(g, h_2)$ on $(W, I_l)$ and a point $h_1 \in U(I_N)$, choose a datum $\varphi''$ on $(W, I_N)$ with $\theta''(g, h_1) \ne 0$ (`exists_projOn_eq_pairTheta_ne_zero`, `:208`). By box-product factorization of theta kernels, $y_2(h) := \theta^{W,V}(g, h) \cdot \overline{\text{coeff } \Xi}(h\gamma)$ has vanishing descents to $\mathbb{H}^N$!
   - By `integral_blockEmb_eq_zero_of_descentsVanish` (`:309`), integrating $y_2$ over $[U(I_l)]$ kills $\int_{[U(I_l)]} \overline{\theta^\circ(g, h_2)} \cdot \text{coeff}(\Xi)((h_1, h_2)\gamma)\, dh_2 = 0$ (`integral_conj_pairTheta_mul_algFormCoeff_eq_zero`, `:237`).
   - Rewriting the integral over $[U(I_l)]$ as a class sum (`stdClassSum_gramForm_eq_zero`, `:338`) and substituting the glued-lattice Cartan product (`DividedSplitting.stdClassSum_inner_productForm_eq_zero`, `:701`), every $U(V^\circ)$-slice of $\Xi$ against $\theta^\circ(g, \cdot)$ is identically zero (`sum_slice_eq_zero_of_mem_falseLiftsAt`, `GluingMaps.lean:905`), so $\langle \Xi, \text{glue}_\vartheta(\Theta^\circ y) \rangle = 0$ (`GluingMaps.lean:1049`).

---

#### Part II: How `AuxiliaryForms/` Fills the Remaining $\le 4 d_T / b^2$ Dimensions (`src/New/Determinant/AuxiliaryForms/` & `LongForms.lean`)

Theorem A + B (`New.star_inequality`, `MainInequality.lean:97-118`) gives $n$ linearly independent target forms $y_1, \dots, y_n \in D.\text{targetForms}$ with $(1 - 4/b^2) d_T \le n$, leaving $n' = d_T - n \le \frac{4 d_T}{b^2}$ dimensions unfilled. To apply the product formula `covolume_add_index_nonneg`, we must complete $\{y_i\}$ to a full basis of $D.\text{targetForms}$ with auxiliary forms $z_1, \dots, z_{n'}$ whose lifts $\Theta_\vartheta z_i$ have:
1. Controlled $\ell$-adic denominators (after a single $\vartheta$-dependent scalar $\gamma(\vartheta)$), and
2. Controlled archimedean norms at $\vartheta = 1$, **small enough that $n' \cdot (\text{cost per form}) \le d_T \cdot b$**.

Why can't we just pick a short integral basis directly on $Y_0$ and apply $\Theta_\vartheta$? Because $Y_0$ is **indefinite**, and $\Theta_\vartheta : Y_0 \to Y_m$ is an $m$-step chain outside the stable range whose $\ell$-adic denominators and archimedean blowup on $Y_0$ are difficult to control directly!

**The Two-Grid Path Bypass (`AuxiliaryForms/`):**
1. **Start on the definite space $\tilde{Y}^m_0$ (`FirstPath.lean` & `DeepLevelVanishing.lean`):**
   Consider the two $m \times m$ grids of spaces: $(Y^a_b)$ (`z = false`) and $(\tilde{Y}^b_a)$ (`z = true`), where $\tilde{Y}^0_0 = Y_0 \oplus \langle 1 \rangle$ and $\tilde{Y}^m_0$ is **positive definite** (`LastPath.lean:20`, `FirstPath.lean:272`).
   - On the definite space $\tilde{Y}^m_0$ at deep level $\mathfrak{b} = \varpi^{\text{natB}}$, `span_isShort_eq_top_gridLevelForms` (`SpanningForms.lean:860`) constructs a spanning set of forms $\varphi \in D.\text{gridLevelForms } m$ that are **all-prime integral** and **archimedean-short** ($\text{weylNormSq}(\sigma \circ \varphi) \le \exp(x^{99} b^2)$)!
2. **Pull back to $Y_0$ via $\Theta^\flat$ and $\text{res}^\flat$ (`FirstPath.lean`):**
   - Let $\Theta^\flat = D.\text{transposedChain } 1\, \text{true } 0$ be the weighted $m$-step transposed lift down the first column $\tilde{Y}^m_0 \to \dots \to \tilde{Y}^0_0$. By `gridLevelForms_eq_map_transposedChain` (`FirstPath.lean:229`), $\Theta^\flat$ is **surjective** onto level-$\mathfrak{b}$ forms on $\tilde{Y}^0_0$ (proved by adjunction to `weightedChain`, which is injective by `IsTriangle` for `z = true`!).
   - By `exists_eq_zero_of_orthogonal_gridLevelForms` (`DeepLevelVanishing.lean:42`), there exists a single real point $g_0 \in G_\infty(\tilde{Y}^0_0)$ such that restriction to $U(Y_0)$ of $g_0$-translates of level-$\mathfrak{b}$ forms on $\tilde{Y}^0_0$ pairs nondegenerately with every nonzero form of level $J_M$ on $Y_0$.
   - Hence the restriction map $r = \text{res}^\flat : D.\text{gridLevelForms } m \to D.\text{principalForms}(Y_0)$ (`exists_isFlatRestriction_range_eq_top`, `FirstPath.lean:336`) is **surjective**, and maps the spanning short set $\{\varphi\}$ to a spanning set $\{r\varphi\}$ on $Y_0$!
   - By `IsFlatRestriction.integral_lowerChainUpTo` (`FirstPath.lean:362`), for any test form $y'$ on $Y_m$ and any $m$-fold twist $\vartheta$, the pairing $\int_{[U(Y_m)]} y' \cdot \Theta_\vartheta(r\varphi)$ equals a period on the **first path** $(\tilde{Y}^m_0 \to \tilde{Y}^0_0 \text{ then } Y_0 \to Y_m)$ (`exists_isPathDatum_first`, `:430`).
3. **Turn the Path Across the Two Grids to the Last Path (`GridPaths.lean`, `Turns.lean`, `DiagonalTurns.lean`):**
   - A `TwoGridPath` from $(m,0)$ to $(0,m)$ starts as `first m` (through $(0,0)$, mostly indefinite!) and turns square-by-square (`TwoGridPath.turn_induction`, `GridPaths.lean:24`) until it becomes `last m` (through $(m,m)$: $\tilde{Y}^m_0 \to \tilde{Y}^m_m = Y^m_m \to Y_m$).
   - **Off-diagonal turns (`Turns.lean:27`):** `Corner.IsTurn` applies `one_square_identity_of_isEdgeFamily` + `SquareLaw` (`nextDatum`), accumulating one `turnRatio i j ϑ` factor in the denominator of the proportionality constant $c(\vartheta)$.
   - **Diagonal turns (`DiagonalTurns.lean:12-25`):** At $(j,j)$, a seesaw moves the period to $S = Y^{j+1}_j = \tilde{Y}^{j+1}_j$, reverses the kernel on the extra line via `columnLineKernel` $\leftrightarrow$ `rowLineKernel`, and moves on.
   - **Result (`exists_integral_lowerChainUpTo_eq_lastPathPeriod`, `SpanningForms.lean:489`):** For all $y', \varphi, \vartheta$,
     $$[K_0 : J_\vartheta(Y_m)] \int_{[U(Y_m)]} y' \cdot \Theta_\vartheta(r\varphi) = \beta \cdot \frac{\text{lastPathPeriod}(\Psi_\vartheta, (y', \varphi))}{c(\vartheta)},$$
     where $|c(\vartheta)|$ is $(Nm\,Q)^{e/2} \prod_{i,j < m} D.\text{turnRatio } i\, j\, \vartheta$ up to a constant!
4. **Why the Last Path Gives Both Integrality & Shortness (`LastPath.lean` & `SpanningForms.lean`):**
   - **Crucially, every single space along `last m` is positive definite!** Thus all $2m$ lifts along the two halves of `last m` are finite sums over definite class sets (`exists_lastPathPeriod_mem_smul_norm_le`, `LastPath.lean:37`).
   - Testing $y'$ against a dual-weight delta form $\delta_x(v)$ (`lastPathConjDelta`, `SpanningForms.lean:615`) reads off the coordinate pairing $v \cdot \text{dualPairing} \cdot (c(\vartheta)/c(1) \cdot \Theta_\vartheta(s \cdot r\varphi))(x)$ (`exists_dualPairing_eq_mul_lastPathPeriod`, `:744`).
   - **Integrality:** Each lift on the last path has denominator cleared by `liftDenominator` (`SpanningForms.lean:85`), and the middle branching pairing is cleared by $N \le \exp(x^{99} b^2)$ (`exists_mul_lastPathPeriod_mem_embValRing`, `:282`), while `dualHook` is absorbed into the nonzero scalar $s$ (`exists_lowerChain_integral_and_weylNormSq_le`, `:776`). Thus $(c(\vartheta)/c(1)) \cdot \Theta_\vartheta(s \cdot r\varphi)$ is integral at every $p \nmid Nm(Q)$!
   - **Archimedean size at $\vartheta = 1$:** Each definite lift multiplies $\sqrt{\text{weylNormSq}}$ by at most $\exp(x^{99} b^2)$ (`sqrt_weylNormSq_lastPathKernel_le`, `:350`) and there are $\le \exp(x^{199} b^2)$ class-sum terms (`norm_lastPathPeriod_le`, `:384`), giving squared norm $\le \exp(x^{202} b^2)$ (`exists_span_short_lifts_eq_top`, `:884`)!
   - Projecting onto $D.\text{targetForms}$ via `goodProjTranslate 1` (`LongForms.lean:105-114`), since $x^{99} + x^{202} b^2 \le 2 x_1^2 b^2$, we obtain a spanning set of auxiliary forms `IsAuxiliaryForm γ` (`LongForms.lean:56`) with squared norm $\le \exp(2 x_1^2 b^2)$ and scalar height $\le m^2 t x_1 \cdot 2 \le b$ (`LongForms.lean:243-248`).
5. **Absorbing the Completion Cost (`mul_completion_cost_le`, `LongForms.lean:133`):**
   Each auxiliary form costs at most $2 x_1^2 b^2 + b$ (`LongForms.lean:227`). Because $n' \le \frac{4}{b^2} d_T$ and $4(2 x_1^2 + b^{-1}) \le b$ (`LongForms.lean:139`),
   $$n' (2 x_1^2 b^2 + b) \le \frac{4}{b^2} d_T (2 x_1^2 b^2 + b) = d_T \cdot 4(2 x_1^2 + b^{-1}) \le d_T \cdot b.$$
   The $b^{-2}$ in the codimension bound $(1 - 4/b^2) d_T \le n$ **cancels the $b^2$** in the auxiliary forms' log-norm exponent $2 x_1^2 b^2$! The remaining $2 d_T b$ (one $d_T b$ from completion, one $d_T b$ from $\text{height}(|c(\vartheta)|^{-2})$) is absorbed into $3 f a \log^4 b$ (`LongForms.lean:284-286`).

---

## 3. Classical Barriers Bypassed & Tight Constants

### 3.1 Textbook Machinery Skipped & How the Custom Bypass Avoids Every Classical Trap

| Classical Barrier / Textbook Machinery | Why Classical Proof Fails Here | How `OneLift/` + `Determinant/` Bypasses It |
|---|---|---|
| **1. Regularized Siegel–Weil / Rallis inner product formula below Weil's convergent range** (Kudla–Rallis, Gan–Qiu–Takeda) | On $Y_0 \to Y_1 \to \dots \to Y_m$, the intermediate steps and characters sit outside the convergent range, and $m$ different twists $\vartheta, \dots, \vartheta^m$ appear. Regularized theta integrals introduce Arthur-type truncation / Eisenstein poles and uncomputed local constants. | **Triangle of Lifts + Finite Square Law (`ChainNorms.lean`, `SquareLaw.lean`):** Never regularizes divergent theta integrals. Works entirely inside the convergent/cuspidal range of `IsSquare` (`OneSquare.lean:879`) via the ramified Exchange Theorem, propagating `nextDatum` across squares (`SquareLaw.sum_eq_nextDatum`). In the adjoint squares, equal ranks cancel `lValueProd` completely (`exists_squareLaw_triangleReversedLift`, `ChainNorms.lean:299`). |
| **2. Local $p$-adic / archimedean pullbacks of Siegel Eisenstein series at ramified places $Q$** (Explicit doubling-method local zeta integrals) | Computing the exact local doubling zeta integrals at arbitrary ramified primes $w \in Q$ for high-rank $U(W_j) \to U(V_j)$ and arbitrary tame characters $\vartheta$ is notoriously messy and level-dependent. | **Mod-$\varpi^2$ Lattice Gluing + Three Exchanges (`GluingMaps.lean`, `ThreeExchanges.lean`, `GluedLattices.lean`):** Pushes the twist $\vartheta$ out of $V^\circ$ and into $V''$ using a single Hermite-form lattice change $\gamma$ mod $\varpi^2$ (`exists_isGlued`). Then three applications of the Exchange Identity turn the $(W_j, V'')$ theta series into a scalar $c'_\vartheta$ times a twist-free function $\mathsf{F}_i$, so $c'_\vartheta \operatorname{glue}_\vartheta^* \Theta_{j,\vartheta} = \Theta^\circ$ bypasses local zeta integrals on $W_j \times V_j$ altogether! |
| **3. Multiplicity-one / explicit spectral decomposition for $U(V_j)$ at level $J_\vartheta$** | The target space $V_j$ is definite of rank $6r$; at ramified level $J_\vartheta$, projecting onto $\operatorname{range}(\Theta_{j,\vartheta})$ mixes lifts with non-lifts ("false lifts") that have the same central idempotent $e_0$ and the same unramified Hecke eigenvalue $H_w(X_*)=0$ at one split place $w$ (or even many). | **Hyperbolic-Tower Period Vanishing (`FalseLifts/`):** Instead of needing strong multiplicity-one or endoscopic classification for $U(6r)$, `TestedForms.lean:604` proves that *any* form orthogonal to false lifts projects to $\operatorname{range}(\Theta_{j,\vartheta})$ without increasing `normSqAt σ`! And `FalseLifts/` proves via $q^{m'+1} |X_*| \le 1$ on $W_j \oplus \mathbb{H}^N$ that false lifts have zero $U(V^\circ)$-theta periods, so $\operatorname{glue}_\vartheta(\Theta^\circ y)$ automatically lies in $(\text{FalseLifts})^\perp$. |
| **4. Constructing a global short integral basis on an indefinite unitary group $U(Y_0)$** | $U(Y_0)$ is non-compact (indefinite), so Minkowski/LLL lattice reduction of automorphic forms directly on $Y_0$ fails to control $\Theta_\vartheta$ twisted integrality and $\sigma$-conjugates across all $m$ steps. | **Two-Grid Path Transfer (`AuxiliaryForms/`):** Constructs short integral forms on the **compact/definite** space $\tilde{Y}^m_0$ (`SpanningForms.lean:860`), pushes them to $Y_0$ via $\text{res}^\flat \circ \Theta^\flat$, and transfers the inner product across $m^2$ grid squares to the all-definite `last m` path (`DiagonalTurns.lean`, `LastPath.lean`), where every lift is a finite definite class sum! |
| **5. Non-vanishing of single-lift inner products / basis problem via Arthur packets** | Proving $\Theta^\circ$ is injective requires showing good forms on $W_j$ cannot be orthogonal to all $\mathsf{F}_i \theta^\circ$. | **Sparse Sums + Non-Cuspidal Peaks (`ProductsSpan.lean`):** Uses analytic peak non-cuspidality ($\lambda_1(g) \ge (5 b^{24})^{-1/2}$) and `exists_datum_norm_modKernel_sub_polyMatrixCoeff_le` to show a linear combination of $\mathsf{F}_i$ approximates a nonzero model function $F_0$ to error $O(b^{-19 n_*})$, defeating the reproducing formula on $(W_j, V^\circ)$ by pure positivity. |

### 3.2 Genuinely Tight Numerical & Asymptotic Constants

1. **The $4 / b^2$ Codimension Threshold vs. $2 x_1^2 b^2$ Auxiliary Cost (`LongForms.lean:133-143`):**
   - Auxiliary forms have log squared-norm $\le 2 x_1^2 b^2$ (coming from `D.x ^ 99 + D.x ^ 202 * D.b ^ 2 ≤ 2 * D.x₁ ^ 2 * D.b ^ 2` at `LongForms.lean:110`, since $x^{202} \ll x_1^2$ in `Data.Sizes` where $x^{10^6} \le x_1$).
   - Notice $b^2$ is **genuinely tight** against $n' \le (4 / b^2) d_T$: if the codimension fraction were $O(1/b)$ instead of $O(1/b^2)$, the completion cost would be $\Omega(d_T x_1^2 b)$, blowing up the error budget $3 f a \log^4 b$ (remember $x_1^{10^6} \le b$, whereas $a = x b$, so $x_1^2 b \gg a \log^4 b$!). It is specifically the $b^{-2}$ factor in Theorem B (`enough_forms`, `MainInequality.lean:100`) that reduces $2 x_1^2 b^2$ to $8 x_1^2 \le b \ll f a \log^4 b$!

2. **The Rank Margin $2r + 2N + 3 < n$ in the Hyperbolic Tower (`GluingMaps.lean:918`, `PeriodsOfFalseLifts.lean:147`, `HyperbolicPlaneStep.lean:83`):**
   - `eq_zero_of_heckePolyOp_eq_zero` (`HyperbolicPlaneStep.lean:83, 99-105`) requires $q^{m'+1} |X_*| \le 1$ so that $\prod_{j=0}^{m'-1}(1 + q^j |X_*|) \le e^{1/2} < 2$.
   - Here $m' = r + N$ (at the top of the tower $W_j \oplus \mathbb{H}^N$) and $|X_*| = q^{-(n - r/2 - 1)}$, giving $\frac{3}{2} r + N + 2 \le n$, strengthened cleanly to $2r + 2N + 3 < n$ (`GluingMaps.lean:918`).
   - With $N = \operatorname{rk} V'' = r + 9m + 1$ (`GluingMaps.lean:106`) and $n = r + t = 6r$, the constraint is $4r + 18m + 5 < 6r \iff 18m + 5 < 2r$ (satisfied with huge room by $100m + 9 < k \le r$, `GluingMaps.lean:135`). Note that $t = 5r$ is chosen large enough to absorb both $V''$ ($r + 9m + 1$) and $V^\circ$ ($> 2r$, needed for reproduction `2 * r < rk V°` in `ProductsSpan.lean:804`) while keeping $2r + 2N + 3 < r + t$.

3. **The $6\text{-vs-}3$ Denominator Budget Coefficient (`TwistedValueHeights.lean:1017`, `LiftVolumeHeight.lean:764-766`):**
   - Each `IsMainPair` contributes height $\le 6 \cdot \text{denominatorBudget} - \text{directionAmount}$ (`TwistedValueHeights.lean:1017`):
     - $1 \cdot \text{denominatorBudget}$ from `mainPair` projection (`:1064`),
     - $2 \cdot \text{denominatorBudget}$ from $c_0 \overline{c_0}$ (`:1084`),
     - $2 \cdot x_1 \le 2 \cdot \text{denominatorBudget}$ from $q_2(\vartheta)^{-2}$ (`:1099-1101`),
     - $+1 \cdot \text{denominatorBudget}$ slack from `mainPair` vs `heightLe_norm_trivialLift_sq` (`:1098-1101`, which contributes $-\sum_\tau \text{jetSize} + \sum_\tau \text{primeSum}$ netting $-\text{directionAmount}$).
   - There are $k/2$ main pairs (`exists_heckeValueProd_eq_mul_prod_ratio`, `:1195`), squared in `heckeValueProd` (`:1199`), giving $k(6 \cdot \text{denominatorBudget} - \text{directionAmount})$ (`:1235`).
   - Adding $D.r \cdot \text{denominatorBudget}$ from `ClearsProjection` (`LiftVolumeHeight.lean:753`) plus $3 A = 3 f m b \log^2 b$ (`:751`) + $10 m x_1$ (`:765`) must stay below $k \log b \cdot \text{denominatorBudget}$ (`:764-766`), which works because $\log b \gg 7$ and $k = r + 1 - m \sim r$ while $D.r \le k + m$ and $f m b \log^2 b \ll f a \log^3 b$.

4. **The Error Budget `3 f a log^4 b` in Theorem C (`LongForms.lean:277`):**
   - `heightLe_chainDeterminant_one_div` (`LongForms.lean:196`) loses $d_T (b + f a \log^4 b - \text{mainAmount})$.
   - `mul_completion_cost_le` (`:135`) loses $d_T b$, and `b ≤ f a log^4 b` (`:284`).
   - Thus the total absorbed loss per dimension is $b + f a \log^4 b + b \le 3 f a \log^4 b$ (`:277`).

5. **Sparse Sum Exponents in `ProductsSpan.lean:124-136, 910-918`:**
   - Threshold $\lambda_1(g)\lambda_1(g') \ge b^{-13}$ vs. separation $b^6$, giving error $b^{-20 n_*}$ with $n_* = 2 f t^3$, against growth $(4 b^{n_*} + 1) \cdot 2 < b^{2 n_*} \le b^{19 n_*}$. Very comfortable slack once $b > 10$.

---

## 4. Community & Audit Takeaways

### 4.1 What a Sceptical Number Theorist Will Question First (and Exact Lean Answers)

1. **"Wait — $\operatorname{glue}_\vartheta^* \circ \Theta_{j,\vartheta}$ depends on $\vartheta$ at the twist places $Q$ and via the theta-kernel characters. How could $c'_\vartheta \, \operatorname{glue}_\vartheta^* \circ \Theta_{j,\vartheta}$ really be twist-independent?!"**
   - **Answer (`GluingMaps.lean:458, 539, 1041`):** `glue j ϑ` uses a lattice $\gamma$ (`glueLattice j ϑ i`) that is **trivial ($=1$) at all places of $Q$** (`GluedForms.lean:247`) and whose mod-$\varpi^2$ congruence at $M$ is fixed once at $\vartheta = 1$. In `normalizedDescent_stdClassSum_productForm` (`GluingMaps.lean:481`), the $(W_j, V_j)$ theta kernel splits into a $(W_j, V'')$-theta series $\Xi_{\vartheta, i}$ carrying **all** the $Q$-dependence and $\vartheta$-characters (`firstFactorChar_mul_upsilonU1_zpow`, `GluingMaps.lean:427`), multiplied by a $(W_j, V^\circ)$-kernel $\theta^\circ$ that has **no** $\vartheta$ and **no** $Q$ (`thetaKernelPairing`, `ProductsSpan.lean:728`). Averaging over `congruenceGroup` $\bar{J}^1$ leaves $y \in \text{goodForms}$ invariant (`:441`), and the third exchange (`twistFactor_mul_firstFactorPairing`, `GluingMaps.lean:327`) collapses $\Xi_{\vartheta, i}$ to $c'^{-1}_\vartheta c'' \mathsf{F}_i$.

2. **"How do you know $c'_\vartheta \ne 0$ and $\ker(\operatorname{pr} U_\vartheta) = 0$? Couldn't $\Theta^\circ$ or $U^\circ$ vanish?"**
   - **Answer (`GluingMaps.lean:1061, 1077`, `ProductsSpan.lean:866`, `LiftVolumeHeight.lean:634-637`):** `periodLift_injective` (`GluingMaps.lean:1061`) proves $\Theta^\circ$ is injective via `eq_zero_of_integral_choiceFn_thetaKernelPairing` (`ProductsSpan.lean:866`). Since $D.\text{targetDim} > 0$, there exists $y \ne 0$, so $c'_\vartheta \cdot \text{glue}_\vartheta^*(\Theta_{j,\vartheta} y) = \Theta^\circ y \ne 0 \implies c'_\vartheta \ne 0$ (`twistFactor_ne_zero`, `GluingMaps.lean:1077`), and $U^\circ \propto (\Theta^\circ)^* \Theta^\circ$ is strictly positive definite, so $\det(U^\circ) \ne 0$ (`LiftVolumeHeight.lean:636`) and $\det(\operatorname{pr} U_\vartheta) \ne 0$ (`:749`).

3. **"What if $\beta = 0$ in `exists_integral_lowerChainUpTo_eq_lastPathPeriod` (`SpanningForms.lean:489`)? Doesn't `s = D.dualHook * N / β` blow up?"**
   - **Answer (`SpanningForms.lean:796-816`):** No! Look at `SpanningForms.lean:796-797`: `let s := if β = 0 then 1 else D.dualHook * N / β` and `let ε := if β = 0 then 0 else 1`. If $\beta = 0$, then *every* pairing of `lowerChain ϑ (r φ)` vanishes, so $s = 1$ makes every pairing $0 = D.\text{dualHook} \cdot 0$, which is trivially $p$-integral and small! (And of course, since `lowerChainAtLevel` is injective and `r` is surjective, $\beta$ isn't actually $0$, though the proof doesn't even need $\beta \ne 0$!)

4. **"In `normSqAt_starProjection_le` (`TestedForms.lean:604`), you project orthogonally for $\sigma = 1$, yet you claim `normSqAt (Z.starProjection y) σ ≤ normSqAt y σ` for EVERY $\sigma \in \operatorname{Aut}(\mathbb{C})$! Since $\sigma$ does not preserve the $\sigma=1$ inner product, isn't that false in general?"**
   - **Answer (`TestedForms.lean:579-632`):** It would be false for a general subspace $Z$, **and that is why false lifts are so powerful**: `mem_sup_ker_sup_range_of_isOrthogonalToFalseLifts` (`TestedForms.lean:579`) decomposes $y = z + x$ with $z \in Z$ and $x \in \ker(e_0) + \operatorname{range}(H_w(X_*))$. Because $e_0$ is a central idempotent (`innerAt_groupAlgAction`, `:507`) and $H_w(X_*)$ is normal for `innerAt σ` at **every $\sigma$** (`innerAt_heckePolyOnForms_eq_zero`, `:531`), $x$ is `innerAt σ`-orthogonal to $Z$ for **every $\sigma \in \operatorname{Aut}(\mathbb{C})$** simultaneously (`h_orth`, `:617-625`)! Hence $z$ is simultaneously the $\sigma=1$ orthogonal projection of $y$ *and* $\sigma$-orthogonal to $x$, so Pythagoras at $\sigma$ (`normSqAt_le_add_of_innerAt_eq_zero`, `:565`) gives $\|z\|_\sigma^2 \le \|z+x\|_\sigma^2 = \|y\|_\sigma^2$.

5. **"In `ChainNorms.lean`, how do the $m$ different twists $\vartheta, \vartheta^2, \dots, \vartheta^m$ collapse into single-lift Rallis factors without mixing up the moduli $Q(\vartheta^j)$?"**
   - **Answer (`FitTwists.lean:40`, `NormOfChain.lean:376`, `ChainNorms.lean:48`):** $\vartheta$ is an `MFoldTwist`, meaning $\psi_w^n \ne 1$ for **every** $w \in Q$ and every $1 \le n \le m$. Thus $\vartheta^1, \vartheta^2, \dots, \vartheta^m$ all have the **exact same ramified prime set $Q$**, hence the same `twistModulus` and the same `twistFactor` $c_Q$ (`NormOfChain.lean:374-376`), allowing clean cancellation of $c_Q^{m d_T}$.

6. **"When gluing mod $\varpi^2$ (`GluedLattices.lean`), couldn't `congruenceGroup` fail to preserve the level of `goodForms`?"**
   - **Answer (`GluingMaps.lean:441`):** Every $u \in \text{congruenceGroup}$ satisfies $u \equiv 1 \pmod{\varpi}$ (`reduceAt_liftMod_congruenceGroup`, `GluedLattices.lean:476`), whereas `D.goodForms` are fixed by the **principal** level $J(\varpi)$ at the chosen places (`principalForms`). So `goodForm_mul_liftMod_congruenceGroup` holds identically.

---

### 4.2 Architectural & `TauCeti ShortGRH` Extraction Opportunities

1. **Pure Finite Linear Algebra / Square Law (`src/New/Determinant/Chain/SquareLaw.lean` & `TriangleNorms.lean`):**
   - `SquareLaw.lean` (`SquareLaw`, `nextDatum`, `SquareLaw.sum_eq_nextDatum`, `SquareLaw.exists_sum_matrixFourier_eq_sum_nextDatum`) and `TriangleNorms.lean` (`IsTriangle`, `HasSquareModuli`, `weightedChain`, `IsTriangle.exists_inner_weightedChain_eq`) are **100% domain-agnostic**: they depend only on finite matrices over a commutative ring, finite Fourier transforms, and finite-dimensional complex inner product spaces—no adeles, no CM fields, no theta functions!
   - Both files are prime candidates for standalone extraction into `Lib/General/` or `TauCeti` as reusable linear-algebraic machinery for commuting-square determinant factorizations.

2. **Hermite-Form Mod-$\varpi^2$ Lattice Gluing (`src/New/OneLift/ComparisonOperator/GluedLattices.lean:558-850`):**
   - The core equivalence `isBlockNormalized_mul_iff` / `exists_isGlued` (relating $x \equiv (1;0) \pmod{\varpi}$ on a split space after lattice change $\gamma$ to block-normalized conditions mod $\varpi^2$ up to a unique element of $1 + \varpi \operatorname{Mat}_r$) is pure `IsValuationPair` / Hermite normal form linear algebra over $\hat{\mathcal{O}}_E / \varpi^2$. Isolating the abstract $\mathcal{O}/\varpi^2$ splitting lemma into `Lib/General/LinearAlgebra/HermiteForm.lean` would shrink `GluedLattices.lean` substantially.

3. **Abstract `normDet` Compression & Eigenvalue-Product Height Machinery (`src/New/OneLift/LiftVolumeHeight.lean:59-96`):**
   - `normDet_sq_mul_det_compression` (`:62`) and `norm_map_det_le_pow` (`:84`) are clean general linear-algebra / normed-field lemmas about compressions $p \circ T|_{u(U)}$ and eigenvalue bounds under arbitrary ring homomorphisms $\mathbb{C} \to K$, ready for `Lib/General/LinearAlgebra/`.

4. **Small-Root Maximum Principle on Spherical Hecke Modules (`src/New/OneLift/FalseLifts/HyperbolicPlaneStep.lean:81-112`):**
   - `eq_zero_of_heckePolyOp_eq_zero` proves that any bounded spherical function on $U(W')$ killed by $H_w(X)$ with $q^{m'+1}|X| \le 1$ is identically zero via the $q$-binomial theorem. This is a clean, self-contained spectral-gap lemma on unitary Hecke modules.

5. **Two-Grid Combinatorics (`src/New/Determinant/AuxiliaryForms/GridPaths.lean`):**
   - `GridPath` and `TwoGridPath` (`turn_induction` from `first m` to `last m` across $m^2$ unit squares) is pure combinatorics with zero adelic imports (`public import Lib.Speed` only, `:3`), already cleanly decoupled from the analytic/arithmetic `Turns.lean` and `DiagonalTurns.lean`.
