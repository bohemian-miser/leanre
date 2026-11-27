# Deep Mathematical Reader: `New/Derivatives/` (Formal Groups, Vacuum, Divisibility, 12-Copy Sharpness) & `New/UpperBound/ElementaryDivisors/`

Target repository: `/usr/local/google/home/rop/github-personal/leanre/data/rh_grh` (`src/New/`)  
Scope: **33 Lean files (21,055 lines)** across `src/New/Derivatives/` (23 files) and `src/New/UpperBound/ElementaryDivisors/` (10 files), together with their exact callers in `New/UpperBound/` (`Kernels/`, `Divisibility/`, `Size/`), `New/OneLift/`, `New/Determinant/Twist/`, and `New/Reduction/`.

---

## 1. Engine Architecture & Entry/Exit Interface

### 1.1 High-Level Data Flow into `(⋆)`

The two pillars examined here supply the two opposing $p$-adic halves of the main inequality `New.star_inequality` (`src/New/Reduction/MainInequality.lean:160` area, combining Theorems A, B, and C):

```
                ┌────────────────────────────────────────────────────────────┐
                │            src/New/Derivatives/Vacuum/ & FormalGroup/      │
                │  TightFrames + ShortVectors + IntegralVacuum + Scale       │
                │  + StandardDataProducts + JetIntegrality                   │
                │  FormalGroup/{Resolution, FrobeniusCongruence, Exponent,   │
                │               ThetaProducts}                               │
                └──────────────┬──────────────────────────┬──────────────────┘
                               │                          │
        (Upper side: jets)     │                          │ (Lower side: 12-copy sharpness)
                               ▼                          ▼
 ┌──────────────────────────────────────────┐  ┌────────────────────────────────────────────┐
 │  Divisibility/{NormalForm,NullFrames,    │  │ Sharpness/{OneCurve,LeastValuation,        │
 │                Count}.lean               │  │            Couplings,NearPairs,Cases,       │
 │  -> Vacuum/Divisibility.lean:            │  │            BoundAttained}.lean              │
 │     norm_jet_jetSeries_le_pow (:107)     │  │ -> BoundAttained.lean:456:                 │
 │     exists_hasNormalForm_jetSeries (:177)│  │    exists_rpow_neg_localPrimeSumTotal_le_  │
 │     norm_jet_minorProd_jetSeries_le(:222)│  │    norm_coeff                              │
 │     norm_schurJet_jetSeries_le_          │  └──────────────────────┬─────────────────────┘
 │       of_charges (:253)                  │                         │
 └──────────────────┬───────────────────────┘                         │
                    │                                                 ▼
      ┌─────────────┴─────────────┐                 ┌───────────────────────────────────────┐
      ▼                           ▼                 │ New/OneLift/HeckeValues/              │
┌────────────────────┐  ┌────────────────────────┐  │   TwistedValueHeights.lean:883, 1015, │
│ Kernels/           │  │ Divisibility/          │  │   1235                                │
│ ThetaLiftGauge.lean│  │ ValuationAtNonSplit    │  │ -> LiftVolumeHeight.lean:731          │
│ :324, 350          │  │ Primes.lean:346        │  │ -> Determinant/Twist/LongForms.lean:  │
└─────────┬──────────┘  └──────────┬─────────────┘  │    integral_forms_long (:274, Thm C)  │
          │                        │                └─────────────────┬─────────────────────┘
          │   (Exceptional inert   │                                  │
          │    primes collision)   │                                  │
          ▼                        ▼                                  │
┌────────────────────────────────────────────────┐                    │
│ UpperBound/ElementaryDivisors/                 │                    │
│ FrobeniusCycle.elementary_divisors (:1181)     │                    │
│   -> Divisibility/HeckeEdges.lean:778          │                    │
│   -> Divisibility/MarkOperator.lean:356        │                    │
│   -> Divisibility/LocalDivisibility.lean:351   │                    │
└────────────────────┬───────────────────────────┘                    │
                     │                                                │
                     ▼                                                │
┌────────────────────────────────────────────────┐                    │
│ New/Reduction/ShortAndEnough.lean              │                    │
│  Theorem A: span_short_integralRamified_eq_top │                    │
│             (:202), indexLe_normalizedPoincare │                    │
│             (:324)                             │                    │
│  Theorem B: exists_le_finrank_iSup_range_      │                    │
│             normalizedPoincare (:361)          │                    │
│  + Size/ArchimedeanSize.lean:187               │                    │
└────────────────────┬───────────────────────────┘                    │
                     │                                                │
                     └───────────────────────┬────────────────────────┘
                                             ▼
                      ┌──────────────────────────────────────────────┐
                      │   New/Reduction/MainInequality.lean          │
                      │   star_inequality: m · rem ≤ f · a · log⁵ b  │
                      │   (directionAmount cancels identically)      │
                      └──────────────────────────────────────────────┘
```

### 1.2 Exact Exported Theorems & Verified Callers

#### A. Upper-Bound Jet & Divisibility Exports (`New/Derivatives/Vacuum/`)
1. `New.Parameters.norm_intVacuum_le_one` (`src/New/Derivatives/Vacuum/IntegralVacuum.lean:457`)
   - Statement: For `x : n → 𝔸f (P.E s)`, every prime `p` with `[Fact p.Prime] [PadicPlace p]` sees `‖ι_p (intVacuum x)‖ ≤ 1` (boundedness at finite places of the normalized vacuum `θ°`).
   - Caller: `src/New/Derivatives/Vacuum/StandardDataProducts.lean:340`.
2. `New.Parameters.norm_jet_jetSeries_le_one` (`src/New/Derivatives/Vacuum/Divisibility.lean:64`) & `New.Parameters.norm_jet_jetSeries_le_pow` (`src/New/Derivatives/Vacuum/Divisibility.lean:107`)
   - Statement: If `f ∈ standardData V 1` (the $\mathcal{O}_E$-span of integral vacuum translates at finite places) and `‖ι_p (c / (star δ * d))‖ ≤ 1`, then the Schur/Taylor jet series `(V.jetSeries (c * P.jetScale s) f)` has every multi-index derivative coefficient `l` bounded in `ℂ_[p]` by `‖ι_p (c / (star δ * d))‖ ^ (∑ τ, (l τ).sum)` (and `≤ 1` when `c = star δ * d * P.jetScale s`).
   - Caller: `src/New/UpperBound/Kernels/ThetaLiftGauge.lean:324` (`omega_mem_raises_of_schurJet_le` / gauge integrality at all primes).
3. `New.Parameters.exists_hasNormalForm_jetSeries` (`src/New/Derivatives/Vacuum/Divisibility.lean:177`)
   - Statement: At any non-split prime `p` (`chiK P.d p ≠ 1`), for `f ∈ standardData V 1` and `‖ι_p c‖ ≤ 1`, there exist a uniformizer root `ϖ : ℂ_[p]` with `‖ϖ‖ = p ^ (-ρ_p)` and a series `l` over `Fin N₀` such that `(V.jetSeries (c * P.jetScale s) f)` is in `V.HasNormalForm p ϖ l`.
   - Internal callers: `norm_jet_minorProd_jetSeries_le` (`:232`) and `norm_schurJet_jetSeries_le_of_charges` (`:270`).
4. `New.Parameters.norm_jet_minorProd_jetSeries_le` (`src/New/Derivatives/Vacuum/Divisibility.lean:222`)
   - Statement: Bounds the `ℂ_[p]`-norm of any height-`1` minor-product jet of `(V.jetSeries (c * P.jetScale s) f)` at non-split `p` by `p ^ (-(predictedDivisibility ...) + |Φ| * N^3 * (1 + logb p (max (boxes κ N) 1)))`.
   - Caller: `src/New/UpperBound/Kernels/ThetaLiftGauge.lean:350`.
5. `New.Parameters.norm_schurJet_jetSeries_le_of_charges` (`src/New/Derivatives/Vacuum/Divisibility.lean:253`)
   - Statement: Upgrades `norm_jet_minorProd_jetSeries_le` from minor-products to full `schurJet` derivatives (`rowFilling`, `colFilling`) using arbitrary non-split `p` charges `charge : Φ → ℕ → n → ℕ` (exempt pairs `(τ, b)` must satisfy `charge τ b = 0` or `charge partner b = 0`), paying an error term bounded via `exists_norm_schurJet_le_norm_jet_minorProd` (`src/New/Derivatives/Divisibility/Count.lean:805`).
   - Caller: `src/New/UpperBound/Divisibility/ValuationAtNonSplitPrimes.lean:346` (`IsMarked.ω_ofSplitPlaces_mem_raises` at `:316`), which feeds `LocalDivisibility.lean` and Theorem A (`ShortAndEnough.lean:309`).

#### B. Sharpness Export (`New/Derivatives/Sharpness/BoundAttained.lean`)
6. `New.Data.exists_rpow_neg_localPrimeSumTotal_le_norm_coeff` (`src/New/Derivatives/Sharpness/BoundAttained.lean:456`)
   - Statement: At any prime `p` (`Fact p.Prime`, `[PadicPlace p]`), for the trivial/main modulus `𝔪 = (D.piM : 𝓞 P.K)` (norm `D.M`, coprime to `p`), there exist an indicator datum `y₀` in `D.twelveSpace` (`Hom(D.E, D.E¹²)`) and a scalar multiplier `t : ℂ` such that:
     - `‖σ t‖ ≤ exp (D.f * D.m / D.k * D.b)` for all `σ : Gal(ℂ / P.K)`,
     - `t • θ_{𝔪}(y₀)` is finite-place integral (coming from `D.exists_le_norm_coeff_indicatorDatum` at `:352` and `D.norm_map_mul_intVacuum_le` at `:397`), and
     - a single jet coefficient of `t • y₀` has $p$-adic norm at least `p ^ (-D.localPrimeSumTotal p) · ...` (matching the exact `localPrimeSumTotal p = ∑_σ s_p(κ(σ), σ)` inside `D.gain p`).
   - Caller: `src/New/OneLift/HeckeValues/TwistedValueHeights.lean:883`, producing `heightLe_inv_ratio` (`:1015`, `HeightLe (6 * D.denominatorBudget - D.directionAmount)`) and `heightLe_inv_heckeValueProd_div` (`:1235`), which enters `New/OneLift/LiftVolumeHeight.lean:763` (`heightLe_liftDeterminant_ratio` at `:731`) and finally **Theorem C** (`integral_forms_long` at `src/New/Determinant/Twist/LongForms.lean:274`).

#### C. Elementary Divisors Export (`New/UpperBound/ElementaryDivisors/`)
7. `New.FrobeniusCycle.elementary_divisors` (`src/New/UpperBound/ElementaryDivisors/ElementaryDivisorTheorem.lean:1181`)
   - Statement: Given a `FrobeniusCycle N W embValRing` with `T.p` non-unit in `embValRing`, rank `k`, degree `n`, parahoric depth `r`, proportion `θ ∈ (0, 1]` satisfying `T.IsLargeDegree k n r θ`, and an `EdgeCoordinates` system over `X` with `EdgeHecke` axioms, the edge Hecke operator `f` preserves the integral module `Y = (X × I → embValRing)` and satisfies
     ```lean
     IsOntoUpToColength (T.p : embValRing) f.range m Y
       ((3 * T.divisorConstant k n r + θ * m) * (Nat.card X * Nat.card I))
     ```
     for all `m : ℕ`, where `I = Exponents N k n`.
   - Callers:
     - `src/New/UpperBound/Divisibility/HeckeEdges.lean:778` (`isOntoUpToColength_scaledHeckeOperator_of_frobeniusCycle`)
     - `src/New/UpperBound/Divisibility/MarkOperator.lean:356` (`IsMarked.isOntoUpToColength_scaledHeckeOperator`, setting `θ = 1 / (m² f)`)
     - `src/New/UpperBound/Divisibility/LocalDivisibility.lean:341, 351` (`IsMarked.isOntoUpToColength_prod_scaledHeckeOperator_pow`), directly entering Theorem A (`New/Reduction/ShortAndEnough.lean:309`).

---

## 2. Step-by-Step Mathematical Walkthrough

### 2.1 Height-2 Formal Group Divisibility at Non-Split Primes (`FormalGroup/` + `Divisibility/`)

The first core question is: **how does the CM elliptic curve's height-2 formal group over $K = \mathbb{Q}(\sqrt{-d})$ force extra $p$-adic jet divisibility beyond the trivial Legendre factorial bound $\frac{l}{p-1}$?**

#### Step 1: Theta series and Frobenius congruence (`Resolution.lean`, `FrobeniusCongruence.lean`)
Fix the CM lattice $\mathcal{O}_K \subset \mathbb{C}$ with odd prime discriminant $-d$ (`d ≡ q₀/2 - 1 mod q₀`, so $d \equiv 3 \pmod 4$) and normalized Weierstrass/Jacobi theta function $\theta(z)$ associated to `CMLattice`. Over $\mathbb{C}_p$ at a non-split prime $p$ ($\chi_K(p) \neq 1$, hence $p \neq 2$ because $18480 \mid q_0$ and $d \equiv 7 \pmod 8$), let $\mathcal{O}$ be the valuation ring of $\mathbb{C}_p$, $\pi_p \in \mathcal{O}_K$ a prime element above $p$ (so $\pi_p = p$ if $p$ is inert, $\pi_p = \sqrt{-d}$ if $p = d$), and let $q_p = N_{K/\mathbb{Q}}(\pi_p)$ be the norm ($p^2$ if inert, $p$ if $p = d$).

In `src/New/Derivatives/FormalGroup/FrobeniusCongruence.lean`, the multiplication-by-$\pi_p$ isogeny on the CM elliptic curve expresses $\theta(\pi_p z)$ in terms of $\theta(z)^{q_p}$ and the rational function $R(x)$ of the isogeny (`exists_rescale_theta_eq_pow_mul_aeval`, `:163`). Bounding the coefficients of $R(x)$ below degree $q_p/2$ by $\pi_p$ yields the key algebraic congruence (`CMLattice.exists_rescale_theta_eq_pow_mul_one_add_smul`, `:232`):
$$\theta(\pi_p z) = \theta(z)^{q_p} (1 + \pi_p H(y)), \qquad H \in \mathcal{O}[[y]],$$
where $y = \theta(z)^2/\dots$ or rather $y$ is the formal parameter (`taylorVia`) in `C.multiSeriesRing`. Taking $-\log$ gives `CMLattice.exists_negLogTheta_frobenius_congruence` (`:269`):
$$q_p \, g(z) - g(\pi_p z) \in \pi_p \, \mathcal{O}[[y]], \qquad g(z) := -\log \theta(z).$$
Crucially, why is this stronger than $1$-dimensional Lubin–Tate/Legendre divisibility? Look at the local parameter $z$ vs. the formal group parameter $x$ (`translatedX`, normalized Weierstrass $x$-coordinate centered at the origin). By solving the $3$-term ODE recursion for $x(z)$ (`derivative_pow_mul_derivative_taylorVia_translatedX` around `:328` and `norm_coeff_pow_taylorVia_translatedX_recursion_lt_one` at `:359`), the series coefficient satisfies:
- `norm_coeff_taylorVia_translatedX_eq_one` (`FrobeniusCongruence.lean:431`): at inert $p$, $\|[z^{p-1}] x(z)\|_p = 1$, i.e. the formal group logarithm has **height 2** ($z = \log_{\mathcal{F}}(x)$ has $[p](x) \equiv u x^{p^2} \pmod p$, while in the coordinate $z$, $x(z)$ has a $p$-adic unit coefficient already at degree $p-1$ and $z$-series expansions pick up $p^j$-power jumps).

#### Step 2: Isolating the flat part $g^\flat$ and the exponent series $\Xi_1$ (`Exponent.lean`)
In `src/New/Derivatives/FormalGroup/Exponent.lean`, let `leastFlatDegree` (`:65` area) be $k_0 = p+1$ if $p$ is inert and $k_0 = 2$ if $p = d$ is ramified. Averaging $g(\zeta z)$ over $(q_p - 1)$-st roots of unity eliminates all terms of degree $\not\equiv k_0 \pmod{q_p - 1}$ (`negLogThetaPart`, denoted $g^\flat$). Rescaling by $\varpi \in \mathbb{C}_p$ of valuation $\rho_p := \frac{v_p(\pi_p)}{q_p - 1}$ — explicitly:
$$\rho_p = \frac{1}{p^2 - 1} \text{ (inert)}, \qquad \rho_p = \frac{1}{2(p-1)} \text{ (ramified } p=d\text{)}$$
— and defining `exponentSeries` (`Ξ₁`, rescaled by $-(\varpi^{p+1}/p)^{-1}$ when inert, or $-(\varpi^2/\pi_d)^{-1}$ when ramified), `exists_rescale_theta_eq_mul_expSubst` (`Exponent.lean:248`) splits off a **unit** $W(z) \in \mathcal{O}[[z]]^\times$ containing all degrees not congruent to $p+1 \pmod{q_p - 1}$:
$$\theta(\varpi z) = W(z) \cdot \exp(c_\varpi \Xi_1(z)), \qquad c_\varpi = \varpi^{p+1}/p.$$
Notice the magic of $c_\varpi$:
- For inert $p > 2$, $v_p(c_\varpi) = \frac{p+1}{p^2 - 1} - 1 = \frac{1}{p-1} - 1 < 0$! That means $c_\varpi$ has **$p$-adic norm strictly larger than $1$** ($p^{1 - 1/(p-1)}$)! Thus $\theta(\varpi z)$ is NOT even locally integral in $z$ unless the exponents of $\exp(c_\varpi \Xi_1(z))$ match to cancel $c_\varpi$ — or conversely, when $W(z)$ is cancelled by $4$-squares or coupled across variables, the $\varpi$-rescaling forces extra factors of $\varpi$ per derivative!
Wait — why doesn't $\exp(c_\varpi \Xi_1)$ blow up the $\theta$-jets of $f(\varpi z)$? Because in `exists_eq_exponentSeries_dvd_sub_tsum_of_inert` (`Exponent.lean:562`) and `CMLattice.exists_exponent_tsum` (`:645`), solving the Frobenius functional equation `exists_functional_equation_exponentSeries` (`:276`) degree-by-degree (`C_dvd_pow_sub_primePowerSeries_odd_mul_even` at `:403` and `CMLattice.norm_coeff_exponentSeries_eq_one` at `:512`) proves:
$$\Xi_1(z) \equiv \sum_{e \in I_p^\circ} \sum_{j \ge 0} \lambda_{e,j} \, (z^{p^e} z)^{p^j} \pmod{\pi_p},$$
where $I_p^\circ$ is the odd positive integers if $p$ is inert (and all integers $\ge 1$ if $p = d$), and crucially $\lambda_{e,0}$ is a **$p$-adic unit** for odd $e$ when $p$ is inert (`norm_coeff_exponentSeries_eq_one`).

#### Step 3: Multivariable resolution of identity & Normal Form (`Resolution.lean`, `ThetaProducts.lean`, `NormalForm.lean`)
In our applications, theta functions live on a vector space $V = \operatorname{Hom}(X, E)$ or $E^n$, with complex places $\Phi = \operatorname{Gal}(E/K) \cong (\mathbb{Z}/q_1)^\times$. On $E$, we pick a finite **$p$-integral resolution of the identity** (`New.IsResolution`, `Resolution.lean:65`):
$$\sum_j m_j \, u_j u_j^\dagger = 1, \qquad u_j^\dagger := \overline{u_j} \text{ or } \text{conj-weighted adjoint},$$
with $m_j \in \mathbb{Z}$, $u_j \in \mathcal{O}_E$ integral above $p$ (`IsIntegralAbove`, `:95`), and `IsResolution.sum_smul_linearSeries` (`:150`).

Why does this convert $\sum_j m_j \Xi_1(u_j^\dagger z)$ into clean monomial couplings across infinite places $\tau \in \Phi$?
By `New/Derivatives/Field/PrimeDecomposition.lean:741` (`natCast_dvd_pow_sub_galOfPlaceInt_star`) and `ThetaProducts.lean:144` (`norm_pow_sub_conj_partner_le` / `dvd_pow_sub_sum_partner` at `:218`), at an inert prime $p$ and odd exponent $e$, Frobenius at $p^e$ acts on $\mathcal{O}_E / p$ as the Galois automorphism at `-p^e` composed with complex conjugation! Define the **partner map** (`Parameters.partner`, `ThetaProducts.lean:60`):
$$\tau' := u(-p^e) \cdot \tau \qquad (\text{so } \tau(\alpha)^{p^e} \equiv \overline{\tau'(\alpha)} \pmod{\pi_p}).$$
Therefore, summing over the resolution identity gives (`piPrimeInt_dvd_sum_linearSeries_sub_coupling`, `ThetaProducts.lean:249`):
$$\sum_j m_j (u_j^\dagger z)^{p^e} (u_j^\dagger z) \equiv \Gamma_e(z) := \sum_{\tau \in \Phi} \bigl( z_\tau \overline{z}_{\tau'} \text{ / bilinear coupling } \Gamma_e \bigr) \pmod{\pi_p}.$$
Consequently (`Parameters.exists_hasNormalForm`, `ThetaProducts.lean:450` area), every rescaled product of theta functions $F(\varpi z)$ has **normal form** (`HasNormalForm`, `NormalForm.lean:58`):
$$F(\varpi z) = W(z) \cdot \exp\!\Bigl(\sum_{e \in I_p^\circ} \sum_{j \ge 0} \mu_{e,j} \, \Gamma_e(z)^{p^j}\Bigr),$$
where $W \in \mathcal{O}[[z]]^\times$ and `HasNormalForm.norm_coeff_subst_le_one` (`NormalForm.lean:252`) guarantees that if we substitute $z \mapsto z(s)$ so that $\Gamma_e(z(s)) \in \pi_p \mathcal{O}[[s]]$ for all $e \le \lfloor \log_p B \rfloor$, then **every Taylor coefficient of $F(\varpi z(s))$ of total degree $\le B$ has $p$-adic norm $\le 1$!**

#### Step 4: Null frames, charges, and the minor-product jet bound (`NullFrames.lean`, `Count.lean`)
Given a Schur jet derivative of `columnDetProd` (products of $\det(z_{\tau, \text{col}})$ for a filling of Young diagrams at places $\tau \in \Phi$):
1. At any row of columns, `Divisibility/NullFrames.lean` (`exists_newDirection_dvd`, `:412` area) introduces auxiliary direction variables `DirectionVar` (`Count.lean:155`, at most $|\Phi| N^3$ variables via `card_directionVar_le`) via a $p$-integral basis change (`CongruenceChoice`, `:248` area).
2. A pair `(τ, τ')` at exponent $e$ is coupled via $\Gamma_e$: to kill $\Gamma_e(z(s)) \bmod \pi_p$, at least one side of each pair in the diagram must carry either:
   - a $\pi_p^{1/p^e}$-scaling on the source side (paying $1/p^e$ valuation per box, giving the local term $(a/p^e - \kappa(-p^e \tau))_+$!), or
   - a $\pi_p$-scaling / Hecke **charge** `charge τ b` on an `IsExemptPair` (`NullFrames.lean:198`), provided `charge τ b = 0` or `charge (partner τ) b = 0` (`IsChargeExponent`, `Count.lean:280` area).
3. `norm_jet_le_of_isHomogeneous` (`Count.lean:95`) applies Legendre's bound $v_p(l!) \le l / (p-1)$ to pass from Taylor coefficients to partial derivatives.
4. `heightOneColumns` / `lowBoxCount` / `predictedDivisibility` (`Count.lean:380-460`) track the balance between Legendre's factorial term $v_p(l!)$, the $\varpi^B$ rescaling cost ($-B \rho_p$, leaving the single-curve baseline Katz slope $\gamma_p = v_p(l!)/l - \rho_p \approx \frac{p}{p^2-1}$ at inert $p$), and the **coupling divisibility** from $\Gamma_e(z)$ ($e \in I_p^\circ$), minus `deductionTerm` and $|\Phi| N^3 (1 + \log_p \max(B,1))$.
   On the archimedean side (`PrimeSums.lean:28-30`), `D.jetSize j = log j! + j log(M / Ω)` already absorbs $\log j!$, while `D.localPrimeSum p y σ = v(π_p) ∑_{e ∈ I_p} (y / p^e - κ(-p^e σ))_+` (`ShortColumns.lean:87`) isolates the non-split Frobenius coupling gain. In `Cases.lean` (`leastValLE_twelve`), the sharp Taylor-coefficient valuation bound takes the form
   $$\operatorname{val}_{12}(l) \le S_p + 2 \sum_{\tau} v_p(B_\tau) - v_p(l!),$$
   so multiplying by $l!$ to compare $\partial^l F(0)$ cancels $v_p(l!)$ against Taylor normalization: on split primes ($S_p = 0$), $\partial^l F(0)$ can be made a $p$-adic unit, while on non-split primes its $p$-adic valuation matches $S_p = \text{localPrimeSumTotal } p$ up to the negligible error terms!

Let's double-check the exact arithmetic of `Divisibility/Count.lean`:
In `Count.lean`, `norm_jet_minorProd_le_of_hasNormalForm` (`Count.lean:680` area) combines:
- `norm_jet_columnDetProd_subst` (`Count.lean:320` area): using `IsChargeExponent` and `fillingCharge`, each box/pair contributes the coupling valuations,
- `eraseHeightOne` / `predictedDivisibility` (`Count.lean:395-450`): erasing height-1 columns (at $a$-places where diagrams have $a$ columns of height $1$) extracts $a \cdot v(\pi_p) \sum_e (1/p^e \dots)$ minus `deductionTerm`, while the remaining $\le k$ rows of length $\kappa(\tau)$ contribute `k * localPrimeSum p (κ τ) τ`!
- Finally `exists_norm_schurJet_le_norm_jet_minorProd` (`Count.lean:805`) writes any Schur vector `schurJet` as a `ℤ`-linear combination of `minorProd`s (`minorProd_eq_sum`, `:770` area) without losing $p$-adic norm (`≤ max`).

---

### 2.2 Vacuum Integrality, Short Vectors & Tight Frames (`Vacuum/`)

The upper bound needs Schwartz test functions $\varphi \in \text{standardData } V \, 1$ whose finite-place values are integral at **all** primes $p$ (including primes $p \mid q_1$!) and whose Fourier/theta expansions in local coordinates admit `HasNormalForm`.

#### Step 1: Constructing Tight Frames Coprime to $q_1$ Without a Dual Basis (`ShortVectors.lean`)
A tight frame over $\mathcal{O}_E$ of length $h$ is a family $u : \operatorname{Fin} h \to \mathcal{O}_E$ with $\sum_{i} u_i \overline{u_i} = h \cdot \dots$ wait: strictly speaking, in `TightFrames.lean` and `ShortVectors.lean`:
- A tight frame of weight $c$ / length $h$ satisfies $\sum_i u_i \overline{u_i} = \dots$ (`isTightFrame_pow` in `TightFrames.lean` and `Data.exists_isTightFrame` in `ShortVectors.lean:679`).
Why is finding short tight frames coprime to $q_1$ subtle? Classical Minkowski/LLL methods require inverting a lattice basis or lose primes dividing the discriminant $d \cdot q_1$. Instead, `src/New/Derivatives/Vacuum/ShortVectors.lean` does something completely elementary and explicit:
1. It constructs algebraic integers in $E = K(\zeta_{q_1})$ directly from cyclotomic roots and $\beta_K = \frac{1+\sqrt{-d}}{2}$ (satisfying $\beta_K^2 - \beta_K + \frac{d+1}{4} = 0$).
2. **`exists_cyclotomic_different_factor`** (`ShortVectors.lean:121`): Explicitly factors $N \cdot V = \Phi_N'(\zeta)(\zeta^r - 1) M$ in $\mathbb{Z}[\zeta]$, bounding the size of the cofactor.
3. **`exists_quad_congr_mod_q₁`** (`ShortVectors.lean` line before `:292`): Solves $\frac{d+1}{4} z^2 + z + 1 \equiv 0 \pmod{q_1}$ by exploiting the fact that $d \equiv q_0/2 - 1 \pmod{q_0}$ makes $\frac{d+1}{4}$ **nilpotent modulo powers of $2$** (and $q_1 = 3^c 2^s q_0$), solving it via Hensel lifting / finite truncation without dual bases!
4. **`exists_isTightFrame_coprime`** (`ShortVectors.lean:292`) & **`exists_isTightFrame_of_coprime`** (`:480` area) & **`Data.exists_isTightFrame`** (`:679`): Produces a tight frame of length $h \le (d q_1)^6$ coprime to $q_1$, and takes powers/combinations to achieve entries $c_i \ge 6 f b$ of length $M$ possessing `HasUnitLinearForm` at **every** prime $p$ (so at every $p$, at least one $u_i$ is a unit modulo $p$, guaranteeing non-degeneracy of local coordinates even at $p \mid q_1 d$).

#### Step 2: From Chowla–Selberg Vacuum to `intVacuum` and `standardData` (`TightFrames.lean`, `IntegralVacuum.lean`, `Scale.lean`, `JetIntegrality.lean`, `StandardDataProducts.lean`)
- In `TightFrames.lean`: defines `cmCurve`, `cmPeriod`, `chowlaSelbergUnit`, `areaScale`, `periodFactor`, and `jetScale` (`:60-200`). Using `norm_iota_periodFactor_eq_one` (the $p$-adic norm of `periodFactor` under any $\iota_p$ is $1$, proved via the CM Chowla–Selberg period relation and torsion values), any tight frame decomposes a holomorphic theta line integral (`taylor_line_eq_subst_jetSeries`, `exists_isResolutionProduct_of_isTightFrame`).
- In `IntegralVacuum.lean`: defines the integral vacuum function `intVacuum` (`θ°`, `:380` area) via `vacuumScale`, proves finite-place integrality `norm_intVacuum_le_one` (`:457`), Galois conjugate archimedean bounds `norm_ringEquiv_intVacuum_le` (`:510` area), non-vanishing `exists_intVacuum_ne_zero`, and `standardData V δ` (`:420` area).
- In `Scale.lean` & `JetIntegrality.lean`: defines `jetRing` (`JetIntegrality.lean:150` area), proves `pderiv_mem_jetRing`, `norm_jet_thetaProd_pow_mul_le_one`, and shows that the finite Heisenberg / Weil representation operators preserve `standardData` (`finHeisenbergOp_mem_standardData`, `omega_mem_standardData`, `JetIntegrality.lean:290-330`).
- In `StandardDataProducts.lean`:
  1. Uses Fourier inversion over a tight frame of **coprime square length $b^2$** (`exists_coprime_isTightFrame_sq`, `StandardDataProducts.lean:280` area) to expand twisted translates (`CMLattice.exists_prod_twistedTranslate_eq_thetaProd_mul`, `:180` area; `IsVacuumExpansion`, `exists_isVacuumExpansion`, `:350` area).
  2. Proves **`exists_jetSeries_map_eq_thetaProd_pow_mul`** (`StandardDataProducts.lean:490` area): any $f \in \text{standardData } V \, 1$ has `jetSeries` equal to a product $\theta(z)^N \cdot H(z)$ with $H$ integral in a $p$-integral resolution `w / (b m)`. This is the exact bridge into `Vacuum/Divisibility.lean:177` (`exists_hasNormalForm_jetSeries`).

---

### 2.3 Why 12 Copies of the CM Curve Prove Sharpness & Cancel `directionAmount` (`Sharpness/`)

The second core question is: **how does `Sharpness/` (on 12 copies of the CM curve) prove the $p$-adic divisibility bound is attained so that `directionAmount` cancels cleanly between the upper and lower sides of `(⋆)`?**

#### Step 1: Single-curve Katz limit (`OneCurve.lean`)
In `src/New/Derivatives/Sharpness/OneCurve.lean`, define `CMLattice.maxDerivNorm C n` (supremum of $p$-adic norms of $n$-th derivatives of sections/functions in $C$’s $p$-adic integral ring). Via the addition law on the elliptic curve (`maxDerivNorm_add_le` via $y(z_0 + z_1)^j$, `:150` area) and Fekete's submultiplicative lemma (`pow_le_of_submultiplicative`, `:75` area), `CMLattice.katz_divisibility_limit` (`OneCurve.lean:272`) shows that for the formal parameter `formalParam` at non-split $p$:
$$\|n! \cdot \operatorname{coeff}_n(f)\|_p \ge p^{-\gamma_p n} \quad \text{(for suitably chosen } f\text{)}.$$
Wait: $1$ copy cannot produce a *small* Taylor coefficient of prescribed multi-degree while *also* cancelling $\theta(z)$'s zeros/growth AND creating the coupled derivatives $(\varpi^{p+1}/p) \partial\Xi_1$ across infinite places!

#### Step 2: Why **6 copies**? Lagrange's 4-squares identity in $\mathbb{Z}_p$ (`LeastValuation.lean`)
Look at `src/New/Derivatives/Sharpness/LeastValuation.lean`:
- **`padicInt_sum_four_squares`** (`LeastValuation.lean:261`): Every $p$-adic integer (specifically $-1 \in \mathbb{Z}_p$, or with $0$ for the 5th copy) is a sum of 4 squares in $\mathbb{Z}_p$! Thus there exist $\delta_0, \delta_1, \delta_2, \delta_3, \delta_4, \delta_5 \in \mathbb{Z}_p$ with $\delta_0 = 1$, $\delta_5 = 0$ (or 4 nonzero + 1 + 1 = 6 coordinates) satisfying:
  $$\sum_{c=0}^5 \delta_c^2 = 0 \quad \text{in } \mathbb{Z}_p.$$
- Why does $\sum_{c=0}^5 \delta_c^2 = 0$ solve the $\Theta$-cancellation problem?
  Recall $\theta(z)$ has a quadratic leading exponent $e^{-c |z|^2}$ / $z^2$-behavior in the archimedean/theta transformation! More precisely, when we define the **6-copy scaled theta product** (`scaledThetaProd` on $\operatorname{Fin} 6$, `:440` area), summing $\delta_c^2$ over $c \in \operatorname{Fin} 6$ cancels the quadratic phase / theta-multiplier obstruction, so:
  - **`prod_rescale_theta_mem`** (`LeastValuation.lean:415`): $\prod_{c=0}^5 \theta(\delta_c z)$ lies in `C.multiSeriesRing μ`!
  - **`exists_scaledThetaProd_mem_mul_eq_one`** (`LeastValuation.lean:526`): There exists a 6-copy choice $\delta$ whose `scaledThetaProd` is an **invertible unit** in `C.multiSeriesRing μ`!
- Defining `CMLattice.LeastValLE C m r v` (meaning there is an $m$-copy theta-integral function $F(z_0,\dots,z_{m-1})$ whose degree-$r$ Taylor part has minimum $p$-adic valuation $\le v$):
  - `leastValLE_of_unit_coefficients` (`LeastValuation.lean:547`) and `leastValLE_zero_of_span` (`:593`) use the 6-copy invertible `scaledThetaProd` to invert/cancel any unwanted $\theta$ factors, proving that:
    1. On 6 copies, `val₆(η) ≤ 0` (`leastValLE_six_zero_of_inert`, `Cases.lean:150` area) — i.e., **we can match ANY remaining degree $\eta$ at zero valuation loss** (on Taylor coeffs, or $\le \gamma_p |\eta| - v(\eta!)$ if needed), and
    2. On 6 copies, `val₆(l) ≤ -v_p(l!)` for split $p$.

#### Step 3: Why **12 = 6 + 6 copies**? Coupling pairs via `couplingSubst` (`Couplings.lean`)
Now consider **Couplings.lean** (`src/New/Derivatives/Sharpness/Couplings.lean`) on 6 copies (`z₀, z₁, …, z₅`) and **Cases.lean** (`src/New/Derivatives/Sharpness/Cases.lean`) on 12 copies (`Fin 12` = first `6` copies + second `6` copies):
- Why can't 6 copies do both the coupling AND the residual weight $\eta$?
  In `Couplings.lean`, an `IsCouplingFamily` (`:58`) at a non-split prime $p$ selects a list of coupled exponent-place pairs $(\tau_i, e_i)$ (`powerDegree` $\nu'$, `partnerDegree` $\nu''$). It substitutes into the 6-copy invertible $\theta$-product via **`couplingSubst`** (`:364`):
  $$z_0 = z' + z'', \qquad z_c = \delta_c z' \quad (c = 1, \dots, 5), \qquad \sum_{c=1}^5 \delta_c^2 + 1 = 0.$$
  Look at what happens at $z'' = 0$! Because $\prod_{c=0}^5 \theta(\delta_c z')$ is a **unit**, differentiating with respect to $z''$ along the direction $\tau^+$ hits $\theta(z' + z'')$, i.e. $\exp(c_\varpi \Xi_1(z' + z''))$!
  For **inert $p > 2$**, look at `one_lt_norm_pow_div_of_inert` (`Couplings.lean:450` area):
  $$\left\| \frac{\varpi^{p+1}}{p} \right\|_p = p^{1 - \frac{p+1}{p^2-1}} = p^{1 - \frac{1}{p-1}} > 1!$$
  Each differentiation $\partial_{z''_{\tau^+}}$ pulls down one factor of $c_\varpi = \varpi^{p+1}/p$ (with **negative valuation** $\frac{1}{p-1} - 1 < 0$) times $\partial_{z_{\tau^+}} \Xi_1$, whose leading term is $(z_{\tau^+})^{p^e}$.
  - In **case $k < p$** (`leastValLE_twelve_of_lt`, `Cases.lean` around `:450`), every coupling occurs at $e = 1$: `leastValLE_partnerDegree_of_isCouplingFamily` (`Couplings.lean` around `:510`) attains `val₆(ν' + ν'') ≤ -|j|` using $6$ copies, and `leastValLE_six_of_isCouplingFamily` (`Couplings.lean:586`) attains `val₆` with factorial adjustment.
  - In **case $p \le k$** (`leastValLE_twelve_localPrimeSumTotal_of_le`, `Cases.lean`), higher exponents $e \ge 1$ contribute via `IsNearPair` (Step 4).
  - Then **adding the two independent 6-copy functions** (via `LeastValLE.add`, `LeastValuation.lean:280` area, multiplying $F_1(z_0,\dots,z_5) \cdot F_2(z_6,\dots,z_{11})$ on `Fin 12`!) combines:
    - **Copies $0..5$**: realize the exact coupled exponents $(\nu' + \nu'')$ attaining the negative valuation $-S_p$ (from `IsCouplingFamily` at all coupled pairs in `NearPairs`),
    - **Copies $6..11$**: supply the remaining **uncoupled degree $\eta$** at valuation $\le 0$ (`leastValLE_six_zero_of_inert` / `-v_p(\eta!)`)!
  That is the literal reason for **12 copies = 6 (couplings via $z_0 = z'+z''$) + 6 (residual $\eta$-degree completion via $1+\sum_{c=1}^4 a_c^2 = 0$)**!

#### Step 4: Near Pairs, `D.sparse`, and `lossProduct` (`NearPairs.lean`, `Cases.lean`)
When $p \le k$ (small non-split primes), higher exponents $e \ge 1$ contribute to `localPrimeSum p κ τ`. Two distinct $b$-places $\sigma_1, \sigma_2 \in \Phi_b$ could potentially collide under partner shifts $-p^e \tau$.
In `src/New/Derivatives/Sharpness/NearPairs.lean`:
- **`notMem_bPlaces_of_two_partners`** (`:95` area): uses `D.sparse` (the sparseness hypothesis on $\Phi_b \subset \Phi$) to rule out two distinct partner overlaps!
- **`IsNearPair`** (`:130` area): proves pairs $(e, \tau)$ contributing near a weight window are vertex-disjoint (`exponent_unique`, `eq_and_eq_of_partner_eq`, `end_ne_start`).
- **`lossFactorCount`** (`n♯ = ⌈6 b / k⌉₊`) & **`lossProduct`** ($B_\tau$): absorbs the $e \ge l_0/2$ tail and multinomial error via `tsum_partnerMinTerm_add_le` / `error_le_padicValNat_lossProduct` (`NearPairs.lean:380-460`).
- **`Cases.lean` (`leastValLE_twelve`, `:610` area)**: unites split primes, $k < p$, and $p \le k$ for near weights `IsNearWeights` (`κ(τ) ≤ l_τ ≤ κ(τ) + x^{42}`) into the uniform 12-copy bound:
  $$\operatorname{val}_{12}(l) \le S_p + 2 \sum_{\tau} v_p(B_\tau) - v_p(l!).$$

#### Step 5: From 12-Copy Local Series to Global Indicator Datum & `directionAmount` Cancellation (`BoundAttained.lean`, `OneLift`, `LongForms`, `ShortAndEnough`, `MainInequality`)
In `src/New/Derivatives/Sharpness/BoundAttained.lean`:
1. **`twelveSpace`** (`:157`): `(stdSpace D.E Unit).hom (stdSpace D.E (Fin 12))` (hermitian maps $E \to E^{12}$, rank $12$).
2. Build a tight frame of length $M$ with $c_i \ge 6 f b$ and `HasUnitLinearForm` via `Data.exists_isTightFrame` (`ShortVectors.lean:679`). Lift the polynomial/monomial product `(y θ³)^e θ^(c - 3e)` achieving `leastValLE_twelve` into a global algebraic theta section `F ∈ 𝒮 D.twelveSpace` (`twelveTaylor`).
3. **`exists_integral_isThetaFunction_twelveTaylor_eq`** (`:210` area) + **`exists_norm_le_norm_indicatorDatum`** (`:276`) + **`exists_le_norm_coeff_indicatorDatum`** (`:352`): use Fourier inversion over residue classes modulo $\mathfrak{m} = (\pi_M)$ to pass from the global theta series to a single finite-level test vector **`indicatorDatum`** $y_0 \bmod \mathfrak{m}$, scaled by $t$ satisfying **`norm_map_mul_intVacuum_le`** (`:397`, $\|\sigma t\| \le \exp(f m b / k)$), giving **`exists_rpow_neg_localPrimeSumTotal_le_norm_coeff`** (`:456`): a coefficient bounded below in $\mathbb{C}_p$ by $p^{-\text{localPrimeSumTotal}(p)}$.
4. **How `directionAmount` cancels in `(⋆)`**:
   - **Lower side (Theorem C)**:
     1. `TwistedValueHeights.lean:883` calls `exists_rpow_neg_localPrimeSumTotal_le_norm_coeff` at every $p$ to lower-bound the Hecke value of a well-chosen twist $\xi_\iota$, proving `heightLe_inv_ratio` (`:1015`, `HeightLe (6 * D.denominatorBudget - D.directionAmount)`) and `heightLe_inv_heckeValueProd_div` (`:1235`). Notice why **`- D.directionAmount`** appears! In `PrimeSums.lean:30`,
        $$\text{directionAmount} := \sum_{\tau \in \Phi} \bigl(s_\infty(\kappa(\tau)) - s_{\text{fin}}(\kappa(\tau), \tau)\bigr),$$
        where $s_\infty(\kappa) = \log \kappa! + \kappa \log(M/\Omega)$ (the archimedean norm of the jet of order $\kappa$ from `AlgebraicPartSize.lean:482`) and $s_{\text{fin}}(\kappa, \tau) = \sum_p 2 \cdot \text{localPrimeSum } p \, \kappa(\tau) \, \tau \cdot \log p$ (the $p$-adic norm attained by `exists_rpow_neg_localPrimeSumTotal_le_norm_coeff`!).
     2. Raising to power $d = \text{targetDim}$ and combining across all $m$ lifts in `LiftVolumeHeight.lean:731` -> `LongForms.lean:192, 274` multiplies by $m \cdot k$, giving **`D.mainAmount = m * k * D.directionAmount`** on the left-hand side of **Theorem C** (`integral_forms_long`, `LongForms.lean:274`):
        $$d \cdot (\text{mainAmount} - 3 f a \log^4 b) \le c + 2 \delta.$$
   - **Upper side (Theorems A & B)**:
     1. In `ArchimedeanSize.lean:155, 187`, `two_mul_sum_gain_mul_log` and `mainAmount_sub_add_two_mul_sum_gain` expand `D.gain p = m (∑_{τ ∈ Φ_a} s_p(a, τ) + k F(p))` (from `ShortColumns.lean:98`)! Because `gain` subtracted $m \cdot s_{\text{fin}}(a, \tau)$ and $m k \sum_\tau s_{\text{fin}}(\kappa(\tau), \tau)$ via `invGainFactor = ∏ l ^ (-g_l)` (`ShortAndEnough.lean:61, 95`), multiplying by `invGainFactor` in Theorem A (`span_short_integralRamified_eq_top`, `ShortAndEnough.lean:202`) gives upper log-squared norm:
        $$\text{chainSize} - 2 \sum_{p < x_1} \text{gain}_p \log p + \text{err} = \text{mainAmount} - m \cdot \text{totalRemainder} + f a \log^4 b!$$
        Specifically (`ArchimedeanSize.lean:187`), $s_{\text{fin}}(\kappa(\tau), \tau)$ cancels **identically** inside `D.mainAmount`!
     2. Combining Theorem A, Theorem B (`exists_le_finrank_iSup_range_normalizedPoincare`, `ShortAndEnough.lean:361`), and Theorem C (`integral_forms_long`, `LongForms.lean:274`) in `MainInequality.lean:103-160` cancels `D.targetDim * D.mainAmount` from both sides, leaving `m * totalRemainder ≤ f * a * log⁵ b`!

---

### 2.4 Rescuing Frobenius Collisions via `ElementaryDivisors/` (Stepanov + Dixon–Anderson + Dual Schur)

The third core question is: **how do `Vacuum/` and `ElementaryDivisors/` rescue Frobenius collisions on $\tau \equiv 1 \pmod{q_0}$?**

#### Step 1: Why Frobenius collisions threaten $a$-places (`MarkedPrimes.lean`, `ValuationAtNonSplitPrimes.lean`)
At $a$-places ($\tau \in \Phi_a$, i.e. $\tau \equiv 1 \pmod{q_0}$), the lift diagrams have $a$ columns of height $1$. By `NormalForm`/`Count`, we want to extract $\sum_{\tau \in \Phi_a} \text{localPrimeSum } p \, a \, \tau \approx \sum_{e \text{ odd}} \frac{a}{p^e}$ at inert $p < x_1$.
However, if $-p^e \equiv 1 \pmod{q_0}$ for an **odd** exponent $e$, then the partner $-p^e \tau$ of an $a$-place $\tau$ is **itself an $a$-place** (`IsCollision`), so $(\tau, -p^e \tau)$ is a self-collision inside $\Phi_a$ that cannot simultaneously avoid `aPlaces` unless we charge one side!
- If $p \equiv \pm 1 \pmod m$ (`IsPlusMinusOneModLifts`), or if the order $o_0$ of $-p$ in $(\mathbb{Z}/q_0)^\times$ is even or $> \lceil \log_p m \rceil$, the total collision sum $\sum \frac{a}{p^e}$ is tiny enough to dump into `allowedLoss p` (`Loss.eq` = `f (log b)^2 a / p * (m if p ≡ ±1 mod m else 1)`, `LocalDivisibility.lean:44` / `ShortColumns.lean:111`).
- **The danger zone (`IsExceptional`)**: When $\chi_K(p) = -1$, $p \not\equiv \pm 1 \pmod m$, and $-p$ has **odd order $o_0 \le \mathfrak{r} := \lceil \log_p m \rceil$** mod $q_0$, the collision sum $a / p^{o_0}$ over $m$ lifts exceeds the `allowedLoss p` budget of $f a (\log b)^2 / p$.

#### Step 2: Marking $\Lambda$ & Charging via Scaled Hecke Operators (`MarkedPrimes.lean`, `MarkOperator.lean`, `ValuationAtNonSplitPrimes.lean`)
The rescue:
1. Choose a **full mark** $\Lambda \subset \text{FinPlace } E$ above $p$ (`exists_isFullMark`, `MarkedPrimes.lean` around `:240`): for $\mathfrak{w} \mid p$ and $\tau \in \Phi$, `smul_eq_self_iff_of_inert` gives $\tau \mathfrak{w} = \mathfrak{w} \iff \tau = (-p)^{\text{even}}$ and `smul_eq_star_iff_of_inert` gives $\tau \mathfrak{w} = \overline{\mathfrak{w}} \iff \tau = (-p)^{\text{odd}}$ (`PrimeDecomposition.lean:723, 732`). Hence $\mathfrak{w} \neq \overline{\mathfrak{w}}$ (each prime above $p$ in $E$ is split over $K$), and $\Lambda$ picks **one prime from each conjugate pair** $\{\mathfrak{w}, \overline{\mathfrak{w}}\}$ induced by $\Phi_a$ (`hΛ.star_notMem`: $\Lambda \cap \overline{\Lambda} = \emptyset$).
2. At each $\mathfrak{l} \in \Lambda$, apply the **scaled Hecke operator** $p^{A_{\mathfrak{l}}} T_{\mathfrak{l}, \mathfrak{r}}$ (`heckeScalingExponent l` = $a \cdot \#\{\tau \in \Phi_a \mid \text{inducedPlace } \tau = \mathfrak{l}\}$, `MarkOperator.lean`), **once per lift** (`Y^m` in `LocalDivisibility.lean:343`).
3. On the image of $T_{\mathfrak{l}, \mathfrak{r}}$, diagonal representatives `neighborDiagonal` have valuation jumps up to $\mathfrak{r}$ at $\mathfrak{l}$ and $0$ at $\overline{\mathfrak{l}}$. Because every collision pair $(\tau, -p^e \tau)$ with odd $e$ flips $\mathfrak{l} \leftrightarrow \overline{\mathfrak{l}}$ (`smul_eq_star_iff_of_inert`), **one endpoint induces $\Lambda$ and its partner induces $\overline{\Lambda}$**! Thus `neighborCharge` (`ValuationAtNonSplitPrimes.lean:152`, `IsMarked.neighborCharge_ne_zero_or_partner`) satisfies the `norm_schurJet_jetSeries_le_of_charges` hypothesis **without ever vanishing on both endpoints**, recovering the full `gain p` divisibility on `Y^m(M)`!

#### Step 3: Bounding the Colength of $Y^m(M) + p^{j_p} M$ over Non-Noetherian `embValRing` (`ElementaryDivisors/`)
Everything now reduces to proving that $Y_{\mathfrak{l}} = p^{A_{\mathfrak{l}}} T_{\mathfrak{l}, \mathfrak{r}}$ loses almost nothing in colength modulo $p^{j_p}$ (`FrobeniusCycle.elementary_divisors`, `ElementaryDivisorTheorem.lean:1181`)!

Look closely at the setting (`TwistingData.lean:60-290`, `MarkOperator.lean:300-355`):
- **Frobenius Cycle**: Let $N$ be the number of $a$-places inducing $\mathfrak{l}$ or $\overline{\mathfrak{l}}$. Since multiplication by $-p^{o_0}$ alternates $\mathfrak{l} \leftrightarrow \overline{\mathfrak{l}}$ ($o_0$ is odd!), ordering the coset gives a `FrobeniusCycle N W embValRing` (`N` even, $P = p^{o_0}$, $q = P^N = |\text{ResField } W|$): embeddings $\iota_i : W \to \mathcal{O} := \text{embValRing} \subset \mathbb{C}$ satisfying:
  $$\iota_{i+1}(x) \equiv \iota_i(x)^P \pmod p, \qquad \iota_i \text{ alternates even (in } \Lambda\text{) and odd (in } \overline{\Lambda}\text{)}.$$
  Here `embValRing` (`src/Lib/General/Algebra/AdicCompletion.lean:80-120`) is a valuation subring of $\mathbb{C}$ (non-Noetherian! Value group can be dense!).
- **How `ElementaryDivisors/` bypasses Noetherianity & proves the Colength Bound**:
  1. **Colength without Noetherian modules (`Colength.lean:39`, `ElementaryDivisorTheorem.lean:110-420`)**: Defines `ColengthDvd M N z` as: every finite family in $M$ admits a $\mathcal{O}$-linear combination matrix $m$ with $\det m \mid z$ mapping into $N$. Over any `ValuationRing`, Hermite/Smith diagonalization (`exists_elementary_divisors_mod_summand`, `ElementaryDivisorTheorem.lean:105` area; `exists_mul_inv_eq_mul_diagonal`, `Edges.lean:110` area) still works on **finitely generated free modules**! And an ad-hoc Nakayama-style lemma (`smul_top_le_of_le_sup_smul_top`, `ElementaryDivisorTheorem.lean:210` area) handles submodules of the form `w^(c-1) M ⊆ N + w^c M` when we pass through `w = √p` (`T.sqrtPrime`).
  2. **Stepanov's Method + Gauss Filtration + Pieri Defect (`RootLemma.lean`, `Depth.lean`)**:
     Look at `letterMatrix`, `letterRep`, and `deepForms` (`TwistingData.lean:90-270`). An element of `allEdgesForms` comes from parahoric Hecke edges (`ParahoricCosets`, depth `r = ceilLogLifts p` blocks of size $r \times (k-r)$ modulo $p$, so off-diagonal entries vanish mod $p$, `p_dvd_letterMatrix_of_mem_parahoric`).
     In `RootLemma.lean`:
     - `stepanov_count` (`:72`): Polynomials in $x$ over $\mathbb{F}_q$ acted on by `P`-powers have vanishing order bounded by degree/weight.
     - Lifting via `adicFiltration` and `gaussFiltration` (`:150-220`) to $\mathcal{O}$, if a polynomial vanishes modulo $w^c$ along ALL `SL_k(W)` parahoric translates in an $r$-block, `FrobeniusCycle.defect_nonpos_of_extreme_term` (`:1190`) forces every extreme surviving exponent $\beta$ to satisfy the **Pieri cone inequality** (`weight_defectWeight_nonpos_of_least`, `:1270` area):
       $$\langle \text{exponent}(\beta), \, \text{defectWeight}(i, a, r) \rangle \le \text{defectThreshold}(k, c) := 3 k c!$$
     - Why? Each parahoric step shifts variables by Frobenius $P$-powers; `Depth.lean` (`prod_deepOrder_le`, `:200` area; `sum_finrank_deepForms_le`, `:878`) bounds the sum of dimensions of deep subspaces (`depth ≥ δ`) across all $1 \le \delta \le M$ by `T.divisorConstant k n r = N n (1 / P^(2 r) + r^2 / (k P))`! Notice the two terms: $P^{-2r}$ comes from `SL_r × SL_{k-r}` depth mixing, and $r^2 / (k P)$ comes from Stepanov/shallow specialization (`specializeShallow`).
  3. **Dixon–Anderson Interlacing & Cone Volume Counting (`PieriCone.lean`, `DefectCount.lean`)**:
     - To convert the deep-defect condition over $N$ Frobenius-coupled letters into a linear algebra dimension bound over the residue field $\mathbb{F}_p$, `PieriCone.lean` (`det_interlacing_indicator`, `:88`; `sum_sign_indicator_pos_eq_indicator_pieriCone`, `:260` area) proves the Dixon–Anderson integral/combinatorial interlacing identity evaluating signed determinants of step matrices `permStep` to indicators of the `pieriCone`.
     - `DefectCount.lean` packages the coupled Frobenius defects into `defectCone` + `powerPacking` (`:100-200`), bounds hyperplane slices (`volume_degreeSlab_le`, `:790` area), and proves **`FrobeniusCycle.index_mul_finrank_defectConditions_le`** (`:935` area): the codimension/dimension of polynomials forced into `defectConditions` inside the residue field is bounded!
  4. **Dual Schur Pairing + Multinomial Weights (`Edges.lean`, `InvariantAverage.lean`, `AveragingMap.lean`)**:
     - We don't just need the *end* (vertex) basis to cover a small-defect subspace; we need the **edge Hecke map** $h \mapsto (g \cdot h)_{\text{edges}}$ to match a **dual pairing** (`IsEdgePairing b b'`, `Edges.lean:297`), where $b_\beta \, b'_\beta = p^{N c_0}$ with `c_0 = T.multinomialExponent k = k^2 * frobExp * N`!
     - Why multinomial weights $b_\beta$? Because on symmetric power / Schur representations of $\operatorname{GL}_k$, the $\operatorname{GL}_k$-invariant bilinear form `⟨h, h'⟩ = ∑_β h'_β b_β h_β` makes $g$ and $g^T$ **adjoint** (`IsAdjointWeight`, `InvariantAverage.lean:150` area; `exists_isAdjointWeight`, `:139`)! Its denominators are multinomial coefficients dividing $p^{c_0}$ (this is the **Dual Schur** mechanism!).
     - **`InvariantAverage.lean`** (`exists_isAverage`) + **`AveragingMap.lean`** (`exists_average_mem_defectConditions_and_dvd_sub`, `:699`): builds a Levi-invariant averaging matrix `Av` using $D = N n k (\ell + 2) P^\ell < P^N$ (`IsLargeDegree`!) so that modulo $w^c$ ($c = \text{congruencePrecision } k = 5 N c_0$), `Av` kills every monomial of defect $> 3 \cdot \text{defectThreshold } k \, c$ while preserving `⟨Av h, h'⟩ ≡ p^(N c_0) ⟨h, h'⟩ mod w^c`!
     - **`Edges.lean`** (`originFunctions`, `:410` area; `pow_dvd_pairing_letterRep`, `:670` area) + **`ElementaryDivisorTheorem.lean`** (`nearInverse`, `pairingMap`, `exists_elementary_divisors_mod_summand`, `:890-1175`): composes `Add * Inv ≡ p^(2 N c_0) (mod w^c)` on the halfway lattice! Using $c = 5 N c_0$, `mul_multinomialExponent_le_divisorConstant` (`:611`) ensures $N c_0 \le c_{\text{div}}$, splitting total colength into:
       - End budget: `c_div * |X| |I|`
       - Middle ($2 N c_0$) budget: `2 * c_div * |X| |I|`
       - Stepanov exceptional defect-cone generators: `θ * m * |X| |I|`
       Summing to **`(3 * c_div + θ * m) * |X| * |I|`**!
     - Substituting $\theta = 1 / (m^2 f)$ and `3 * c_div ≤ 12 * a * ℓ / (m * p)` (`three_mul_divisorConstant_le`, `MarkOperator.lean:119`) and multiplying over $m$ lifts (`LocalDivisibility.lean:305, 341`) yields colength $\le \text{loss}(p) \cdot \dim(\text{SourceForm})$, absorbed effortlessly into Theorem A's error budget (`errorUnit = f a log³ b`)!

---

## 3. Classical Barriers Bypassed & Tight Constants

### 3.1 Classical Machinery Bypassed

| Classical Textbook Barrier | Why It Fails or Explodes Here | Exact Custom Bypass in `rh_grh` |
|---|---|---|
| **Noetherian Smith Normal Form & Finite Module Length** | `embValRing ⊂ ℂ` is a non-Noetherian valuation ring (non-discrete value group, ideals not finitely generated). Standard PID elementary divisor theorems don't compile or don't apply. | `ColengthDvd` (`Colength.lean:39`) replaces module length by existence of finitely-generated base-change matrices whose determinant divides $p^e$; coupled with `ValuationRing` Hermite/Smith on finite-rank matrices (`exists_mul_inv_eq_mul_diagonal`, `Edges.lean:110` area) and an explicit $w^{c-1}$ Nakayama step (`smul_top_le_of_le_sup_smul_top`, `ElementaryDivisorTheorem.lean:210` area). |
| **Dual Lattice / Gram-Schmidt for Short Integral Frames** | Inverting a frame matrix over $\mathcal{O}_E$ puts $\det \mid q_1 d$ into denominators, destroying $p$-integrality at primes $p \mid q_1 d$. | `ShortVectors.lean` constructs explicit short tight frames of length $h \le (d q_1)^6$ coprime to $q_1$ via `exists_quad_congr_mod_q₁` (nilpotency of $(d+1)/4 \bmod q_1$) and `exists_cyclotomic_different_factor` ($\Phi_N'(\zeta)(\zeta^r - 1)$), achieving `HasUnitLinearForm` at *all* primes including $p \mid q_1 d$. |
| **CM Theta-Divisor Cancellation on 1 Curve** | On $1$ copy of $E$, Katz's formal group bound gives an upper slope $\gamma_p$, **not** sharpness for arbitrary multi-place weight tuples $\kappa(\tau)$ and coupled $\Gamma_e$ derivatives. | **12-copy construction** (`Sharpness/LeastValuation.lean`, `Couplings.lean`, `Cases.lean`): 4-squares in $\mathbb{Z}_p$ (`1 + a₀²+a₁²+a₂²+a₃² = 0`) creates a **6-copy unit** `scaledThetaProd`, letting copies `0..5` extract coupled derivatives via $z_0 = z'+z''$ ($\|\varpi^{p+1}/p\|_p > 1$ for inert $p > 2$) while copies `6..11` carry uncoupled degree $\eta$ at zero valuation loss. |
| **Algebraic Period / Chowla–Selberg Transcendence Machinery** | Relating $\theta(\tau)$-derivatives globally across Galois conjugates normally invokes deep CM period relations / Shimura's reciprocity theorem in full generality. | Restricted explicitly to the `CMLattice` theta normalization (`TightFrames.lean` `periodFactor`, `norm_iota_periodFactor_eq_one`, `IntegralVacuum.lean` `intVacuum`) + finite-frame Fourier inversion (`StandardDataProducts.lean`, `BoundAttained.lean:276`). |
| **Kloosterman / Trace Formula Bounds for Colliding Inert Primes** | When $-p^{o_0} \equiv 1 \pmod{q_0}$ for odd $o_0 \le \log_p m$, $a$-places collide with themselves; classical single-lift estimates lose $\gg a / p^{o_0}$ per lift. | **Full Mark Scaled Hecke Rescue** (`MarkedPrimes`, `MarkOperator`, `ElementaryDivisors`): splits $\mathfrak{l} \in \Lambda$ vs $\overline{\mathfrak{l}} \in \overline{\Lambda}$ using oddness of $o_0$, forces one-sided charges via $Y^m$, and proves $Y$ has tiny colength via Stepanov + Dixon–Anderson + Dual Schur (`FrobeniusCycle.elementary_divisors`). |

### 3.2 Genuinely Tight Numerical & Asymptotic Constants

1. **Number of CM copies = `12` (`6 + 6`)** (`Sharpness/LeastValuation.lean:261, 526`, `BoundAttained.lean:157`):
   - `4` squares for $-1 \in \mathbb{Z}_p$ (`padicInt_sum_four_squares`, uniformly valid over $\mathbb{Z}_p$ without quadratic reciprocity case-splitting) + `1` constant (`1`) + `1` padding/coupling variable (`0` on the residual block or `z''` on the coupling block) = **`6`** copies per unit block (`Fin 6`), doubled to **`12`** (`Fin 12`) to simultaneously hold both `IsCouplingFamily` (`z_0 = z'+z''`, `Couplings.lean:364`) and residual uncoupled degree $\eta$ (`Cases.lean` around `:150`). *Reducing 6 copies to 5 fails whenever $-1$ requires all 4 squares in $\mathbb{Z}_p$ (uniformly via Lagrange's 4-squares theorem); doubling `6` to `12` keeps the coupled and uncoupled blocks algebraically independent.*
2. **Height-2 Formal Group Slope $\rho_p$** (`FormalGroup/Exponent.lean`):
   - $\rho_p = \frac{v_p(\pi_p)}{q_p - 1} = \frac{1}{p^2 - 1}$ (inert) or $\frac{1}{2(p-1)}$ (ramified $p=d$). Exact and sharp: `‖ϖ^{p+1}/p‖_p = p^{1 - 1/(p-1)} > 1` strictly requires $p > 2$ inert (`one_lt_norm_pow_div_of_inert`, `Couplings.lean:450` area; $p=2$ splits or is excluded by $d \equiv 7 \pmod 8$ and $18480 \mid q_0$).
3. **Near-pair truncation threshold `n♯ = ⌈6 b / k⌉₊`** (`NearPairs.lean:250` area):
   - Governs the `lossProduct B_τ` error bound; matches the `6 * denominatorBudget` height slack in `TwistedValueHeights.lean:1015`.
4. **Elementary Divisor Size Conditions (`IsLargeDegree`, `HeckeEdges.lean:772`, `ElementaryDivisorTheorem.lean:427, 467, 611, 883`)**:
   - Parahoric block condition: `0 < r` and **`2 r ≤ k`** (the block size $r = \lceil \log_p m \rceil$ cannot exceed half the rank $k = r_{\text{target}} + 1 - m$).
   - Large-degree condition: `a^4 ≤ q` and **`(N k log q / θ)^5 P^{3 r} ≤ a`**, where $q = P^N = |\text{ResField } W|$. This forces $a = x b$ to dominate the Levi averaging degree $D = N n k (\ell + 2) P^\ell < P^N$ (`AveragingMap.lean:716-718`) and makes the colength bound `(3 c_div + θ m) |X| |I|` tiny.
   - Precision & colength constants:
     - `multinomialExponent k` $= c_0 = k^2 \cdot \text{frobExp} \cdot N = k^2 \log_p q$ (`ElementaryDivisorTheorem.lean:441`)
     - `congruencePrecision k` $= c = 5 N c_0$ (`ElementaryDivisorTheorem.lean:427`; needed so `Add * Inv ≡ p^{2 N c_0} (mod w^c)` clears `2 N c_0` plus margin)
     - `divisorConstant k n r` $= c_{\text{div}} = N n (P^{-2 r} + r^2 / (k P))$ (`Depth.lean:791`)
     - Exact linear combination in `ElementaryDivisorTheorem.lean:1138`: $1 \cdot c_{\text{div}}$ (end lattice) $+ 2 \cdot c_{\text{div}}$ (middle $2 N c_0 \le 2 c_{\text{div}}$ via `mul_multinomialExponent_le_divisorConstant`, `:611`) $+ \theta m$ (exceptional generators) $= 3 c_{\text{div}} + \theta m$.
   - Transfer to `MarkOperator.lean:119, 305, 413`: `θ = 1 / (m² f)`, `j_p = ⌈2 m f a / p⌉` (`collisionExponent`, `ShortColumns.lean:122`), and `3 c_div ≤ 12 a ℓ / (m p)`, giving total Hecke colength $\le \text{loss}(p) \cdot \dim(\text{SourceForm})$.
5. **Global Scales in `AdmissibleData` / `OneSidedBound.lean:42, 82`**:
   - `(log b)^{100} ≤ x`, **`x^{10^6} ≤ x_1`**, **`x_1^{10^6} ≤ b`**, `m ∈ [√x, 2√x]`, `2^{towerExp} = m^{22}` (`PrimeSums.lean:82`), `q₀` a multiple of `18480 = 16 · 3 · 5 · 7 · 11`. Notice how $m \approx x^{1/2}$ forces $x^{10^6} \le x_1$ and `IsLargeDegree` simultaneously with room to spare (`errorUnit = f a log³ b` vs `f a log⁴ b` vs `f a log⁵ b` in `(⋆)`).

---

## 4. Community & Audit Takeaways

### 4.1 What a Sceptical Working Number Theorist Would Question First (with Exact Lean Answers)

1. **"You use Katz's formal group slope $\frac{1}{p^2-1}$ at inert $p$, which only holds if the formal group over $\mathcal{O}_K$ truly has height 2 and the parameter $z$ matches. How do you know the theta series doesn't vanish or lose a $p$-unit factor in its leading term?"**
   - **Exact Lean Answer**: `CMLattice.norm_coeff_taylorVia_translatedX_eq_one` (`src/New/Derivatives/FormalGroup/FrobeniusCongruence.lean:431`) proves $\|[z^{p-1}] x(z)\|_p = 1$ via the $3$-term ODE recursion `norm_coeff_pow_taylorVia_translatedX_recursion_lt_one` (`:359`), and `CMLattice.norm_coeff_exponentSeries_eq_one` (`src/New/Derivatives/FormalGroup/Exponent.lean:512`) proves $\lambda_{e,0}$ is a unit for odd $e$.
2. **"Why doesn't expanding a multi-dimensional Weil-representation Schwartz function at $p \mid q_1 d$ introduce $q_1 d$ denominators in your theta-product decomposition?"**
   - **Exact Lean Answer**: `exists_isTightFrame_coprime` (`src/New/Derivatives/Vacuum/ShortVectors.lean:292`) and `Data.exists_isTightFrame` (`:679`) explicitly build tight frames of length $\le (d q_1)^6$ coprime to $q_1$ with `HasUnitLinearForm` at *all* primes $p$, while `norm_intVacuum_le_one` (`src/New/Derivatives/Vacuum/IntegralVacuum.lean:457`) and `exists_jetSeries_map_eq_thetaProd_pow_mul` (`src/New/Derivatives/Vacuum/StandardDataProducts.lean:490` area) verify $p$-integrality at every prime including $p \mid q_1 d$.
3. **"Even if 6 copies cancel $\Theta$ via Lagrange's 4-squares identity, how do you simultaneously differentiate $z_0 = z' + z''$ to pull down negative-valuation factors $\varpi^{p+1}/p$ AND still match arbitrary remaining exponents $\eta$?"**
   - **Exact Lean Answer**: `exists_scaledThetaProd_mem_mul_eq_one` (`src/New/Derivatives/Sharpness/LeastValuation.lean:526`) builds the invertible 6-copy unit, `couplingSubst` + `leastValLE_six_of_isCouplingFamily` (`src/New/Derivatives/Sharpness/Couplings.lean:364, 586`) attains the negative coupling valuations on copies `0..5` using `one_lt_norm_pow_div_of_inert`, `leastValLE_six_zero_of_inert` (`src/New/Derivatives/Sharpness/Cases.lean:150` area) handles $\eta$ on copies `6..11`, and `LeastValLE.add` (`LeastValuation.lean:280` area) multiplies them on `twelveSpace` (`BoundAttained.lean:157`).
4. **"How do you rule out cascading partner collisions when you construct the `IsCouplingFamily` in `Sharpness`? Couldn't $b$-places overlap?"**
   - **Exact Lean Answer**: `notMem_bPlaces_of_two_partners` and `IsNearPair` (`src/New/Derivatives/Sharpness/NearPairs.lean:95, 130` area) invoke `D.sparse` to prove vertex-disjointness (`exponent_unique`, `eq_and_eq_of_partner_eq`, `end_ne_start`), while `error_le_padicValNat_lossProduct` bounds all tail and multinomial errors cleanly.
5. **"Wait — `embValRing ⊂ ℂ` is NOT Noetherian! How can `ElementaryDivisorTheorem.lean` talk about 'colength' and 'elementary divisors' of Hecke operators over a non-Noetherian valuation ring?"**
   - **Exact Lean Answer**: `ColengthDvd` (`src/New/Reduction/Lattices/Colength.lean:39`) defines index divisibility purely via finite-rank transition matrices with $\det \mid z$ (never assuming Noetherian submodules!). Finite-rank matrix diagonalization over a general `ValuationRing` (`exists_elementary_divisors_mod_summand` in `ElementaryDivisorTheorem.lean` and `exists_mul_inv_eq_mul_diagonal` in `Edges.lean:110` area) plus an explicit `w^{c-1}` power Nakayama lemma (`smul_top_le_of_le_sup_smul_top`) avoids Noetherianity completely.
6. **"Where exactly does the monstrous `directionAmount` cancel, and could an $s_\infty$ vs. $s_{\text{fin}}$ discrepancy survive by a factor of $2$ or $k$?"**
   - **Exact Lean Answer**: On the upper side, `ArchimedeanSize.lean:187` (`mainAmount_sub_add_two_mul_sum_gain`) proves literally by `ring` that `mainAmount - m * totalRemainder + 2 * ∑ gain * log = m * #aPlaces * mainPrimeSum + m * k * ∑ jetSize`. On the lower side, `BoundAttained.lean:456` (`exists_rpow_neg_localPrimeSumTotal_le_norm_coeff`) -> `TwistedValueHeights.lean:1015, 1235` -> `LiftVolumeHeight.lean:731` -> `LongForms.lean:192, 274` produces `d * mainAmount`. Both cancel identically inside `MainInequality.lean:103-160`.

### 4.2 Clean Extraction Opportunities (`TauCeti` / `ShortGRH`)

1. **`ValuationRing` Colength & Smith/Hermite Engine (`New/Reduction/Lattices/Colength.lean` + `ElementaryDivisors/ElementaryDivisorTheorem.lean:1-420`)**:
   - The `ColengthDvd` / `IsOntoUpToColength` API and `ValuationRing` matrix normal forms (`exists_elementary_divisors_mod_summand`, `exists_mul_inv_eq_mul_diagonal`) have zero dependency on modular forms or CM curves. Extracting this into `TauCeti.RingTheory.ValuationRing.Colength` gives Mathlib/TauCeti a clean reusable elementary-divisor theory for arbitrary (non-Noetherian) valuation domains such as $\mathcal{O}_{\mathbb{C}_p}$ and `embValRing`.
2. **Modular Polynomial Method & Averaging over $\operatorname{GL}_k(\mathbb{F}_q)$ (`ElementaryDivisors/` generic core)**:
   - `FrobeniusCycle`, `RootLemma.lean` (`stepanov_count`, `gaussFiltration`), `PieriCone.lean` (`det_interlacing_indicator` / Dixon–Anderson), `DefectCount.lean` (`volume_degreeSlab_le`), and `InvariantAverage.lean` (`exists_isAdjointWeight` via multinomial dual Schur) form an abstract theorem about parahoric/Hecke elementary divisors of $\operatorname{GL}_k$-representations in mixed characteristic (`(3 * divisorConstant + θ * m) * |X| * |I|`). Extracting `FrobeniusCycle` as a standalone package in `TauCeti` would cleanly isolate the most subtle representation-theoretic combinatorics of the entire proof.
3. **Constructive Coprime Tight Frames in Cyclotomic/CM Fields (`Vacuum/ShortVectors.lean`)**:
   - Short vectors / tight frames over $\mathcal{O}_E$ with `HasUnitLinearForm` at every prime and norm bound $(d q_1)^6$ (`exists_isTightFrame_coprime`) could live cleanly in `TauCeti.NumberTheory.CMField.TightFrames` for any CM/cyclotomic lattice application (`ShortGRH` or sphere-packing / Hecke eigenvalue bounds).
4. **4-Square Valuation Cancellation on $E^6$ (`Sharpness/LeastValuation.lean`)**:
   - `padicInt_sum_four_squares` + inverting a formal power series product via $1 + \sum_{c=1}^4 a_c^2 = 0$ is a slick self-contained $p$-adic analysis trick applicable to lower-bounding Taylor coefficients of general abelian/theta functions.
