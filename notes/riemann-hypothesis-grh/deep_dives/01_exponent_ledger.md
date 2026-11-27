# Quantitative Exponent & Constant Ledger for `New` (`rh_grh`)

All references below are verified directly against disk in `src/` with exact line numbers and Lean identifiers. Note that `New/Reduction/Parameters.lean` does not exist on disk; `New.Parameters` is defined in `src/New/Reduction/Data/FieldsAndPlaces.lean:73`.

---

## 1. Master Parameter, Exponent & Constant Ledger

### 1.1 Base Field, Root-of-Unity & Conductor Constants

| Symbol / Name | Exact Lean Definition (`src/...:line`) | Mathematical Role | Forcing Constraint & Tightness |
| :--- | :--- | :--- | :--- |
| `P.q₀`, `18480` | `New.Parameters` (`src/New/Reduction/Data/FieldsAndPlaces.lean:73-83`): `dvd_q₀ : 18480 ∣ q₀`, `q₀_dvd_and_not_dvd : q₀ ∣ 2 * (d + 1) ∧ ¬q₀ ∣ d + 1`. Instantiated in `New.grh` (`src/New/Reduction/OneSidedBound.lean:254-258`) with `q₀ := 18480 * q` | Level / modulus of induction for $\chi$, base cyclotomic modulus for $K(\zeta_{q_0})$, and conductor forcing congruence $d \equiv q_0/2 - 1 \pmod{q_0}$ | **Triple hard arithmetic forcing (knife-edge LCM):** $18480 = 2^4 \cdot 3 \cdot 5 \cdot 7 \cdot 11$. (1) $16 \mid q_0$ plus `q₀_dvd_and_not_dvd` forces $8 \mid d+1$ with odd quotient, hence $d \equiv 7 \pmod 8$ (`instPrimeSevenModEight`, `FieldsAndPlaces.lean:94-96`), required by `LFunction_ne_zero_of_primeRemainder_le` (`Zeros/Criterion.lean:41-42`) and `isPolar_primeRemainder` (`Zeros/PrimeError.lean:430`). (2) $3 \cdot 18480 = 11 \cdot 5040$ puts $\zeta_{5040} \in E$ (`PrimeDecomposition.lean:145-150`). (3) Having $2,3,5,7,11 \mid 18480$ forces every prime $< 13$ to divide $q_0$, hence split in $K$ (`chiK_eq_one_of_dvd`, `FieldsAndPlaces.lean:153`), giving $13 \le p$ for every nonsplit prime (`thirteen_le_of_chiK_ne_one`, `FieldsAndPlaces.lean:171`). |
| `5040` | `HasPrimitiveRoot5040` (`src/Lib/Adelic/Adeles/Basic.lean:439-441`); instance for `P.E s` at `src/New/Derivatives/Field/PrimeDecomposition.lean:145-150` | Ensures $E = K(\zeta_{q_1})$ contains $\zeta_{5040}$ | **Forced divisibility LCM ($5040 = 2^4 \cdot 3^2 \cdot 5 \cdot 7$):** `Adeles/Basic.lean:465,476` only uses $4 \mid 5040$ (to extract $i = \sqrt{-1}$ with $\bar i = -i$) and $7 \mid 5040$ (to extract $\omega = -(\eta + \eta^2 + \eta^4)$ solving $\omega + \bar\omega = 1, \omega\bar\omega = 2$), making $E/E^+$ unramified at all finite primes (`PrimeDecomposition.lean`). Any multiple of $\operatorname{lcm}(4,7)=28$ (together with $3 \mid q_1$) would give $i,\omega$; $5040 = 7!$ is a convenient super-multiple dividing $3 q_0$. |
| `13 ≤ p` | `thirteen_le_of_chiK_ne_one` (`src/New/Reduction/Data/FieldsAndPlaces.lean:171-174`): `have h_dvd : p ∣ 18480 := by interval_cases p <;> trivial` | Lower bound on every inert/ramified prime $p$ | **Consequence of `18480 ∣ q₀`:** Consumed in `MarkOperator.lean:66,325,409` (`isLargeDegree_of_le_card`), where proof line 83 actually only needs `3 ≤ p` (`3 ^ D.m ≤ T.q`), though $p \ge 13$ cleanly exceeds small ramified primes ($2,3,5,7,11$). |
| `P.d`, `K` | `P.d : ℕ` (`FieldsAndPlaces.lean:75`), prime $d \equiv 7 \pmod 8$, $d \equiv q_0/2 - 1 \pmod{q_0}$, $64 < d$ (`FieldsAndPlaces.lean:145`) | Imaginary quadratic field $K = \mathbb{Q}(\sqrt{-d})$ (unramified outside $d$, $2$ splits) | Existence via Dirichlet's theorem / Linnik-type bound modulo $q_0$ inside `OneSidedBound.lean:259` (`exists_prime_modEq`). |
| `s = D.towerExp`, `2^s = m^22` | `exists_m_eq_two_pow : ∃ e : ℕ, m = 2 ^ (e + 1) ∧ towerExp = (e + 1) * 22` (`AdmissibleData.lean:125`), bounded by `towerExp ≤ 32 * logX` (`AdmissibleData.lean:129`); built in `Existence.lean:403,422` | Height $s$ of the cyclotomic $\mathbb{Z}_2$-tower $E = K(\zeta_{q_1})$ so that $2^s = m^{22}$ | **Exponent `22` is tightly constrained from below by two bottlenecks:** (1) `CrystallineDefect.lean:203`: `D.halfGap ^ 3 ≤ (2 ^ D.towerExp) ^ 12`. Since $\text{halfGap} = r^8$ and $r \le 3 x^5$, $(\text{halfGap})^3 = r^{24} \le 3^{24} x^{120}$; meanwhile $(2^s)^{12} = (m^{22})^{12} \ge (x^{1/2})^{264} = x^{132}$. Had the exponent been $20$, $(m^{20})^{12} \approx x^{120}$ would lose the constant headroom against $3^{24}$. (2) `Existence.lean:421-437` (`mul_rank_lt_two_pow`) and `Filling.IsAdmissible.k_le_f` (`Setup.lean:134`): $2^s = m^{22} > (\varrho+1)k$ and $f = [E:\mathbb{Q}]_{\infty} \ge m^{22} \approx x^{11} \gg k \approx x^5$. Also `MarkedPrimes.lean:156-176` uses `¬ D.IsPlusMinusOneModLifts p` ($m \nmid p \pm 1$) against $2^{s+1} = 2 m^{22} \ge m$ so $m \mid \operatorname{ord}(-p)$ in $(\mathbb{Z}/q_1)^\times$. Conversely `towerExp ≤ 32 logX` holds because $2^{22(e+1)} \approx x^{11}$ yields $s \approx (11/\log 2)\log x < 32 \log x$ (`Existence.lean:441,499`). |
| `l₀ s` | `New.l₀ (s : ℕ) : ℕ := 3 ^ (Nat.log 3 s + 4)` (`FieldsAndPlaces.lean:99`) | Degree of auxiliary $3$-power subextension inside $K(\zeta_{q_1})$; Behrend short-arc bound | **Forced by Behrend's 3-AP-free sparseness + short arcs:** `mul_lt_l₀ : 27 * s < l₀ s` (`FieldsAndPlaces.lean:101`) is used directly in `CrystallineDefect.lean:207,213`: $a + b \le 24 s \le 27 s < l_0$, while `l₀_le_mul : l₀ s ≤ 81 * s` (`FieldsAndPlaces.lean:106`) keeps $l_0$ polylogarithmic in $x$ so that $x_1^{3 l_0^2} \le \sqrt{b}$ holds in `Sizes.lean:60` and `MarkOperator.lean:107`. Because $3^{\lfloor \log_3 s \rfloor + 1} > s$, multiplying by $3^3 = 27$ forces `+ 4` (`3^4 = 81`). |
| `towerDeg s`, `D.f` | `New.towerDeg := 3 ^ (Nat.log 3 s + 5) * 2 ^ s` (`= 3 * l₀ s * 2 ^ s`) (`FieldsAndPlaces.lean:112,115`); `card_placeClass_eq_one_eq_towerDeg` (`FieldsAndPlaces.lean:365`); `D.f := Fintype.card D.Φ` (`Sizes.lean:93`: $m^{22} \le f$) | Degree $[E : K] = \operatorname{towerDeg} s$, so $f = \varphi(q_0) \cdot \operatorname{towerDeg} s$ (`Sizes.lean:93`) | Bounded below by `D.m ^ 22 ≤ D.f` (`Sizes.lean:93`, hence $x^{11} \le f$) and bounded above via `HasLogUpper N (11 * D.logX + (Real.log D.logB / 5 + P.constantBound))` (`MarkOperator.lean:93`). The extra factor `3` in `3^(...+5)` ensures `5040 ∣ 3 * q₀` (`HasPrimitiveRoot5040`, `PrimeDecomposition.lean:145-150`) and `exists_three_term_free` (`Existence.lean:95`). |
| `P.q₁ s`, `P.q₂ s` | `q₁ := P.q₀ * towerDeg s` (`FieldsAndPlaces.lean:119`); `q₂ := (P.q₀ * P.d) ^ (s + 6)` (`FieldsAndPlaces.lean:184`) | Conductor $q_1$ defining $E = K(\zeta_{q_1})$; auxiliary modulus $q_2$ satisfying `q₁ * d ∣ q₂` (`FieldsAndPlaces.lean:190`) | Exponent `s + 6` ensures `towerDeg s * d = 3^(Nat.log 3 s + 5) * 2^s * d` divides `(q₀ * d)^(s + 6)` since $2,3 \mid q_0$ (`FieldsAndPlaces.lean:190`), while `Sizes.lean:110` bounds $\log q_2$ linearly in $s$ (`q₂_le`) for discriminant and class-number bounds (`Existence.lean:441`, `Sizes.lean:125`). |

---

### 1.2 Asymptotic Scale Hierarchy (`x`, `x₁`, `b`, `m`, `r`, `k`, `t`, `a`)

Every scale lives in `New.Data` (`src/New/Reduction/Data/AdmissibleData.lean:84-275`, bounds in `Sizes.lean:17-30` and `Existence.lean:804-902`):

| Symbol | Exact Lean Definition (`src/...:line`) | Role & Asymptotic Size | What Forces This Exact Exponent / Relation |
| :--- | :--- | :--- | :--- |
| `x`, `logX` | `D.x : ℕ`, `D.logX : ℝ` (`AdmissibleData.lean`); `D.x = x`, `exp D.logX = x` (`Existence.lean:804`) | Target prime-remainder cutoff $x \to \infty$ | Drives $m \asymp \sqrt{x} \implies R_{q_0}(x) \ll_{\varepsilon} x^{-1/2 + 6\varepsilon}$. |
| `x₁`, `logX₁` | `1e6 * logX ≤ logX₁` (`AdmissibleData.lean:109`). In `Existence.lean:804`: $\log x_1 = \lfloor W \rfloor \ge x^{\varepsilon/12}$ (`OneSidedBound.lean:88`) where `log logB ≥ 6 log logX₁` (`AdmissibleData.lean:112`) | Cut-off between small nonsplit primes ($p < x_1$) and large primes ($p_0, p_1, N \ge x_1$), and scale of remainder subtraction $R_{q_0}(x_1), R_1(x_1)$ | **Upper & lower squeeze:** Must be large enough that unconditional PNT (`PrimeNumberTheorem.lean`) makes $|R(x_1)| \le (\log x_1)^{-B} \le x^{-2} \ll x^{-1/2}$ (`OneSidedBound.lean:111-126`, needing `x^(ε/12) ≤ log x₁`). Must be small enough relative to `b` that `x₁^(3 * l₀^2) ≤ √b` (`Sizes.lean:60`, forced by `MarkOperator.lean:107-108`!), which requires $\log\log b \ge 6 \log\log x_1$ (`AdmissibleData.lean:112`). |
| `b`, `logB` | `D.b`, `D.logB`; `1e6 * logX₁ ≤ logB`, `6 * log logX₁ ≤ log logB`, `1e12 * constantBound ≤ log logB`, `100 * log logB ≤ logX` (`AdmissibleData.lean:105-112`) | Weight on sparse set `D.bPlaces` (making $M = p_0 p_1 \in [b^{20}, b^{22}]$, $N \le b^{60 n}$) and error scale | **Two-sided squeeze on `log b`:** Needs $\log b \le 2 x^\varepsilon$ (`OneSidedBound.lean:87`) so `log^6 b / m` only loses $x^{6\varepsilon}$ (`OneSidedBound.lean:140`). Conversely `Filling.IsAdmissible.mul_rootDiscr_pow_le` (`Setup.lean:137`) requires `(200 f k rd)^1000 ≤ b` (generous convenience power ensuring $b \gg (f k \cdot \mathrm{rd}_E)^{1000}$), and `MarkOperator.lean:107-108` requires $x_1^{3 l_0^2} \le \sqrt{b}$ — achieved because `100 * log logB ≤ logX` implies $\log b \le e^{(\log x)/100} \le x^\varepsilon$ while still $\log b \ge (\log x_1)^6$. |
| `m`, `ϱ` | `m_mem : (m : ℝ) ∈ Icc (exp (logX / 2)) (2 * exp (logX / 2))` (`AdmissibleData.lean:121`), `m = 2 ^ (e + 1)` (`:125`); `ϱ := D.m / 2 - 1` (`LabelsAndIndexTypes.lean:246`) | Number of theta lifts (`m`) and Witt index (`ϱ`) of the ambient group $U(\varrho+1, \varrho)$ | **Exact source of the GRH $x^{-1/2}$ saving:** Every factor in `(⋆)` keeps $m$ in front of `totalRemainder` (`D.m * D.totalRemainder` in `MainInequality.lean:160`), which upon dividing by $m a |\mathrm{bPlaces}|$ gives $\varphi(q_0) \log^6 b / m \le 64 \varphi(q_0) x^{6\varepsilon - 1/2}$ (`OneSidedBound.lean:77,164`). Meanwhile $m$ is a power of $2$ so $(p \text{ inert}, m \nmid p \pm 1) \implies m \mid \operatorname{ord}(-p)$ in $(\mathbb{Z}/q_1)^\times$ (`MarkedPrimes.lean:156-176`). Also `m ≥ 10000` (`Magnitudes.lean:458`), and on `RealPlaceSizes`, `ϱ ≥ 10⁸` (`RealPlaceGauge.lean:321`, forced below). |
| `ϱ ≥ 10⁸` (`vs 10⁵`) | `RealPlaceSizes.ten_pow_le_varrho : 10 ^ 8 ≤ 𝔰.ϱ` (`src/New/Spanning/Frames/RealPlaceGauge.lean:321`) vs `Filling.IsAdmissible.ten_pow_five_le_varrho : 10 ^ 5 ≤ 𝔰.ϱ` (`src/New/Spanning/Unfolding/Setup.lean:126`) | Lower bound on number of hyperbolic planes $\varrho$ (`n = ϱ + 1`) | **Surprising split between two subsystems:** The adelic/unfolding core (`Setup.lean:126`, `Unfolding/Terms.lean:506`) only needs `10^5 ≤ ϱ` (e.g., `mul_sq_le_cube : C n^2 ≤ n^3` for `C ≤ 10^5`, or `LatticesOfCorank.lean:682` bounding `b`-exponents by `10^5 n^9`). However, the Archimedean dyadic shell decay at complex places (`RealShells.lean:164,597-604`, instantiated inside `RealPlaceSizes`) forces **`10^8 ≤ ϱ`**! Explicitly, `RealShells.lean:598-604` proves `exp_t : 10^8 * n^4 + (K + 6) ≤ s` from `n^7 + K = k = s + 3n + 6` and `10^8 ≤ ϱ < n`: since $n^7 \ge (10^8 + 1)^3 n^4 > 10^{24} n^4$, why $10^8$? Because `RealShells.lean:478` ALSO uses `mul_pow_four_le_s : 10^10 * n^4 ≤ s` (a factor $100$ larger than $10^8$, to beat `L^(10^9 n^4)` from `400 n^2` times box constants + `10^8 n^4` threshold!). Note $10^8 \cdot n^4 \le 10^{10} \cdot n^4 \ll n^7$ easily once `n ≥ 10^4`; `10^8` is a **generous convenience constant** matching $10^9$ and $10^{10}$ in `RealShells.lean`. |
| `r`, `k`, `t` | `r_mem : (r : ℝ) ∈ Icc (exp (5 * logX)) (3 * exp (5 * logX))`, `r = 3^(...+?)` (`AdmissibleData.lean:122,126`); `k := r + 1 - m` (`AdmissibleData.lean:207`); `t := 5 * r` (`:210`); `n j := k + j * (t + 1)` (`:232`) | Ranks: $Y_0$ has rank $r$; $X_0$ has rank $k$; each lift increases rank by $t+1 = 5r+1$; $X_m$ has rank $n_m = k + m(t+1)$ | **Multiple intersecting constraints force `r ≍ x⁵` and `t = 5r`:** (1) `Filling.IsAdmissible.pow_le_k` (`Setup.lean:132`): $1000 (2\varrho + 2)^9 \le k$. Since $2\varrho + 2 = m \le 2 x^{1/2}$, $(2\varrho+2)^9 \asymp x^{4.5}$; choosing $r \asymp x^5$ clears $x^{4.5}$ with $x^{0.5}$ room (`hundred_mul_m_le_k`, `Magnitudes.lean:594`; also satisfies `MarkOperator.lean:139`: `r_ceil^2 * m ≤ k`, since `r_ceil ≤ l₀ ≪ x^{0.1}` and `m ≈ x^{0.5}`, and `LiftChains.lean:564`: `2 n_m ≤ r t`, which simplifies to `2(r + 5mr) ≤ 5 r^2`, i.e., `10m + 2 ≤ 5r`). (2) `OneLift/ComparisonOperator/ThreeExchanges.lean:134` needs `t > 11 m` (easily true for `t = 5r ≫ 5·2·m` when $r \asymp x^5$). `t = 5r` also forces `halfGap = r^8` beats `2(k + t + 1) ≤ halfGap` and `ChosenGroupOrder` degree `(r t)^2` stays small relative to `x` / `b`. |
| `halfGap`, `gap`, `reducedHalfGap` | `halfGap := D.r ^ 8` (`AdmissibleData.lean:213`), `gap := 2 * D.halfGap` (`:216`), `reducedHalfGap := (D.halfGap - (D.t + 1)) / 2` (`:219`) | Distance between consecutive blocks of Harish-Chandra parameters in $X_j$ and $Y_m$ | **Forced by `Rows.lean:509-510` (`isCuspKernel_typeKernel_paramW`) and `CrystallineDefect.lean:203`:** `Rows.lean:510` requires `500 * D.r ^ 3 ≤ D.halfGap` (for finite dimensionality / cusp kernel separation of `typeKernel`). Why $r^8$ instead of $r^4$? Generous margin (`r^3 ≪ r^8`, leaving room for `m * gap + halfGap ≤ halfGap^2` in `Estimates.lean:211`, `gap_threshold`, and `halfGap^22` in Galois congruences), while STILL small enough that `halfGap^3 = r^24 ≤ (3 x^5)^24 ~ x^120 ≤ (2^s)^12` (`CrystallineDefect.lean:203`)! |
| `a`, `aPlaces`, `bPlaces`, `offWeight` | `a := D.natX * D.natB` (`AdmissibleData.lean:222`), `offWeight := a / D.natX₁` (`:225`), `weight σ := if σ ∈ bPlaces then natB else offWeight` (`:152-154`, `Magnitudes.lean:565`), `aPlaces := {τ : D.Φ \| P.placeClass ... τ = 1}` (`:245`) | First-row height `a` at `aPlaces`; Behrend sparse set `bPlaces` (`towerDeg ≤ bPlaces.card * logB`, `:139`); weights are $b$ on `bPlaces` and $x b / x_1$ elsewhere | Because `a = x b` and $\kappa(\tau) = b$ on `bPlaces`, we have $a / \kappa(\tau) = x$ at `bPlaces` and $a / \kappa(\tau) \approx x_1$ elsewhere (`PrimeSums.lean:141,171`). Thus `offWeight = a / x₁` cuts off primes $> x_1$ (`PrimeSums.lean:193`), leaving `bPlaces` to pick up $R_{q_0}(x) - R_{q_0}(x_1)$ while all `aPlaces` contribute $R_1(x_1)$ (`PrimeSums.lean:183`). Moreover `#bPlaces ≥ towerDeg / logB` (`AdmissibleData.lean:139`) preserves `0 ≤ mainAmount` (`PrimeSums.lean:301`). |

---

### 1.3 Level Primes `M = p₀ p₁`, Prime `N`, and Auxiliary Moments & Error Budgets

| Symbol | Exact Lean Definition (`src/...:line`) | Role | Forcing Constraint & Tightness |
| :--- | :--- | :--- | :--- |
| `M = p₀ p₁` | `M := D.levelPrime 0 * D.levelPrime 1` (`AdmissibleData.lean:242`); `levelPrime i ∈ [exp logB ^ 10, exp logB ^ 11]` (`AdmissibleData.lean:159`, `Existence.lean:318`: $M \in [b^{20}, b^{22}]$ relaxed in `Setup.lean:151-153` to $b^{19} \le M \le b^{23}$); `p_i ≡ 1 mod q₂²` (`:158`) | Finite level of source forms; primes chosen above split $p_i$ in $K(\zeta_{q_1})$ so $M \mid r \iff \forall w, r \equiv 0 \pmod w \land \bar r \equiv 0 \pmod w$ | **Why $p_i \in [b^{10}, b^{11}]$ ($M \in [b^{20}, b^{22}]$):** (1) `Filling.IsAdmissible.le_M : b^19 ≤ M` (`Setup.lean:153`) is forced directly by `FillingAdmissible.lean:571,636,653`! Specifically, `abs_log_mainSecondMoment_div_identitySecondMoment_sub_le` gives ratio $\approx (M b^{-15/2})^{kf}$ with $\pm k f \log b / 4$ error and factorials $\le b^{5kf/4}$; $b^{19} \le M \implies 19 - 15/2 - 1/4 > 11$ (actually $19 - 7.75 = 11.25 > 11$, giving `b^(11kf) D_id ≤ D_main` in `FillingAdmissible.lean:636`!), and the upper bound $M \le b^{23}$ keeps completion/period costs `(M/b^6)^(kf)` polynomial in $b$ (and ensures `chosenGroupOrder ≤ M^((rt)^2 f)` is sub-exponential in $x$ relative to $a$). |
| `logLevelMin`, `N` | `Parameters.logLevelMin` (`AdmissibleData.lean:74-76`): $m \frac{1}{f} \sum_\tau \log \kappa(\tau) + (m - 1) \log \frac{M \cdot \mathrm{rd}_E}{2\pi} - \frac{15}{2} \log b$; `log N ∈ [logLevelMin, logLevelMin + √logB]` (`AdmissibleData.lean:167`), prime $N \equiv 1 \pmod{q_2^2}$ (`:166`) | Auxiliary split prime $N$ of $E$ giving the ambient level of $Y_0$ for the Bessel / Poincaré second moment | **THE TIGHTEST KNIFE-EDGE EQUATION IN THE PROOF (`-15/2` forced from BOTH directions):** (1) **Lower bound (`N ≥ N₋`):** In `ArchimedeanSize.lean:120`, `N` enters the Archimedean norm bound of `Y_m`-shifted forms via $-(a - \dots)\log N$, needing $\log N \ge \log N_-$ to cancel $m(s_\infty(a) - s_{\mathrm{main}}) - m\kappa \dots$ down to `32 * a * logB` (`ArchimedeanSize.lean:187-192`). (2) **Upper bound (`N ≤ N₋ e^{\sqrt{\log b}}`):** In `FillingAdmissible.lean:571`, the second-moment ratio $\mathcal{D}_{\mathrm{main}}/\mathcal{D}_{\mathrm{id}}$ equals $(M b^{-15/2})^{kf} \cdot \mathrm{card}(\mathrm{BesselCoord}) (k-1)!^f$ up to $b^{\pm kf/4}$, because `log N ≤ logLevelTarget + √logB` cancels the mass-ratio discriminant/weight product down to `(log M - 15/2 * logB) * k * f`. With `b^19 ≤ M` (`Setup.lean:153`) and `log_factor_le ≤ (5/4) f k logB` (`FillingAdmissible.lean:647`), the exponent margin above the required `b^(11 k f)` lower bound (`FillingAdmissible.lean:636`) is $19 - \frac{15}{2} - \frac{1}{4} = 11.25 > 11$ (a total slack of only $\frac{1}{4}\log b$ per $k f$!). Note also `N_le_pow : N ≤ b^(60 n)` (`FillingAdmissible.lean:666`), from `log N ≤ 30 (2ϱ + 2) logB`. |
| `errorUnit` | `abbrev errorUnit := D.f * D.a * D.logB ^ 3` (`AdmissibleData.lean:262`) | Base sub-logarithmic error unit $f a \log^3 b$, magnified by `logB` in `MainInequality` | Absorbs `allowedLoss` (`ShortColumns`), Archimedean slack, `denominatorBudget`, and `indexLe` contributions, while still $f a \log^5 b \ll m a |\mathrm{bPlaces}|$ since $f / |\mathrm{bPlaces}| \le \log b$, giving $\log^6 b / m$! |
| `denominatorBudget` | `denominatorBudget := D.errorUnit / (D.m * D.k)` (`FitTwists.lean:162`) | Allowable height loss per lift ($j$) and per dimension in Theorem C (`LiftVolumeHeight.lean:731`) | Exact normalization so summing over $1 \le j \le m$ and $k$ copies in `integral_forms_long_with_completion_cost` (`LongForms.lean:223`) gives `m * k * denominatorBudget * logB = errorUnit * logB = f a log^4 b`! |
| `1 + 9 / D.b ^ 4` | `sum_hilbertSchmidtNorm_scaledPoincare_sq_le` (`SpanningTheorem.lean:274`) from `Moments.lean:579` and `MomentBounds.lean:441-452` (`le_one_add_nine_mul_of_le_add`) | Upper bound on the second moment $\sum \|\tilde P_s \varphi\|^2 \le (1 + 9 b^{-4}) \cdot \mathcal{D}_{\mathrm{main}}$ | **Derived algebraically, NOT arbitrary:** From `secondMoment_fixer_isOpenElement_le` (`MomentBounds.lean:281`), open elements contribute $(1 + 4 b^{-4}) \mathcal{D}_{\mathrm{main}}$ (since $(1 + b^{-4})^2 \le 1 + 4 b^{-4}$); non-open elements contribute $\le b^{-4} \cdot \mathrm{LHS}$ (`sum_not_isOpenElement_le`, `MomentBounds.lean:417`). Thus $M \le (1 + 4x) C + x M$ for $x = b^{-4} \le 1/10$, and `le_one_add_nine_mul_of_le_add` (`MomentBounds.lean:441-446`) solves $(1 - x)(1 + 9x) - (1 + 4x) = x(4 - 9x) \ge 0$ (`4/9 > 1/10`). |
| `4 / D.b ^ 2`, `(8 * D.b ^ 2)⁻¹`, `16 * ε` | `SpanningTheorem.lean:343` uses `ε₀ = (8 * D.b^2)⁻¹`, `isSpread` with `3/2 * ε₀`; `FewTranslates.lean:420,498` uses `(1 - 16 * ε) * d_T`; `ShortAndEnough.lean:399-404` (`enough_forms`) gives `(1 - 4 / D.b^2) * targetDim` | Fraction of `targetDim` missed by spanning `t` translates of `ramifiedSourceForms` | **Evenly split `2/b² + 2/b² = 4/b²`:** (1) `Moments.lean:1239` bounds diagonal near-isometry error by $4 b^{-4} + b^{-6} \le 5 b^{-4} \le (8 b^2)^{-1}$, and $9 b^{-4} \le (8 b^2)^{-1}$. Applying `IsSpread.exists_few_le_finrank_iSup_range` (`FewTranslates.lean:498`) with $\varepsilon = (8 b^2)^{-1}$ gives rank $\ge (1 - 16 \varepsilon) d_T = (1 - 2/b^2) d_T$ and count $\le \frac{5}{2}(1 + \log((16\varepsilon)^{-1})) d_T \le 5 d_T \log(1 + 2b^2)$ (`ShortAndEnough.lean:361-376`). (2) Passing from `SourceForm` to `ramifiedSourceForms` subtracts at most `(f / (N - 1)) * #t * dim SourceForm ≤ (2 / b²) * targetDim` (`ShortAndEnough.lean:378-392`). (3) Total missing dimension $n' \le (4/b^2) d_T$ matches `mul_completion_cost_le` (`LongForms.lean:133`), where $4/b^2$ cancels the $b^2$ inside completion cost $2 x_1^2 b^2 + b$! **Note on `8ε`:** There is **no literal `8 * ε`** in the codebase! The actual constants are **`(8 * D.b ^ 2)⁻¹`** (`SpanningTheorem.lean:343`), **`16 * ε`** (`FewTranslates.lean:420,498`), and **`6 * ε`** (`OneSidedBound.lean:140`). |
| `6 * ε`, `ε/12`, `ε/6` | `OneSidedBound.lean:87-167, 214-243` | Power loss in $R_{q_0}(x) \ll x^{-1/2 + 6\varepsilon}$ before re-scaling $\delta = \min(1/200, \varepsilon/6)$ | **Exact arithmetic:** `logB ≤ 2 x^ε` (`OneSidedBound.lean:87`) raised to the **6th power** in `D.logB ^ 6` from `Data.primeRemainder_le` (`OneSidedBound.lean:46,79`) gives `(2 x^ε)^6 / x^(1/2) = 64 x^(-1/2 + 6ε)`. Meanwhile `eventually_exists_data_scales` (`OneSidedBound.lean:88-101`) ensures $x^{\varepsilon/12} \le D.\mathrm{logX}_1$ (combining $x^{\varepsilon/6}$ from `eventually_exists_data` with $2 \le x^{\varepsilon/12}$), and taking $B \ge 24/\varepsilon$ in PNT (`OneSidedBound.lean:111,123`) gives $(\log x_1)^{-B} \le x^{-2}$. |
| `jetSize`, `directionAmount`, `mainAmount` | `jetSize j := log j! + j log(M / bigOmega)` (`AdmissibleData.lean:266`); `directionAmount := ∑_σ (jetSize (weight σ) - primeSum (weight σ) σ)` (`:271`); `mainAmount := D.m * D.k * D.directionAmount` (`PrimeSums.lean:68`) | Archimedean vs $p$-adic slope discrepancy summed over $m$ lifts and $k$ rows | **Must satisfy `0 ≤ mainAmount` (`PrimeSums.lean:301`)!** Because `n ≤ targetDim` in `MainInequality.lean:145`, cancelling `n * mainAmount` against `targetDim * mainAmount` is ONLY valid because `0 ≤ mainAmount`! |

---

## 2. Exact End-to-End Derivation of the `(⋆)` Covolume Cancellation Inequality & GRH

### Step A: Upper Bound — Short Vectors & Index Budget (`Theorem A`, `ShortAndEnough.lean`)

1. **Vector norm bound (`Theorem A(a)`):**
   `New.Data.span_short_integralRamified_eq_top` (`src/New/Reduction/ShortAndEnough.lean:202-205`):
   ```lean
   theorem span_short_integralRamified_eq_top (D : Data P) :
       Submodule.span ℂ {φ ∈ D.integralRamified |
         ∀ (s : D.chosenGL) (σ : ℂ ≃+* ℂ),
           (D.Θ 1 (D.normalizedPoincare s φ)).normSqAt σ ≤
             Real.exp (D.mainAmount - D.m * D.totalRemainder + D.f * D.a * D.logB ^ 4)} = ⊤
   ```
   **How it is proved (`ShortAndEnough.lean:206-236`):**
   - Start with `φ₀ ∈ D.integralRamified` (`ramifiedSourceForms`, level-$N$ integral forms with auxiliary finite level scaling).
   - Lift through the $m$ definite spaces $X_0 \to \dots \to X_m$, branch to $Y_m$, descend to $Y_0$, translate by $s \in \mathfrak{G} = \text{chosenGL}$, and apply Poincaré series (`normalizedPoincare s φ₀ = c_B • projectedPoincare s φ₀`).
   - By `weylNormSq_compositeLift_le` (`ArchimedeanSize.lean`), the unscaled Poincaré norm squared at every $\sigma \in \operatorname{Aut}(\mathbb{C})$ has log at most:
     $$\mathrm{mainAmount} - m \cdot \mathrm{totalRemainder} + 2 \sum_{p \in \mathrm{smallNonsplitPrimes}} \mathrm{gain}(p) \log p + \mathrm{errorUnit}.$$
     Inside `ArchimedeanSize.lean:83-133, 187-192` (`mul_jetSize_sub_mainPrimeSum_sub_le`), the Euler–Chowla–Selberg constant $c_1 = \operatorname{Re}\frac{L'}{L}(1, \chi_K) = -1 - \gamma_{\mathrm{CS}}(d)$ cancels identically between `jetSize(a)` (via `M / bigOmega`) and `mainPrimeSum`, while $\log N \ge \log N_-$ subtracts the linear weight-and-level terms down to `32 * a * logB`.
   - Meanwhile, the short-column primes $p \in \mathrm{smallNonsplitPrimes}$ gain extra divisibility `gain(p)` (`ShortColumns.lean:98`), minus `allowedLoss(p)` (`Estimates.lean:299`). Scaling by `invGainFactor = ∏ l ^ (-gainExponent l)` (`ShortAndEnough.lean:57,61`, where `gainExponent l = ⌊gain l - allowedLoss l⌋`) injects `norm_invGainFactor` (`ShortAndEnough.lean:121`):
     $$2 \log |c_B| \le -2 \sum_{p \in \mathrm{smallNonsplitPrimes}} \mathrm{gain}(p) \log p + 2\,\mathrm{errorUnit} + 2\,\mathrm{natB}$$
     (`log_invGainFactor_le`, `ShortAndEnough.lean:95`), **exactly cancelling** the `2 ∑ gain(p) log p` term and leaving total log-norm error $\le 3\,\mathrm{errorUnit} + 2\,\mathrm{natB} \le f a \log^4 b$.
   - Taking `Θ 1` maps `D.targetLattice` vectors $\in \mathbb{Z}$ at finite places (`IntegralTargetForms.lean:96`).

2. **Denominator / Index bound (`Theorem A(b)`):**
   `New.Data.indexLe_normalizedPoincare` (`src/New/Reduction/ShortAndEnough.lean:324-326`):
   ```lean
   theorem indexLe_normalizedPoincare (D : Data P) {n : ℕ} {t : Finset D.chosenGL}
       {y : Fin n → D.targetLattice.Carrier}
       (hy : ∀ i : Fin n, ∃ s ∈ t, y i ∈ D.normalizedPoincare s '' D.integralRamified) :
       D.targetLattice.IndexLe y ((#t : ℝ) * Module.finrank ℂ D.ramifiedSourceForms * (2 * D.errorUnit))
   ```
   Uses `finrank_sourceForm_le_two_mul` (`:240`), local prime loss bound `sum_allowedLoss_mul_log_le` (`Estimates.lean:323`: $\le \mathrm{errorUnit}$ after accounting for `invGainFactor` and level $N$ denominator `2 * m * f * b`), and lattice-index multiplicativity.

---

### Step B: Almost-Full-Rank Spanning with Few Translates (`Theorem B`, `ShortAndEnough.lean`)

`New.Data.enough_forms` (`src/New/Reduction/ShortAndEnough.lean:399-404`):
```lean
theorem enough_forms (D : Data P) :
    0 < D.targetDim ∧
      ∃ t : Finset D.chosenGL,
        (#t : ℝ) * Module.finrank ℂ D.ramifiedSourceForms ≤
          5 * D.targetDim * Real.log (1 + 2 * D.b ^ 2) ∧
        (1 - 4 / D.b ^ 2) * D.targetDim ≤
          Module.finrank ℂ ↥(⨆ s ∈ t, LinearMap.range (D.normalizedPoincare s))
```
- `isSpread_goodPoincare` (`SpanningTheorem.lean:343`) verifies the abstract second-moment axiom `IsSpread D.goodPoincare (3/2 * (8 D.b^2)⁻¹)` from:
  1. `isNearIsometry_e₀_comp_scaledPoincare` (`SpanningTheorem.lean:261`): frame deviation $\le 5 b^{-4} \le (8 b^2)^{-1}$.
  2. `sum_hilbertSchmidtNorm_scaledPoincare_sq_le` (`SpanningTheorem.lean:274`): HS second moment $\le (1 + 9 b^{-4}) \mathcal{D}_{\mathrm{main}}$.
- `IsSpread.exists_few_le_finrank_iSup_range` (`FewTranslates.lean:498`) extracts $t \subseteq \mathfrak{G}$ covering rank $\ge (1 - 16 \varepsilon_0) d_T = (1 - 2/b^2) d_T$ with $\#t \cdot \dim \mathrm{SourceForm} \le 5 d_T \log(1 + 2b^2)$.
- Restricting to the codimension $\le f/(N-1)$ subspace `ramifiedSourceForms` loses at most $(2/b^2) d_T$ rank (`ShortAndEnough.lean:378-392`), giving final rank $\ge (1 - 4/b^2) d_T$.

---

### Step C: Determinant / Congruence Lower Bound (`Theorem C`, `LongForms.lean`)

`New.integral_forms_long` (`src/New/Determinant/Twist/LongForms.lean:274-277`):
```lean
theorem integral_forms_long {P : Parameters} (D : Data P) {n : ℕ}
    {y : Fin n → D.targetLattice.Carrier} {δ c : ℝ} (hy : LinearIndependent ℂ y)
    (hn : (1 - 4 / D.b ^ 2) * D.targetDim ≤ n)
    (hδ : D.targetLattice.IndexLe y δ) (hc : D.targetLattice.CovolumeLe y c) :
    D.targetDim * (D.mainAmount - 3 * (D.f * D.a * D.logB ^ 4)) ≤ c + 2 * δ
```
**Chain inside `LongForms.lean`:**
1. Complete $y$ ($n$ vectors) to a basis of `targetDim` by adding $n' = d_T - n \le (4/b^2) d_T$ auxiliary basis vectors `IsAuxiliaryForm` (`LongForms.lean:56,72`). Their height contribution is absorbed by `mul_completion_cost_le` (`LongForms.lean:133`), which uses $n' \le (4/b^2) d_T$ to cancel the $b^2$ in `2 * x₁^2 * b^2 + b`, fitting inside $d_T \cdot (f a \log^4 b)$.
2. By `exists_hasSmallRatios_heightLe_liftDeterminant_div` (`:151`) and `exists_chainDeterminant_one_div_eq` (`:174`, constructed via Galois-representation/Ribet congruence machinery in `FitTwistsExist.lean` / `LongForms.lean`), one obtains an `MFoldTwist` $\iota$ with `heightLe_chainDeterminant_one_div` (`:192`):
   $$\mathrm{HeightLe}(Z(1)/Z(\xi_\iota),\; d_T \cdot (f a \log^4 b - \mathrm{mainAmount}))$$
   (coming from `LiftVolumeHeight.lean:731`, summing $d_T k (\log b \cdot \mathrm{denominatorBudget} - \mathrm{directionAmount})$ over $1 \le j \le m$).
3. Applying the product formula / covolume-index duality `TwistedLattice.covolume_add_index_nonneg` (`TwistedLattice.lean:492`, via `HeightLe.nonneg_of_one` in `Heights.lean:201` on $(\mathrm{vol}_\theta/\mathrm{vol}_1) \cdot (\mathrm{vol}_1/\mathrm{vol}_\theta) = 1$) to `integral_forms_long_with_completion_cost` (`LongForms.lean:223`) yields:
   $$d_T \cdot (\mathrm{mainAmount} - 3 f a \log^4 b) \le c + 2\delta.$$

---

### Step D: Gluing A + B + C into `(⋆)` (`MainInequality.lean:93-165`)

`New.star_inequality` (`src/New/Reduction/MainInequality.lean:93-95`):
```lean
theorem star_inequality (D : Data P) :
    D.m * D.totalRemainder ≤ D.f * D.a * D.logB ^ 5
```
**Exact line-by-line cancellation (`MainInequality.lean:96-165`):**
1. Invoke `D.enough_forms` (Theorem B) to get $t \subseteq \mathfrak{G}$ with $\#t \cdot \dim \mathrm{ramifiedSourceForms} \le 5 d_T \log(1 + 2b^2)$ and $\dim \bigoplus_{s \in t} \mathrm{range}(\tilde P_s) \ge (1 - 4/b^2) d_T$.
2. By `D.span_short_integralRamified_eq_top` (Theorem A(a)), each $\mathrm{range}(\tilde P_s)$ is spanned by images of short vectors $\varphi \in \mathrm{integralRamified}$ whose $\sigma$-squared norm satisfies $\log \le \mathrm{mainAmount} - m\,\mathrm{totalRemainder} + \mathrm{sizeError}$ (where `sizeError := D.f * D.a * D.logB ^ 4`). Extract a linearly independent subset $y : \mathrm{Fin}\,n \to \mathrm{targetLattice.Carrier}$ (`n ≤ d_T`, `(1 - 4/b^2) d_T ≤ n`).
3. Apply `TwistedLattice.covolumeLe_of_normSqAt_le` (`TwistedLattice.lean`) and Theorem A(b) (`indexLe_normalizedPoincare`):
   - `c := n * (mainAmount - m * totalRemainder + sizeError)` (`h_covolume_upper`)
   - `δ := d_T * indexBudgetPerDim`, where `indexBudgetPerDim := 10 * log (1 + 2 * b^2) * errorUnit` (`h_index_upper`, from $5 \cdot 2 = 10$).
4. Apply Theorem C (`D.integral_forms_long`, `MainInequality.lean:138-141`):
   $$d_T (\mathrm{mainAmount} - 3\,\mathrm{sizeError}) \le n(\mathrm{mainAmount} - m\,\mathrm{totalRemainder} + \mathrm{sizeError}) + 2 d_T \cdot \mathrm{indexBudgetPerDim}.$$
5. **Cancellation of `mainAmount` (`MainInequality.lean:143-147`):**
   Using $n \le d_T$ and **`0 ≤ D.mainAmount`** (`D.mainAmount_nonneg`, `PrimeSums.lean:301`), we have $0 \le \mathrm{mainAmount} + \mathrm{sizeError}$, hence:
   $$n(\mathrm{mainAmount} + \mathrm{sizeError}) \le d_T(\mathrm{mainAmount} + \mathrm{sizeError}) \quad (\texttt{h\_main\_comparison}).$$
   Substituting cancels $d_T \cdot \mathrm{mainAmount}$ identically:
   $$n \cdot (m \cdot \mathrm{totalRemainder}) \le d_T \cdot (4\,\mathrm{sizeError} + 2\,\mathrm{indexBudgetPerDim}) \quad (\texttt{h\_main\_cancelled}).$$
6. Since $4 / b^2 \le 1/2$, we have $d_T / 2 \le n$ (`:151-157`). Dividing by $n$ yields:
   $$D.m \cdot D.\mathrm{totalRemainder} \le 2(4\,\mathrm{sizeError} + 2\,\mathrm{indexBudgetPerDim}) \le D.f \cdot D.a \cdot D.\logB^5.$$

---

### Step E: Extracting the $1/m \asymp x^{-1/2}$ Prime Remainder Bound & GRH (`OneSidedBound.lean`, `New/Main.lean`)

1. **`Data.primeRemainder_le` (`src/New/Reduction/OneSidedBound.lean:45-79`):**
   Unpacks `totalRemainder_eq` (`src/New/Reduction/PrimeSums.lean:183-186`):
   $$\mathrm{totalRemainder} = D.a \cdot \Big(|\mathrm{bPlaces}| \cdot \big(R_{q_0}(x) - R_{q_0}(x_1)\big) + |\mathrm{aPlaces}| \cdot R_1(x_1)\Big)$$
   where $R_q(y) = \mathrm{primeRemainder}\,P.d\,q\,y$. Dividing `star_inequality` (`totalRemainder ≤ f * a * logB ^ 5 / m`) by $a \cdot |\mathrm{bPlaces}|$, using `f = #aPlaces * φ(q₀)` (`f_eq_card_aPlaces_mul`, `PrimeSums.lean:89`) and `|#aPlaces| / |#bPlaces| ≤ logB` (`towerDeg_le_card_bPlaces_mul`, `AdmissibleData.lean:139`), yields (`OneSidedBound.lean:46-79`):
   $$\mathrm{primeRemainder}\,P.d\,P.q_0\,D.x \le \frac{\varphi(q_0) \cdot D.\logB^6}{D.m} + |\mathrm{primeRemainder}\,P.d\,P.q_0\,D.x_1| + D.\logB \cdot |\mathrm{primeRemainder}\,P.d\,1\,D.x_1|.$$
   Notice the exact source of the 6 powers of $\log b$: `logB^5` from `(⋆)` divided by `m * a * #bPlaces` picks up `f / #bPlaces ≤ logB` (`5 + 1 = 6`).

2. **Asymptotic specialization (`eventually_primeRemainder_natCast_le`, `OneSidedBound.lean:137-169`):**
   With $\log b \le 2 x^\varepsilon$, $m \ge x^{1/2}$ (`:87-88`), and unconditional PNT giving $|R(x_1)| \le x^{-2}$ (`:107-129`), we get:
   $$R_{q_0}(x) \le \frac{\varphi(q_0) (2 x^\varepsilon)^6}{x^{1/2}} + x^{-2} + 2 x^\varepsilon x^{-2} \le (64\,\varphi(q_0) + 3) x^{-1/2 + 6\varepsilon}.$$

3. **Real $y$ & GRH (`eventually_primeRemainder_le_mul_rpow` `:213-245`, `New.grh` `:249-280`, `New/Main.lean:33,42`):**
   Re-indexing $\delta = \min(1/200, \varepsilon/6)$ and stepping $y \mapsto \lfloor y \rfloor$ drops the factor $2$ on constants to $(128\,\varphi(q_0) + 32) y^{-1/2 + \varepsilon}$. Then `LFunction_ne_zero_of_primeRemainder_le` (`Criterion.lean:41`) proves GRH for primitive/all Dirichlet $L$-functions (`New.zeros_on_line`) and $\zeta(s)$ (`New.zeta_zeros_on_line`).

---

## 3. Five Sharpest Mathematical Insights & Tight Constraints Found in Code

1. **`18480 = 2^4 \cdot 3 \cdot 5 \cdot 7 \cdot 11$ performs three completely independent arithmetic jobs at once.**
   It is tempting to think $18480 = \frac{11}{3} \cdot 5040$ is merely about $\zeta_{5040}$, but inspecting `FieldsAndPlaces.lean` reveals three decoupled constraints:
   - $2^4 \mid q_0$ combined with `q₀ ∣ 2(d+1) ∧ ¬q₀ ∣ (d+1)` forces $d \equiv 7 \pmod 8$ (`:94-96`), splitting $2$ in $K$ and satisfying `Criterion.lean:41-42`.
   - $4, 7 \mid 5040 \mid 3 q_0$ puts $i$ and $\omega = \frac{1+\sqrt{-7}}{2}$ into $E$ (`Adeles/Basic.lean:465,476`, `PrimeDecomposition.lean:145-150`).
   - $11 \mid 18480$ has *nothing* to do with $5040$: it plugs the gap between $7$ and $13$, forcing all primes $p < 13$ to split in $K$ so every nonsplit prime satisfies $13 \le p$ (`thirteen_le_of_chiK_ne_one`, `:171`).

2. **Cancellation of `mainAmount` in `(⋆)` critically depends on Behrend's lower density bound `0 ≤ mainAmount`.**
   In `MainInequality.lean:143-147`, Theorem A(a) upper-bounds covolume by $n(\mathrm{mainAmount} - m\,\mathrm{totalRemainder} + \mathrm{sizeError})$ where $n \le d_T$ is the rank of the independent short vectors, whereas Theorem C lower-bounds covolume by $d_T(\mathrm{mainAmount} - 3\,\mathrm{sizeError})$. Replacing $n \cdot \mathrm{mainAmount}$ by $d_T \cdot \mathrm{mainAmount}$ moves in the **required** direction only because `0 ≤ D.mainAmount` (`PrimeSums.lean:301`)! Tracing `le_mainAmount` (`PrimeSums.lean:295`) shows `0 ≤ directionAmount` comes from `jetSize(weight σ) - primeSum(weight σ, σ)` weighted heavily on the dense-enough Behrend set `bPlaces` (`|bPlaces| ≥ towerDeg / logB`), without which $n < d_T$ would leak a negative $(d_T - n) \cdot |\mathrm{mainAmount}| \approx \frac{1}{b^2} \cdot m k f a \log M$ error — dwarfing the GRH saving by factors of $a$ and $k$!

3. **`2^s = m^22` (`towerExp = 22(e+1)`) is tightly pinched between Behrend short-arc length in $C$-crystalline congruences and $k \le f$.**
   In `CrystallineDefect.lean:202-213`, to keep any three $b$-places from sitting in a Frobenius orbit within step $\log_\ell(\mathrm{halfGap}^3)$, the proof requires $\mathrm{halfGap}^3 \le (2^s)^{12}$ so that $a + b \le 24 s \le 27 s < l_0$. Since $\mathrm{halfGap} = r^8$ and $r \le 3 x^5$, $\mathrm{halfGap}^3 \le 3^{24} x^{120}$, whereas $(2^s)^{12} = (m^{22})^{12} \ge x^{132}$. Lowering `22` to `20` leaves $x^{120}$ vs $3^{24} x^{120}$ violated! Simultaneously, `r ≍ x⁵` is pinned between `k ≥ 1000 (2ϱ+2)⁹ ~ x^{4.5}` (`Setup.lean:132`) below and `f ~ x¹¹` (`FillingAdmissible`, `CrystallineDefect`) above.

4. **`1 + 9 b⁻⁴` and `4 / b²` are exact closed-form consequences of two bootstrap / split-loss inequalities.**
   - In `MomentBounds.lean:441-446`, open elements bound the main part of the second moment by $(1 + 4 b^{-4}) C$ (expanding $(1 + b^{-4})^2$) and non-open elements add at most $b^{-4} M$. Solving $M \le (1 + 4x) C + x M$ for $x = b^{-4} \le 1/10$ gives $(1-x)(1+9x) - (1+4x) = x(4-9x) \ge 0$, producing `1 + 9 b⁻⁴`.
   - In `ShortAndEnough.lean:361-392`, the rank loss `4 / b²` in Theorem B splits $2/b^2 + 2/b^2$: taking $\varepsilon_0 = (8 b^2)^{-1}$ in `FewTranslates.lean:498` yields `(1 - 16 ε₀) d_T = (1 - 2/b²) d_T`, and restricting from `SourceForm` to the codimension-$f/(N-1)$ subspace `ramifiedSourceForms` loses another `≤ (2/b²) d_T`. Meanwhile `LongForms.lean:133` uses `n' ≤ (4/b²) d_T` to cancel `b²` in the completion cost `2 x₁² b² + b`.

5. **Two-sided knife-edge constraint on `-15/2 * logB` in `logLevelMin` — and the `10^5` vs `10^8` discrepancy on `ϱ`.**
   - `logLevelMin` (`AdmissibleData.lean:74-76`) sits in a tight two-sided vise: moving `-15/2` up (increasing $N$) shrinks $\mathcal{D}_{\mathrm{main}} / \mathcal{D}_{\mathrm{id}} \approx (M b^{-15/2})^{kf}$ toward the `b^(11 k f)` floor (`FillingAdmissible.lean:571,636`, where $M \ge b^{19}$ only leaves margin $19 - 15/2 - 1/4 = 11.25 > 11$); moving `-15/2` down (decreasing $N$) shrinks the Archimedean cancellation $-\log N$ in `ArchimedeanSize.lean:120` until short vectors exceed the covolume bound.
   - Separately, the adelic unfolding setup (`Setup.lean:126`) only requires `10^5 ≤ ϱ`, whereas `RealPlaceSizes` (`RealPlaceGauge.lean:321`) enforces `10^8 ≤ ϱ` so that the dyadic shell cutoff `s = k - 3n - 6 ≥ n^7 - 3n - 6` cleanly dominates `10^10 * n^4` and `10^8 * n^4 + K + 6` (`RealShells.lean:478,598-604`).
