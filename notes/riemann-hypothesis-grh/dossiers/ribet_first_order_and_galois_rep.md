# Step-Back Mathematical Reverse-Engineering: First-Order Ribet, Finite-Level Taylor–Wiles, and the "No-Weil–Deligne" Galois Representation Stack (`grh / main`)

> **Target:** [`leanprover-community/riemann-hypothesis`](https://github.com/leanprover-community/riemann-hypothesis/tree/c3574bd1d732aad94e096732f983fc515288ed54) (`main`, Apache-2.0) @ `c3574bd1d732aad94e096732f983fc515288ed54` (Lean `v4.37.0-rc1`, Mathlib `31ce06ea`, Tau Ceti `fce5bf3e`).
> **Scope audited (read-only):** **46 files (~29,986 LOC)** across two tightly coupled subsystems — [`src/New/Congruences/FirstOrder/`](https://github.com/leanprover-community/riemann-hypothesis/tree/c3574bd1d732aad94e096732f983fc515288ed54/src/New/Congruences/FirstOrder) (15 files, 10,715 LOC) and [`src/Lib/GaloisRep/`](https://github.com/leanprover-community/riemann-hypothesis/tree/c3574bd1d732aad94e096732f983fc515288ed54/src/Lib/GaloisRep) (31 files, 19,271 LOC) — plus their exact downstream consumers, supporting library modules (`FittingIdealsAndLengths`, `BlockFittingBound`, `Eigenvalues`, `Etale/Basic`), `TauCeti` overlap modules (all 11 files / 2,833 LOC of `WeilDeligne`, `BrauerNesbitt`, `IntegralModel`, `HeckeRing/GLn`, `FittingIdeal`, `GeneralizedMatrixAlgebra`, `RibetLattice`), and a live conflict audit against ~500 open upstream PRs.
> **Method:** Work backwards from the highest-Slopscore and longest-proof hotspots (`#1` `LabelCompatibility` [46], `#2` `RibetMatrices` [35], `#3` `QuadraticStep` [33, `bf=25`], `RibetLemma` [32], `AuxiliaryPrimeTie` [30], `#1` longest proof `PrimeDegreeTransfer` [170L], `#4` longest `SeedRepresentation` [140L]) to recover the high-level mathematical problem space, compare it against textbook arithmetic geometry, pinpoint *why* standard methods fail or were bypassed, and separate genuine mathematical shortcuts from true eliminable Lean engineering debt.

---

## Executive Summary

At first glance, these ~30,000 lines look alien to a working number theorist: there are **no Weil–Deligne representations**, **no Local Langlands correspondence for $\mathrm{GL}_n$**, **no endoscopic transfer for even-rank unitary groups**, **no infinite Taylor–Wiles patching ($R_\infty = \mathbb{T}_\infty$)**, **no Poitou–Tate 9-term duality or $H^2$**, and **no Bellaïche–Chenevier GMAs or Hensel orthogonal idempotents**. Instead, one finds multivariate `MvPolynomial J O`-matrices modulo $\langle X_j^2 \rangle$, a "tied normalizer" $\rho_0 = e + (1-e)(a-1)$, a mirabolic finite-group transfer theorem, a quadratic shift $x(x+k)$, a dense filter `mostFrobenii`, and an annihilating-polynomial predicate `PolyKillsAt`.

**Core finding:** **Almost none of that mathematical weirdness is accidental AI brute force.** Every major non-standard construction solves a concrete obstruction where the textbook theorem either **fails mathematically** (small primes $\ell \le t$ destroying Hensel idempotents; Vandiver's conjecture blocking even Tate-twist class groups; $t$-fold colliding cyclotomic eigenvalues breaking classical CHT Taylor–Wiles projections) or carries a **50k–100k LOC formalization tax** that the proof's actual narrow interface never needs.

At the same time, our line-by-line forensics prove that **the top Slopscore outliers in the entire 300k-line repository ARE driven by genuine, eliminable Lean engineering debt** — dead local instances, one of only three `attribute [-instance]` strong technical debt hacks in the whole repo, kernel-level `decide +kernel` enumerations, 16-case `split_ifs` truth tables, 13-field single-use intermediate records, 52-binder copy-pasted signatures, quantifier-smuggling anti-patterns, unbundled 7-tuple existential contracts, and genuine `TauCeti` duplications (`BrauerNesbitt`, `IntegralModel`, `glnHeckePolynomial`, `FittingIdeal`).

- **Genuine mathematical innovations to PRESERVE (10):** Prime triangles + parity-decoupling Frobenius shift (Vandiver evasion), 3-stage $O[X_j]$-Fitting filtration modulo telescoping colon ideals, single finite-level first-order norm deformation $\mathcal{N} = \prod_j (\mathrm{Nm}_j + \alpha_j \partial_j)$, mirabolic transfer $\mathrm{Ver}(g_{00}) = \det$, quadratic finite-difference $x(x+k)$ (handling $\ell = 2$), non-commutative Cramer's rule via Amitsur + right-action of $\rho_0$, 3-way generator split $W \oplus s_0 \oplus s$, `mostFrobenii` + `PolyKillsAt`, twin convergent definite theta lifts $U(n) \to U(2n+1)$ + Bézout, and prime-degree cyclic base change + finite-group Shintani lift.
- **Verified negative ecosystem findings (Do NOT force):** `TauCeti.RepresentationTheory.WeilDeligne` (11 files, 2,833 LOC) is pure abstract parameter algebra with zero $\ell$-adic monodromy theorem, zero $D_{\mathrm{pst}}$ functor, and zero LLC bridge; `TauCeti.GMAData` and `TauCeti.RibetLattice` mathematically fail when $\ell \le t$ (no orthogonal idempotents) and in higher rank.
- **Concrete high-impact upstream refactoring roadmap (Candidates A–G):** **~1,200–1,600+ net LOC deletable** across 7 surgical, conflict-checked PR candidates — every one substantially exceeding our calibrated baseline quality bar ([PR #6070](https://github.com/leanprover-community/riemann-hypothesis/pull/6070), `-48` net LOC genuine ecosystem deletion).

---

## Part I: First-Order Ribet & Finite-Level Taylor–Wiles (`src/New/Congruences/FirstOrder/`)

### I.1 Problem Space, Exact Boundary, and 15-File Dataflow

To control Arakelov lattice volumes and heights in [`LiftVolumeHeight.lean#L739`](https://github.com/leanprover-community/riemann-hypothesis/blob/c3574bd1d732aad94e096732f983fc515288ed54/src/New/OneLift/LiftVolumeHeight.lean#L739), the global argument ([`FitTwistsExist.lean#L521`](https://github.com/leanprover-community/riemann-hypothesis/blob/c3574bd1d732aad94e096732f983fc515288ed54/src/New/Congruences/FitTwistsExist.lean#L521), `New.exists_isRegularFamily`) must bound the **$\ell$-adic denominator of the orthogonal projection** $\mathrm{pr}_Z : \mathrm{Form}_V \to Z$ onto the subspace $Z$ of definite unitary theta lifts $W_j \to V_j$ (ranks $r < n = r + t$, with $t \le 5r$, and $r = 1, n = 2z$ for main critical pairs), **uniformly across all primes $\ell$** (including $\ell = 2$ and small primes) so that $\sum_\ell \beta_\ell \log \ell \le D.\mathrm{denominatorBudget}$.

The **entire 15-file, 10,715-LOC directory** funnels into **one single downstream consumer**, [`src/New/Congruences/FitTwistsExist.lean#L3`](https://github.com/leanprover-community/riemann-hypothesis/blob/c3574bd1d732aad94e096732f983fc515288ed54/src/New/Congruences/FitTwistsExist.lean#L3), via **one primary theorem**: [`New.Selmer.denominatorLe_clearingBound`](https://github.com/leanprover-community/riemann-hypothesis/blob/c3574bd1d732aad94e096732f983fc515288ed54/src/New/Congruences/FirstOrder/DenominatorBound.lean#L1325-L1335) (called at [`L419`](https://github.com/leanprover-community/riemann-hypothesis/blob/c3574bd1d732aad94e096732f983fc515288ed54/src/New/Congruences/FitTwistsExist.lean#L419) for `range (D.goodLift ϑ j)` and [`L448`](https://github.com/leanprover-community/riemann-hypothesis/blob/c3574bd1d732aad94e096732f983fc515288ed54/src/New/Congruences/FitTwistsExist.lean#L448) for `ℂ ∙ trivialLift`). It produces a Hecke-eigenform-preserving diagonal operator $\Lambda \in \mathrm{End}_{\mathbb{C}}(Z)$ clearing denominators of $\mathrm{pr}_Z(y)$ for all $\ell$-integral forms $y$ orthogonal to false lifts, with
$$\|\iota_\ell(\det \Lambda)\| \;\ge\; \exp\bigl(-\dim_{\mathbb{C}}(Z)\cdot r \cdot \mathrm{clearingBound}(D, \ell)\cdot \log \ell\bigr).$$

**Critical architectural separation inside `src/New/Congruences/`:** There are **two completely distinct** auxiliary-prime engines:
1. **`New/Congruences/Selmer/` (`TwistingTheorem.lean`, `Descent.lean`, `Untied.lean`):** Chooses the anticyclotomic twist $\vartheta$ (modulus $Q$) using scalar-slope tied Selmer groups $z(\gamma_v) = s \cdot z(\varphi_v)$ ($s \in \mathcal{O}$) so the **main summand's** crystalline Selmer group $\mathrm{Sel}_Q(\psi R)$ has short divisible length $\le \mathrm{twistError}(\ell, D)$.
2. **`New/Congruences/FirstOrder/` (the 15 files audited here):** With $\vartheta$ already fixed, executes Ribet's method on the normalized theta-lift Galois representation
   $$u_x \;\simeq\; \psi R_x \;\oplus\; \bigoplus_{e=0}^{t-1} \chi_{\mathrm{cyc}}^{-e}$$
   to clear denominators **without ever bounding the even Tate-twist cohomology classes $H^1_{\mathrm{unr}}(E, (\mathcal{O}/\ell^\nu)(-e))^+$**.

```text
GALOIS / KUMMER / TRIANGLE SIDE (2,152L)          ALGEBRAIC RIBET MATRIX WALL (4,321L)
────────────────────────────────────────          ────────────────────────────────────
EvenClasses.lean (268L)                           Lib/General/Algebra/{FittingIdealsAndLengths,BlockFittingBound}
  evenClasses, withConjInv, IsPrimeTriangle          │
        │                                            ▼
        ▼                                         FittingBlock.lean (709L)
KummerMaps.lean (870L)                              3-stage O[X_j]-Fitting bound (L141), colon ideal
  E → E⁺ Galois transport; odd Kummer maps ψ;       (⟨X_j²⟩ : ∏_{ty<e} X_j) (L449), unit-row elimination
  concrete N-unit reciprocity (no H²/Poitou-Tate)    │
        │                                            ├──► TraceRelations.lean (987L)
        ▼                                            │      clearingBound, conj self-dual doubling (L254),
TrianglePrimes.lean (711L)                           │      dualDefect crystalline bound (L678, L775)
  Lex-ordered J = {0<e<t} ×ₗ testPoints;             │
  parity-decoupling shift σ = δ^{ℓ^ν}(gg^c·u/u^c)    ├──► RibetMatrices.lean (945L)
  ⇒ ONE fixed finite J for ALL ν > 0                 │      tieIdeal, tiedRows, tiedNormaliser ρ₀ = e+(1-e)(a-1),
        │                                            │      main block B₀, 13-field CharacterRows
        ▼                                            │              │
TateTwistCocycles.lean (303L)                        │    RibetMethod.lean (567L) [Amitsur + block Cayley-Hamilton]
  even part killed ⇒ mod-ℓ^h embeds into shaOdd      │              │
  ⇒ HasTriangleCost (plugs into FittingBlock)        └──────► RibetLemma.lean (689L)
        │                                                       glues B₀ + char blocks via exact projector k
        └──────────────────────────────┬────────────────────────┘
                                       ▼
                              RibetElement.lean (424L)
                                `ribet_columns` (L293): produces polynomial Ribet element
                                𝒟 ∈ 𝕋[X_j] vanishing below ∏ X_j on lifts, bounded top coeff 𝒟_J(π)
                                       │
AUTOMORPHIC FIRST-ORDER DEFORMATION    │
(2,905L)                               │
────────────────────────────────────   │
HeckeStrings.lean (500L)               │
  Satake root chain X₀,…,X₀q^(t-1)     │
  via SphericalChainLemma (no Tadić)   │
        │                              │
OnePrime.lean (867L)                   │
  Mirabolic Ver(g₀₀) = det (L510);     │
  quadratic shift x(x+k) (L817);       │
  inductive Higman pullback (L315)     │
        │                              │
TiedTraces.lean (820L)                 │
  Tame/Frob dictionary at w ∈ Q        │
  (mod 2·n! via IwahoriCompatibility)  │
        │                              │
AuxiliaryPrimeTie.lean (718L)          │
  𝒩 = ∏_j (Nm_j + α_j ∂_j) kills       │
  tiedIdeal; picks ν AFTER #J fixed    │
        └──────────────┬───────────────┘
                       ▼
           DenominatorBound.lean (1,337L)
             `denominatorLe_clearingBound` (L1325) ──► FitTwistsExist.lean
```

### I.2 What Traditional Mathematics Would Do Instead

| Classical Paradigm | Standard Mechanism |
|---|---|
| **Ribet (1976)** (*Invent. Math.* 34; cf. `TauCeti/.../RibetLattice.lean`) & **Wiles (1990)** | For irreducible $\rho : G \to \mathrm{GL}_2(K)$ with residual trace $\bar{\chi}_1 + \bar{\chi}_2$ (**$\bar{\chi}_1 \neq \bar{\chi}_2$**), lift eigenvalues via Hensel's lemma, rescale maximal off-diagonal entry, produce a non-split extension in $H^1(G, \bar{\chi}_1 \bar{\chi}_2^{-1})$. Quantitatively (Wiles 1990), work over completed local Gorenstein $\mathbb{T}_\mathfrak{m}$ and invoke the **Iwasawa Main Conjecture** to bound class groups by $p$-adic $L$-values. |
| **Urban (2001) / Skinner–Urban (2014)** & **Bellaïche–Chenevier (2009)** (*Astérisque* 324; cf. `TauCeti/.../GeneralizedMatrixAlgebra/`) | For higher-rank congruences with **pairwise non-isomorphic residual summands**, lift orthogonal idempotents $e_0, \dots, e_t$ to Henselian $\mathbb{T}_\mathfrak{m}[G]$, form the GMA Peirce decomposition $e_i R e_j$, and map off-diagonal entry modules $A_{ij}$ into $\mathrm{Ext}^1(\rho_j, \rho_i)$ to bound the total reducibility ideal $I^{\mathrm{tot}}$ by $\mathrm{Fitt}(\mathrm{Sel}^\vee)$. |
| **Taylor–Wiles (1995) / Diamond (1997) / Kisin (2009)** & **Clozel–Harris–Taylor (2008)** (*IHES*, §3.4) | On definite unitary groups $U(n)$ (CHT08), assume **$\bar{\rho}$ adequate (irreducible)**, choose an **infinite sequence** of auxiliary prime sets $Q_N$ ($q \equiv 1 \pmod{\ell^N}$) where $\bar{\rho}(\mathrm{Frob}_w)$ has a **distinct simple eigenvalue**, project via a $U_w$-idempotent (invoking **Tadić 1986 / Casselman 1980**), patch $M_{Q_N}$ as $N \to \infty$ over $R_\infty = \mathcal{O}[[x_1,\dots,x_g]]$ via ultrafilters, and apply Auslander–Buchsbaum to get $R = \mathbb{T}$. |
| **Dasgupta–Kakde–Silliman–Wang (2023)**, **Lecouturier (2019/2021)**, **Dotto–Thorne (2026)** | DKSW handles residually indistinguishable characters for $\mathrm{GL}_2$ via normalized $2\times 2$ presentations and separation denominators; Lecouturier/Merel/Wake–Wang-Erickson use cup/Massey products and Kummer–Vandiver pairings on Eisenstein ideals; Dotto–Thorne / Calegari–Geraghty use derived patching + **Poitou–Tate 9-term duality** + **Greenberg–Wiles**. |

### I.3 Why Traditional Methods Break — Seven Genuine Mathematical Innovations

Every counter-intuitive layer in `FirstOrder/` is forced by a concrete mathematical wall:

1. **Vandiver's Conjecture Blocks Direct Ribet & Wiles (1990) → Prime Triangles + Parity-Decoupled Shift (`EvenClasses`, `KummerMaps`, `TrianglePrimes`, `TateTwistCocycles`, `FittingBlock`):**
   - For the $t - 1$ nontrivial Tate twists $\mathcal{O}(-e)$ ($0 < e < t$), the **odd** cocycles `shaOdd` are bounded unconditionally and explicitly (`X ≤ 2^(4T²⁷) h_E`) by Jacobi-sum Stickelberger + Kolyvagin derivatives ([`Lib/Cyclotomic/OddSha.lean#L22-L25`](https://github.com/leanprover-community/riemann-hypothesis/blob/c3574bd1d732aad94e096732f983fc515288ed54/src/Lib/Cyclotomic/OddSha.lean#L22-L25)).
   - The **even** cocycles `evenClasses` ([`EvenClasses.lean#L60`](https://github.com/leanprover-community/riemann-hypothesis/blob/c3574bd1d732aad94e096732f983fc515288ed54/src/New/Congruences/FirstOrder/EvenClasses.lean#L60)) live in the plus-part class group $\mathrm{Cl}(E(\mu_{\ell^\infty}))^+$ — **Vandiver's conjecture territory**, with no unconditional upper bound (and even Iwasawa theory only yields $p$-adic regulators, not a universal prime-summed integer bound).
   - **The escape:** Rather than bounding `#evenClasses`, impose **formal linear ties** $z(\tau_j) = X_j z(\varphi_j)$ over $\mathcal{O}[X_j]$ along a fixed finite lexicographically ordered set $J = \{0 < e < t\} \times_{\mathrm{lex}} \mathrm{testPoints}$ ([`TrianglePrimes.lean#L680`](https://github.com/leanprover-community/riemann-hypothesis/blob/c3574bd1d732aad94e096732f983fc515288ed54/src/New/Congruences/FirstOrder/TrianglePrimes.lean#L680), `#J` **independent of $\nu$**!). Passing to $F = E^+$ (`KummerMaps.lean`), Chebotarev constructs the prime $x_j$ inductively at the **parity-decoupling Frobenius shift** ([`TrianglePrimes.lean#L443`](https://github.com/leanprover-community/riemann-hypothesis/blob/c3574bd1d732aad94e096732f983fc515288ed54/src/New/Congruences/FirstOrder/TrianglePrimes.lean#L443)):
     $$\sigma \;=\; \delta^{\ell^\nu} \cdot \bigl(g \cdot g^c \cdot (u / u^c)\bigr).$$
     Because every Kummer map $\psi$ is **odd** ($\psi(a^c) = -\psi(a)$), $\psi(s) = 2\psi(u)$ near $\sigma$ ([`L279`](https://github.com/leanprover-community/riemann-hypothesis/blob/c3574bd1d732aad94e096732f983fc515288ed54/src/New/Congruences/FirstOrder/TrianglePrimes.lean#L279)); because every $z \in \mathrm{evenClasses}$ is **even** ($z(a^c) = z(a)$), $z(s) = 2z(g)$ ([`L296`](https://github.com/leanprover-community/riemann-hypothesis/blob/c3574bd1d732aad94e096732f983fc515288ed54/src/New/Congruences/FirstOrder/TrianglePrimes.lean#L296)); and $\delta^{\ell^\nu}$ ($\delta \in \ker \chi_{\mathrm{cyc}}$) moves $\sigma$ into the allowed Frobenius set $W$ invisibly to all $\ell^\nu$-torsion cocycles!
   - Thus $\psi_j(\varphi_i) = 0$ for all $i > j$ while $\psi_j(\varphi_j) \neq 0$, collapsing global reciprocity on $\{i \ge j\}$ to a single term at $j$ ([`L556`](https://github.com/leanprover-community/riemann-hypothesis/blob/c3574bd1d732aad94e096732f983fc515288ed54/src/New/Congruences/FirstOrder/TrianglePrimes.lean#L556)). In the 3-stage $\mathcal{O}[X_j]$-Fitting filtration [`exists_mul_prod_X_mem_fittingIdeal`](https://github.com/leanprover-community/riemann-hypothesis/blob/c3574bd1d732aad94e096732f983fc515288ed54/src/New/Congruences/FirstOrder/FittingBlock.lean#L141-L214) modulo the telescoping colon ideal $\mathfrak{q}_e = (\langle X_j^2 \rangle : \prod_{\mathrm{ty}(j) < e} X_j)$ ([`L449–L509`](https://github.com/leanprover-community/riemann-hypothesis/blob/c3574bd1d732aad94e096732f983fc515288ed54/src/New/Congruences/FirstOrder/FittingBlock.lean#L449-L509)), each even-class test vector $v_j$ satisfies $(C X_j) v_j \in T$, putting $F \cdot \prod_{j \in J} X_j$ in the Fitting ideal with $v_\ell(F(0))$ bounded solely by `crystallineColength + length(shaOdd) + #s · v(C)` — **`#evenClasses` vanishes completely from the inequality!**

2. **Reducible $\bar{\rho}$ + $t$-Fold Cyclotomic Collision Breaks Classical CHT/Taylor–Wiles Patching → Single Finite-Level First-Order Norm Deformation (`HeckeStrings`, `OnePrime`, `TiedTraces`, `AuxiliaryPrimeTie`):**
   - Classical CHT08 requires $\bar{\rho}$ irreducible/adequate AND a simple eigenvalue of $\bar{\rho}(\mathrm{Frob}_w)$ so a $U_w$-idempotent splits off a rank-1 line. Here $\bar{\rho}$ is reducible and at any split $w$ with $q_w \equiv 1 \pmod{\ell^\nu}$, **all $t$ characters $\chi_{\mathrm{cyc}}^{-e}(\mathrm{Frob}_w) \equiv 1 \pmod{\ell^\nu}$ collide!**
   - Consequently, any weak lift ($\det(1 - u_x(g)) = 0$) carries a full **$t$-term Satake chain** $X_0, X_0 q, \dots, X_0 q^{t-1}$ in its Hecke polynomial ([`HeckeStrings.lean#L290`](https://github.com/leanprover-community/riemann-hypothesis/blob/c3574bd1d732aad94e096732f983fc515288ed54/src/New/Congruences/FirstOrder/HeckeStrings.lean#L290), proved via an elementary finite-geometry hyperplane count in [`SphericalChainLemma.lean#L541`](https://github.com/leanprover-community/riemann-hypothesis/blob/c3574bd1d732aad94e096732f983fc515288ed54/src/Lib/LocalGL/SphericalChainLemma.lean#L541) — bypassing Tadić's 1986 unitary dual classification!).
   - Because the Ribet element $\mathcal{D} \in \mathbb{T}[\alpha_j]$ only needs the **squarefree** monomial $\prod_{j \in J} \alpha_j$ and $\#J$ is **fixed independently of $\nu$**, **no $N \to \infty$ patching, ultrafilters, universal deformation rings, or Auslander–Buchsbaum are needed!** One picks a single large $\nu$ *after* $\#J$ is fixed so $2 \cdot n! \cdot (n_0 c^2)^{\#J + 1} \mid \ell^\nu$ ([`AuxiliaryPrimeTie.lean#L480`](https://github.com/leanprover-community/riemann-hypothesis/blob/c3574bd1d732aad94e096732f983fc515288ed54/src/New/Congruences/FirstOrder/AuxiliaryPrimeTie.lean#L480)) and deforms the base-level group norm to **first order** ([`AuxiliaryPrimeTie.lean#L252`](https://github.com/leanprover-community/riemann-hypothesis/blob/c3574bd1d732aad94e096732f983fc515288ed54/src/New/Congruences/FirstOrder/AuxiliaryPrimeTie.lean#L252)):
     $$\mathcal{N} \;=\; \prod_{j \in J} \bigl(\mathrm{Nm}_j + \alpha_j \partial_j\bigr), \qquad \partial_j \;=\; -\mathrm{Tr}_j \cdot \bigl(p_j(\widetilde{U}_j)\, L_{\mathrm{indLine}}\bigr) \cdot \mathrm{Tr}_j'.$$

3. **Three Algebraic Gems Powering $\partial_j$ (`OnePrime`, `TiedTraces`, `AuxiliaryPrimeTie`):**
   - **Mirabolic transfer = determinant ([`OnePrime.lean#L510`](https://github.com/leanprover-community/riemann-hypothesis/blob/c3574bd1d732aad94e096732f983fc515288ed54/src/New/Congruences/FirstOrder/OnePrime.lean#L510), `transfer_firstEntry`):** On $\mathrm{GL}_N(\mathbb{F}_q)$, the group-theoretic transfer of the $(1, N-1)$ parabolic character $g \mapsto g_{00}$ equals $\det(g)$ (proved cleanly via orbit cycle lengths of $\mathrm{diag}(x, 1, \dots, 1)$ + transvection induction). This converts the line-parahoric logarithm $L_{\mathrm{indLine}}$ into the determinant logarithm $L_{\mathrm{indDet}}$, yielding the 5-line differentiation identity ([`AuxiliaryPrimeTie.lean#L181-L197`](https://github.com/leanprover-community/riemann-hypothesis/blob/c3574bd1d732aad94e096732f983fc515288ed54/src/New/Congruences/FirstOrder/AuxiliaryPrimeTie.lean#L181-L197)):
     $$\partial_j \cdot \mathrm{tr}[(\gamma_j - 1) g] \;\equiv\; \mathrm{Nm}_j \cdot \mathrm{tr}[(\varphi_j - 1) H_j(\varphi_j) g] \pmod{\ell^\nu / (2\cdot n!)}.$$
   - **Quadratic finite-difference trick ([`OnePrime.lean#L817`](https://github.com/leanprover-community/riemann-hypothesis/blob/c3574bd1d732aad94e096732f983fc515288ed54/src/New/Congruences/FirstOrder/OnePrime.lean#L817), `map_valMinAbs_eq_zero_of_shift`):** Applying a shift-invariant linear functional $C$ on $\mathbb{Z}/m\mathbb{Z}$ to $f(x) = x(x+k)$ gives $f(x-k) - f(x) = -2kx$, killing $2k \cdot C(\mathrm{valMinAbs}) \bmod m$ **without inverting $2$**, so **$\ell = 2$ works uniformly**.
   - **Inductive Higman norm pullback ([`OnePrime.lean#L315`](https://github.com/leanprover-community/riemann-hypothesis/blob/c3574bd1d732aad94e096732f983fc515288ed54/src/New/Congruences/FirstOrder/OnePrime.lean#L315)):** Pulls every subset coefficient $\mathcal{N}_S$ back through $\mathrm{Nm}$ (`(c²δ')^#J 𝒩_S ≡ Y_S Nm`), so on a lift $y$ only the top term $\mathcal{D}_J$ survives, clearing the denominator in one finite-level stroke.

4. **Character Collisions at Small $\ell \le D.\mathrm{halfGap}^2$ Break Ribet (1976) & Bellaïche–Chenevier GMAs → Non-Commutative Cramer's Rule (`RibetMethod`, `RibetMatrices`, `RibetLemma`):**
   - Because $(\ell - 1) \mid (e - e')$ occurs for all small $\ell$ and growing $t = 5r \to \infty$, **orthogonal Hensel idempotents DO NOT EXIST** in $\mathcal{O}[G]$ or $\mathbb{T}_\mathfrak{m}[G]$ — breaking both classical Ribet (1976) and `TauCeti.GMAData`. Nor can one globally conjugate a non-local family $u : Y \to G \to M_\sigma(\mathcal{O})$ into upper-triangular form.
   - **The escape:** Separate the main block $\rho_x$ from all $t$ characters using an exact integral projector $k$ from scalar inertia $\gamma_x$ ([`RibetLemma.lean#L300`](https://github.com/leanprover-community/riemann-hypothesis/blob/c3574bd1d732aad94e096732f983fc515288ed54/src/New/Congruences/FirstOrder/RibetLemma.lean#L300)). Introduce the surgical **tied normalizer** $\rho_0 = e + (1-e)(a-1)$ with $e = c_1(\gamma - 1)$ ([`RibetMatrices.lean#L239`](https://github.com/leanprover-community/riemann-hypothesis/blob/c3574bd1d732aad94e096732f983fc515288ed54/src/New/Congruences/FirstOrder/RibetMatrices.lean#L239)), which simultaneously acts as **$1$ on $\rho_\pi$**, **$0$ on $\xi_0 = 1$**, and **$\xi_e(a) - 1$ on $\xi_{e>0}$**.
   - In [`RibetMethod.lean#L55-L277, L484-L566`](https://github.com/leanprover-community/riemann-hypothesis/blob/c3574bd1d732aad94e096732f983fc515288ed54/src/New/Congruences/FirstOrder/RibetMethod.lean#L55-L277), let $\Lambda[X]$ act on $Q = \Lambda / \mathrm{traceIdeal}$ with $\Lambda$ on the **left** and $X$ by **right** multiplication with $\rho_0$; tied rows satisfy $(B - X B_1) y = 0$. Amitsur + block Cayley–Hamilton yields $P(X) \in S[X]$ with $I \cdot P(\rho_0) \subseteq \mathfrak{a}$ and $P(0) = \det(\rho(B))$. Taking $f := \mathrm{tr}(\rho(\rho_1 P(\rho_0)))$ (with $\rho_1$ supported on $\xi_0$ on lifts, so $\rho_1 \rho_0 = 0$) kills all higher terms of $P(\rho_0)$ on lifts while multiplying every $\det(\rho(w))$ into $\mathcal{J}$ — **without ever conjugating non-lift $u_x$!**
   - Meanwhile, the **3-way generator split $W \oplus s_0 \oplus s$** ([`RibetMatrices.lean#L252`](https://github.com/leanprover-community/riemann-hypothesis/blob/c3574bd1d732aad94e096732f983fc515288ed54/src/New/Congruences/FirstOrder/RibetMatrices.lean#L252)) eliminates uncontrolled Noetherian compactness generators $s_0$ via **unscaled** common unit rows (cost $1^{\#s_0} = 1$, [`FittingBlock.lean#L330, L652`](https://github.com/leanprover-community/riemann-hypothesis/blob/c3574bd1d732aad94e096732f983fc515288ed54/src/New/Congruences/FirstOrder/FittingBlock.lean#L330)) *before* applying Lagrange pseudo-idempotents $q_e$ (cost $C^{\#s}$, zero when $\ell > \mathrm{halfGap}^2$).

5. **Bypassing Poitou–Tate Duality & Greenberg–Wiles $H^2$:** [`KummerMaps.lean`](https://github.com/leanprover-community/riemann-hypothesis/blob/c3574bd1d732aad94e096732f983fc515288ed54/src/New/Congruences/FirstOrder/KummerMaps.lean#L376) feeds `tateTwistPlus` over $E^+$ directly into concrete $N$-unit / $m$-th power reciprocity on $Z^1$ ([`RelationsModL.lean#L448`](https://github.com/leanprover-community/riemann-hypothesis/blob/c3574bd1d732aad94e096732f983fc515288ed54/src/Lib/ClassField/GreenbergWiles/RelationsModL.lean#L448)), avoiding 9-term global duality and $H^2$ completely.
6. **$\nu$-Independent Wild/Small-$\ell$ Crystalline Defect Bounds:** Where Fontaine–Laffaille fails ($\ell \le b$ or $\ell \mid p_0 p_1$), non-crystalline torsion leakage is bounded uniformly in $M$ by local Tate duality `dualDefect` ([`TraceRelations.lean#L678, L775`](https://github.com/leanprover-community/riemann-hypothesis/blob/c3574bd1d732aad94e096732f983fc515288ed54/src/New/Congruences/FirstOrder/TraceRelations.lean#L678)) and main-block cocycles pass to `DivisibleQuot O` ($K/\mathcal{O}$, [`RibetLemma.lean#L474`](https://github.com/leanprover-community/riemann-hypothesis/blob/c3574bd1d732aad94e096732f983fc515288ed54/src/New/Congruences/FirstOrder/RibetLemma.lean#L474)).
7. **Conjugate Self-Duality Doubling:** [`isTraceIdeal_withConjInv`](https://github.com/leanprover-community/riemann-hypothesis/blob/c3574bd1d732aad94e096732f983fc515288ed54/src/New/Congruences/FirstOrder/TraceRelations.lean#L254-L326) doubles the tie index from $J$ to $J \times \mathrm{Bool}$ (sharing the same variable $X_j$) so automorphic ties on $(\tau_j, \varphi_j)$ control $(z + z \circ \mathrm{conjGal})(\tau_j)$.

### I.4 Slopscore Forensics & True Eliminable Plumbing in `FirstOrder/`

| File | LOC | Slopscore | Real Engineering Friction (Distinguished from Metric Noise) |
|---|---:|---:|---|
| [`RibetMatrices.lean`](https://github.com/leanprover-community/riemann-hypothesis/blob/c3574bd1d732aad94e096732f983fc515288ed54/src/New/Congruences/FirstOrder/RibetMatrices.lean) | 945 | **35** *(31 @ HEAD)* | Single-use **13-field, 16-param `structure CharacterRows`** (`L739–L782`); 10-arg `tiedRows` signature copy-pasted across ~20 lemmas; unnecessary `attribute [local instance] algebraMvPolynomial` (`L49`, only 3 uses = `MvPolynomial.map`); 9 trivial 1-line `tieIdeal` wrappers (`L110–L228`). |
| [`RibetLemma.lean`](https://github.com/leanprover-community/riemann-hypothesis/blob/c3574bd1d732aad94e096732f983fc515288ed54/src/New/Congruences/FirstOrder/RibetLemma.lean) | 689 | **32** | 45-line signature (`L555–L599`); file-wide `algebraMvPolynomial` (`L59`, needed at 2 sites); 122L block (`L403–L525`) unused in `RibetLemma` (only called by `RibetElement:269`); 2 single-use `CharacterRows` unpackers (`L346–L394`). |
| [`AuxiliaryPrimeTie.lean`](https://github.com/leanprover-community/riemann-hypothesis/blob/c3574bd1d732aad94e096732f983fc515288ed54/src/New/Congruences/FirstOrder/AuxiliaryPrimeTie.lean) | 718 | **30** | **18 inline copies** of `∑ g, D.residueRep Q g` (no `BaseLevel.normOp` def!); **two naked 7-tuple existential contracts** (`exists_deformed_norm_family` `L252`, `exists_heckeAlgebra_ribetElement` `L570`); hidden `set_option synthInstance.maxHeartbeats 200000` (`L83`) + copied `RingHomClass`/`Fintype.ofFinite` local instances (`L69–L71`); 13L `sub_dvd_pow_sub_smul_pow` (`L333–L345`) = 2-line Mathlib `sub_dvd_pow_sub_pow`. |
| [`FittingBlock.lean`](https://github.com/leanprover-community/riemann-hypothesis/blob/c3574bd1d732aad94e096732f983fc515288ed54/src/New/Congruences/FirstOrder/FittingBlock.lean) | 709 | **27** | **100% dead** `attribute [local instance] algebraMvPolynomial` at `L318` (zero uses!); chimera split at `L216`. |
| [`DenominatorBound.lean`](https://github.com/leanprover-community/riemann-hypothesis/blob/c3574bd1d732aad94e096732f983fc515288ed54/src/New/Congruences/FirstOrder/DenominatorBound.lean) | 1,337 | **22** | 5 single-use wrapper chains (~145L): `exists_isCommonRibetElement_ellVal_le` (`L483–L521`), 4-lemma `span_*_invtSubmodule` chain (`L778–L907`), `exists_det_one_sub_ne_zero` + `exists_prod_sub_det_one_sub_eq_zero` (`L406–L449`), duplicate `IsLiftGenerator.exists_isMainSummandLike*` (`L839, L964`), `denominatorLe_clearingBound` fold (`L1325`). |
| [`RibetElement.lean`](https://github.com/leanprover-community/riemann-hypothesis/blob/c3574bd1d732aad94e096732f983fc515288ed54/src/New/Congruences/FirstOrder/RibetElement.lean) | 424 | **22** | 36-line signature (`L293–L328`); dual `Sigma (SummandCoordIndex r)` vs `r ⊕ Fin t` reindexing (`L334, L384–L387`). |
| [`TiedTraces.lean`](https://github.com/leanprover-community/riemann-hypothesis/blob/c3574bd1d732aad94e096732f983fc515288ed54/src/New/Congruences/FirstOrder/TiedTraces.lean) | 820 | **20** | Copied `synthInstance.maxHeartbeats 200000` (`L147`) + `RingHomClass`/`Fintype.ofFinite` local instances (`L58–L61`). |
| [`TraceRelations.lean`](https://github.com/leanprover-community/riemann-hypothesis/blob/c3574bd1d732aad94e096732f983fc515288ed54/src/New/Congruences/FirstOrder/TraceRelations.lean) | 987 | **13** | Clean overall; `denominatorError : ℝ≥0∞` (`L110–L135`) is just a `ℕ` (cast noise); dual `SummandCoordIndex` (`L371–L399`). |
| [`RibetMethod.lean`](https://github.com/leanprover-community/riemann-hypothesis/blob/c3574bd1d732aad94e096732f983fc515288ed54/src/New/Congruences/FirstOrder/RibetMethod.lean) | 567 | **13** | Clean overall; duplicate `det_mem_of_coeff_mem` (`L346–L362`) vs `exists_mul_eq_algebraMap_det` (`L428`) + redundant `hρ_span` (`L221, L527`). |
| `TrianglePrimes` (13), `KummerMaps` (13), `TateTwistCocycles` (12), `EvenClasses` (8), `HeckeStrings` (5), `OnePrime` (5) | 3,419 | **5–13** | Already at human Mathlib baseline! Minor hygiene only: `EvenClasses.withConjInv` (`L77`) duplicates `New.idOrConjInv` (`CMSplittingCharacters.lean:758`); `KummerMaps:73–299` is generic `E/E⁺` Galois transport; `5+-tuple` unpacks in `EvenClasses`/`KummerMaps` are false positives from upstream `inertiaAbove`. |

---

## Part II: The "No-Weil–Deligne, Most-Frobenii" Galois Representation Stack (`src/Lib/GaloisRep/`)

### II.1 Exact Narrow Consumer Boundary & 6-Stage Pipeline

A complete import audit across `src/New/` shows **only 10 files** (all in `src/New/Congruences/`) import `Lib.GaloisRep`. The entire 31-file, 19,271-LOC stack delivers just **five concrete contracts**:

1. **Global attachment + spherical compatibility for all ranks $n \ge 1$** ([`AllRanks.lean#L469`](https://github.com/leanprover-community/riemann-hypothesis/blob/c3574bd1d732aad94e096732f983fc515288ed54/src/Lib/GaloisRep/Main/AllRanks.lean#L469), `sphericalCompat_std`): continuous semisimple (`IsTraceNondeg`) `r : GalRep ℓ E n` matching `charpoly = ιℓ(P w)` on `mostFrobenii E`, plus `IsGoodAt`, `HasJumpsAt`, and `PolyKillsAt` at spherical split places.
2. **Depth-zero tame inertia compatibility** ([`LabelCompatibility.lean#L496`](https://github.com/leanprover-community/riemann-hypothesis/blob/c3574bd1d732aad94e096732f983fc515288ed54/src/Lib/GaloisRep/LocalGlobal/LabelCompatibility.lean#L496), `Attached.isLabelledAt` + [`LocalFormTypes.lean#L289`](https://github.com/leanprover-community/riemann-hypothesis/blob/c3574bd1d732aad94e096732f983fc515288ed54/src/Lib/GaloisRep/LocalGlobal/LocalFormTypes.lean#L289), `HasParahoricType.hasProductLabel`): for a squarefree degree-$d$ Green label `c` + block determinant characters `χ_l` at a split place (both $w \nmid \ell$ and $w \mid \ell$), yields `IsFiniteTypeAt`, `HasJumpsAt`, and `IsLabelledAt A T d! (PolyKillsAt r A) ...`.
3. **Taylor–Wiles parahoric Frobenius–$U_\varpi$ trace identity** ([`IwahoriCompatibility.lean#L541, L668`](https://github.com/leanprover-community/riemann-hypothesis/blob/c3574bd1d732aad94e096732f983fc515288ed54/src/Lib/GaloisRep/LocalGlobal/IwahoriCompatibility.lean#L541), `isParahoricCompatible_galRep`, `hecke_eq_frob_on_parahoricEigenspace`): `tr(T M) • G(U) y = tr(G(F) T M) • y` on the $(1, n-1)$ line-stabilizer eigenspace.
4. **Lattice / residual irreducibility machinery** ([`Pseudorepresentations.lean#L120, L203, L236`](https://github.com/leanprover-community/riemann-hypothesis/blob/c3574bd1d732aad94e096732f983fc515288ed54/src/Lib/GaloisRep/Pseudocharacter/Pseudorepresentations.lean#L120)): `IsLatticeIn.span_range_eq_top_of_map_pow_eq_map_conj` etc.
5. **`BaseLevel` / `TaylorWilesPlaces` / `SelmerModules` / `DivisibleSelmerModules` containers.**

```text
[1] SeedRepresentation (866L) + CuspidalTypes (564L) + KillingPolynomials (496L)
    Odd rank a, E ⊇ ℚ(√-d), cuspidal type at w₀, free HT weights ⇒ PEL Shimura cohomology (1, a-1)
    + congruence relation (killing poly) + Sen cocharacter/Laurent powMinor ⇒ exact charpoly on mostFrobenii.
        │
        ▼
[2] SplitCase (676L) + WeightCongruence (741L) + Pseudocharacter/{Semisimple,Pseudo}representations (1,373L)
    Removes cuspidal-type & free-weight hypotheses via ultrametric Kaplansky Stone–Weierstrass
    + Procesi–Taylor bypass (`exists_rep_of_trace_identities`) + `local_clauses_of_trace_limit`.
        │
        ▼
[3] OddRank (522L) + QuadraticStep (579L) + BaseChange/PrimeDegreeTransfer (926L) + {GlobalRoot,TwistedTraceIdentity}
    Removes E ⊇ ℚ(√-d) via quadratic steps E(√-D) + definite prime-degree twisted trace formula
    + gluing across open subgroups `stepKer(χ T)` + `DescendsAt`.
        │
        ▼
[4] AllRanks (802L) + ThetaLift (517L) + AttachedRepresentations (437L)
    ALL ranks n ≥ 1 (NO ENDOSCOPY!): twin convergent definite theta lifts U(n) → U(2n+1) along two
    disjoint U(1) characters μ₀, μ₁ + trace cancellation + Bézout (`PolyKillsAt.of_mul_of_isCoprime`)
    ⇒ delivers `sphericalCompat_std`.
        │
        ▼
[5] IwahoriCompatibility (735L) + BaseChange/IwahoriEigenforms (841L)
    Sorted pro-p Iwahori eigencharacters: tame cyclic prime-degree base change shrinks [E_wˣ : D] → 1
    (unramified spherical) + Vandermonde/Horner parahoric trace identity (`hecke_eq_frob_on_parahoricEigenspace`).
        │
        ▼
[6] LabelCompatibility (519L) + BaseChange/ShintaniLift (404L) + LocalFormTypes (385L)
    Depth-zero Green labels: inert cyclic prime-degree base change (induction on primes dividing d!)
    + finite-group Shintani lift splits c over k_u ⇒ sorted tame Iwahori [5] ⇒ `Attached.isLabelledAt`.
```

### II.2 Traditional Literature vs. `Lib/GaloisRep/` (Why Each Shortcut Is Optimal)

| Dimension | Classical Literature (HT01, TY07, Shin11, CH13, BLGGT14, Caraiani12/14) | `src/Lib/GaloisRep/` & Why the Bypass Works |
|---|---|---|
| **Global attachment** | Match `charpoly(ρ_π(Frob_v)) = P_v(X)` at **every** unramified place using full quantitative Chebotarev + strong multiplicity one + Arthur–Clozel base change $U(n) \to \mathrm{GL}_n$. | **`mostFrobenii E`** ([`Main/Defs.lean#L213-L238`](https://github.com/leanprover-community/riemann-hypothesis/blob/c3574bd1d732aad94e096732f983fc515288ed54/src/Lib/GaloisRep/Main/Defs.lean#L213-L238)): topological dense-open-cofinite filter ($\forall$ nonempty open $V$, $\exists$ nonempty open $O \subseteq V$ holding for cofinally many $w$) backed by a 113-line qualitative Chebotarev ([`Chebotarev.lean`](https://github.com/leanprover-community/riemann-hypothesis/blob/c3574bd1d732aad94e096732f983fc515288ed54/src/Lib/ClassField/Global/Chebotarev.lean)). Continuity fixes $\mathrm{tr}(r(g))$ everywhere on $G_E$, and `mostFrobenii` pulls back cleanly under open embeddings (`L270`) without tracking exact ramification sets. |
| **Even ranks $n = 2k$** | Twisted Arthur–Selberg trace formula, fundamental lemma, endoscopic transfer $U(n) \to \mathrm{GL}_n$ (Labesse, Shin 2011, Morel, Mok). | **Twin convergent definite theta lifts $U(n) \to U(2n+1)$** ([`ThetaLift.lean#L437`](https://github.com/leanprover-community/riemann-hypothesis/blob/c3574bd1d732aad94e096732f983fc515288ed54/src/Lib/GaloisRep/Main/ThetaLift.lean#L437), [`AllRanks.lean#L118, L218`](https://github.com/leanprover-community/riemann-hypothesis/blob/c3574bd1d732aad94e096732f983fc515288ed54/src/Lib/GaloisRep/Main/AllRanks.lean#L118)) with disjoint $U(1)$ characters $\mu_0, \mu_1$ (non-vanishing via Rallis inner product) + trace cancellation + Bézout. **Eliminates endoscopy entirely.** |
| **Local-global compatibility ($v \nmid \ell$ and $v \mid \ell$)** | Full LLC $\mathrm{rec}_{E_v}(\pi_v)$ → **Weil–Deligne representation $(r, N)$**, proved via Harris–Taylor Lubin–Tate/Rapoport–Zink tower geometry (HT01/TY07), Caraiani's monodromy-weight theorem, and Fontaine $D_{\mathrm{pst}}$ / Saito / BLGGT14. | **`PolyKillsAt` + Cyclic Base Change + Shintani Lift:** `PolyKillsAt` unifies $v \nmid \ell$ ($Q(r(s)) = 0$) and $v \mid \ell$ (action on Fontaine periods $D_{\mathrm{pst}}$) in one predicate closed under trace limits, Bézout, and `DescendsAt`. Every ramified type in GRH is **depth-zero, squarefree, and monodromy-free ($N = 0$)**, so inert prime-degree base change + finite-group Shintani lift reduces Green labels $\to$ sorted tame Iwahori $\to$ unramified spherical using only a simple definite twisted trace formula! |
| **Trace-limit reconstruction** | Chenevier determinant theory + Taylor–Procesi–Rouquier invariant theory. | **`exists_rep_of_trace_identities`** ([`Pseudorepresentations.lean`](https://github.com/leanprover-community/riemann-hypothesis/blob/c3574bd1d732aad94e096732f983fc515288ed54/src/Lib/GaloisRep/Pseudocharacter/Pseudorepresentations.lean)): assumes all polynomial trace identities on an approximating monoid, bypassing Procesi invariant theory cleanly. |

### II.3 Verified `TauCeti` Ecosystem Audit (Negative & Positive Findings)

- **Definitive NEGATIVE verdict on `TauCeti/RepresentationTheory/WeilDeligne/` (11 files, 2,833 LOC):** All 11 files (`Basic`, `Local`, `Unramified`, `InertialType`, `BaseChange`, `Operations`, `Rescale`, `Restriction`, `Determinant`, `Special`, `SymmetricPower`) formalize pure linear algebra of abstract $(V, r, N)$ parameters. `TauCeti` has **zero** $\ell$-adic monodromy functor ($v \nmid \ell$; `LocalMonodromyDatum` is Scholze's axiomatic purity datum only), **zero** Fontaine $D_{\mathrm{pst}} \to \mathrm{WD}$ functor ($v \mid \ell$), and **zero** LLC/automorphic bridge. `src/` currently has **0** references to `WeilDeligne`, and `New/Congruences/` never needs $N \neq 0$. **Do NOT force `WeilDeligne` into `Lib/GaloisRep/`.**
- **Verified POSITIVE `TauCeti` overlaps (Genuine PR `#6070`-caliber deletions):**
  1. **`TauCeti.RepresentationTheory.Continuous.{BrauerNesbitt, IntegralModel/{Basic,Matrix}}`** $\longleftrightarrow$ [`SemisimpleRepresentations.lean`](https://github.com/leanprover-community/riemann-hypothesis/blob/c3574bd1d732aad94e096732f983fc515288ed54/src/Lib/GaloisRep/Pseudocharacter/SemisimpleRepresentations.lean) (658L): Once `IsTraceNondeg ↔ Representation.IsSemisimpleRepresentation` is bridged over `IsAlgClosed k`, `CharZero k`, `exists_conj_of_trace_eq` delegates to `Continuous.BrauerNesbitt` and `eventually_exists_isLatticeIn` delegates to `IntegralModel.nonempty` + `exists_basis_continuousMonoidHom_GL` (**~250–350 net LOC deletable**).
  2. **`TauCeti.NumberTheory.HeckeRing.GLn.HeckePolynomial.Basic.glnHeckePolynomial`** $\longleftrightarrow$ [`New.heckePoly`](https://github.com/leanprover-community/riemann-hypothesis/blob/c3574bd1d732aad94e096732f983fc515288ed54/src/Lib/GaloisRep/Main/Defs.lean#L70) (83 refs): Exact formula match ($\sum (-1)^i q^{\binom{i}{2}} T_i X^{n-i}$) including Satake factorization (`IwahoriCompatibility.lean#L180`) and dual inversion (`AttachedRepresentations.lean#L317-L344`) (**~100–150 net LOC deletable**).
  3. **`TauCeti.RingTheory.FittingIdeal` (`Submodule.minorsIdeal`)** $\longleftrightarrow$ [`New.Selmer.fittingIdeal`](https://github.com/leanprover-community/riemann-hypothesis/blob/c3574bd1d732aad94e096732f983fc515288ed54/src/Lib/General/Algebra/FittingIdealsAndLengths.lean#L476) (**~60–90 net LOC deletable**; note ordered triangle induction `exists_ge_mul_prod_mem` and dual Noetherian `exists_addVal_le_relLength` stay local).

### II.4 Anatomy of the `#1` & `#3` Worst Slopscore Files and `#1` & `#4` Longest Monoliths

1. **`#1` Worst Slopscore in the Entire 300k Repo — [`LabelCompatibility.lean`](https://github.com/leanprover-community/riemann-hypothesis/blob/c3574bd1d732aad94e096732f983fc515288ed54/src/Lib/GaloisRep/LocalGlobal/LabelCompatibility.lean) (519L, Slopscore `46.0`):**
   - **Strong technical debt (`attribute [-instance]` at [`L101`](https://github.com/leanprover-community/riemann-hypothesis/blob/c3574bd1d732aad94e096732f983fc515288ed54/src/Lib/GaloisRep/LocalGlobal/LabelCompatibility.lean#L101)) — 1 of ONLY 3 occurrences in the entire 300k-line repo!** Root cause traced to [`Lib/Cohomology/Etale/Basic.lean#L490`](https://github.com/leanprover-community/riemann-hypothesis/blob/c3574bd1d732aad94e096732f983fc515288ed54/src/Lib/Cohomology/Etale/Basic.lean#L490): a default-priority global `instance : IsAbsIntegrallyClosedLocal K` for `[Field K] [IsAlgClosed K]` causes `c.aroots K` to resolve `IsDomain K` through `IsFaithfulMulChar K T → IsAlgClosed K → IsAbsIntegrallyClosedLocal K → IsDomain K`, dragging `T` into `IsLabelledAt`'s section variables. Setting `priority := low` at `Etale/Basic.lean:490` fixes the root cause globally.
   - **6 instance-surgery hacks in 519L** (duplicate `Fintype.ofFinite` at `L65, L280`, `attribute [-instance]` at `L101`, 2 inline `let : Field/Algebra` instances at `L181–L183`, `algebraize [j, i]` + `subst` at `L247, L256`).
   - **2 forced non-defeq `using!` hacks (`L337, L339`)** + an **11-lemma `simp` bomb (`L348–L350`)**.
   - **10-conjunct flat existential `IsTameExponent` (`L84–L94`)** instead of a `structure`, forcing 13-variable positional `obtain`s (`L132, L248`) and 17-field anonymous tuple constructors (`L223, L268`).
   - **~150 copy-pasted binders across 3 theorems** (`L293–L305`, `L414–L426`, `L496–L507`) because `section LabelCompatibility` declares zero `variable`s.
   - **Quantifier-smuggling anti-pattern:** `isLabelledAt_one` and `isLabelledAt_of_root_pow_eq_one` stuff `(σ, Q)`-independent `IsFiniteTypeAt ∧ HasJumpsAt` inside `IsLabelledAt`'s predicate solely to thread them through `induction_on_primes`, forcing `Attached.isLabelledAt` (`L515–L517`) to conjure a dummy witness `σ₀` to extract them back out!

2. **`#3` Worst Slopscore (`33.0`, `bf=25.0`) — [`QuadraticStep.lean`](https://github.com/leanprover-community/riemann-hypothesis/blob/c3574bd1d732aad94e096732f983fc515288ed54/src/Lib/GaloisRep/Main/QuadraticStep.lean) (579L):**
   - **4 `decide +kernel` calls (`L118–L119`) — the ONLY file in `Lib/GaloisRep/` with `decide +kernel`:** exhaustively enumerates `ZMod 80` and `ZMod 63` in the kernel instead of a 5-line CRT proof via `ZMod.unitsEquivProd` ($(\mathbb{Z}/80)^\times \cong (\mathbb{Z}/16)^\times \times (\mathbb{Z}/5)^\times$ has exponent $4$; $(\mathbb{Z}/63)^\times \cong (\mathbb{Z}/9)^\times \times (\mathbb{Z}/7)^\times$ has exponent $6$).
   - **13 `grind` calls** (highest in `Lib/GaloisRep/`), clustered in `exists_real_twist` (`L246–L287`: 5 `grind` hammers rewriting `Quotient.eq_zero_iff_mem` instead of working directly in $\mathcal{O}_E / w^k$ with `ring`).
   - **16-case `split_ifs <;> simp [*]` truth table (`L403–L410`)** proving a 4-line $\mathbb{F}_2^2$ spanning fact: if $v = (\chi(\sigma), \chi(\sigma^c)) \in \{0, \frac{1}{2}\}^2$ has $v_1 + v_2 \neq 0$, then $\{v, \mathrm{swap}(v)\}$ spans $\{0, \frac{1}{2}\}^2$.
   - **Two 4-way Kummer sign case-bashes (`L204–L215`, `L358–L368`)** replaced by `map_mul` on a 5-line homomorphism `sqrtSign : Gal(Ω/E) →* {±1}` ($g \mapsto g(b)/b$).
   - **24L dead-weight unbundling wrapper `exists_isStep_hasQuadSubfield` (`L552–L575`)** whose only 2 callers (`OddRank.lean:457`, `LocalGlobalCompatibility.lean:203`) can consume `exists_isQuadraticStep` directly.

3. **`#1` & `#4` Longest Proofs in the Repo:**
   - [`PrimeDegreeTransfer.lean#L703-L859`](https://github.com/leanprover-community/riemann-hypothesis/blob/c3574bd1d732aad94e096732f983fc515288ed54/src/Lib/GaloisRep/BaseChange/PrimeDegreeTransfer.lean#L703-L859) (`exists_eigenvector_of_isTransferLevel`, **170L**): takes ~35 unpacked arguments duplicating `IsLocalMatching` (which its single caller at `L907` just destructured!) and packs 9 stages + 8 interdependent local `let`s inline.
   - [`SeedRepresentation.lean#L686-L816`](https://github.com/leanprover-community/riemann-hypothesis/blob/c3574bd1d732aad94e096732f983fc515288ed54/src/Lib/GaloisRep/Main/SeedRepresentation.lean#L686-L816) (`exists_padicRep_of_cuspidal_type_at_embedding`, **140L**): chains 7 stages inline, notably an extractable 39L `U(a) → GU(a)` test-vector & `OccursInWeight` lemma (`L752–L790`).

---

## Part III: Honest Separation Matrix (Preserve vs. Refactor vs. Do NOT Do)

| Pattern / Subsystem | Verdict | Justification |
|---|---|---|
| Prime triangles + parity-decoupling shift $\sigma = \delta^{\ell^\nu}(g g^c u/u^c)$ + 3-stage $O[X_j]$-Fitting filtration | **KEEP (Essential Math)** | Unconditionally evades Vandiver's conjecture (`#evenClasses` drops out). |
| Finite-level first-order norm $\mathcal{N} = \prod_j (\mathrm{Nm}_j + \alpha_j \partial_j)$ + `Ver(g₀₀) = det` + quadratic shift $x(x+k)$ | **KEEP (Essential Math)** | Eliminates infinite $N \to \infty$ patching, ultrafilters, Auslander–Buchsbaum, and works for $\ell = 2$. |
| Non-commutative Cramer (`RibetMethod`) + `tiedNormaliser` $\rho_0$ + 3-way split $W \oplus s_0 \oplus s$ | **KEEP (Essential Math)** | Works at small $\ell \le t$ without Hensel idempotents and without conjugating non-lifts. |
| `mostFrobenii` + `PolyKillsAt` + twin theta lifts $U(n) \to U(2n+1)$ + cyclic BC / Shintani lift | **KEEP (Essential Math)** | Eliminates endoscopy, Harris–Taylor Lubin–Tate geometry, LLC for $\mathrm{GL}_n$, and Weil–Deligne $(r, N)$. |
| `TauCeti.WeilDeligne` / `TauCeti.GMAData` / `TauCeti.RibetLattice` replacement | **DO NOT DO** | Mathematically mismatched or unbridged (zero monodromy/$D_{\mathrm{pst}}$/LLC bridge; no orthogonal idempotents at $\ell \le t$). |
| Rewriting `OnePrime`, `HeckeStrings`, `TrianglePrimes`, `RibetMethod`, or upstream `inertiaAbove` | **DO NOT DO** | Already Slopscore 5–13 (human Mathlib baseline); touching would be lateral churn. |
| `LabelCompatibility` + `Etale/Basic:490`, `QuadraticStep`, `SemisimpleRepresentations` → `TauCeti`, `TieSystem` / killing `CharacterRows` & dead `algebraMvPolynomial`, `DenominatorBound` wrapper pruning, `BaseLevel.normOp` + bundling `AuxiliaryPrimeTie` | **REFACTOR (High ROI)** | Pure Lean engineering debt or direct `TauCeti` duplication; **~1,200–1,600+ net LOC deletable** with major readability and Slopscore wins. |

---

## Part IV: Ranked High-Impact Upstream Refactoring Roadmap

All seven candidates clear our calibrated minimum bar ([PR #6070](https://github.com/leanprover-community/riemann-hypothesis/pull/6070): `-48` net LOC genuine structural/ecosystem deletion, zero churn, zero warnings). **Live conflict check (2026-11-26, 500 open upstream PRs):** Every open PR touching these directories is a tiny lint/deprecation/unused-instance micro-PR (`#5862`, `#5868`, `#6003` [`+2/-7`], `#6223`, `#6232`, `#6256`, `#6262`, `#6268`, `#6277`, `#6278`) — **zero substantive overlap** with Candidates A–G! *(Only note `#6031` removes `IsTwistedLattice.scalar_eq`/`ζ` in `DenominatorBound`/`RibetElement`/`TraceRelations`, so check `#6031` before branching Candidate E.)*

| Rank | Candidate | Files Touched | Est. Net LOC | Key Technical & Slopscore Win |
|---:|---|---|---:|---|
| **A** | **`LabelCompatibility` structural cleanup + root-cause `Etale/Basic:490` priority fix** | `Etale/Basic.lean` (1L), `LabelCompatibility.lean` | **-150 to -180L** | Eliminates **1 of only 3 `attribute [-instance]` strong-debt hacks in the entire 300k repo**; promotes `IsTameExponent` to a `structure`; fixes quantifier-smuggling (`σ₀` hack); kills `using!` × 2 & ~150 repeated binders. Drops `#1` Slopscore **`46.0 → single digits`**. |
| **B** | **Algebraic rewrite of `QuadraticStep.lean`** | `QuadraticStep.lean`, `OddRank.lean` (1 site), `LocalGlobalCompatibility.lean` (1 site) | **-150+L** | Eliminates **all 4 `decide +kernel` calls** (5L CRT via `ZMod.unitsEquivProd`), 16-case `split_ifs` (4L $\mathbb{F}_2^2$ span), 4-way Kummer sign case-bashes (5L `sqrtSign →*`), 5 `grind`s in `exists_real_twist`, and dead-weight 24L `exists_isStep_hasQuadSubfield`. Drops `#3` Slopscore **`33.0 (bf=25) → single digits`**. |
| **C** | **Deduplicate `SemisimpleRepresentations.lean` against `TauCeti`** | `SemisimpleRepresentations.lean` | **-250 to -350L** | Bridge `IsTraceNondeg ↔ Representation.IsSemisimpleRepresentation`, delegating `exists_conj_of_trace_eq` to `TauCeti.Continuous.BrauerNesbitt` and `eventually_exists_isLatticeIn` to `TauCeti.IntegralModel`. Largest pure `TauCeti` deletion! |
| **D** | **Ribet Matrix Core: `TieSystem` + kill 13-field `CharacterRows` + drop dead `algebraMvPolynomial`** | `FittingBlock.lean`, `RibetMatrices.lean`, `RibetLemma.lean`, *(optional)* `RibetMethod.lean` | **-320 to -435L** | Deletes **100% dead** `algebraMvPolynomial` (`FittingBlock:318`) + scopes `RibetMatrices`/`RibetLemma`; bundles 6-field `TieSystem`; eliminates 13-field/16-param `CharacterRows`; inlines 9 trivial `tieIdeal` wrappers; deduplicates `RibetMethod`. Drops `RibetMatrices` **`35 → ~12`**, `RibetLemma` **`32 → ~13`**, `FittingBlock` **`27 → ~15`**. |
| **E** | **Prune `DenominatorBound` wrapper chains + `denominatorError : ℕ` + unify `r ⊕ Fin t`** | `DenominatorBound.lean`, `TraceRelations.lean`, `RibetElement.lean`, `FitTwistsExist.lean` | **-220 to -260L** | Collapses 5 single-use wrapper chains (~145L), drops `ℝ≥0∞` cast noise on `denominatorError`, removes `Sigma (SummandCoordIndex r)` vs `r ⊕ Fin t` dual reindexing. *(Check `#6031` first.)* |
| **F** | **De-slop `AuxiliaryPrimeTie` & `TiedTraces` (`BaseLevel.normOp`, bundled records, drop `synthInstance` hacks)** | `TiedTraces.lean`, `AuxiliaryPrimeTie.lean` | **-60 to -90L** | Replaces **18** inline `∑ g, residueRep Q g` copies with `BaseLevel.normOp`; bundles two 7-tuple existentials into `DeformedNormFamily` & `HeckeRibetData`; eliminates copied `synthInstance.maxHeartbeats 200000` + `RingHomClass` hacks; 2L Mathlib `sub_dvd_pow_sub_pow`. Drops `AuxiliaryPrimeTie` **`30 → ≤ 5`**, `TiedTraces` **`20 → ≤ 5`**. |
| **G** | **Ecosystem alignments & monolith bundling** | `Main/Defs.lean` (`heckePoly` → `TauCeti.glnHeckePolynomial`, **-100 to -150L**); `FittingIdealsAndLengths.lean` (`fittingIdeal` → `TauCeti.minorsIdeal`, **-60 to -90L**); `PrimeDegreeTransfer` / `SeedRepresentation` bundling | **-160 to -240L** | Unifies 83 `heckePoly` call sites onto `TauCeti`, aligns Fitting ideals onto `TauCeti`, and bundles `IsLocalMatching` / `exists_testVector_and_occursInWeight` to break up the `#1` (170L) and `#4` (140L) monoliths. |

---

## Part V: One-Page Conceptual Key (Human-Readable Intuition)

### Key 1 — How `New/Congruences/FirstOrder/` Evades Vandiver & Infinite Patching
1. **Why normal Ribet gets stuck:** For a theta lift $u_x \simeq \psi R_x \oplus \bigoplus_{e=0}^{t-1} \chi_{\mathrm{cyc}}^{-e}$, the main summand's Selmer length is already bounded (`Selmer/TwistingTheorem`) and the **odd** Tate-twist cocycles `shaOdd` are bounded unconditionally by Stickelberger + Kolyvagin (`OddSha`). Only the **even** Tate-twist cocycles `evenClasses` ($\mathrm{Cl}(E(\mu_{\ell^\infty}))^+$) lack an unconditional bound (Vandiver's conjecture).
2. **Galois escape:** Pick a fixed finite ordered **prime triangle $J$** via Chebotarev at the parity-decoupling shift $\sigma = \delta^{\ell^\nu}(g g^c \cdot u/u^c)$, so odd Kummer maps satisfy $\psi_j(\varphi_i) = 0$ for $i > j$ while even classes satisfy $z(\varphi_j) = 2 z(g_j)$. Imposing formal ties $z(\tau_j) = X_j z(\varphi_j)$ over $\mathcal{O}[X_j]$ lets upper-triangular reciprocity kill all even classes at cost $\prod X_j$, leaving a Fitting-ideal valuation independent of `#evenClasses`.
3. **Matrix engine without Hensel idempotents:** Because characters collide mod small $\ell \le t$, separate $\rho_x$ from characters by an exact inertia projector $k$, introduce $\rho_0 = e + (1-e)(a-1)$ ($1$ on $\rho_\pi$, $0$ on $\xi_0$, $\xi_e(a)-1$ on $\xi_{e>0}$), eliminate uncontrolled Noetherian generators $s_0$ via unscaled unit rows, and apply Amitsur + block Cayley–Hamilton to $(B - X B_1) y = 0$ (right $X$-action by $\rho_0$) to obtain a polynomial Hecke Ribet element $\mathcal{D} \in \mathbb{T}[X_j]$ without ever conjugating non-lifts.
4. **Automorphic realization at ONE finite level $\nu$:** Because $\#J$ is independent of $\nu$ and only the squarefree term $\prod X_j$ matters, choose $\nu$ *after* $\#J$ is fixed and deform the base-level group norm to first order: $\mathcal{N} = \prod_j (\mathrm{Nm}_j + \alpha_j \partial_j)$. The mirabolic transfer theorem $\mathrm{Ver}(g_{00}) = \det$ makes $\partial_j$ differentiate tame inertia into Frobenius, killing the tie ideal; Higman's trace trick pulls lower terms through $\mathrm{Nm}$, isolating $\mathcal{D}_J$ as an integral denominator-clearing operator!

### Key 2 — How `Lib/GaloisRep/` Avoids Endoscopy, LLC, and Weil–Deligne
1. **Minimal consumer interface:** `New/Congruences/` only ever needs continuous traces on a dense Frobenius set (`mostFrobenii`), local annihilating polynomials (`PolyKillsAt`) on depth-zero monodromy-free ($N = 0$) inertia/Fontaine periods, and one parahoric Vandermonde trace identity at Taylor–Wiles primes.
2. **Four shortcuts that stay purely inside definite unitary groups:**
   - **Seed $\to$ Odd Split:** PEL congruence relation gives killing polynomials $\to$ Sen cocharacter (`KillingPolynomials`) upgrades to exact `charpoly` $\to$ ultrametric Stone–Weierstrass + trace-identity limits remove cuspidal-type/free-weight restrictions.
   - **Split $\to$ General Odd:** Quadratic steps $E(\sqrt{-D})$ + definite prime-degree twisted trace formula glue across open subgroups.
   - **Odd $\to$ All Ranks (No Endoscopy):** Two convergent definite theta lifts $U(n) \to U(2n+1)$ along disjoint $U(1)$ characters + trace cancellation + Bézout on `PolyKillsAt`.
   - **Spherical $\to$ Depth-Zero Types (No LLC / No Weil–Deligne):** Prime-degree inert cyclic base change + finite-group Shintani lift splits Green's character into sorted tame Iwahori eigencharacters; tame cyclic base change shrinks $[E_w^\times : D] \to 1$ (unramified spherical).
