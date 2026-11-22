/* ==========================================================================
   explain_kb.js — Strictly Guardrail-2-compliant contextual explainer KB
   Every entry tags claims with [L] (Lean source / real DB), [A] (remark.pdf),
   [C] (cited community reading), [S] (standard maths), or [M] (our analogy,
   always paired with "Where this analogy breaks").
   NEVER invents math glue for unaudited internal modules.
   ========================================================================== */
"use strict";

window.EXPLAIN_KB = (function () {
  var PROVENANCE = {
    L: { label: "Lean / Extracted", desc: "Directly observed in Lean source, challenge.ndjson, or deterministic leanre DB scan." },
    A: { label: "Author Note", desc: "Asserted in Alpöge's 4-page note (remark.pdf). Note Footnote 4 warns parts paraphrase a machine summary." },
    C: { label: "Community Reading", desc: "Reported by independent community audits (Deicyde, Sutherland, jae-63, nasqret, drew2apps)." },
    S: { label: "Standard Maths", desc: "Published, textbook mathematics independent of this proof." },
    M: { label: "RE / CS Analogy", desc: "Pedagogical systems analogy. Always carries an explicit 'Where this analogy breaks' note." }
  };

  var ENTRIES = [
    {
      match: function (name) { return name === "Main" || name === "Statements" || name.indexOf("MainTheorems") >= 0; },
      title: "Entry Point & Specification Boundary (Layer 1 & 2)",
      blocks: [
        { tag: "L", head: "What is actually here", text: "Main.lean (12 lines) exports 5 headline theorems: Mathlib's own RiemannHypothesis plus 4 thin wrappers defined in Statements.lean (which imports ONLY Mathlib) — 1 zeta RH wrapper (RiemannZetaZerosOnLine) + 3 Dirichlet L-function GRH wrappers. Nothing in the 17.37M-line proof can alter what these statements mean." },
        { tag: "C", head: "Verification status (2026-11-21)", text: "Reported accepted by Lean v4.33.1 leanchecker, Rust nanoda, con-leche --compare (against 51,692-decl Challenge), and lean4lean. All 5 headline theorems depend strictly on [propext, Classical.choice, Quot.sound]." },
        { tag: "S", head: "Scope boundary — Dirichlet GRH only", text: "In this archive, GRH covers Dirichlet L-functions L(s, χ) only — NOT Dedekind zeta or general Hecke L-functions. Computationally, this makes Miller's deterministic primality test & deterministic Tonelli-Shanks unconditional, but does NOT break RSA/ECC/lattices or cover class-group Hecke bounds." },
        { tag: "M", head: "RE analogy: main() and the API header", text: "Treat Main.lean as the binary's export table and Statements.lean as the public header contract. A kernel replay checks that the implementation satisfies the header; human auditors only need to verify the header + Mathlib's definitions match classical RH." },
        { tag: "M", head: "Where this analogy breaks", text: "In software, specs are often buggy while code is easy to read. Here, the spec is 1 line long (and stable in Mathlib), while understanding WHY the 175,187-file implementation works is the real open problem." }
      ],
      labs: [
        { title: "Playable RH·MAP — Entry Point & Trust Chain", desc: "Inspect the 4 layers of 'Is RH Proved?' in the concept map.", href: "../prototypes/concept_map_demo.html#node=tcb&lens=re" }
      ]
    },
    {
      match: function (name) { return /RhOfRight|CritLine|ClaimStrip|Imprimitive|GammaFactorNonvanishing/i.test(name); },
      title: "Classical Functional-Equation Reflection (~200 Lines)",
      blocks: [
        { tag: "L", head: "Verbatim reduction above allChi", text: "Everything in Formalism.GammaFactorNonvanishing (RhOfRight.lean is 62 lines; CritLine.lean is 32 lines) uses only Mathlib's riemannZeta_one_sub and completedLFunction_one_sub to mirror any zero with Re(s) < 1/2 to 1 - s with Re(1 - s) > 1/2." },
        { tag: "S", head: "Why non-vanishing on Re(s) > 1/2 suffices", text: "Because ζ(s) and primitive L(s, χ) satisfy a reflection symmetry across Re(s) = 1/2, ruling out zeros in the right half-plane automatically rules out the left half-plane. For imprimitive characters, extra Euler factors vanish only on Re(s) = 0." },
        { tag: "M", head: "RE analogy: thin textbook adapter", text: "This layer is a clean, readable 200-line adapter between the archive's single internal master claim (UpperTheory.EveryCharacter) and the 5 public theorems. If you want to read real Lean from this corpus, start here." },
        { tag: "M", head: "Where this analogy breaks", text: "File-level import graphs make small files here look gigantic (transitively importing >100k modules via EveryCharacter). Only declaration-level or Horn-contract analysis shows how tiny this layer truly is." }
      ],
      labs: [
        { title: "Lab A — Watch the Mirror Symmetry Live", desc: "Drag a rogue zero off Re(s) = 1/2 and see the functional equation force its mirror partner 1 − β ± iγ.", href: "../prototypes/concept_map_demo.html#tab=labA&node=reflect&rogue=0.7,17.8" }
      ]
    },
    {
      match: function (name) { return /MainConclusion|EveryCharacter|OpenLiteratureStatements|EveryCharacterOfLiterature/i.test(name); },
      title: "Dependency-Injection Assembly & the 195 'Literature' Theorems",
      blocks: [
        { tag: "L", head: "The top-level Horn spine", text: "MainConclusion.lean wires everyCharacter := everyCharacter_of_row galoisLocalGlobalStrong_recParameter, passing ⟨h, recTExists, h⟩ and vwin_of_row h into every_character_of_literature_of_vWin. EveryCharacter.lean exhibits plugWin (hG : Green) (hV : VWin) (h : Nonempty (Hyps …)) : ZeroFreeAll." },
        { tag: "C", head: "The 195 *_of_literature surprise", text: "Community readers (jae-63, keithadler) found that OpenLiteratureStatements wraps 195 theorems named *_of_literature (Hironaka, Siegel-Weil, Fargues, Bhatt-Scholze, etc.), yet 191 of 195 ignore the bundle argument and invoke complete in-repo proofs, while the 3 bundle fields are themselves proved in-repo." },
        { tag: "M", head: "RE analogy: statically linked vendored stdlib", text: "Looks like a manifest of dynamic external imports; actually statically linked inside the binary. Because Mathlib lacked these graduate theorems, the proof formalized them internally — explaining a huge fraction of the 17.37M lines." },
        { tag: "M", head: "Where this analogy breaks", text: "Being proved in-repo guarantees soundness for RH, but does NOT prove that each internal *_of_literature statement faithfully matches the full textbook theorem it is named after." }
      ],
      labs: [
        { title: "RH·MAP — Explore the Lean Spine", desc: "See how allChi connects the automorphic foundation, VWin, and the analytic engine.", href: "../prototypes/concept_map_demo.html#hl=spine&lens=re&node=allchi" }
      ]
    },
    {
      match: function (name) { return /StatementOC|Landau|TopWin|ExplicitFormula|CharFamily|MellinRamp|CoreGm|WindowInequality|TieGlobal/i.test(name); },
      title: "The Proof's Observable Gz(x) & Localized Landau Engine",
      blocks: [
        { tag: "L", head: "Verbatim statistic in Formalism/StatementOC.lean", text: "Sz(x) = Σ_{n ≤ x} Λ(n)(x/n − 1) and Gz(x) = Sz(x) − x log x + (1 + γ)x (plus character twist Gchi). This literally matches Item #5 of Alpöge's 4-page note." },
        { tag: "S", head: "Why a ramp-weighted sum beats ψ(x)", text: "Explicit formula: Gz(x) = log(2π) − Σ_ρ x^ρ / (ρ(ρ−1)) + O(x⁻²). Unlike Chebyshev's ψ(x), the zero sum converges absolutely and under RH stays inside ±0.0462·√x (where 0.0462 = 2 + γ − log 4π)." },
        { tag: "C", head: "One-sided window criterion", text: "Community readings (nasqret, jae-63) report that a localized Landau theorem shows a ONE-SIDED upper bound G_ψ(x) ≤ x^(1/2+9ε) on arbitrarily late multiplicative windows [Y, Y^(3/2)] already forbids zeros with Re(s) > 1/2+9ε." },
        { tag: "M", head: "RE analogy: low-pass oscilloscope probe", text: "Gz(x) is the single cleanest instrumentation tap in the proof: primes in, spectrum of ζ out, with Gibbs ringing filtered away." },
        { tag: "M", head: "Where this analogy breaks", text: "One-zero intuition ('catching upswings') breaks with infinitely many interfering zeros; the real mechanism is Landau's theorem on non-negative coefficients, which is why the proof averages over characters with positive weights." }
      ],
      labs: [
        { title: "Lab A — Live Gz(x) Oscilloscope & Rogue Zero", desc: "Plot Formalism.Gz from real primes vs. 1,000 Odlyzko zeros, shade a Landau window, and drag a rogue zero off Re(s) = 1/2.", href: "../prototypes/concept_map_demo.html#tab=labA&node=gz&rogue=0.7,17.8" }
      ]
    },
    {
      match: function (name) { return /ExistsPageN|VWin|VwinOfRow|Behrend|GaloisCohomology|Selmer|Window1|IsChiField/i.test(name); },
      title: "Cohomological Window (VWin), Auxiliary Primes & Iwasawa Tower",
      blocks: [
        { tag: "L", head: "Verbatim structure in ExistsPageN.lean", text: "VWin := ∀ ψ, VWinAt ψ 401 bounds weighted Galois cohomology lengths shaLen over 1 ≤ e < ⌊x^401⌋ by √(exp(x^ε)) across windows [Y, Y²] for cyclotomic subfields IsChiField ψ e q d E with 2^(e+2) | N and WinPair primes q ≡ 3 (mod 8), d ≡ 7 (mod 16), q | d + 1." },
        { tag: "A", head: "Author's note context (Items #11, #17, #19)", text: "Alpöge describes an Iwasawa tower analogous to pigeonholing over F_{q^n}/F_q (Item #11), controlling residual H¹ classes via a weakening of Vandiver (Item #17), and using Behrend sets to pick the tower (Item #19, which Footnote 7 guesses is removable)." },
        { tag: "C", head: "Open mapping question", text: "jae-63 noted Formalism/BehrendSets has 89 declarations, none reached within depth ≤ 12 of everyCharacter in text traces — still open whether BehrendSets is live in the compiled kernel slice." },
        { tag: "M", head: "RE analogy: leak budget + parameter sweep", text: "Each divisibility step leaks a little via H¹ cohomology; VWin sweeps the 2-power tower knob and pigeonholes a clean window where the total leak stays below budget." },
        { tag: "M", head: "Where this analogy breaks", text: "Why the specific constants 401, 1/52, q ≡ 3 mod 8, d ≡ 7 mod 16 appear is deep arithmetic geometry, not an arbitrary tuning parameter." }
      ],
      labs: [
        { title: "RH·MAP — Paying the Costs (VWin & Iwasawa)", desc: "Inspect how VWin, character averaging, and the 41-day timeline fit together.", href: "../prototypes/concept_map_demo.html#node=vandiver&lens=lean" }
      ]
    },
    {
      match: function (name) { return /Theta|Rallis|Seesaw|Bessel|SiegelMass|SlopeIneq|Covolume|Stepanov|LeviDeterminants|BlockDeterminants|HypsAlt|ThirdPlaceSeries/i.test(name); },
      title: "Iterated Theta Lifts (m ≈ √X), Stepanov Ancestry & Bost Slope Ledger",
      blocks: [
        { tag: "A", head: "Core idea from remark.pdf (p. 1, Items #7–#13)", text: "Alpöge frames the argument as a descendant of Stepanov's finite-field RH proof. Integers lack derivatives ('multiplicity'), so Claude proposed chaining m ≈ √X theta lifts between totally definite unitary groups U(X_0) → … → U(X_m), each step mimicking one unit of multiplicity, paired with GGP/Bessel periods, Rallis seesaw, and Bost's slope inequality." },
        { tag: "C", head: "Community reading of the estimate", text: "nasqret Step 4 reads the central inequality as weighing algebraic-integer divisibility (ASK) against size (MAIN) via Bost's slope inequality, yielding error scaling like x/m + m + √x — balancing at m ≈ √x." },
        { tag: "M", head: "RE analogy: gadget chain + conservation ledger", text: "Just as Chebyshev's 1850 trick uses log|N| ≥ Σ v_p(N) log p (size is a budget, divisibility spends it), chaining theta lifts acts as a composable gadget chain whose optimal length minimizes x/m + m at √x." },
        { tag: "M", head: "Where this analogy breaks", text: "Chebyshev's binomial trick only yields constant-factor bounds, not √x; and WHY an iterated theta lift adds 'multiplicity' in the sense of Stepanov is the mathematical heart that no outsider has yet fully explained." }
      ],
      labs: [
        { title: "Lab C — Divisibility vs Size & the √X Balance", desc: "Explore Chebyshev's C(2n,n) ledger and slide chain length m across the X/m + m curve.", href: "../prototypes/concept_map_demo.html#tab=labC&node=theta" },
        { title: "Lab B — Finite Fields (Where RH Is Already Proved)", desc: "Explore Hasse's bound |a_p| ≤ 2√p and supersingular CM primes where D^p = 0.", href: "../prototypes/concept_map_demo.html#tab=labB&node=cm&curve=0,1" }
      ]
    },
    {
      match: function (name, info) {
        var flags = (info && info.module && info.module.forensic_flags) || [];
        return /kexactB|kcopy|OwnStruct|CutCptCopy|HeckeNonvanishing\.Imports|BuildAid|EvalFrameOrd/i.test(name) ||
          flags.indexOf("kexactB") >= 0 || flags.indexOf("CutCptCopy") >= 0 || flags.indexOf("kcopy") >= 0;
      },
      title: "Metaprogramming & Elaborator-Bypass Forensic Hotspot",
      blocks: [
        { tag: "L", head: "What leanre detected here", text: "Direct corpus forensics found kexactB in 50 files directly and 72 files including its kc%/kq%/kd%/tr_via/tr_clause macro wrappers (closest is 6 hops from Main), kcopy in 4 files, CutCptCopy in 2 files (2 addDecl sites at 17 hops), and run_tac/run_cmd in 21 files (16 run_tac + 5 BuildAid run_cmd). Zero sorry/axiom/native_decide/unsafe/implemented_by exist." },
        { tag: "C", head: "Security & soundness implications (Deicyde NOTES.md)", text: "Bypassing the elaborator via Term.elabTermAndSynthesize + g.assign does NOT bypass the Lean kernel — every final constant is still checked by the kernel and external replayers. Because Lean v4.33.1 predates v4.34.1 runtime soundness fixes (#15241, #15289), independent non-Lean-runtime kernels (Rust nanoda, con-leche) close this vulnerability class." },
        { tag: "M", head: "RE analogy: inline assembly / unchecked cast", text: "Think of kexactB as an unsafe cast that skips the frontend type-checker to avoid elaborator heartbeat blowups, relying 100% on the hardware MMU (the independent kernel verifier) to catch invalid states." },
        { tag: "M", head: "Where this analogy breaks", text: "In a sound theorem prover, skipping the elaborator cannot forge a theorem if the independent kernel checks out — its real operational risk is build-time code execution during lake build (which must be sandboxed)." }
      ],
      labs: [
        { title: "RH·MAP — Proof Threat Model & Kernel Replays", desc: "Review the full TCB threat model and multi-kernel verification matrix.", href: "../prototypes/concept_map_demo.html#node=kernel&lens=re" }
      ]
    },
    {
      match: function (name, info) {
        var flags = (info && info.module && info.module.forensic_flags) || [];
        return /DyadicPrimeIntervals|ChebyshevPrimeBounds\.SmallLoop|LamCopy|RingSpecNormalisedCharacterEq|IRRPrimeRecipSum|InvFiveLogLeSumInvPrimes|PrincipalizationCertificate/i.test(name) ||
          flags.indexOf("lean4lean_timeout") >= 0 || flags.indexOf("slow_con_leche") >= 0 || flags.indexOf("decide_kernel") >= 0;
      },
      title: "Kernel Compute / Replay Bottleneck (Profiler Hotspot)",
      blocks: [
        { tag: "L", head: "Two exact bottleneck mechanisms found by leanre", text: "1) Dependent HEq/subst tactic blowup: lam_copy (55.2s) and sigSpan_copy (40.3s, literally a 2-line tactic body!) call copy_cases h D D' on nested dependent structures (D7/CopyAll), generating huge kernel proof terms. 2) Kernel compute tables via decide +kernel: PI.PC.loop_run (35.1s) runs a 131,070-step trial-division sieve with a custom strictness thunk force; DyadicPrimeIntervals.Run1–4 shard a 131,070-step check (h = 2..131,072) using 362! (771 digits) into four chunks (Run1: 32,766 steps; Run2–4: 32,768 steps each); PrimeRecip.table_ok (17.2s) verifies a hardcoded prime witness table up to 16,900." },
        { tag: "C", head: "Checker logs as a CPU profiler", text: "Sutherland's lean4lean and con-leche logs pinpointed exactly these 5 timeout modules and 5 slowest declarations out of 175,187 files." },
        { tag: "M", head: "RE analogy: kernel profiler flamegraph", text: "Even without reading the math, runtime hotspots reveal where the AI switched from abstract reasoning to brute-force kernel computation or massive mechanical term duplication." },
        { tag: "M", head: "Where this analogy breaks", text: "Slow checking time does NOT imply a lemma is mathematically deep — often the slowest declarations are mechanical boilerplate or finite numerical checks." }
      ],
      labs: []
    },
    {
      match: function (name, info) { return (info && info.entity_kind === "tcb") || /riemannZeta|RiemannHypothesis|DirichletCharacter\.LFunction|HurwitzZeta|completedRiemannZeta/i.test(name); },
      title: "Semantic TCB — Mathlib Definitions You Must Trust (Layer 2)",
      blocks: [
        { tag: "L", head: "Inside challenge.ndjson (51,692 declarations)", text: "Streaming Sutherland's challenge.ndjson.zst (6,495,712 NDJSON lines) yields 51,692 declaration records: 40,431 theorems (78.22%, kernel-checked) and 11,261 non-theorem definitions/inductives/opaques/quots/axioms (21.78%). Following pure definition-to-definition edges shrinks the semantic reading surface to 2,570 definitions (5.0% of challenge). riemannHypothesis reaches 51,215 decls (+2 for riemannZeta_eq_zero_re / RiemannZetaZerosOnLine); adding all 3 Dirichlet GRH theorems adds just 470 declarations (DirichletCharacter.LFunction → ZMod.LFunction → HurwitzZeta), totaling 51,687 reachable + 5 unreachable export primitives = 51,692. sorryAx has fan-in 5 exclusively on Challenge.lean proof value stubs, 0 in statement types." },
        { tag: "S", head: "What makes a definition trustworthy?", text: "No proof assistant can formally prove that Mathlib's riemannZeta matches Bernhard Riemann's 1859 paper. Humans validate definitions via 'known-answer theorems' proved in Mathlib: Euler product / Dirichlet series for Re(s) > 1, analytic continuation, pole at s = 1, and functional equation." },
        { tag: "M", head: "RE analogy: auditing the trusted computing base", text: "Filtering out the 40,431 theorems and tracing pure def-to-def dependencies shrinks the human-trust surface by 95%, focusing auditors on core definitions (riemannZeta, HurwitzZeta, DirichletCharacter.LFunction, Complex, Real)." },
        { tag: "M", head: "Where this analogy breaks", text: "Even 2,570 definitions span Mathlib's measure theory, Mellin transforms, and complex analysis — still a real library audit, though vastly smaller than 17.37M lines." }
      ],
      labs: [
        { title: "RH·MAP — The 1-Line Formal Spec", desc: "Compare Mathlib's RiemannHypothesis definition against the classical statement.", href: "../prototypes/concept_map_demo.html#node=rhdef&lens=lean" }
      ]
    },
    {
      match: function (name) { return name.indexOf("AbelianVarietyTheory") >= 0; },
      title: "Namespace Misnomer Alert: Development/AbelianVarietyTheory",
      blocks: [
        { tag: "L", head: "The largest directory in the proof (~99,187 files)", text: "Over 56% of all files in the archive sit under Development/AbelianVarietyTheory. Real leanre namespace inspection confirms that the declarations declared INSIDE these files predominantly live in unrelated namespaces (GlobalTheory.LocGL, representation theory, theta-chain specs, even PrimeRecip prime tables!)." },
        { tag: "C", head: "Why directory names cannot be trusted", text: "Both jae-63 and drew2apps warned that folder names in this AI-generated codebase do not match contents. Always classify modules by their actual declaration signatures, Mathlib imports, and Horn contracts — never by file path." },
        { tag: "M", head: "RE analogy: misleading debug symbols in a stripped binary", text: "Like encountering functions named render_ui() inside a malware binary that actually implement RC4 decryption. Treat directory names as untrusted hints and trust the call/declaration graph." },
        { tag: "M", head: "Where this analogy breaks", text: "The mislabeling here is almost certainly an artifact of organic AI-assisted iterative development (reusing a scratch directory tree as the proof evolved), not adversarial obfuscation." }
      ],
      labs: []
    }
  ];

  function lookup(name, info) {
    for (var i = 0; i < ENTRIES.length; i++) {
      if (ENTRIES[i].match(name || "", info)) {
        return ENTRIES[i];
      }
    }
    return null;
  }

  return {
    PROVENANCE: PROVENANCE,
    lookup: lookup
  };
})();
