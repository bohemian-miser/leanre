# SIGHASH v1 — normalized signature hashes for Lean 4 declarations

Status: **frozen v1** (2026-11-22). Reference implementation: `leanre/sighash.py`
(stdlib only). Tests: `leanre/test_flirt_sighash.py`. Any change to a byte layout or a
normalization rule below needs a new scheme id (`k2n`, `s2n`, …); v1 digests are never
redefined.

Used by: FLIRT Tier 2 (`leanre/flirt/tier2*`), the kernel extractor
(`leanre/kernel-rs`, columns `sighash` / `sighash_anon`), annotation packs
(`docs/ANNOTATION_PACKS.md`, key = declaration name + sighash).

## 0. What a sighash is — and is not

A sighash identifies the **statement** (type / signature) of a declaration:

| changes that must NOT change the hash | where it is guaranteed |
|---|---|
| proof term / definition body / tactic script | the value is never an input |
| the declaration's own name, the file it lives in | never an input; `_private.<module>.0.` stripped (N1) |
| bound-variable names (alpha-renaming) | kernel: de Bruijn; source: rule S5 |
| binder kind `( )` / `{ }` / `[ ]` / `⦃ ⦄` | dropped in both forms |
| universe-parameter names and their declaration order | renumbered by first occurrence (K3 / S6) |
| whitespace, comments, attributes, modifiers | source: S1 |

Limits, stated plainly:

* It is a hash of a statement, **not a proof of mathematical equivalence**. Two
  statements that are logically equivalent but written differently (hypotheses
  reordered, `a ≤ b` vs `b ≥ a`, a definition unfolded) hash differently.
* Equal hashes mean "same normalized statement", which for a `def` only means "same
  type": every `ℕ → ℕ` function shares one hash. Consumers must use `sig_size` /
  `n_tokens` to discard low-information signatures.
* **Kernel and source hashes live in different spaces and are never compared.** The
  source form has no elaborator: implicit arguments, instances, notation and name
  resolution are invisible to it. The kernel form is exact [L]; the source form is a
  deterministic approximation whose precision and recall must be *measured* (gate F2),
  not assumed.

## 1. Schemes and string format

```
<scheme>:<32 lowercase hex>          digest = SHA-256(...) truncated to 16 bytes
regex: ^(k1n|k1a|s1n|s1t|s1a):[0-9a-f]{32}$
```

| scheme | space | constants / identifiers |
|---|---|---|
| `k1n` | kernel | every constant by its (N1-normalized) full name |
| `k1a` | kernel | as `k1n`, but project-local constants → positional placeholders |
| `s1n` | source | identifiers exactly as written |
| `s1t` | source | free identifiers reduced to their last dot-component (`Nat.Prime` → `Prime`) |
| `s1a` | source | as `s1t`, but project-local identifiers → positional placeholders |

Invariants: `k1a` digest = `k1n` digest iff no project-local constant occurs;
`s1a` digest = `s1t` digest iff no identifier resolves to a project-local name.
`k1n` and `s1n` never depend on a lexicon.

`H(x)` below is `SHA-256(x)[0:16]` (16 raw bytes). `‖` is byte concatenation.
`dec(n)` is the ASCII decimal of a natural number. Single quoted letters are one ASCII byte.

## 2. Kernel form (`k1n`, `k1a`)

Input: the type expression of a constant in a lean4export NDJSON stream (format 3.x):
hash-consed `ie` expression records, `il` level records, `in` name records.

### K1 — Merkle node hashes

The hash is defined by structural recursion, so it is a function of the *tree* but is
computed in time linear in the *DAG* (memoize per expression id). It must never be
computed from a printed term.

Levels (level id 0 is `zero`):

| level | hash |
|---|---|
| zero | `H('z')` |
| succ l | `H('s' ‖ h(l))` |
| max a b | `H('m' ‖ h(a) ‖ h(b))` |
| imax a b | `H('i' ‖ h(a) ‖ h(b))` |
| param p | `H('p' ‖ dec(index(p)))` — index per K3 |

No algebraic level normalization is applied (`max u v` ≠ `max v u`).

Expressions:

| expr | hash |
|---|---|
| bvar i | `H('v' ‖ dec(i))` |
| sort l | `H('S' ‖ h(l))` |
| const c us | `H('C' ‖ nameref(c) ‖ H('u' ‖ h(us₁) ‖ … ‖ h(usₙ)))` (n = 0 → `H('u')`) |
| app f a | `H('A' ‖ h(f) ‖ h(a))` |
| lam (type t) (body b) | `H('F' ‖ h(t) ‖ h(b))` |
| forallE (type t) (body b) | `H('P' ‖ h(t) ‖ h(b))` |
| letE (type t) (value v) (body b) | `H('T' ‖ h(t) ‖ h(v) ‖ h(b))` |
| proj typeName idx struct | `H('J' ‖ nameref(typeName) ‖ h(struct) ‖ dec(idx))` |
| natVal n | `H('N' ‖ decimal string as exported)` |
| strVal s | `H('X' ‖ UTF-8 bytes of s)` |
| mdata _ e | `h(e)` (transparent) |

Binder names, `binderInfo` and `letE.nondep` are not inputs.

### K2 — `nameref`

Name rendering: components joined with `.`, numeric components in decimal, string
components verbatim (same as `leanre/ndjson.py`).

* **N1**: if the first component is `_private`, drop everything up to and including the
  first component `0` (`_private.A.B.0.Ns.x` → `Ns.x`), provided something remains.
* self reference: if `c` is the j-th inductive type (0-based, record order of `types`) of
  the constant's own inductive record → `H('r' ‖ dec(j))` — in **both** variants.
* `k1a` only: if `c` is project-local (§4) → `H('l' ‖ dec(i))`, `i` = K3 index.
* otherwise → `H('n' ‖ UTF-8(N1(c)))`.

### K3 — numbering (universe parameters and local constants)

One pre-order depth-first walk over the constant's root expression(s), visiting each
DAG node once (a node already visited is skipped — this yields exactly the
first-occurrence order of the tree). Child order: `app` fn, arg · `lam`/`forallE` type,
body · `letE` type, value, body · `proj` typeName then struct · `const` name then `us`
left to right · `sort` its level · `succ` child · `max`/`imax` left, right · `mdata`
inner. Each distinct universe parameter gets the next index (from 0) at first visit;
each distinct project-local constant (after N1 they are still distinct *names*; a self
reference is never numbered) gets the next local index at first visit. Numbering is
per constant, never global, and is independent of the `levelParams` list.

Implementation note (not normative): subtrees with no universe parameter and no local
constant are numbering-free and their digest can be memoized globally per expr id; all
other nodes need a per-constant memo.

### K4 — per-constant signature

| constant | digest | roots for K3 |
|---|---|---|
| `thm`, `def`, `opaque`, `axiom`, `quot` | `h(type)` | `[type]` |
| constructor, recursor | `h(type)` (with self references of its record) | `[type]` |
| inductive type `T` | `H('I' ‖ h(T.type) ‖ H('c' ‖ h(ctor₀.type) ‖ … ‖ h(ctorₖ.type)))`, constructors of `T` in `cidx` order | `[T.type, ctor₀.type, …]` (one shared numbering) |

So a structure's sighash covers its field types, and renaming the structure does not
change it. Recursors are derived and not part of the inductive digest.

Emitted next to the digest:

* `sig_size` — number of expression nodes of the hashed root(s) **as a tree** (levels
  and `mdata` not counted), saturating at 4294967295.
* `n_local` — number of distinct project-local constants (0 for `k1n`-only runs).

### Test vectors (kernel)

`python3 leanre/sighash.py kernel data/challenge.ndjson.zst` over Sutherland's
`challenge.ndjson.zst` (SHA-256 `c24ef99d…8ac6`) [L]:

| constant | role | k1n digest | sig_size |
|---|---|---|---|
| `Eq` | ind | `9b6f06f8db5118e2bdbc908c372d83af` | 18 |
| `Eq.refl` | ctor | `c64be5b2f9642b213b07820357c25edf` | 11 |
| `Nat` | ind | `b71e7069cc04ceee2c16b081df8a6912` | 5 |
| `Nat.rec` | rec | `b033a24af52fc76a9076abff377f06fa` | 25 |
| `Quot.lift` | quot | `7319a02be17c4b1921caf748dedb246f` | 43 |
| `propext` | axiom | `111a97953c49c42b90a0cea7496a8cb0` | 17 |
| `Nat.add_comm` | thm | `8711a40244dde9448f1d7b24ba5c44d2` | 43 |
| `riemannZeta` | def | `9d494be70e55e434e5550ff3fa70c921` | 3 |
| `DirichletCharacter.LFunction` | def | `76ce4556e798490a83365382cd50fc47` | 37 |
| `riemannHypothesis` | thm | `e67d3cf7e6fa39c3480c359052fb059f` | 1 |

Whole-file regression: the TSV `name \t role \t k1n \t k1a \t sig_size \t n_local \n`,
one line per constant in export order (inductive record: types, then ctors, then recs,
each in record order):

| run | constants | SHA-256 of the TSV |
|---|---|---|
| no lexicon | 53,722 | `1c0b8c380ae14e89398f4837fdcd77df1716b1ee1fb2d54d68197848e1e1767e` |
| lexicon `294e04cd1ef65e37` | 53,722 | `720e1df87e3e300d4437ec294b966d655fa14ebc7935ff9eca43186781f6deb1` |

With the lexicon exactly 4 of the 53,722 constants have `k1a ≠ k1n` (the four headline
theorems whose type mentions a project definition from `Statements`), e.g.
`LFunction_eq_zero_re` k1n `95410a95…cb6d`, k1a `aa3e662b…fbed`.

Sanity observation [L]: among the 40,431 theorems of that export there are 36,819
distinct `k1n`; collisions are genuine restatements such as `congrArg` / `congr_arg`,
`Nat.zero_lt_succ` / `Nat.succ_pos`, `Nat.succ_sub_succ_eq_sub` / `Nat.succ_sub_succ`.

## 3. Source form (`s1n`, `s1t`, `s1a`)

Input: an ordered list of binder groups (auto-included `variable` binders first, then
the declaration's own) and the result-type text. API:

```python
sighash.source_sig(binders: list[str | list[str]], type: str | list[str], resolve=None) -> dict
sighash.source_hash(binders, type, resolve=None) -> (s1n, s1a, n_tokens)
sighash.source_hash_header("theorem foo (a : ℕ) : a + 0 = a := …") -> dict   # splits for you
sighash.source_decl_hashes(file_text, lexicon=None) -> iterator                # whole file
```

The digest is `H(UTF-8(" ".join(tokens)))` of the canonical token stream built by:

* **S1 lexing.** Strip `--` and nested `/- -/` comments. Tokens: string literals,
  identifiers (dotted, `«»`-quoted, Unicode letters, digits/subscripts, `'`, `!`, `?`),
  numerals, the ASCII operators `:= <-> -> => <= >= != :: ++ && || |>. |> <| .. //`,
  and every other non-space character on its own. Letter-like postfix notations
  `ˣ ᵀ ᴴ ᵒ ᵖ ᵐ ᵃ ᵈ ᶜ ᵛ ᶠ` are split off identifiers. Whitespace is not a token.
* **S2 notation.** `->`→`→`, `<->`→`↔`, `<=`→`≤`, `>=`→`≥`, `!=`→`≠`, `=>`→`↦`,
  `λ`→`fun`, `forall`/`Π`→`∀`, `exists`→`∃`, `ℕ ℤ ℚ ℝ ℂ`→`Nat Int Rat Real Complex`.
* **S3 binders.** Each group is expanded to one entry per bound name: `(a b : T)` →
  `(a : T) (b : T)`; `[C α]` → anonymous entry of type `C α`; `{α}` → entry without
  type. The bracket kind is dropped, and so is a default value / auto-param
  (`(h : P := by tac)` → `(h : P)`; the kernel form keeps `optParam`/`autoParam`).
* **S4 telescope normal form.** While the result type starts with `∀ binders,` the
  binders are moved into the entry list (`∀ x ∈ s,` becomes entry `x` plus an anonymous
  entry `x ∈ s`); while it has a top-level `A → rest` (no top-level `↔`, `↦`, `,`,
  `<|` and no binder-like prefix `∀ ∃ fun ∑ ∏ ∫ ⨆ ⨅ ⋃ ⋂ Σ … if let have show match`
  before the arrow) `A` becomes an anonymous entry; `(x : A) → rest` becomes a named
  entry. Redundant outer parentheses are removed. Hence
  `theorem t (a : ℕ) (h : P a) : Q a` ≡ `theorem t : ∀ a : ℕ, P a → Q a`.
* **S5 bound names.** Binding sites are the telescope names and, inside terms, the
  variables of `∀ ∃ fun ∑ ∏ ∫ ⨆ ⨅ ⋃ ⋂ Σ …` up to their `,`/`↦`, set-builder /
  subtype braces `{x | …}` `{x : T // …}`, and `(x : A) →` / `(x : A) ×` groups. A
  telescope name never referenced later is printed `_`. Every other binding site gets
  a fresh index in stream order and is printed `#k`; a reference `x` or `x.f` resolves
  to the **latest preceding** site of `x` and is printed `#k` / `#k.f`. (Scopes are not
  parsed: reusing a name in sibling scopes is handled, a reference to an outer variable
  after an inner shadowing of the same name is not.)
* **S6 universes.** Identifiers directly after `Type` / `Sort` (or inside the
  parenthesis following them) and inside `.{…}` are universe names, printed `u#k` by
  first occurrence.
* **S7 free identifiers.** `s1n`: as written. `s1t`: last dot-component. `s1a`: if
  `resolve(identifier)` returns a project-local name (§4, rule L2) print `L#k` (k by
  first occurrence of the resolved name), else the last dot-component.
* Stream layout: for each entry `(` name [`:` type tokens] `)`, then `:` and the result
  tokens if a result type exists.

Also returned: `n_tokens`, `n_binders`, `n_local`, and the three token lists (for
fuzzy / shingle matching in Tier 2).

Not covered by the source form (v1): structure fields and inductive constructors
(only parameters and the stated sort are hashed), `open`/namespace-relative name
resolution for `s1n`, notation defined by the project, implicit `autoImplicit` binders.

**V1 — `variable` auto-inclusion** (`iter_source_decls`): a non-instance `variable`
is included when its name is mentioned in the header, or in the type of an included
variable (fixpoint); an instance / anonymous variable is included when every variable
it mentions is included. Header-only, matching Lean ≥ 4.12 behaviour for theorems.

### Test vectors (source)

| header (synthetic) | canonical `s1n` stream | `s1n` |
|---|---|---|
| `theorem foo (a b : ℕ) (h : a ≤ b) : a + 0 = a` | `( #0 : Nat ) ( #1 : Nat ) ( _ : #0 ≤ #1 ) : #0 + 0 = #0` | `s1n:05be2e992a40935f9fe815a81e3f2d3e` |
| `theorem bar : ∀ (x y : Nat), x <= y -> x + 0 = x` | identical | identical |

## 4. "Project-local" and the lexicon

`k1a` / `s1a` abstract the names a project defines itself, so that a statement about
`ProjA.myBound` can match the same statement about `ProjB.theirBound`. Library
(Lean core, Std, Batteries, Mathlib) names are never abstracted.

A **lexicon** is the set of fully-qualified names a project declares, obtained from a
source scan (`sighash.build_lexicon`, column-0 commands, correct
`namespace`/`section`/`end`/`_root_` scoping, named declarations only). File format:
UTF-8, one name per line, sorted by code point, LF-terminated. `lexicon_id` = first 16
hex of the SHA-256 of the file. A digest of an `…a` scheme is only meaningful together
with its `lexicon_id`; store it in the table's metadata.

* **L1 (kernel).** `c` is local iff `N1(c)` is in the lexicon, or a proper dot-prefix of
  `N1(c)` is (auxiliaries: `x._proof_1`, `S.mk`, `S.rec`, `x.match_1`, `x.eq_1`).
* **L2 (source).** identifier `t` written in namespace `ns` with opens `O` is local iff
  `P.t'` is in the lexicon for some non-empty dot-prefix `t'` of `t` (longest first)
  and some `P` ∈ {"", prefixes of `ns`, `o`, `prefix(ns).o` for `o` ∈ `O`}.

Known under-approximations (they cost recall, never determinism): auto-named
instances (`instFooBar`) and declarations emitted by metaprograms have no source name
and are treated as library constants.

Pinned lexicon for `Deicyde/riemann-hypothesis@40e56bab` (175,187 `.lean` files) [L]:

```
python3 leanre/sighash.py build-lexicon --src data/rh_mirror/src \
    --out outputs/flirt/cache/lexicon_rh.txt --workers 24 --expect-files 175187
# files=175187 names=1051704 lexicon_id=294e04cd1ef65e37
# sha256=294e04cd1ef65e37097f72e3ef3f30abf29e69eb1de50c0f8875a6b29aeaa43a
```

(The file lists identifiers only; it is gitignored under `outputs/flirt/cache/` and is
rebuilt in ~8 s.) Note for consumers of `outputs/leanre.db`: its Phase 2
`declarations.name` pops a namespace on every anonymous `end`, so 63,893 of its
1,050,792 distinct names differ from this lexicon; prefer the lexicon for alignment.

## 5. Using sighashes as keys

* **Annotation packs** store `sighash` = the `k1n` string when a kernel export exists
  for the corpus, else the `s1n` string. Re-anchoring order: (name, sighash) exact →
  unique sighash under another name (rename) → name only (statement changed; flag for
  review). `k1a` / `s1a` may be stored in `extra` as a weaker fallback and must carry
  `lexicon_id`.
* **Tier 2** compares `s1n`, then `s1t`, then `s1a` between corpora (source space), and
  `k1n` / `k1a` between constants of the same export (kernel space), and reports which
  scheme produced each match. Signatures with small `n_tokens` / `sig_size` are
  low-information and must be thresholded by measured false-positive rate.
* A match is evidence that two declarations *state* the same thing in the same words.
  It is never, by itself, a claim about the mathematics [M: the FLIRT analogy — a
  byte-pattern hit names a library function; it breaks here because equal statements
  do not imply equal definitions underneath when local names were abstracted].

## 6. Reproduce

```
python3 -m unittest leanre/test_flirt_sighash.py -v            # 22 tests + 1 opt-in
LEANRE_SLOW=1 python3 -m unittest leanre/test_flirt_sighash.py  # + challenge TSV SHA (≈30 s)
python3 leanre/sighash.py kernel data/challenge.ndjson.zst --grep Nat.add_comm
python3 leanre/sighash.py source "theorem foo (a b : ℕ) (h : a ≤ b) : a + 0 = a" --tokens
```
