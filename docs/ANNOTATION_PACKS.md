# Annotation packs (`leanre.annot/1`)

Portable, git-backed symbol renames, aliases and notes for `leanre`, with mandatory provenance.
A pack is a plain `.jsonl` file you can commit, diff, review in a PR and merge. There is no server
state: `annotations/` in this repository *is* the database.

Implementation: `leanre/annot.py` (stdlib only). Tests: `leanre/test_annot.py`. Gates: A1–A3 in
`docs/PHASE3_GATES.md`. Signature hashes: `docs/SIGHASH.md` (owned by `leanre/sighash.py`; this
module treats them as opaque strings and never computes them).

> Annotations describe the *artifact* (names, structure, where things live). A pack never upgrades a
> claim: kernel acceptance of a declaration (Layer 1) says nothing about semantic fidelity, human
> comprehension or mathematical consensus (Guardrail 1), and an annotation cannot say otherwise
> without a provenance tag that shows where the statement comes from.

## 1. File format

UTF-8, LF line endings, no BOM, final newline. One JSON object per line. Every line is the
**canonical encoding** of its object:

```python
json.dumps(obj, sort_keys=True, ensure_ascii=False, separators=(",", ":"), allow_nan=False)
```

Line order is fixed, so two exports of the same content are byte-identical and a PR diff shows
exactly the records that changed:

1. the header `{"schema":"leanre.annot/1","type":"pack"}`;
2. `layer` lines, sorted by layer id;
3. `annot` lines, sorted by `(target, name, sighash, layer, slot)` (missing = empty string;
   plain code-point order).

Optional fields are **omitted** when empty (never `null`, `""`, `[]`, `{}` or `false`), so each
record has exactly one representation. Duplicate JSON keys, unknown fields and unknown line types
are errors.

### Layer line

| field | req | meaning |
|---|---|---|
| `type` | yes | `"layer"` |
| `layer` | yes | id: 1–4 segments of `[a-z0-9][a-z0-9._-]*` joined by `/`, e.g. `human/canonical-facts`, `ai/flirt-tier3` |
| `kind` | yes | `"human"` or `"ai-draft"` |
| `default_on` | yes | whether the layer is shown before the user chooses. Must be `false` for `ai-draft` |
| `title` | yes | short display title |
| `description` | no | free text |

### Annotation line

| field | req | meaning |
|---|---|---|
| `type` | yes | `"annot"` |
| `target` | yes | `"decl"` (declaration name), `"module"`, `"folder"` (dotted module-path prefix) or `"namespace"` (declared Lean namespace) |
| `name` | yes | the anchored name, exactly as in the graph |
| `sighash` | no | primary normalized signature hash per `docs/SIGHASH.md` v1 (`^(k1n\|k1a\|s1n\|s1t\|s1a):[0-9a-f]{32}$`; `k1n` when a kernel export exists, else `s1n`); `decl` only |
| `alt_sighash` | no | further hashes of the same declaration in other schemes (e.g. `k1a`, `s1n`); needs `sighash`. When an `…a` scheme is stored, record its `lexicon_id` in `extra` (`docs/SIGHASH.md` §4–§5) |
| `slot` | no | lets one layer hold several notes on one declaration (`[a-z0-9._-]+`) |
| `layer` | yes | id of a layer declared in the same pack |
| `rename` | * | display name to show instead of `name` |
| `aliases` | * | extra search/display names (sorted, unique) |
| `note` | * | free text, at most 2,000 characters |
| `tag` | yes | provenance: `L`, `A`, `C`, `S` or `M` (stored without brackets, shown as `[L]`) |
| `source` | yes | citation backing the tag (see §2) |
| `breaks` | iff `M` | "where this analogy/heuristic breaks" |
| `author` | yes | who wrote it; `ai:<model>` for model output |
| `draft` | iff ai-draft | `true` on every record of an `ai-draft` layer, absent elsewhere |
| `created`, `updated` | yes | UTC `YYYY-MM-DDTHH:MM:SSZ`, `updated >= created` |
| `was` | no | previous anchor names, added when a record follows a rename (§5) |
| `extra` | no | free JSON object for tool metadata (model, confidence, cluster id, prompt hash, …) |

\* at least one of `rename` / `aliases` / `note` is required.

**Record key** = `(layer, target, name, sighash, slot)`. Two records with the same key and
different content are a *conflict* (§4). `annot.record_id(rec)` is a 16-hex digest of the key for
URLs and UI ids; it is derived, never stored.

The 2,000-character cap on notes is deliberate: packs carry identifiers, counts and short
remarks, not proof source. The upstream archive has no license; do not paste `.lean` text into
notes (Guardrail 3).

### Example

The lines below are a **synthetic illustration of the format** (invented names and hashes, not
extracted telemetry):

```json
{"schema":"leanre.annot/1","type":"pack"}
{"default_on":false,"kind":"ai-draft","layer":"ai/example-drafts","title":"Example drafts","type":"layer"}
{"default_on":true,"kind":"human","layer":"human/example","title":"Example notes","type":"layer"}
{"author":"ai:example-model","breaks":"Label guessed from type tokens only; nobody has read the proof.","created":"2026-11-22T03:00:00Z","draft":true,"extra":{"blinded":true,"confidence":0.4},"layer":"ai/example-drafts","name":"Example.lemma_17","rename":"commutativity_helper","sighash":"k1n:00112233445566778899aabbccddeeff","source":"synthetic example","tag":"M","target":"decl","type":"annot","updated":"2026-11-22T03:00:00Z"}
{"author":"example-reviewer","created":"2026-11-22T03:00:00Z","layer":"human/example","name":"Example.lemma_17","note":"Stated in Example/Basic.lean.","sighash":"k1n:00112233445566778899aabbccddeeff","source":"synthetic example","tag":"L","target":"decl","type":"annot","updated":"2026-11-22T03:00:00Z"}
```

## 2. Provenance (Guardrail 2)

Every annotation carries one tag and a non-empty `source`. The validator enforces presence and
shape; it cannot check that a citation is *true* — that is what review of the PR is for.

| tag | meaning | `source` should contain |
|---|---|---|
| `L` | extracted by us from the pinned Lean source / kernel export | file or export, declaration, commit or SHA-256 |
| `A` | asserted in Alpöge's `remark.pdf`, not independently traced | section/page; Footnote 4's caveat applies |
| `C` | third-party verifier / community report, not executed by us | who, where |
| `S` | standard published mathematics | named theorem + year / reference |
| `M` | CS/RE analogy or heuristic label | what it is based on — **and** a `breaks` note |

An explanation of *how* one theorem implies another that cannot cite `L`/`A`/`C`/`S` does not
belong in a pack.

## 3. Layers

Layers are independent overlays. Turning one on or off never changes a file; it only changes what
`annot.view(pack, enabled)` returns.

* `human` layers hold curated, reviewed content.
* `ai-draft` layers hold model output (FLIRT Tier 3 labels). The format makes it impossible for a
  draft to pass as a fact:
  * `default_on` must be `false`; `annot.default_layers()` never returns an `ai-draft` layer, so
    drafts appear only when a caller lists the layer explicitly;
  * every record carries `"draft": true` in the file itself, has an `ai:<model>` author and may
    only use tag `M` (so it always has a `breaks` note);
  * an `ai:*` author is rejected in a `human` layer, and a merge can never change a layer's kind.
* `view()` marks every annotation with `draft` and `display_tag`. Human renames always outrank
  draft renames; among layers of the same class the order of `enabled` decides. If enabled layers
  of the winning class disagree on a rename, the entry gets `rename_conflict: true` and the
  candidates are listed in `conflicts` — one is shown, none is hidden.
* `annot.promote(pack, id, to_layer, author=, tag=, source=, now=)` is how a person adopts a
  draft: it copies the record into a human layer under that person's own author and provenance
  (recording `extra.promoted_from`). The draft stays where it was.

On disk, `annotations/` holds **one file per layer**: `<layer id with "/" replaced by "__">.jsonl`
(`human/canonical-facts` → `annotations/human__canonical-facts.jsonl`). File names are derived
only from validated layer ids. `annot.PackStore` is the read/write API for that directory.

## 4. Merge, import, conflicts

`annot.merge(ours, theirs, resolve=None)` returns
`{pack, added, identical, conflicts, resolved, layers_added, ok}`. Nothing is overwritten silently:

* same key, same content → `identical`;
* new key → `added`;
* same key, different content → a `conflicts` entry with both versions and the differing `fields`
  (`kind` is `content`, or `timestamp_only` when only timestamps differ); **ours is kept**;
* same layer id, different definition → `kind: "layer"`; a record that is illegal under our
  definition of its layer → `kind: "invalid_here"`.

A conflict is settled only by an explicit `resolve={id: "ours" | "theirs"}`.
`PackStore.import_text(text, resolve=None, dry_run=False)` applies the same rule to the directory
and **writes nothing while any conflict is unresolved**; an invalid pack is rejected whole.
`PackStore.upsert(fields, expect_updated=…)` uses optimistic locking: creating an existing key, or
editing with a stale `expect_updated`, raises `ConflictError`.

For git: because packs are sorted with one record per line, independent additions merge cleanly.
If two branches edit the same record, git leaves conflict markers and `validate` reports them
(`git_conflict_marker`) instead of letting a broken pack load.

## 5. Anchoring and re-anchoring (gate A1)

An annotation on a declaration is anchored by its **name** and its **normalized signature hash**.
The hash covers the statement (type) only — not the proof, not the declaration's own name, not
binder or universe names (`docs/SIGHASH.md`). Therefore:

* the proof is simplified or replaced → name and hash unchanged → still an exact hit;
* the declaration is renamed, statement unchanged → the hash finds it under its new name.

Hashes of different schemes (kernel `k1n`/`k1a`, source `s1n`/…) are different spaces and are
never compared with each other.

`annot.reanchor(pack, graph)` reports, per record, against a `GraphIndex`
(`{name: hashes}` from any source: `GraphIndex.from_kernel_db`, `.from_sqlite`, `.from_tsv`, or a dict):

| status | meaning |
|---|---|
| `exact` | name present and the primary hash matches (or an `alt_sighash` matches when the graph has no hash of the primary's scheme) |
| `name_only` | name present, not confirmed by hash. `reason`: `signature_changed`, `unhashed_annotation`, `unhashed_graph`, `no_common_scheme`, or `non_decl_target` (modules, folders and namespaces anchor by name only) |
| `hash_only` | name gone, a recorded hash exists under other name(s): `candidates`, `unique`, and `resolved_name` when there is exactly one |
| `orphan` | neither name nor hash found |
| `unchecked` | the graph supplies no name table for this target type; nothing is claimed |

Limits, stated plainly:

* A signature hash is not unique. Many declarations can share a statement shape (the corpus has
  large clone clusters), so `hash_only` can be ambiguous; then all candidates are listed and
  nothing is resolved automatically.
* `hash_only` shows that a declaration with the same normalized statement exists under another
  name. It is evidence of a rename, not proof that the note still applies — the report is for a
  person to read.
* A match through a name-abstracted hash (`k1a`) is weaker than through the primary hash and is
  flagged `via_primary: false`.

`annot.rebind(pack, report, now=…)` applies the safe part of a report to a *copy*: unique
primary-hash renames are followed (old name kept in `was`), and missing hashes are filled in for
name hits. Changed signatures (`accept_signature_change=True`) and alt-hash renames
(`accept_alt_hash=True`) are opt-in; ambiguous and orphaned records are left alone and listed. A
re-keyed record that would collide with an existing one is reported, not overwritten.

## 6. Python API

```python
import annot                                    # with leanre/ on sys.path

pack, issues = annot.parse(text)                # never raises; issues = [{line, code, severity, msg}]
pack = annot.loads(text); pack = annot.load(path)          # raise annot.PackError(.issues)
text = annot.dumps(pack, layers=None); annot.dump(pack, path)
annot.validate_text(text, canonical=True) -> [issue]       # [] = valid AND canonical bytes
annot.merge(ours, theirs, resolve=None) -> dict
annot.diff(a, b) -> {added, removed, changed, layers_added, layers_removed, layers_changed, same}
annot.default_layers(pack) -> [layer id]        # never an ai-draft layer
annot.layer_table(pack, enabled=None) -> [{layer, kind, draft, default_on, enabled, title, description, count}]
annot.view(pack, enabled=None) -> {layers, enabled, targets, conflicts}
annot.promote(pack, id, to_layer, *, author, tag, source, now, breaks=None)
annot.GraphIndex(decls, names=None, label="", restrict_to=None)
annot.reanchor(pack, graph, layers=None) -> {graph, total, counts, entries}
annot.rebind(pack, report, *, now, accept_signature_change=False, fill_missing_hash=True, accept_alt_hash=False)

p = annot.Pack(); p.add_layer(id, kind, title, description="", default_on=None)
p.put(annot.make_annotation(name=, layer=, tag=, source=, author=, now=, sighash=None, alt_sighash=None,
                            target="decl", slot=None, rename=None, aliases=None, note=None,
                            breaks=None, draft=False, extra=None))

store = annot.PackStore("annotations")
store.load() -> (Pack, issues)        store.export_text(layers=None) -> str
store.ensure_layer(id, kind, title)   store.import_text(text, resolve=None, dry_run=False) -> report
store.upsert(fields, now=None, expect_updated=None) -> record + id
store.delete(id, expect_updated=...)  store.save(pack)
```

Errors: `annot.PackError` (validation; HTTP 400) and its subclass `annot.ConflictError`
(would overwrite; HTTP 409). Both carry `.issues`.

## 7. CLI

`annot.register_cli(subparsers)` adds the `annot` subcommand to the `leanre` CLI
(dispatch: `args.annot_func(args)` → exit code). It also runs standalone:

```bash
python3 leanre/annot.py validate annotations/            # exit 1 on any issue (CI check)
python3 leanre/annot.py layers annotations/              # on/off, DRAFT marker, counts
python3 leanre/annot.py export annotations/ -o all.jsonl [--layer human/canonical-facts]
python3 leanre/annot.py import theirs.jsonl --into annotations/ [--dry-run] [--resolve ID=theirs]   # exit 2 on conflicts
python3 leanre/annot.py merge a.jsonl b.jsonl -o merged.jsonl                                      # exit 2 on conflicts
python3 leanre/annot.py diff a.jsonl b.jsonl             # exit 1 when different
python3 leanre/annot.py reanchor annotations/ --kernel-db outputs/kernel/kernel.db \
        [--leanre-db outputs/leanre.db] [--summary] [--rebind-out rebound.jsonl]
```

## 8. Committed packs

* `annotations/human__canonical-facts.jsonl` — small human-layer example pack. Every note
  transcribes a canonical fact already audited in `HANDOFF.md` §3 (item 4) and is tagged `[L]`
  with the pinned commit or SHA-256; it adds no new claim. It was transcribed by the Phase 3
  annotation worker (see its `author` field), not hand-written by a person. Regenerate with
  `python3 annotations/tools/make_seed.py` (uses current UTC time; pass `--now <UTC>` to reproduce
  a specific timestamp).
* `annotations/ai__decomp-phase4.jsonl` — AI-draft overlay layer (`kind: "ai-draft"`,
  `default_on: false`, `draft: true`, `tag: "M"`, `author: "ai:leanre-phase4-swarm"`) synthesized
  from the top `READ`/`PARTIAL` landmark nodes across the 6 Phase 4 `outputs/decomp/*.json`
  files, anchored to exact `k1n` sighashes from `outputs/kernel/kernel.db`. Off by default; every
  record carries an explicit `breaks` caveat. Regenerate with
  `python3 annotations/tools/make_decomp_pack.py`.
