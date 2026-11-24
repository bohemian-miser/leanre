# Project Review Notes (`notes/<slug>/`)

This directory holds **separately authored review notes** (human or AI-assisted)
for individual Lean 4 proofs in the `leanre` gallery. It is strictly separated
from the deterministic tool core.

## Trust Boundary: Core vs. Notes

| Layer | Examples | Provenance in `manifest.json` |
| --- | --- | --- |
| **Core (tool-generated)** | `manifest.json`, `data/summary.md`, `data/outline.json`, `data/module_matrix.json`, `data/embedding_2d.json`, `data/circuits/*.json`, `data/flirt_tier1.json`, `data/corpus_comparison.json` | Listed under `provenance.tool_generated` |
| **Notes (authored)** | `notes/<slug>/findings/*.md`, `notes/<slug>/dossiers/*.md`, `notes/<slug>/*.md`, `notes/<slug>/annotations/*.jsonl` | Recorded under `provenance.notes_layer` (`enabled: true`) |

Any repository exported **without** a `notes/<slug>/` directory produces only
deterministic tool output (`provenance.notes_layer.enabled = false`). Authored
prose never enters or impersonates the deterministic scanner, kernel extractor,
signature-matching (FLIRT) fingerprinting, embedding, or stylometry pipeline.

## Directory Layout

Each project's optional notes live under `notes/<slug>/`:

```text
notes/
  <slug>/
    findings/         # Optional short finding chapters (*.md)
    dossiers/         # Optional deep-dive review dossiers (*.md)
    *.md              # Top-level review dossiers (excluding README.md)
    annotations/      # Optional portable `leanre.annot/1` JSONL packs (*.jsonl)
```

## How to Attach Notes Safely

1. Create `notes/<slug>/` matching the project's gallery slug (for example,
   `notes/navier-stokes/` or `notes/navier-stokes-euler/`).
2. Add Markdown dossiers or findings using pinned upstream GitHub `#L<n>` links.
   Never paste multi-line raw `.lean` proof bodies from unlicensed repositories.
3. For structured symbol-level commentary, add `leanre.annot/1` packs under
   `notes/<slug>/annotations/*.jsonl` and validate them with:

   ```bash
   python3 -m leanre annot validate notes/<slug>/annotations/<pack>.jsonl
   ```

4. Build a single project or the full gallery with `--notes-dir` or
   `leanre_gallery.toml`:

   ```bash
   python3 -m leanre gallery add <src_dir> --out-dir site \
     --slug <slug> --title "<Title>" --notes-dir notes/<slug>

   python3 -m leanre publish --config leanre_gallery.toml --out-dir site
   ```
