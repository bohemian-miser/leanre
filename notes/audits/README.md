# Blind Audit Rounds Ledger (`notes/audits/`)

This directory stores PR-extensible **Blind Alternatives-First Reconstruction** audit rounds in the `leanre.audits/1` schema (see [`docs/LEAN_SLOPSCORE.md`](../../docs/LEAN_SLOPSCORE.md)).

## Contributing an Audit Round

To avoid merge conflicts, add a standalone JSON file under `notes/audits/contrib/<author>__<slug>.json` containing either a single round object or `{"schema": "leanre.audits/1", "rounds": [...]}`:

```json
{
  "id": "round-002-theta-kernel",
  "round": 2,
  "project": "riemann-hypothesis-cleanup",
  "target": "Development/PillarA/ThetaKernel",
  "author": "@your-handle",
  "date": "2026-11-26",
  "summary": "Blind reconstruction compared against current cleanup HEAD; identified 3 redundant local instances and a 12-field bundle replaceable by Mathlib structures.",
  "static_slop": 54.2,
  "blind_slop": 48.0
}
```

### Rules
- Required non-empty string fields: `id` (globally unique), `project`, `target`, `author`, `date` (`YYYY-MM-DD`), `summary`.
- Optional numeric scores `static_slop` and `blind_slop` must lie in `0..100`.
- **Never** paste verbatim third-party Lean proof bodies or unlicensed prose; link to pinned commit SHAs instead.
- Validate locally before opening a PR:

```bash
python3 leanre/leanre.py slop audits --dir notes/audits
```
