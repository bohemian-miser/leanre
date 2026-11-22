#!/usr/bin/env python3
"""Build annotations/ai__decomp-phase4.jsonl from Phase 4 outputs/decomp/*.json + outputs/kernel/kernel.db.

Creates a canonical, schema-validated `leanre.annot/1` AI-draft overlay layer (`layer: "ai/decomp-phase4"`,
`kind: "ai-draft"`, `default_on: false`, `draft: true`, `tag: "M"`, `author: "ai:leanre-phase4-swarm"`)
covering the top verified landmark nodes (`status` in `READ`/`PARTIAL`) across the 6 Phase 4
`leanre.decomp/v1` files, anchored to exact frozen SIGHASH v1 `k1n` digests from `outputs/kernel/kernel.db`.

Guardrails enforced:
- Read-only SQLite access (`mode=ro`, parameterized SQL).
- No multi-line Lean text and no proof bodies: only schematic English summaries and <=1-line
  fair-use signature headers (stripped before `:=`).
- Every record is marked `draft: true`, tagged `M`, and carries an explicit `breaks` caveat.
- Uses real current UTC time by default (pass `--now YYYY-MM-DDTHH:MM:SSZ` to reproduce a timestamp).
"""
from __future__ import annotations

import argparse
import json
import os
import re
import sqlite3
import sys

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.join(REPO, "leanre"))
import annot  # noqa: E402

LAYER = "ai/decomp-phase4"
AUTHOR = "ai:leanre-phase4-swarm"
DECOMP_FILES = (
    "spine_map.json",
    "tcb_audit.json",
    "pillar_theta.json",
    "pillar_galois.json",
    "pillar_window.json",
    "pillar_volume_lit.json",
)
HEADER_RE = re.compile(
    r"^\s*(@\[[^\]]*\]\s*)*(private |protected |noncomputable |nonrec |unsafe |partial )*"
    r"(theorem|lemma|def|abbrev|instance|structure|class|inductive|axiom|opaque)\b"
)
# Authoritative pillar preference when a landmark appears in several files with equal READ status.
PILLAR_RANK = {"theta": 0, "galois": 0, "window": 0, "volume": 0, "tcb": 1, "spine": 2}
GENERIC_PREFIX = "Dominator node ("
GENERIC_MARKER = "verified by header, anchor, and dominator hierarchy"


def clean_ws(text: str) -> str:
    return " ".join(text.replace("\r", " ").replace("\n", " ").split()).strip()


def clean_header(raw: object) -> str | None:
    if not isinstance(raw, str):
        return None
    h = clean_ws(raw)
    if not h or not HEADER_RE.match(h):
        return None
    # Strip any proof/definition body after `:=` so only the <=1-line fair-use signature remains.
    if ":=" in h:
        h = h.split(":=", 1)[0].rstrip()
    if len(h) > 220:
        h = h[:217].rstrip() + "..."
    return h or None


def make_breaks(status: str, verdict: str) -> str:
    if verdict in ("proxy", "degenerate", "vacuous"):
        return (
            f"AI-draft Phase 4 decompilation summary flagging verdict={verdict} (status={status}); "
            "header/contract inspection only (proof body unread). Verify the Lean definition and call sites directly."
        )
    if status == "PARTIAL":
        return (
            "AI-draft Phase 4 decompilation summary (status=PARTIAL: not all nested project contracts unfolded "
            "to Mathlib ground types; proof body unread). May miss hidden hypotheses or degeneracies."
        )
    return (
        "AI-draft Phase 4 decompilation summary (status=READ header/contract only; proof body not audited by a "
        "human mathematician). Does not certify mathematical correctness or Layer 3/4 consensus."
    )


def select_landmarks(decomp_dir: str, per_pillar: int) -> dict[str, dict]:
    selected: dict[str, dict] = {}
    files_for: dict[str, set[str]] = {}
    for fn in DECOMP_FILES:
        path = os.path.join(decomp_dir, fn)
        with open(path, encoding="utf-8") as f:
            doc = json.load(f)
        if doc.get("schema") != "leanre.decomp/v1":
            raise ValueError(f"{path}: unexpected schema {doc.get('schema')!r}")
        pillar = doc["pillar"]
        root = doc.get("root")
        cands = []
        for n in doc.get("nodes", []):
            if n.get("status") not in ("READ", "PARTIAL"):
                continue
            summary = clean_ws(n.get("summary") or "")
            if not summary or (summary.startswith(GENERIC_PREFIX) and GENERIC_MARKER in summary):
                continue
            if "automorphy lifting" in summary.lower():
                raise ValueError(f"{fn}: disallowed phrase 'automorphy lifting' in {n['id']}")
            cands.append((n, summary))
        cands.sort(
            key=lambda item: (
                0 if item[0]["id"] == root else 1,
                0 if item[0]["status"] == "READ" else 1,
                -(item[0].get("dom", {}).get("subtree") or 0),
                item[0]["id"],
            )
        )
        for n, summary in cands[:per_pillar]:
            nid = n["id"]
            files_for.setdefault(nid, set()).add(fn)
            rank = (
                0 if n["status"] == "READ" else 1,
                0 if nid == root else 1,
                0 if n.get("verdict") not in (None, "", "unknown") else 1,
                PILLAR_RANK.get(pillar, 9),
                -len(summary),
                fn,
            )
            cur = selected.get(nid)
            if cur is None or rank < cur["rank"]:
                selected[nid] = {
                    "rank": rank,
                    "file": fn,
                    "pillar": pillar,
                    "node": n,
                    "summary": summary,
                }
    for nid, item in selected.items():
        item["decomp_files"] = sorted(files_for[nid])
    return selected


def fetch_kernel_hashes(kernel_db: str, names: list[str]) -> tuple[dict[str, tuple], str | None]:
    conn = sqlite3.connect("file:" + os.path.abspath(kernel_db) + "?mode=ro", uri=True)
    try:
        lex_id = None
        row = conn.execute("SELECT value_json FROM meta WHERE key='sighash'").fetchone()
        if row:
            lex_id = (json.loads(row[0]).get("lexicon") or {}).get("id")
        out: dict[str, tuple] = {}
        for i in range(0, len(names), 500):
            part = names[i:i + 500]
            qs = ",".join("?" * len(part))
            for r in conn.execute(
                f"SELECT name, sighash, sighash_anon, sig_size, n_local FROM consts WHERE name IN ({qs})",
                part,
            ):
                out[r[0]] = r[1:]
        return out, lex_id
    finally:
        conn.close()


def build_pack(decomp_dir: str, kernel_db: str, per_pillar: int, now: str) -> annot.Pack:
    selected = select_landmarks(decomp_dir, per_pillar)
    names = sorted(selected)
    kmap, lex_id = fetch_kernel_hashes(kernel_db, names)
    missing = [n for n in names if n not in kmap or not kmap[n][0]]
    if missing:
        raise RuntimeError(f"{len(missing)} landmark(s) missing k1n sighash in {kernel_db}: {missing[:5]}")

    p = annot.Pack()
    p.add_layer(
        LAYER,
        "ai-draft",
        "Phase 4 decompilation landmarks (AI draft)",
        description=(
            "AI-generated draft overlay synthesized from the 6 Phase 4 outputs/decomp/*.json files "
            "(top READ/PARTIAL landmarks per pillar), anchored to exact k1n sighashes from "
            "outputs/kernel/kernel.db (solution.ndjson.zst SHA-256 5ea74b91...244e). Off by default; "
            "every record is marked draft=true and tagged [M]. Layer 1 kernel validity does not imply "
            "Layer 2/3/4 comprehension or mathematical consensus (Guardrail 1)."
        ),
        default_on=False,
    )

    for nid in names:
        item = selected[nid]
        n = item["node"]
        k1n, k1a, sig_size, n_local = kmap[nid]
        pillar = item["pillar"]
        status = n["status"]
        verdict = n.get("verdict") or "unknown"
        role = n.get("role") or "unknown"
        anchor = n.get("anchor") or "unknown"
        dom = n.get("dom") or {}
        subtree = dom.get("subtree")
        depth = dom.get("depth")

        prefix = f"[{pillar} | {role} | {status}/{verdict}"
        if isinstance(subtree, int):
            prefix += f" | dom={subtree:,}"
        prefix += "] "
        note = prefix + item["summary"]
        if len(note) > 1800:
            note = note[:1797].rstrip() + "..."

        source = (
            f"outputs/decomp/{item['file']} (pillar={pillar}, status={status}, verdict={verdict}); "
            f"anchor {anchor}; k1n from outputs/kernel/kernel.db (solution.ndjson.zst SHA-256 5ea74b91...244e)"
        )
        if len(source) > annot.MAX_SHORT:
            source = source[:annot.MAX_SHORT - 3].rstrip() + "..."

        extra: dict = {
            "pillar": pillar,
            "role": role,
            "status": status,
            "verdict": verdict,
            "anchor": anchor,
            "decomp_files": item["decomp_files"],
            "sig_size": sig_size,
            "n_local": n_local,
        }
        if isinstance(subtree, int):
            extra["dom_subtree"] = subtree
        if isinstance(depth, int):
            extra["dom_depth"] = depth
        alt = None
        if k1a and k1a != k1n:
            alt = [k1a]
            if lex_id:
                extra["lexicon_id"] = lex_id
        hdr = clean_header(n.get("header"))
        if hdr:
            extra["header"] = hdr

        p.put(
            annot.make_annotation(
                target="decl",
                name=nid,
                sighash=k1n,
                alt_sighash=alt,
                layer=LAYER,
                note=note,
                tag="M",
                source=source,
                breaks=make_breaks(status, verdict),
                author=AUTHOR,
                draft=True,
                extra=extra,
                now=now,
            )
        )
    return p


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--decomp-dir", default=os.path.join(REPO, "outputs", "decomp"))
    ap.add_argument("--kernel-db", default=os.path.join(REPO, "outputs", "kernel", "kernel.db"))
    ap.add_argument("--per-pillar", type=int, default=25, help="top landmarks selected per decomp file")
    ap.add_argument("--now", default=None, help="UTC ISO-8601 timestamp (default: current UTC time)")
    ap.add_argument("--out", default=os.path.join(REPO, "annotations", annot.layer_filename(LAYER)))
    args = ap.parse_args()

    now = args.now or annot.utc_now()
    pack = build_pack(args.decomp_dir, args.kernel_db, args.per_pillar, now)
    text = annot.dump(pack, args.out)
    issues = annot.validate_text(text)
    if issues:
        raise annot.PackError(issues)
    by_pillar: dict[str, int] = {}
    for rec in pack.annots.values():
        pil = rec["extra"]["pillar"]
        by_pillar[pil] = by_pillar.get(pil, 0) + 1
    print(f"{args.out}: {len(pack)} records ({by_pillar}), {len(text.encode('utf-8')):,} B, now={now}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
