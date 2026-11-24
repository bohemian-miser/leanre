#!/usr/bin/env python3
"""leanre.annot -- portable, git-backed JSONL annotation packs (Phase 3, gates A1-A3).

A *pack* is a UTF-8 ``.jsonl`` file: one canonical JSON object per line, sorted, with a
schema header line, layer-definition lines and annotation lines.  See
``docs/ANNOTATION_PACKS.md`` for the normative format.  Stdlib only (Python >= 3.10).

Design rules (enforced here, not just documented):

* An annotation is anchored by ``(target, name, sighash)``.  ``sighash`` is the normalized
  signature hash specified in ``docs/SIGHASH.md`` (owned by ``leanre/sighash.py``); this
  module treats it as an opaque string and never computes it, so a proof-body change
  (same name, same sighash) is an exact hit and a rename with an unchanged signature is
  re-resolved through the hash (``reanchor``).
* Every annotation carries a provenance tag ``L/A/C/S/M`` plus a source citation
  (Guardrail 2); ``M`` additionally needs a "where this breaks" note.
* Layers are independent.  ``ai-draft`` layers are never on by default, every record in
  them is marked ``"draft": true``, is authored ``ai:*`` and may only carry tag ``M``;
  ``ai:*`` authors cannot write into human layers.
* Nothing is silently overwritten: ``merge`` / ``PackStore.import_text`` /
  ``PackStore.upsert`` report conflicts and keep the existing record unless the caller
  resolves each conflict explicitly.
* ``dumps(loads(text)) == text`` for every canonical pack (byte-identical round trip).
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import sys
import tempfile
from typing import Any, Callable, Iterable, Iterator, Mapping, Optional, Sequence

SCHEMA = "leanre.annot/1"

TAGS = ("L", "A", "C", "S", "M")
TAG_MEANING = {
    "L": "extracted by us from the pinned Lean source / kernel export (cite file or export + commit/SHA)",
    "A": "asserted in Alpoge's remark.pdf, not independently traced (Footnote 4 caveat applies)",
    "C": "third-party verifier / community report, not independently executed by us",
    "S": "standard published mathematics (named theorem + year)",
    "M": "CS/RE analogy or heuristic label; must say where it breaks",
}
# decl = kernel/source declaration name; module = Lean module name; folder = dotted module-path
# prefix (directory); namespace = declared Lean namespace.  Only decl carries signature hashes.
TARGETS = ("decl", "module", "folder", "namespace")
HUMAN_LAYER_KINDS = ("human", "human-review")
DRAFT_LAYER_KINDS = ("ai-draft", "bot-check")
LAYER_KINDS = HUMAN_LAYER_KINDS + DRAFT_LAYER_KINDS
AI_AUTHOR_PREFIX = "ai:"
BOT_AUTHOR_PREFIXES = ("ai:", "bot:")

OVERLAY_SCHEMA = "leanre.treemap.overlay/1"
OVERLAY_STATUSES = ("verified", "read", "summary", "flagged")
VALID_ANNOT_STATUSES = ("verified", "read", "summary", "flagged", "partial", "opaque", "suspect")
MAX_PR_PACK_BYTES = 2 * 1024 * 1024  # 2 MiB per contrib PR pack

STATUS_EXACT = "exact"
STATUS_NAME_ONLY = "name_only"
STATUS_HASH_ONLY = "hash_only"
STATUS_ORPHAN = "orphan"
STATUS_UNCHECKED = "unchecked"  # graph has no table for this target type; nothing is claimed
STATUSES = (STATUS_EXACT, STATUS_NAME_ONLY, STATUS_HASH_ONLY, STATUS_ORPHAN, STATUS_UNCHECKED)

MAX_NOTE = 2000       # also keeps packs from becoming a vehicle for raw .lean text (Guardrail 3)
MAX_SHORT = 500
MAX_ALIASES = 32

LAYER_RE = re.compile(r"^[a-z0-9][a-z0-9._-]{0,63}(/[a-z0-9][a-z0-9._-]{0,63}){0,3}$")
SLOT_RE = re.compile(r"^[a-z0-9][a-z0-9._-]{0,63}$")
# Opaque to this module; shape follows docs/SIGHASH.md ("<scheme>:<lowercase hex>", e.g. k1n:<32 hex>).
# Hashes of different schemes live in different spaces and are never compared with each other.
SIGHASH_RE = re.compile(r"^[a-z][a-z0-9._-]{0,31}:[0-9a-f]{16,128}$")
TS_RE = re.compile(r"^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z$")
_CTRL_RE = re.compile(r"[\x00-\x08\x0b-\x1f\x7f\u2028\u2029]")
_CONFLICT_MARK_RE = re.compile(r"^(<{7}|={7}|>{7}|\|{7})( |$)")

_LAYER_FIELDS = {"type", "layer", "kind", "default_on", "title", "description"}
_ANNOT_REQUIRED = ("type", "target", "name", "layer", "tag", "source", "author", "created", "updated")
_ANNOT_OPTIONAL = (
    "sighash", "alt_sighash", "slot", "rename", "aliases", "note", "breaks",
    "draft", "was", "extra", "status", "verdict", "url",
)
_ANNOT_FIELDS = set(_ANNOT_REQUIRED) | set(_ANNOT_OPTIONAL)
_PAYLOAD = ("rename", "aliases", "note")
_TS_FIELDS = ("created", "updated")

Key = tuple  # (layer, target, name, sighash-or-"", slot-or-"")


class PackError(ValueError):
    """Raised when a pack (or a single record) fails validation.  ``.issues`` is a list of dicts."""

    def __init__(self, issues: Sequence[Mapping[str, Any]]):
        self.issues = [dict(i) for i in issues]
        head = "; ".join(
            (f"line {i['line']}: " if i.get("line") else "") + f"{i['code']}: {i['msg']}" for i in self.issues[:5]
        )
        more = f" (+{len(self.issues) - 5} more)" if len(self.issues) > 5 else ""
        super().__init__(head + more)


class ConflictError(PackError):
    """Raised by ``PackStore.upsert`` / ``delete`` when a write would overwrite a different record."""


def _issue(code: str, msg: str, line: int = 0, severity: str = "error") -> dict:
    return {"line": line, "code": code, "severity": severity, "msg": msg}


# ----------------------------------------------------------------------------------------------
# Canonical encoding
# ----------------------------------------------------------------------------------------------

def canonical_json(obj: Any) -> str:
    """The one canonical single-line encoding: sorted keys, no spaces, raw UTF-8, no NaN."""
    return json.dumps(obj, sort_keys=True, ensure_ascii=False, separators=(",", ":"), allow_nan=False)


def record_key(rec: Mapping[str, Any]) -> Key:
    return (rec["layer"], rec.get("target", "decl"), rec["name"], rec.get("sighash") or "", rec.get("slot") or "")


def key_id(key: Key) -> str:
    """Stable 16-hex id of a record key (for URLs / UI element ids).  Derived, never stored."""
    return hashlib.sha256(canonical_json(list(key)).encode("utf-8")).hexdigest()[:16]


def record_id(rec: Mapping[str, Any]) -> str:
    return key_id(record_key(rec))


def display_tag(rec: Mapping[str, Any]) -> str:
    return "[" + rec["tag"] + "]"


def _sort_key(key: Key) -> tuple:
    layer, target, name, sighash, slot = key
    return (target, name, sighash, layer, slot)


def _clean_str(v: Any) -> Any:
    return v.strip() if isinstance(v, str) else v


def normalize_layer(rec: Mapping[str, Any]) -> dict:
    out = {"type": "layer"}
    for k, v in rec.items():
        if k == "type":
            continue
        if k in ("title", "description"):
            v = _clean_str(v)
            if v in (None, ""):
                continue
        out[k] = v
    if "default_on" not in out and out.get("kind") in LAYER_KINDS:
        out["default_on"] = out["kind"] in HUMAN_LAYER_KINDS
    return out


def normalize_annot(rec: Mapping[str, Any]) -> dict:
    """Return the canonical form of an annotation dict (drop empty optionals, sort/dedupe lists)."""
    out: dict = {"type": "annot"}
    for k, v in rec.items():
        if k == "type":
            continue
        if k in ("rename", "note", "breaks", "source", "author", "slot", "sighash", "status", "verdict", "url"):
            v = _clean_str(v)
        if k in _ANNOT_OPTIONAL and (v is None or v == "" or v == [] or v == {} or v is False):
            continue
        if k in ("aliases", "was", "alt_sighash") and isinstance(v, (list, tuple)) and all(isinstance(x, str) for x in v):
            v = sorted({x.strip() for x in v if x.strip()})
            if not v:
                continue
        out[k] = v
    out.setdefault("target", "decl")
    return out


# ----------------------------------------------------------------------------------------------
# Record validation
# ----------------------------------------------------------------------------------------------

def _check_text(errs: list, field: str, v: Any, limit: int, multiline: bool = False) -> bool:
    if not isinstance(v, str) or not v:
        errs.append(("bad_" + field, f"{field} must be a non-empty string"))
        return False
    if len(v) > limit:
        errs.append(("too_long", f"{field} is {len(v)} chars (limit {limit})"))
    if _CTRL_RE.search(v) or (not multiline and "\n" in v):
        errs.append(("bad_chars", f"{field} contains control characters" + ("" if multiline else " or a newline")))
    return True


def check_layer(rec: Mapping[str, Any]) -> list:
    """Validate one (normalized) layer record -> list of (code, msg)."""
    errs: list = []
    for k in sorted(set(rec) - _LAYER_FIELDS):
        errs.append(("unknown_field", f"unknown layer field {k!r}"))
    lid = rec.get("layer")
    if not isinstance(lid, str) or not LAYER_RE.match(lid):
        errs.append(("bad_layer", f"layer id {lid!r} must match {LAYER_RE.pattern}"))
    kind = rec.get("kind")
    if kind not in LAYER_KINDS:
        errs.append(("bad_kind", f"layer kind {kind!r} must be one of {list(LAYER_KINDS)}"))
    if not isinstance(rec.get("default_on"), bool):
        errs.append(("bad_default_on", "default_on must be true or false"))
    elif kind in DRAFT_LAYER_KINDS and rec["default_on"]:
        errs.append(("ai_draft_default_on", f"{kind} layers must have default_on=false"))
    _check_text(errs, "title", rec.get("title"), MAX_SHORT)
    if "description" in rec:
        _check_text(errs, "description", rec["description"], MAX_NOTE, multiline=True)
    return errs


def check_annot(rec: Mapping[str, Any], layer: Optional[Mapping[str, Any]]) -> list:
    """Validate one (normalized) annotation record against its layer -> list of (code, msg)."""
    errs: list = []
    for k in sorted(set(rec) - _ANNOT_FIELDS):
        errs.append(("unknown_field", f"unknown annotation field {k!r}"))
    for k in _ANNOT_REQUIRED:
        if k not in rec:
            errs.append(("missing_" + k, f"missing mandatory field {k!r}"))
    if rec.get("target") not in TARGETS:
        errs.append(("bad_target", f"target {rec.get('target')!r} must be one of {list(TARGETS)}"))
    if "name" in rec:
        if _check_text(errs, "name", rec["name"], MAX_SHORT) and rec["name"] != rec["name"].strip():
            errs.append(("bad_name", "name has leading/trailing whitespace"))
    if "sighash" in rec:
        if not isinstance(rec["sighash"], str) or not SIGHASH_RE.match(rec["sighash"]):
            errs.append(("bad_sighash", f"sighash {rec['sighash']!r} must match {SIGHASH_RE.pattern}"))
        elif rec.get("target") != "decl":
            errs.append(("bad_sighash", "only target=decl annotations carry a sighash"))
    if "alt_sighash" in rec:
        v = rec["alt_sighash"]
        if not isinstance(v, list) or not all(isinstance(x, str) and SIGHASH_RE.match(x) for x in v):
            errs.append(("bad_alt_sighash", "alt_sighash must be a list of sighash strings"))
        elif "sighash" not in rec:
            errs.append(("bad_alt_sighash", "alt_sighash requires a primary sighash"))
        elif rec["sighash"] in v or len(v) > 8:
            errs.append(("bad_alt_sighash", "alt_sighash must not repeat the primary sighash (max 8 entries)"))
    if "slot" in rec and (not isinstance(rec["slot"], str) or not SLOT_RE.match(rec["slot"])):
        errs.append(("bad_slot", f"slot {rec['slot']!r} must match {SLOT_RE.pattern}"))
    lid = rec.get("layer")
    if "layer" in rec and (not isinstance(lid, str) or not LAYER_RE.match(lid)):
        errs.append(("bad_layer", f"layer id {lid!r} must match {LAYER_RE.pattern}"))
    # provenance (Guardrail 2)
    tag = rec.get("tag")
    if "tag" in rec and tag not in TAGS:
        errs.append(("bad_tag", f"provenance tag {tag!r} must be one of {list(TAGS)} (stored without brackets)"))
    if "source" in rec:
        _check_text(errs, "source", rec["source"], MAX_SHORT)
    if tag == "M":
        if "breaks" not in rec:
            errs.append(("missing_breaks", "tag M requires a 'breaks' note (where the analogy/heuristic breaks)"))
    elif "breaks" in rec and tag in TAGS:
        errs.append(("unexpected_breaks", "'breaks' is only allowed with tag M"))
    if "breaks" in rec:
        _check_text(errs, "breaks", rec["breaks"], MAX_NOTE, multiline=True)
    if "author" in rec:
        _check_text(errs, "author", rec["author"], 120)
    # payload
    if not any(k in rec for k in _PAYLOAD):
        errs.append(("empty_annotation", "annotation needs at least one of rename / aliases / note"))
    if "rename" in rec:
        _check_text(errs, "rename", rec["rename"], MAX_SHORT)
    if "note" in rec:
        _check_text(errs, "note", rec["note"], MAX_NOTE, multiline=True)
    for lf in ("aliases", "was"):
        if lf in rec:
            v = rec[lf]
            if not isinstance(v, list) or not all(isinstance(x, str) and x for x in v):
                errs.append(("bad_" + lf, f"{lf} must be a list of non-empty strings"))
            else:
                if len(v) > MAX_ALIASES:
                    errs.append(("too_long", f"{lf} has {len(v)} entries (limit {MAX_ALIASES})"))
                for x in v:
                    _check_text(errs, lf, x, MAX_SHORT)
    if "extra" in rec and not isinstance(rec["extra"], dict):
        errs.append(("bad_extra", "extra must be a JSON object"))
    if "status" in rec:
        if _check_text(errs, "status", rec["status"], 64) and rec["status"].lower() not in VALID_ANNOT_STATUSES:
            errs.append(("bad_status", f"status {rec['status']!r} must be one of {list(VALID_ANNOT_STATUSES)}"))
    if "verdict" in rec:
        _check_text(errs, "verdict", rec["verdict"], MAX_SHORT)
    if "url" in rec:
        _check_text(errs, "url", rec["url"], MAX_SHORT)
    for tf in _TS_FIELDS:
        if tf in rec and (not isinstance(rec[tf], str) or not TS_RE.match(rec[tf])):
            errs.append(("bad_" + tf, f"{tf} must be UTC ISO-8601 'YYYY-MM-DDTHH:MM:SSZ'"))
    if all(isinstance(rec.get(tf), str) and TS_RE.match(rec[tf]) for tf in _TS_FIELDS) and rec["updated"] < rec["created"]:
        errs.append(("bad_updated", "updated is earlier than created"))
    if "draft" in rec and rec["draft"] is not True:
        errs.append(("bad_draft", "draft, when present, must be true"))
    # layer coupling: AI/bot drafts can never masquerade as facts, humans never write into AI/bot layers
    if isinstance(lid, str) and "layer" in rec:
        if layer is None:
            errs.append(("undeclared_layer", f"layer {lid!r} is not declared by a layer line in this pack"))
        else:
            author = rec.get("author") if isinstance(rec.get("author"), str) else ""
            is_ai = any(author.startswith(p) for p in BOT_AUTHOR_PREFIXES)
            lkind = layer.get("kind")
            if lkind in DRAFT_LAYER_KINDS:
                if rec.get("draft") is not True:
                    errs.append(("draft_unmarked", f"records in a {lkind} layer must carry \"draft\": true"))
                if not is_ai:
                    errs.append(("draft_author", f"records in a {lkind} layer must have an 'ai:<id>' or 'bot:<id>' author"))
                if lkind == "ai-draft" and tag in TAGS and tag != "M":
                    errs.append(("draft_tag", f"AI-draft records may only carry tag M (got {tag}); "
                                              "promote to a human layer to assert L/A/C/S"))
            elif lkind in HUMAN_LAYER_KINDS:
                if "draft" in rec:
                    errs.append(("draft_in_human_layer", "\"draft\" is only allowed in ai-draft or bot-check layers"))
                if is_ai:
                    errs.append(("ai_author_in_human_layer",
                                 "'ai:*' and 'bot:*' authors may only write into ai-draft or bot-check layers"))
    return errs


# ----------------------------------------------------------------------------------------------
# Pack
# ----------------------------------------------------------------------------------------------

class Pack:
    """In-memory pack: ``layers`` (id -> layer dict) and ``annots`` (key -> annotation dict)."""

    def __init__(self) -> None:
        self.layers: dict = {}
        self.annots: dict = {}

    # -- construction -------------------------------------------------------------------------
    def copy(self) -> "Pack":
        p = Pack()
        p.layers = {k: json.loads(canonical_json(v)) for k, v in self.layers.items()}
        p.annots = {k: json.loads(canonical_json(v)) for k, v in self.annots.items()}
        return p

    def add_layer(self, layer: str, kind: str = "human", title: str = "", description: str = "",
                  default_on: Optional[bool] = None) -> dict:
        """Declare a layer.  Re-declaring identically is a no-op; a different definition raises."""
        rec = normalize_layer({"layer": layer, "kind": kind, "title": title or layer,
                               "description": description,
                               "default_on": (kind in HUMAN_LAYER_KINDS) if default_on is None else default_on})
        errs = check_layer(rec)
        if errs:
            raise PackError([_issue(c, m) for c, m in errs])
        old = self.layers.get(layer)
        if old is not None and old != rec:
            raise ConflictError([_issue("layer_conflict", f"layer {layer!r} already defined differently")])
        self.layers[layer] = rec
        return rec

    def put(self, rec: Mapping[str, Any], replace: bool = False) -> dict:
        """Insert a full annotation record.  Refuses to overwrite a different record unless ``replace``."""
        rec = normalize_annot(rec)
        errs = check_annot(rec, self.layers.get(rec.get("layer")))
        if errs:
            raise PackError([_issue(c, m) for c, m in errs])
        key = record_key(rec)
        old = self.annots.get(key)
        if old is not None and old != rec and not replace:
            raise ConflictError([_issue("conflict", f"record {key_id(key)} {key!r} exists with different content")])
        self.annots[key] = rec
        return rec

    def get(self, rid: str) -> Optional[dict]:
        for k, v in self.annots.items():
            if key_id(k) == rid:
                return v
        return None

    def sorted_annots(self) -> list:
        return [self.annots[k] for k in sorted(self.annots, key=_sort_key)]

    def subset(self, layers: Iterable[str]) -> "Pack":
        want = set(layers)
        p = Pack()
        p.layers = {k: v for k, v in self.layers.items() if k in want}
        p.annots = {k: v for k, v in self.annots.items() if k[0] in want}
        return p.copy()

    def __eq__(self, other: object) -> bool:
        return isinstance(other, Pack) and self.layers == other.layers and self.annots == other.annots

    def __len__(self) -> int:
        return len(self.annots)


def make_annotation(*, name: str, layer: str, tag: str, source: str, author: str, now: str,
                    sighash: Optional[str] = None, alt_sighash: Optional[Sequence[str]] = None,
                    target: str = "decl", slot: Optional[str] = None,
                    rename: Optional[str] = None, aliases: Optional[Sequence[str]] = None,
                    note: Optional[str] = None, breaks: Optional[str] = None, draft: bool = False,
                    extra: Optional[Mapping[str, Any]] = None, created: Optional[str] = None) -> dict:
    """Build a normalized annotation dict (validated when it is ``put`` into a Pack)."""
    return normalize_annot({
        "target": target, "name": name, "sighash": sighash, "slot": slot, "layer": layer,
        "alt_sighash": list(alt_sighash) if alt_sighash else None,
        "rename": rename, "aliases": list(aliases) if aliases else None, "note": note,
        "tag": tag.strip("[]") if isinstance(tag, str) else tag, "source": source, "breaks": breaks,
        "author": author, "draft": bool(draft), "extra": dict(extra) if extra else None,
        "created": created or now, "updated": now,
    })


def utc_now() -> str:
    import datetime
    return datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


# ----------------------------------------------------------------------------------------------
# Export / import / validate
# ----------------------------------------------------------------------------------------------

def header_line() -> str:
    return canonical_json({"type": "pack", "schema": SCHEMA})


def dumps(pack: Pack, layers: Optional[Iterable[str]] = None) -> str:
    """Export: canonical text.  Header, then layer lines by id, then annotations by
    (target, name, sighash, layer, slot).  Deterministic: depends only on pack content."""
    if layers is not None:
        pack = pack.subset(layers)
    lines = [header_line()]
    lines += [canonical_json(pack.layers[k]) for k in sorted(pack.layers)]
    lines += [canonical_json(r) for r in pack.sorted_annots()]
    return "\n".join(lines) + "\n"


def _no_dup_pairs(pairs: list) -> dict:
    d: dict = {}
    for k, v in pairs:
        if k in d:
            raise ValueError(f"duplicate JSON key {k!r}")
        d[k] = v
    return d


def _reject_constant(tok: str) -> Any:
    raise ValueError(f"non-finite number {tok} is not allowed")


def parse(text: str) -> tuple:
    """Parse pack text -> (Pack, issues).  Never raises on bad content; every problem is an issue.

    Issues with severity ``error`` mean the pack is invalid; ``noncanonical`` issues (severity
    ``format``) mean the content is valid but the bytes are not the canonical export."""
    pack = Pack()
    issues: list = []
    if isinstance(text, bytes):
        try:
            text = text.decode("utf-8")
        except UnicodeDecodeError as e:
            return pack, [_issue("bad_utf8", str(e))]
    if text.startswith("\ufeff"):
        issues.append(_issue("bom", "file starts with a UTF-8 BOM", 1))
        text = text[1:]
    if "\r" in text:
        issues.append(_issue("carriage_return", "CR characters found; packs use LF line endings only"))
        text = text.replace("\r\n", "\n").replace("\r", "\n")
    if text and not text.endswith("\n"):
        issues.append(_issue("noncanonical", "missing final newline", severity="format"))
    raw_lines = text.split("\n")
    if raw_lines and raw_lines[-1] == "":
        raw_lines.pop()
    seen_header = False
    pending: list = []  # (lineno, raw, normalized annot)
    order: list = []    # (lineno, rank, sortkey) for the sortedness check
    for n, raw in enumerate(raw_lines, 1):
        if not raw.strip():
            issues.append(_issue("blank_line", "blank line", n))
            continue
        if _CONFLICT_MARK_RE.match(raw):
            issues.append(_issue("git_conflict_marker", "unresolved git merge conflict marker", n))
            continue
        try:
            obj = json.loads(raw, object_pairs_hook=_no_dup_pairs, parse_constant=_reject_constant)
        except ValueError as e:
            issues.append(_issue("bad_json", str(e), n))
            continue
        if not isinstance(obj, dict):
            issues.append(_issue("bad_json", "line is not a JSON object", n))
            continue
        typ = obj.get("type")
        if typ == "pack":
            if seen_header:
                issues.append(_issue("duplicate_header", "more than one pack header line", n))
            elif n != 1:
                issues.append(_issue("header_not_first", "pack header must be the first line", n))
            seen_header = True
            if obj.get("schema") != SCHEMA:
                issues.append(_issue("bad_schema", f"schema {obj.get('schema')!r} is not {SCHEMA!r}", n))
            elif set(obj) != {"type", "schema"}:
                issues.append(_issue("unknown_field", "pack header carries only 'type' and 'schema'", n))
            elif raw != header_line():
                issues.append(_issue("noncanonical", "header line is not canonically encoded", n, "format"))
            continue
        if typ == "layer":
            rec = normalize_layer(obj)
            errs = check_layer(rec)
            for c, m in errs:
                issues.append(_issue(c, m, n))
            lid = rec.get("layer")
            if errs or not isinstance(lid, str):
                continue
            if lid in pack.layers:
                if pack.layers[lid] == rec:
                    issues.append(_issue("duplicate_layer", f"layer {lid!r} declared twice", n))
                else:
                    issues.append(_issue("layer_conflict", f"layer {lid!r} declared twice with different definitions", n))
                continue
            pack.layers[lid] = rec
            order.append((n, 0, (lid,)))
            if canonical_json(rec) != raw:
                issues.append(_issue("noncanonical", "layer line is not canonically encoded", n, "format"))
            continue
        if typ == "annot":
            pending.append((n, raw, normalize_annot(obj)))
            continue
        issues.append(_issue("bad_type", f"unknown line type {typ!r} (expected pack / layer / annot)", n))
    if not seen_header:
        issues.append(_issue("missing_header", f"first line must be {header_line()}", 1))
    first_line: dict = {}
    for n, raw, rec in pending:
        errs = check_annot(rec, pack.layers.get(rec.get("layer")) if isinstance(rec.get("layer"), str) else None)
        for c, m in errs:
            issues.append(_issue(c, m, n))
        if errs:
            continue
        key = record_key(rec)
        if key in pack.annots:
            same = pack.annots[key] == rec
            issues.append(_issue("duplicate_key" if same else "conflict",
                                 f"record {key_id(key)} repeats line {first_line[key]}"
                                 + ("" if same else " with DIFFERENT content (kept the first; resolve by hand)"), n))
            continue
        pack.annots[key] = rec
        first_line[key] = n
        order.append((n, 1, _sort_key(key)))
        if canonical_json(rec) != raw:
            issues.append(_issue("noncanonical", "annotation line is not canonically encoded", n, "format"))
    prev = None
    for n, rank, sk in order:
        cur = (rank, sk)
        if prev is not None and cur < prev:
            issues.append(_issue("noncanonical", "lines are not in canonical sort order", n, "format"))
            break
        prev = cur
    issues.sort(key=lambda i: (i["line"], i["code"]))
    return pack, issues


def errors_of(issues: Iterable[Mapping[str, Any]]) -> list:
    return [dict(i) for i in issues if i["severity"] == "error"]


def validate_text(text: str, canonical: bool = True) -> list:
    """Validate pack text -> list of issues (empty = valid).  With ``canonical=True`` (default,
    what CI should run on ``annotations/``) non-canonical bytes/ordering are reported too."""
    pack, issues = parse(text)
    if canonical:
        if not errors_of(issues) and not issues and dumps(pack) != (text.decode("utf-8") if isinstance(text, bytes) else text):
            issues.append(_issue("noncanonical", "bytes differ from the canonical export", severity="format"))
        return issues
    return errors_of(issues)


def validate_file(path: str, canonical: bool = True) -> list:
    with open(path, "rb") as f:
        return validate_text(f.read(), canonical=canonical)


def loads(text: str) -> Pack:
    """Import: parse + validate; raises PackError on any error.  Accepts unsorted / hand-formatted
    packs (those are normalized), but never invalid ones."""
    pack, issues = parse(text)
    errs = errors_of(issues)
    if errs:
        raise PackError(errs)
    return pack


def load(path: str) -> Pack:
    with open(path, "rb") as f:
        return loads(f.read())


def _atomic_write(path: str, text: str) -> None:
    d = os.path.dirname(os.path.abspath(path))
    os.makedirs(d, exist_ok=True)
    fd, tmp = tempfile.mkstemp(prefix=".annot-", suffix=".tmp", dir=d)
    try:
        with os.fdopen(fd, "wb") as f:
            f.write(text.encode("utf-8"))
        os.replace(tmp, path)
    except BaseException:
        if os.path.exists(tmp):
            os.unlink(tmp)
        raise


def dump(pack: Pack, path: str, layers: Optional[Iterable[str]] = None) -> str:
    text = dumps(pack, layers)
    _atomic_write(path, text)
    return text


# ----------------------------------------------------------------------------------------------
# Merge / diff
# ----------------------------------------------------------------------------------------------

def _changed_fields(a: Mapping[str, Any], b: Mapping[str, Any]) -> list:
    return sorted(k for k in set(a) | set(b) if a.get(k) != b.get(k))


def merge(ours: Pack, theirs: Pack, resolve: Optional[Mapping[str, str]] = None) -> dict:
    """Merge ``theirs`` into a copy of ``ours``.  Never overwrites silently.

    Returns ``{"pack", "added", "identical", "conflicts", "resolved", "layers_added", "ok"}``.
    A record present on both sides with different content is a *conflict*: ours is kept and the
    conflict is listed (``kind`` = ``content`` or ``timestamp_only``) unless ``resolve`` maps its id
    (or ``"layer:<id>"`` for layer-definition conflicts) to ``"theirs"`` / ``"ours"``.
    ``ok`` is true iff no unresolved conflict remains."""
    resolve = dict(resolve or {})
    for k, v in resolve.items():
        if v not in ("ours", "theirs"):
            raise ValueError(f"resolve[{k!r}] must be 'ours' or 'theirs'")
    out = ours.copy()
    res: dict = {"pack": out, "added": [], "identical": [], "conflicts": [], "resolved": [], "layers_added": []}
    for lid in sorted(theirs.layers):
        t = theirs.layers[lid]
        o = out.layers.get(lid)
        if o is None:
            out.layers[lid] = json.loads(canonical_json(t))
            res["layers_added"].append(lid)
        elif o != t:
            rid = "layer:" + lid
            choice = resolve.get(rid)
            kind_change = o.get("kind") != t.get("kind")
            if choice == "theirs" and kind_change:
                choice = None  # changing a layer's kind would re-class its records; never automatic
            if choice == "theirs":
                out.layers[lid] = json.loads(canonical_json(t))
            if choice:
                res["resolved"].append({"id": rid, "choice": choice})
            else:
                res["conflicts"].append({"id": rid, "kind": "layer", "layer": lid, "ours": o, "theirs": t,
                                         "fields": _changed_fields(o, t)})
    for key in sorted(theirs.annots, key=_sort_key):
        t = theirs.annots[key]
        rid = key_id(key)
        o = out.annots.get(key)
        if o is None:
            errs = check_annot(t, out.layers.get(key[0]))
            if errs:  # e.g. their record is not legal under OUR definition of the layer
                res["conflicts"].append({"id": rid, "kind": "invalid_here", "key": list(key), "ours": None,
                                         "theirs": t, "fields": [], "errors": [m for _, m in errs]})
                continue
            out.annots[key] = json.loads(canonical_json(t))
            res["added"].append(rid)
        elif o == t:
            res["identical"].append(rid)
        else:
            fields = _changed_fields(o, t)
            kind = "timestamp_only" if set(fields) <= set(_TS_FIELDS) else "content"
            choice = resolve.get(rid)
            if choice == "theirs" and check_annot(t, out.layers.get(key[0])):
                choice = None
            if choice == "theirs":
                out.annots[key] = json.loads(canonical_json(t))
            if choice:
                res["resolved"].append({"id": rid, "choice": choice})
            else:
                res["conflicts"].append({"id": rid, "kind": kind, "key": list(key), "ours": o, "theirs": t,
                                         "fields": fields})
    res["ok"] = not res["conflicts"]
    return res


def diff(a: Pack, b: Pack) -> dict:
    """Structural diff a -> b: ``added`` / ``removed`` / ``changed`` records and layers."""
    out: dict = {"added": [], "removed": [], "changed": [], "layers_added": [], "layers_removed": [],
                 "layers_changed": []}
    for key in sorted(set(a.annots) | set(b.annots), key=_sort_key):
        x, y = a.annots.get(key), b.annots.get(key)
        if x is None:
            out["added"].append({"id": key_id(key), "key": list(key), "record": y})
        elif y is None:
            out["removed"].append({"id": key_id(key), "key": list(key), "record": x})
        elif x != y:
            out["changed"].append({"id": key_id(key), "key": list(key), "fields": _changed_fields(x, y),
                                   "before": x, "after": y})
    for lid in sorted(set(a.layers) | set(b.layers)):
        x, y = a.layers.get(lid), b.layers.get(lid)
        if x is None:
            out["layers_added"].append(lid)
        elif y is None:
            out["layers_removed"].append(lid)
        elif x != y:
            out["layers_changed"].append({"layer": lid, "fields": _changed_fields(x, y)})
    out["same"] = not any(out[k] for k in list(out))
    return out


# ----------------------------------------------------------------------------------------------
# Layers / overlay view
# ----------------------------------------------------------------------------------------------

def default_layers(pack: Pack) -> list:
    """Layers that are on when the user has not chosen: human layers with default_on. Never ai-draft/bot-check."""
    return sorted(l for l, d in pack.layers.items() if d["kind"] in HUMAN_LAYER_KINDS and d["default_on"])


def layer_table(pack: Pack, enabled: Optional[Iterable[str]] = None) -> list:
    on = set(default_layers(pack) if enabled is None else enabled)
    counts: dict = {}
    for k in pack.annots:
        counts[k[0]] = counts.get(k[0], 0) + 1
    return [{"layer": l, "kind": d["kind"], "draft": d["kind"] in DRAFT_LAYER_KINDS, "default_on": d["default_on"],
             "enabled": l in on, "title": d["title"], "description": d.get("description", ""),
             "count": counts.get(l, 0)} for l, d in sorted(pack.layers.items())]


def view(pack: Pack, enabled: Optional[Iterable[str]] = None) -> dict:
    """Overlay of the enabled layers (default: ``default_layers``; AI drafts only when listed).

    Returns ``{"layers": layer_table, "enabled": [...], "targets": {"<target>:<name>": entry},
    "conflicts": [...]}``.  Each entry has ``annotations`` (records + ``id``, ``display_tag``,
    ``draft``) and an effective ``rename``: human layers outrank ai-draft layers, then the order of
    ``enabled``.  If several enabled layers of the winning class propose different renames the
    entry gets ``rename_conflict: true`` and the disagreement is listed in ``conflicts`` -- the
    first one is shown, none is hidden."""
    order = list(default_layers(pack) if enabled is None else enabled)
    unknown = [l for l in order if l not in pack.layers]
    if unknown:
        raise PackError([_issue("undeclared_layer", f"unknown layer(s): {unknown}")])
    rank = {l: i for i, l in enumerate(order)}
    targets: dict = {}
    for key in sorted(pack.annots, key=_sort_key):
        if key[0] not in rank:
            continue
        rec = pack.annots[key]
        ent = targets.setdefault(f"{key[1]}:{key[2]}", {"target": key[1], "name": key[2], "annotations": []})
        a = dict(rec)
        a["id"] = key_id(key)
        a["display_tag"] = display_tag(rec)
        a["draft"] = pack.layers[key[0]]["kind"] in DRAFT_LAYER_KINDS
        ent["annotations"].append(a)
    conflicts: list = []
    for tk, ent in targets.items():
        ent["annotations"].sort(key=lambda a: (a["draft"], rank[a["layer"]], a.get("sighash", ""), a.get("slot", "")))
        aliases: set = set()
        for a in ent["annotations"]:
            aliases.update(a.get("aliases", []))
        ent["aliases"] = sorted(aliases)
        cands = [a for a in ent["annotations"] if "rename" in a]
        ent["rename"] = None
        ent["rename_draft"] = False
        ent["rename_conflict"] = False
        if cands:
            top = cands[0]
            ent["rename"], ent["rename_draft"], ent["rename_layer"] = top["rename"], top["draft"], top["layer"]
            rivals = [a for a in cands if a["draft"] == top["draft"]]
            if len({a["rename"] for a in rivals}) > 1:
                ent["rename_conflict"] = True
                conflicts.append({"kind": "rename", "target": ent["target"], "name": ent["name"],
                                  "shown": top["rename"],
                                  "candidates": [{"id": a["id"], "layer": a["layer"], "rename": a["rename"],
                                                  "author": a["author"]} for a in rivals]})
    return {"layers": layer_table(pack, order), "enabled": order, "targets": targets, "conflicts": conflicts}


def promote(pack: Pack, rid: str, to_layer: str, *, author: str, tag: str, source: str, now: str,
            breaks: Optional[str] = None) -> dict:
    """A human adopts an AI draft: copy record ``rid`` into human layer ``to_layer`` under the
    human's own author + provenance.  The draft stays where it is; nothing is overwritten."""
    src = pack.get(rid)
    if src is None:
        raise KeyError(rid)
    rec = {k: v for k, v in src.items() if k not in ("draft", "breaks", "extra")}
    rec.update(layer=to_layer, author=author, tag=tag.strip("[]"), source=source, created=now, updated=now)
    if breaks:
        rec["breaks"] = breaks
    rec["extra"] = {"promoted_from": {"layer": src["layer"], "author": src["author"], "id": rid}}
    return pack.put(rec)


# ----------------------------------------------------------------------------------------------
# Re-anchoring against a (new) graph
# ----------------------------------------------------------------------------------------------

def _scheme(h: str) -> str:
    return h.split(":", 1)[0]


def record_hashes(rec: Mapping[str, Any]) -> list:
    """Primary sighash first, then alt_sighash (sorted)."""
    return ([rec["sighash"]] if rec.get("sighash") else []) + list(rec.get("alt_sighash", []))


class GraphIndex:
    """What ``reanchor`` needs from a graph: name -> signature hashes, hash -> names, and
    (optionally) the sets of module / folder / namespace names.  No dependency on kernel.db.

    ``decls``: mapping or iterable of ``(name, hashes)`` where ``hashes`` is a string, an iterable
    of strings (preferred scheme first, e.g. ``(k1n, k1a)``) or None/"" for "present, unhashed".
    ``names``: ``{"module": iterable, "folder": iterable, "namespace": iterable}`` (any subset).
    ``restrict_to``: a Pack; only rows relevant to its records are kept, so a multi-million-row
    constant table can be streamed through in constant memory."""

    def __init__(self, decls: Any = (), names: Optional[Mapping[str, Iterable[str]]] = None,
                 label: str = "", restrict_to: Optional[Pack] = None) -> None:
        self.label = label
        self.hashes_of: dict = {}
        self.names_of: dict = {}
        want_names = want_hashes = None
        if restrict_to is not None:
            want_names = {k[2] for k in restrict_to.annots if k[1] == "decl"}
            want_hashes = {h for r in restrict_to.annots.values() for h in record_hashes(r)}
        items = decls.items() if isinstance(decls, Mapping) else decls
        for row in items:
            name, hs = row[0], row[1:] if len(row) != 2 else row[1]
            if hs is None or isinstance(hs, str):
                hs = (hs,) if hs else ()
            hs = tuple(h for h in hs if h)
            if want_names is None or name in want_names or any(h in want_hashes for h in hs):
                self.hashes_of[name] = hs
            for h in hs:
                if want_hashes is None or h in want_hashes:
                    self.names_of.setdefault(h, []).append(name)
        for v in self.names_of.values():
            v.sort()
        self.names: dict = {t: set(v) for t, v in (names or {}).items()}
        self.restricted = restrict_to is not None

    @classmethod
    def from_tsv(cls, path: str, label: str = "", restrict_to: Optional[Pack] = None) -> "GraphIndex":
        """``name<TAB>hash[<TAB>hash...]`` per line (hashes may be absent); '#' lines ignored."""
        def rows() -> Iterator[tuple]:
            with open(path, "r", encoding="utf-8") as f:
                for line in f:
                    line = line.rstrip("\n")
                    if not line or line.startswith("#"):
                        continue
                    parts = line.split("\t")
                    yield parts[0], tuple(p.strip() for p in parts[1:])
        return cls(rows(), label=label or path, restrict_to=restrict_to)

    @classmethod
    def from_sqlite(cls, path: str, sql: str, label: str = "", restrict_to: Optional[Pack] = None,
                    names: Optional[Mapping[str, Iterable[str]]] = None) -> "GraphIndex":
        """Read-only: ``sql`` must be a single SELECT returning ``(name, hash[, hash...])`` rows."""
        import sqlite3
        if not re.match(r"^\s*select\b[^;]*;?\s*$", sql, re.I | re.S):
            raise ValueError("sql must be a single SELECT statement")
        conn = sqlite3.connect("file:" + os.path.abspath(path) + "?mode=ro", uri=True)
        try:
            return cls(conn.execute(sql), names=names, label=label or path, restrict_to=restrict_to)
        finally:
            conn.close()

    KERNEL_SQL = "SELECT name, sighash, sighash_anon FROM consts"

    @staticmethod
    def _chunked_in(conn: Any, sql_prefix: str, values: Sequence[str], chunk: int = 500) -> Iterator[tuple]:
        for i in range(0, len(values), chunk):
            part = values[i:i + chunk]
            qs = ",".join("?" * len(part))
            yield from conn.execute(sql_prefix + f" ({qs})", part)

    @classmethod
    def from_kernel_db(cls, kernel_db: str, restrict_to: Optional[Pack] = None,
                       leanre_db: Optional[str] = None) -> "GraphIndex":
        """Index ``outputs/kernel/kernel.db`` (table ``consts(name, sighash, sighash_anon)``, see
        docs/KERNEL.md).  With ``leanre_db`` (Phase 2 ``outputs/leanre.db``) module names
        (``modules.name``) and folder prefixes (``namespace_stats.prefix``) become checkable too.
        Uses indexed parameterized lookups when ``restrict_to`` is given."""
        import sqlite3
        names: dict = {}
        if leanre_db:
            conn = sqlite3.connect("file:" + os.path.abspath(leanre_db) + "?mode=ro", uri=True)
            try:
                if restrict_to is not None:
                    want_m = sorted({k[2] for k in restrict_to.annots if k[1] == "module"})
                    want_f = sorted({k[2] for k in restrict_to.annots if k[1] == "folder"})
                    names["module"] = [r[0] for r in cls._chunked_in(conn, "SELECT name FROM modules WHERE name IN", want_m)]
                    names["folder"] = [r[0] for r in cls._chunked_in(conn, "SELECT prefix FROM namespace_stats WHERE prefix IN", want_f)]
                else:
                    names["module"] = [r[0] for r in conn.execute("SELECT name FROM modules")]
                    names["folder"] = [r[0] for r in conn.execute("SELECT prefix FROM namespace_stats")]
            finally:
                conn.close()
        if restrict_to is None:
            return cls.from_sqlite(kernel_db, cls.KERNEL_SQL, label=kernel_db, names=names)
        want_n = sorted({k[2] for k in restrict_to.annots if k[1] == "decl"})
        want_h = sorted({h for r in restrict_to.annots.values() for h in record_hashes(r)})
        conn = sqlite3.connect("file:" + os.path.abspath(kernel_db) + "?mode=ro", uri=True)
        try:
            seen: dict = {}
            for col, vals in (("name", want_n), ("sighash", want_h), ("sighash_anon", want_h)):
                for row in cls._chunked_in(conn, f"SELECT name, sighash, sighash_anon FROM consts WHERE {col} IN", vals):
                    seen[row[0]] = row
            return cls(seen.values(), names=names, label=kernel_db, restrict_to=restrict_to)
        finally:
            conn.close()

    @classmethod
    def from_anchors_json(cls, path: str, label: str = "", restrict_to: Optional[Pack] = None) -> tuple:
        """Load compact anchor index JSON -> ``(GraphIndex, subtree_sizes_by_name)``.

        Accepts either ``{"decls": {name: "k1n:..." | ["k1n:...", ...] | {"sighash": ..., "alt_sighash": [...],
        "dom_subtree": int}}, "modules": [...], "folders": [...], "namespaces": [...]}`` or a flat mapping
        ``{name: hash_or_obj}``."""
        with open(path, "r", encoding="utf-8") as f:
            raw = json.load(f)
        if not isinstance(raw, dict):
            raise ValueError(f"{path}: expected JSON object")
        decls_map = raw.get("decls") if isinstance(raw.get("decls"), dict) else raw
        names: dict = {}
        for plural, singular in (("modules", "module"), ("folders", "folder"), ("namespaces", "namespace")):
            if isinstance(raw.get(plural), (list, tuple)):
                names[singular] = [x for x in raw[plural] if isinstance(x, str)]
        rows: list = []
        subtrees: dict = {}
        for k, v in decls_map.items():
            if k in ("schema", "generated_utc", "project", "modules", "folders", "namespaces", "decls"):
                continue
            if isinstance(v, str):
                rows.append((k, (v,)))
            elif isinstance(v, (list, tuple)):
                rows.append((k, tuple(x for x in v if isinstance(x, str))))
            elif isinstance(v, dict):
                hs: list = []
                if isinstance(v.get("sighash"), str) and v["sighash"]:
                    hs.append(v["sighash"])
                for ah in v.get("alt_sighash") or v.get("hashes") or ():
                    if isinstance(ah, str) and ah and ah not in hs:
                        hs.append(ah)
                rows.append((k, tuple(hs)))
                ds = v.get("dom_subtree") if "dom_subtree" in v else v.get("subtree_size")
                if isinstance(ds, int) and ds > 0:
                    subtrees[k] = ds
        return cls(rows, names=names, label=label or path, restrict_to=restrict_to), subtrees


def reanchor(pack: Pack, graph: GraphIndex, layers: Optional[Iterable[str]] = None) -> dict:
    """Re-anchoring report of ``pack`` against ``graph``.  Pure: changes nothing.

    Hashes are only ever compared within one scheme.  Per record ``status``:
      ``exact``      name present and the primary sighash is among the graph's hashes for it (or,
                     when the graph has no hash of the primary's scheme, an alt_sighash is);
      ``name_only``  name present but not confirmed by hash -- ``reason`` is ``signature_changed``
                     (same scheme, different hash), ``unhashed_annotation``, ``unhashed_graph``,
                     ``no_common_scheme`` or ``non_decl_target`` (module / folder / namespace
                     targets anchor by name only);
      ``hash_only``  name absent, a recorded hash present under other name(s) = rename with an
                     unchanged signature; ``candidates`` lists them (``via`` = the hash that hit,
                     ``via_primary``), ``resolved_name`` is set only when exactly one candidate
                     exists (``unique: true``);
      ``orphan``     neither name nor hash found;
      ``unchecked``  the graph carries no name table for this target type (nothing is claimed).
    """
    want = None if layers is None else set(layers)
    entries: list = []
    counts = {s: 0 for s in STATUSES}
    for key in sorted(pack.annots, key=_sort_key):
        layer, target, name, sighash, slot = key
        if want is not None and layer not in want:
            continue
        rec = pack.annots[key]
        hashes = record_hashes(rec)
        e: dict = {"id": key_id(key), "layer": layer, "target": target, "name": name, "sighash": sighash or None}
        if slot:
            e["slot"] = slot
        if target != "decl":
            pool = graph.names.get(target)
            if pool is None:
                e.update(status=STATUS_UNCHECKED, reason="no_" + target + "_table")
            elif name in pool:
                e.update(status=STATUS_NAME_ONLY, reason="non_decl_target")
            else:
                e.update(status=STATUS_ORPHAN, reason="name_not_found")
        elif name in graph.hashes_of:
            g = graph.hashes_of[name]
            gschemes = {_scheme(h) for h in g}
            if not hashes:
                e.update(status=STATUS_NAME_ONLY, reason="unhashed_annotation", graph_sighashes=list(g))
            elif not g:
                e.update(status=STATUS_NAME_ONLY, reason="unhashed_graph")
            elif sighash in g:
                e.update(status=STATUS_EXACT, via=sighash, via_primary=True)
            elif _scheme(sighash) in gschemes:
                e.update(status=STATUS_NAME_ONLY, reason="signature_changed", graph_sighashes=list(g))
            else:
                hit = [h for h in hashes[1:] if h in g]
                if hit:
                    e.update(status=STATUS_EXACT, via=hit[0], via_primary=False)
                elif any(_scheme(h) in gschemes for h in hashes[1:]):
                    e.update(status=STATUS_NAME_ONLY, reason="signature_changed", graph_sighashes=list(g))
                else:
                    e.update(status=STATUS_NAME_ONLY, reason="no_common_scheme", graph_sighashes=list(g))
        else:
            hit = next((h for h in hashes if h in graph.names_of), None)
            if hit is not None:
                cands = graph.names_of[hit]
                e.update(status=STATUS_HASH_ONLY, via=hit, via_primary=hit == sighash,
                         candidates=list(cands[:50]), candidate_count=len(cands), unique=len(cands) == 1)
                if len(cands) == 1:
                    e["resolved_name"] = cands[0]
                    e["graph_sighashes"] = list(graph.hashes_of.get(cands[0], ()))
            else:
                e.update(status=STATUS_ORPHAN, reason="name_and_hash_not_found" if hashes else "name_not_found")
        counts[e["status"]] += 1
        entries.append(e)
    return {"graph": graph.label, "total": len(entries), "counts": counts, "entries": entries}


def _set_hashes(rec: dict, g: Sequence[str], prefer_scheme: Optional[str] = None) -> None:
    g = list(g)
    primary = next((h for h in g if prefer_scheme and _scheme(h) == prefer_scheme), g[0])
    rec["sighash"] = primary
    rec["alt_sighash"] = [h for h in g if h != primary]


def rebind(pack: Pack, report: Mapping[str, Any], *, now: str, accept_signature_change: bool = False,
           fill_missing_hash: bool = True, accept_alt_hash: bool = False) -> dict:
    """Apply a ``reanchor`` report to a copy of ``pack``.

    * ``hash_only`` + unique + hit on the primary sighash -> the record follows the rename (old
      name appended to ``was``); a hit on an alt hash only (e.g. the name-abstracted variant) is
      weaker evidence and is followed only with ``accept_alt_hash=True``;
    * ``name_only/unhashed_annotation`` -> the graph's hashes are filled in (``fill_missing_hash``);
    * ``name_only/signature_changed`` -> re-keyed to the new hash only with
      ``accept_signature_change=True`` (the statement changed: a human should re-read the note);
    * ambiguous ``hash_only``, ``orphan`` and ``unchecked`` records are left untouched and listed
      in ``skipped``.
    A re-keyed record that would land on an existing different record is a conflict, not an overwrite.
    Returns ``{"pack", "moved", "skipped", "conflicts"}``."""
    out = pack.copy()
    by_id = {key_id(k): k for k in out.annots}
    res: dict = {"pack": out, "moved": [], "skipped": [], "conflicts": []}
    for e in report["entries"]:
        key = by_id.get(e["id"])
        if key is None or e["status"] == STATUS_EXACT:
            continue
        if e["status"] == STATUS_NAME_ONLY and e.get("reason") == "non_decl_target":
            continue
        rec = dict(out.annots[key])
        if e["status"] == STATUS_HASH_ONLY and e.get("unique") and (e.get("via_primary") or accept_alt_hash):
            rec["was"] = sorted(set(rec.get("was", [])) | {rec["name"]})
            rec["name"] = e["resolved_name"]
        elif e["status"] == STATUS_NAME_ONLY and e.get("reason") == "unhashed_annotation" \
                and fill_missing_hash and e.get("graph_sighashes"):
            _set_hashes(rec, e["graph_sighashes"])
        elif e["status"] == STATUS_NAME_ONLY and e.get("reason") == "signature_changed" and accept_signature_change:
            _set_hashes(rec, e["graph_sighashes"], _scheme(rec["sighash"]))
        else:
            res["skipped"].append({"id": e["id"], "status": e["status"], "reason": e.get("reason", "ambiguous")})
            continue
        rec["updated"] = max(now, rec["updated"])
        rec = normalize_annot(rec)
        new_key = record_key(rec)
        errs = check_annot(rec, out.layers.get(rec["layer"]))
        if errs or (new_key in out.annots and new_key != key):
            res["conflicts"].append({"id": e["id"], "kind": "invalid" if errs else "key_collision",
                                     "would_be": key_id(new_key), "errors": [m for _, m in errs]})
            continue
        del out.annots[key]
        out.annots[new_key] = rec
        res["moved"].append({"id": e["id"], "new_id": key_id(new_key), "status": e["status"],
                             "name": rec["name"], "sighash": rec.get("sighash")})
    return res


# ----------------------------------------------------------------------------------------------
# Directory store (annotations/): one canonical file per layer
# ----------------------------------------------------------------------------------------------

def layer_filename(layer: str) -> str:
    if not LAYER_RE.match(layer):
        raise PackError([_issue("bad_layer", f"layer id {layer!r} must match {LAYER_RE.pattern}")])
    return layer.replace("/", "__") + ".jsonl"


class PackStore:
    """A directory of packs, one file per layer (``<layer with '/' -> '__'>.jsonl``).

    This is the write path for the workbench: every mutation validates, reports conflicts instead
    of overwriting, and rewrites only the affected layer file(s), atomically, in canonical form.
    File names are derived from validated layer ids only (no caller-supplied paths)."""

    def __init__(self, root: str) -> None:
        self.root = os.path.abspath(root)

    def files(self) -> list:
        if not os.path.isdir(self.root):
            return []
        return sorted(os.path.join(self.root, f) for f in os.listdir(self.root)
                      if f.endswith(".jsonl") and not f.startswith("."))

    def load(self) -> tuple:
        """-> (Pack, issues).  Issues carry a ``file`` key.  Cross-file disagreements are reported as
        ``conflict`` / ``layer_conflict`` issues (first file in name order wins, nothing is merged over)."""
        pack = Pack()
        issues: list = []
        for path in self.files():
            with open(path, "rb") as f:
                p, iss = parse(f.read())
            rel = os.path.basename(path)
            for i in iss:
                i["file"] = rel
                issues.append(i)
            m = merge(pack, p)
            for c in m["conflicts"]:
                code = "layer_conflict" if c["kind"] == "layer" else "conflict"
                i = _issue(code, f"{c['id']} differs from an earlier file ({', '.join(c['fields']) or c['kind']})")
                i["file"] = rel
                issues.append(i)
            pack = m["pack"]
        return pack, issues

    def _save_layers(self, pack: Pack, layers: Iterable[str]) -> list:
        written = []
        for lid in sorted(set(layers)):
            path = os.path.join(self.root, layer_filename(lid))
            if lid in pack.layers:
                dump(pack, path, layers=[lid])
                written.append(os.path.basename(path))
        return written

    def save(self, pack: Pack) -> list:
        errs = errors_of(parse(dumps(pack))[1])
        if errs:
            raise PackError(errs)
        return self._save_layers(pack, pack.layers)

    def export_text(self, layers: Optional[Iterable[str]] = None) -> str:
        pack, issues = self.load()
        if errors_of(issues):
            raise PackError(errors_of(issues))
        return dumps(pack, layers)

    def import_text(self, text: str, resolve: Optional[Mapping[str, str]] = None, dry_run: bool = False) -> dict:
        """Merge an uploaded pack into the store.  Writes only when there is no unresolved conflict
        (and not ``dry_run``).  Returns the ``merge`` report (JSON-ready, without ``pack``) plus
        ``written`` (file names) and ``applied``."""
        theirs = loads(text)
        ours, issues = self.load()
        if errors_of(issues):
            raise PackError(errors_of(issues))
        m = merge(ours, theirs, resolve)
        pack = m.pop("pack")
        m["written"], m["applied"] = [], False
        if m["ok"] and not dry_run:
            touched = set(m["layers_added"]) | {k[0] for k in pack.annots if pack.annots[k] != ours.annots.get(k)}
            touched |= {l for l in pack.layers if pack.layers[l] != ours.layers.get(l)}
            m["written"] = self._save_layers(pack, touched)
            m["applied"] = True
        return m

    def ensure_layer(self, layer: str, kind: str = "human", title: str = "", description: str = "",
                     default_on: Optional[bool] = None) -> dict:
        pack, issues = self.load()
        if errors_of(issues):
            raise PackError(errors_of(issues))
        if layer in pack.layers and not title and not description and default_on is None \
                and pack.layers[layer]["kind"] == kind:
            return pack.layers[layer]
        rec = pack.add_layer(layer, kind, title, description, default_on)
        self._save_layers(pack, [layer])
        return rec

    def upsert(self, fields: Mapping[str, Any], *, now: Optional[str] = None,
               expect_updated: Optional[str] = None) -> dict:
        """Create or edit one annotation.  ``fields`` = annotation fields without timestamps.

        Create: the key must not exist (else ConflictError).  Edit: pass ``expect_updated`` = the
        ``updated`` value the editor loaded; a mismatch (someone else changed it) is a ConflictError,
        never a silent overwrite.  ``created`` is preserved on edit.  Returns the stored record + ``id``."""
        now = now or utc_now()
        pack, issues = self.load()
        if errors_of(issues):
            raise PackError(errors_of(issues))
        rec = normalize_annot({k: v for k, v in fields.items() if k not in ("created", "updated", "id", "display_tag")})
        if isinstance(rec.get("tag"), str):
            rec["tag"] = rec["tag"].strip("[]")
        for k in ("layer", "name"):
            if not isinstance(rec.get(k), str):
                raise PackError([_issue("missing_" + k, f"missing mandatory field {k!r}")])
        key = record_key(rec)
        old = pack.annots.get(key)
        if old is None:
            if expect_updated is not None:
                raise ConflictError([_issue("conflict", f"record {key_id(key)} no longer exists")])
            rec["created"] = rec["updated"] = now
        else:
            if expect_updated is None:
                raise ConflictError([_issue("conflict", f"record {key_id(key)} already exists; pass "
                                                         "expect_updated to edit it")])
            if expect_updated != old["updated"]:
                raise ConflictError([_issue("conflict", f"record {key_id(key)} was changed at {old['updated']} "
                                                         f"(you loaded {expect_updated})")])
            rec["created"] = old["created"]
            rec["updated"] = max(now, old["updated"])
        stored = pack.put(rec, replace=True)
        self._save_layers(pack, [key[0]])
        return dict(stored, id=key_id(key))

    def delete(self, rid: str, *, expect_updated: str) -> dict:
        pack, issues = self.load()
        if errors_of(issues):
            raise PackError(errors_of(issues))
        for key, rec in pack.annots.items():
            if key_id(key) == rid:
                if rec["updated"] != expect_updated:
                    raise ConflictError([_issue("conflict", f"record {rid} was changed at {rec['updated']}")])
                del pack.annots[key]
                self._save_layers(pack, [key[0]])
                return rec
        raise KeyError(rid)


# ----------------------------------------------------------------------------------------------
# Contributor PR checks, Treemap Overlay compiler & Template generator
# ----------------------------------------------------------------------------------------------

_CONTRIB_SLUG_RE = re.compile(r"^[a-z0-9][a-z0-9_-]{0,63}$")
_CONTRIB_FILE_RE = re.compile(r"^([a-z0-9][a-z0-9._-]{0,62})__([a-z0-9][a-z0-9._-]{0,62})\.jsonl$")
_SHA40_RE = re.compile(r"^[0-9a-f]{40}$")
_GH_LINK_RE = re.compile(
    r"(https?)://github\.com/([A-Za-z0-9_.-]+)/([A-Za-z0-9_.-]+)/(blob|tree|raw|commits?)/([^/#?\s\"')>\]]+)"
)
_GH_AT_RE = re.compile(r"\b([A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+)@([A-Za-z0-9_.-]+)")
_GH_URL_EXTRACT_RE = re.compile(r"https://github\.com/[^\s;\"')>\]]+")

_REPO_ALIASES = {
    "deicyde/riemann-hypothesis": "leanprover-community/riemann-hypothesis",
}

_OVERCLAIM_RE = re.compile(
    r"\b(?:"
    r"RH\s+(?:is|has\s+been)\s+(?:now\s+)?(?:proved|proven|solved|settled|established|verified)"
    r"|(?:proves|proved|proven|solves|solved|settles|settled|establishes|established)\s+(?:the\s+)?"
    r"(?:RH|GRH|ERH|Riemann\s+Hypothesis|Generalized\s+Riemann\s+Hypothesis|Extended\s+Riemann\s+Hypothesis)"
    r"|(?:Riemann\s+Hypothesis|Generalized\s+Riemann\s+Hypothesis|Extended\s+Riemann\s+Hypothesis|GRH|ERH)\s+"
    r"(?:is|has\s+been)\s+(?:now\s+)?(?:proved|proven|solved|settled|established|verified)"
    r"|proof\s+of\s+(?:the\s+)?(?:RH|GRH|Riemann\s+Hypothesis)\s+is\s+(?:complete|valid|correct|verified|sound)"
    r"|(?:unconditionally|completely|fully)\s+(?:proves|proved|verifies|verified)\s+(?:the\s+)?"
    r"(?:RH|GRH|Riemann\s+Hypothesis)"
    r"|verified\s+(?:the\s+)?(?:RH|Riemann\s+Hypothesis)"
    r"|(?:Navier[-–]Stokes|millennium\s+prize(?:\s+problem)?)\s+(?:is|has\s+been)\s+(?:solved|proved|proven|settled)"
    r")\b",
    re.I,
)

_LEAN_BY_RE = re.compile(r":=\s*by\b")
_LEAN_FENCE_RE = re.compile(r"```+\s*(?:lean4?|lean)?", re.I)
_LEAN_IMPORT_HEAD_RE = re.compile(r"^\s*import\s+[A-Z][A-Za-z0-9_.]*\s*$", re.M)
_LEAN_STMT_LINE_RE = re.compile(
    r"^\s*(?:"
    r"import\s+[A-Z][\w.]*"
    r"|open(?:\s+scoped)?\s+[A-Z][\w.]*"
    r"|namespace\s+[A-Za-z_][\w.]*"
    r"|end\s+[A-Za-z_][\w.]*"
    r"|set_option\s+\w+"
    r"|@\[[^\]]+\]"
    r"|(?:private\s+|protected\s+|noncomputable\s+|unsafe\s+|partial\s+)*(?:theorem|lemma|def|abbrev|structure|inductive|instance|axiom|opaque)\s+[A-Za-z_«]"
    r"|(?:have|suffices|obtain|rcases|induction|cases|refine|exact|apply|rw|simp|simp_all|omega|linarith|ring|aesop)\b"
    r"|\|\s*[A-Za-z0-9_'.⟨]+\s*=>"
    r")"
)

_NEGATIVE_VERDICTS = frozenset({"flagged", "suspect", "degenerate", "vacuous", "broken", "false", "disproved"})
_POSITIVE_VERDICTS = frozenset({"real", "verified", "sound", "ok", "clean"})


def _parse_gallery_toml_fallback(text: str) -> dict:
    projects: list = []
    cur: Optional[dict] = None
    for raw in text.splitlines():
        line = raw.split("#", 1)[0].strip()
        if not line:
            continue
        if line == "[[projects]]":
            cur = {}
            projects.append(cur)
            continue
        if cur is not None and "=" in line:
            k, v = [x.strip() for x in line.split("=", 1)]
            if len(v) >= 2 and v[0] == '"' and v[-1] == '"':
                cur[k] = v[1:-1]
            elif v in ("true", "false"):
                cur[k] = v == "true"
    return {"projects": projects}


def load_gallery_registry(config_path: Optional[str] = None) -> tuple:
    """Load ``leanre_gallery.toml`` -> ``(projects_by_slug, repo_to_pinned_sha, explicit_file_loaded)``."""
    default_cfg = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "leanre_gallery.toml")
    chosen = config_path if (config_path and os.path.isfile(config_path)) else (default_cfg if os.path.isfile(default_cfg) else None)
    projects: dict = {}
    repo_commits: dict = {}
    if not chosen:
        return projects, repo_commits, False
    with open(chosen, "rb") as f:
        raw = f.read()
    try:
        import tomllib  # type: ignore[import-not-found]
        doc = tomllib.loads(raw.decode("utf-8"))
    except ImportError:
        doc = _parse_gallery_toml_fallback(raw.decode("utf-8"))
    for p in doc.get("projects", []):
        if not isinstance(p, dict) or not isinstance(p.get("slug"), str):
            continue
        slug = p["slug"]
        projects[slug] = dict(p)
        rurl = p.get("repo_url", "")
        sha = p.get("pinned_commit", "")
        m = re.match(r"^https://github\.com/([^/]+/[^/#?]+?)(?:\.git)?/?$", rurl)
        if m and isinstance(sha, str) and sha:
            repo_key = m.group(1).lower()
            repo_commits[repo_key] = sha
    for alias, target in _REPO_ALIASES.items():
        if target in repo_commits:
            repo_commits[alias] = repo_commits[target]
    return projects, repo_commits, bool(config_path and os.path.isfile(config_path))


def _sanitize_slug(raw: str, fallback: str = "item") -> str:
    s = raw.strip().lstrip("@").lower()
    s = s.replace(":", "-")
    s = re.sub(r"[^a-z0-9._-]+", "-", s).strip("._-")
    return (s[:48] or fallback)


def _author_owner_slugs(author: str) -> set:
    a = author.strip().lstrip("@")
    out = {_sanitize_slug(a, "")}
    for pref in BOT_AUTHOR_PREFIXES:
        if a.lower().startswith(pref):
            rest = _sanitize_slug(a[len(pref):], "")
            tag = pref[:-1]
            if rest:
                out.add(rest)
                out.add(f"{tag}-{rest}")
                out.add(f"{tag}.{rest}")
    # Also match underscore <-> hyphen equivalence for GitHub handles
    expanded = set()
    for s in out:
        if s:
            expanded.add(s)
            expanded.add(s.replace("_", "-"))
    return expanded


def _has_lean_paste(text: str) -> Optional[str]:
    if not isinstance(text, str) or not text:
        return None
    if _LEAN_BY_RE.search(text):
        return "contains Lean tactic proof block ':= by'"
    if _LEAN_FENCE_RE.search(text):
        return "contains fenced code block (do not paste .lean snippets)"
    lines = [ln for ln in text.splitlines() if ln.strip()]
    if len(lines) >= 2:
        if _LEAN_IMPORT_HEAD_RE.search(text):
            return "contains multi-line Lean 'import ...' snippet"
        lean_lines = sum(1 for ln in lines if _LEAN_STMT_LINE_RE.match(ln))
        if lean_lines >= 2:
            return f"contains multi-line Lean code/tactic snippet ({lean_lines} lines)"
    return None


def _check_github_pins(text: str, repo_commits: Mapping[str, str]) -> list:
    errs: list = []
    if not isinstance(text, str) or not text:
        return errs
    for m in _GH_LINK_RE.finditer(text):
        scheme, owner, repo, _kind, ref = m.groups()
        repo_clean = repo[:-4] if repo.endswith(".git") else repo
        key = _REPO_ALIASES.get(f"{owner}/{repo_clean}".lower(), f"{owner}/{repo_clean}".lower())
        if scheme.lower() != "https":
            errs.append(("unpinned_url", f"GitHub link must use https:// (got {m.group(0)})"))
        if not _SHA40_RE.match(ref):
            errs.append(("unpinned_url", f"GitHub link uses non-pinned ref {ref!r} (expected 40-hex commit SHA)"))
            continue
        want = repo_commits.get(key)
        if want and _SHA40_RE.match(want) and ref != want:
            errs.append(("wrong_pinned_sha", f"GitHub SHA {ref[:12]}... for {owner}/{repo_clean} != gallery pinned_commit {want}"))
    for m in _GH_AT_RE.finditer(text):
        raw_repo, ref = m.groups()
        key = _REPO_ALIASES.get(raw_repo.lower(), raw_repo.lower())
        if key not in repo_commits:
            continue
        if not _SHA40_RE.match(ref):
            errs.append(("unpinned_url", f"citation {m.group(0)!r} uses non-pinned ref {ref!r} (expected 40-hex commit SHA)"))
            continue
        want = repo_commits[key]
        if _SHA40_RE.match(want) and ref != want:
            errs.append(("wrong_pinned_sha", f"citation SHA {ref[:12]}... for {raw_repo} != gallery pinned_commit {want}"))
    return errs


def infer_entry_status(rec: Mapping[str, Any], layer_def: Mapping[str, Any]) -> str:
    """Normalize an annotation's review status into ``verified | read | summary | flagged``."""
    is_draft = bool(rec.get("draft") or layer_def.get("kind") in DRAFT_LAYER_KINDS)
    ex = rec.get("extra") if isinstance(rec.get("extra"), dict) else {}
    raw_st = str(rec.get("status") or ex.get("status") or "").strip().lower()
    raw_vd = str(rec.get("verdict") or ex.get("verdict") or "").strip().lower()
    if raw_st in ("flagged", "suspect", "broken", "issue") or raw_vd in ("flagged", "suspect", "broken"):
        return "flagged"
    if not rec.get("status") and raw_vd in ("degenerate", "vacuous"):
        return "flagged"
    if raw_st == "verified":
        return "read" if is_draft else "verified"
    if raw_st == "read":
        return "read"
    if raw_st in ("summary", "partial", "opaque"):
        return "summary"
    if not is_draft:
        return "verified" if rec.get("tag") in ("L", "S") else "read"
    return "summary"


def _overlay_layer_kind(kind: str) -> str:
    return "human-review" if kind == "human" else kind


def _load_dom_subtrees(kernel_db: str, names: Sequence[str]) -> dict:
    if not names or not os.path.isfile(kernel_db):
        return {}
    import sqlite3
    out: dict = {}
    conn = sqlite3.connect("file:" + os.path.abspath(kernel_db) + "?mode=ro", uri=True)
    try:
        tables = {r[0] for r in conn.execute("SELECT name FROM sqlite_master WHERE type='table'")}
        if "decls" in tables and "dom" in tables:
            sql = "SELECT d.name, dom.subtree_size FROM decls d JOIN dom ON dom.decl_id = d.decl_id WHERE dom.tree_id = 0 AND d.name IN"
            for name, sz in GraphIndex._chunked_in(conn, sql, sorted(set(names))):
                if isinstance(sz, int) and sz > 0:
                    out[name] = sz
    except sqlite3.Error:
        return {}
    finally:
        conn.close()
    return out


def _tiny_demo_graph(repo_root: str, restrict_to: Optional[Pack] = None) -> Optional[GraphIndex]:
    demo_ndjson = os.path.join(repo_root, "examples", "tiny_demo", "demo.ndjson")
    if not os.path.isfile(demo_ndjson):
        return None
    try:
        import sighash as _sh
    except ImportError:
        return None
    rows = [(r["name"], ("k1n:" + r["k1n"].hex(), "k1a:" + r["k1a"].hex()))
            for r in _sh.kernel_sighashes(demo_ndjson)]
    return GraphIndex(rows, label=demo_ndjson, restrict_to=restrict_to)


def discover_contrib_files(contrib_root: str) -> list:
    if not os.path.isdir(contrib_root):
        return []
    found: list = []
    for dp, dn, fn in os.walk(contrib_root):
        dn.sort()
        for f in sorted(fn):
            if f in (".gitkeep", "README.md") or f.startswith(".annot-"):
                continue
            found.append(os.path.join(dp, f))
    return sorted(found)


def check_pr(
    files: Sequence[str] = (),
    *,
    all_contrib: bool = False,
    contrib_root: str = "annotations/contrib",
    gallery_config: Optional[str] = None,
    kernel_db: Optional[str] = None,
    leanre_db: Optional[str] = None,
    anchors_path: Optional[str] = None,
    allow_shared: bool = False,
    strict: bool = False,
    max_bytes: int = MAX_PR_PACK_BYTES,
) -> dict:
    """Validate contributor PR annotation packs without requiring kernel.db on CI runners.

    Returns ``{"ok": bool, "anchor_mode": str, "files": [...], "issues": [...], "totals": {...}}``."""
    abs_contrib = os.path.abspath(contrib_root)
    inferred_repo = os.path.dirname(os.path.dirname(abs_contrib))
    local_gallery = gallery_config or (
        os.path.join(inferred_repo, "leanre_gallery.toml")
        if os.path.isfile(os.path.join(inferred_repo, "leanre_gallery.toml")) else None
    )
    projects, repo_commits, strict_projects = load_gallery_registry(local_gallery)
    if local_gallery and os.path.isfile(local_gallery):
        strict_projects = True

    targets = list(files)
    if all_contrib:
        for p in discover_contrib_files(contrib_root):
            if p not in targets:
                targets.append(p)

    # Seed layers in top-level annotations/ cannot be hijacked by contrib packs
    annot_parent = os.path.dirname(abs_contrib)
    reserved_layers: dict = {}
    if os.path.isdir(annot_parent):
        for seed_path in PackStore(annot_parent).files():
            try:
                sp = load(seed_path)
                for lid in sp.layers:
                    reserved_layers[lid] = os.path.basename(seed_path)
            except PackError:
                pass

    kdb = kernel_db or (
        os.path.join(inferred_repo, "outputs", "kernel", "kernel.db")
        if os.path.isfile(os.path.join(inferred_repo, "outputs", "kernel", "kernel.db")) else None
    )
    ldb = leanre_db or (
        os.path.join(inferred_repo, "outputs", "leanre.db")
        if os.path.isfile(os.path.join(inferred_repo, "outputs", "leanre.db")) else None
    )
    anc = anchors_path or (
        os.path.join(inferred_repo, "outputs", "annot_anchors.json")
        if os.path.isfile(os.path.join(inferred_repo, "outputs", "annot_anchors.json")) else None
    )
    if kdb and os.path.isfile(kdb):
        anchor_mode = f"kernel_db ({os.path.relpath(kdb, inferred_repo) if os.path.commonpath([os.path.abspath(kdb), inferred_repo]) == inferred_repo else kdb})"
    elif anc and os.path.isfile(anc):
        anchor_mode = f"anchors_json ({os.path.basename(anc)})"
    else:
        anchor_mode = "offline (kernel.db / annot_anchors.json not present; format + SHA checks active)"

    seen_contrib_layers: dict = {}  # lid -> (rel_display, file_author_slug, lrec)
    seen_contrib_keys: dict = {}    # record_key -> (rel_display, rec)
    file_reports: list = []
    all_issues: list = []

    for raw_path in targets:
        f_issues: list = []

        def add_f(code: str, msg: str, line: int = 0, severity: str = "error") -> None:
            item = {"file": str(raw_path), "line": line, "code": code, "severity": severity, "msg": msg}
            f_issues.append(item)
            all_issues.append(item)

        raw_str = str(raw_path)
        segs = re.split(r"[\\/]+", raw_str)
        has_traversal = (".." in segs) or ("\x00" in raw_str) or ("\\" in raw_str)
        abs_path = os.path.abspath(raw_str) if "\x00" not in raw_str else ""
        inside_contrib = False
        if abs_path:
            try:
                inside_contrib = os.path.commonpath([abs_contrib, abs_path]) == abs_contrib and abs_path != abs_contrib
            except ValueError:
                inside_contrib = False

        if has_traversal:
            add_f("path_traversal", f"path {raw_str!r} contains '..' or forbidden path separators")
        elif not inside_contrib:
            add_f("bad_path", f"pack {raw_str!r} must live under {contrib_root}/<project_slug>/<author>__<slug>.jsonl")

        project_slug = ""
        file_author_slug = ""
        rel_display = raw_str
        if inside_contrib and not has_traversal:
            rel_contrib = os.path.relpath(abs_path, abs_contrib).replace(os.sep, "/")
            rel_display = "annotations/contrib/" + rel_contrib
            parts = rel_contrib.split("/")
            if len(parts) != 2:
                add_f("bad_path", f"expected annotations/contrib/<project_slug>/<author>__<slug>.jsonl (got {rel_display!r})")
            else:
                project_slug, fname = parts
                if not _CONTRIB_SLUG_RE.match(project_slug):
                    add_f("bad_path", f"invalid project slug {project_slug!r}")
                elif strict_projects and projects and project_slug not in projects:
                    add_f("unknown_project", f"project slug {project_slug!r} not in leanre_gallery.toml ({sorted(projects)})")
                m_fn = _CONTRIB_FILE_RE.match(fname)
                if not m_fn:
                    add_f("bad_filename", f"filename {fname!r} must match <author_slug>__<pack_slug>.jsonl")
                else:
                    file_author_slug = m_fn.group(1)

        if has_traversal or not abs_path:
            file_reports.append({
                "file": rel_display, "project": project_slug, "layer": "-", "kind": "-",
                "trust_tier": "-", "entries": 0, "distinct_decls": 0,
                "status_counts": {k: 0 for k in OVERLAY_STATUSES},
                "subtree_coverage_delta": None, "ok": False, "issues": f_issues,
            })
            continue

        if os.path.islink(abs_path) or os.path.islink(os.path.dirname(abs_path)):
            add_f("symlink_forbidden", "symlinks are not permitted in annotations/contrib/")
            file_reports.append({
                "file": rel_display, "project": project_slug, "layer": "-", "kind": "-",
                "trust_tier": "-", "entries": 0, "distinct_decls": 0,
                "status_counts": {k: 0 for k in OVERLAY_STATUSES},
                "subtree_coverage_delta": None, "ok": False, "issues": f_issues,
            })
            continue

        if not os.path.isfile(abs_path):
            add_f("missing_file", f"file does not exist: {raw_str}")
            file_reports.append({
                "file": rel_display, "project": project_slug, "layer": "-", "kind": "-",
                "trust_tier": "-", "entries": 0, "distinct_decls": 0,
                "status_counts": {k: 0 for k in OVERLAY_STATUSES},
                "subtree_coverage_delta": None, "ok": False, "issues": f_issues,
            })
            continue

        sz = os.path.getsize(abs_path)
        if sz > max_bytes:
            add_f("pack_too_large", f"file size {sz:,} B exceeds {max_bytes:,} B (2 MiB) PR pack limit")

        with open(abs_path, "rb") as f:
            raw_bytes = f.read()

        # Pre-scan raw JSON lines to catch explicit draft=false / missing draft before normalization strips False
        raw_objs: list = []
        try:
            decoded_text = raw_bytes.decode("utf-8")
            for ln_no, raw_ln in enumerate(decoded_text.splitlines(), 1):
                s_ln = raw_ln.strip()
                if not s_ln or _CONFLICT_MARK_RE.match(s_ln):
                    continue
                try:
                    o = json.loads(s_ln)
                    if isinstance(o, dict):
                        raw_objs.append((ln_no, o))
                except ValueError:
                    pass
        except UnicodeDecodeError:
            pass

        pack, parse_issues = parse(raw_bytes)
        val_issues = validate_text(raw_bytes, canonical=True)
        for iss in val_issues:
            sev = "error" if (iss["severity"] == "error" or strict) else "warning"
            add_f(iss["code"], iss["msg"], iss.get("line", 0), sev)

        # Raw trust check (catches AI/bot packseven if layer kind was forged or draft: false was stripped)
        file_looks_bot = file_author_slug.startswith(("ai-", "ai.", "bot-", "bot."))
        raw_layers = {o.get("layer"): (ln, o) for ln, o in raw_objs if o.get("type") == "layer" and isinstance(o.get("layer"), str)}
        for ln_no, o in raw_objs:
            if o.get("type") == "layer":
                lkind = o.get("kind")
                lid = str(o.get("layer") or "")
                is_bot_layer = lkind in DRAFT_LAYER_KINDS or lid.startswith(("ai/", "bot/")) or file_looks_bot
                if is_bot_layer:
                    if lkind not in DRAFT_LAYER_KINDS:
                        add_f("ai_in_human_layer", f"AI/bot pack layer {lid!r} must use kind 'ai-draft' or 'bot-check' (got {lkind!r})", ln_no)
                    if o.get("default_on") is not False:
                        if not any(x["code"] == "ai_draft_default_on" and x["line"] == ln_no for x in f_issues):
                            add_f("ai_draft_default_on", f"AI/bot layer {lid!r} must set default_on=false", ln_no)
            elif o.get("type") == "annot":
                auth = str(o.get("author") or "")
                lid = str(o.get("layer") or "")
                l_info = raw_layers.get(lid, (0, {}))[1]
                is_bot_rec = (
                    any(auth.startswith(p) for p in BOT_AUTHOR_PREFIXES)
                    or l_info.get("kind") in DRAFT_LAYER_KINDS
                    or lid.startswith(("ai/", "bot/"))
                    or file_looks_bot
                )
                if is_bot_rec and o.get("draft") is not True:
                    if not any(x["code"] == "draft_unmarked" and x["line"] == ln_no for x in f_issues):
                        add_f("draft_unmarked", "AI/bot annotation records must set \"draft\": true", ln_no)
                if l_info.get("kind") == "ai-draft":
                    raw_st = str(o.get("status") or (o.get("extra") or {}).get("status") or "").strip().lower()
                    if raw_st == "verified":
                        add_f("ai_verified_claim", "AI-draft records cannot claim status='verified'", ln_no)

        if not pack.layers:
            add_f("empty_layers", "pack declares no layer lines")
        if len(pack) == 0:
            add_f("empty_pack", "pack contains 0 annotation records")

        for lid, lrec in pack.layers.items():
            if lid in reserved_layers:
                add_f("duplicate_contrib_layer", f"layer {lid!r} is already owned by seed pack {reserved_layers[lid]}")
            elif lid in seen_contrib_layers and seen_contrib_layers[lid][0] != rel_display:
                prev_file, prev_owner, prev_lrec = seen_contrib_layers[lid]
                if not allow_shared and prev_owner != file_author_slug:
                    add_f("duplicate_contrib_layer", f"layer {lid!r} is already owned by {prev_file}")
                elif prev_lrec != lrec:
                    add_f("layer_conflict", f"layer {lid!r} definition differs from {prev_file}")
            else:
                seen_contrib_layers[lid] = (rel_display, file_author_slug, lrec)
            for fld in ("title", "description"):
                txt = lrec.get(fld, "")
                if txt and _OVERCLAIM_RE.search(txt):
                    add_f("overclaim", f"layer {fld} contains disallowed overclaim phrase: {_OVERCLAIM_RE.search(txt).group(0)!r}")
                paste = _has_lean_paste(txt)
                if paste:
                    add_f("lean_proof_paste", f"layer {fld} {paste}")

        for rkey, rec in pack.annots.items():
            if rkey in seen_contrib_keys and seen_contrib_keys[rkey][0] != rel_display:
                prev_f, prev_rec = seen_contrib_keys[rkey]
                code = "duplicate_key" if prev_rec == rec else "conflict"
                add_f(code, f"record {rec['name']!r} in layer {rec['layer']!r} already present in {prev_f}")
            else:
                seen_contrib_keys[rkey] = (rel_display, rec)

        proj_meta = projects.get(project_slug, {})
        kernel_anchored = (
            proj_meta.get("mode") == "kernel_site"
            or proj_meta.get("category") in ("kernel", "demo")
            or project_slug in ("riemann-hypothesis", "tiny-demo")
        )

        authors_seen: set = set()
        status_counts = {k: 0 for k in OVERLAY_STATUSES}
        explicit_subtrees: dict = {}

        for ln_no, o in raw_objs:
            if o.get("type") != "annot":
                continue
            name = str(o.get("name") or "")
            target = str(o.get("target") or "decl")
            note = o.get("note")
            if not isinstance(note, str) or not note.strip():
                add_f("missing_note", f"record {name!r} in contrib pack must include a non-empty 'note'", ln_no)
            if kernel_anchored and target == "decl" and not o.get("sighash"):
                add_f("missing_sighash", f"decl {name!r} in kernel-anchored project {project_slug!r} requires 'sighash'", ln_no)

            auth = str(o.get("author") or "").strip()
            if auth:
                authors_seen.add(auth)
                if file_author_slug and not allow_shared and file_author_slug not in _author_owner_slugs(auth):
                    add_f(
                        "foreign_author",
                        f"record author {auth!r} does not match file owner {file_author_slug!r} (use your own file or --allow-shared)",
                        ln_no,
                    )

            for fld in ("note", "breaks", "rename", "source", "verdict"):
                val = o.get(fld)
                if isinstance(val, str) and val:
                    m_oc = _OVERCLAIM_RE.search(val)
                    if m_oc:
                        add_f("overclaim", f"{fld} contains disallowed overclaim phrase {m_oc.group(0)!r}", ln_no)
            for al in o.get("aliases") or ():
                if isinstance(al, str) and _OVERCLAIM_RE.search(al):
                    add_f("overclaim", f"alias contains disallowed overclaim phrase {_OVERCLAIM_RE.search(al).group(0)!r}", ln_no)

            for fld in ("note", "breaks"):
                val = o.get(fld)
                if isinstance(val, str):
                    paste = _has_lean_paste(val)
                    if paste:
                        add_f("lean_proof_paste", f"{fld} {paste}", ln_no)
            ex = o.get("extra")
            if isinstance(ex, dict):
                for ek, ev in ex.items():
                    if isinstance(ev, str):
                        paste = _has_lean_paste(ev)
                        if paste:
                            add_f("lean_proof_paste", f"extra.{ek} {paste}", ln_no)
                ds = ex.get("dom_subtree")
                if isinstance(ds, int) and ds > 0 and target == "decl" and name:
                    explicit_subtrees[name] = max(explicit_subtrees.get(name, 0), ds)

            for url_fld in (o.get("source"), o.get("url"), ex.get("url") if isinstance(ex, dict) else None, o.get("note")):
                if isinstance(url_fld, str) and url_fld:
                    for c_code, c_msg in _check_github_pins(url_fld, repo_commits):
                        add_f(c_code, c_msg, ln_no)

        if len(authors_seen) > 1 and not allow_shared:
            add_f("mixed_authors", f"pack mixes multiple authors {sorted(authors_seen)} without --allow-shared")

        # Status breakdown & optional graph anchor check
        for rec in pack.sorted_annots():
            ldef = pack.layers.get(rec["layer"], {})
            st = infer_entry_status(rec, ldef)
            status_counts[st] = status_counts.get(st, 0) + 1

        decl_names = sorted({r["name"] for r in pack.annots.values() if r.get("target", "decl") == "decl"})
        db_subtrees: dict = {}
        if len(pack) > 0:
            graph: Optional[GraphIndex] = None
            if project_slug == "tiny-demo" and not kernel_db and not anchors_path:
                graph = _tiny_demo_graph(inferred_repo, restrict_to=pack)
            elif kdb and os.path.isfile(kdb) and (project_slug in ("", "riemann-hypothesis") or kernel_db):
                graph = GraphIndex.from_kernel_db(kdb, restrict_to=pack, leanre_db=ldb)
                db_subtrees = _load_dom_subtrees(kdb, decl_names)
            elif anc and os.path.isfile(anc) and (project_slug in ("", "riemann-hypothesis") or anchors_path):
                graph, db_subtrees = GraphIndex.from_anchors_json(anc, restrict_to=pack)

            if graph is not None:
                rep = reanchor(pack, graph)
                for ent in rep["entries"]:
                    if ent["status"] == STATUS_ORPHAN:
                        add_f("anchor_orphan", f"target {ent['name']!r} ({ent.get('sighash')}) not found in {graph.label}")
                    elif ent["status"] == STATUS_NAME_ONLY and ent.get("reason") == "signature_changed":
                        add_f(
                            "anchor_hash_mismatch",
                            f"sighash mismatch for {ent['name']!r}: pack has {ent.get('sighash')}, graph has {ent.get('graph_sighashes')}",
                        )

        merged_subtrees = dict(db_subtrees)
        merged_subtrees.update(explicit_subtrees)
        cov_delta = sum(merged_subtrees[n] for n in decl_names if n in merged_subtrees) if merged_subtrees else None

        primary_lid = sorted(pack.layers)[0] if pack.layers else "-"
        primary_kind = pack.layers[primary_lid]["kind"] if primary_lid in pack.layers else "-"
        trust_tier = (
            "ai-draft" if primary_kind in DRAFT_LAYER_KINDS
            else ("human-review" if primary_kind in HUMAN_LAYER_KINDS else "-")
        )
        hard_errs = [x for x in f_issues if x["severity"] == "error" or (strict and x["severity"] == "warning")]
        file_reports.append({
            "file": rel_display,
            "project": project_slug or "unknown",
            "layer": primary_lid if len(pack.layers) <= 1 else f"{primary_lid} (+{len(pack.layers) - 1})",
            "kind": primary_kind,
            "trust_tier": trust_tier,
            "entries": len(pack),
            "distinct_decls": len(decl_names),
            "status_counts": status_counts,
            "subtree_coverage_delta": cov_delta,
            "ok": len(hard_errs) == 0,
            "issues": f_issues,
        })

    hard_total = [x for x in all_issues if x["severity"] == "error" or (strict and x["severity"] == "warning")]
    return {
        "ok": len(hard_total) == 0,
        "strict": strict,
        "anchor_mode": anchor_mode,
        "files_checked": len(file_reports),
        "files": file_reports,
        "issues": all_issues,
        "totals": {
            "entries": sum(f["entries"] for f in file_reports),
            "distinct_decls": sum(f["distinct_decls"] for f in file_reports),
            "errors": len(hard_total),
        },
    }


def format_pr_markdown_report(report: Mapping[str, Any]) -> str:
    """Format a ``check_pr`` report as a crisp GitHub-Flavored Markdown table."""
    verdict = "PASS" if report.get("ok") else "FAIL"
    lines = [
        "## Annotation PR Validation Summary",
        "",
        f"- **Result:** **{verdict}** (`{report.get('files_checked', 0)}` pack(s), "
        f"`{report.get('totals', {}).get('entries', 0)}` record(s), "
        f"`{report.get('totals', {}).get('errors', 0)}` error(s))",
        f"- **Anchor verification:** `{report.get('anchor_mode', 'offline')}`",
        "",
    ]
    files = report.get("files") or []
    if not files:
        lines.append("_No contributor packs under `annotations/contrib/` to check._\n")
        return "\n".join(lines)

    lines.extend([
        "| File | Layer | Kind | Trust tier | Entries | Distinct decls | Status (`verified/read/summary/flagged`) | Est. subtree coverage Δ | Check |",
        "|---|---|---|---|---:|---:|---|---:|---|",
    ])
    for f in files:
        sc = f.get("status_counts") or {}
        st_str = f"`{sc.get('verified', 0)} / {sc.get('read', 0)} / {sc.get('summary', 0)} / {sc.get('flagged', 0)}`"
        cov = f.get("subtree_coverage_delta")
        if cov is None:
            cov_str = "n/a"
        elif f.get("project") == "riemann-hypothesis":
            cov_str = f"+{cov:,} ({100.0 * cov / 1468414:.3f}%)"
        else:
            cov_str = f"+{cov:,}"
        chk = "PASS" if f.get("ok") else "FAIL"
        lines.append(
            f"| `{f['file']}` | `{f['layer']}` | `{f['kind']}` | `{f['trust_tier']}` | "
            f"{f['entries']} | {f['distinct_decls']} | {st_str} | {cov_str} | **{chk}** |"
        )
    issues = report.get("issues") or []
    if issues:
        lines.extend(["", "### Findings", ""])
        for iss in issues[:50]:
            loc = f"{iss['file']}:{iss['line']}" if iss.get("line") else str(iss["file"])
            lines.append(f"- **[{iss['severity'].upper()}]** `{loc}` (`{iss['code']}`): {iss['msg']}")
        if len(issues) > 50:
            lines.append(f"- _... +{len(issues) - 50} additional findings_")
    lines.append("")
    return "\n".join(lines)


def _entry_is_contested(entries: Sequence[Mapping[str, Any]]) -> bool:
    """Return True when multiple layers disagree on a target's status, verdict, or human rename."""
    if len(entries) < 2:
        return False
    layers = {e["layer"] for e in entries}
    if len(layers) < 2:
        return False
    has_flagged = any(
        e["status"] == "flagged" or str(e.get("verdict") or "").lower() in _NEGATIVE_VERDICTS
        for e in entries
    )
    has_positive = any(
        (e["status"] in ("verified", "read") and str(e.get("verdict") or "").lower() not in _NEGATIVE_VERDICTS)
        or str(e.get("verdict") or "").lower() in _POSITIVE_VERDICTS
        for e in entries
    )
    if has_flagged and has_positive:
        return True
    verdicts = {str(e.get("verdict") or "").lower() for e in entries if e.get("verdict")}
    if (verdicts & _POSITIVE_VERDICTS) and (verdicts & (_NEGATIVE_VERDICTS | {"proxy"})):
        return True
    human_renames = {e.get("rename") for e in entries if not e.get("draft") and e.get("rename")}
    if len(human_renames) > 1:
        return True
    return False


def build_overlay(
    annotations_dir: str = "annotations",
    *,
    contrib_dir: Optional[str] = None,
    project: Optional[str] = None,
    manifest_path: Optional[str] = None,
    dossiers_dir: Optional[str] = None,
    now: Optional[str] = None,
) -> dict:
    """Compile ``annotations/*.jsonl`` + ``annotations/contrib/**/*.jsonl`` (+ optional manifest/dossiers)
    into ``leanre.treemap.overlay/1`` JSON."""
    abs_annot = os.path.abspath(annotations_dir)
    c_root = os.path.abspath(contrib_dir) if contrib_dir else os.path.join(abs_annot, "contrib")
    repo_root = os.path.dirname(abs_annot)

    pack_paths: list = []
    # Top-level seed/decomp packs in annotations/ belong to riemann-hypothesis
    if project in (None, "", "all", "riemann-hypothesis") and os.path.isdir(abs_annot):
        pack_paths.extend(PackStore(abs_annot).files())

    # Project-specific notes/<slug>/annotations/*.jsonl if present
    if project and project != "all":
        notes_annot = os.path.join(repo_root, "notes", project, "annotations")
        if os.path.isdir(notes_annot):
            pack_paths.extend(PackStore(notes_annot).files())

    # Contributor PR packs under annotations/contrib/<slug>/*.jsonl
    if os.path.isdir(c_root):
        if project and project != "all":
            proj_dir = os.path.join(c_root, project)
            if os.path.isdir(proj_dir):
                pack_paths.extend(
                    p for p in discover_contrib_files(proj_dir) if p.endswith(".jsonl")
                )
        else:
            pack_paths.extend(
                p for p in discover_contrib_files(c_root) if p.endswith(".jsonl")
            )

    layers_meta: dict = {}
    layer_authors: dict = {}
    layer_counts: dict = {}
    entries: dict = {}
    total_records = 0

    for p in pack_paths:
        pk = load(p)
        for lid, ldef in pk.layers.items():
            if lid not in layers_meta:
                layers_meta[lid] = dict(ldef)
                layer_authors[lid] = []
                layer_counts[lid] = 0
        for rec in pk.sorted_annots():
            lid = rec["layer"]
            ldef = layers_meta.get(lid) or pk.layers[lid]
            auth = rec["author"]
            if auth not in layer_authors[lid]:
                layer_authors[lid].append(auth)
            layer_counts[lid] = layer_counts.get(lid, 0) + 1
            total_records += 1

            ex = rec.get("extra") if isinstance(rec.get("extra"), dict) else {}
            st = infer_entry_status(rec, ldef)
            verdict = str(rec.get("verdict") or ex.get("verdict") or "")
            url = str(rec.get("url") or ex.get("url") or "")
            if not url and isinstance(rec.get("source"), str):
                m_u = _GH_URL_EXTRACT_RE.search(rec["source"])
                if m_u:
                    url = m_u.group(0)
            is_draft = bool(rec.get("draft") or ldef.get("kind") in DRAFT_LAYER_KINDS)
            item: dict = {
                "layer": lid,
                "kind": _overlay_layer_kind(ldef["kind"]),
                "target": rec.get("target", "decl"),
                "status": st,
                "verdict": verdict,
                "author": auth,
                "note": rec.get("note") or rec.get("rename") or "",
                "draft": is_draft,
                "sighash": rec.get("sighash", ""),
                "source": rec.get("source", ""),
                "updated": rec.get("updated", ""),
                "breaks": rec.get("breaks", ""),
                "contested": False,
            }
            if url:
                item["url"] = url
            if rec.get("rename"):
                item["rename"] = rec["rename"]
            entries.setdefault(rec["name"], []).append(item)

    # Optional manifest / dossiers enrichment
    dossier_items: list = []
    if manifest_path and os.path.isfile(manifest_path):
        with open(manifest_path, "r", encoding="utf-8") as f:
            man = json.load(f)
        for doc in man.get("dossiers", []) if isinstance(man, dict) else []:
            if isinstance(doc, dict) and doc.get("targets"):
                for tgt in doc["targets"]:
                    if isinstance(tgt, str) and tgt:
                        dossier_items.append((tgt, doc.get("title") or doc.get("slug") or "Dossier", doc.get("route") or doc.get("path") or ""))
    if dossiers_dir and os.path.isdir(dossiers_dir):
        for fn in sorted(os.listdir(dossiers_dir)):
            if not fn.endswith(".md") or fn == "README.md":
                continue
            full = os.path.join(dossiers_dir, fn)
            if not os.path.isfile(full):
                continue
            with open(full, "r", encoding="utf-8", errors="replace") as f:
                head_txt = f.read(4096)
            m_t = re.search(r"^#\s+(.+)$", head_txt, re.M)
            title = m_t.group(1).strip() if m_t else fn[:-3]
            for m_tk in re.finditer(r"`([A-Z][A-Za-z0-9_']*(?:\.[A-Za-z0-9_']+)+)`", head_txt):
                dossier_items.append((m_tk.group(1), title, f"#docs/{fn[:-3]}"))

    if dossier_items:
        dlid = "human/dossiers"
        layers_meta.setdefault(dlid, {
            "layer": dlid, "kind": "dossier", "default_on": True,
            "title": "Technical dossiers & review notes",
            "description": "Cross-linked Markdown review dossiers.",
        })
        layer_authors.setdefault(dlid, ["leanre"])
        seen_d = set()
        for tgt, title, route in dossier_items:
            if (tgt, route) in seen_d:
                continue
            seen_d.add((tgt, route))
            layer_counts[dlid] = layer_counts.get(dlid, 0) + 1
            total_records += 1
            entries.setdefault(tgt, []).append({
                "layer": dlid, "kind": "dossier", "target": "decl", "status": "read",
                "verdict": "", "author": "leanre", "note": title, "draft": False,
                "sighash": "", "source": route, "dossier_route": route,
                "updated": now or utc_now(), "breaks": "", "contested": False,
            })

    contested_targets = 0
    for tgt in sorted(entries):
        elist = entries[tgt]
        elist.sort(key=lambda e: (e["draft"], e["layer"], e.get("sighash", "")))
        contested = _entry_is_contested(elist)
        if contested:
            contested_targets += 1
            for e in elist:
                e["contested"] = True

    layers_out = []
    for lid in sorted(layers_meta, key=lambda k: (not layers_meta[k].get("default_on", False), k)):
        ldef = layers_meta[lid]
        auths = layer_authors.get(lid) or []
        auth_summary = auths[0] if len(auths) == 1 else (", ".join(auths[:2]) + (f" (+{len(auths) - 2})" if len(auths) > 2 else ""))
        layers_out.append({
            "id": lid,
            "title": ldef["title"],
            "kind": _overlay_layer_kind(ldef["kind"]),
            "default_on": bool(ldef.get("default_on", False)),
            "author": auth_summary,
            "count": layer_counts.get(lid, 0),
            "description": ldef.get("description", ""),
        })

    resolved_project = project or ("riemann-hypothesis" if not os.path.isdir(c_root) or set(os.listdir(c_root)) <= {".gitkeep"} else "all")
    return {
        "schema": OVERLAY_SCHEMA,
        "generated_utc": now or utc_now(),
        "project": resolved_project,
        "layers": layers_out,
        "entries": {k: entries[k] for k in sorted(entries)},
        "stats": {
            "total_layers": len(layers_out),
            "total_records": total_records,
            "unique_targets": len(entries),
            "contested_targets": contested_targets,
        },
    }


def make_template_pack(
    *,
    project: str,
    name: str,
    author: str,
    kind: str = "human-review",
    target: str = "decl",
    sighash: Optional[str] = None,
    status: Optional[str] = None,
    note: Optional[str] = None,
    source: Optional[str] = None,
    breaks: Optional[str] = None,
    gallery_config: Optional[str] = None,
    now: Optional[str] = None,
) -> tuple:
    """Build a ready-to-edit valid contrib ``(Pack, suggested_rel_path)``."""
    ts = now or utc_now()
    if kind not in LAYER_KINDS:
        raise PackError([_issue("bad_kind", f"kind {kind!r} must be one of {list(LAYER_KINDS)}")])
    is_bot_kind = kind in DRAFT_LAYER_KINDS
    clean_author = author.strip()
    if is_bot_kind and not any(clean_author.startswith(p) for p in BOT_AUTHOR_PREFIXES):
        prefix = "bot:" if kind == "bot-check" else "ai:"
        clean_author = prefix + clean_author.lstrip("@")
    elif not is_bot_kind and any(clean_author.startswith(p) for p in BOT_AUTHOR_PREFIXES):
        raise PackError([_issue("ai_author_in_human_layer", "human-review template cannot use an 'ai:' or 'bot:' author")])

    author_slug = _sanitize_slug(clean_author, "contributor")
    decl_slug = _sanitize_slug(name.split(".")[-1] if "." in name else name, "notes")
    proj_slug = _sanitize_slug(project, "riemann-hypothesis")
    layer_prefix = "bot" if kind == "bot-check" else ("ai" if is_bot_kind else "human")
    layer_id = f"{layer_prefix}/{author_slug}-{decl_slug}"[:60].rstrip("._-")

    projects, _rc, _ = load_gallery_registry(gallery_config)
    pmeta = projects.get(proj_slug, {})
    if not source:
        rurl = pmeta.get("repo_url", "")
        sha = pmeta.get("pinned_commit", "")
        if rurl and _SHA40_RE.match(str(sha)):
            source = f"{rurl}/tree/{sha}"
        elif proj_slug == "tiny-demo":
            source = "examples/tiny_demo/Main.lean#L1; demo.ndjson"
        else:
            source = f"{proj_slug} pinned source"

    resolved_hash = sighash
    if not resolved_hash and target == "decl":
        repo_root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
        if proj_slug == "tiny-demo":
            g = _tiny_demo_graph(repo_root)
            if g and name in g.hashes_of and g.hashes_of[name]:
                resolved_hash = g.hashes_of[name][0]
        elif proj_slug == "riemann-hypothesis":
            kdb = os.path.join(repo_root, "outputs", "kernel", "kernel.db")
            if os.path.isfile(kdb):
                tmp_p = Pack()
                tmp_p.add_layer("human/tmp", "human", "tmp")
                tmp_p.put(make_annotation(name=name, layer="human/tmp", tag="L", source="tmp", author="tmp", now=ts, note="tmp"))
                g = GraphIndex.from_kernel_db(kdb, restrict_to=tmp_p)
                if name in g.hashes_of and g.hashes_of[name]:
                    resolved_hash = g.hashes_of[name][0]
        if not resolved_hash and (pmeta.get("mode") == "kernel_site" or proj_slug in ("riemann-hypothesis", "tiny-demo")):
            resolved_hash = "k1n:" + "0" * 32

    pack = Pack()
    pack.add_layer(
        layer_id,
        kind=kind,
        title=f"{clean_author} notes on {name}",
        default_on=not is_bot_kind,
    )
    tag = "M" if kind == "ai-draft" else ("C" if kind == "bot-check" else "L")
    eff_status = status or ("summary" if is_bot_kind else "read")
    eff_breaks = breaks or ("Draft note; proof body not yet audited by a human reviewer." if tag == "M" else None)
    eff_note = note or f"Summary of {name}: replace with concise mathematical or structural findings."
    rec_dict = make_annotation(
        name=name,
        target=target,
        sighash=resolved_hash if target == "decl" else None,
        layer=layer_id,
        tag=tag,
        source=source,
        author=clean_author,
        now=ts,
        note=eff_note,
        breaks=eff_breaks,
        draft=is_bot_kind,
    )
    rec_dict["status"] = eff_status
    pack.put(rec_dict)
    rel_out = os.path.join("annotations", "contrib", proj_slug, f"{author_slug}__{decl_slug}.jsonl")
    return pack, rel_out


# ----------------------------------------------------------------------------------------------
# CLI  (`leanre annot ...` -- the coordinator calls register_cli(subparsers) and args.annot_func(args))
# ----------------------------------------------------------------------------------------------

def _read_pack_arg(path: str) -> Pack:
    if os.path.isdir(path):
        pack, issues = PackStore(path).load()
        if errors_of(issues):
            raise PackError(errors_of(issues))
        return pack
    return load(path)


def _print_json(obj: Any) -> None:
    sys.stdout.write(json.dumps(obj, indent=2, sort_keys=True, ensure_ascii=False) + "\n")


def cmd_validate(args: argparse.Namespace) -> int:
    bad = 0
    paths: list = []
    for p in args.paths:
        if os.path.isdir(p):
            paths += PackStore(p).files()
            contrib_sub = os.path.join(p, "contrib")
            if os.path.isdir(contrib_sub):
                paths += [f for f in discover_contrib_files(contrib_sub) if f.endswith(".jsonl")]
            elif os.path.basename(os.path.abspath(p)) == "contrib":
                paths += [f for f in discover_contrib_files(p) if f.endswith(".jsonl")]
        else:
            paths.append(p)
    seen_p: set = set()
    dedup_paths: list = []
    for path in paths:
        ap = os.path.abspath(path)
        if ap not in seen_p:
            seen_p.add(ap)
            dedup_paths.append(path)
    for path in dedup_paths:
        issues = validate_file(path, canonical=not args.lenient)
        for i in issues:
            print(f"{path}:{i['line']}: {i['severity']}: {i['code']}: {i['msg']}")
        bad += bool(issues)
        if not issues:
            pack = load(path)
            print(f"{path}: OK ({len(pack.layers)} layer(s), {len(pack)} annotation(s), schema {SCHEMA})")
    for p in args.paths:
        if os.path.isdir(p):
            for i in PackStore(p).load()[1]:
                if i["code"] in ("conflict", "layer_conflict") and not i["line"]:
                    print(f"{p}/{i['file']}: error: {i['code']}: {i['msg']}")
                    bad += 1
    return 1 if bad else 0


def cmd_export(args: argparse.Namespace) -> int:
    text = dumps(_read_pack_arg(args.src), args.layer or None)
    if args.out and args.out != "-":
        _atomic_write(args.out, text)
    else:
        sys.stdout.write(text)
    return 0


def cmd_import(args: argparse.Namespace) -> int:
    with open(args.pack, "rb") as f:
        text = f.read()
    resolve = dict(x.split("=", 1) for x in args.resolve or [])
    rep = PackStore(args.into).import_text(text, resolve=resolve, dry_run=args.dry_run)
    _print_json(rep)
    return 0 if rep["ok"] else 2


def cmd_merge(args: argparse.Namespace) -> int:
    resolve = dict(x.split("=", 1) for x in args.resolve or [])
    m = merge(_read_pack_arg(args.ours), _read_pack_arg(args.theirs), resolve)
    pack = m.pop("pack")
    if m["ok"] and args.out:
        dump(pack, args.out)
    _print_json(m)
    return 0 if m["ok"] else 2


def cmd_diff(args: argparse.Namespace) -> int:
    d = diff(_read_pack_arg(args.a), _read_pack_arg(args.b))
    _print_json(d)
    return 0 if d["same"] else 1


def cmd_layers(args: argparse.Namespace) -> int:
    pack = _read_pack_arg(args.src)
    for row in layer_table(pack):
        mark = "DRAFT" if row["draft"] else "     "
        print(f"{'on ' if row['enabled'] else 'off'}  {mark}  {row['kind']:<8}  {row['count']:>6}  {row['layer']}  -- {row['title']}")
    return 0


def cmd_reanchor(args: argparse.Namespace) -> int:
    pack = _read_pack_arg(args.src)
    if args.graph_tsv:
        graph = GraphIndex.from_tsv(args.graph_tsv, restrict_to=pack)
    elif args.kernel_db:
        graph = GraphIndex.from_kernel_db(args.kernel_db, restrict_to=pack, leanre_db=args.leanre_db)
    else:
        graph = GraphIndex.from_sqlite(args.graph_db, args.sql, restrict_to=pack)
    rep = reanchor(pack, graph, args.layer or None)
    if args.summary:
        _print_json({"graph": rep["graph"], "total": rep["total"], "counts": rep["counts"]})
    else:
        _print_json(rep)
    if args.rebind_out:
        rb = rebind(pack, rep, now=args.now or utc_now(), accept_signature_change=args.accept_signature_change,
                    accept_alt_hash=args.accept_alt_hash)
        dump(rb.pop("pack"), args.rebind_out)
        _print_json(rb)
    return 0


def cmd_check_pr(args: argparse.Namespace) -> int:
    if not args.files and not args.all_contrib:
        print("leanre annot check-pr: specify one or more pack files or --all-contrib", file=sys.stderr)
        return 2
    rep = check_pr(
        args.files,
        all_contrib=args.all_contrib,
        contrib_root=args.contrib_root,
        gallery_config=args.gallery_config,
        kernel_db=args.kernel_db,
        leanre_db=args.leanre_db,
        anchors_path=args.anchors,
        allow_shared=args.allow_shared,
        strict=args.strict,
    )
    md = format_pr_markdown_report(rep)
    if args.markdown_report:
        _atomic_write(args.markdown_report, md)
    if args.json:
        _print_json(rep)
    else:
        sys.stdout.write(md)
    return 0 if rep["ok"] else 1


def cmd_overlay(args: argparse.Namespace) -> int:
    ov = build_overlay(
        args.src,
        contrib_dir=args.contrib_dir,
        project=args.project,
        manifest_path=args.manifest,
        dossiers_dir=args.dossiers_dir,
        now=args.now,
    )
    text = json.dumps(ov, indent=2, ensure_ascii=False) + "\n"
    if args.out and args.out != "-":
        _atomic_write(args.out, text)
    else:
        sys.stdout.write(text)
    return 0


def cmd_template(args: argparse.Namespace) -> int:
    pack, suggested = make_template_pack(
        project=args.project,
        name=args.name,
        author=args.author,
        kind=args.kind,
        target=args.target,
        sighash=args.sighash,
        status=args.status,
        note=args.note,
        source=args.source,
        breaks=args.breaks,
        gallery_config=args.gallery_config,
        now=args.now,
    )
    text = dumps(pack)
    out_path = args.out or suggested
    if out_path == "-":
        sys.stdout.write(text)
    else:
        _atomic_write(out_path, text)
        print(f"wrote {out_path} ({len(pack)} record(s), layer {sorted(pack.layers)[0]})")
    return 0


def register_cli(sub: Any, dest: str = "annot_func") -> argparse.ArgumentParser:
    """Add the ``annot`` subcommand to an argparse subparsers object.  Dispatch with
    ``return getattr(args, dest)(args)``; every handler returns a process exit code."""
    p = sub.add_parser("annot", help="Portable JSONL annotation packs: validate/check-pr/overlay/template/export/import/merge/diff/layers/reanchor")
    s = p.add_subparsers(dest="annot_cmd", required=True)

    q = s.add_parser("validate", help="Validate pack files / directories (exit 1 on any issue)")
    q.add_argument("paths", nargs="+")
    q.add_argument("--lenient", action="store_true", help="schema errors only; allow non-canonical formatting")
    q.set_defaults(**{dest: cmd_validate})

    q = s.add_parser("check-pr", help="Validate contributor PR packs under annotations/contrib/ (offline-safe)")
    q.add_argument("files", nargs="*", help="Pack files to check")
    q.add_argument("--all-contrib", action="store_true", help="Check all packs under --contrib-root")
    q.add_argument("--contrib-root", default="annotations/contrib", help="Root directory for contributor packs")
    q.add_argument("--gallery-config", default=None, help="Path to leanre_gallery.toml for pinned SHA checks")
    q.add_argument("--kernel-db", default=None, help="Optional kernel.db path for exact sighash verification")
    q.add_argument("--leanre-db", default=None, help="Optional leanre.db path for module/folder verification")
    q.add_argument("--anchors", default=None, help="Optional compact annot_anchors.json path")
    q.add_argument("--allow-shared", action="store_true", help="Allow multi-author / shared pack ownership")
    q.add_argument("--strict", action="store_true", help="Fail on formatting warnings as well as errors")
    q.add_argument("--json", action="store_true", help="Emit structured JSON report to stdout")
    q.add_argument("--markdown-report", default=None, help="Write GitHub Markdown summary report to path")
    q.set_defaults(**{dest: cmd_check_pr})

    q = s.add_parser("overlay", help="Compile annotations/ + annotations/contrib/ into leanre.treemap.overlay/1 JSON")
    q.add_argument("src", nargs="?", default="annotations", help="Annotations directory (default: annotations)")
    q.add_argument("-o", "--out", default="-", help="Output overlay.json path (default: stdout)")
    q.add_argument("--project", default=None, help="Optional gallery project slug filter (e.g. riemann-hypothesis)")
    q.add_argument("--contrib-dir", default=None, help="Optional override for annotations/contrib directory")
    q.add_argument("--manifest", default=None, help="Optional site manifest.json for dossier target links")
    q.add_argument("--dossiers-dir", default=None, help="Optional Markdown dossiers directory")
    q.add_argument("--now", default=None, help="Override generated_utc timestamp")
    q.set_defaults(**{dest: cmd_overlay})

    q = s.add_parser("template", help="Generate a valid contributor JSONL pack stub in annotations/contrib/<slug>/")
    q.add_argument("--project", required=True, help="Gallery project slug (e.g. riemann-hypothesis, navier-stokes)")
    q.add_argument("--name", required=True, help="Target declaration / module / folder name")
    q.add_argument("--author", required=True, help="Contributor handle (e.g. @alice or ai:model-name)")
    q.add_argument("--kind", default="human-review", choices=list(LAYER_KINDS), help="Layer trust kind")
    q.add_argument("--out", default=None, help="Output .jsonl path (default: annotations/contrib/<project>/<author>__<decl>.jsonl)")
    q.add_argument("--target", default="decl", choices=list(TARGETS), help="Target entity kind")
    q.add_argument("--sighash", default=None, help="Normalized signature hash (e.g. k1n:<32 hex>)")
    q.add_argument("--status", default=None, choices=["summary", "read", "verified", "flagged"], help="Initial review status")
    q.add_argument("--note", default=None, help="Initial note text")
    q.add_argument("--source", default=None, help="Pinned evidence link or citation")
    q.add_argument("--breaks", default=None, help="Caveat note (required for tag M / ai-draft)")
    q.add_argument("--gallery-config", default=None, help="Optional path to leanre_gallery.toml")
    q.add_argument("--now", default=None, help="Timestamp override (YYYY-MM-DDTHH:MM:SSZ)")
    q.set_defaults(**{dest: cmd_template})

    q = s.add_parser("export", help="Write the canonical pack for a file or directory (optionally some layers)")
    q.add_argument("src")
    q.add_argument("-o", "--out", default="-")
    q.add_argument("--layer", action="append")
    q.set_defaults(**{dest: cmd_export})

    q = s.add_parser("import", help="Merge a pack into an annotations directory; conflicts are reported (exit 2)")
    q.add_argument("pack")
    q.add_argument("--into", default="annotations")
    q.add_argument("--dry-run", action="store_true")
    q.add_argument("--resolve", action="append", metavar="ID=ours|theirs")
    q.set_defaults(**{dest: cmd_import})

    q = s.add_parser("merge", help="Merge two packs; writes --out only when conflict-free (exit 2 otherwise)")
    q.add_argument("ours")
    q.add_argument("theirs")
    q.add_argument("-o", "--out")
    q.add_argument("--resolve", action="append", metavar="ID=ours|theirs")
    q.set_defaults(**{dest: cmd_merge})

    q = s.add_parser("diff", help="Structural diff of two packs (exit 1 when different)")
    q.add_argument("a")
    q.add_argument("b")
    q.set_defaults(**{dest: cmd_diff})

    q = s.add_parser("layers", help="List layers; AI-draft layers are off by default and marked DRAFT")
    q.add_argument("src")
    q.set_defaults(**{dest: cmd_layers})

    q = s.add_parser("reanchor", help="Report exact / name_only / hash_only / orphan against a graph")
    q.add_argument("src")
    g = q.add_mutually_exclusive_group(required=True)
    g.add_argument("--graph-tsv", help="name<TAB>hash[<TAB>hash...] lines")
    g.add_argument("--kernel-db", help="outputs/kernel/kernel.db (read-only; table consts)")
    g.add_argument("--graph-db", help="any SQLite DB (opened read-only); use with --sql")
    q.add_argument("--sql", default=GraphIndex.KERNEL_SQL, help="SELECT returning (name, hash[, hash...])")
    q.add_argument("--leanre-db", help="with --kernel-db: Phase 2 leanre.db for module / folder names")
    q.add_argument("--accept-alt-hash", action="store_true")
    q.add_argument("--layer", action="append")
    q.add_argument("--summary", action="store_true")
    q.add_argument("--rebind-out", help="also write the re-bound pack here")
    q.add_argument("--accept-signature-change", action="store_true")
    q.add_argument("--now", help="timestamp for re-bound records (default: current UTC)")
    q.set_defaults(**{dest: cmd_reanchor})
    return p


def main(argv: Optional[Sequence[str]] = None) -> int:
    ap = argparse.ArgumentParser(prog="annot.py", description=__doc__.splitlines()[0])
    register_cli(ap.add_subparsers(dest="cmd", required=True))
    argv = list(sys.argv[1:] if argv is None else argv)
    if argv[:1] != ["annot"]:
        argv = ["annot"] + argv
    args = ap.parse_args(argv)
    try:
        return int(args.annot_func(args))
    except PackError as e:
        for i in e.issues:
            print(f"error: {i.get('file', '')}{':' if i.get('file') else ''}{i['line'] or ''} {i['code']}: {i['msg']}",
                  file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
