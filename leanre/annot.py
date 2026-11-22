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
LAYER_KINDS = ("human", "ai-draft")
AI_AUTHOR_PREFIX = "ai:"

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
_ANNOT_OPTIONAL = ("sighash", "alt_sighash", "slot", "rename", "aliases", "note", "breaks", "draft", "was", "extra")
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
        out["default_on"] = out["kind"] == "human"
    return out


def normalize_annot(rec: Mapping[str, Any]) -> dict:
    """Return the canonical form of an annotation dict (drop empty optionals, sort/dedupe lists)."""
    out: dict = {"type": "annot"}
    for k, v in rec.items():
        if k == "type":
            continue
        if k in ("rename", "note", "breaks", "source", "author", "slot", "sighash"):
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
    elif kind == "ai-draft" and rec["default_on"]:
        errs.append(("ai_draft_default_on", "ai-draft layers must have default_on=false"))
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
    for tf in _TS_FIELDS:
        if tf in rec and (not isinstance(rec[tf], str) or not TS_RE.match(rec[tf])):
            errs.append(("bad_" + tf, f"{tf} must be UTC ISO-8601 'YYYY-MM-DDTHH:MM:SSZ'"))
    if all(isinstance(rec.get(tf), str) and TS_RE.match(rec[tf]) for tf in _TS_FIELDS) and rec["updated"] < rec["created"]:
        errs.append(("bad_updated", "updated is earlier than created"))
    if "draft" in rec and rec["draft"] is not True:
        errs.append(("bad_draft", "draft, when present, must be true"))
    # layer coupling: AI drafts can never masquerade as facts, humans never write into AI layers
    if isinstance(lid, str) and "layer" in rec:
        if layer is None:
            errs.append(("undeclared_layer", f"layer {lid!r} is not declared by a layer line in this pack"))
        else:
            author = rec.get("author") if isinstance(rec.get("author"), str) else ""
            is_ai = author.startswith(AI_AUTHOR_PREFIX)
            if layer.get("kind") == "ai-draft":
                if rec.get("draft") is not True:
                    errs.append(("draft_unmarked", "records in an ai-draft layer must carry \"draft\": true"))
                if not is_ai:
                    errs.append(("draft_author", f"records in an ai-draft layer must have an '{AI_AUTHOR_PREFIX}<model>' author"))
                if tag in TAGS and tag != "M":
                    errs.append(("draft_tag", f"AI-draft records may only carry tag M (got {tag}); "
                                              "promote to a human layer to assert L/A/C/S"))
            elif layer.get("kind") == "human":
                if "draft" in rec:
                    errs.append(("draft_in_human_layer", "\"draft\" is only allowed in ai-draft layers"))
                if is_ai:
                    errs.append(("ai_author_in_human_layer",
                                 f"'{AI_AUTHOR_PREFIX}*' authors may only write into ai-draft layers"))
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
                               "default_on": (kind == "human") if default_on is None else default_on})
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
    """Layers that are on when the user has not chosen: human layers with default_on. Never ai-draft."""
    return sorted(l for l, d in pack.layers.items() if d["kind"] == "human" and d["default_on"])


def layer_table(pack: Pack, enabled: Optional[Iterable[str]] = None) -> list:
    on = set(default_layers(pack) if enabled is None else enabled)
    counts: dict = {}
    for k in pack.annots:
        counts[k[0]] = counts.get(k[0], 0) + 1
    return [{"layer": l, "kind": d["kind"], "draft": d["kind"] == "ai-draft", "default_on": d["default_on"],
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
        a["draft"] = pack.layers[key[0]]["kind"] == "ai-draft"
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
        paths += PackStore(p).files() if os.path.isdir(p) else [p]
    for path in paths:
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


def register_cli(sub: Any, dest: str = "annot_func") -> argparse.ArgumentParser:
    """Add the ``annot`` subcommand to an argparse subparsers object.  Dispatch with
    ``return getattr(args, dest)(args)``; every handler returns a process exit code."""
    p = sub.add_parser("annot", help="Portable JSONL annotation packs: validate/export/import/merge/diff/layers/reanchor")
    s = p.add_subparsers(dest="annot_cmd", required=True)

    q = s.add_parser("validate", help="Validate pack files / directories (exit 1 on any issue)")
    q.add_argument("paths", nargs="+")
    q.add_argument("--lenient", action="store_true", help="schema errors only; allow non-canonical formatting")
    q.set_defaults(**{dest: cmd_validate})

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
