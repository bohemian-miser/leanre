"""`leanre decompile` CLI.  Wire into leanre/leanre.py with:

    import decompile.cli as decompile_cli      # (leanre/ is on sys.path there)
    decompile_cli.register_cli(sub)
    ...
    if args.cmd == "decompile": return int(args.decompile_func(args))

or run standalone:  python3 -m decompile <cmd> ...   (from inside leanre/)
                    python3 leanre/decompile <cmd> ...
"""
from __future__ import annotations

import argparse
import json
import os
import re
import sys
from typing import Any, Optional

from .graph import Decompiler
from .kdb import (
    DEFAULT_KERNEL_DB,
    DEFAULT_SRC,
    Decl,
    KernelDB,
    ResolveError,
    ResolveResult,
    is_auto_instance_name,
    resolve_leanre_db_path,
)
from .schema import validate_file
from .source import (
    Contract,
    find_dead_in_src,
    format_anchor,
    grep_body_lines,
    grep_fields,
    one_line,
    preserve_truncate,
    read_contract,
    resolve_source_config,
    slice_body_lines,
)

_FLAG_NAMES = (
    (1, "refl_true"),
    (2, "of_decide"),
    (4, "reduce_bool"),
    (8, "reduce_nat"),
    (16, "sorry"),
    (32, "trust_compiler"),
)

_SORT_TYPE_RE = re.compile(r"^(?:Type|Sort)\b|→\s*(?:Type|Sort)\b")


def _effective_src_and_cfg(a: argparse.Namespace) -> tuple[str, dict[str, Any]]:
    cfg_path = getattr(a, "config", None)
    raw_src = getattr(a, "src_root", None)
    if cfg_path and (raw_src is None or raw_src == DEFAULT_SRC):
        cfg = resolve_source_config(None, cfg_path)
        resolved = cfg.get("resolved_src_root") or raw_src or DEFAULT_SRC
        return resolved, resolve_source_config(resolved, cfg_path)
    eff_src = raw_src or DEFAULT_SRC
    return eff_src, resolve_source_config(eff_src, cfg_path)


def _kdb(a: argparse.Namespace) -> KernelDB:
    ldb = resolve_leanre_db_path(a.kernel_db, a.leanre_db)
    kdb = KernelDB(a.kernel_db, ldb, a.tree)
    open_list = getattr(a, "_opened_kdbs", None)
    if isinstance(open_list, list):
        open_list.append(kdb)
    return kdb


def _dec(a: argparse.Namespace) -> Decompiler:
    eff_src, _ = _effective_src_and_cfg(a)
    return Decompiler(_kdb(a), eff_src, config_path=getattr(a, "config", None))


def _dump(obj: Any) -> None:
    print(json.dumps(obj, ensure_ascii=False, indent=1))


def _warn_case_fold(query: str, matched_name: str) -> None:
    print(
        f"warning: [case-fold] {query!r} resolved to {matched_name!r} via case-insensitive fallback "
        f"(pass --exact-case to reject)",
        file=sys.stderr,
    )


def _print_resolve_err(err: ResolveError) -> None:
    print(f"error: {err}", file=sys.stderr)
    if err.hits:
        label = "Matching candidates:" if err.ambiguous else "Top candidate matches (exact-case first, then ALL dom subtree):"
        print(label, file=sys.stderr)
        for h in err.hits:
            print(
                f"  {h.decl.id}\t{h.decl.kind}\t{h.all_dom}\t{h.decl.name}\t{h.decl.module or h.decl.method}\t[{h.match}]",
                file=sys.stderr,
            )
        if err.ambiguous:
            print(
                "  hint: pass an explicit FQN/suffix above, --near <decl>, or --continue-on-error",
                file=sys.stderr,
            )
    elif not err.ambiguous:
        print("  (no fuzzy/suffix candidate matches found)", file=sys.stderr)


def _err_entry(err: ResolveError) -> dict:
    return {
        "query": err.query,
        "error": str(err),
        "ambiguous": err.ambiguous,
        "candidates": [
            {
                "id": h.decl.id,
                "name": h.decl.name,
                "kind": h.decl.kind,
                "dom_subtree": h.all_dom,
                "module": h.decl.module,
                "method": h.decl.method,
                "match": h.match,
            }
            for h in err.hits
        ],
    }


def _load_manifest_info(src_root: str) -> Optional[dict]:
    abs_src = os.path.abspath(src_root)
    for cand_dir in (abs_src, os.path.dirname(abs_src)):
        mf = os.path.join(cand_dir, "lake-manifest.json")
        if os.path.exists(mf):
            try:
                with open(mf, encoding="utf-8") as f:
                    data = json.load(f)
            except (OSError, json.JSONDecodeError):
                return None
            tc_path = os.path.join(cand_dir, "lean-toolchain")
            toolchain = None
            if os.path.exists(tc_path):
                try:
                    with open(tc_path, encoding="utf-8") as tf:
                        toolchain = tf.read().strip()
                except OSError:
                    pass
            return {"manifest_path": mf, "packages": data.get("packages") or [], "toolchain": toolchain}
    return None


def _match_package(decl_name: str, manifest: Optional[dict]) -> Optional[dict]:
    if not manifest:
        return None
    ns = decl_name.split(".", 1)[0]
    if ns in ("Lean", "Init", "Std") and manifest.get("toolchain"):
        return {"name": "lean4-core", "rev": manifest["toolchain"], "url": "https://github.com/leanprover/lean4"}
    pkgs = manifest.get("packages") or []
    for pkg in pkgs:
        pname = str(pkg.get("name") or "")
        if pname.lower() == ns.lower():
            return {"name": pname, "rev": pkg.get("rev"), "url": pkg.get("url")}
    for pkg in pkgs:
        if str(pkg.get("name") or "").lower() == "mathlib":
            return {"name": pkg["name"], "rev": pkg.get("rev"), "url": pkg.get("url"), "inferred": True}
    return None


def _decode_flags(flags: int) -> list[str]:
    return [label for bit, label in _FLAG_NAMES if flags & bit]


def _cmd_resolve(a) -> int:
    try:
        eff_src, src_cfg = _effective_src_and_cfg(a)
    except FileNotFoundError as err:
        print(f"error: {err}", file=sys.stderr)
        return 2
    anchor_prefix = src_cfg["anchor_prefix"]
    kdb = _kdb(a)
    near = getattr(a, "near", None)
    exact_case = bool(getattr(a, "exact_case", False))
    kdb.preload_stems(a.queries)
    results = []
    any_miss = False
    for query in a.queries:
        q_clean = query.strip().removeprefix("_root_.")
        stem = q_clean.rsplit(".", 1)[-1]
        hits = kdb.resolve(query, limit=a.limit, near=near, exact_case=exact_case)
        cands = [
            {
                "id": h.decl.id,
                "name": h.decl.name,
                "kind": h.decl.kind,
                "dom_subtree": h.all_dom,
                "module": h.decl.module,
                "method": h.decl.method,
                "match": h.match,
            }
            for h in hits
        ]
        has_strong = any(h.match in ("exact", "suffix", "infix", "unqualified") for h in hits)
        if not has_strong:
            src_hits = kdb.find_source_decls(query, limit=a.limit, exact_case=exact_case)
            if not src_hits and kdb.l is None and not hits:
                dead_cs = find_dead_in_src(
                    eff_src,
                    query,
                    limit=a.limit,
                    anchor_prefix=anchor_prefix,
                    exact_case=exact_case,
                )
                src_hits = [
                    {
                        "name": c.name,
                        "kind": c.keyword,
                        "module": c.file[:-5].replace("/", ".") if c.file.endswith(".lean") else None,
                        "line": c.line,
                        "snippet": c.header,
                        "file": c.file,
                    }
                    for c in dead_cs
                ]
            if src_hits:
                dead_cands = [
                    {
                        "id": None,
                        "name": s["name"],
                        "kind": s["kind"],
                        "dom_subtree": 0,
                        "module": s["module"],
                        "method": "dead_source_only",
                        "status": "dead_source_only",
                        "file": s["file"],
                        "line": s["line"],
                        "anchor": format_anchor(s["file"], s["line"], anchor_prefix),
                        "match": "dead_source_only",
                    }
                    for s in src_hits
                ]
                cands = (dead_cands + cands)[: a.limit]

        case_folded_hit: Optional[str] = None
        if not exact_case and hits:
            has_exact_case_query = any(
                h.match in ("exact", "suffix", "infix", "unqualified")
                and (
                    h.decl.name == q_clean
                    or h.decl.name.endswith("." + q_clean)
                    or h.match == "infix"
                    or ("." not in q_clean and h.decl.name.endswith("." + stem))
                )
                for h in hits
            )
            if hits[0].match == "case_fold":
                case_folded_hit = hits[0].decl.name
            elif not has_exact_case_query:
                q_lo = q_clean.lower()
                cf_full = next(
                    (
                        h.decl.name
                        for h in hits
                        if h.match == "case_fold"
                        and (h.decl.name.lower() == q_lo or h.decl.name.lower().endswith("." + q_lo))
                    ),
                    None,
                )
                if cf_full is not None:
                    case_folded_hit = cf_full
        if case_folded_hit is not None:
            _warn_case_fold(query, case_folded_hit)

        if not cands:
            any_miss = True
        res_item: dict[str, Any] = {
            "query": query,
            "exact": bool(hits and hits[0].match == "exact"),
            "candidates": cands,
        }
        if case_folded_hit is not None:
            res_item["case_folded"] = True
        results.append(res_item)

    if a.json:
        _dump(results[0] if len(results) == 1 else results)
    else:
        for idx, res in enumerate(results):
            if len(results) > 1:
                if idx > 0:
                    print()
                print(f"== {res['query']} ==")
            if not res["candidates"]:
                print(f"no matches for {res['query']!r}", file=sys.stderr)
            for c in res["candidates"]:
                cid = c["id"] if c["id"] is not None else "-"
                loc = c.get("anchor") or c["module"] or c["method"]
                print(f"{cid}\t{c['kind']}\t{c['dom_subtree']}\t{c['name']}\t{loc}\t[{c['match']}]")
    return 0 if (not any_miss or getattr(a, "continue_on_error", False)) else 1


def _print_contract_body(body: str, max_len: int, preserve_lines: bool, total_lines: int = 0) -> None:
    if not preserve_lines:
        print(f"  := {one_line(body, max_len)}")
        return
    truncated = max_len > 0 and len(body) > max_len
    txt = preserve_truncate(body, max_len) or ""
    lines = txt.split("\n")
    if len(lines) <= 1:
        print(f"  := {txt}")
    else:
        print(f"  := {lines[0]}")
        for ln in lines[1:]:
            print(f"    {ln}" if ln else "")
    if truncated and total_lines > 0:
        shown = len(lines)
        print(
            f"    [truncated at {max_len} chars ({shown}/{total_lines} body lines); "
            f"pass --max-len 0, --body-lines A:B, or --grep REGEX]"
        )


def _print_filtered_body(
    c: Contract,
    *,
    body_lines_spec: Optional[str],
    grep_pat: Optional[str],
    context: int,
) -> dict[str, Any]:
    """Filter/slice `c.body_lines` for `--body-lines` and/or `--grep`, returning JSON metadata."""
    blines = c.body_lines
    meta: dict[str, Any] = {"body_lines_total": len(blines)}
    work_lines: list[tuple[int, str]] = list(blines)

    if body_lines_spec:
        sliced, mode = slice_body_lines(work_lines, body_lines_spec, decl_line=c.line)
        meta["body_slice"] = {
            "spec": body_lines_spec,
            "mode": mode,
            "lines": [{"line": fl, "offset": off, "text": txt} for fl, off, txt in sliced],
        }
        work_lines = [(fl, txt) for fl, _off, txt in sliced]

    if grep_pat is not None:
        hunks = grep_body_lines(work_lines, grep_pat, context=context)
        match_count = sum(1 for h in hunks for _, _, _, is_m in h if is_m)
        meta["body_grep"] = {
            "pattern": grep_pat,
            "context": context,
            "match_count": match_count,
            "hunks": [
                [{"line": fl, "offset": off, "text": txt, "match": is_m} for fl, off, txt, is_m in h]
                for h in hunks
            ],
        }
    return meta


def _render_filtered_body_text(c: Contract, meta: dict[str, Any]) -> None:
    total = meta["body_lines_total"]
    if "body_grep" in meta:
        g = meta["body_grep"]
        print(f"  grep     : /{g['pattern']}/ ({g['match_count']} match(es) in {total} body line(s), C={g['context']})")
        for h_idx, hunk in enumerate(g["hunks"]):
            if h_idx > 0:
                print("    --")
            for row in hunk:
                sep = ":" if row["match"] else "-"
                print(f"    L{row['line']}{sep} {row['text']}")
        return
    if "body_slice" in meta:
        sl = meta["body_slice"]
        rows = sl["lines"]
        span = f"L{rows[0]['line']}..L{rows[-1]['line']}" if rows else "empty"
        print(f"  slice    : {sl['spec']} ({sl['mode']} mode, {span}, {len(rows)}/{total} body line(s))")
        for row in rows:
            print(f"    L{row['line']}: {row['text']}")
        if sl["mode"] == "offset" and c.body_lines:
            m_end = re.search(r":\s*(\d+)\s*$", sl["spec"])
            m_start = re.match(r"^\s*(\d+)\s*:", sl["spec"])
            end_n = int(m_end.group(1)) if m_end else None
            start_n = int(m_start.group(1)) if m_start else None
            fl_lo, fl_hi = c.body_lines[0][0], c.body_lines[-1][0]
            if end_n is not None and end_n > total and start_n is not None and fl_lo <= start_n <= fl_hi:
                print(
                    f"    [note: interpreted {sl['spec']} as 1-based body offsets (total={total}); "
                    f"pass L{sl['spec'].lstrip()} for .lean file lines L{fl_lo}..L{fl_hi}]"
                )


def _find_dead_contracts(
    kdb: KernelDB,
    src_root: str,
    query: str,
    *,
    include_thm: bool,
    preserve_lines: bool,
    anchor_prefix: str,
    exact_case: bool = False,
) -> list[tuple[Contract, str, Optional[str]]]:
    """Fallback lookup for dead declarations absent from `kernel.db`."""
    rows = kdb.find_source_decls(query, exact_case=exact_case)
    if rows:
        out: list[tuple[Contract, str, Optional[str]]] = []
        for r in rows:
            c = read_contract(
                src_root,
                r["file"],
                r["name"],
                hint=r["line"],
                include_thm=include_thm,
                preserve_lines=preserve_lines,
                anchor_prefix=anchor_prefix,
            )
            if c is None:
                c = Contract(
                    name=r["name"],
                    keyword=r["kind"],
                    file=r["file"],
                    line=r["line"],
                    header=r["snippet"] or r["name"],
                    anchor_prefix=anchor_prefix,
                )
            out.append((c, r["kind"], r["module"]))
        return out
    if kdb.l is None or os.path.realpath(src_root) != os.path.realpath(DEFAULT_SRC):
        cs = find_dead_in_src(
            src_root,
            query,
            include_thm=include_thm,
            preserve_lines=preserve_lines,
            anchor_prefix=anchor_prefix,
            exact_case=exact_case,
        )
        return [
            (
                c,
                c.keyword,
                c.file[:-5].replace("/", ".") if c.file.endswith(".lean") else None,
            )
            for c in cs
        ]
    return []


def _print_missing_summary(missing: list[str], errors: list[dict]) -> None:
    if not errors:
        return
    print()
    print(f"missing ({len(missing)}): {', '.join(missing)}")
    for e in errors:
        tag = "AMBIGUOUS" if e.get("ambiguous") else "NOT FOUND"
        print(f"  error [{e['query']}] [{tag}]: {e['error']}")


def _wants_instance_summary(c: Contract) -> bool:
    if c.keyword in ("structure", "class", "inductive"):
        return True
    if c.keyword in ("def", "abbrev") and c.type and _SORT_TYPE_RE.search(c.type):
        return True
    return False


def _filter_contract_fields(
    c: Contract,
    pattern: str,
    context: int = 0,
    max_len: int = 2000,
) -> dict[str, Any]:
    hunks = grep_fields(c.fields, pattern, context=context)
    match_count = sum(1 for h in hunks for _, _, is_m in h if is_m)
    f_len = 0 if max_len <= 0 else 240
    return {
        "pattern": pattern,
        "context": context,
        "total_fields": len(c.fields),
        "match_count": match_count,
        "hunks": [
            [
                {
                    "index": idx1,
                    "name": f.name,
                    "type": one_line(f.type, f_len),
                    "default": f.default,
                    "line": f.line,
                    "match": is_m,
                }
                for f, idx1, is_m in h
            ]
            for h in hunks
        ],
    }


def _render_filtered_fields_text(fg: dict[str, Any]) -> None:
    ctx_s = f", C={fg['context']}" if fg["context"] > 0 else ""
    print(f"  fields   : /{fg['pattern']}/ ({fg['match_count']}/{fg['total_fields']} field(s) matched{ctx_s})")
    for h_idx, hunk in enumerate(fg["hunks"]):
        if h_idx > 0:
            print("    --")
        for row in hunk:
            sep = ":" if row["match"] else "-"
            ln_pref = f"L{row['line']}{sep} " if row.get("line") is not None else f"  {sep} "
            print(f"    {ln_pref}.{row['name']} : {row['type']}")


def _cmd_contract(a) -> int:
    # Validate --grep, --fields-grep, and --body-lines syntax upfront before scanning
    grep_pat: Optional[str] = getattr(a, "grep", None)
    fields_grep_pat: Optional[str] = getattr(a, "fields_grep", None)
    body_lines_spec: Optional[str] = getattr(a, "body_lines", None)
    context_n: int = getattr(a, "context", 0)
    deps_max: int = getattr(a, "deps_max", 0) or 0
    if context_n < 0:
        print(f"error: invalid --context {context_n}: must be >= 0", file=sys.stderr)
        return 2
    if grep_pat is not None:
        try:
            re.compile(grep_pat)
        except re.error as err:
            print(f"error: invalid --grep regex {grep_pat!r}: {err}", file=sys.stderr)
            return 2
    if fields_grep_pat is not None:
        try:
            re.compile(fields_grep_pat)
        except re.error as err:
            print(f"error: invalid --fields-grep regex {fields_grep_pat!r}: {err}", file=sys.stderr)
            return 2
    if body_lines_spec is not None:
        try:
            slice_body_lines([], body_lines_spec)
        except ValueError as err:
            print(f"error: {err}", file=sys.stderr)
            return 2

    try:
        D = _dec(a)
    except FileNotFoundError as err:
        print(f"error: {err}", file=sys.stderr)
        return 2

    has_body_filter = (grep_pat is not None) or (body_lines_spec is not None)
    eff_body = a.body or has_body_filter
    eff_include_thm = a.include_thm or has_body_filter
    eff_preserve = a.preserve_lines or has_body_filter
    near = getattr(a, "near", None)
    exact_case = bool(getattr(a, "exact_case", False))
    D.kdb.preload_stems(a.names)

    entries: list[tuple[str, Any]] = []  # ("live", (query, ResolveResult)) | ("dead", (query, matches, cf))
    missing: list[str] = []
    errors: list[dict] = []

    for nm in a.names:
        try:
            res = D.kdb.resolve_unique_detail(nm, near=near, exact_case=exact_case)
            if res.case_folded:
                _warn_case_fold(nm, res.decl.name)
            entries.append(("live", (nm, res)))
        except ResolveError as err:
            dead_matches = [] if err.ambiguous else _find_dead_contracts(
                D.kdb,
                D.src_root,
                nm,
                include_thm=eff_include_thm,
                preserve_lines=eff_preserve,
                anchor_prefix=D.anchor_prefix,
                exact_case=exact_case,
            )
            if dead_matches:
                c0 = dead_matches[0][0]
                nm_clean = nm.strip().removeprefix("_root_.")
                dead_cf = (
                    not exact_case
                    and c0.name != nm_clean
                    and not c0.name.endswith("." + nm_clean)
                    and (c0.name.lower() == nm_clean.lower() or c0.name.lower().endswith("." + nm_clean.lower()))
                )
                if dead_cf:
                    _warn_case_fold(nm, c0.name)
                entries.append(("dead", (nm, dead_matches, dead_cf)))
                continue
            if not a.continue_on_error:
                _print_resolve_err(err)
                return 1
            _print_resolve_err(err)
            missing.append(nm)
            errors.append(_err_entry(err))

    live_decls = [payload[1].decl for ktag, payload in entries if ktag == "live"]
    D.kdb.preload_src_rows(live_decls)

    manifest: Optional[dict] = None
    manifest_loaded = False

    def get_manifest() -> Optional[dict]:
        nonlocal manifest, manifest_loaded
        if not manifest_loaded:
            manifest = _load_manifest_info(D.src_root)
            manifest_loaded = True
        return manifest

    if a.table:
        rows = []
        for kind_tag, payload in entries:
            if kind_tag == "live":
                _nm, res = payload
                d, resolved_from = res.decl, res.resolved_from
                c = D.contract(d, include_thm=eff_include_thm, preserve_lines=eff_preserve)
                st = D.kdb.decl_stats(d)
                row = {
                    "id": d.id,
                    "name": d.name,
                    "kind": d.kind,
                    "dom_subtree": st["all_dom_subtree"],
                    "fan_in": st["fan_in"],
                    "module": d.module,
                    "method": d.method,
                    "anchor": c.anchor if c else None,
                    "header": one_line(c.header, a.max_len) if c else None,
                }
                if resolved_from is not None:
                    row["resolved_from"] = resolved_from
                if res.case_folded:
                    row["case_folded"] = True
                rows.append(row)
            else:
                _nm, matches, dead_cf = payload
                c, dkind, dmod = matches[0]
                row = {
                    "id": None,
                    "name": c.name,
                    "kind": dkind,
                    "status": "dead_source_only",
                    "dom_subtree": None,
                    "fan_in": None,
                    "module": dmod,
                    "method": "dead_source_only",
                    "file": c.file,
                    "line": c.line,
                    "anchor": c.anchor,
                    "header": one_line(c.header, a.max_len),
                }
                if dead_cf:
                    row["case_folded"] = True
                rows.append(row)
        if a.json:
            _dump({"results": rows, "missing": missing, "errors": errors} if errors else rows)
        else:
            print("id\tkind\tdom\tfan_in\tmodule\tanchor\theader")
            for r in rows:
                rid = r["id"] if r["id"] is not None else "-"
                dom_s = r["dom_subtree"] if r["dom_subtree"] is not None else "-"
                fi_s = r["fan_in"] if r["fan_in"] is not None else "-"
                hdr = r["header"] or "-"
                if r.get("case_folded"):
                    hdr = f"[case-fold] {hdr}"
                if r.get("status") == "dead_source_only":
                    hdr = f"[dead_source_only] {hdr}"
                print(
                    f"{rid}\t{r['kind']}\t{dom_s}\t{fi_s}\t"
                    f"{r['module'] or r['method']}\t{r['anchor'] or '-'}\t{hdr}"
                )
            _print_missing_summary(missing, errors)
        return 0

    json_items = []
    for idx, (kind_tag, payload) in enumerate(entries):
        if kind_tag == "dead":
            nm, matches, dead_cf = payload
            c, dkind, dmod = matches[0]
            others = matches[1:]
            with_body = eff_body and (eff_include_thm or dkind not in ("thm", "theorem", "lemma"))
            eff_fg_pat_d = fields_grep_pat if fields_grep_pat is not None else (grep_pat if c.fields else None)
            fg_meta_d = _filter_contract_fields(c, eff_fg_pat_d, context=context_n, max_len=a.max_len) if (eff_fg_pat_d is not None and c.fields) else None
            want_body_fmeta_d = has_body_filter and c.body is not None and not (
                grep_pat is not None and body_lines_spec is None and c.keyword in ("structure", "class", "inductive") and bool(c.fields)
            )
            fmeta = (
                _print_filtered_body(c, body_lines_spec=body_lines_spec, grep_pat=grep_pat, context=context_n)
                if want_body_fmeta_d
                else None
            )
            if a.json:
                c_json_d = c.to_json(a.max_len, with_body=with_body, preserve_lines=eff_preserve)
                if fg_meta_d is not None:
                    c_json_d["fields_total"] = fg_meta_d["total_fields"]
                    c_json_d["fields"] = [
                        {k: v for k, v in row.items() if k not in ("index", "match") and v is not None}
                        for h in fg_meta_d["hunks"]
                        for row in h
                    ]
                item: dict[str, Any] = {
                    "status": "dead_source_only",
                    "query": nm,
                    "decl": {
                        "id": None,
                        "name": c.name,
                        "kind": dkind,
                        "module": dmod,
                        "method": "dead_source_only",
                    },
                    "file": c.file,
                    "line": c.line,
                    "anchor": c.anchor,
                    "header": one_line(c.header, a.max_len),
                    "contract": c_json_d,
                }
                if dead_cf:
                    item["case_folded"] = True
                if fg_meta_d is not None:
                    item["fields_grep"] = fg_meta_d
                if fmeta:
                    item.update(fmeta)
                if others:
                    item["other_matches"] = [
                        {
                            "name": oc.name,
                            "kind": okind,
                            "module": omod,
                            "file": oc.file,
                            "line": oc.line,
                            "anchor": oc.anchor,
                            "header": one_line(oc.header, a.max_len),
                        }
                        for oc, okind, omod in others
                    ]
                json_items.append(item)
                continue

            if idx > 0:
                print()
            print(f"{c.name}  [{dkind}] status=dead_source_only module={dmod} (absent from kernel.db)")
            if dead_cf:
                print(f"  warning  : [case-fold] query {nm!r} matched {c.name!r} via case-folding (pass --exact-case to reject)")
            print(f"  anchor   : {c.anchor}")
            print(f"  file     : {c.file}")
            print(f"  line     : {c.line}")
            if c.namespace:
                print(f"  namespace: {c.namespace}")
            for v in c.variables:
                print(f"  variable : {v}")
            print(f"  header   : {one_line(c.header, a.max_len)}")
            if c.extends:
                print(f"  extends  : {', '.join(c.extends)}")
            if fg_meta_d is not None:
                _render_filtered_fields_text(fg_meta_d)
            else:
                for f in c.fields:
                    print(f"    .{f.name} : {' '.join(f.type.split())}")
            if fmeta is not None:
                _render_filtered_body_text(c, fmeta)
            elif with_body and c.body is not None and fg_meta_d is None:
                _print_contract_body(c.body, a.max_len, eff_preserve, total_lines=len(c.body_lines))
            elif a.body and not has_body_filter and not eff_include_thm and dkind in ("thm", "theorem", "lemma"):
                print("  hint     : theorem proof body omitted by default; pass --include-thm to include it")
            for oc, okind, _omod in others:
                print(f"  other    : {oc.name} [{okind}] ({oc.anchor})")
            continue

        nm, res = payload
        d, resolved_from = res.decl, res.resolved_from
        c = D.contract(d, include_thm=eff_include_thm, preserve_lines=eff_preserve)
        with_body = eff_body and (eff_include_thm or d.kind != "thm")
        need_stats = c is None or d.ground
        st = D.kdb.decl_stats(d) if need_stats else None
        pkg = _match_package(d.name, get_manifest()) if d.ground else None
        dep_hdrs = D.deps_headers(d, max_len=a.max_len, max_deps=deps_max) if getattr(a, "deps_headers", False) else None
        inst_info = D.attached_instances(d) if (c is not None and _wants_instance_summary(c)) else None
        eff_fg_pat = fields_grep_pat if fields_grep_pat is not None else (grep_pat if (c is not None and c.fields) else None)
        fg_meta = (
            _filter_contract_fields(c, eff_fg_pat, context=context_n, max_len=a.max_len)
            if (c is not None and c.fields and eff_fg_pat is not None)
            else None
        )
        want_body_fmeta = (
            has_body_filter
            and c is not None
            and c.body is not None
            and not (grep_pat is not None and body_lines_spec is None and c.keyword in ("structure", "class", "inductive") and bool(c.fields))
        )
        fmeta = (
            _print_filtered_body(c, body_lines_spec=body_lines_spec, grep_pat=grep_pat, context=context_n)
            if want_body_fmeta
            else None
        )

        if a.json:
            c_json = c.to_json(a.max_len, with_body=with_body, preserve_lines=eff_preserve) if c else None
            if c_json is not None and fg_meta is not None:
                c_json["fields_total"] = fg_meta["total_fields"]
                c_json["fields"] = [
                    {k: v for k, v in row.items() if k not in ("index", "match") and v is not None}
                    for h in fg_meta["hunks"]
                    for row in h
                ]
            item = {
                "decl": {"id": d.id, "name": d.name, "kind": d.kind, "module": d.module, "method": d.method},
                "contract": c_json,
            }
            if resolved_from is not None:
                item["resolved_from"] = resolved_from
            if res.case_folded:
                item["case_folded"] = True
            if res.near_candidates >= 2:
                item["near_candidates"] = res.near_candidates
            if dep_hdrs is not None:
                item["deps_headers"] = dep_hdrs
            if inst_info is not None and inst_info["count"] > 0:
                item["attached_instances"] = inst_info
            if fg_meta is not None:
                item["fields_grep"] = fg_meta
            if fmeta is not None:
                item.update(fmeta)
            if st is not None:
                item["kernel"] = {
                    "kind": st["kind"],
                    "live_mask": st["live_mask"],
                    "fan_in": st["fan_in"],
                    "fan_out": st["fan_out"],
                    "type_nodes": st["type_nodes"],
                    "value_nodes": st["value_nodes"],
                    "flags": st["flags"],
                    "flag_names": _decode_flags(st["flags"]),
                    "method": st["method"],
                    "all_dom_subtree": st["all_dom_subtree"],
                }
            if pkg is not None:
                item["package"] = pkg
            json_items.append(item)
            continue

        if idx > 0:
            print()
        print(f"{d.name}  [{d.kind}] id={d.id} module={d.module} ({d.method})")
        if res.case_folded:
            print(f"  warning  : [case-fold] query {nm!r} matched {d.name!r} via case-folding (pass --exact-case to reject)")
        if res.near_candidates >= 2:
            print(f"  note     : disambiguated {nm!r} -> {d.name!r} (1 of {res.near_candidates} via --near {near})")
        if c is None:
            is_auto_i = d.method == "unmatched:project_auto_instance" or is_auto_instance_name(d.name)
            if d.ground:
                print("  (no source contract: ground Mathlib/Lean decl)")
            elif is_auto_i:
                print("  note     : Lean 4 auto-synthesized project typeclass instance (kernel-verified, no explicit named source line)")
            else:
                print("  OPAQUE: source not located")
            if st is not None:
                flag_str = f"{st['flags']}"
                fnames = _decode_flags(st["flags"])
                if fnames:
                    flag_str += f" ({','.join(fnames)})"
                print(
                    f"  kernel   : kind={st['kind']} live_mask={st['live_mask']} "
                    f"fan_in={st['fan_in']} fan_out={st['fan_out']} "
                    f"type_nodes={st['type_nodes']} value_nodes={st['value_nodes']} "
                    f"flags={flag_str} method={st['method']}"
                )
            if pkg is not None:
                rev = pkg.get("rev") or "-"
                url = pkg.get("url") or ""
                extra = f" ({url})" if url else ""
                print(f"  package  : {pkg['name']} rev={rev}{extra}")
            if dep_hdrs:
                print(f"  deps     : {len(dep_hdrs)} project signature dep(s)")
                for dh in dep_hdrs:
                    print(f"    {dh['name']} [{dh['kind']}] ({dh['anchor'] or dh['module']}) : {dh['header'] or '-'}")
            continue

        print(f"  anchor   : {c.anchor}")
        if c.parent_info:
            pi = c.parent_info
            if pi.get("is_constructor"):
                print(
                    f"  ctor_of  : {pi['name']} [{pi['keyword']}] ({pi['fields_count']} fields, {pi['anchor']})"
                )
                print(
                    f"  note     : kernel edges attach to parent {pi['keyword']} {pi['name']} (id={d.id}); "
                    f"for constructor/literal sites run: {pi['instantiations_cmd']}"
                )
            elif pi.get("auto_instance"):
                print(
                    f"  note     : elaborated Lean 4 instance located from {pi['source_kind']} in {c.file}:{c.line}"
                )
            else:
                print(f"  field_of : {pi['name']} [{pi['keyword']}] ({pi['fields_count']} fields, {pi['anchor']})")
        if c.namespace:
            print(f"  namespace: {c.namespace}")
        for v in c.variables:
            print(f"  variable : {v}")
        print(f"  header   : {one_line(c.header, a.max_len)}")
        if c.extends:
            print(f"  extends  : {', '.join(c.extends)}")
        if fg_meta is not None:
            _render_filtered_fields_text(fg_meta)
        else:
            for f in c.fields:
                print(f"    .{f.name} : {' '.join(f.type.split())}")
        if fmeta is not None:
            _render_filtered_body_text(c, fmeta)
        elif with_body and c.body is not None and fg_meta is None:
            _print_contract_body(c.body, a.max_len, eff_preserve, total_lines=len(c.body_lines))
        elif a.body and not has_body_filter and not eff_include_thm and (d.kind == "thm" or c.keyword in ("theorem", "lemma")):
            print("  hint     : theorem proof body omitted by default; pass --include-thm to include it")
        if inst_info is not None and inst_info["count"] > 0:
            stem = d.name.rsplit(".", 1)[-1]
            print(
                f"  instances: {inst_info['count']} attached "
                f"(project={inst_info['project_count']}, external={inst_info['external_count']}; "
                f"search: decompile search {stem} --kind instance)"
            )
            for sm in inst_info["same_module"][:4]:
                print(f"    {sm['anchor']} : {sm['header']}")
        if dep_hdrs is not None:
            print(f"  deps     : {len(dep_hdrs)} project contract/signature dep(s)")
            for dh in dep_hdrs:
                loc = dh["anchor"] or dh["module"] or "-"
                print(f"    {dh['name']} [{dh['kind']}] ({loc}) : {dh['header'] or '-'}")
        elif c.keyword in ("def", "abbrev") and len(a.names) <= 4 and not d.ground:
            proj_deps, _ = D.contract_deps(d)
            if len(proj_deps) >= 3:
                print(
                    f"  hint     : leanre decompile unfold {d.name} --depth 2  "
                    f"(expands {len(proj_deps)} nested project contracts)"
                )

    if a.json:
        if errors:
            _dump({"results": json_items, "missing": missing, "errors": errors})
        else:
            _dump(json_items[0] if len(json_items) == 1 else json_items)
    else:
        _print_missing_summary(missing, errors)
    return 0


def _cmd_producers(a) -> int:
    try:
        D = _dec(a)
    except FileNotFoundError as err:
        print(f"error: {err}", file=sys.stderr)
        return 2
    near = getattr(a, "near", None)
    exact_case = bool(getattr(a, "exact_case", False))
    include_impl = bool(getattr(a, "include_implications", False))
    D.kdb.preload_stems(a.targets)
    results: list[dict[str, Any]] = []
    missing: list[str] = []
    errors: list[dict] = []

    for nm in a.targets:
        try:
            rdet = D.kdb.resolve_unique_detail(nm, near=near, exact_case=exact_case)
            if rdet.case_folded:
                _warn_case_fold(nm, rdet.decl.name)
        except ResolveError as err:
            _print_resolve_err(err)
            missing.append(nm)
            errors.append(_err_entry(err))
            continue
        res = D.producers(
            rdet.decl,
            live_only=a.live_only,
            include_dead=a.include_dead,
            include_implications=include_impl,
            limit=a.limit,
            max_len=a.max_len,
        )
        if rdet.resolved_from is not None:
            res["resolved_from"] = rdet.resolved_from
        if rdet.case_folded:
            res["case_folded"] = True
        results.append(res)

    rc = 0 if (not errors or a.continue_on_error) else 1
    if a.json:
        if errors:
            if results or a.continue_on_error:
                _dump({"results": results, "missing": missing, "errors": errors})
        else:
            _dump(results[0] if len(results) == 1 else results)
        return rc

    for idx, res in enumerate(results):
        if idx > 0:
            print()
        tgt = res["target"]
        kw = tgt.get("keyword") or tgt["kind"]
        print(
            f"== {tgt['name']} [{kw}] ({res['live_count']} live / {res['total_count']} producer(s)) "
            f"anchor={tgt.get('anchor') or tgt.get('module') or '-'} =="
        )
        if res.get("ctor_of"):
            pi = res["ctor_of"]
            print(
                f"  note: {tgt['name']} is a constructor of {pi['name']}; "
                f"for constructor/literal sites run: {pi['instantiations_cmd']}"
            )
        prods = res["producers"]
        if prods:
            print("dom\tkind\tlive\trole\tanchor\tname\theader")
            for p in prods:
                live_s = "yes" if p["live"] else ("dead" if p.get("status") == "dead_source_only" else "no")
                loc = p.get("anchor") or p.get("module") or "-"
                print(
                    f"{p['dom_subtree']}\t{p['kind']}\t{live_s}\t{p['role']}\t"
                    f"{loc}\t{p['name']}\t{p.get('header') or '-'}"
                )
        else:
            print("  (0 codomain producers in kernel.db)")

        if not prods or include_impl:
            if res.get("embedded_in_defs"):
                print(f"  embedded in def(s): {', '.join(res['embedded_in_defs'])}")
            if res.get("wrapper_producers"):
                wp_s = ", ".join(
                    f"{wp['name']} -> {wp['via_wrapper']} [{wp['wrapper_role']}] ({wp['anchor']})"
                    for wp in res["wrapper_producers"][:6]
                )
                print(f"  wrapper producer(s) ({len(res['wrapper_producers'])}): {wp_s}")
            pc_tot = res.get("premise_consumers_count", 0)
            pc_live = res.get("live_premise_consumers_count", 0)
            if pc_tot > 0:
                sample_p = ", ".join(
                    f"{pc['name']} ({pc['anchor'] or '-'})"
                    for pc in (res.get("premise_consumers") or ())[:5]
                )
                more_p = f" (+{pc_tot - 5} more)" if pc_tot > 5 else ""
                print(f"  premise/hypothesis uses: {pc_tot} ({pc_live} live) — assumed in: {sample_p}{more_p}")
            if res.get("record_field_carriers"):
                rf_list = res["record_field_carriers"]
                rf_s = ", ".join(
                    f"{rf['field']}{'[cond]' if rf.get('conditional') else ''} ({rf['anchor']})"
                    for rf in rf_list[:6]
                )
                print(f"  record-field carrier(s) ({len(rf_list)}): {rf_s}")
            if not prods and pc_tot == 0 and not res.get("record_field_carriers") and not res.get("embedded_in_defs"):
                print("  premise/hypothesis uses: 0 (no project consumers reference this declaration)")
            if not prods and res.get("dead_source_producers"):
                print(
                    f"  dead source producer(s) ({len(res['dead_source_producers'])}; pass --include-dead): "
                    + ", ".join(dp["name"] for dp in res["dead_source_producers"])
                )
    if results or a.continue_on_error:
        _print_missing_summary(missing, errors)
    return rc


def _print_unfold(u: dict, ind: int = 0) -> None:
    pad = "  " * ind
    tag = "GROUND" if u.get("ground") else ("REF" if u.get("ref") else ("…" if u.get("unexpanded") else u.get("kind", "")))
    stop_tag = " [STOPPED]" if u.get("stopped") else ""
    print(f"{pad}- {u['id']} [{tag}]{stop_tag}{' via ' + u['edge'] if u.get('edge') else ''}  {u.get('anchor') or ''}")
    if u.get("header"):
        print(f"{pad}    {u['header']}")
    for f in u.get("fields", []):
        print(f"{pad}    .{f['name']} : {f['type']}")
    if u.get("fields_truncated"):
        print(f"{pad}    ... (+{u['fields_truncated']} more fields)")
    elif u.get("stopped") and u.get("fields_count"):
        print(f"{pad}    ... ({u['fields_count']} fields omitted at stop boundary)")
    if u.get("body"):
        print(f"{pad}    := {u['body']}")
    if u.get("opaque"):
        print(f"{pad}    OPAQUE ({u['opaque']})")
    elif u.get("auto_instance") and not u.get("header"):
        print(f"{pad}    (auto-synthesized project instance; kernel-verified)")
    if u.get("ground_deps"):
        print(f"{pad}    ground: {', '.join(u['ground_deps'])}")
    for k in u.get("deps", []):
        _print_unfold(k, ind + 1)


def _resolve_single_cmd(
    D: Decompiler,
    name: str,
    continue_on_error: bool,
    *,
    near: Optional[str] = None,
    exact_case: bool = False,
) -> tuple[Optional[Decl], Optional[str], Optional[ResolveError]]:
    try:
        res = D.kdb.resolve_unique_detail(name, near=near, exact_case=exact_case)
        if res.case_folded:
            _warn_case_fold(name, res.decl.name)
        return res.decl, res.resolved_from, None
    except ResolveError as err:
        _print_resolve_err(err)
        if not continue_on_error:
            return None, None, err
        return None, None, err


def _cmd_unfold(a) -> int:
    D = _dec(a)
    d, resolved_from, err = _resolve_single_cmd(
        D,
        a.name,
        a.continue_on_error,
        near=getattr(a, "near", None),
        exact_case=bool(getattr(a, "exact_case", False)),
    )
    if d is None:
        assert err is not None
        if not a.continue_on_error:
            return 1
        if a.json:
            _dump({"results": [], "missing": [a.name], "errors": [_err_entry(err)]})
        else:
            _print_missing_summary([a.name], [_err_entry(err)])
        return 0
    u = D.unfold(
        d,
        a.depth,
        with_body=not a.no_body,
        max_len=a.max_len,
        full_fields=a.full_fields,
        stop_at=a.stop_at,
        max_fields=a.max_fields,
    )
    if resolved_from is not None:
        u["resolved_from"] = resolved_from
    _dump(u) if a.json else _print_unfold(u)
    return 0


def _render_term_wiring_text(tw: dict[str, Any]) -> None:
    mode = tw.get("mode")
    callee = tw.get("callee") or "-"
    ln = tw.get("line")
    ln_s = f"L{ln}: " if ln is not None else ""
    if mode in ("record_literal", "where_fields"):
        flds = tw.get("fields") or []
        print(f"  term   : {ln_s}{mode} -> {callee} ({len(flds)} field(s)):")
        for f in flds:
            fln = f"L{f['line']}: " if f.get("line") is not None else ""
            via_s = f" [via {f['via']}]" if f.get("via") else ""
            roots_s = f"  roots={f['root_hyps']}" if f.get("root_hyps") else ""
            print(f"    {fln}.{f['field']} := {f['expr']}{via_s}{roots_s}")
        return
    args = tw.get("args") or []
    print(f"  term   : {ln_s}{mode} -> {callee} ({len(args)} arg(s)):")
    for a in args:
        idx_s = f"#{a['index']}" if a.get("index") is not None else f"({a.get('named', '?')}:=)"
        p_parts = []
        if a.get("param_name"):
            p_parts.append(str(a["param_name"]))
        if a.get("param_type"):
            p_parts.append(str(a["param_type"]))
        param_s = f" ({' : '.join(p_parts)})" if p_parts else ""
        rhs_s = a.get("via") if (a.get("kind") == "call" and a.get("via")) else a.get("expr")
        if a.get("kind") == "call" and a.get("via") and a.get("expr") and a["expr"] != a["via"]:
            rhs_s = f"{a['via']}  [{one_line(a['expr'], 100)}]"
        steps_s = f" steps={a['uses_steps']}" if a.get("uses_steps") else ""
        roots_s = f" roots={a['root_hyps']}" if a.get("root_hyps") else ""
        print(f"    {idx_s} [{a['kind']}]{param_s} <- {rhs_s}{steps_s}{roots_s}")


def _print_horn_text(h: dict[str, Any]) -> None:
    print(f"{h['via']}  [{h['kind']}]  {h.get('anchor') or ''}")
    if h.get("header"):
        print(f"  header : {h['header']}")
    print(f"  hyps   : {', '.join(h['hyps']) if h['hyps'] else '(none)'}")
    print(f"  concl  : {', '.join(h['concl']) if h['concl'] else '(none)'}")
    print(f"  lemmas : {', '.join(h['lemmas_project']) if h['lemmas_project'] else '(none)'}")
    hw = h.get("have_wiring")
    if hw is None:
        return
    tw = hw.get("term_wiring")
    has_steps = bool(hw.get("destructured") or hw.get("steps"))
    has_any = bool(has_steps or hw.get("terminal") or tw)
    if not has_any:
        print("  wiring : 0 have/obtain steps (term-mode or single-tactic proof)")
        return
    if not has_steps:
        print("  wiring : 0 have/obtain steps (direct term/application proof)")
    if hw.get("destructured"):
        print("  obtain :")
        for ob in hw["destructured"]:
            pat_s = ob.get("pattern") or f"⟨{', '.join(ob['vars'])}⟩"
            print(f"    L{ob['line']}: {pat_s} := {ob['from']}  <- {ob['root_hyps']}")
    if hw.get("steps"):
        print(f"  steps  ({len(hw['steps'])} have/let):")
        for st in hw["steps"]:
            tp = f" : {st['type']}" if st.get("type") else ""
            via = st.get("via") or "-"
            deps_s = f" steps={st['uses_steps']}" if st.get("uses_steps") else ""
            roots_s = f" roots={st['root_hyps']}" if st.get("root_hyps") else ""
            print(f"    L{st['line']}: {st['kind']} {st['name']}{tp}  := {via}{deps_s}{roots_s}")
    if hw.get("terminal"):
        tm = hw["terminal"]
        print(
            f"  close  : L{tm['line']}: {tm['tactic']} {tm.get('via') or '-'}  "
            f"steps={tm['uses_steps']} roots={tm['root_hyps']}"
        )
    if tw is not None:
        _render_term_wiring_text(tw)


def _cmd_horn(a) -> int:
    D = _dec(a)
    d, resolved_from, err = _resolve_single_cmd(
        D,
        a.name,
        a.continue_on_error,
        near=getattr(a, "near", None),
        exact_case=bool(getattr(a, "exact_case", False)),
    )
    if d is None:
        assert err is not None
        if not a.continue_on_error:
            return 1
        _dump({"results": [], "missing": [a.name], "errors": [_err_entry(err)]})
        return 0
    want_hw = bool(getattr(a, "have_wiring", False))
    if a.graph:
        g = D.horn_graph(d, a.max, have_wiring=want_hw)
        if getattr(a, "text", False):
            for idx, item in enumerate(g):
                if idx > 0:
                    print()
                _print_horn_text(item)
        else:
            _dump(g)
    else:
        h = D.horn(d, have_wiring=want_hw)
        if resolved_from is not None:
            h["resolved_from"] = resolved_from
        if getattr(a, "text", False):
            _print_horn_text(h)
        else:
            _dump(h)
    return 0


def _print_dom_spine_text(sp: dict[str, Any], ind: int = 0) -> None:
    pad = "  " * ind
    if sp.get("id") == "ROOT" and "children" in sp and "kind" not in sp:
        print("ROOT")
        for ch in sp["children"]:
            print(f"  - {ch['id']}  subtree={ch['subtree']}")
        return
    edge_s = f" via {sp['direct_edge']}" if sp.get("direct_edge") else ""
    cone_s = (
        f" proj_cone={sp['proj_cone']} full_cone={sp['full_cone']}"
        if "full_cone" in sp
        else ""
    )
    print(
        f"{pad}- {sp['id']} [{sp.get('kind', '')}]{edge_s}  "
        f"subtree={sp.get('subtree')} depth={sp.get('depth')} children={sp.get('children_subtree_total', 0)}/{sp.get('children', 0) if isinstance(sp.get('children'), int) else len(sp.get('children', []))}{cone_s}"
    )
    kids = sp.get("children")
    if isinstance(kids, list):
        for ch in kids:
            _print_dom_spine_text(ch, ind + 1)
    if sp.get("pruned_count"):
        print(f"{pad}  ... (+{sp['pruned_count']} child(ren) {sp.get('pruned_reason', 'pruned')})")


def _print_dom_contains_text(doc: dict[str, Any]) -> None:
    rt = doc["root"]
    print(
        f"== dom --contains under {rt['id']} [{rt['kind']}] "
        f"(dom_size={rt['dom_size']}, depth={rt['dom_depth']}, tree={doc['tree']}) =="
    )
    print("dom_in\tcone_in\tcone_dist\tdom_hops\tdom_size\tstatus\tdecl\tidom_or_chain")
    for r in doc["results"]:
        dom_s = "yes" if r["dom_in"] else "no"
        cone_s = "yes" if r["cone_in"] else "no"
        cd_s = str(r["cone_dist"]) if r["cone_dist"] is not None else "-"
        dh_s = str(r["dom_hops"]) if r["dom_hops"] is not None else "-"
        chain = r.get("idom_chain") or []
        if r["dom_in"]:
            owner_s = " <- ".join(chain[:4]) + (" <- ..." if len(chain) > 4 else "")
        else:
            owner_s = f"idom={r['idom'] or 'ROOT'}"
            if len(chain) > 2:
                owner_s += f" (top={chain[-1]})"
        print(
            f"{dom_s}\t{cone_s}\t{cd_s}\t{dh_s}\t{r['dom_size']}\t"
            f"{r['status']}\t{r['id']}\t{owner_s}"
        )


def _cmd_dom(a) -> int:
    D = _dec(a)
    near = getattr(a, "near", None)
    exact_case = bool(getattr(a, "exact_case", False))
    want_text = bool(getattr(a, "text", False)) and not bool(getattr(a, "json", False))

    contains_raw: Optional[list[str]] = getattr(a, "contains", None)
    if contains_raw is not None:
        pos_names: list[str] = list(getattr(a, "names", None) or [])
        if pos_names:
            queries = [*contains_raw, *pos_names[:-1]]
            root_q = pos_names[-1]
        else:
            if len(contains_raw) < 2:
                print(
                    "error: dom --contains requires at least one query and <Root> "
                    "(e.g. decompile dom --contains X Y <Root>)",
                    file=sys.stderr,
                )
                return 2
            queries = list(contains_raw[:-1])
            root_q = contains_raw[-1]

        D.kdb.preload_stems([root_q, *queries])
        r_decl, r_from, r_err = _resolve_single_cmd(
            D, root_q, a.continue_on_error, near=near, exact_case=exact_case
        )
        if r_decl is None:
            assert r_err is not None
            if not a.continue_on_error:
                return 1
            err_doc = {
                "root": {"query": root_q, "id": None},
                "tree": D.kdb.tree_label,
                "results": [],
                "missing": [root_q],
                "errors": [_err_entry(r_err)],
            }
            if want_text:
                _print_missing_summary([root_q], [_err_entry(r_err)])
            else:
                _dump(err_doc)
            return 0

        resolved_targets: list[tuple[str, Decl, Optional[str]]] = []
        missing: list[str] = []
        errors: list[dict] = []
        for q_item in queries:
            try:
                t_res = D.kdb.resolve_unique_detail(q_item, near=near, exact_case=exact_case)
                if t_res.case_folded:
                    _warn_case_fold(q_item, t_res.decl.name)
                resolved_targets.append((q_item, t_res.decl, t_res.resolved_from))
            except ResolveError as err:
                _print_resolve_err(err)
                missing.append(q_item)
                errors.append(_err_entry(err))

        rc_dc = 0 if (not errors or a.continue_on_error) else 1
        if not resolved_targets and not a.continue_on_error:
            return rc_dc

        doc = D.dom_contains(
            r_decl,
            resolved_targets,
            project_only=bool(getattr(a, "project_only", False)),
            kind=getattr(a, "kind", "both"),
        )
        if r_from is not None:
            doc["root"]["resolved_from"] = r_from
        if errors:
            doc["missing"] = missing
            doc["errors"] = errors
        if want_text:
            _print_dom_contains_text(doc)
            _print_missing_summary(missing, errors)
        else:
            _dump(doc)
        return rc_dc

    if not a.names:
        print("error: the following arguments are required: decl", file=sys.stderr)
        return 2

    if len(a.names) == 1 and a.names[0] in ("ROOT", "-"):
        kids = D.kdb.dom_children(None, a.limit, a.min_size)
        root_rows = [{"id": D.kdb.decl(k.decl_id).name, "subtree": k.subtree_size} for k in kids]
        if want_text:
            _print_dom_spine_text({"id": "ROOT", "children": root_rows})
        else:
            _dump(root_rows)
        return 0
    results = []
    missing = []
    errors = []
    for nm in a.names:
        if nm in ("ROOT", "-"):
            kids = D.kdb.dom_children(None, a.limit, a.min_size)
            results.append({"id": "ROOT", "children": [{"id": D.kdb.decl(k.decl_id).name, "subtree": k.subtree_size} for k in kids]})
            continue
        try:
            rdet = D.kdb.resolve_unique_detail(nm, near=near, exact_case=exact_case)
            if rdet.case_folded:
                _warn_case_fold(nm, rdet.decl.name)
        except ResolveError as err:
            _print_resolve_err(err)
            if not a.continue_on_error:
                return 1
            missing.append(nm)
            errors.append(_err_entry(err))
            continue
        sp = D.dom_spine(rdet.decl, a.depth, a.min_size, a.limit, with_cone=a.with_cone)
        if rdet.resolved_from is not None:
            sp["resolved_from"] = rdet.resolved_from
        results.append(sp)
    if want_text:
        for idx, sp in enumerate(results):
            if idx > 0:
                print()
            _print_dom_spine_text(sp)
        _print_missing_summary(missing, errors)
        return 0
    if errors:
        _dump({"results": results, "missing": missing, "errors": errors})
    else:
        _dump(results[0] if len(results) == 1 else results)
    return 0


def _cmd_path(a) -> int:
    D = _dec(a)
    near = getattr(a, "near", None)
    exact_case = bool(getattr(a, "exact_case", False))
    want_text = bool(getattr(a, "text", False)) and not bool(getattr(a, "json", False))
    s, s_from, s_err = _resolve_single_cmd(D, a.src, a.continue_on_error, near=near, exact_case=exact_case)
    t, t_from, t_err = (None, None, None)
    if a.dst is not None and (s is not None or a.continue_on_error):
        t, t_from, t_err = _resolve_single_cmd(D, a.dst, a.continue_on_error, near=near, exact_case=exact_case)
    if s is None or (a.dst is not None and t is None):
        if not a.continue_on_error:
            return 1
        missing: list[str] = []
        errors: list[dict] = []
        if s_err is not None:
            missing.append(a.src)
            errors.append(_err_entry(s_err))
        if t_err is not None:
            missing.append(a.dst)
            errors.append(_err_entry(t_err))
        if want_text:
            _print_missing_summary(missing, errors)
            return 0
        _dump({
            "from": s.name if s is not None else a.src,
            "to": (t.name if t is not None else a.dst),
            "kind": a.kind,
            "project_only": a.project_only,
            "found": False,
            "length": None,
            "path": [],
            "missing": missing,
            "errors": errors,
        })
        return 0
    assert s is not None
    if a.dst is None:
        chain = D.kdb.dom_path(s)
        chain_rows = [{"id": D.kdb.decl(n.decl_id).name, "depth": n.depth, "subtree": n.subtree_size} for n in chain]
        if want_text:
            print("depth\tsubtree\tdecl")
            for row in chain_rows:
                print(f"{row['depth']}\t{row['subtree']}\t{row['id']}")
        else:
            _dump(chain_rows)
        return 0
    assert t is not None
    p = D.shortest_path(s, t, project_only=a.project_only, kind=a.kind)
    out = {
        "from": s.name,
        "to": t.name,
        "kind": a.kind,
        "project_only": a.project_only,
        "found": p is not None,
        "length": (len(p) - 1) if p is not None else None,
        "path": p or [],
    }
    if s_from is not None or t_from is not None:
        rf = {}
        if s_from is not None:
            rf["from"] = s_from
        if t_from is not None:
            rf["to"] = t_from
        out["resolved_from"] = rf
    if want_text:
        if p is None:
            print(f"not found: no {a.kind} path from {s.name} to {t.name}")
        else:
            print(f"found (length={len(p) - 1}, kind={a.kind}):")
            for idx, step in enumerate(p):
                edge_lbl = f"  --[{step['edge']}]--> " if idx > 0 else "  "
                print(f"{edge_lbl}{step['id']} [{step['kind']}]")
    else:
        _dump(out)
    return 0


def _cmd_node(a) -> int:
    D = _dec(a)
    d, resolved_from, err = _resolve_single_cmd(
        D,
        a.name,
        a.continue_on_error,
        near=getattr(a, "near", None),
        exact_case=bool(getattr(a, "exact_case", False)),
    )
    if d is None:
        assert err is not None
        if not a.continue_on_error:
            return 1
        _dump({"results": [], "missing": [a.name], "errors": [_err_entry(err)]})
        return 0
    nd = D.node(d, with_body=False)
    if resolved_from is not None:
        nd["resolved_from"] = resolved_from
    _dump(nd)
    return 0


def _cmd_search(a) -> int:
    try:
        D = _dec(a)
        rows = D.kdb.search_rows(
            a.pattern,
            a.limit,
            project_only=a.project_only,
            no_aux=a.no_aux,
            case_sensitive=a.case_sensitive,
            kind=a.kind,
            module_regex=a.module,
            sort_by=a.sort_by,
            regex=a.regex,
            search_module=a.search_module,
            src_root=D.src_root,
        )
    except (ValueError, FileNotFoundError) as err:
        print(f"error: {err}", file=sys.stderr)
        return 2
    if a.json:
        _dump([
            {
                "id": d.id,
                "kind": d.kind,
                "dom_subtree": dom_sz,
                "fan_in": fi,
                "value_nodes": vn,
                "name": d.name,
                "module": d.module,
                "method": d.method,
            }
            for d, dom_sz, fi, vn in rows
        ])
        return 0
    for d, dom_sz, fi, vn in rows:
        extra = ""
        if a.sort_by == "fan_in":
            extra = f"\tfan_in={fi}"
        elif a.sort_by == "vn":
            extra = f"\tvn={vn}"
        print(f"{d.id}\t{d.kind}\t{dom_sz if dom_sz is not None else '-'}\t{d.name}\t{d.module or d.method}{extra}")
    return 0


def _cmd_validate(a) -> int:
    kdb = None if a.no_db else KernelDB(a.kernel_db, None, a.tree)
    bad = 0
    for p in a.files:
        errs = validate_file(p, kdb)
        print(f"{p}: {'OK' if not errs else f'{len(errs)} error(s)'}")
        for e in errs[:50]:
            print(f"  - {e}")
        bad += bool(errs)
    return 1 if bad else 0


def _print_readers_text(res: dict[str, Any]) -> None:
    mode = res["mode"]
    tgt = res["target"]
    if mode == "field_census":
        print(
            f"== {tgt['name']} [{tgt['keyword']}] field reader census "
            f"({tgt['fields_count']} field(s), anchor={tgt['anchor']}) =="
        )
        print("idx\tlive\ttotal\tanchor\tfield\ttype\tsample_readers")
        for f in res["fields"]:
            samp = ", ".join(f["sample_readers"][:3]) if f["sample_readers"] else "(unread)"
            print(
                f"#{f['index']}\t{f['live_readers']}\t{f['total_readers']}\t{f['anchor']}\t"
                f".{f['field']}\t{f['type']}\t{samp}"
            )
        return

    if mode == "field":
        print(
            f"== {tgt['name']}.{tgt['field']} [field #{tgt['field_index']}/{tgt['fields_total']}] "
            f"({res['live_count']} live / {res['total_count']} reader(s)) anchor={tgt['field_anchor']} =="
        )
        print(f"  type: {tgt['field_type']}")
        rlist = res["readers"]
        if not rlist:
            print("  (0 project field readers found)")
            return
        print("dom\tkind\tlive\tsite\tanchor\tname\tsnippet")
        for r in rlist:
            live_s = "yes" if r["live"] else "no"
            print(
                f"{r['dom_subtree']}\t{r['kind']}\t{live_s}\t{r['site_kind']}\t"
                f"{r['anchor'] or '-'}\t{r['name']}\t{r.get('snippet') or '-'}"
            )
        return

    if mode == "conjunct_census":
        print(
            f"== {tgt['name']} [{tgt['keyword']}] conjunct reader census "
            f"({tgt['conjuncts_total']} conjunct(s), anchor={tgt['anchor']}) =="
        )
        if res.get("wrappers"):
            ws = ", ".join(f"{w['name']} [slot #{w['conjunct_index']}/{w['conjuncts_total']}]" for w in res["wrappers"])
            print(f"  wrappers: {ws}")
        print("conj\tlive\ttotal\tformula\tsample_readers")
        for c in res["conjuncts"]:
            samp = ", ".join(c["sample_readers"][:3]) if c["sample_readers"] else "(0 explicit projections)"
            print(
                f"#{c['conjunct']}\t{c['live_readers']}\t{c['total_readers']}\t"
                f"{c['formula']}\t{samp}"
            )
        return

    # mode == "conjunct"
    print(
        f"== {tgt['name']} [{tgt['keyword']}] conjunct #{tgt['conjunct']}/{tgt['conjuncts_total']} "
        f"({res['live_count']} live / {res['total_count']} reader(s)) anchor={tgt['anchor']} =="
    )
    print(f"  conjunct #{tgt['conjunct']}: {tgt['formula']}")
    if res.get("wrappers"):
        ws = ", ".join(f"{w['name']} [slot #{w['conjunct_index']}/{w['conjuncts_total']}]" for w in res["wrappers"])
        print(f"  wrappers: {ws}")
    rlist = res["readers"]
    if not rlist:
        print("  (0 explicit conjunct readers found)")
        return
    print("dom\tkind\tlive\tsite\tanchor\tname\tsnippet")
    for r in rlist:
        live_s = "yes" if r["live"] else "no"
        print(
            f"{r['dom_subtree']}\t{r['kind']}\t{live_s}\t{r['site_kind']}\t"
            f"{r['anchor'] or '-'}\t{r['name']}\t{r.get('snippet') or '-'}"
        )


def _cmd_readers(a) -> int:
    if getattr(a, "field", None) is not None and getattr(a, "conjunct", None) is not None:
        print("error: pass at most one of --field NAME or --conjunct N", file=sys.stderr)
        return 2
    try:
        D = _dec(a)
    except FileNotFoundError as err:
        print(f"error: {err}", file=sys.stderr)
        return 2
    near = getattr(a, "near", None)
    exact_case = bool(getattr(a, "exact_case", False))
    D.kdb.preload_stems(a.targets)
    results: list[dict[str, Any]] = []
    missing: list[str] = []
    errors: list[dict] = []

    for nm in a.targets:
        try:
            rdet = D.kdb.resolve_unique_detail(nm, near=near, exact_case=exact_case)
            if rdet.case_folded:
                _warn_case_fold(nm, rdet.decl.name)
        except ResolveError as err:
            _print_resolve_err(err)
            missing.append(nm)
            errors.append(_err_entry(err))
            continue
        try:
            res = D.readers(
                rdet.decl,
                field=a.field,
                conjunct=a.conjunct,
                live_only=a.live_only,
                limit=a.limit,
                max_len=a.max_len,
            )
        except ValueError as verr:
            print(f"error [{nm}]: {verr}", file=sys.stderr)
            missing.append(nm)
            errors.append({"query": nm, "error": str(verr), "ambiguous": False, "candidates": []})
            continue
        if rdet.resolved_from is not None:
            res["resolved_from"] = rdet.resolved_from
        if rdet.case_folded:
            res["case_folded"] = True
        results.append(res)

    rc = 0 if (not errors or a.continue_on_error) else 1
    if a.json:
        if errors:
            if results or a.continue_on_error:
                _dump({"results": results, "missing": missing, "errors": errors})
        else:
            _dump(results[0] if len(results) == 1 else results)
        return rc

    for idx, res in enumerate(results):
        if idx > 0:
            print()
        _print_readers_text(res)
    if results or a.continue_on_error:
        _print_missing_summary(missing, errors)
    return rc


def _cmd_spine_map(a) -> int:
    from .spine import build_spine_map
    doc = build_spine_map(_dec(a), top=a.top, log=sys.stderr)
    with open(a.out, "w", encoding="utf-8") as f:
        json.dump(doc, f, ensure_ascii=False, indent=1)
        f.write("\n")
    print(f"wrote {a.out}: {len(doc['nodes'])} nodes, {len(doc['edges'])} edges", file=sys.stderr)
    return 0


def _common(p: argparse.ArgumentParser) -> None:
    p.add_argument("--kernel-db", default=DEFAULT_KERNEL_DB)
    p.add_argument(
        "--leanre-db",
        "--source-db",
        dest="leanre_db",
        default=None,
        help="Path to outputs/leanre.db (auto-detected beside --kernel-db if omitted)",
    )
    p.add_argument("--src", "--src-root", dest="src_root", default=DEFAULT_SRC, help="Path to Lean source root")
    p.add_argument("--config", default=None, help="Path to leanre.toml profile (auto-discovered from --src if omitted)")
    p.add_argument("--tree", default="ALL", help="dom_trees.label (ALL, ROOT:<name>, STMT_ALL)")
    p.add_argument(
        "--near",
        default=None,
        metavar="decl",
        help="Prefer candidates sharing longest namespace/cone prefix with <decl> when disambiguating short names",
    )
    p.add_argument(
        "--exact-case",
        action="store_true",
        help="Refuse case-insensitive fallback resolution (fail instead of case-folding)",
    )


def build_parser(p: argparse.ArgumentParser, dest: str = "decompile_func") -> argparse.ArgumentParser:
    sp = p.add_subparsers(dest="decompile_cmd", required=True)

    def add(name: str, fn, help_: str, epilog: Optional[str] = None) -> argparse.ArgumentParser:
        def _wrapped(a: argparse.Namespace) -> int:
            a._opened_kdbs = []
            try:
                rc = fn(a)
                sys.stdout.flush()
                return rc
            except BrokenPipeError:
                try:
                    devnull = os.open(os.devnull, os.O_WRONLY)
                    os.dup2(devnull, sys.stdout.fileno())
                    os.close(devnull)
                except OSError:
                    pass
                return 0
            finally:
                for k in getattr(a, "_opened_kdbs", ()):
                    k.close()

        q = sp.add_parser(name, help=help_, epilog=epilog)
        _common(q)
        q.set_defaults(**{dest: _wrapped})
        return q

    q = add("resolve", _cmd_resolve, "Resolve exact, exact-case suffix, module-qualified, or fuzzy decl names")
    q.add_argument("queries", nargs="+", metavar="query")
    q.add_argument("--limit", type=int, default=10)
    q.add_argument("--json", action="store_true")
    q.add_argument("--continue-on-error", action="store_true")

    q = add(
        "contract",
        _cmd_contract,
        "Exact header / fields / body of one or more declarations (tip: see `unfold --depth 2` for recursive expansion)",
        epilog=(
            "Tip: To expand nested project definitions/conjuncts in one call instead of chaining "
            "`contract` batches, run: leanre decompile unfold <decl> --depth 2"
        ),
    )
    q.add_argument("names", nargs="+", metavar="decl")
    q.add_argument("--body", action="store_true")
    q.add_argument("--include-thm", action="store_true")
    q.add_argument("--preserve-lines", action="store_true", help="Keep newlines/indentation in --body output")
    q.add_argument(
        "--grep",
        default=None,
        metavar="REGEX",
        help="Filter declaration body lines (or structure fields) by REGEX with .lean line numbers",
    )
    q.add_argument(
        "--fields-grep",
        default=None,
        metavar="REGEX",
        help="Filter structure/class/inductive fields by REGEX (with -C context and .lean line numbers)",
    )
    q.add_argument(
        "-C",
        "--context",
        type=int,
        default=0,
        metavar="N",
        help="Show N lines/fields of context around each --grep / --fields-grep match (default: 0)",
    )
    q.add_argument(
        "--body-lines",
        default=None,
        metavar="A:B",
        help=(
            "Slice inclusive body line range A:B (or bare N for 1:N): 1-based body offset by default, "
            "or prefix with L for 1-based .lean file lines (e.g. L700:715); prints .lean line numbers"
        ),
    )
    q.add_argument(
        "--deps-headers",
        action="store_true",
        help="Print compact 1-hop headers for non-Mathlib project deps referenced by signature/contract",
    )
    q.add_argument(
        "--deps-max",
        type=int,
        default=0,
        metavar="N",
        help="Cap number of --deps-headers entries printed per declaration (0 = all)",
    )
    q.add_argument("--continue-on-error", action="store_true", help="Report missing/ambiguous decls without aborting batch")
    q.add_argument("--table", action="store_true")
    q.add_argument("--json", action="store_true")
    q.add_argument("--max-len", type=int, default=2000)

    q = add(
        "producers",
        _cmd_producers,
        "Find project declarations whose type/codomain constructs or returns <Target>, ranked by dom",
    )
    q.add_argument("targets", nargs="+", metavar="Target")
    q.add_argument("--live-only", action="store_true", help="Restrict to live declarations (live_mask != 0)")
    q.add_argument("--include-dead", action="store_true", help="Also include dead source-only producers from leanre.db")
    q.add_argument(
        "--include-implications",
        action="store_true",
        help="Also report premise/hypothesis consumers, record-field carriers, and wrapper-def producers",
    )
    q.add_argument("--limit", type=int, default=50)
    q.add_argument("--max-len", type=int, default=240)
    q.add_argument("--json", action="store_true")
    q.add_argument("--continue-on-error", action="store_true")

    q = add(
        "readers",
        _cmd_readers,
        "Find project declarations that read/project a structure field (--field) or N-th ∧-conjunct (--conjunct)",
    )
    q.add_argument("targets", nargs="+", metavar="Target")
    q.add_argument("--field", default=None, metavar="NAME", help="Structure/class field name to find readers of")
    q.add_argument("--conjunct", type=int, default=None, metavar="N", help="1-based ∧-conjunct index to find readers of")
    q.add_argument("--live-only", action="store_true", help="Restrict to live declarations (live_mask != 0)")
    q.add_argument("--limit", type=int, default=50)
    q.add_argument("--max-len", type=int, default=220)
    q.add_argument("--json", action="store_true")
    q.add_argument("--text", action="store_true", help="Human-readable table output (default unless --json)")
    q.add_argument("--continue-on-error", action="store_true")

    q = add("unfold", _cmd_unfold, "Recursive contract unfolding to Mathlib/Lean ground types")
    q.add_argument("name")
    q.add_argument("--depth", type=int, default=2)
    q.add_argument("--json", action="store_true")
    q.add_argument("--no-body", action="store_true")
    q.add_argument("--max-len", type=int, default=400)
    q.add_argument("--full-fields", action="store_true")
    q.add_argument("--stop-at", action="append", default=[])
    q.add_argument("--max-fields", type=int, default=None)
    q.add_argument("--continue-on-error", action="store_true")

    q = add("horn", _cmd_horn, "Declaration-level Horn clause (hyps ∧ lemmas → concl), --have-wiring DAG, or BFS Horn graph")
    q.add_argument("name")
    q.add_argument("--graph", action="store_true")
    q.add_argument("--max", type=int, default=100)
    q.add_argument("--have-wiring", action="store_true", help="Extract have/let/obtain proof-step wiring DAG from source body")
    q.add_argument("--text", action="store_true", help="Print compact human-readable Horn / have-wiring summary instead of JSON")
    q.add_argument("--continue-on-error", action="store_true")

    q = add("dom", _cmd_dom, "Dominator spine below decl(s), or batch containment check (--contains X Y <Root>)")
    q.add_argument("names", nargs="*", metavar="decl")
    q.add_argument(
        "--contains",
        nargs="+",
        action="extend",
        default=None,
        metavar="query",
        help="Test whether query decl(s) lie inside <Root>'s dominator subtree and/or reachable cone",
    )
    q.add_argument("--depth", type=int, default=1)
    q.add_argument("--min-size", "--min-subtree", type=int, default=500, dest="min_size")
    q.add_argument("--limit", type=int, default=60)
    q.add_argument("--with-cone", action="store_true")
    q.add_argument("--kind", choices=("type", "value", "both"), default="both", help="Edge kind for --contains cone check")
    q.add_argument("--project-only", action="store_true", help="Restrict --contains cone check to project decls")
    q.add_argument("--text", action="store_true", help="Print compact human-readable table/tree instead of JSON")
    q.add_argument("--json", action="store_true", help="Print JSON output (default unless --text is passed)")
    q.add_argument("--continue-on-error", action="store_true")

    q = add("path", _cmd_path, "idom chain to root (1 arg) or shortest directed edge BFS path (2 args)")
    q.add_argument("src", metavar="from_decl")
    q.add_argument("dst", nargs="?", default=None, metavar="to_decl")
    q.add_argument("--project-only", action="store_true")
    q.add_argument("--kind", choices=("type", "value", "both"), default="both")
    q.add_argument("--text", action="store_true", help="Print compact human-readable path summary instead of JSON")
    q.add_argument("--json", action="store_true", help="Print JSON output (default unless --text is passed)")
    q.add_argument("--continue-on-error", action="store_true")

    q = add("node", _cmd_node, "leanre.decomp/v1 node skeleton for a decl")
    q.add_argument("name")
    q.add_argument("--continue-on-error", action="store_true")

    q = add("search", _cmd_search, "Search kernel decl names with project/kind/instance/aux/module filters")
    q.add_argument("pattern")
    q.add_argument("--limit", type=int, default=50)
    q.add_argument("--project-only", action="store_true")
    q.add_argument("--no-aux", action="store_true", help="Exclude compiler/tactic auxiliary decls")
    q.add_argument("--include-aux", action="store_false", dest="no_aux", default=argparse.SUPPRESS,
                   help="Include auxiliary decls (overrides --no-aux)")
    q.add_argument("--case-sensitive", action="store_true")
    q.add_argument("--kind", default=None, help="Comma-separated kind filter: thm,def,inductive,instance,axiom,opaque,quot")
    q.add_argument("--module", default=None, help="Regex filter on decl_module.module")
    q.add_argument("--regex", action="store_true", help="Treat pattern as Python regex (supports | alternation)")
    q.add_argument("--search-module", action="store_true", help="Match pattern across both module and decl.name")
    q.add_argument("--sort-by", choices=("name", "dom", "fan_in", "vn"), default="name")
    q.add_argument("--json", action="store_true")
    q.set_defaults(no_aux=False)

    q = add("validate", _cmd_validate, "Validate outputs/decomp/*.json against leanre.decomp/v1")
    q.add_argument("files", nargs="+")
    q.add_argument("--no-db", action="store_true")
    q = add("spine-map", _cmd_spine_map, "Regenerate outputs/decomp/spine_map.json")
    q.add_argument("--out", default="outputs/decomp/spine_map.json")
    q.add_argument("--top", type=int, default=60)
    return p


def register_cli(sub: Any, dest: str = "decompile_func") -> argparse.ArgumentParser:
    """Attach `decompile` to a leanre argparse subparsers object."""
    p = sub.add_parser("decompile", help="Proof decompiler: contracts, producers, unfolding, Horn graph, dominator spine")
    return build_parser(p, dest)


def main(argv: Optional[list[str]] = None) -> int:
    ap = argparse.ArgumentParser(prog="leanre decompile")
    build_parser(ap)
    a = ap.parse_args(argv)
    return int(a.decompile_func(a))
