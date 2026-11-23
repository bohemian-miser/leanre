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
    resolve_leanre_db_path,
)
from .schema import validate_file
from .source import (
    Contract,
    find_dead_in_src,
    format_anchor,
    grep_body_lines,
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
    results = []
    any_miss = False
    for query in a.queries:
        hits = kdb.resolve(query, limit=a.limit, near=near)
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
        has_strong = any(h.match in ("exact", "suffix", "unqualified") for h in hits)
        if not has_strong:
            src_hits = kdb.find_source_decls(query, limit=a.limit)
            if not src_hits and kdb.l is None and not hits:
                dead_cs = find_dead_in_src(eff_src, query, limit=a.limit, anchor_prefix=anchor_prefix)
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
        if not cands:
            any_miss = True
        results.append({
            "query": query,
            "exact": bool(hits and hits[0].match == "exact"),
            "candidates": cands,
        })

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


def _find_dead_contracts(
    kdb: KernelDB,
    src_root: str,
    query: str,
    *,
    include_thm: bool,
    preserve_lines: bool,
    anchor_prefix: str,
) -> list[tuple[Contract, str, Optional[str]]]:
    """Fallback lookup for dead declarations absent from `kernel.db`."""
    rows = kdb.find_source_decls(query)
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
        print(f"  error [{e['query']}]: {e['error']}")


def _wants_instance_summary(c: Contract) -> bool:
    if c.keyword in ("structure", "class", "inductive"):
        return True
    if c.keyword in ("def", "abbrev") and c.type and _SORT_TYPE_RE.search(c.type):
        return True
    return False


def _cmd_contract(a) -> int:
    # Validate --grep and --body-lines syntax upfront before scanning
    grep_pat: Optional[str] = getattr(a, "grep", None)
    body_lines_spec: Optional[str] = getattr(a, "body_lines", None)
    context_n: int = getattr(a, "context", 0)
    if context_n < 0:
        print(f"error: invalid --context {context_n}: must be >= 0", file=sys.stderr)
        return 2
    if grep_pat is not None:
        try:
            re.compile(grep_pat)
        except re.error as err:
            print(f"error: invalid --grep regex {grep_pat!r}: {err}", file=sys.stderr)
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

    entries: list[tuple[str, Any]] = []  # ("live", (Decl, resolved_from)) | ("dead", (query, matches))
    missing: list[str] = []
    errors: list[dict] = []

    for nm in a.names:
        try:
            d, resolved_from = D.kdb.resolve_unique(nm, near=near)
            entries.append(("live", (d, resolved_from)))
        except ResolveError as err:
            dead_matches = [] if err.ambiguous else _find_dead_contracts(
                D.kdb,
                D.src_root,
                nm,
                include_thm=eff_include_thm,
                preserve_lines=eff_preserve,
                anchor_prefix=D.anchor_prefix,
            )
            if dead_matches:
                entries.append(("dead", (nm, dead_matches)))
                continue
            if not a.continue_on_error:
                _print_resolve_err(err)
                return 1
            _print_resolve_err(err)
            missing.append(nm)
            errors.append(_err_entry(err))

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
                d, resolved_from = payload
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
                rows.append(row)
            else:
                _nm, matches = payload
                c, dkind, dmod = matches[0]
                rows.append({
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
                })
        if a.json:
            _dump({"results": rows, "missing": missing, "errors": errors} if errors else rows)
        else:
            print("id\tkind\tdom\tfan_in\tmodule\tanchor\theader")
            for r in rows:
                rid = r["id"] if r["id"] is not None else "-"
                dom_s = r["dom_subtree"] if r["dom_subtree"] is not None else "-"
                fi_s = r["fan_in"] if r["fan_in"] is not None else "-"
                hdr = r["header"] or "-"
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
            nm, matches = payload
            c, dkind, dmod = matches[0]
            others = matches[1:]
            with_body = eff_body and (eff_include_thm or dkind not in ("thm", "theorem", "lemma"))
            fmeta = (
                _print_filtered_body(c, body_lines_spec=body_lines_spec, grep_pat=grep_pat, context=context_n)
                if (has_body_filter and c.body is not None)
                else None
            )
            if a.json:
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
                    "contract": c.to_json(a.max_len, with_body=with_body, preserve_lines=eff_preserve),
                }
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
            for f in c.fields:
                print(f"    .{f.name} : {' '.join(f.type.split())}")
            if fmeta is not None:
                _render_filtered_body_text(c, fmeta)
            elif with_body and c.body is not None:
                _print_contract_body(c.body, a.max_len, eff_preserve, total_lines=len(c.body_lines))
            for oc, okind, _omod in others:
                print(f"  other    : {oc.name} [{okind}] ({oc.anchor})")
            continue

        d, resolved_from = payload
        c = D.contract(d, include_thm=eff_include_thm, preserve_lines=eff_preserve)
        with_body = eff_body and (eff_include_thm or d.kind != "thm")
        need_stats = c is None or d.ground
        st = D.kdb.decl_stats(d) if need_stats else None
        pkg = _match_package(d.name, get_manifest()) if d.ground else None
        dep_hdrs = D.deps_headers(d, max_len=a.max_len) if getattr(a, "deps_headers", False) else None
        inst_info = D.attached_instances(d) if (c is not None and _wants_instance_summary(c)) else None
        fmeta = (
            _print_filtered_body(c, body_lines_spec=body_lines_spec, grep_pat=grep_pat, context=context_n)
            if (has_body_filter and c is not None and c.body is not None)
            else None
        )

        if a.json:
            item = {
                "decl": {"id": d.id, "name": d.name, "kind": d.kind, "module": d.module, "method": d.method},
                "contract": c.to_json(a.max_len, with_body=with_body, preserve_lines=eff_preserve) if c else None,
            }
            if resolved_from is not None:
                item["resolved_from"] = resolved_from
            if dep_hdrs is not None:
                item["deps_headers"] = dep_hdrs
            if inst_info is not None and inst_info["count"] > 0:
                item["attached_instances"] = inst_info
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
        if c is None:
            print("  (no source contract: ground Mathlib/Lean decl)" if d.ground else "  OPAQUE: source not located")
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
            print(f"  field_of : {pi['name']} [{pi['keyword']}] ({pi['fields_count']} fields, {pi['anchor']})")
        if c.namespace:
            print(f"  namespace: {c.namespace}")
        for v in c.variables:
            print(f"  variable : {v}")
        print(f"  header   : {one_line(c.header, a.max_len)}")
        if c.extends:
            print(f"  extends  : {', '.join(c.extends)}")
        for f in c.fields:
            print(f"    .{f.name} : {' '.join(f.type.split())}")
        if fmeta is not None:
            _render_filtered_body_text(c, fmeta)
        elif with_body and c.body is not None:
            _print_contract_body(c.body, a.max_len, eff_preserve, total_lines=len(c.body_lines))
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
    results: list[dict[str, Any]] = []
    missing: list[str] = []
    errors: list[dict] = []

    for nm in a.targets:
        try:
            d, resolved_from = D.kdb.resolve_unique(nm, near=near)
        except ResolveError as err:
            _print_resolve_err(err)
            if not a.continue_on_error:
                return 1
            missing.append(nm)
            errors.append(_err_entry(err))
            continue
        res = D.producers(
            d,
            live_only=a.live_only,
            include_dead=a.include_dead,
            limit=a.limit,
            max_len=a.max_len,
        )
        if resolved_from is not None:
            res["resolved_from"] = resolved_from
        results.append(res)

    if a.json:
        if errors:
            _dump({"results": results, "missing": missing, "errors": errors})
        else:
            _dump(results[0] if len(results) == 1 else results)
        return 0

    for idx, res in enumerate(results):
        if idx > 0:
            print()
        tgt = res["target"]
        kw = tgt.get("keyword") or tgt["kind"]
        print(
            f"== {tgt['name']} [{kw}] ({res['live_count']} live / {res['total_count']} producer(s)) "
            f"anchor={tgt.get('anchor') or tgt.get('module') or '-'} =="
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
            if res.get("embedded_in_defs"):
                print(f"  embedded in def(s): {', '.join(res['embedded_in_defs'])}")
            if res.get("dead_source_producers"):
                print(
                    f"  dead source producer(s) ({len(res['dead_source_producers'])}; pass --include-dead): "
                    + ", ".join(dp["name"] for dp in res["dead_source_producers"])
                )
    _print_missing_summary(missing, errors)
    return 0


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
) -> tuple[Optional[Decl], Optional[str], Optional[ResolveError]]:
    try:
        d, resolved_from = D.kdb.resolve_unique(name, near=near)
        return d, resolved_from, None
    except ResolveError as err:
        _print_resolve_err(err)
        if not continue_on_error:
            return None, None, err
        return None, None, err


def _cmd_unfold(a) -> int:
    D = _dec(a)
    d, resolved_from, err = _resolve_single_cmd(D, a.name, a.continue_on_error, near=getattr(a, "near", None))
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


def _print_horn_text(h: dict[str, Any]) -> None:
    print(f"{h['via']}  [{h['kind']}]  {h.get('anchor') or ''}")
    if h.get("header"):
        print(f"  header : {h['header']}")
    print(f"  hyps   : {', '.join(h['hyps']) if h['hyps'] else '(none)'}")
    print(f"  concl  : {', '.join(h['concl']) if h['concl'] else '(none)'}")
    print(f"  lemmas : {', '.join(h['lemmas_project']) if h['lemmas_project'] else '(none)'}")
    hw = h.get("have_wiring")
    if not hw:
        return
    if hw.get("destructured"):
        print("  obtain :")
        for ob in hw["destructured"]:
            print(f"    L{ob['line']}: ⟨{', '.join(ob['vars'])}⟩ := {ob['from']}  <- {ob['root_hyps']}")
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


def _cmd_horn(a) -> int:
    D = _dec(a)
    d, resolved_from, err = _resolve_single_cmd(D, a.name, a.continue_on_error, near=getattr(a, "near", None))
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


def _cmd_dom(a) -> int:
    D = _dec(a)
    near = getattr(a, "near", None)
    if len(a.names) == 1 and a.names[0] in ("ROOT", "-"):
        kids = D.kdb.dom_children(None, a.limit, a.min_size)
        _dump([{"id": D.kdb.decl(k.decl_id).name, "subtree": k.subtree_size} for k in kids])
        return 0
    results = []
    missing: list[str] = []
    errors: list[dict] = []
    for nm in a.names:
        if nm in ("ROOT", "-"):
            kids = D.kdb.dom_children(None, a.limit, a.min_size)
            results.append({"id": "ROOT", "children": [{"id": D.kdb.decl(k.decl_id).name, "subtree": k.subtree_size} for k in kids]})
            continue
        try:
            d, resolved_from = D.kdb.resolve_unique(nm, near=near)
        except ResolveError as err:
            _print_resolve_err(err)
            if not a.continue_on_error:
                return 1
            missing.append(nm)
            errors.append(_err_entry(err))
            continue
        sp = D.dom_spine(d, a.depth, a.min_size, a.limit, with_cone=a.with_cone)
        if resolved_from is not None:
            sp["resolved_from"] = resolved_from
        results.append(sp)
    if errors:
        _dump({"results": results, "missing": missing, "errors": errors})
    else:
        _dump(results[0] if len(results) == 1 else results)
    return 0


def _cmd_path(a) -> int:
    D = _dec(a)
    near = getattr(a, "near", None)
    s, s_from, s_err = _resolve_single_cmd(D, a.src, a.continue_on_error, near=near)
    t, t_from, t_err = (None, None, None)
    if a.dst is not None and (s is not None or a.continue_on_error):
        t, t_from, t_err = _resolve_single_cmd(D, a.dst, a.continue_on_error, near=near)
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
        _dump([{"id": D.kdb.decl(n.decl_id).name, "depth": n.depth, "subtree": n.subtree_size} for n in chain])
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
    _dump(out)
    return 0


def _cmd_node(a) -> int:
    D = _dec(a)
    d, resolved_from, err = _resolve_single_cmd(D, a.name, a.continue_on_error, near=getattr(a, "near", None))
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


def build_parser(p: argparse.ArgumentParser, dest: str = "decompile_func") -> argparse.ArgumentParser:
    sp = p.add_subparsers(dest="decompile_cmd", required=True)

    def add(name: str, fn, help_: str, epilog: Optional[str] = None) -> argparse.ArgumentParser:
        def _wrapped(a: argparse.Namespace) -> int:
            a._opened_kdbs = []
            try:
                return fn(a)
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
        help="Filter declaration body lines by REGEX with .lean line numbers (implies --body --include-thm --preserve-lines)",
    )
    q.add_argument(
        "-C",
        "--context",
        type=int,
        default=0,
        metavar="N",
        help="Show N lines of context around each --grep match (default: 0)",
    )
    q.add_argument(
        "--body-lines",
        default=None,
        metavar="A:B",
        help=(
            "Slice inclusive body line range A:B: 1-based body offset by default (e.g. 1:30 or +1:30), "
            "or prefix with L for 1-based .lean file lines (e.g. L700:715); prints .lean line numbers"
        ),
    )
    q.add_argument(
        "--deps-headers",
        action="store_true",
        help="Print compact 1-hop headers for non-Mathlib project deps referenced by signature/contract",
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
    q.add_argument("--limit", type=int, default=50)
    q.add_argument("--max-len", type=int, default=240)
    q.add_argument("--json", action="store_true")
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

    q = add("dom", _cmd_dom, "Dominator spine below one or more decls (name or ROOT)")
    q.add_argument("names", nargs="+", metavar="decl")
    q.add_argument("--depth", type=int, default=1)
    q.add_argument("--min-size", "--min-subtree", type=int, default=500, dest="min_size")
    q.add_argument("--limit", type=int, default=60)
    q.add_argument("--with-cone", action="store_true")
    q.add_argument("--continue-on-error", action="store_true")

    q = add("path", _cmd_path, "idom chain to root (1 arg) or shortest directed edge BFS path (2 args)")
    q.add_argument("src", metavar="from_decl")
    q.add_argument("dst", nargs="?", default=None, metavar="to_decl")
    q.add_argument("--project-only", action="store_true")
    q.add_argument("--kind", choices=("type", "value", "both"), default="both")
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
