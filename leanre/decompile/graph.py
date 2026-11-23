"""Decompiler: kernel graph + source contracts -> contract unfolding, Horn clauses, dominator spine,
producers, cones/slices.  All results are plain dicts (JSON-ready, `leanre.decomp/v1` node shape)."""
from __future__ import annotations

import os
from collections import deque
from typing import Any, Iterable, Optional

from .kdb import BOTH, EDGE_REL, TYPE, VALUE, Decl, KernelDB, DEFAULT_SRC, _chunks, _escape_like, is_auto_instance_name
from .readers import analyze_conjunct_readers, analyze_structure_readers, split_target_conjuncts
from .source import (
    Contract,
    classify_codomain_producer,
    enrich_term_wiring_with_callee,
    extract_have_wiring,
    format_anchor,
    identifiers,
    locate_auto_instance_contract,
    one_line,
    read_contract,
    resolve_source_config,
    split_header,
)

CONTRACT_KINDS = ("def", "inductive", "opaque", "axiom", "quot")
# Lean/Mathlib plumbing that is never interesting as a contract leaf.
_NOISE_PREFIX = ("inst", "Lean.", "OfNat.", "HDiv.", "HAdd.", "HMul.", "HSub.", "HPow.", "Eq", "Nat.inst", "Real.inst",
                 "Complex.inst", "Int.inst", "Rat.inst", "Decidable", "And", "Or", "Not", "Iff", "Exists", "True",
                 "False", "outParam", "id", "autoParam", "optParam")


def _noise(name: str) -> bool:
    last = name.rsplit(".", 1)[-1]
    return (name.startswith(_NOISE_PREFIX) or last.startswith("inst") or last.startswith("to")
            and last[2:3].isupper() or "._" in name)


def _arrow_split(t: str) -> list[str]:
    """Split a statement at depth-0 `→` (premises..., conclusion)."""
    out, depth, cur = [], 0, []
    for ch in t:
        if ch in "([{⦃⟨":
            depth += 1
        elif ch in ")]}⦄⟩":
            depth = max(0, depth - 1)
        if ch == "→" and depth == 0:
            out.append("".join(cur)); cur = []
        else:
            cur.append(ch)
    out.append("".join(cur))
    return [x.strip() for x in out if x.strip()]


def _normalize_stop(stop_at: Optional[Iterable[str]]) -> list[str]:
    out: list[str] = []
    for item in stop_at or ():
        for part in str(item).split(","):
            s = part.strip()
            if s and s not in out:
                out.append(s)
    return out


def _matches_stop(name: str, rules: list[str]) -> bool:
    for r in rules:
        if name == r or name.endswith("." + r) or name.startswith(r + "."):
            return True
    return False


class Decompiler:
    def __init__(
        self,
        kdb: Optional[KernelDB] = None,
        src_root: str = DEFAULT_SRC,
        *,
        config_path: Optional[str] = None,
    ) -> None:
        self.kdb = kdb or KernelDB()
        self._src_cfg = resolve_source_config(src_root, config_path)
        self.src_root = src_root or self._src_cfg["resolved_src_root"] or DEFAULT_SRC
        self.anchor_prefix: str = self._src_cfg["anchor_prefix"]
        self.upstream_url_template: str = self._src_cfg["upstream_url_template"]
        self.pinned_commit: str = self._src_cfg["pinned_commit"]
        self._contracts: dict[tuple[int, str], Optional[Contract]] = {}
        self._thm_contracts: dict[tuple[int, str], Optional[Contract]] = {}
        self._preserved_contracts: dict[tuple[int, str, bool], Optional[Contract]] = {}

    # ---- contracts ---------------------------------------------------
    def locate(self, d: Decl) -> tuple[Optional[str], Optional[int], Optional[str]]:
        """(rel_file, line_hint, snippet) for a project decl."""
        row = self.kdb.src_row(d)
        if row:
            return row["file"], row["line"], row["snippet"]
        if d.module:
            return self.kdb.module_file(d.module), None, None
        return None, None, None

    def _locate_auto_instance(
        self,
        d: Decl,
        *,
        include_thm: bool = False,
        preserve_lines: bool = False,
        include_scope: bool = True,
    ) -> Optional[Contract]:
        """Locate anonymous `instance : Class (Carrier ...)` or `deriving` blocks for elaborated auto-instances."""
        tdeps = [x for x, _ in self.kdb.deps(d, (TYPE, BOTH)) if x.id != d.id]
        proj_tdeps = [x for x in tdeps if not x.ground and not x.is_aux]
        carrier_stems = list(dict.fromkeys(x.name.rsplit(".", 1)[-1] for x in proj_tdeps))
        type_stems = list(dict.fromkeys(x.name.rsplit(".", 1)[-1] for x in tdeps))

        cand_modules: list[str] = []
        if d.module:
            cand_modules.append(d.module)
        for x in proj_tdeps:
            if x.module and x.module not in cand_modules:
                cand_modules.append(x.module)

        line_hints_by_mod: dict[str, list[int]] = {}
        if self.kdb.l is not None:
            ns = d.name.rsplit(".", 1)[0] if "." in d.name else ""
            if ns:
                for mod, lno in self.kdb.l.execute(
                    "SELECT module, line_no FROM declarations WHERE kind='instance' AND name LIKE ? ESCAPE '!' LIMIT 50",
                    (f"{_escape_like(ns)}.!_anon!_%",),
                ):
                    mstr = str(mod)
                    if mstr not in cand_modules:
                        cand_modules.append(mstr)
                    line_hints_by_mod.setdefault(mstr, []).append(int(lno))
            for mod in list(cand_modules):
                if mod not in line_hints_by_mod:
                    rows = self.kdb.l.execute(
                        "SELECT line_no FROM declarations WHERE module=? AND kind='instance' ORDER BY line_no LIMIT 50",
                        (mod,),
                    ).fetchall()
                    line_hints_by_mod[mod] = [int(r[0]) for r in rows]

        for mod in cand_modules[:6]:
            rel_file = self.kdb.module_file(mod)
            if not rel_file:
                continue
            found = locate_auto_instance_contract(
                self.src_root,
                rel_file,
                d.name,
                carrier_stems=carrier_stems,
                type_stems=type_stems,
                line_hints=line_hints_by_mod.get(mod, ()),
                include_thm=include_thm,
                preserve_lines=preserve_lines,
                anchor_prefix=self.anchor_prefix,
                include_scope=include_scope,
            )
            if found is not None:
                return found
        return None

    def contract(self, key: int | str | Decl, include_thm: bool = False,
                 preserve_lines: bool = False, include_scope: bool = True) -> Optional[Contract]:
        if isinstance(key, Decl):
            d = key
        else:
            d = self.kdb.maybe(key) or (self.kdb.resolve_unique(key)[0] if isinstance(key, str) else self.kdb.decl(key))
        ckey = (d.id, d.name)
        if include_scope:
            if preserve_lines:
                if (d.id, d.name, include_thm) in self._preserved_contracts:
                    return self._preserved_contracts[(d.id, d.name, include_thm)]
            else:
                cache = self._thm_contracts if include_thm else self._contracts
                if ckey in cache:
                    return cache[ckey]
        elif not preserve_lines and not include_thm and ckey in self._contracts:
            return self._contracts[ckey]

        c = None
        if not d.ground:
            f, hint, _ = self.locate(d)
            if f and d.kind != "ctor":
                c = read_contract(
                    self.src_root,
                    f,
                    d.name,
                    hint,
                    include_thm=include_thm,
                    preserve_lines=preserve_lines,
                    anchor_prefix=self.anchor_prefix,
                    include_scope=include_scope,
                )
            if c is None and f and "." in d.name:
                parent, last = d.name.rsplit(".", 1)
                pc = read_contract(
                    self.src_root,
                    f,
                    parent,
                    hint,
                    include_thm=include_thm,
                    preserve_lines=preserve_lines,
                    anchor_prefix=self.anchor_prefix,
                    include_scope=include_scope,
                )
                if pc is not None:
                    if d.kind == "ctor" or (pc.keyword in ("structure", "class") and last == "mk"):
                        fld = next((x for x in pc.fields if x.name == last), None)
                        if fld is not None and pc.keyword == "inductive":
                            c = Contract(
                                name=d.name,
                                keyword="ctor",
                                file=pc.file,
                                line=fld.line if fld.line is not None else pc.line,
                                header=f"constructor {parent}.{last} : {' '.join(fld.type.split())}",
                                type=fld.type,
                                namespace=pc.namespace,
                                variables=pc.variables,
                                anchor_prefix=self.anchor_prefix,
                                parent_info={
                                    "name": parent,
                                    "keyword": pc.keyword,
                                    "fields_count": len(pc.fields),
                                    "anchor": pc.anchor,
                                    "is_constructor": True,
                                    "instantiations_cmd": f"leanre bundles --instantiations {parent}",
                                },
                            )
                        else:
                            fld_sig = " → ".join(
                                f"({x.name} : {' '.join(x.type.split())})" for x in pc.fields[:8]
                            )
                            if len(pc.fields) > 8:
                                fld_sig += f" → … (+{len(pc.fields) - 8} fields)"
                            arrow_s = f"{fld_sig} → {parent}" if fld_sig else parent
                            c = Contract(
                                name=d.name,
                                keyword="ctor",
                                file=pc.file,
                                line=pc.line,
                                header=f"constructor {d.name} : {arrow_s}",
                                binders=list(pc.binders),
                                type=arrow_s,
                                fields=list(pc.fields),
                                namespace=pc.namespace,
                                variables=pc.variables,
                                anchor_prefix=self.anchor_prefix,
                                parent_info={
                                    "name": parent,
                                    "keyword": pc.keyword,
                                    "fields_count": len(pc.fields),
                                    "anchor": pc.anchor,
                                    "is_constructor": True,
                                    "instantiations_cmd": f"leanre bundles --instantiations {parent}",
                                },
                            )
                    else:
                        fld = next((x for x in pc.fields if x.name == last), None)
                        if fld is not None:  # structure projection -> synthesize from parent field
                            c = Contract(
                                name=d.name,
                                keyword="field",
                                file=pc.file,
                                line=fld.line if fld.line is not None else pc.line,
                                header=f"{parent}.{last} : {' '.join(fld.type.split())}",
                                type=fld.type,
                                namespace=pc.namespace,
                                variables=pc.variables,
                                anchor_prefix=self.anchor_prefix,
                                parent_info={
                                    "name": parent,
                                    "keyword": pc.keyword,
                                    "fields_count": len(pc.fields),
                                    "anchor": pc.anchor,
                                },
                            )
                        elif d.is_aux:
                            c = pc
            if c is None and (d.method == "unmatched:project_auto_instance" or is_auto_instance_name(d.name)):
                c = self._locate_auto_instance(
                    d,
                    include_thm=include_thm,
                    preserve_lines=preserve_lines,
                    include_scope=include_scope,
                )
        if include_scope:
            if preserve_lines:
                self._preserved_contracts[(d.id, d.name, include_thm)] = c
            else:
                cache = self._thm_contracts if include_thm else self._contracts
                cache[ckey] = c
        return c

    def deps_headers(self, key: int | str | Decl, max_len: int = 240, max_deps: int = 0) -> list[dict[str, Any]]:
        """1-hop project contract/signature headers referenced by `key` (solves opened-namespace opacity)."""
        if isinstance(key, Decl):
            d = key
        else:
            d = self.kdb.maybe(key) or (self.kdb.resolve_unique(key)[0] if isinstance(key, str) else self.kdb.decl(key))
        kinds = (TYPE, BOTH) if d.kind == "thm" else (TYPE, VALUE, BOTH)
        out: list[dict[str, Any]] = []
        edges = [
            (x, ek)
            for x, ek in self.kdb.deps(d, kinds)
            if x.id != d.id and not x.ground and not x.is_aux
        ]
        edges.sort(key=lambda t: (0 if t[1] in (TYPE, BOTH) else 1, t[0].name))
        if max_deps > 0:
            edges = edges[:max_deps]
        self.kdb.preload_src_rows([x for x, _ in edges])
        for x, ek in edges:
            xc = self.contract(x, include_scope=False)
            hdr = one_line(xc.header, max_len) if xc else None
            if xc and xc.body and xc.keyword in ("abbrev", "def") and xc.type is None and hdr:
                short_b = one_line(xc.body, max(80, max_len - len(hdr) - 4))
                if short_b:
                    hdr = f"{hdr} := {short_b}"
            out.append({
                "id": x.id,
                "name": x.name,
                "kind": x.kind,
                "keyword": xc.keyword if xc else None,
                "edge": EDGE_REL[ek],
                "module": x.module,
                "anchor": xc.anchor if xc else None,
                "header": hdr,
            })
        return out

    def attached_instances(self, key: int | str | Decl, limit: int = 6) -> dict[str, Any]:
        """Fast `<2ms` summary of instances whose type references `key` (`edges_dst` + same-module `leanre.db`)."""
        if isinstance(key, Decl):
            d = key
        else:
            d = self.kdb.maybe(key) or (self.kdb.resolve_unique(key)[0] if isinstance(key, str) else self.kdb.decl(key))
        rows = self.kdb.k.execute(
            "SELECT src FROM edges WHERE dst=? AND kind IN (1, 3) LIMIT 2000",
            (d.id,),
        ).fetchall()
        inst_decls = [
            u for u in self.kdb.decls([int(r[0]) for r in rows])
            if u.id != d.id and not u.is_aux and self.kdb.is_instance(u, src_root=self.src_root)
        ]
        proj_inst = [u for u in inst_decls if not u.ground]
        ext_inst = [u for u in inst_decls if u.ground]

        same_mod: list[dict[str, Any]] = []
        if self.kdb.l is not None and d.module:
            stem = d.name.rsplit(".", 1)[-1]
            mrows = self.kdb.l.execute(
                "SELECT d.name, d.line_no, d.signature_snippet, m.file_path "
                "FROM declarations d JOIN modules m ON m.name = d.module "
                "WHERE d.module = ? AND d.kind = 'instance' AND d.signature_snippet LIKE ? ESCAPE '!' "
                "ORDER BY d.line_no LIMIT ?",
                (d.module, f"%{_escape_like(stem)}%", limit),
            ).fetchall()
            for nm, lno, snip, fp in mrows:
                same_mod.append({
                    "name": nm,
                    "anchor": format_anchor(fp, int(lno), self.anchor_prefix),
                    "header": one_line(snip, 180),
                })

        total = max(len(proj_inst) + len(ext_inst), len(same_mod))
        return {
            "count": total,
            "project_count": max(len(proj_inst), len(same_mod)),
            "external_count": len(ext_inst),
            "same_module": same_mod[:limit],
            "instances": [u.name for u in (proj_inst + ext_inst)[:limit]],
        }

    def producers(
        self,
        key: int | str | Decl,
        *,
        live_only: bool = False,
        include_dead: bool = False,
        include_implications: bool = False,
        limit: int = 50,
        max_len: int = 240,
    ) -> dict[str, Any]:
        """Find declarations whose type/codomain constructs or concludes `key`, ranked by `dom` descending."""
        if isinstance(key, Decl):
            d = key
        else:
            d = self.kdb.maybe(key) or (self.kdb.resolve_unique(key)[0] if isinstance(key, str) else self.kdb.decl(key))
        tc = self.contract(d)
        q = (
            "SELECT e.src, d2.live_mask, COALESCE(dom.subtree_size, 0) AS dom_sz, d2.fan_in "
            "FROM edges e "
            "JOIN decls d2 ON d2.id = e.src "
            "LEFT JOIN dom ON dom.tree_id = ? AND dom.decl_id = d2.id "
            "WHERE e.dst = ? AND e.kind IN (1, 3) "
            "ORDER BY (d2.live_mask != 0) DESC, dom_sz DESC, d2.fan_in DESC"
        )
        raw_rows = self.kdb.k.execute(q, (self.kdb._all_tree_id, d.id)).fetchall()
        cand_ids = [int(r[0]) for r in raw_rows if int(r[0]) != d.id]
        meta_by_id = {int(r[0]): (int(r[1]), int(r[2]), int(r[3])) for r in raw_rows}
        decls_list = [
            u for u in self.kdb.decls(cand_ids)
            if not u.ground and not u.is_aux and (not live_only or meta_by_id[u.id][0] != 0)
        ]
        self.kdb.preload_src_rows(decls_list)

        # Fast pre-screening via leanre.db `horn_proves` / `signature_snippet` when fan-in is huge (>300)
        stem = d.name.rsplit(".", 1)[-1]
        src_hint_map: dict[int, tuple[Optional[str], Optional[str], Optional[str], Optional[int]]] = {}
        if self.kdb.l is not None and len(decls_list) > 300:
            sids = [u.src_decl_id for u in decls_list if u.src_decl_id is not None]
            for chunk in _chunks(sids, 900):
                iq = (
                    "SELECT d.id, d.horn_proves, d.signature_snippet, m.file_path, d.line_no "
                    f"FROM declarations d JOIN modules m ON m.name = d.module WHERE d.id IN ({','.join('?' * len(chunk))})"
                )
                for sid, hp, snip, fp, lno in self.kdb.l.execute(iq, chunk):
                    src_hint_map[int(sid)] = (hp, snip, fp, int(lno))

        results: list[dict[str, Any]] = []
        premise_consumers: list[dict[str, Any]] = []
        record_fields: list[dict[str, Any]] = []
        for u in decls_list:
            live_mask, dom_sz, fan_in = meta_by_id[u.id]
            if u.src_decl_id in src_hint_map:
                hp, snip, fp, lno = src_hint_map[u.src_decl_id]
                if hp and (hp == stem or hp.endswith("." + stem) or d.name.endswith("." + hp)):
                    results.append({
                        "id": u.id,
                        "name": u.name,
                        "kind": u.kind,
                        "live": live_mask != 0,
                        "live_mask": live_mask,
                        "dom_subtree": dom_sz,
                        "fan_in": fan_in,
                        "role": "direct",
                        "module": u.module,
                        "anchor": format_anchor(fp, lno, self.anchor_prefix) if (fp and lno) else None,
                        "header": one_line(snip, max_len),
                    })
                    continue
                # If snippet is NOT truncated (len < 235) and does not mention `stem` after `:`, skip disk read
                if snip and len(snip) < 235 and not snip.endswith("..."):
                    _, _, _, s_typ, _ = split_header(snip)
                    if classify_codomain_producer(s_typ, d.name) is None:
                        premise_consumers.append({
                            "id": u.id,
                            "name": u.name,
                            "kind": u.kind,
                            "live": live_mask != 0,
                            "dom_subtree": dom_sz,
                            "fan_in": fan_in,
                            "anchor": format_anchor(fp, lno, self.anchor_prefix) if (fp and lno) else None,
                            "header": one_line(snip, max_len),
                        })
                        continue

            uc = self.contract(u, include_scope=False)
            if uc is None:
                continue
            if uc.keyword == "field":
                pi = uc.parent_info or {}
                record_fields.append({
                    "field": u.name,
                    "structure": pi.get("name"),
                    "live": live_mask != 0,
                    "dom_subtree": dom_sz,
                    "conditional": bool(uc.type and ("→" in uc.type or "->" in uc.type)),
                    "anchor": uc.anchor,
                    "header": one_line(uc.header, max_len),
                })
                continue
            role = classify_codomain_producer(uc.type, d.name)
            if role is None:
                if uc.keyword not in ("structure", "class", "inductive"):
                    premise_consumers.append({
                        "id": u.id,
                        "name": u.name,
                        "kind": u.kind,
                        "live": live_mask != 0,
                        "dom_subtree": dom_sz,
                        "fan_in": fan_in,
                        "anchor": uc.anchor,
                        "header": one_line(uc.header, max_len),
                    })
                continue
            results.append({
                "id": u.id,
                "name": u.name,
                "kind": u.kind,
                "live": live_mask != 0,
                "live_mask": live_mask,
                "dom_subtree": dom_sz,
                "fan_in": fan_in,
                "role": role,
                "module": u.module,
                "anchor": uc.anchor,
                "header": one_line(uc.header, max_len),
            })

        # Optional (or automatic empty-live fallback) dead source-only producers from leanre.db
        dead_producers: list[dict[str, Any]] = []
        if self.kdb.l is not None and (include_dead or not results):
            known_names = {r["name"] for r in results} | {d.name}
            drows = self.kdb.l.execute(
                "SELECT d.name, d.kind, d.module, d.line_no, d.signature_snippet, d.horn_proves, m.file_path "
                "FROM declarations d JOIN modules m ON m.name = d.module "
                "WHERE d.horn_proves = ? OR d.horn_proves LIKE ? ESCAPE '!' "
                "ORDER BY d.id LIMIT 50",
                (stem, f"%.{_escape_like(stem)}"),
            ).fetchall()
            for nm, knd, mod, lno, snip, hp, fp in drows:
                if nm in known_names or self.kdb.maybe(nm) is not None:
                    continue
                dc = read_contract(
                    self.src_root, fp, nm, hint=int(lno), anchor_prefix=self.anchor_prefix, include_scope=False
                )
                role = classify_codomain_producer(dc.type if dc else None, d.name) or "direct"
                dead_producers.append({
                    "id": None,
                    "name": nm,
                    "kind": knd,
                    "live": False,
                    "live_mask": 0,
                    "dom_subtree": 0,
                    "fan_in": 0,
                    "role": role,
                    "status": "dead_source_only",
                    "module": mod,
                    "anchor": dc.anchor if dc else format_anchor(fp, int(lno), self.anchor_prefix),
                    "header": one_line(dc.header if dc else snip, max_len),
                })

        # Value-edge def wrappers (when a Prop-def like OnePlace / ThinScales is embedded inside another Prop-def)
        embedded_defs: list[str] = []
        wrapper_producers: list[dict[str, Any]] = []
        if not results or include_implications:
            for u, ek in self.kdb.users(d, limit=150):
                if ek in (VALUE, BOTH) and not u.ground and not u.is_aux and u.kind == "def" and u.id != d.id:
                    embedded_defs.append(u.name)
            embedded_defs = sorted(set(embedded_defs))
            # Check whether any embedded wrapper def (`Glue`, `Char_at`) has its own live codomain producers!
            for w_name in embedded_defs[:8]:
                wd = self.kdb.maybe(w_name)
                if wd is None:
                    continue
                wc = self.contract(wd, include_scope=False)
                w_role = classify_codomain_producer(wc.body if wc else None, d.name)
                if w_role is None:
                    continue
                is_cond_wrap = bool(wc and wc.body and ("→" in wc.body or "->" in wc.body))
                for wu, wek in self.kdb.users(wd, limit=80):
                    if wek not in (TYPE, BOTH) or wu.ground or wu.is_aux or wu.id in (d.id, wd.id):
                        continue
                    wuc = self.contract(wu, include_scope=False)
                    if wuc is None or wuc.keyword == "field":
                        continue
                    p_role = classify_codomain_producer(wuc.type, wd.name)
                    if p_role is None:
                        continue
                    wst = self.kdb.decl_stats(wu)
                    if live_only and wst["live_mask"] == 0:
                        continue
                    wrapper_producers.append({
                        "id": wu.id,
                        "name": wu.name,
                        "kind": wu.kind,
                        "live": wst["live_mask"] != 0,
                        "dom_subtree": wst["all_dom_subtree"],
                        "via_wrapper": wd.name,
                        "wrapper_role": "implication_codomain" if is_cond_wrap else w_role,
                        "anchor": wuc.anchor,
                        "header": one_line(wuc.header, max_len),
                    })
            wrapper_producers.sort(key=lambda x: (0 if x["live"] else 1, -x["dom_subtree"], x["name"]))

        results.sort(key=lambda r: (0 if r["live"] else 1, -r["dom_subtree"], -r["fan_in"], r["name"]))
        premise_consumers.sort(key=lambda r: (0 if r["live"] else 1, -r["dom_subtree"], -r["fan_in"], r["name"]))
        record_fields.sort(key=lambda r: (0 if r["live"] else 1, -r["dom_subtree"], r["field"]))
        live_count = sum(1 for r in results if r["live"])
        combined = results + (dead_producers if include_dead else [])
        out: dict[str, Any] = {
            "target": {
                "id": d.id,
                "name": d.name,
                "kind": d.kind,
                "keyword": tc.keyword if tc else None,
                "module": d.module,
                "anchor": tc.anchor if tc else None,
                "header": one_line(tc.header, max_len) if tc else None,
            },
            "live_count": live_count,
            "total_count": len(combined),
            "producers": combined[:limit] if limit > 0 else combined,
        }
        if tc and tc.parent_info and tc.parent_info.get("is_constructor"):
            out["ctor_of"] = tc.parent_info
        if dead_producers and not include_dead:
            out["dead_source_producers"] = dead_producers[:10]
        if embedded_defs:
            out["embedded_in_defs"] = embedded_defs[:15]
        if not results or include_implications:
            out["premise_consumers_count"] = len(premise_consumers)
            out["live_premise_consumers_count"] = sum(1 for x in premise_consumers if x["live"])
            if premise_consumers:
                out["premise_consumers"] = premise_consumers[: min(limit if limit > 0 else 15, 15)]
            if record_fields:
                out["record_field_carriers"] = record_fields[:15]
            if wrapper_producers:
                out["wrapper_producers"] = wrapper_producers[:10]
        return out

    def node(self, key: int | str | Decl, with_body: bool = False, max_len: int = 400) -> dict:
        """Schema node skeleton (leanre.decomp/v1) prefilled with everything mechanically known."""
        if isinstance(key, Decl):
            d = key
        else:
            d = self.kdb.maybe(key) or (self.kdb.resolve_unique(key)[0] if isinstance(key, str) else self.kdb.decl(key))
        dn = self.kdb.dom(d)
        idom = self.kdb.decl(int(dn.idom)).name if dn and dn.idom is not None else None
        c = self.contract(d)
        n = {
            "id": d.name, "kid": d.id, "kind": d.kind, "module": d.module,
            "anchor": c.anchor if c else None,
            "header": one_line(c.header, max_len) if c else None,
            "dom": {"depth": dn.depth, "subtree": dn.subtree_size, "idom": idom} if dn else None,
            "role": "theorem" if d.kind == "thm" else ("structure" if c and c.keyword in ("structure", "class") else "contract"),
            "status": "OPAQUE" if (c is None and not d.ground) else "PARTIAL",
            "verdict": "unknown", "tag": "L", "summary": "",
            "fields": [{"name": f.name, "type": one_line(f.type, 240), "ground": None} for f in (c.fields if c else [])],
        }
        if with_body and c and c.body is not None:
            n["body"] = one_line(c.body, max_len)
        if d.ground:
            n["status"], n["verdict"], n["role"] = "READ", "real", "glue"
            n["summary"] = "Mathlib/Lean library declaration (ground type)"
        return n

    # ---- contract unfolder -------------------------------------------
    def contract_deps(self, d: Decl) -> tuple[list[tuple[Decl, int]], list[tuple[Decl, int]]]:
        """(project contract deps, ground deps) that *define the meaning* of d:
        theorems -> type edges only; defs/structures -> type + value edges."""
        kinds = (TYPE, BOTH) if d.kind == "thm" else (TYPE, VALUE, BOTH)
        proj, ground = [], []
        for x, k in self.kdb.deps(d, kinds):
            if x.id == d.id:
                continue
            if x.ground:
                if x.kind in CONTRACT_KINDS and not _noise(x.name):
                    ground.append((x, k))
            elif x.kind in CONTRACT_KINDS:
                proj.append((x, k))
        proj.sort(key=lambda t: t[0].name)
        ground.sort(key=lambda t: t[0].name)
        return proj, ground

    def unfold(
        self,
        key: int | str | Decl,
        depth: int = 2,
        with_body: bool = True,
        max_ground: int = 40,
        max_len: int = 400,
        full_fields: bool = False,
        stop_at: Optional[Iterable[str]] = None,
        max_fields: Optional[int] = None,
        _seen: Optional[set] = None,
        _is_root: bool = True,
    ) -> dict:
        """Recursive signature/contract unfolding down to Mathlib/Lean ground types.
        Nodes already expanded elsewhere are emitted as {"id", "ref": true}."""
        if isinstance(key, Decl):
            d = key
        else:
            d = self.kdb.maybe(key) or (self.kdb.resolve_unique(key)[0] if isinstance(key, str) else self.kdb.decl(key))
        seen = _seen if _seen is not None else set()
        seen.add(d.id)
        stop_rules = _normalize_stop(stop_at)
        c = self.contract(d)
        hdr_len = 0 if max_len <= 0 else max_len
        body_len = 0 if max_len <= 0 else (600 if max_len == 400 else max_len)
        fld_len = 0 if (full_fields or max_len <= 0) else (240 if max_len == 400 else max_len)
        out: dict = {"id": d.name, "kind": d.kind, "keyword": c.keyword if c else None,
                     "anchor": c.anchor if c else None, "ground": d.ground,
                     "header": one_line(c.header, hdr_len) if c else None}
        stopped = not _is_root and bool(stop_rules) and _matches_stop(d.name, stop_rules)
        if stopped:
            out["stopped"] = True
            if c and c.fields:
                if full_fields:
                    out["fields"] = [{"name": f.name, "type": one_line(f.type, fld_len)} for f in c.fields]
                else:
                    out["fields_count"] = len(c.fields)
            return out
        if c and c.fields:
            flds = c.fields
            if not _is_root and max_fields is not None and max_fields >= 0 and not full_fields and len(flds) > max_fields:
                out["fields_truncated"] = len(flds) - max_fields
                flds = flds[:max_fields]
            out["fields"] = [{"name": f.name, "type": one_line(f.type, fld_len)} for f in flds]
        if c and with_body and c.body is not None and d.kind != "thm":
            out["body"] = one_line(c.body, body_len)
        if not d.ground and c is None:
            if d.method == "unmatched:project_auto_instance" or is_auto_instance_name(d.name):
                out["auto_instance"] = True
            else:
                out["opaque"] = "source not located"
        if d.ground:
            return out
        proj, ground = self.contract_deps(d)
        out["ground_deps"] = [x.name for x, _ in ground[:max_ground]]
        if len(ground) > max_ground:
            out["ground_deps_truncated"] = len(ground) - max_ground
        kids = []
        for x, k in proj:
            if x.id in seen:
                kids.append({"id": x.name, "edge": EDGE_REL[k], "ref": True})
            elif depth <= 0:
                kids.append({"id": x.name, "edge": EDGE_REL[k], "unexpanded": True})
            else:
                sub = self.unfold(
                    x,
                    depth - 1,
                    with_body,
                    max_ground,
                    max_len=max_len,
                    full_fields=full_fields,
                    stop_at=stop_rules,
                    max_fields=max_fields,
                    _seen=seen,
                    _is_root=False,
                )
                sub["edge"] = EDGE_REL[k]
                kids.append(sub)
        out["deps"] = kids
        return out

    # ---- Horn clauses ------------------------------------------------
    def horn(self, key: int | str | Decl, *, have_wiring: bool = False) -> dict:
        """Declaration-level Horn clause for a theorem T:
            concl  = project contracts named in T's statement conclusion,
            hyps   = project contracts named in T's explicit hypothesis binders,
            lemmas = project theorems T's proof term uses directly (value edges) -- the `A ∧ B` that
                     T combines; each lemma is itself a Horn clause.
        Contract membership comes from kernel type edges [L]; the hyps/concl split from the source header."""
        if isinstance(key, Decl):
            d = key
        else:
            d = self.kdb.maybe(key) or (self.kdb.resolve_unique(key)[0] if isinstance(key, str) else self.kdb.decl(key))
        c = self.contract(d, include_thm=have_wiring, preserve_lines=have_wiring)
        tdeps = [x for x, k in self.kdb.deps(d, (TYPE, BOTH))
                 if x.kind in CONTRACT_KINDS and x.id != d.id and (not x.ground or not _noise(x.name))]
        vlem = [x for x, k in self.kdb.deps(d, (VALUE, BOTH)) if x.kind == "thm" and not x.is_aux]
        vdef = [x for x, k in self.kdb.deps(d, (VALUE,)) if not x.ground and x.kind in CONTRACT_KINDS]
        hyps, concl = [], []
        if c is not None:
            hyp_ids = set().union(*[identifiers(b) for b in c.binders]) if c.binders else set()
            segs = _arrow_split(c.type or "")
            con_ids = identifiers(segs[-1] if segs else c.type)
            for sgm in segs[:-1]:  # `theorem t : A → B → C` : A, B are premises
                hyp_ids |= identifiers(sgm)
            for x in tdeps:
                last = x.name.rsplit(".", 1)[-1]
                hit = lambda ids: any(t == x.name or t.endswith("." + last) or t == last for t in ids)
                if hit(con_ids):
                    concl.append(x.name)
                if hit(hyp_ids):
                    hyps.append(x.name)
        out = {
            "via": d.name,
            "kind": d.kind,
            "anchor": c.anchor if c else None,
            "header": one_line(c.header, 400) if c else None,
            "hyps": sorted(set(hyps)),
            "concl": sorted(set(concl)),
            "statement_contracts": sorted(x.name for x in tdeps if not x.ground),
            "statement_ground": sorted(x.name for x in tdeps if x.ground),
            "lemmas": sorted(x.name for x in vlem),
            "lemmas_project": sorted(x.name for x in vlem if not x.ground),
            "value_contracts": sorted(x.name for x in vdef),
        }
        if have_wiring:
            if c is not None and c.body_lines:
                lemma_map = _unique_suffix_map([x.name for x in [*vlem, *vdef] if not x.ground])
                type_map = _unique_suffix_map([x.name for x in [*tdeps, *vdef] if not x.ground])
                hw = extract_have_wiring(c, known_lemmas=lemma_map, known_types=type_map)
                tw = hw.get("term_wiring")
                if tw and tw.get("mode") == "application" and tw.get("callee"):
                    callee_d = self.kdb.maybe(str(tw["callee"]))
                    if callee_d is None:
                        try:
                            callee_d, _ = self.kdb.resolve_unique(str(tw["callee"]), near=d.name)
                            tw["callee"] = callee_d.name
                        except Exception:
                            callee_d = None
                    if callee_d is not None and not callee_d.ground:
                        callee_c = self.contract(callee_d, include_scope=False)
                        if callee_c is not None:
                            enrich_term_wiring_with_callee(tw, callee_c)
                out["have_wiring"] = hw
            else:
                out["have_wiring"] = {
                    "binders": [],
                    "intros": [],
                    "destructured": [],
                    "steps": [],
                    "terminal": None,
                }
        return out

    def readers(
        self,
        key: int | str | Decl,
        *,
        field: Optional[str] = None,
        conjunct: Optional[int] = None,
        live_only: bool = False,
        limit: int = 50,
        max_len: int = 220,
    ) -> dict[str, Any]:
        """Reverse-lookup project declarations that read/project a structure field (`--field`)
        or `N`-th `∧`-conjunct (`--conjunct`) of `key`."""
        if field is not None and conjunct is not None:
            raise ValueError("pass at most one of --field NAME or --conjunct N")
        if isinstance(key, Decl):
            d = key
        else:
            d = self.kdb.maybe(key) or (self.kdb.resolve_unique(key)[0] if isinstance(key, str) else self.kdb.decl(key))
        c = self.contract(d, preserve_lines=True)
        if c is None:
            raise ValueError(f"cannot locate source contract for {d.name}")

        # Shorthand `decompile readers StructName.fieldName` -> unwrap parent structure & field!
        if c.keyword == "field" and c.parent_info and field is None and conjunct is None:
            parent_name = c.parent_info.get("name")
            if parent_name and "." in d.name:
                pd = self.kdb.maybe(parent_name)
                pc = self.contract(pd, preserve_lines=True) if pd is not None else None
                if pd is not None and pc is not None and pc.fields:
                    return analyze_structure_readers(
                        self,
                        pd,
                        pc,
                        field_name=d.name.rsplit(".", 1)[-1],
                        live_only=live_only,
                        limit=limit,
                        max_len=max_len,
                    )

        if c.keyword == "ctor" and c.parent_info:
            parent_name = c.parent_info.get("name")
            raise ValueError(
                f"{d.name} is a constructor of {parent_name}; pass `{parent_name} --field <NAME>` for field readers "
                f"or run `leanre bundles --instantiations {parent_name}` for constructor sites"
            )

        is_struct = c.keyword in ("structure", "class") or (bool(c.fields) and c.keyword != "inductive" and c.body is None)
        if field is not None or (is_struct and conjunct is None):
            return analyze_structure_readers(
                self,
                d,
                c,
                field_name=field,
                live_only=live_only,
                limit=limit,
                max_len=max_len,
            )
        return analyze_conjunct_readers(
            self,
            d,
            c,
            conjunct_idx=conjunct,
            live_only=live_only,
            limit=limit,
            max_len=max_len,
        )

    def horn_graph(
        self,
        root: int | str | Decl,
        max_nodes: int = 200,
        project_only: bool = True,
        *,
        have_wiring: bool = False,
    ) -> list[dict]:
        """BFS over value-edge lemma uses from `root`, emitting one Horn clause per theorem."""
        r = root if isinstance(root, Decl) else self.kdb.decl(root)
        out, q, seen = [], deque([r]), {r.id}
        while q and len(out) < max_nodes:
            d = q.popleft()
            if d.kind != "thm":
                continue
            h = self.horn(d, have_wiring=have_wiring)
            out.append(h)
            for nm in (h["lemmas_project"] if project_only else h["lemmas"]):
                x = self.kdb.decl(nm)
                if x.id not in seen:
                    seen.add(x.id)
                    q.append(x)
        return out

    # ---- dominator spine ---------------------------------------------
    def dom_spine(
        self,
        root: int | str | Decl,
        depth: int = 2,
        min_size: int = 500,
        limit: int = 60,
        with_cone: bool = False,
    ) -> dict:
        r = root if isinstance(root, Decl) else self.kdb.decl(root)
        dn = self.kdb.dom(r)
        st = self.kdb.dom_child_stats(r)
        out: dict = {
            "id": r.name,
            "kind": r.kind,
            "module": r.module,
            "subtree": dn.subtree_size if dn else None,
            "depth": dn.depth if dn else None,
            **st,
        }
        if with_cone:
            cone_ids = self._fast_cone(r.id)
            ground_ids = self.kdb.ground_id_set(cone_ids)
            out["all_dom_subtree"] = self.kdb.all_dom_subtree(r.id)
            out["proj_cone"] = len(cone_ids) - len(ground_ids)
            out["full_cone"] = len(cone_ids)
        total_children = st["children"]
        if depth > 0:
            kids = self.kdb.dom_children(r, limit=limit, min_size=min_size)
            out["children"] = [self.dom_spine(self.kdb.decl(k.decl_id), depth - 1, min_size, limit, False) for k in kids]
            for ch in out["children"]:
                ek = self.kdb.edge_kind(r.id, self.kdb.decl(ch["id"]).id)
                ch["direct_edge"] = EDGE_REL.get(ek) if ek else None
            if len(kids) < total_children:
                below = self.kdb.dom_below_count(r, min_size)
                out["pruned_count"] = total_children - len(kids)
                if below > 0 and len(kids) < limit:
                    out["pruned_reason"] = "pruned_below_min_size"
                elif below == 0:
                    out["pruned_reason"] = "pruned_by_limit"
                else:
                    out["pruned_reason"] = "pruned_below_min_size_and_limit"
        elif total_children > 0:
            out["pruned_count"] = total_children
            out["pruned_reason"] = "pruned_at_depth_limit"
        return out

    def dom_contains(
        self,
        root: int | str | Decl,
        targets: Iterable[tuple[str, Decl, Optional[str]]],
        *,
        project_only: bool = False,
        kind: str = "both",
    ) -> dict[str, Any]:
        """Test for each target `(query_str, decl, resolved_from)` whether it lies inside the
        dominator subtree (`dom_in`) and/or reachable cone (`cone_in`, shortest `cone_dist`) of `root`."""
        r = root if isinstance(root, Decl) else self.kdb.decl(root)
        r_dom = self.kdb.dom(r)
        rows: list[dict[str, Any]] = []
        for q_str, d, r_from in targets:
            chain = self.kdb.dom_path(d)
            chain_ids = [n.decl_id for n in chain]
            dom_in = r.id in chain_ids
            dom_hops = chain_ids.index(r.id) if dom_in else None
            d_dom = chain[0] if chain else None
            idom_name = self.kdb.decl(chain[1].decl_id).name if len(chain) > 1 else None
            chain_slice = chain[: dom_hops + 1] if (dom_in and dom_hops is not None) else chain
            idom_chain = [self.kdb.decl(n.decl_id).name for n in chain_slice]

            pth = self.shortest_path(r, d, project_only=project_only, kind=kind)
            cone_in = pth is not None
            cone_dist = (len(pth) - 1) if pth is not None else None

            if d.id == r.id:
                status = "self"
            elif dom_in:
                status = "dominated"
            elif cone_in:
                status = "shared_in_cone"
            else:
                status = "outside"

            item: dict[str, Any] = {
                "query": q_str,
                "id": d.name,
                "decl_id": d.id,
                "kind": d.kind,
                "module": d.module,
                "status": status,
                "dom_in": dom_in,
                "cone_in": cone_in,
                "dom_hops": dom_hops,
                "cone_dist": cone_dist,
                "dom_size": d_dom.subtree_size if d_dom is not None else 0,
                "all_dom_size": self.kdb.all_dom_subtree(d.id),
                "dom_depth": d_dom.depth if d_dom is not None else None,
                "idom": idom_name,
                "idom_chain": idom_chain,
                "shortest_path": [x["id"] for x in pth] if pth is not None else None,
            }
            if r_from is not None:
                item["resolved_from"] = r_from
            rows.append(item)

        return {
            "root": {
                "id": r.name,
                "decl_id": r.id,
                "kind": r.kind,
                "module": r.module,
                "dom_size": r_dom.subtree_size if r_dom is not None else 0,
                "dom_depth": r_dom.depth if r_dom is not None else None,
            },
            "tree": self.kdb.tree_label,
            "kind": kind,
            "project_only": project_only,
            "results": rows,
        }

    # ---- shortest dependency path ------------------------------------
    def shortest_path(
        self,
        src: int | str | Decl,
        dst: int | str | Decl,
        *,
        project_only: bool = False,
        kind: str = "both",
    ) -> Optional[list[dict]]:
        """Shortest directed dependency path (BFS in `edges` src -> dst) from `src` to `dst`."""
        kind_map = {"type": (TYPE, BOTH), "value": (VALUE, BOTH), "both": (TYPE, VALUE, BOTH)}
        if kind not in kind_map:
            raise ValueError(f"invalid kind {kind!r} (expected type|value|both)")
        kinds = kind_map[kind]
        s = src if isinstance(src, Decl) else self.kdb.decl(src)
        t = dst if isinstance(dst, Decl) else self.kdb.decl(dst)
        if s.id == t.id:
            return [{"id": s.name, "kind": s.kind, "module": s.module, "edge": None}]

        fwd_prev: dict[int, tuple[Optional[int], Optional[int]]] = {s.id: (None, None)}
        bwd_next: dict[int, tuple[Optional[int], Optional[int]]] = {t.id: (None, None)}
        fwd_q: list[int] = [s.id]
        bwd_q: list[int] = [t.id]
        ground_cache: dict[int, bool] = {s.id: s.ground, t.id: t.ground}
        meet: Optional[int] = None

        def filter_ground(cand_ids: list[int]) -> None:
            miss = [i for i in cand_ids if i not in ground_cache]
            if miss:
                gset = self.kdb.ground_id_set(miss)
                for i in miss:
                    ground_cache[i] = i in gset

        while fwd_q and bwd_q and meet is None:
            if len(fwd_q) <= len(bwd_q):
                cand_edges: list[tuple[int, int, int]] = []
                for sid, did, ek in self.kdb.iter_out_batch(fwd_q):
                    if int(ek) in kinds:
                        cand_edges.append((int(sid), int(did), int(ek)))
                if project_only:
                    filter_ground([d for _, d, _ in cand_edges if d not in bwd_next])
                nxt_fwd: list[int] = []
                for sid, did, ek in cand_edges:
                    if did in fwd_prev:
                        continue
                    if did in bwd_next:
                        fwd_prev[did] = (sid, ek)
                        meet = did
                        break
                    if project_only and ground_cache.get(did, False):
                        continue
                    fwd_prev[did] = (sid, ek)
                    nxt_fwd.append(did)
                fwd_q = nxt_fwd
            else:
                cand_rev: list[tuple[int, int, int]] = []
                for chunk in _chunks(bwd_q, 900):
                    q = f"SELECT src, dst, kind FROM edges WHERE dst IN ({','.join('?' * len(chunk))})"
                    for sid, did, ek in self.kdb.k.execute(q, chunk):
                        if int(ek) in kinds:
                            cand_rev.append((int(sid), int(did), int(ek)))
                if project_only:
                    filter_ground([u for u, _, _ in cand_rev if u not in fwd_prev])
                nxt_bwd: list[int] = []
                for sid, did, ek in cand_rev:
                    if sid in bwd_next:
                        continue
                    if sid in fwd_prev:
                        bwd_next[sid] = (did, ek)
                        meet = sid
                        break
                    if project_only and ground_cache.get(sid, False):
                        continue
                    bwd_next[sid] = (did, ek)
                    nxt_bwd.append(sid)
                bwd_q = nxt_bwd

        if meet is None:
            return None

        left: list[tuple[int, Optional[int]]] = []
        cur: Optional[int] = meet
        while cur is not None:
            prev_id, ek = fwd_prev[cur]
            left.append((cur, ek))
            cur = prev_id
        left.reverse()

        right: list[tuple[int, Optional[int]]] = []
        cur = meet
        while True:
            nxt_id, ek = bwd_next[cur]
            if nxt_id is None:
                break
            right.append((nxt_id, ek))
            cur = nxt_id

        full = left + right
        decl_map = {d.id: d for d in self.kdb.decls([nid for nid, _ in full])}
        return [
            {
                "id": decl_map[nid].name,
                "kind": decl_map[nid].kind,
                "module": decl_map[nid].module,
                "edge": EDGE_REL[ek] if ek else None,
            }
            for nid, ek in full
        ]

    # ---- cones / slices ----------------------------------------------
    def _fast_cone(self, seed_id: int) -> set[int]:
        """Use cached CSR from spine.py when already on disk; otherwise SQLite BFS."""
        try:
            import json as _json
            from .spine import CACHE_DIR, CSR
            row = self.kdb.k.execute("SELECT value_json FROM meta WHERE key='content_hashes'").fetchone()
            edges_hash = _json.loads(row[0]).get("edges") if row else None
            if edges_hash and os.path.exists(os.path.join(CACHE_DIR, f"csr_e{edges_hash[:16]}.kind")):
                if not hasattr(self, "_csr_cache") or self._csr_cache is None:
                    self._csr_cache = CSR.load(self.kdb)
                mask = self._csr_cache.reach([seed_id])
                return {i for i, b in enumerate(mask) if b}
        except Exception:
            pass
        return self.cone([seed_id])

    def cone(self, seeds: Iterable[int | str | Decl], kinds: tuple[int, ...] = (TYPE, VALUE, BOTH),
             stop: Optional[set[int]] = None) -> set[int]:
        """Forward closure (everything the seeds depend on), optionally not expanding through `stop`."""
        ids = [s.id if isinstance(s, Decl) else self.kdb.decl(s).id for s in seeds]
        seen = set(ids)
        frontier = list(ids)
        stop = stop or set()
        while frontier:
            nxt = []
            exp = [i for i in frontier if i not in stop]
            for _src, dst, k in self.kdb.iter_out_batch(exp):
                if k in kinds and dst not in seen:
                    seen.add(dst)
                    nxt.append(dst)
            frontier = nxt
        return seen

    def dom_subtree(self, root: int | str | Decl) -> set[int]:
        r = root if isinstance(root, Decl) else self.kdb.decl(root)
        out, frontier = {r.id}, [r.id]
        k = self.kdb.k
        while frontier:
            nxt = []
            for i in range(0, len(frontier), 900):
                ch = frontier[i:i + 900]
                q = f"SELECT decl_id FROM dom WHERE tree_id=? AND idom IN ({','.join('?' * len(ch))})"
                for (x,) in k.execute(q, [self.kdb.tree_id, *ch]):
                    out.add(int(x)); nxt.append(int(x))
            frontier = nxt
        return out


def _unique_suffix_map(names: Iterable[str]) -> dict[str, str]:
    """Map unambiguous dot-suffixes (and full FQNs) to full FQNs."""
    counts: dict[str, list[str]] = {}
    full_map: dict[str, str] = {}
    for nm in names:
        full_map[nm] = nm
        parts = nm.split(".")
        for i in range(1, len(parts)):
            suf = ".".join(parts[i:])
            counts.setdefault(suf, []).append(nm)
    for suf, vals in counts.items():
        if len(vals) == 1 and suf not in full_map:
            full_map[suf] = vals[0]
    return full_map
