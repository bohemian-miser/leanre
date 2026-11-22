"""Decompiler: kernel graph + source contracts -> contract unfolding, Horn clauses, dominator spine,
cones/slices.  All results are plain dicts (JSON-ready, `leanre.decomp/v1` node shape)."""
from __future__ import annotations

import os
from collections import deque
from typing import Iterable, Optional

from .kdb import BOTH, EDGE_REL, TYPE, VALUE, Decl, KernelDB, DEFAULT_SRC
from .source import Contract, identifiers, one_line, read_contract

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


class Decompiler:
    def __init__(self, kdb: Optional[KernelDB] = None, src_root: str = DEFAULT_SRC) -> None:
        self.kdb = kdb or KernelDB()
        self.src_root = src_root
        self._contracts: dict[int, Optional[Contract]] = {}

    # ---- contracts ---------------------------------------------------
    def locate(self, d: Decl) -> tuple[Optional[str], Optional[int], Optional[str]]:
        """(rel_file, line_hint, snippet) for a project decl."""
        row = self.kdb.src_row(d)
        if row:
            return row["file"], row["line"], row["snippet"]
        if d.module:
            return self.kdb.module_file(d.module), None, None
        return None, None, None

    def contract(self, key: int | str | Decl) -> Optional[Contract]:
        d = key if isinstance(key, Decl) else self.kdb.decl(key)
        if d.id in self._contracts:
            return self._contracts[d.id]
        c = None
        if not d.ground:
            f, hint, _ = self.locate(d)
            if f:
                c = read_contract(self.src_root, f, d.name, hint)
                if c is None and "." in d.name:
                    parent, last = d.name.rsplit(".", 1)
                    pc = read_contract(self.src_root, f, parent, hint)
                    fld = next((x for x in pc.fields if x.name == last), None) if pc else None
                    if fld is not None:  # structure projection / constructor -> synthesize from parent field
                        c = Contract(name=d.name, keyword="field", file=pc.file, line=pc.line,
                                     header=f"{parent}.{last} : {' '.join(fld.type.split())}",
                                     type=fld.type, namespace=pc.namespace, variables=pc.variables)
                    elif d.is_aux:
                        c = pc
        self._contracts[d.id] = c
        return c

    def node(self, key: int | str | Decl, with_body: bool = False, max_len: int = 400) -> dict:
        """Schema node skeleton (leanre.decomp/v1) prefilled with everything mechanically known."""
        d = key if isinstance(key, Decl) else self.kdb.decl(key)
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

    def unfold(self, key: int | str | Decl, depth: int = 2, with_body: bool = True, max_ground: int = 40,
               _seen: Optional[set] = None) -> dict:
        """Recursive signature/contract unfolding down to Mathlib/Lean ground types.
        Nodes already expanded elsewhere are emitted as {"id", "ref": true}."""
        d = key if isinstance(key, Decl) else self.kdb.decl(key)
        seen = _seen if _seen is not None else set()
        seen.add(d.id)
        c = self.contract(d)
        out: dict = {"id": d.name, "kind": d.kind, "keyword": c.keyword if c else None,
                     "anchor": c.anchor if c else None, "ground": d.ground,
                     "header": one_line(c.header, 400) if c else None}
        if c and c.fields:
            out["fields"] = [{"name": f.name, "type": one_line(f.type, 240)} for f in c.fields]
        if c and with_body and c.body is not None and d.kind != "thm":
            out["body"] = one_line(c.body, 600)
        if not d.ground and c is None:
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
                sub = self.unfold(x, depth - 1, with_body, max_ground, seen)
                sub["edge"] = EDGE_REL[k]
                kids.append(sub)
        out["deps"] = kids
        return out

    # ---- Horn clauses ------------------------------------------------
    def horn(self, key: int | str | Decl) -> dict:
        """Declaration-level Horn clause for a theorem T:
            concl  = project contracts named in T's statement conclusion,
            hyps   = project contracts named in T's explicit hypothesis binders,
            lemmas = project theorems T's proof term uses directly (value edges) -- the `A ∧ B` that
                     T combines; each lemma is itself a Horn clause.
        Contract membership comes from kernel type edges [L]; the hyps/concl split from the source header."""
        d = key if isinstance(key, Decl) else self.kdb.decl(key)
        c = self.contract(d)
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
        return {"via": d.name, "kind": d.kind, "anchor": c.anchor if c else None,
                "header": one_line(c.header, 400) if c else None,
                "hyps": sorted(set(hyps)), "concl": sorted(set(concl)),
                "statement_contracts": sorted(x.name for x in tdeps if not x.ground),
                "statement_ground": sorted(x.name for x in tdeps if x.ground),
                "lemmas": sorted(x.name for x in vlem),
                "lemmas_project": sorted(x.name for x in vlem if not x.ground),
                "value_contracts": sorted(x.name for x in vdef)}

    def horn_graph(self, root: int | str | Decl, max_nodes: int = 200, project_only: bool = True) -> list[dict]:
        """BFS over value-edge lemma uses from `root`, emitting one Horn clause per theorem."""
        r = root if isinstance(root, Decl) else self.kdb.decl(root)
        out, q, seen = [], deque([r]), {r.id}
        while q and len(out) < max_nodes:
            d = q.popleft()
            if d.kind != "thm":
                continue
            h = self.horn(d)
            out.append(h)
            for nm in (h["lemmas_project"] if project_only else h["lemmas"]):
                x = self.kdb.decl(nm)
                if x.id not in seen:
                    seen.add(x.id)
                    q.append(x)
        return out

    # ---- dominator spine ---------------------------------------------
    def dom_spine(self, root: int | str | Decl, depth: int = 2, min_size: int = 500, limit: int = 60) -> dict:
        r = root if isinstance(root, Decl) else self.kdb.decl(root)
        dn = self.kdb.dom(r)
        st = self.kdb.dom_child_stats(r)
        out = {"id": r.name, "kind": r.kind, "module": r.module,
               "subtree": dn.subtree_size if dn else None, "depth": dn.depth if dn else None, **st}
        if depth > 0:
            kids = self.kdb.dom_children(r, limit=limit, min_size=min_size)
            out["children"] = [self.dom_spine(self.kdb.decl(k.decl_id), depth - 1, min_size, limit) for k in kids]
            for ch in out["children"]:
                ek = self.kdb.edge_kind(r.id, self.kdb.decl(ch["id"]).id)
                ch["direct_edge"] = EDGE_REL.get(ek) if ek else None
        return out

    # ---- cones / slices ----------------------------------------------
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
