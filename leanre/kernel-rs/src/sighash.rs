//! Kernel signature hashes `k1n` / `k1a` — bit-for-bit port of the reference
//! implementation `leanre/sighash.py` (`KernelSigHasher`), spec docs/SIGHASH.md v1.
//!
//! Merkle hash of a constant's kernel TYPE over the hash-consed expression
//! DAG. Binder names/info are not hashed, universe parameters and (k1a only)
//! project-local constants are renumbered by first occurrence in a fixed DFS,
//! references to the constant's own inductive block are positional.

use crate::parse::*;
use crate::store::Store;
use rayon::prelude::*;
use serde_json::json;
use sha2::{Digest, Sha256};
use std::collections::{HashMap, HashSet};
use std::hash::{BuildHasherDefault, Hasher};

pub const SPEC_VERSION: &str = "1";
const SIZE_CAP: u64 = 0xFFFF_FFFF;
pub type H16 = [u8; 16];

#[derive(Default)]
pub struct U32Hasher(u64);
impl Hasher for U32Hasher {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, bytes: &[u8]) {
        for &b in bytes {
            self.0 = (self.0 ^ b as u64).wrapping_mul(0x100_0000_01B3);
        }
    }
    fn write_u32(&mut self, i: u32) {
        self.0 = (i as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15);
    }
}
type FMap<V> = HashMap<u32, V, BuildHasherDefault<U32Hasher>>;
type FSet = HashSet<u32, BuildHasherDefault<U32Hasher>>;

pub fn h16(parts: &[&[u8]]) -> H16 {
    let mut h = Sha256::new();
    for p in parts {
        h.update(p);
    }
    let d = h.finalize();
    let mut o = [0u8; 16];
    o.copy_from_slice(&d[..16]);
    o
}

fn dec(n: u64, buf: &mut [u8; 20]) -> &[u8] {
    let mut x = n;
    let mut i = 20;
    loop {
        i -= 1;
        buf[i] = b'0' + (x % 10) as u8;
        x /= 10;
        if x == 0 {
            break;
        }
    }
    &buf[i..]
}

/// Rule N1: `_private.<module path>.0.<rest>` -> `<rest>`.
pub fn norm_const_name(name: &str) -> &str {
    if name.starts_with("_private.") {
        let mut pos = 0usize;
        for (i, part) in name.split('.').enumerate() {
            if i >= 1 && part == "0" {
                let rest_start = pos + part.len() + 1;
                if rest_start < name.len() {
                    return &name[rest_start..];
                }
                break;
            }
            pos += part.len() + 1;
        }
    }
    name
}

pub struct Lexicon {
    names: HashSet<String>,
    pub id: String,
}

impl Lexicon {
    pub fn load(path: &str) -> Result<Lexicon, String> {
        let txt = std::fs::read_to_string(path).map_err(|e| format!("lexicon {path}: {e}"))?;
        let names: HashSet<String> = txt.split('\n').filter(|l| !l.is_empty()).map(|l| l.to_string()).collect();
        let mut sorted: Vec<&String> = names.iter().collect();
        sorted.sort();
        let mut h = Sha256::new();
        if !sorted.is_empty() {
            for (i, n) in sorted.iter().enumerate() {
                if i > 0 {
                    h.update(b"\n");
                }
                h.update(n.as_bytes());
            }
            h.update(b"\n");
        }
        let id = crate::reader::hex(&h.finalize())[..16].to_string();
        Ok(Lexicon { names, id })
    }
    /// Rule L1: exact name or a proper dot-prefix is in the lexicon (after N1).
    pub fn is_local(&self, const_name: &str) -> bool {
        let mut n = norm_const_name(const_name);
        loop {
            if self.names.contains(n) {
                return true;
            }
            match n.rfind('.') {
                Some(i) if i > 0 => n = &n[..i],
                _ => return false,
            }
        }
    }
    pub fn len(&self) -> usize {
        self.names.len()
    }
}

pub struct SigTable {
    hn: Vec<H16>,
    ha: Vec<H16>,
    size: Vec<u32>,
    nloc: Vec<u32>,
    lex: Option<(String, usize, String)>,
}

impl SigTable {
    pub fn named(&self, ci: usize) -> Option<String> {
        Some(format!("k1n:{}", crate::reader::hex(&self.hn[ci])))
    }
    pub fn anon(&self, ci: usize) -> Option<String> {
        Some(format!("k1a:{}", crate::reader::hex(&self.ha[ci])))
    }
    pub fn size(&self, ci: usize) -> Option<i64> {
        Some(self.size[ci] as i64)
    }
    pub fn n_local(&self, ci: usize) -> Option<i64> {
        Some(self.nloc[ci] as i64)
    }
    pub fn meta(&self) -> serde_json::Value {
        json!({"spec": "docs/SIGHASH.md", "spec_version": SPEC_VERSION, "schemes": ["k1n", "k1a"],
            "lexicon": self.lex.as_ref().map(|(id, n, path)| json!({"id": id, "names": n, "file": std::path::Path::new(path).file_name().map(|x| x.to_string_lossy().to_string())})),
            "note": if self.lex.is_none() { "no project-local lexicon supplied: k1a == k1n for every constant" } else { "k1a abstracts project-local constants per the lexicon" }})
    }
}

struct Ctx<'a> {
    s: &'a Store,
    /// name id -> flat constant index (u32::MAX if not a declared constant)
    nid2ci: &'a [u32],
    nameref: &'a [H16],
    local: &'a [bool],
    lex: Option<&'a Lexicon>,
    h_zero: H16,
    h_empty_us: H16,
}

#[derive(Default)]
struct Sess {
    memo: FMap<(H16, H16, u64)>,
    lmemo: FMap<H16>,
    seen: FSet,
    lv: FMap<u32>,
    lc: FMap<u32>,
    stack: Vec<u32>,
    lstack: Vec<u32>,
}

impl<'a> Ctx<'a> {
    fn is_local(&self, nid: u32) -> bool {
        let ci = self.nid2ci.get(nid as usize).copied().unwrap_or(u32::MAX);
        if ci != u32::MAX {
            self.local[ci as usize]
        } else {
            self.lex.map(|l| l.is_local(&self.s.name_string(nid))).unwrap_or(false)
        }
    }
    fn name_ref(&self, nid: u32) -> H16 {
        let ci = self.nid2ci.get(nid as usize).copied().unwrap_or(u32::MAX);
        if ci != u32::MAX {
            self.nameref[ci as usize]
        } else {
            let n = self.s.name_string(nid);
            h16(&[b"n", norm_const_name(&n).as_bytes()])
        }
    }

    fn number_level(&self, lid: u32, lv: &mut FMap<u32>, st: &mut Vec<u32>) {
        let s = self.s;
        st.clear();
        st.push(lid);
        while let Some(x) = st.pop() {
            let i = x as usize;
            match s.l_kind[i] {
                L_PARAM => {
                    let n = lv.len() as u32;
                    lv.entry(s.l_a[i]).or_insert(n);
                }
                L_SUCC => st.push(s.l_a[i]),
                L_MAX | L_IMAX => {
                    st.push(s.l_b[i]);
                    st.push(s.l_a[i]);
                }
                _ => {}
            }
        }
    }

    /// Rule K3: first-occurrence numbering of universe params and project-local constants.
    /// (The reference prunes closed subtrees; they contain neither, so the numbering is identical.)
    fn number(&self, roots: &[u32], selfmap: &[u32], ss: &mut Sess) {
        let s = self.s;
        ss.lv.clear();
        ss.lc.clear();
        ss.seen.clear();
        for &root in roots {
            ss.stack.clear();
            ss.stack.push(root);
            while let Some(e) = ss.stack.pop() {
                if !ss.seen.insert(e) {
                    continue;
                }
                let i = e as usize;
                match s.tag[i] {
                    K_APP | K_LAM | K_PI => {
                        ss.stack.push(s.b[i]);
                        ss.stack.push(s.a[i]);
                    }
                    K_CONST => {
                        let nid = s.a[i];
                        if !selfmap.contains(&nid) && !ss.lc.contains_key(&nid) && self.is_local(nid) {
                            let n = ss.lc.len() as u32;
                            ss.lc.insert(nid, n);
                        }
                        let off = s.b[i] as usize;
                        let k = s.us[off] as usize;
                        for u in off + 1..off + 1 + k {
                            self.number_level(s.us[u], &mut ss.lv, &mut ss.lstack);
                        }
                    }
                    K_SORT => self.number_level(s.a[i], &mut ss.lv, &mut ss.lstack),
                    K_LET => {
                        let (v, b) = s.lets[s.b[i] as usize];
                        ss.stack.push(b);
                        ss.stack.push(v);
                        ss.stack.push(s.a[i]);
                    }
                    K_PROJ => {
                        let (nid, _) = s.projs[s.b[i] as usize];
                        if !selfmap.contains(&nid) && !ss.lc.contains_key(&nid) && self.is_local(nid) {
                            let n = ss.lc.len() as u32;
                            ss.lc.insert(nid, n);
                        }
                        ss.stack.push(s.a[i]);
                    }
                    K_MDATA => ss.stack.push(s.a[i]),
                    _ => {}
                }
            }
        }
    }

    fn hlevel(&self, lid: u32, lv: &FMap<u32>, memo: &mut FMap<H16>) -> H16 {
        if let Some(h) = memo.get(&lid) {
            return *h;
        }
        let s = self.s;
        let i = lid as usize;
        let h = match s.l_kind[i] {
            L_PARAM => {
                let mut db = [0u8; 20];
                h16(&[b"p", dec(*lv.get(&s.l_a[i]).expect("unnumbered universe param") as u64, &mut db)])
            }
            L_SUCC => {
                let a = self.hlevel(s.l_a[i], lv, memo);
                h16(&[b"s", &a])
            }
            L_MAX | L_IMAX => {
                let a = self.hlevel(s.l_a[i], lv, memo);
                let b = self.hlevel(s.l_b[i], lv, memo);
                h16(&[if s.l_kind[i] == L_MAX { b"m" } else { b"i" }, &a, &b])
            }
            _ => self.h_zero,
        };
        memo.insert(lid, h);
        h
    }

    /// Rules K1/K2: (named digest, anon digest, tree size) of `root`.
    fn hash(&self, root: u32, selfmap: &[u32], ss: &mut Sess) -> (H16, H16, u64) {
        let s = self.s;
        ss.stack.clear();
        ss.stack.push(root);
        let cap = |x: u64| x.min(SIZE_CAP);
        while let Some(&e) = ss.stack.last() {
            if ss.memo.contains_key(&e) {
                ss.stack.pop();
                continue;
            }
            let i = e as usize;
            let t = s.tag[i];
            match t {
                K_APP | K_LAM | K_PI => {
                    let (x, y) = (s.a[i], s.b[i]);
                    let (rx, ry) = (ss.memo.get(&x).copied(), ss.memo.get(&y).copied());
                    if let (Some(rx), Some(ry)) = (rx, ry) {
                        let tb: &[u8] = if t == K_APP {
                            b"A"
                        } else if t == K_LAM {
                            b"F"
                        } else {
                            b"P"
                        };
                        let hn = h16(&[tb, &rx.0, &ry.0]);
                        let ha = if rx.0 == rx.1 && ry.0 == ry.1 { hn } else { h16(&[tb, &rx.1, &ry.1]) };
                        ss.memo.insert(e, (hn, ha, cap(1 + rx.2 + ry.2)));
                    } else {
                        if ry.is_none() {
                            ss.stack.push(y);
                        }
                        if rx.is_none() {
                            ss.stack.push(x);
                        }
                    }
                }
                K_CONST => {
                    let off = s.b[i] as usize;
                    let k = s.us[off] as usize;
                    let hu = if k == 0 {
                        self.h_empty_us
                    } else {
                        let mut buf: Vec<u8> = Vec::with_capacity(1 + 16 * k);
                        buf.push(b'u');
                        for u in off + 1..off + 1 + k {
                            let h = self.hlevel(s.us[u], &ss.lv, &mut ss.lmemo);
                            buf.extend_from_slice(&h);
                        }
                        h16(&[&buf])
                    };
                    let nid = s.a[i];
                    let mut db = [0u8; 20];
                    let (hn, ha) = if let Some(j) = selfmap.iter().position(|&x| x == nid) {
                        let r = h16(&[b"r", dec(j as u64, &mut db)]);
                        let h = h16(&[b"C", &r, &hu]);
                        (h, h)
                    } else {
                        let hn = h16(&[b"C", &self.name_ref(nid), &hu]);
                        let ha = match ss.lc.get(&nid) {
                            None => hn,
                            Some(&li) => h16(&[b"C", &h16(&[b"l", dec(li as u64, &mut db)]), &hu]),
                        };
                        (hn, ha)
                    };
                    ss.memo.insert(e, (hn, ha, 1));
                }
                K_BVAR => {
                    let mut db = [0u8; 20];
                    let h = h16(&[b"v", dec(s.a[i] as u64, &mut db)]);
                    ss.memo.insert(e, (h, h, 1));
                }
                K_SORT => {
                    let hl = self.hlevel(s.a[i], &ss.lv, &mut ss.lmemo);
                    let h = h16(&[b"S", &hl]);
                    ss.memo.insert(e, (h, h, 1));
                }
                K_LET => {
                    let (v, b) = s.lets[s.b[i] as usize];
                    let ty = s.a[i];
                    let (ra, rb, rc) = (ss.memo.get(&ty).copied(), ss.memo.get(&v).copied(), ss.memo.get(&b).copied());
                    if let (Some(ra), Some(rb), Some(rc)) = (ra, rb, rc) {
                        let hn = h16(&[b"T", &ra.0, &rb.0, &rc.0]);
                        let ha = h16(&[b"T", &ra.1, &rb.1, &rc.1]);
                        ss.memo.insert(e, (hn, ha, cap(1 + ra.2 + rb.2 + rc.2)));
                    } else {
                        if rc.is_none() {
                            ss.stack.push(b);
                        }
                        if rb.is_none() {
                            ss.stack.push(v);
                        }
                        if ra.is_none() {
                            ss.stack.push(ty);
                        }
                    }
                }
                K_PROJ => {
                    let st = s.a[i];
                    match ss.memo.get(&st).copied() {
                        None => ss.stack.push(st),
                        Some(rs) => {
                            let (nid, idx) = s.projs[s.b[i] as usize];
                            let mut idxb = [0u8; 20];
                            let idx = dec(idx as u64, &mut idxb);
                            let mut db = [0u8; 20];
                            let (rn, ra) = if let Some(j) = selfmap.iter().position(|&x| x == nid) {
                                let r = h16(&[b"r", dec(j as u64, &mut db)]);
                                (r, r)
                            } else {
                                let rn = self.name_ref(nid);
                                let ra = match ss.lc.get(&nid) {
                                    None => rn,
                                    Some(&li) => h16(&[b"l", dec(li as u64, &mut db)]),
                                };
                                (rn, ra)
                            };
                            let hn = h16(&[b"J", &rn, &rs.0, idx]);
                            let ha = h16(&[b"J", &ra, &rs.1, idx]);
                            ss.memo.insert(e, (hn, ha, cap(1 + rs.2)));
                        }
                    }
                }
                K_NAT => {
                    let h = h16(&[b"N", s.lit(s.a[i])]);
                    ss.memo.insert(e, (h, h, 1));
                }
                K_STR => {
                    let h = h16(&[b"X", s.lit(s.a[i])]);
                    ss.memo.insert(e, (h, h, 1));
                }
                K_MDATA => {
                    let c = s.a[i];
                    match ss.memo.get(&c).copied() {
                        None => ss.stack.push(c),
                        Some(r) => {
                            ss.memo.insert(e, r);
                        }
                    }
                }
                _ => panic!("sighash: undefined expression id {e}"),
            }
        }
        ss.memo[&root]
    }

    fn fresh(ss: &mut Sess) {
        if ss.memo.capacity() > (1 << 16) {
            ss.memo = FMap::default();
        } else {
            ss.memo.clear();
        }
        ss.lmemo.clear();
        if ss.seen.capacity() > (1 << 16) {
            ss.seen = FSet::default();
        }
    }

    /// Rule K4 for a plain constant (thm/def/opaque/axiom/quot/ctor/rec).
    fn plain(&self, ty: u32, selfmap: &[u32], ss: &mut Sess) -> (H16, H16, u32, u32) {
        Self::fresh(ss);
        self.number(&[ty], selfmap, ss);
        let (hn, ha, size) = self.hash(ty, selfmap, ss);
        (hn, ha, size as u32, ss.lc.len() as u32)
    }

    fn decl(&self, d: &DeclRec, ss: &mut Sess) -> Vec<(H16, H16, u32, u32)> {
        if d.kind != D_INDUCTIVE {
            return vec![self.plain(d.consts[0].ty, &[], ss)];
        }
        let selfmap: Vec<u32> = d.consts.iter().filter(|c| c.ckind == C_INDUCT).map(|c| c.name).collect();
        let mut out = Vec::with_capacity(d.consts.len());
        for c in &d.consts {
            if c.ckind == C_INDUCT {
                let mut mine: Vec<&ConstRec> = d.consts.iter().filter(|x| x.ckind == C_CTOR && x.induct == c.name).collect();
                mine.sort_by_key(|x| x.cidx);
                let mut roots = vec![c.ty];
                roots.extend(mine.iter().map(|x| x.ty));
                Self::fresh(ss);
                self.number(&roots, &selfmap, ss);
                let parts: Vec<(H16, H16, u64)> = roots.iter().map(|&r| self.hash(r, &selfmap, ss)).collect();
                let mut bn: Vec<u8> = vec![b'c'];
                let mut ba: Vec<u8> = vec![b'c'];
                for p in &parts[1..] {
                    bn.extend_from_slice(&p.0);
                    ba.extend_from_slice(&p.1);
                }
                let hn = h16(&[b"I", &parts[0].0, &h16(&[&bn])]);
                let ha = h16(&[b"I", &parts[0].1, &h16(&[&ba])]);
                let size = parts.iter().map(|p| p.2).sum::<u64>().min(SIZE_CAP);
                out.push((hn, ha, size as u32, ss.lc.len() as u32));
            } else {
                out.push(self.plain(c.ty, &selfmap, ss));
            }
        }
        out
    }
}

pub fn compute_all(s: &Store, cname: &[String], coff: &[usize], lexicon: Option<&str>) -> Result<SigTable, String> {
    let lex = match lexicon {
        Some(p) => Some(Lexicon::load(p)?),
        None => None,
    };
    let mut nid2ci = vec![u32::MAX; s.n_kind.len()];
    for (di, d) in s.decls.iter().enumerate() {
        for (k, c) in d.consts.iter().enumerate() {
            nid2ci[c.name as usize] = (coff[di] + k) as u32;
        }
    }
    let nameref: Vec<H16> = cname.par_iter().map(|n| h16(&[b"n", norm_const_name(n).as_bytes()])).collect();
    let local: Vec<bool> = match &lex {
        Some(l) => cname.par_iter().map(|n| l.is_local(n)).collect(),
        None => vec![false; cname.len()],
    };
    let ctx = Ctx { s, nid2ci: &nid2ci, nameref: &nameref, local: &local, lex: lex.as_ref(), h_zero: h16(&[b"z"]), h_empty_us: h16(&[b"u"]) };
    let per: Vec<Vec<(H16, H16, u32, u32)>> = (0..s.decls.len()).into_par_iter().with_min_len(64).map_init(Sess::default, |ss, di| ctx.decl(&s.decls[di], ss)).collect();
    let n = cname.len();
    let (mut hn, mut ha, mut size, mut nloc) = (Vec::with_capacity(n), Vec::with_capacity(n), Vec::with_capacity(n), Vec::with_capacity(n));
    for v in per {
        for (a, b, c, d) in v {
            hn.push(a);
            ha.push(b);
            size.push(c);
            nloc.push(d);
        }
    }
    if hn.len() != n {
        return Err("sighash: constant count mismatch".into());
    }
    Ok(SigTable { hn, ha, size, nloc, lex: lex.map(|l| (l.id.clone(), l.len(), lexicon.unwrap().to_string())) })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn n1_private_prefix() {
        assert_eq!(norm_const_name("_private.Mathlib.Foo.Bar.0.Baz.qux"), "Baz.qux");
        assert_eq!(norm_const_name("_private.M.0"), "_private.M.0");
        assert_eq!(norm_const_name("Foo.0.bar"), "Foo.0.bar");
        assert_eq!(norm_const_name("_private.0.x"), "x");
        assert_eq!(norm_const_name("_private.A.0.b.0.c"), "b.0.c");
    }

    #[test]
    fn h16_concatenates_parts() {
        assert_eq!(h16(&[b"A", b"bc"]), h16(&[b"Abc"]));
        assert_ne!(h16(&[b"z"]), h16(&[b"s"]));
    }
}
