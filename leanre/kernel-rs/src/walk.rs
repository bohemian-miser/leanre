//! Per-declaration expression-DAG walks: exact type-dependency and
//! value-dependency constant sets (kept separate), DAG node counts and
//! kernel-pattern flags.

use crate::parse::*;
use crate::store::{Store, NONE};
use rayon::prelude::*;

pub const F_REFL_TRUE: u32 = 1;
pub const F_OF_DECIDE: u32 = 2;
pub const F_REDUCE_BOOL: u32 = 4;
pub const F_REDUCE_NAT: u32 = 8;
pub const F_SORRY: u32 = 16;
pub const F_TRUST_COMPILER: u32 = 32;

const EMPTY: u32 = u32::MAX;

/// Open-addressing u32 set that is cheap to clear when small.
pub struct FastSet {
    tab: Vec<u32>,
    mask: usize,
    len: usize,
}

impl FastSet {
    pub fn new() -> Self {
        FastSet { tab: vec![EMPTY; 1024], mask: 1023, len: 0 }
    }
    #[inline]
    fn slot(&self, k: u32) -> usize {
        ((k as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15) >> 29) as usize & self.mask
    }
    /// true if `k` was not present.
    #[inline]
    pub fn insert(&mut self, k: u32) -> bool {
        let mut i = self.slot(k);
        loop {
            let v = self.tab[i];
            if v == k {
                return false;
            }
            if v == EMPTY {
                self.tab[i] = k;
                self.len += 1;
                if self.len * 2 > self.tab.len() {
                    self.grow();
                }
                return true;
            }
            i = (i + 1) & self.mask;
        }
    }
    fn grow(&mut self) {
        let old = std::mem::replace(&mut self.tab, vec![EMPTY; (self.mask + 1) * 4]);
        self.mask = self.tab.len() - 1;
        for k in old {
            if k != EMPTY {
                let mut i = self.slot(k);
                while self.tab[i] != EMPTY {
                    i = (i + 1) & self.mask;
                }
                self.tab[i] = k;
            }
        }
    }
    pub fn clear(&mut self) {
        if self.tab.len() > (1 << 16) {
            *self = FastSet::new();
        } else if self.len > 0 {
            self.tab.fill(EMPTY);
            self.len = 0;
        }
    }
    #[allow(dead_code)]
    pub fn len(&self) -> usize {
        self.len
    }
}

/// Name ids of the constants used by the structural kernel patterns.
#[derive(Clone, Copy)]
pub struct Markers {
    pub eq_refl: u32,
    pub bool_ty: u32,
    pub bool_true: u32,
    pub of_decide_eq_true: u32,
}

#[derive(Default, Clone)]
pub struct DeclEdges {
    pub trefs: Vec<u32>,
    pub vrefs: Vec<u32>,
    pub tnodes: u64,
    pub vnodes: u64,
    pub flags: u32,
    pub dangling: u32,
}

struct Scratch {
    seen: FastSet,
    stack: Vec<u32>,
    refs: Vec<u32>,
}

#[inline]
fn is_const(s: &Store, e: u32, name: u32) -> bool {
    s.tag[e as usize] == K_CONST && s.a[e as usize] == name
}

/// `Eq.refl.{_} Bool Bool.true`
#[inline]
fn is_refl_true(s: &Store, e: u32, m: &Markers) -> bool {
    let i = e as usize;
    if s.tag[i] != K_APP || !is_const(s, s.b[i], m.bool_true) {
        return false;
    }
    let f = s.a[i] as usize;
    s.tag[f] == K_APP && is_const(s, s.b[f], m.bool_ty) && is_const(s, s.a[f], m.eq_refl)
}

fn walk(s: &Store, roots: &[u32], self_idx: u32, m: &Markers, sc: &mut Scratch, want_flags: bool) -> (Vec<u32>, u64, u32, u32) {
    sc.seen.clear();
    sc.stack.clear();
    sc.refs.clear();
    let mut nodes = 0u64;
    let mut flags = 0u32;
    let mut dangling = 0u32;
    for &r in roots {
        if sc.seen.insert(r) {
            sc.stack.push(r);
        }
    }
    macro_rules! visit {
        ($x:expr) => {{
            let x = $x;
            if sc.seen.insert(x) {
                sc.stack.push(x);
            }
        }};
    }
    macro_rules! cref {
        ($nid:expr) => {{
            let d = s.c2d.get($nid as usize).copied().unwrap_or(NONE);
            if d == NONE {
                dangling += 1;
            } else if d != self_idx {
                sc.refs.push(d);
            }
        }};
    }
    while let Some(e) = sc.stack.pop() {
        nodes += 1;
        let i = e as usize;
        match s.tag[i] {
            K_APP => {
                let (f, a) = (s.a[i], s.b[i]);
                if want_flags && s.tag[a as usize] != K_BVAR {
                    if is_const(s, a, m.bool_true) {
                        // e = (_ Bool.true): is e itself `Eq.refl Bool true`?
                        let fi = f as usize;
                        if s.tag[fi] == K_APP && is_const(s, s.b[fi], m.bool_ty) && is_const(s, s.a[fi], m.eq_refl) {
                            flags |= F_REFL_TRUE;
                        }
                    } else if is_refl_true(s, a, m) {
                        // e = (f (Eq.refl true)): is f = `of_decide_eq_true p inst`?
                        let fi = f as usize;
                        if s.tag[fi] == K_APP {
                            let ffi = s.a[fi] as usize;
                            if s.tag[ffi] == K_APP && is_const(s, s.a[ffi], m.of_decide_eq_true) {
                                flags |= F_OF_DECIDE;
                            }
                        }
                    }
                }
                visit!(f);
                visit!(a);
            }
            K_LAM | K_PI => {
                visit!(s.a[i]);
                visit!(s.b[i]);
            }
            K_CONST => cref!(s.a[i]),
            K_LET => {
                let (v, b) = s.lets[s.b[i] as usize];
                visit!(s.a[i]);
                visit!(v);
                visit!(b);
            }
            K_PROJ => {
                let (tn, _) = s.projs[s.b[i] as usize];
                cref!(tn);
                visit!(s.a[i]);
            }
            K_MDATA => visit!(s.a[i]),
            _ => {}
        }
    }
    sc.refs.sort_unstable();
    sc.refs.dedup();
    (sc.refs.clone(), nodes, flags, dangling)
}

pub fn extract_edges(s: &Store, m: &Markers) -> Vec<DeclEdges> {
    (0..s.decls.len())
        .into_par_iter()
        .with_min_len(64)
        .map_init(
            || Scratch { seen: FastSet::new(), stack: Vec::new(), refs: Vec::new() },
            |sc, di| {
                let d = &s.decls[di];
                let troots: Vec<u32> = d.consts.iter().map(|c| c.ty).collect();
                let (trefs, tnodes, _, dt) = walk(s, &troots, di as u32, m, sc, false);
                let (vrefs, vnodes, flags, dv) = if d.value_roots.is_empty() { (Vec::new(), 0, 0, 0) } else { walk(s, &d.value_roots, di as u32, m, sc, true) };
                DeclEdges { trefs, vrefs, tnodes, vnodes, flags, dangling: dt + dv }
            },
        )
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn fastset_behaves_like_hashset() {
        let mut fs = FastSet::new();
        let mut hs = std::collections::HashSet::new();
        let mut x = 12345u64;
        for round in 0..3 {
            for _ in 0..(50_000 * (round + 1)) {
                x = x.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
                let k = ((x >> 33) % 70_000) as u32;
                assert_eq!(fs.insert(k), hs.insert(k));
            }
            assert_eq!(fs.len(), hs.len());
            fs.clear();
            hs.clear();
        }
    }
}
