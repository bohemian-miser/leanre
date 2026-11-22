//! In-memory tables for the whole export: expression DAG (struct-of-arrays,
//! 9 bytes per node), name tree, universe levels and declaration records.

use crate::parse::*;

pub const NONE: u32 = u32::MAX;

#[derive(Default)]
pub struct Store {
    pub tag: Vec<u8>,
    pub a: Vec<u32>,
    pub b: Vec<u32>,
    pub lets: Vec<(u32, u32)>,
    pub us: Vec<u32>,
    pub projs: Vec<(u32, u32)>,
    pub lits: Vec<(u64, u32)>,
    pub lit_bytes: Vec<u8>,
    pub n_pre: Vec<u32>,
    pub n_kind: Vec<u8>,
    pub n_val: Vec<u64>,
    pub n_len: Vec<u32>,
    pub name_bytes: Vec<u8>,
    pub l_kind: Vec<u8>,
    pub l_a: Vec<u32>,
    pub l_b: Vec<u32>,
    pub decls: Vec<DeclRec>,
    pub meta: Option<String>,
    pub lines: u64,
    pub slow_lines: u64,
    pub expr_lines: u64,
    pub name_lines: u64,
    pub level_lines: u64,
    pub dup_expr: u64,
    pub dup_name: u64,
    pub dup_level: u64,
    pub expr_kind_counts: [u64; 11],
    /// name id -> declaration index (NONE if the name is not a declared constant)
    pub c2d: Vec<u32>,
    pub dup_const: u64,
}

impl Store {
    pub fn new() -> Self {
        let mut s = Store::default();
        // name 0 = anonymous, level 0 = zero (implicit in the format)
        s.n_pre.push(0);
        s.n_kind.push(0);
        s.n_val.push(0);
        s.n_len.push(0);
        s.l_kind.push(L_ZERO);
        s.l_a.push(0);
        s.l_b.push(0);
        s
    }

    pub fn apply(&mut self, pc: ParsedChunk) -> Result<(), String> {
        self.lines += pc.lines;
        self.slow_lines += pc.slow_lines;
        if let Some(m) = pc.meta {
            self.meta = Some(m);
        }
        let base_bytes = self.name_bytes.len() as u64;
        // names (string components live in pc.bytes together with literals; copy only what names use)
        for (id, pre, comp) in &pc.names {
            let id = *id as usize;
            if id >= self.n_kind.len() {
                self.n_pre.resize(id + 1, 0);
                self.n_kind.resize(id + 1, 0);
                self.n_val.resize(id + 1, 0);
                self.n_len.resize(id + 1, 0);
            } else if self.n_kind[id] != 0 || id == 0 {
                self.dup_name += 1;
            }
            self.n_pre[id] = *pre;
            match comp {
                NameComp::Str { off, len } => {
                    self.n_kind[id] = 1;
                    self.n_val[id] = self.name_bytes.len() as u64;
                    self.n_len[id] = *len;
                    self.name_bytes.extend_from_slice(&pc.bytes[*off as usize..(*off + *len) as usize]);
                }
                NameComp::Num(i) => {
                    self.n_kind[id] = 2;
                    self.n_val[id] = *i;
                }
            }
        }
        let _ = base_bytes;
        self.name_lines += pc.names.len() as u64;
        for &(id, kind, a, b) in &pc.levels {
            let id = id as usize;
            if id >= self.l_kind.len() {
                self.l_kind.resize(id + 1, L_UNDEF);
                self.l_a.resize(id + 1, 0);
                self.l_b.resize(id + 1, 0);
            } else if self.l_kind[id] != L_UNDEF {
                self.dup_level += 1;
            }
            self.l_kind[id] = kind;
            self.l_a[id] = a;
            self.l_b[id] = b;
        }
        self.level_lines += pc.levels.len() as u64;
        let base_lets = self.lets.len() as u64;
        let base_us = self.us.len() as u64;
        let base_projs = self.projs.len() as u64;
        let base_lits = self.lits.len() as u64;
        let base_lit_bytes = self.lit_bytes.len() as u64;
        if base_lets + pc.lets.len() as u64 >= NONE as u64 || base_us + pc.us.len() as u64 >= NONE as u64 || base_projs + pc.projs.len() as u64 >= NONE as u64 || base_lits + pc.lits.len() as u64 >= NONE as u64 {
            return Err("side-table index exceeds u32".into());
        }
        self.lets.extend_from_slice(&pc.lets);
        self.us.extend_from_slice(&pc.us);
        self.projs.extend_from_slice(&pc.projs);
        for &(off, len) in &pc.lits {
            self.lits.push((self.lit_bytes.len() as u64, len));
            self.lit_bytes.extend_from_slice(&pc.bytes[off as usize..(off + len) as usize]);
        }
        let _ = base_lit_bytes;
        let n = pc.e_id.len();
        self.expr_lines += n as u64;
        for i in 0..n {
            let id = pc.e_id[i] as usize;
            let tag = pc.e_tag[i];
            let mut a = pc.e_a[i];
            let mut b = pc.e_b[i];
            match tag {
                K_LET => b += base_lets as u32,
                K_CONST => b += base_us as u32,
                K_PROJ => b += base_projs as u32,
                K_NAT | K_STR => a += base_lits as u32,
                _ => {}
            }
            self.expr_kind_counts[tag as usize] += 1;
            if id == self.tag.len() {
                self.tag.push(tag);
                self.a.push(a);
                self.b.push(b);
            } else {
                if id > self.tag.len() {
                    self.tag.resize(id + 1, K_UNDEF);
                    self.a.resize(id + 1, 0);
                    self.b.resize(id + 1, 0);
                } else if self.tag[id] != K_UNDEF {
                    self.dup_expr += 1;
                }
                self.tag[id] = tag;
                self.a[id] = a;
                self.b[id] = b;
            }
        }
        self.decls.extend(pc.decls);
        Ok(())
    }

    /// Build the constant -> declaration map and validate references made by declaration records.
    pub fn finish(&mut self) -> Result<(), String> {
        if self.decls.len() >= NONE as usize {
            return Err("too many declarations".into());
        }
        self.c2d = vec![NONE; self.n_kind.len()];
        for (di, d) in self.decls.iter().enumerate() {
            for c in &d.consts {
                let nid = c.name as usize;
                if nid >= self.c2d.len() || self.n_kind[nid] == 0 {
                    return Err(format!("declaration {di} names undefined name id {nid}"));
                }
                if self.c2d[nid] != NONE {
                    self.dup_const += 1;
                }
                self.c2d[nid] = di as u32;
                if c.ty as usize >= self.tag.len() || self.tag[c.ty as usize] == K_UNDEF {
                    return Err(format!("declaration {di} type expr {} undefined", c.ty));
                }
            }
            for &v in &d.value_roots {
                if v as usize >= self.tag.len() || self.tag[v as usize] == K_UNDEF {
                    return Err(format!("declaration {di} value expr {v} undefined"));
                }
            }
        }
        Ok(())
    }

    /// Dotted rendering identical to Phase 2 `ndjson.py` (plain join, no «» escaping).
    pub fn name_string(&self, mut id: u32) -> String {
        let mut parts: Vec<String> = Vec::new();
        while id != 0 {
            let i = id as usize;
            match self.n_kind.get(i).copied().unwrap_or(0) {
                1 => {
                    let off = self.n_val[i] as usize;
                    parts.push(String::from_utf8_lossy(&self.name_bytes[off..off + self.n_len[i] as usize]).into_owned());
                }
                2 => parts.push(self.n_val[i].to_string()),
                _ => {
                    parts.push("?undefined-name?".into());
                    break;
                }
            }
            id = self.n_pre[i];
        }
        parts.reverse();
        parts.join(".")
    }

    pub fn lit(&self, k: u32) -> &[u8] {
        let (off, len) = self.lits[k as usize];
        &self.lit_bytes[off as usize..off as usize + len as usize]
    }

    pub fn drop_expr_tables(&mut self) {
        self.tag = Vec::new();
        self.a = Vec::new();
        self.b = Vec::new();
        self.lets = Vec::new();
        self.us = Vec::new();
        self.projs = Vec::new();
        self.lits = Vec::new();
        self.lit_bytes = Vec::new();
        self.n_pre = Vec::new();
        self.n_kind = Vec::new();
        self.n_val = Vec::new();
        self.n_len = Vec::new();
        self.name_bytes = Vec::new();
        self.l_kind = Vec::new();
        self.l_a = Vec::new();
        self.l_b = Vec::new();
        self.c2d = Vec::new();
    }

    pub fn mem_bytes(&self) -> u64 {
        (self.tag.capacity() + 4 * self.a.capacity() + 4 * self.b.capacity() + 8 * self.lets.capacity() + 4 * self.us.capacity() + 8 * self.projs.capacity() + 16 * self.lits.capacity() + self.lit_bytes.capacity() + 17 * self.n_kind.capacity() + self.name_bytes.capacity() + 4 * self.c2d.capacity()) as u64
    }
}
