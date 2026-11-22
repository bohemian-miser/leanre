//! Line parser: lean4export NDJSON (format 3.1.0) -> compact per-chunk columns.
//!
//! Hot lines (`ie` expressions, `in` names, `il` levels) go through the
//! allocation-free cursor in `json.rs`; declaration records, `meta`, and any
//! line the fast path does not recognise go through strict `serde_json`.

use crate::json::{unescape, Cur};
use serde_json::Value;

pub const K_BVAR: u8 = 0;
pub const K_SORT: u8 = 1;
pub const K_CONST: u8 = 2;
pub const K_APP: u8 = 3;
pub const K_LAM: u8 = 4;
pub const K_PI: u8 = 5;
pub const K_LET: u8 = 6;
pub const K_PROJ: u8 = 7;
pub const K_NAT: u8 = 8;
pub const K_STR: u8 = 9;
pub const K_MDATA: u8 = 10;
pub const K_UNDEF: u8 = 255;

pub const L_ZERO: u8 = 0;
pub const L_SUCC: u8 = 1;
pub const L_MAX: u8 = 2;
pub const L_IMAX: u8 = 3;
pub const L_PARAM: u8 = 4;
pub const L_UNDEF: u8 = 255;

pub const D_THM: u8 = 0;
pub const D_DEF: u8 = 1;
pub const D_OPAQUE: u8 = 2;
pub const D_AXIOM: u8 = 3;
pub const D_QUOT: u8 = 4;
pub const D_INDUCTIVE: u8 = 5;
pub const DECL_KIND_NAMES: [&str; 6] = ["thm", "def", "opaque", "axiom", "quot", "inductive"];

pub const C_THM: u8 = 0;
pub const C_DEF: u8 = 1;
pub const C_OPAQUE: u8 = 2;
pub const C_AXIOM: u8 = 3;
pub const C_QUOT: u8 = 4;
pub const C_INDUCT: u8 = 5;
pub const C_CTOR: u8 = 6;
pub const C_REC: u8 = 7;
pub const CONST_KIND_NAMES: [&str; 8] = ["thm", "def", "opaque", "axiom", "quot", "induct", "ctor", "rec"];

pub const ATTR_UNSAFE: u8 = 1;
pub const ATTR_PARTIAL: u8 = 2;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NameComp {
    Str { off: u32, len: u32 },
    Num(u64),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstRec {
    pub name: u32,
    pub ckind: u8,
    pub ty: u32,
    pub lparams: Vec<u32>,
    /// For inductive types: constructor name ids in cidx order.
    pub ctors: Vec<u32>,
    /// For constructors: name id of the inductive type and constructor index.
    pub induct: u32,
    pub cidx: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DeclRec {
    pub kind: u8,
    pub attrs: u8,
    /// Constants declared by this record. Inductive: types, then ctors, then recs (export order).
    pub consts: Vec<ConstRec>,
    pub value_roots: Vec<u32>,
    pub n_types: u32,
    pub n_ctors: u32,
    pub n_recs: u32,
    /// Size of the `all` mutual group (thm/def/opaque), 0 if absent.
    pub n_all: u32,
}

#[derive(Default, Debug, PartialEq, Eq)]
pub struct ParsedChunk {
    pub seq: u64,
    pub lines: u64,
    pub slow_lines: u64,
    pub e_id: Vec<u32>,
    pub e_tag: Vec<u8>,
    pub e_a: Vec<u32>,
    pub e_b: Vec<u32>,
    pub lets: Vec<(u32, u32)>,
    pub us: Vec<u32>,
    pub projs: Vec<(u32, u32)>,
    pub lits: Vec<(u32, u32)>,
    pub bytes: Vec<u8>,
    pub names: Vec<(u32, u32, NameComp)>,
    pub levels: Vec<(u32, u8, u32, u32)>,
    pub decls: Vec<DeclRec>,
    pub meta: Option<String>,
    pub err: Option<String>,
    scratch_us: Vec<u32>,
}

#[inline]
fn u32c(x: u64) -> Result<u32, ()> {
    if x < u32::MAX as u64 {
        Ok(x as u32)
    } else {
        Err(())
    }
}

#[derive(Default)]
struct Flds<'a> {
    arg: Option<u64>,
    fn_: Option<u64>,
    body: Option<u64>,
    ty: Option<u64>,
    name: Option<u64>,
    value: Option<u64>,
    st: Option<u64>,
    type_name: Option<u64>,
    idx: Option<u64>,
    pre: Option<u64>,
    i: Option<u64>,
    expr: Option<u64>,
    s: Option<(&'a [u8], bool)>,
    us: bool,
}

fn obj<'a>(c: &mut Cur<'a>, us: &mut Vec<u32>) -> Result<Flds<'a>, ()> {
    c.eat(b'{')?;
    let mut f = Flds::default();
    c.ws();
    if c.peek() == b'}' {
        c.i += 1;
        return Ok(f);
    }
    loop {
        let (k, e) = c.raw_str()?;
        if e {
            return Err(());
        }
        c.eat(b':')?;
        match k {
            b"arg" => f.arg = Some(c.num()?),
            b"fn" => f.fn_ = Some(c.num()?),
            b"body" => f.body = Some(c.num()?),
            b"type" => f.ty = Some(c.num()?),
            b"name" => f.name = Some(c.num()?),
            b"value" => f.value = Some(c.num()?),
            b"struct" => f.st = Some(c.num()?),
            b"typeName" => f.type_name = Some(c.num()?),
            b"idx" => f.idx = Some(c.num()?),
            b"pre" => f.pre = Some(c.num()?),
            b"i" => f.i = Some(c.num()?),
            b"expr" => f.expr = Some(c.num()?),
            b"str" => f.s = Some(c.raw_str()?),
            b"us" => {
                us.clear();
                c.eat(b'[')?;
                c.ws();
                if c.peek() == b']' {
                    c.i += 1;
                } else {
                    loop {
                        us.push(u32c(c.num()?)?);
                        c.ws();
                        match c.peek() {
                            b',' => c.i += 1,
                            b']' => {
                                c.i += 1;
                                break;
                            }
                            _ => return Err(()),
                        }
                    }
                }
                f.us = true;
            }
            b"binderInfo" => {
                c.raw_str()?;
            }
            b"nondep" | b"data" => c.skip_value()?,
            _ => return Err(()),
        }
        c.ws();
        match c.peek() {
            b',' => c.i += 1,
            b'}' => {
                c.i += 1;
                break;
            }
            _ => return Err(()),
        }
    }
    Ok(f)
}

fn pair(c: &mut Cur) -> Result<(u32, u32), ()> {
    c.eat(b'[')?;
    let a = u32c(c.num()?)?;
    c.eat(b',')?;
    let b = u32c(c.num()?)?;
    c.eat(b']')?;
    Ok((a, b))
}

enum V<'a> {
    None,
    App(u32, u32),
    Lam(u32, u32),
    Pi(u32, u32),
    Let(u32, u32, u32),
    Const(u32),
    Proj(u32, u32, u32),
    Bvar(u32),
    Sort(u32),
    Nat(&'a [u8], bool),
    Str(&'a [u8], bool),
    Mdata(u32),
    NStr(u32, &'a [u8], bool),
    NNum(u32, u64),
    Succ(u32),
    Max(u32, u32),
    Imax(u32, u32),
    Param(u32),
}

impl ParsedChunk {
    #[inline]
    fn push_expr(&mut self, id: u32, tag: u8, a: u32, b: u32) {
        self.e_id.push(id);
        self.e_tag.push(tag);
        self.e_a.push(a);
        self.e_b.push(b);
    }
    fn push_let(&mut self, id: u32, t: u32, v: u32, b: u32) {
        let k = self.lets.len() as u32;
        self.lets.push((v, b));
        self.push_expr(id, K_LET, t, k);
    }
    fn push_const(&mut self, id: u32, name: u32, us: &[u32]) {
        let off = self.us.len() as u32;
        self.us.push(us.len() as u32);
        self.us.extend_from_slice(us);
        self.push_expr(id, K_CONST, name, off);
    }
    fn push_proj(&mut self, id: u32, st: u32, tn: u32, idx: u32) {
        let k = self.projs.len() as u32;
        self.projs.push((tn, idx));
        self.push_expr(id, K_PROJ, st, k);
    }
    fn push_lit(&mut self, id: u32, tag: u8, raw: &[u8], esc: bool) -> Result<(), ()> {
        let k = self.lits.len() as u32;
        let off = self.bytes.len();
        if esc {
            unescape(raw, &mut self.bytes)?;
        } else {
            self.bytes.extend_from_slice(raw);
        }
        self.lits.push((off as u32, (self.bytes.len() - off) as u32));
        self.push_expr(id, tag, k, 0);
        Ok(())
    }
    fn push_name_str(&mut self, id: u32, pre: u32, raw: &[u8], esc: bool) -> Result<(), ()> {
        let off = self.bytes.len();
        if esc {
            unescape(raw, &mut self.bytes)?;
        } else {
            self.bytes.extend_from_slice(raw);
        }
        self.names.push((id, pre, NameComp::Str { off: off as u32, len: (self.bytes.len() - off) as u32 }));
        Ok(())
    }

    /// Fast path. Returns Err(()) *without mutating self* (except scratch) if the
    /// line is not a recognised ie/in/il record.
    fn fast(&mut self, line: &[u8]) -> Result<(), ()> {
        let mut c = Cur::new(line);
        c.eat(b'{')?;
        let (mut ie, mut il, mut inn) = (None, None, None);
        let mut v = V::None;
        let mut us = std::mem::take(&mut self.scratch_us);
        us.clear();
        let mut has_us = false;
        let r = (|| -> Result<(), ()> {
            loop {
                let (k, e) = c.raw_str()?;
                if e {
                    return Err(());
                }
                c.eat(b':')?;
                match k {
                    b"ie" => ie = Some(u32c(c.num()?)?),
                    b"il" => il = Some(u32c(c.num()?)?),
                    b"in" => inn = Some(u32c(c.num()?)?),
                    b"app" => {
                        let f = obj(&mut c, &mut us)?;
                        v = V::App(u32c(f.fn_.ok_or(())?)?, u32c(f.arg.ok_or(())?)?);
                    }
                    b"lam" => {
                        let f = obj(&mut c, &mut us)?;
                        v = V::Lam(u32c(f.ty.ok_or(())?)?, u32c(f.body.ok_or(())?)?);
                    }
                    b"forallE" => {
                        let f = obj(&mut c, &mut us)?;
                        v = V::Pi(u32c(f.ty.ok_or(())?)?, u32c(f.body.ok_or(())?)?);
                    }
                    b"letE" => {
                        let f = obj(&mut c, &mut us)?;
                        v = V::Let(u32c(f.ty.ok_or(())?)?, u32c(f.value.ok_or(())?)?, u32c(f.body.ok_or(())?)?);
                    }
                    b"const" => {
                        let f = obj(&mut c, &mut us)?;
                        if !f.us {
                            return Err(());
                        }
                        has_us = true;
                        v = V::Const(u32c(f.name.ok_or(())?)?);
                    }
                    b"proj" => {
                        let f = obj(&mut c, &mut us)?;
                        v = V::Proj(u32c(f.st.ok_or(())?)?, u32c(f.type_name.ok_or(())?)?, u32c(f.idx.ok_or(())?)?);
                    }
                    b"mdata" => {
                        let f = obj(&mut c, &mut us)?;
                        v = V::Mdata(u32c(f.expr.ok_or(())?)?);
                    }
                    b"bvar" => v = V::Bvar(u32c(c.num()?)?),
                    b"sort" => v = V::Sort(u32c(c.num()?)?),
                    b"natVal" => {
                        let (s, e) = c.raw_str()?;
                        v = V::Nat(s, e);
                    }
                    b"strVal" => {
                        let (s, e) = c.raw_str()?;
                        v = V::Str(s, e);
                    }
                    b"str" => {
                        let f = obj(&mut c, &mut us)?;
                        let (s, e) = f.s.ok_or(())?;
                        v = V::NStr(u32c(f.pre.ok_or(())?)?, s, e);
                    }
                    b"num" => {
                        let f = obj(&mut c, &mut us)?;
                        v = V::NNum(u32c(f.pre.ok_or(())?)?, f.i.ok_or(())?);
                    }
                    b"succ" => v = V::Succ(u32c(c.num()?)?),
                    b"param" => v = V::Param(u32c(c.num()?)?),
                    b"max" => {
                        let (a, b) = pair(&mut c)?;
                        v = V::Max(a, b);
                    }
                    b"imax" => {
                        let (a, b) = pair(&mut c)?;
                        v = V::Imax(a, b);
                    }
                    _ => return Err(()),
                }
                c.ws();
                match c.peek() {
                    b',' => c.i += 1,
                    b'}' => {
                        c.i += 1;
                        break;
                    }
                    _ => return Err(()),
                }
            }
            c.ws();
            if c.i != c.s.len() {
                return Err(());
            }
            Ok(())
        })();
        let res = r.and_then(|_| match (ie, il, inn, v) {
            (Some(id), None, None, v) => match v {
                V::App(f, a) => Ok(self.push_expr(id, K_APP, f, a)),
                V::Lam(t, b) => Ok(self.push_expr(id, K_LAM, t, b)),
                V::Pi(t, b) => Ok(self.push_expr(id, K_PI, t, b)),
                V::Let(t, val, b) => Ok(self.push_let(id, t, val, b)),
                V::Const(n) if has_us => Ok(self.push_const(id, n, &us)),
                V::Proj(st, tn, idx) => Ok(self.push_proj(id, st, tn, idx)),
                V::Bvar(n) => Ok(self.push_expr(id, K_BVAR, n, 0)),
                V::Sort(l) => Ok(self.push_expr(id, K_SORT, l, 0)),
                V::Mdata(e) => Ok(self.push_expr(id, K_MDATA, e, 0)),
                V::Nat(s, e) => {
                    if e || s.is_empty() || !s.iter().all(|c| c.is_ascii_digit()) {
                        Err(())
                    } else {
                        self.push_lit(id, K_NAT, s, false)
                    }
                }
                V::Str(s, e) => {
                    // validate escapes before mutating
                    if e {
                        let mut tmp = Vec::new();
                        unescape(s, &mut tmp)?;
                    }
                    self.push_lit(id, K_STR, s, e)
                }
                _ => Err(()),
            },
            (None, Some(id), None, v) => match v {
                V::Succ(a) => Ok(self.levels.push((id, L_SUCC, a, 0))),
                V::Max(a, b) => Ok(self.levels.push((id, L_MAX, a, b))),
                V::Imax(a, b) => Ok(self.levels.push((id, L_IMAX, a, b))),
                V::Param(n) => Ok(self.levels.push((id, L_PARAM, n, 0))),
                _ => Err(()),
            },
            (None, None, Some(id), v) => match v {
                V::NStr(pre, s, e) => {
                    if e {
                        let mut tmp = Vec::new();
                        unescape(s, &mut tmp)?;
                    }
                    self.push_name_str(id, pre, s, e)
                }
                V::NNum(pre, i) => Ok(self.names.push((id, pre, NameComp::Num(i)))),
                _ => Err(()),
            },
            _ => Err(()),
        });
        self.scratch_us = us;
        res
    }

    /// Strict serde path: authoritative for declarations/meta, and the fallback for everything else.
    fn slow(&mut self, line: &[u8]) -> Result<(), String> {
        let v: Value = serde_json::from_slice(line).map_err(|e| format!("invalid JSON: {e}"))?;
        let o = v.as_object().ok_or("line is not a JSON object")?;
        fn n32(v: Option<&Value>, what: &str) -> Result<u32, String> {
            let x = v.and_then(|x| x.as_u64()).ok_or_else(|| format!("missing/invalid integer field `{what}`"))?;
            u32c(x).map_err(|_| format!("field `{what}` exceeds u32"))
        }
        fn ids(v: Option<&Value>, what: &str) -> Result<Vec<u32>, String> {
            let a = v.and_then(|x| x.as_array()).ok_or_else(|| format!("missing array `{what}`"))?;
            a.iter().map(|x| n32(Some(x), what)).collect()
        }
        if let Some(m) = o.get("meta") {
            self.meta = Some(m.to_string());
            return Ok(());
        }
        if let Some(idv) = o.get("ie") {
            let id = n32(Some(idv), "ie")?;
            if let Some(d) = o.get("app") {
                self.push_expr(id, K_APP, n32(d.get("fn"), "fn")?, n32(d.get("arg"), "arg")?);
            } else if let Some(d) = o.get("lam") {
                self.push_expr(id, K_LAM, n32(d.get("type"), "type")?, n32(d.get("body"), "body")?);
            } else if let Some(d) = o.get("forallE") {
                self.push_expr(id, K_PI, n32(d.get("type"), "type")?, n32(d.get("body"), "body")?);
            } else if let Some(d) = o.get("letE") {
                self.push_let(id, n32(d.get("type"), "type")?, n32(d.get("value"), "value")?, n32(d.get("body"), "body")?);
            } else if let Some(d) = o.get("const") {
                let us = ids(d.get("us"), "us")?;
                self.push_const(id, n32(d.get("name"), "name")?, &us);
            } else if let Some(d) = o.get("proj") {
                self.push_proj(id, n32(d.get("struct"), "struct")?, n32(d.get("typeName"), "typeName")?, n32(d.get("idx"), "idx")?);
            } else if let Some(d) = o.get("mdata") {
                self.push_expr(id, K_MDATA, n32(d.get("expr"), "expr")?, 0);
            } else if let Some(d) = o.get("bvar") {
                self.push_expr(id, K_BVAR, n32(Some(d), "bvar")?, 0);
            } else if let Some(d) = o.get("sort") {
                self.push_expr(id, K_SORT, n32(Some(d), "sort")?, 0);
            } else if let Some(d) = o.get("natVal") {
                let s = d.as_str().ok_or("natVal is not a string")?;
                if s.is_empty() || !s.bytes().all(|c| c.is_ascii_digit()) {
                    return Err("natVal is not a decimal string".into());
                }
                self.push_lit(id, K_NAT, s.as_bytes(), false).unwrap();
            } else if let Some(d) = o.get("strVal") {
                let s = d.as_str().ok_or("strVal is not a string")?;
                self.push_lit(id, K_STR, s.as_bytes(), false).unwrap();
            } else {
                return Err(format!("unknown expression kind: keys {:?}", o.keys().collect::<Vec<_>>()));
            }
            return Ok(());
        }
        if let Some(idv) = o.get("il") {
            let id = n32(Some(idv), "il")?;
            if let Some(d) = o.get("succ") {
                self.levels.push((id, L_SUCC, n32(Some(d), "succ")?, 0));
            } else if let Some(d) = o.get("max") {
                let p = ids(Some(d), "max")?;
                if p.len() != 2 {
                    return Err("max needs 2 levels".into());
                }
                self.levels.push((id, L_MAX, p[0], p[1]));
            } else if let Some(d) = o.get("imax") {
                let p = ids(Some(d), "imax")?;
                if p.len() != 2 {
                    return Err("imax needs 2 levels".into());
                }
                self.levels.push((id, L_IMAX, p[0], p[1]));
            } else if let Some(d) = o.get("param") {
                self.levels.push((id, L_PARAM, n32(Some(d), "param")?, 0));
            } else {
                return Err(format!("unknown level kind: keys {:?}", o.keys().collect::<Vec<_>>()));
            }
            return Ok(());
        }
        if let Some(idv) = o.get("in") {
            let id = n32(Some(idv), "in")?;
            if let Some(d) = o.get("str") {
                let s = d.get("str").and_then(|x| x.as_str()).ok_or("name str component missing")?;
                self.push_name_str(id, n32(d.get("pre"), "pre")?, s.as_bytes(), false).unwrap();
            } else if let Some(d) = o.get("num") {
                let i = d.get("i").and_then(|x| x.as_u64()).ok_or("name num component missing or > u64")?;
                self.names.push((id, n32(d.get("pre"), "pre")?, NameComp::Num(i)));
            } else {
                return Err(format!("unknown name kind: keys {:?}", o.keys().collect::<Vec<_>>()));
            }
            return Ok(());
        }
        let attrs = |d: &Value| -> u8 {
            let mut a = 0;
            if d.get("isUnsafe").and_then(|x| x.as_bool()) == Some(true) || d.get("safety").and_then(|x| x.as_str()) == Some("unsafe") {
                a |= ATTR_UNSAFE;
            }
            if d.get("safety").and_then(|x| x.as_str()) == Some("partial") {
                a |= ATTR_PARTIAL;
            }
            a
        };
        let n_all = |d: &Value| d.get("all").and_then(|x| x.as_array()).map(|a| a.len() as u32).unwrap_or(0);
        let simple = |d: &Value, kind: u8, ckind: u8, has_value: bool| -> Result<DeclRec, String> {
            Ok(DeclRec {
                kind,
                attrs: attrs(d),
                consts: vec![ConstRec { name: n32(d.get("name"), "name")?, ckind, ty: n32(d.get("type"), "type")?, lparams: ids(d.get("levelParams"), "levelParams")?, ctors: vec![], induct: 0, cidx: 0 }],
                value_roots: if has_value { vec![n32(d.get("value"), "value")?] } else { vec![] },
                n_types: 0,
                n_ctors: 0,
                n_recs: 0,
                n_all: n_all(d),
            })
        };
        if let Some(d) = o.get("thm") {
            self.decls.push(simple(d, D_THM, C_THM, true)?);
        } else if let Some(d) = o.get("def") {
            self.decls.push(simple(d, D_DEF, C_DEF, true)?);
        } else if let Some(d) = o.get("opaque") {
            self.decls.push(simple(d, D_OPAQUE, C_OPAQUE, true)?);
        } else if let Some(d) = o.get("axiom") {
            self.decls.push(simple(d, D_AXIOM, C_AXIOM, false)?);
        } else if let Some(d) = o.get("quot") {
            self.decls.push(simple(d, D_QUOT, C_QUOT, false)?);
        } else if let Some(d) = o.get("inductive") {
            let types = d.get("types").and_then(|x| x.as_array()).ok_or("inductive.types missing")?;
            let ctors = d.get("ctors").and_then(|x| x.as_array()).ok_or("inductive.ctors missing")?;
            let recs = d.get("recs").and_then(|x| x.as_array()).ok_or("inductive.recs missing")?;
            if types.is_empty() {
                return Err("inductive record with no types".into());
            }
            let mut consts = Vec::with_capacity(types.len() + ctors.len() + recs.len());
            let mut at = 0u8;
            for t in types {
                at |= attrs(t);
                consts.push(ConstRec { name: n32(t.get("name"), "name")?, ckind: C_INDUCT, ty: n32(t.get("type"), "type")?, lparams: ids(t.get("levelParams"), "levelParams")?, ctors: ids(t.get("ctors"), "ctors")?, induct: 0, cidx: 0 });
            }
            for c in ctors {
                at |= attrs(c);
                consts.push(ConstRec { name: n32(c.get("name"), "name")?, ckind: C_CTOR, ty: n32(c.get("type"), "type")?, lparams: ids(c.get("levelParams"), "levelParams")?, ctors: vec![], induct: n32(c.get("induct"), "induct")?, cidx: n32(c.get("cidx"), "cidx")? });
            }
            let mut value_roots = Vec::new();
            for r in recs {
                at |= attrs(r);
                consts.push(ConstRec { name: n32(r.get("name"), "name")?, ckind: C_REC, ty: n32(r.get("type"), "type")?, lparams: ids(r.get("levelParams"), "levelParams")?, ctors: vec![], induct: 0, cidx: 0 });
                for rule in r.get("rules").and_then(|x| x.as_array()).ok_or("rec.rules missing")? {
                    value_roots.push(n32(rule.get("rhs"), "rhs")?);
                }
            }
            self.decls.push(DeclRec { kind: D_INDUCTIVE, attrs: at, consts, value_roots, n_types: types.len() as u32, n_ctors: ctors.len() as u32, n_recs: recs.len() as u32, n_all: 0 });
        } else {
            return Err(format!("unknown record: keys {:?}", o.keys().collect::<Vec<_>>()));
        }
        Ok(())
    }

    pub fn parse_line(&mut self, line: &[u8], force_slow: bool) -> Result<(), String> {
        self.lines += 1;
        if !force_slow && self.fast(line).is_ok() {
            return Ok(());
        }
        self.slow_lines += 1;
        self.slow(line)
    }
}

/// Parse a newline-delimited block (complete lines only).
pub fn parse_chunk(seq: u64, data: &[u8], force_slow: bool) -> ParsedChunk {
    let mut pc = ParsedChunk { seq, ..Default::default() };
    let approx = data.len() / 48;
    pc.e_id.reserve(approx);
    pc.e_tag.reserve(approx);
    pc.e_a.reserve(approx);
    pc.e_b.reserve(approx);
    let mut st = 0usize;
    while st < data.len() {
        let end = memchr::memchr(b'\n', &data[st..]).map(|p| st + p).unwrap_or(data.len());
        let mut line = &data[st..end];
        if line.last() == Some(&b'\r') {
            line = &line[..line.len() - 1];
        }
        if !line.is_empty() {
            if let Err(e) = pc.parse_line(line, force_slow) {
                let shown = String::from_utf8_lossy(&line[..line.len().min(200)]).to_string();
                pc.err = Some(format!("chunk {seq} line {}: {e}: {shown}", pc.lines));
                return pc;
            }
        }
        st = end + 1;
    }
    pc
}

#[cfg(test)]
pub mod tests {
    use super::*;

    pub const SAMPLE: &str = r#"{"meta":{"exporter":{"name":"lean4export","version":"3.1.0"},"format":{"version":"3.1.0"},"lean":{"githash":"x","version":"4.33.1"}}}
{"in":1,"str":{"pre":0,"str":"Eq"}}
{"in":2,"str":{"pre":0,"str":"u_1"}}
{"il":1,"param":2}
{"il":4,"succ":2}
{"il":9,"max":[4,6]}
{"il":27,"imax":[2,3]}
{"ie":0,"sort":1}
{"in":8,"num":{"i":0,"pre":7}}
{"bvar":0,"ie":1}
{"forallE":{"binderInfo":"default","body":3,"name":8,"type":2},"ie":4}
{"const":{"name":1,"us":[1]},"ie":7}
{"const":{"name":1,"us":[]},"ie":70}
{"app":{"arg":2,"fn":7},"ie":8}
{"ie":40,"lam":{"binderInfo":"implicit","body":39,"name":8,"type":1}}
{"ie":52964,"letE":{"body":1,"name":760,"nondep":false,"type":52963,"value":1}}
{"ie":170,"proj":{"idx":0,"struct":1,"typeName":31}}
{"ie":8993,"strVal":"Le\"an\u00e9 «α»"}
{"ie":389,"natVal":"340282366920938463463374607431768211456"}
{"in":11,"str":{"pre":1,"str":"«weird.name»\n"}}
{"thm":{"all":[630],"levelParams":[],"name":630,"type":2696,"value":2702}}
{"def":{"all":[39],"hints":"abbrev","levelParams":[11],"name":39,"safety":"safe","type":176,"value":179}}
{"opaque":{"all":[8451],"isUnsafe":false,"levelParams":[],"name":8451,"type":68711,"value":68725}}
{"quot":{"kind":"ind","levelParams":[11],"name":23,"type":86}}
{"axiom":{"isUnsafe":false,"levelParams":[],"name":2661,"type":13681}}
{"inductive":{"ctors":[{"cidx":0,"induct":1,"isUnsafe":false,"levelParams":[2],"name":9,"numFields":0,"numParams":2,"type":12}],"recs":[{"all":[1],"isUnsafe":false,"k":true,"levelParams":[11,2],"name":10,"numIndices":1,"numMinors":1,"numMotives":1,"numParams":2,"rules":[{"ctor":9,"nfields":0,"rhs":41}],"type":37}],"types":[{"all":[1],"ctors":[9],"isRec":false,"isReflexive":false,"isUnsafe":false,"levelParams":[2],"name":1,"numIndices":1,"numNested":0,"numParams":2,"type":6}]}}
"#;

    #[test]
    fn fast_and_slow_paths_agree() {
        let fast = parse_chunk(0, SAMPLE.as_bytes(), false);
        let mut slow = parse_chunk(0, SAMPLE.as_bytes(), true);
        assert!(fast.err.is_none(), "{:?}", fast.err);
        assert!(slow.err.is_none(), "{:?}", slow.err);
        assert_eq!(fast.lines, 26);
        // meta + 6 declaration records are the only lines the fast path may hand to serde
        assert_eq!(fast.slow_lines, 7);
        slow.slow_lines = fast.slow_lines;
        assert_eq!(fast, slow);
        assert_eq!(fast.e_id, vec![0, 1, 4, 7, 70, 8, 40, 52964, 170, 8993, 389]);
        assert_eq!(fast.decls.len(), 6);
        let ind = &fast.decls[5];
        assert_eq!((ind.n_types, ind.n_ctors, ind.n_recs), (1, 1, 1));
        assert_eq!(ind.consts.iter().map(|c| c.name).collect::<Vec<_>>(), vec![1, 9, 10]);
        assert_eq!(ind.value_roots, vec![41]);
        assert_eq!(ind.consts[0].ctors, vec![9]);
    }

    #[test]
    fn rejects_garbage() {
        for bad in ["{\"ie\":1,\"wat\":2}\n", "{\"ie\":1}\n", "not json\n", "{\"il\":3,\"max\":[1]}\n", "{\"ie\":3,\"natVal\":\"12x\"}\n", "{\"zzz\":{}}\n"] {
            let pc = parse_chunk(0, bad.as_bytes(), false);
            assert!(pc.err.is_some(), "{bad}");
        }
    }
}
