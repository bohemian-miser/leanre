//! Minimal allocation-free JSON cursor for the hot ie/in/il lines of a
//! lean4export NDJSON stream. Anything it does not understand returns Err(())
//! and the caller falls back to the strict serde_json path.

pub struct Cur<'a> {
    pub s: &'a [u8],
    pub i: usize,
}

impl<'a> Cur<'a> {
    #[inline]
    pub fn new(s: &'a [u8]) -> Self {
        Cur { s, i: 0 }
    }
    #[inline]
    pub fn peek(&self) -> u8 {
        if self.i < self.s.len() {
            self.s[self.i]
        } else {
            0
        }
    }
    #[inline]
    pub fn ws(&mut self) {
        while self.i < self.s.len() && matches!(self.s[self.i], b' ' | b'\t' | b'\r' | b'\n') {
            self.i += 1;
        }
    }
    #[inline]
    pub fn eat(&mut self, c: u8) -> Result<(), ()> {
        self.ws();
        if self.peek() == c {
            self.i += 1;
            Ok(())
        } else {
            Err(())
        }
    }
    /// Non-negative integer that fits u64 (no sign, fraction or exponent).
    #[inline]
    pub fn num(&mut self) -> Result<u64, ()> {
        self.ws();
        let st = self.i;
        let mut v: u64 = 0;
        while self.i < self.s.len() {
            let d = self.s[self.i].wrapping_sub(b'0');
            if d > 9 {
                break;
            }
            v = v.checked_mul(10).ok_or(())?.checked_add(d as u64).ok_or(())?;
            self.i += 1;
        }
        if self.i == st || matches!(self.peek(), b'.' | b'e' | b'E') {
            return Err(());
        }
        Ok(v)
    }
    /// Returns the raw bytes between the quotes and whether they contain escapes.
    #[inline]
    pub fn raw_str(&mut self) -> Result<(&'a [u8], bool), ()> {
        self.ws();
        if self.peek() != b'"' {
            return Err(());
        }
        self.i += 1;
        let st = self.i;
        let mut esc = false;
        loop {
            match memchr::memchr2(b'"', b'\\', &self.s[self.i..]) {
                None => return Err(()),
                Some(p) => {
                    if self.s[self.i + p] == b'"' {
                        let end = self.i + p;
                        self.i = end + 1;
                        return Ok((&self.s[st..end], esc));
                    }
                    esc = true;
                    self.i += p + 2;
                    if self.i > self.s.len() {
                        return Err(());
                    }
                }
            }
        }
    }
    pub fn skip_value(&mut self) -> Result<(), ()> {
        self.ws();
        match self.peek() {
            b'"' => {
                self.raw_str()?;
                Ok(())
            }
            b'{' | b'[' => {
                let mut depth = 0usize;
                loop {
                    match self.peek() {
                        b'"' => {
                            self.raw_str()?;
                            continue;
                        }
                        b'{' | b'[' => depth += 1,
                        b'}' | b']' => {
                            depth -= 1;
                            if depth == 0 {
                                self.i += 1;
                                return Ok(());
                            }
                        }
                        0 if self.i >= self.s.len() => return Err(()),
                        _ => {}
                    }
                    self.i += 1;
                }
            }
            _ => {
                let st = self.i;
                while self.i < self.s.len() && !matches!(self.s[self.i], b',' | b'}' | b']' | b' ' | b'\n' | b'\r' | b'\t') {
                    self.i += 1;
                }
                if self.i == st {
                    Err(())
                } else {
                    Ok(())
                }
            }
        }
    }
}

fn hex4(b: &[u8]) -> Result<u32, ()> {
    if b.len() < 4 {
        return Err(());
    }
    let mut v = 0u32;
    for &c in &b[..4] {
        v = v * 16 + (c as char).to_digit(16).ok_or(())?;
    }
    Ok(v)
}

/// Unescape the raw content of a JSON string (bytes between the quotes) to UTF-8.
pub fn unescape(raw: &[u8], out: &mut Vec<u8>) -> Result<(), ()> {
    let mut i = 0;
    while i < raw.len() {
        let c = raw[i];
        if c != b'\\' {
            out.push(c);
            i += 1;
            continue;
        }
        i += 1;
        if i >= raw.len() {
            return Err(());
        }
        match raw[i] {
            b'"' => out.push(b'"'),
            b'\\' => out.push(b'\\'),
            b'/' => out.push(b'/'),
            b'b' => out.push(8),
            b'f' => out.push(12),
            b'n' => out.push(b'\n'),
            b'r' => out.push(b'\r'),
            b't' => out.push(b'\t'),
            b'u' => {
                let mut cp = hex4(&raw[i + 1..])?;
                i += 4;
                if (0xD800..0xDC00).contains(&cp) {
                    if raw.len() >= i + 7 && raw[i + 1] == b'\\' && raw[i + 2] == b'u' {
                        let lo = hex4(&raw[i + 3..])?;
                        if (0xDC00..0xE000).contains(&lo) {
                            cp = 0x10000 + ((cp - 0xD800) << 10) + (lo - 0xDC00);
                            i += 6;
                        } else {
                            return Err(());
                        }
                    } else {
                        return Err(());
                    }
                }
                let ch = char::from_u32(cp).ok_or(())?;
                let mut buf = [0u8; 4];
                out.extend_from_slice(ch.encode_utf8(&mut buf).as_bytes());
            }
            _ => return Err(()),
        }
        i += 1;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unescape_matches_serde() {
        for raw in [r#"plain"#, r#"a\"b\\c\/d"#, r#"\u00e9\u03b1\n\t"#, r#"\ud83d\ude00x"#, "αβγ «x»"] {
            let mut out = Vec::new();
            unescape(raw.as_bytes(), &mut out).unwrap();
            let want: String = serde_json::from_str(&format!("\"{}\"", raw)).unwrap();
            assert_eq!(String::from_utf8(out).unwrap(), want, "{raw}");
        }
        let mut out = Vec::new();
        assert!(unescape(br"\ud83d", &mut out).is_err());
        assert!(unescape(br"\q", &mut out).is_err());
    }

    #[test]
    fn cursor_basics() {
        let mut c = Cur::new(br#"{"a":12,"b":"x\"y","c":[1,{"d":"]"}],"e":true}"#);
        c.eat(b'{').unwrap();
        assert_eq!(c.raw_str().unwrap(), (&b"a"[..], false));
        c.eat(b':').unwrap();
        assert_eq!(c.num().unwrap(), 12);
        c.eat(b',').unwrap();
        c.raw_str().unwrap();
        c.eat(b':').unwrap();
        assert_eq!(c.raw_str().unwrap(), (&br#"x\"y"#[..], true));
        c.eat(b',').unwrap();
        c.raw_str().unwrap();
        c.eat(b':').unwrap();
        c.skip_value().unwrap();
        c.eat(b',').unwrap();
        c.raw_str().unwrap();
        c.eat(b':').unwrap();
        c.skip_value().unwrap();
        c.eat(b'}').unwrap();
        assert!(Cur::new(b"1.5").num().is_err());
        assert!(Cur::new(b"99999999999999999999999").num().is_err());
    }
}
