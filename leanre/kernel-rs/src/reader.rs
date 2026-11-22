//! Streaming input pipeline: read (+SHA-256 of the compressed bytes) ->
//! zstd decode (window up to 2^31) -> SHA-256 of the decoded bytes on its own
//! thread -> newline-aligned blocks -> N parser threads -> in-order apply.

use crate::parse::{parse_chunk, ParsedChunk};
use crossbeam_channel::bounded;
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use std::fs::File;
use std::io::Read;
use std::sync::{Arc, Mutex};

const BLOCK: usize = 4 << 20;

pub struct InputInfo {
    pub path: String,
    pub file_bytes: u64,
    pub is_zstd: bool,
    pub file_sha256: String,
    pub uncompressed_bytes: u64,
    pub uncompressed_sha256: String,
    pub chunks: u64,
}

pub fn hex(b: &[u8]) -> String {
    let mut s = String::with_capacity(b.len() * 2);
    for x in b {
        s.push_str(&format!("{:02x}", x));
    }
    s
}

struct HashRead {
    inner: File,
    st: Arc<Mutex<(Sha256, u64)>>,
}

impl Read for HashRead {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        let n = self.inner.read(buf)?;
        if n > 0 {
            let mut g = self.st.lock().unwrap();
            g.0.update(&buf[..n]);
            g.1 += n as u64;
        }
        Ok(n)
    }
}

pub fn run(path: &str, parse_threads: usize, force_slow: bool, mut apply: impl FnMut(ParsedChunk) -> Result<(), String>) -> Result<InputInfo, String> {
    let file = File::open(path).map_err(|e| format!("open {path}: {e}"))?;
    let file_bytes = file.metadata().map_err(|e| e.to_string())?.len();
    let is_zstd = path.ends_with(".zst");
    let st = Arc::new(Mutex::new((Sha256::new(), 0u64)));
    let hr = HashRead { inner: file, st: st.clone() };
    let mut src: Box<dyn Read + Send> = if is_zstd {
        let mut d = zstd::stream::read::Decoder::new(hr).map_err(|e| format!("zstd init: {e}"))?;
        d.window_log_max(31).map_err(|e| format!("zstd window_log_max: {e}"))?;
        Box::new(d)
    } else {
        Box::new(hr)
    };
    let parse_threads = parse_threads.max(1);

    let result = std::thread::scope(|sc| -> Result<(String, u64, u64), String> {
        let (tx_raw, rx_raw) = bounded::<(u64, Vec<u8>)>(parse_threads * 2);
        let (tx_hash, rx_hash) = bounded::<Arc<Vec<u8>>>(64);
        let (tx_out, rx_out) = bounded::<ParsedChunk>(parse_threads * 2);

        let hasher = sc.spawn(move || {
            let mut h = Sha256::new();
            let mut n = 0u64;
            for blk in rx_hash {
                h.update(&blk[..]);
                n += blk.len() as u64;
            }
            (hex(&h.finalize()), n)
        });

        let reader = sc.spawn(move || -> Result<u64, String> {
            let mut carry: Vec<u8> = Vec::new();
            let mut seq = 0u64;
            loop {
                let mut blk = vec![0u8; BLOCK];
                let mut filled = 0;
                while filled < BLOCK {
                    let n = src.read(&mut blk[filled..]).map_err(|e| format!("read/decode error after block {seq}: {e}"))?;
                    if n == 0 {
                        break;
                    }
                    filled += n;
                }
                blk.truncate(filled);
                let eof = filled < BLOCK;
                let blk = Arc::new(blk);
                if filled > 0 && tx_hash.send(blk.clone()).is_err() {
                    return Err("hasher thread gone".into());
                }
                let cut = if eof { Some(filled) } else { memchr::memrchr(b'\n', &blk).map(|p| p + 1) };
                match cut {
                    None => carry.extend_from_slice(&blk),
                    Some(cut) => {
                        let mut chunk = Vec::with_capacity(carry.len() + cut);
                        chunk.extend_from_slice(&carry);
                        chunk.extend_from_slice(&blk[..cut]);
                        carry.clear();
                        carry.extend_from_slice(&blk[cut..]);
                        if !chunk.is_empty() {
                            if tx_raw.send((seq, chunk)).is_err() {
                                return Err("parser threads gone".into());
                            }
                            seq += 1;
                        }
                    }
                }
                if eof {
                    break;
                }
            }
            // make sure the hash covers every byte of the input file (trailing bytes after the last frame)
            let mut sink = vec![0u8; 1 << 16];
            while src.read(&mut sink).map_err(|e| e.to_string())? > 0 {}
            Ok(seq)
        });

        for _ in 0..parse_threads {
            let rx = rx_raw.clone();
            let tx = tx_out.clone();
            sc.spawn(move || {
                for (seq, data) in rx {
                    let pc = parse_chunk(seq, &data, force_slow);
                    drop(data);
                    if tx.send(pc).is_err() {
                        break;
                    }
                }
            });
        }
        drop(rx_raw);
        drop(tx_out);

        let mut next = 0u64;
        let mut pend: BTreeMap<u64, ParsedChunk> = BTreeMap::new();
        let mut err: Option<String> = None;
        'outer: for pc in rx_out.iter() {
            pend.insert(pc.seq, pc);
            while let Some(mut pc) = pend.remove(&next) {
                next += 1;
                if let Some(e) = pc.err.take() {
                    err = Some(e);
                    break 'outer;
                }
                if let Err(e) = apply(pc) {
                    err = Some(e);
                    break 'outer;
                }
            }
        }
        drop(rx_out);
        let chunks = reader.join().map_err(|_| "reader thread panicked".to_string())?;
        let (usha, ubytes) = hasher.join().map_err(|_| "hasher thread panicked".to_string())?;
        if let Some(e) = err {
            return Err(e);
        }
        let chunks = chunks?;
        if next != chunks || !pend.is_empty() {
            return Err(format!("pipeline lost chunks: applied {next} of {chunks}"));
        }
        Ok((usha, ubytes, chunks))
    })?;

    let g = st.lock().unwrap();
    let file_sha256 = hex(&g.0.clone().finalize());
    if g.1 != file_bytes {
        return Err(format!("read {} bytes but file has {}", g.1, file_bytes));
    }
    Ok(InputInfo { path: path.to_string(), file_bytes, is_zstd, file_sha256, uncompressed_bytes: result.1, uncompressed_sha256: result.0, chunks: result.2 })
}
