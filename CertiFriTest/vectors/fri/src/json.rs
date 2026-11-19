//! A minimal JSON writer.
//!
//! The vectors hold nothing but unsigned integers, booleans, short ASCII
//! strings, arrays and objects, so a hand-written writer keeps the output
//! byte-for-byte stable and the key order under control.

use std::fmt::Write;

/// A JSON value. Object keys keep the order they are given in.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Json {
    Num(u64),
    Bool(bool),
    Str(String),
    Arr(Vec<Json>),
    Obj(Vec<(&'static str, Json)>),
}

/// Values at most this long, once rendered on one line, are kept on one line.
const INLINE_WIDTH: usize = 100;

impl Json {
    pub fn str(s: &str) -> Json {
        Json::Str(s.to_string())
    }

    pub fn num(n: usize) -> Json {
        Json::Num(n as u64)
    }

    pub fn arr<T>(items: impl IntoIterator<Item = T>, f: impl Fn(T) -> Json) -> Json {
        Json::Arr(items.into_iter().map(f).collect())
    }

    fn is_scalar(&self) -> bool {
        !matches!(self, Json::Arr(_) | Json::Obj(_))
    }

    /// Render on one line.
    fn compact(&self, out: &mut String) {
        match self {
            Json::Num(n) => write!(out, "{n}").unwrap(),
            Json::Bool(b) => write!(out, "{b}").unwrap(),
            Json::Str(s) => write_string(out, s),
            Json::Arr(items) => {
                out.push('[');
                for (i, item) in items.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    item.compact(out);
                }
                out.push(']');
            }
            Json::Obj(fields) => {
                out.push('{');
                for (i, (key, value)) in fields.iter().enumerate() {
                    if i > 0 {
                        out.push_str(", ");
                    }
                    write_string(out, key);
                    out.push_str(": ");
                    value.compact(out);
                }
                out.push('}');
            }
        }
    }

    /// Whether the value is written on one line: a scalar, an array of
    /// scalars of any length (a digest, a row of field elements), or anything
    /// short enough.
    fn inline(&self) -> Option<String> {
        let all_scalars = match self {
            Json::Arr(items) => items.iter().all(Json::is_scalar),
            Json::Obj(_) => false,
            _ => true,
        };
        let mut line = String::new();
        self.compact(&mut line);
        (all_scalars || line.len() <= INLINE_WIDTH).then_some(line)
    }

    fn pretty(&self, indent: usize, out: &mut String) {
        if let Some(line) = self.inline() {
            out.push_str(&line);
            return;
        }
        let pad = "  ".repeat(indent + 1);
        let close = "  ".repeat(indent);
        match self {
            Json::Arr(items) => {
                out.push_str("[\n");
                for (i, item) in items.iter().enumerate() {
                    out.push_str(&pad);
                    item.pretty(indent + 1, out);
                    out.push_str(if i + 1 < items.len() { ",\n" } else { "\n" });
                }
                out.push_str(&close);
                out.push(']');
            }
            Json::Obj(fields) => {
                out.push_str("{\n");
                for (i, (key, value)) in fields.iter().enumerate() {
                    out.push_str(&pad);
                    write_string(out, key);
                    out.push_str(": ");
                    value.pretty(indent + 1, out);
                    out.push_str(if i + 1 < fields.len() { ",\n" } else { "\n" });
                }
                out.push_str(&close);
                out.push('}');
            }
            _ => unreachable!("scalars are always inline"),
        }
    }

    /// The text of a JSON file holding this value, ending in a newline.
    pub fn to_file_text(&self) -> String {
        let mut out = String::new();
        self.pretty(0, &mut out);
        out.push('\n');
        out
    }
}

fn write_string(out: &mut String, s: &str) {
    assert!(
        s.chars()
            .all(|c| c.is_ascii() && !c.is_ascii_control() && c != '"' && c != '\\'),
        "only plain ASCII strings are written: {s:?}"
    );
    out.push('"');
    out.push_str(s);
    out.push('"');
}
