//! fakes3: the S3 surface echod uses, and nothing else, in memory.
//!
//! The two clients echod speaks S3 through, `object_store` for a
//! general-purpose bucket and the AWS SDK for a directory bucket, issue
//! these requests and no others:
//!
//! ```text
//! PUT    /b              create the bucket              200
//! HEAD   /b              is the bucket there            200 | 404
//! GET    /b?list-type=2  ListObjectsV2: prefix, delimiter, max-keys, continuation-token
//! POST   /b?delete       DeleteObjects: every <Key> in the body        200
//! GET    /b/k            the object; If-None-Match      200 | 304 | 404
//! HEAD   /b/k                                           200 | 404
//! PUT    /b/k            write; If-None-Match: *        412 if it exists
//!                               If-Match: "etag"        412 on a mismatch, 404 if absent
//!                               x-amz-write-offset-bytes  append at the current size, else 400
//! DELETE /b/k                                           204, absent or not
//! ```
//!
//! What they rely on and this keeps: a version is the content (the ETag is
//! the MD5, quoted, as S3 gives it); conditions are decided atomically
//! against the object as it is; listings come back in key order and page at
//! a thousand; a key round-trips byte for byte; an append lands only at the
//! object's current size (`InvalidWriteOffset` otherwise, as S3 Express
//! answers); bodies the SDK sends as `aws-chunked` are unframed.
//!
//! Signatures are not checked. Nothing survives the process. Nothing here is
//! fast, and nothing needs to be.
//!
//! ```shell
//! fakes3 --address 127.0.0.1:9000 --bucket echod --bucket echod-express
//! ```

use std::collections::{BTreeMap, HashMap};
use std::sync::{Arc, Mutex};
use std::time::{SystemTime, UNIX_EPOCH};

use axum::body::Bytes;
use axum::extract::{DefaultBodyLimit, State};
use axum::http::{header, HeaderMap, Method, StatusCode, Uri};
use axum::response::{IntoResponse, Response};
use axum::Router;
use clap::Parser;
use md5::{Digest, Md5};

#[derive(Debug, Parser)]
#[command(name = "fakes3", about = "The S3 surface echod uses, in memory", version)]
struct Args {
    /// Where to listen.
    #[arg(long, default_value = "127.0.0.1:9000")]
    address: String,
    /// A bucket to create at startup. Repeatable.
    #[arg(long)]
    bucket: Vec<String>,
    /// Log every request and its status to stderr.
    #[arg(short, long)]
    verbose: bool,
}

struct Object {
    body: Vec<u8>,
    etag: String,
    /// Seconds since the epoch.
    modified: u64,
}

impl Object {
    fn new(body: Vec<u8>) -> Self {
        let etag = etag_of(&body);
        Self { body, etag, modified: now_secs() }
    }
}

/// Keys in order, so a listing is a range.
type Bucket = BTreeMap<String, Object>;

struct Shared {
    buckets: Mutex<HashMap<String, Bucket>>,
    verbose: bool,
}

#[tokio::main]
async fn main() {
    let args = Args::parse();
    let mut buckets = HashMap::new();
    for b in &args.bucket {
        buckets.insert(b.clone(), Bucket::new());
    }
    let shared = Arc::new(Shared { buckets: Mutex::new(buckets), verbose: args.verbose });
    let app = Router::new().fallback(handle).layer(DefaultBodyLimit::disable()).with_state(shared);
    let listener = match tokio::net::TcpListener::bind(&args.address).await {
        Ok(l) => l,
        Err(e) => {
            eprintln!("fakes3: cannot listen on {}: {e}", args.address);
            std::process::exit(1);
        }
    };
    eprintln!("fakes3: serving {} on http://{}", if args.bucket.is_empty() { "no buckets yet".to_string() } else { args.bucket.join(", ") }, args.address);
    axum::serve(listener, app).await.expect("serve");
}

// ---------------------------------------------------------------------------
// Dispatch
// ---------------------------------------------------------------------------

async fn handle(State(st): State<Arc<Shared>>, method: Method, uri: Uri, headers: HeaderMap, body: Bytes) -> Response {
    let resp = route(&st, &method, &uri, &headers, body);
    if st.verbose {
        eprintln!("{} {}{} -> {}", method, uri.path(), uri.query().map(|q| format!("?{q}")).unwrap_or_default(), resp.status().as_u16());
    }
    resp
}

fn route(st: &Shared, method: &Method, uri: &Uri, headers: &HeaderMap, body: Bytes) -> Response {
    let path = uri.path().trim_start_matches('/');
    let (bucket, key) = match path.split_once('/') {
        Some((b, k)) => (b, Some(percent_decode(k))),
        None if path.is_empty() => return service(method),
        None => (path, None),
    };
    let query = parse_query(uri.query().unwrap_or(""));
    let mut buckets = st.buckets.lock().unwrap_or_else(|e| e.into_inner());
    match key {
        None => bucket_op(&mut buckets, method, bucket, &query, body),
        Some(key) if key.is_empty() => bucket_op(&mut buckets, method, bucket, &query, body),
        Some(key) => {
            let Some(b) = buckets.get_mut(bucket) else {
                return error(StatusCode::NOT_FOUND, "NoSuchBucket", "The specified bucket does not exist");
            };
            object_op(b, method, &key, headers, body)
        }
    }
}

fn service(method: &Method) -> Response {
    match *method {
        Method::GET => xml(StatusCode::OK, "<ListAllMyBucketsResult xmlns=\"http://s3.amazonaws.com/doc/2006-03-01/\"><Buckets></Buckets></ListAllMyBucketsResult>".to_string()),
        _ => error(StatusCode::METHOD_NOT_ALLOWED, "MethodNotAllowed", "The specified method is not allowed against this resource"),
    }
}

fn bucket_op(buckets: &mut HashMap<String, Bucket>, method: &Method, name: &str, query: &[(String, String)], body: Bytes) -> Response {
    match *method {
        Method::POST if query.iter().any(|(k, _)| k == "delete") => match buckets.get_mut(name) {
            Some(b) => delete_objects(b, &body),
            None => error(StatusCode::NOT_FOUND, "NoSuchBucket", "The specified bucket does not exist"),
        },
        Method::PUT => {
            buckets.entry(name.to_string()).or_default();
            StatusCode::OK.into_response()
        }
        Method::HEAD => {
            if buckets.contains_key(name) {
                StatusCode::OK.into_response()
            } else {
                StatusCode::NOT_FOUND.into_response()
            }
        }
        Method::DELETE => {
            buckets.remove(name);
            StatusCode::NO_CONTENT.into_response()
        }
        Method::GET => match buckets.get(name) {
            Some(b) => list(b, name, query),
            None => error(StatusCode::NOT_FOUND, "NoSuchBucket", "The specified bucket does not exist"),
        },
        _ => error(StatusCode::METHOD_NOT_ALLOWED, "MethodNotAllowed", "The specified method is not allowed against this resource"),
    }
}

// ---------------------------------------------------------------------------
// Objects
// ---------------------------------------------------------------------------

fn object_op(b: &mut Bucket, method: &Method, key: &str, headers: &HeaderMap, body: Bytes) -> Response {
    match *method {
        Method::GET | Method::HEAD => {
            let Some(o) = b.get(key) else {
                return error(StatusCode::NOT_FOUND, "NoSuchKey", "The specified key does not exist.");
            };
            if let Some(v) = header_str(headers, header::IF_NONE_MATCH) {
                if etag_matches(v, &o.etag) {
                    return with_object_headers(StatusCode::NOT_MODIFIED, o, Vec::new());
                }
            }
            let body = if *method == Method::GET { o.body.clone() } else { Vec::new() };
            with_object_headers(StatusCode::OK, o, body)
        }
        Method::DELETE => {
            b.remove(key);
            StatusCode::NO_CONTENT.into_response()
        }
        Method::PUT => {
            let body = match unframe(headers, body) {
                Ok(v) => v,
                Err(m) => return error(StatusCode::BAD_REQUEST, "IncompleteBody", &m),
            };
            match header_str(headers, "x-amz-write-offset-bytes") {
                Some(off) => append(b, key, headers, off, body),
                None => put(b, key, headers, body),
            }
        }
        _ => error(StatusCode::METHOD_NOT_ALLOWED, "MethodNotAllowed", "The specified method is not allowed against this resource"),
    }
}

/// A write, under its conditions, decided against the object as it is now.
fn put(b: &mut Bucket, key: &str, headers: &HeaderMap, body: Vec<u8>) -> Response {
    let current = b.get(key);
    if let Some(v) = header_str(headers, header::IF_NONE_MATCH) {
        if let Some(o) = current {
            if etag_matches(v, &o.etag) {
                return error(StatusCode::PRECONDITION_FAILED, "PreconditionFailed", "At least one of the pre-conditions you specified did not hold");
            }
        }
    }
    if let Some(v) = header_str(headers, header::IF_MATCH) {
        match current {
            // S3 answers 404, not 412, for a condition on nothing.
            None => return error(StatusCode::NOT_FOUND, "NoSuchKey", "The specified key does not exist."),
            Some(o) if !etag_matches(v, &o.etag) => {
                return error(StatusCode::PRECONDITION_FAILED, "PreconditionFailed", "At least one of the pre-conditions you specified did not hold");
            }
            Some(_) => {}
        }
    }
    let o = Object::new(body);
    let etag = o.etag.clone();
    b.insert(key.to_string(), o);
    ([(header::ETAG, etag)], StatusCode::OK).into_response()
}

/// An S3 Express append: at the current size, under `If-Match` if given.
/// With no object there, an offset of zero creates it, as S3 Express does.
fn append(b: &mut Bucket, key: &str, headers: &HeaderMap, offset: &str, body: Vec<u8>) -> Response {
    let Ok(offset) = offset.trim().parse::<u64>() else {
        return error(StatusCode::BAD_REQUEST, "InvalidArgument", "x-amz-write-offset-bytes must be a non-negative integer");
    };
    let if_match = header_str(headers, header::IF_MATCH);
    match b.get_mut(key) {
        None => {
            if if_match.is_some() || offset != 0 {
                return error(StatusCode::NOT_FOUND, "NoSuchKey", "The specified key does not exist.");
            }
            put(b, key, headers, body)
        }
        Some(o) => {
            if let Some(v) = if_match {
                if !etag_matches(v, &o.etag) {
                    return error(StatusCode::PRECONDITION_FAILED, "PreconditionFailed", "At least one of the pre-conditions you specified did not hold");
                }
            }
            if offset != o.body.len() as u64 {
                return error(StatusCode::BAD_REQUEST, "InvalidWriteOffset", "The write offset value that you specified does not match the current object size.");
            }
            o.body.extend_from_slice(&body);
            o.etag = etag_of(&o.body);
            o.modified = now_secs();
            ([(header::ETAG, o.etag.clone()), (header::HeaderName::from_static("x-amz-object-size"), o.body.len().to_string())], StatusCode::OK).into_response()
        }
    }
}

/// DeleteObjects, which `object_store` uses for every delete: each `<Key>`
/// in the body goes, present or not, and each is reported deleted.
fn delete_objects(b: &mut Bucket, body: &[u8]) -> Response {
    let text = String::from_utf8_lossy(body);
    let mut out = String::from("<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n<DeleteResult xmlns=\"http://s3.amazonaws.com/doc/2006-03-01/\">");
    let mut rest = text.as_ref();
    while let Some(start) = rest.find("<Key>") {
        let after = &rest[start + "<Key>".len()..];
        let Some(end) = after.find("</Key>") else { break };
        let key = unesc(&after[..end]);
        b.remove(&key);
        out.push_str(&format!("<Deleted><Key>{}</Key></Deleted>", esc(&key)));
        rest = &after[end + "</Key>".len()..];
    }
    out.push_str("</DeleteResult>");
    xml(StatusCode::OK, out)
}

fn with_object_headers(status: StatusCode, o: &Object, body: Vec<u8>) -> Response {
    let mut r = (status, body).into_response();
    let h = r.headers_mut();
    h.insert(header::ETAG, o.etag.parse().expect("etag"));
    h.insert(header::LAST_MODIFIED, http_date(o.modified).parse().expect("date"));
    h.insert(header::CONTENT_LENGTH, o.body.len().to_string().parse().expect("len"));
    h.insert(header::CONTENT_TYPE, "application/octet-stream".parse().expect("type"));
    h.insert(header::ACCEPT_RANGES, "bytes".parse().expect("ranges"));
    r
}

// ---------------------------------------------------------------------------
// Listing
// ---------------------------------------------------------------------------

/// Where a listing resumes: after a key, or past everything under a common
/// prefix. Carried to the client as the continuation token.
enum After {
    Key(String),
    Prefix(String),
}

impl After {
    fn token(&self) -> String {
        match self {
            After::Key(k) => format!("k:{k}"),
            After::Prefix(p) => format!("p:{p}"),
        }
    }
    fn parse(t: &str) -> Option<Self> {
        t.strip_prefix("k:").map(|k| After::Key(k.to_string())).or_else(|| t.strip_prefix("p:").map(|p| After::Prefix(p.to_string())))
    }
    fn skips(&self, key: &str) -> bool {
        match self {
            After::Key(k) => key <= k.as_str(),
            After::Prefix(p) => key.starts_with(p.as_str()) || key <= p.as_str(),
        }
    }
}

enum Entry<'a> {
    Key(&'a str, &'a Object),
    Prefix(String),
}

/// ListObjectsV2: keys under `prefix` in order, rolled up at `delimiter`,
/// at most `max-keys` of them, resuming after `continuation-token` or
/// `start-after`.
fn list(b: &Bucket, name: &str, query: &[(String, String)]) -> Response {
    let q = |k: &str| query.iter().find(|(a, _)| a == k).map(|(_, v)| v.as_str());
    let prefix = q("prefix").unwrap_or("");
    let delimiter = q("delimiter").filter(|d| !d.is_empty());
    let max_keys = q("max-keys").and_then(|m| m.parse::<usize>().ok()).unwrap_or(1000).min(1000);
    let after = match (q("continuation-token"), q("start-after")) {
        (Some(t), _) => match After::parse(t) {
            Some(a) => Some(a),
            None => return error(StatusCode::BAD_REQUEST, "InvalidArgument", "The continuation token provided is incorrect"),
        },
        (None, Some(s)) => Some(After::Key(s.to_string())),
        (None, None) => None,
    };

    let mut entries: Vec<Entry> = Vec::new();
    let mut truncated = false;
    let mut last_prefix: Option<String> = None;
    for (k, o) in b.range(prefix.to_string()..) {
        if !k.starts_with(prefix) {
            break;
        }
        if after.as_ref().is_some_and(|a| a.skips(k)) {
            continue;
        }
        let entry = match delimiter.and_then(|d| k[prefix.len()..].find(d).map(|i| (d, i))) {
            Some((d, i)) => Entry::Prefix(k[..prefix.len() + i + d.len()].to_string()),
            None => Entry::Key(k, o),
        };
        if let Entry::Prefix(p) = &entry {
            if last_prefix.as_deref() == Some(p.as_str()) {
                continue;
            }
        }
        if entries.len() == max_keys {
            truncated = true;
            break;
        }
        if let Entry::Prefix(p) = &entry {
            last_prefix = Some(p.clone());
        }
        entries.push(entry);
    }

    let mut out = String::new();
    out.push_str("<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n<ListBucketResult xmlns=\"http://s3.amazonaws.com/doc/2006-03-01/\">");
    out.push_str(&format!("<Name>{}</Name><Prefix>{}</Prefix><KeyCount>{}</KeyCount><MaxKeys>{}</MaxKeys>", esc(name), esc(prefix), entries.len(), max_keys));
    if let Some(d) = delimiter {
        out.push_str(&format!("<Delimiter>{}</Delimiter>", esc(d)));
    }
    out.push_str(&format!("<IsTruncated>{truncated}</IsTruncated>"));
    if truncated {
        let next = match entries.last() {
            Some(Entry::Key(k, _)) => After::Key(k.to_string()),
            Some(Entry::Prefix(p)) => After::Prefix(p.clone()),
            None => unreachable!("truncated with nothing listed"),
        };
        out.push_str(&format!("<NextContinuationToken>{}</NextContinuationToken>", esc(&next.token())));
    }
    for e in &entries {
        match e {
            Entry::Key(k, o) => out.push_str(&format!(
                "<Contents><Key>{}</Key><LastModified>{}</LastModified><ETag>{}</ETag><Size>{}</Size><StorageClass>STANDARD</StorageClass></Contents>",
                esc(k),
                iso_date(o.modified),
                esc(&o.etag),
                o.body.len()
            )),
            Entry::Prefix(p) => out.push_str(&format!("<CommonPrefixes><Prefix>{}</Prefix></CommonPrefixes>", esc(p))),
        }
    }
    out.push_str("</ListBucketResult>");
    xml(StatusCode::OK, out)
}

// ---------------------------------------------------------------------------
// The wire
// ---------------------------------------------------------------------------

fn header_str<K: header::AsHeaderName>(headers: &HeaderMap, k: K) -> Option<&str> {
    headers.get(k).and_then(|v| v.to_str().ok())
}

/// The quoted MD5 of the content, as S3 computes an ETag for a single put.
fn etag_of(body: &[u8]) -> String {
    let hex: String = Md5::digest(body).iter().map(|b| format!("{b:02x}")).collect();
    format!("\"{hex}\"")
}

/// Does a condition's value name this version? `*` names any. Quotes and a
/// weak marker are not part of the version.
fn etag_matches(condition: &str, etag: &str) -> bool {
    let bare = |s: &str| s.trim().trim_start_matches("W/").trim_matches('"').to_string();
    let mine = bare(etag);
    condition.split(',').any(|c| {
        let c = c.trim();
        c == "*" || bare(c) == mine
    })
}

/// The body as bytes: unframed if the SDK sent it `aws-chunked`, which it
/// does when it signs a checksum in a trailer.
fn unframe(headers: &HeaderMap, body: Bytes) -> Result<Vec<u8>, String> {
    let chunked = header_str(headers, header::CONTENT_ENCODING).is_some_and(|e| e.split(',').any(|p| p.trim() == "aws-chunked"))
        || header_str(headers, "x-amz-content-sha256").is_some_and(|s| s.starts_with("STREAMING-"));
    if !chunked {
        return Ok(body.to_vec());
    }
    let b = &body[..];
    let mut out = Vec::with_capacity(b.len());
    let mut i = 0;
    loop {
        let Some(nl) = find(&b[i..], b"\r\n") else { return Err("aws-chunked: chunk header without CRLF".into()) };
        let line = std::str::from_utf8(&b[i..i + nl]).map_err(|_| "aws-chunked: chunk header is not text")?;
        let size = usize::from_str_radix(line.split(';').next().unwrap_or("").trim(), 16).map_err(|_| format!("aws-chunked: bad chunk size {line:?}"))?;
        i += nl + 2;
        if size == 0 {
            // Trailers follow, then a blank line; nothing in them is needed.
            return Ok(out);
        }
        if i + size > b.len() {
            return Err("aws-chunked: chunk shorter than its size".into());
        }
        out.extend_from_slice(&b[i..i + size]);
        i += size;
        if b.get(i..i + 2) != Some(b"\r\n") {
            return Err("aws-chunked: chunk without trailing CRLF".into());
        }
        i += 2;
    }
}

fn find(hay: &[u8], needle: &[u8]) -> Option<usize> {
    hay.windows(needle.len()).position(|w| w == needle)
}

/// `%XX` undone once, exactly as the client did it; `+` is a plus.
fn percent_decode(s: &str) -> String {
    let b = s.as_bytes();
    let mut out = Vec::with_capacity(b.len());
    let mut i = 0;
    while i < b.len() {
        if b[i] == b'%' && i + 2 < b.len() {
            if let Some(v) = std::str::from_utf8(&b[i + 1..i + 3]).ok().and_then(|h| u8::from_str_radix(h, 16).ok()) {
                out.push(v);
                i += 3;
                continue;
            }
        }
        out.push(b[i]);
        i += 1;
    }
    String::from_utf8_lossy(&out).into_owned()
}

fn parse_query(q: &str) -> Vec<(String, String)> {
    q.split('&')
        .filter(|p| !p.is_empty())
        .map(|p| {
            let (k, v) = p.split_once('=').unwrap_or((p, ""));
            (percent_decode(k), percent_decode(v))
        })
        .collect()
}

fn esc(s: &str) -> String {
    s.replace('&', "&amp;").replace('<', "&lt;").replace('>', "&gt;").replace('"', "&quot;")
}

fn unesc(s: &str) -> String {
    s.replace("&lt;", "<").replace("&gt;", ">").replace("&quot;", "\"").replace("&apos;", "'").replace("&amp;", "&")
}

fn xml(status: StatusCode, body: String) -> Response {
    (status, [(header::CONTENT_TYPE, "application/xml")], body).into_response()
}

fn error(status: StatusCode, code: &str, message: &str) -> Response {
    xml(status, format!("<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n<Error><Code>{}</Code><Message>{}</Message></Error>", esc(code), esc(message)))
}

// ---------------------------------------------------------------------------
// Dates, without a calendar crate
// ---------------------------------------------------------------------------

fn now_secs() -> u64 {
    SystemTime::now().duration_since(UNIX_EPOCH).map(|d| d.as_secs()).unwrap_or(0)
}

/// Civil date from days since the epoch (Howard Hinnant's algorithm).
fn civil(days: i64) -> (i64, u32, u32) {
    let z = days + 719_468;
    let era = z.div_euclid(146_097);
    let doe = z.rem_euclid(146_097);
    let yoe = (doe - doe / 1460 + doe / 36_524 - doe / 146_096) / 365;
    let y = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = (doy - (153 * mp + 2) / 5 + 1) as u32;
    let m = if mp < 10 { mp + 3 } else { mp - 9 } as u32;
    (if m <= 2 { y + 1 } else { y }, m, d)
}

fn split(secs: u64) -> ((i64, u32, u32), u32, u32, u32, usize) {
    let days = (secs / 86_400) as i64;
    let rem = secs % 86_400;
    let weekday = ((days + 4).rem_euclid(7)) as usize;
    (civil(days), (rem / 3600) as u32, (rem % 3600 / 60) as u32, (rem % 60) as u32, weekday)
}

const MONTHS: [&str; 12] = ["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"];
const DAYS: [&str; 7] = ["Sun", "Mon", "Tue", "Wed", "Thu", "Fri", "Sat"];

/// `2026-11-03T10:00:00.000Z`, as a listing carries it.
fn iso_date(secs: u64) -> String {
    let ((y, m, d), hh, mm, ss, _) = split(secs);
    format!("{y:04}-{m:02}-{d:02}T{hh:02}:{mm:02}:{ss:02}.000Z")
}

/// `Tue, 03 Nov 2026 10:00:00 GMT`, as a header carries it.
fn http_date(secs: u64) -> String {
    let ((y, m, d), hh, mm, ss, wd) = split(secs);
    format!("{}, {d:02} {} {y:04} {hh:02}:{mm:02}:{ss:02} GMT", DAYS[wd], MONTHS[(m - 1) as usize])
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn etags_match_bare_quoted_weak_and_star() {
        assert!(etag_matches("\"abc\"", "\"abc\""));
        assert!(etag_matches("abc", "\"abc\""));
        assert!(etag_matches("W/\"abc\"", "\"abc\""));
        assert!(etag_matches("*", "\"abc\""));
        assert!(etag_matches("\"x\", \"abc\"", "\"abc\""));
        assert!(!etag_matches("\"abd\"", "\"abc\""));
    }

    #[test]
    fn a_key_is_decoded_once_and_plus_stays() {
        assert_eq!(percent_decode("t/00000/00000_x%2540y~z"), "t/00000/00000_x%40y~z");
        assert_eq!(percent_decode("a+b%20c"), "a+b c");
        assert_eq!(percent_decode("%zz%"), "%zz%");
    }

    #[test]
    fn aws_chunked_is_unframed() {
        let mut h = HeaderMap::new();
        h.insert(header::CONTENT_ENCODING, "aws-chunked".parse().unwrap());
        let framed = b"3;chunk-signature=deadbeef\r\nabc\r\n2\r\nde\r\n0;chunk-signature=00\r\nx-amz-checksum-crc32:AAAA\r\n\r\n";
        assert_eq!(unframe(&h, Bytes::from_static(framed)).unwrap(), b"abcde");
        let plain = HeaderMap::new();
        assert_eq!(unframe(&plain, Bytes::from_static(b"raw")).unwrap(), b"raw");
    }

    #[test]
    fn dates_render_as_s3_does() {
        // 2026-11-03T10:00:00Z, a Tuesday.
        let t = 1_793_700_000;
        assert_eq!(iso_date(t), "2026-11-03T10:00:00.000Z");
        assert_eq!(http_date(t), "Tue, 03 Nov 2026 10:00:00 GMT");
        assert_eq!(iso_date(0), "1970-01-01T00:00:00.000Z");
        assert_eq!(http_date(0), "Thu, 01 Jan 1970 00:00:00 GMT");
    }

    fn bucket_with(keys: &[&str]) -> Bucket {
        keys.iter().map(|k| (k.to_string(), Object::new(Vec::new()))).collect()
    }

    fn listed(b: &Bucket, query: &[(&str, &str)]) -> String {
        let q: Vec<(String, String)> = query.iter().map(|(k, v)| (k.to_string(), v.to_string())).collect();
        let r = list(b, "b", &q);
        assert_eq!(r.status(), StatusCode::OK);
        let bytes = futures_body(r);
        String::from_utf8(bytes).unwrap()
    }

    fn futures_body(r: Response) -> Vec<u8> {
        let rt = tokio::runtime::Builder::new_current_thread().build().unwrap();
        rt.block_on(async { axum::body::to_bytes(r.into_body(), usize::MAX).await.unwrap().to_vec() })
    }

    #[test]
    fn listings_page_in_order_and_roll_up_at_the_delimiter() {
        let b = bucket_with(&["t/0/a", "t/0/b", "t/1/a", "u"]);
        let x = listed(&b, &[("list-type", "2"), ("prefix", "t/"), ("max-keys", "2")]);
        assert!(x.contains("<IsTruncated>true</IsTruncated>"), "{x}");
        assert!(x.contains("<NextContinuationToken>k:t/0/b</NextContinuationToken>"), "{x}");
        let y = listed(&b, &[("list-type", "2"), ("prefix", "t/"), ("continuation-token", "k:t/0/b")]);
        assert!(y.contains("<Key>t/1/a</Key>") && !y.contains("<Key>t/0/"), "{y}");
        assert!(y.contains("<IsTruncated>false</IsTruncated>"), "{y}");
        let d = listed(&b, &[("list-type", "2"), ("prefix", "t/"), ("delimiter", "/")]);
        assert!(d.contains("<CommonPrefixes><Prefix>t/0/</Prefix></CommonPrefixes><CommonPrefixes><Prefix>t/1/</Prefix></CommonPrefixes>"), "{d}");
        assert!(!d.contains("<Contents>"), "{d}");
        let p = listed(&b, &[("list-type", "2"), ("prefix", "t/"), ("delimiter", "/"), ("max-keys", "1")]);
        assert!(p.contains("<NextContinuationToken>p:t/0/</NextContinuationToken>"), "{p}");
        let p2 = listed(&b, &[("list-type", "2"), ("prefix", "t/"), ("delimiter", "/"), ("continuation-token", "p:t/0/")]);
        assert!(p2.contains("<Prefix>t/1/</Prefix>") && !p2.contains("<Prefix>t/0/</Prefix>"), "{p2}");
    }

    #[test]
    fn a_batch_delete_removes_every_key_named() {
        let mut b = bucket_with(&["a", "b&c", "d"]);
        let body = b"<Delete xmlns=\"http://s3.amazonaws.com/doc/2006-03-01/\"><Object><Key>a</Key></Object><Object><Key>b&amp;c</Key></Object><Object><Key>nope</Key></Object></Delete>";
        let r = delete_objects(&mut b, body);
        assert_eq!(r.status(), StatusCode::OK);
        let x = String::from_utf8(futures_body(r)).unwrap();
        assert!(x.contains("<Deleted><Key>a</Key></Deleted><Deleted><Key>b&amp;c</Key></Deleted><Deleted><Key>nope</Key></Deleted>"), "{x}");
        assert_eq!(b.keys().collect::<Vec<_>>(), vec!["d"]);
    }

    #[test]
    fn conditions_and_appends_are_decided_against_the_object() {
        let mut b = Bucket::new();
        let h = |pairs: &[(&'static str, &str)]| {
            let mut h = HeaderMap::new();
            for (k, v) in pairs {
                h.insert(*k, v.parse().unwrap());
            }
            h
        };
        let first = put(&mut b, "k", &h(&[("if-none-match", "*")]), b"one".to_vec());
        assert_eq!(first.status(), StatusCode::OK);
        let e1 = first.headers().get(header::ETAG).unwrap().to_str().unwrap().to_string();
        assert_eq!(e1, etag_of(b"one"));
        assert_eq!(put(&mut b, "k", &h(&[("if-none-match", "*")]), b"two".to_vec()).status(), StatusCode::PRECONDITION_FAILED);
        assert_eq!(put(&mut b, "k", &h(&[("if-match", "\"nope\"")]), b"two".to_vec()).status(), StatusCode::PRECONDITION_FAILED);
        assert_eq!(put(&mut b, "absent", &h(&[("if-match", &e1)]), b"x".to_vec()).status(), StatusCode::NOT_FOUND);
        assert_eq!(put(&mut b, "k", &h(&[("if-match", &e1)]), b"two".to_vec()).status(), StatusCode::OK);
        let e2 = b["k"].etag.clone();
        assert_ne!(e1, e2);
        // Appends: the right offset under the right version only.
        assert_eq!(append(&mut b, "k", &h(&[("if-match", &e1)]), "3", b"!".to_vec()).status(), StatusCode::PRECONDITION_FAILED);
        assert_eq!(append(&mut b, "k", &h(&[("if-match", &e2)]), "2", b"!".to_vec()).status(), StatusCode::BAD_REQUEST);
        let a = append(&mut b, "k", &h(&[("if-match", &e2)]), "3", b"!".to_vec());
        assert_eq!(a.status(), StatusCode::OK);
        assert_eq!(a.headers().get("x-amz-object-size").unwrap(), "4");
        assert_eq!(b["k"].body, b"two!");
        assert_eq!(append(&mut b, "absent", &h(&[("if-match", &e2)]), "0", b"x".to_vec()).status(), StatusCode::NOT_FOUND);
        assert_eq!(append(&mut b, "fresh", &h(&[]), "0", b"x".to_vec()).status(), StatusCode::OK);
        assert_eq!(append(&mut b, "fresh2", &h(&[]), "5", b"x".to_vec()).status(), StatusCode::NOT_FOUND);
    }
}
