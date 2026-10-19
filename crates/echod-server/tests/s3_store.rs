//! The S3 store against a real S3 API: an emulator or a bucket.
//!
//! Runs only when `ECHOD_S3_ENDPOINT` (or, for a real bucket, just
//! `ECHOD_S3_BUCKET`) is set; otherwise every test here passes vacuously.
//! What it checks is what the commit protocol relies on: a conditional
//! create of an existing key is refused, a conditional write on a stale
//! version is refused, a conditional read of the current version is "not
//! modified", listings page and sort, and a version is a function of the
//! content.
//!
//! ```shell
//! s3s-fs --host 127.0.0.1 --port 8014 --access-key k --secret-key s /tmp/s3root   # mkdir /tmp/s3root/echod
//! AWS_ACCESS_KEY_ID=k AWS_SECRET_ACCESS_KEY=s ECHOD_S3_ENDPOINT=http://127.0.0.1:8014 ECHOD_S3_BUCKET=echod cargo test -p echod-server --test s3_store
//! ```

use std::sync::Arc;

use echod_server::store::{Etag, Read, S3Store, Store, StoreError};

async fn open() -> Option<(Arc<dyn Store>, String)> {
    let bucket = std::env::var("ECHOD_S3_BUCKET").ok()?;
    let endpoint = std::env::var("ECHOD_S3_ENDPOINT").ok();
    let region = std::env::var("ECHOD_S3_REGION").ok().or_else(|| Some("us-east-1".to_string()));
    let store = S3Store::open(&bucket, region.as_deref(), endpoint.as_deref(), false).await;
    let nonce = format!("{:x}", std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos());
    Some((Arc::new(store), format!("test/{nonce}/")))
}

#[tokio::test]
async fn conditional_writes_are_refused_on_a_stale_version() {
    let Some((s, p)) = open().await else { return };
    let k = format!("{p}doc");
    assert_eq!(s.get(&k).await.unwrap(), None);
    let e1 = s.put_if_none_match(&k, b"one".to_vec()).await.unwrap();
    let second = s.put_if_none_match(&k, b"two".to_vec()).await;
    assert!(matches!(second, Err(StoreError::PreconditionFailed)), "a second create is refused, got {second:?}");
    let e2 = s.put_if_match(&k, b"two".to_vec(), &e1).await.unwrap();
    assert_ne!(e1, e2, "a new content is a new version");
    assert!(matches!(s.put_if_match(&k, b"three".to_vec(), &e1).await, Err(StoreError::PreconditionFailed)), "a write on the stale version is refused");
    let (body, e) = s.get(&k).await.unwrap().unwrap();
    assert_eq!(body, b"two");
    assert_eq!(e, e2);
    // S3 answers 304 here. s3s-fs 0.17 ignores If-None-Match on GET and sends
    // the body; the store treats both as a revalidation that found the
    // version current, at the cost of the body.
    match s.get_if_none_match(&k, &e2).await.unwrap() {
        Read::NotModified => {}
        Read::Body(b, e) => {
            eprintln!("note: this S3 does not honour If-None-Match on GET; the body came back");
            assert_eq!(b, b"two");
            assert_eq!(e, e2);
        }
        Read::Absent => panic!("the key exists"),
    }
    match s.get_if_none_match(&k, &e1).await.unwrap() {
        Read::Body(b, e) => {
            assert_eq!(b, b"two");
            assert_eq!(e, e2);
        }
        other => panic!("expected the body, got {other:?}"),
    }
    assert!(matches!(s.get_if_none_match(&format!("{p}absent"), &e1).await.unwrap(), Read::Absent));
    assert!(matches!(s.put_if_match(&format!("{p}absent"), b"x".to_vec(), &e1).await, Err(StoreError::PreconditionFailed)), "a write on an absent key with a version is refused");
    s.delete(&k).await.unwrap();
    assert_eq!(s.get(&k).await.unwrap(), None);
    s.delete(&k).await.unwrap_or(());
}

#[tokio::test]
async fn a_version_is_the_content() {
    let Some((s, p)) = open().await else { return };
    let a = format!("{p}a");
    let b = format!("{p}b");
    let ea = s.put_if_none_match(&a, b"same".to_vec()).await.unwrap();
    let eb = s.put_if_none_match(&b, b"same".to_vec()).await.unwrap();
    assert_eq!(ea, eb, "S3 versions are content hashes: the same bytes are the same version, which is why every write of ours carries a nonce");
    let ea2 = s.put_if_match(&a, b"same".to_vec(), &ea).await.unwrap();
    assert_eq!(ea2, ea, "rewriting the same bytes does not move the version");
    let ea3 = s.put_if_match(&a, b"same!".to_vec(), &ea).await.unwrap();
    assert_ne!(ea3, ea);
    s.delete(&a).await.unwrap();
    s.delete(&b).await.unwrap();
}

#[tokio::test]
async fn listings_page_and_sort() {
    let Some((s, p)) = open().await else { return };
    let n = 1_203;
    for i in 0..n {
        s.put(&format!("{p}t/{:05}/{:05}_x", i / 100, i), Vec::new()).await.unwrap();
    }
    let keys = s.list(&format!("{p}t/"), usize::MAX).await.unwrap();
    assert_eq!(keys.len(), n, "every key, across pages");
    let mut sorted = keys.clone();
    sorted.sort();
    assert_eq!(keys, sorted, "in order");
    let few = s.list(&format!("{p}t/"), 7).await.unwrap();
    assert_eq!(few.len(), 7);
    assert_eq!(few, keys[..7].to_vec());
    let prefixes = s.list_prefixes(&format!("{p}t/")).await.unwrap();
    assert_eq!(prefixes.len(), n.div_ceil(100), "one prefix per bucket of a hundred");
    assert_eq!(prefixes[0], format!("{p}t/00000/"));
    for key in keys {
        s.delete(&key).await.unwrap();
    }
    assert_eq!(s.list(&format!("{p}t/"), usize::MAX).await.unwrap().len(), 0);
}

#[tokio::test]
async fn plain_puts_and_deletes() {
    let Some((s, p)) = open().await else { return };
    let k = format!("{p}k");
    s.put(&k, b"1".to_vec()).await.unwrap();
    s.put(&k, b"2".to_vec()).await.unwrap();
    assert_eq!(s.get(&k).await.unwrap().unwrap().0, b"2");
    s.delete(&k).await.unwrap();
    s.delete(&k).await.unwrap_or(());
    assert_eq!(s.get(&k).await.unwrap(), None);
    assert!(s.ready().await);
    assert!(!s.supports_append());
    assert!(matches!(s.append_if_match(&k, 0, b"x".to_vec(), &Etag("e".into())).await, Err(StoreError::Unavailable(_))));
}
