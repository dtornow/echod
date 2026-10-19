//! The store port against every backend: the in-memory model, the
//! `object_store` crate over memory, and, when `ECHOD_STORE` names one
//! (`s3://bucket`, with `ECHOD_ENDPOINT` for an emulator and credentials in
//! the environment), a real object store.
//!
//! What it checks is what the commit protocol relies on: a conditional
//! create of an existing key is refused, a conditional write on a stale
//! version is refused, a conditional read of the current version is "not
//! modified", listings page and sort. On S3 also: a version is a function of
//! the content, which is why every write of ours carries a nonce.
//!
//! ```shell
//! scripts/s3-tests.sh                                   # the s3s-fs emulator
//! ECHOD_STORE=s3://my-bucket cargo test -p echod-server --test store
//! ```

use std::sync::Arc;

use echod_server::store::{Etag, MemoryStore, ObjectStoreStore, Read, Store, StoreError};

struct Backend {
    name: &'static str,
    store: Arc<dyn Store>,
    /// Versions are content hashes, as on S3.
    content_addressed: bool,
}

async fn backends() -> Vec<Backend> {
    let nonce = format!("{:x}", std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos());
    let mut out = vec![
        Backend { name: "memory", store: Arc::new(MemoryStore::new()), content_addressed: true },
        Backend { name: "object_store memory", store: Arc::new(ObjectStoreStore::new(Arc::new(object_store::memory::InMemory::new()), object_store::path::Path::default())), content_addressed: false },
    ];
    // Not `object_store::local::LocalFileSystem`: it does not implement
    // conditional updates (`PutMode::Update`), so it cannot hold a bucket.
    if let Ok(url) = std::env::var("ECHOD_STORE") {
        let endpoint = std::env::var("ECHOD_ENDPOINT").ok();
        let region = std::env::var("ECHOD_REGION").ok();
        let s = ObjectStoreStore::from_url(&format!("{}/{}", url.trim_end_matches('/'), format!("test-{nonce}")), endpoint.as_deref(), region.as_deref()).unwrap();
        out.push(Backend { name: "object_store url", store: Arc::new(s), content_addressed: url.starts_with("s3") });
    }
    out
}

#[tokio::test]
async fn conditional_writes_are_refused_on_a_stale_version() {
    for b in backends().await {
        let s = &b.store;
        let k = "doc";
        assert_eq!(s.get(k).await.unwrap(), None, "{}", b.name);
        let e1 = s.put_if_none_match(k, b"one".to_vec()).await.unwrap();
        let second = s.put_if_none_match(k, b"two".to_vec()).await;
        assert!(matches!(second, Err(StoreError::PreconditionFailed)), "{}: a second create is refused, got {second:?}", b.name);
        let e2 = s.put_if_match(k, b"two".to_vec(), &e1).await.unwrap();
        assert_ne!(e1, e2, "{}: a new content is a new version", b.name);
        let stale = s.put_if_match(k, b"three".to_vec(), &e1).await;
        assert!(matches!(stale, Err(StoreError::PreconditionFailed)), "{}: a write on the stale version is refused, got {stale:?}", b.name);
        let (body, e) = s.get(k).await.unwrap().unwrap();
        assert_eq!(body, b"two", "{}", b.name);
        assert_eq!(e, e2, "{}", b.name);
        assert!(matches!(s.get_if_none_match(k, &e2).await.unwrap(), Read::NotModified), "{}", b.name);
        match s.get_if_none_match(k, &e1).await.unwrap() {
            Read::Body(bb, e) => {
                assert_eq!(bb, b"two", "{}", b.name);
                assert_eq!(e, e2, "{}", b.name);
            }
            other => panic!("{}: expected the body, got {other:?}", b.name),
        }
        assert!(matches!(s.get_if_none_match("absent", &e1).await.unwrap(), Read::Absent), "{}", b.name);
        let absent = s.put_if_match("absent", b"x".to_vec(), &e1).await;
        assert!(matches!(absent, Err(StoreError::PreconditionFailed)), "{}: a write on an absent key with a version is refused, got {absent:?}", b.name);
        s.delete(k).await.unwrap();
        assert_eq!(s.get(k).await.unwrap(), None, "{}", b.name);
        s.delete(k).await.unwrap();
    }
}

#[tokio::test]
async fn a_version_is_the_content_on_s3() {
    for b in backends().await.into_iter().filter(|b| b.content_addressed) {
        let s = &b.store;
        let ea = s.put_if_none_match("a", b"same".to_vec()).await.unwrap();
        let eb = s.put_if_none_match("b", b"same".to_vec()).await.unwrap();
        assert_eq!(ea, eb, "{}: the same bytes are the same version", b.name);
        let ea2 = s.put_if_match("a", b"same".to_vec(), &ea).await.unwrap();
        assert_eq!(ea2, ea, "{}: rewriting the same bytes does not move the version", b.name);
        let ea3 = s.put_if_match("a", b"same!".to_vec(), &ea).await.unwrap();
        assert_ne!(ea3, ea, "{}", b.name);
        s.delete("a").await.unwrap();
        s.delete("b").await.unwrap();
    }
}

#[tokio::test]
async fn listings_page_and_sort() {
    for b in backends().await {
        let s = &b.store;
        let n = 1_203;
        for i in 0..n {
            s.put(&format!("t/{:05}/{:05}_x%40y~z", i / 100, i), Vec::new()).await.unwrap();
        }
        let keys = s.list("t/", usize::MAX).await.unwrap();
        assert_eq!(keys.len(), n, "{}: every key, across pages", b.name);
        let mut sorted = keys.clone();
        sorted.sort();
        assert_eq!(keys, sorted, "{}: in order", b.name);
        assert_eq!(keys[0], "t/00000/00000_x%40y~z", "{}: keys come back as they were written", b.name);
        let few = s.list("t/", 7).await.unwrap();
        assert_eq!(few, keys[..7].to_vec(), "{}", b.name);
        let prefixes = s.list_prefixes("t/").await.unwrap();
        assert_eq!(prefixes.len(), n.div_ceil(100), "{}: one prefix per bucket of a hundred", b.name);
        assert_eq!(prefixes[0], "t/00000/", "{}", b.name);
        for key in keys {
            s.delete(&key).await.unwrap();
        }
        assert_eq!(s.list("t/", usize::MAX).await.unwrap().len(), 0, "{}", b.name);
    }
}

#[tokio::test]
async fn plain_puts_and_deletes() {
    for b in backends().await {
        let s = &b.store;
        s.put("k", b"1".to_vec()).await.unwrap();
        s.put("k", b"2".to_vec()).await.unwrap();
        assert_eq!(s.get("k").await.unwrap().unwrap().0, b"2", "{}", b.name);
        s.delete("k").await.unwrap();
        s.delete("k").await.unwrap();
        assert_eq!(s.get("k").await.unwrap(), None, "{}", b.name);
        assert!(s.ready().await, "{}", b.name);
        if !s.supports_append() {
            assert!(matches!(s.append_if_match("k", 0, b"x".to_vec(), &Etag("e".into())).await, Err(StoreError::Unavailable(_))), "{}", b.name);
        }
    }
}
