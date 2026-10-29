//! Canonical primitive framing.
//!
//! Integers are fixed-width big endian. Booleans and options use a single
//! `0`/`1` tag. Sequences and UTF-8 text are prefixed by an eight-byte element
//! or byte count. Decoders reject every other representation.

use vstd::prelude::*;

verus! {

/// A defensive recursion bound for sequence decoding.
pub const MAX_SEQUENCE_ITEMS: u64 = 4096;

pub open spec fn u64_bytes(v: u64) -> Seq<u8> {
    seq![
        ((v >> 56) & 0xff) as u8,
        ((v >> 48) & 0xff) as u8,
        ((v >> 40) & 0xff) as u8,
        ((v >> 32) & 0xff) as u8,
        ((v >> 24) & 0xff) as u8,
        ((v >> 16) & 0xff) as u8,
        ((v >> 8) & 0xff) as u8,
        (v & 0xff) as u8,
    ]
}

pub fn encode_u64(v: u64) -> (out: Vec<u8>)
    ensures out@ == u64_bytes(v),
{
    let mut out = Vec::new();
    out.push(((v >> 56) & 0xff) as u8);
    out.push(((v >> 48) & 0xff) as u8);
    out.push(((v >> 40) & 0xff) as u8);
    out.push(((v >> 32) & 0xff) as u8);
    out.push(((v >> 24) & 0xff) as u8);
    out.push(((v >> 16) & 0xff) as u8);
    out.push(((v >> 8) & 0xff) as u8);
    out.push((v & 0xff) as u8);
    out
}

#[verifier::bit_vector]
proof fn lemma_u64_from_bytes(v: u64)
    ensures
        ((u64_bytes(v)[0] as u64) << 56)
            | ((u64_bytes(v)[1] as u64) << 48)
            | ((u64_bytes(v)[2] as u64) << 40)
            | ((u64_bytes(v)[3] as u64) << 32)
            | ((u64_bytes(v)[4] as u64) << 24)
            | ((u64_bytes(v)[5] as u64) << 16)
            | ((u64_bytes(v)[6] as u64) << 8)
            | u64_bytes(v)[7] as u64 == v,
{
}

pub fn decode_u64(bytes: &Vec<u8>) -> (r: Option<u64>)
    ensures
        r == decode_u64_spec(bytes@),
{
    if bytes.len() != 8 {
        None
    } else {
        let v = ((bytes[0] as u64) << 56)
            | ((bytes[1] as u64) << 48)
            | ((bytes[2] as u64) << 40)
            | ((bytes[3] as u64) << 32)
            | ((bytes[4] as u64) << 24)
            | ((bytes[5] as u64) << 16)
            | ((bytes[6] as u64) << 8)
            | bytes[7] as u64;
        proof {
            assert(bytes@.len() == 8);
        }
        Some(v)
    }
}

pub proof fn lemma_u64_round_trip(v: u64)
    ensures decode_u64_spec(u64_bytes(v)) == Some(v),
{
    lemma_u64_from_bytes(v);
}

pub open spec fn decode_u64_spec(bytes: Seq<u8>) -> Option<u64> {
    if bytes.len() != 8 {
        None
    } else {
        Some(((bytes[0] as u64) << 56)
            | ((bytes[1] as u64) << 48)
            | ((bytes[2] as u64) << 40)
            | ((bytes[3] as u64) << 32)
            | ((bytes[4] as u64) << 24)
            | ((bytes[5] as u64) << 16)
            | ((bytes[6] as u64) << 8)
            | bytes[7] as u64)
    }
}

pub open spec fn bool_bytes(v: bool) -> Seq<u8> {
    if v { seq![1u8] } else { seq![0u8] }
}

pub fn encode_bool(v: bool) -> (out: Vec<u8>)
    ensures out@ == bool_bytes(v),
{
    let mut out = Vec::new();
    out.push(if v { 1 } else { 0 });
    out
}

pub fn decode_bool(bytes: &Vec<u8>) -> (r: Option<bool>)
    ensures
        r == decode_bool_spec(bytes@),
{
    if bytes.len() != 1 {
        None
    } else if bytes[0] == 0 {
        Some(false)
    } else if bytes[0] == 1 {
        Some(true)
    } else {
        None
    }
}

pub proof fn lemma_bool_round_trip(v: bool)
    ensures decode_bool_spec(bool_bytes(v)) == Some(v),
{
    if v {
        assert(bool_bytes(v) == seq![1u8]);
    } else {
        assert(bool_bytes(v) == seq![0u8]);
    }
}

pub open spec fn decode_bool_spec(bytes: Seq<u8>) -> Option<bool> {
    if bytes.len() != 1 {
        None
    } else if bytes[0] == 0 {
        Some(false)
    } else if bytes[0] == 1 {
        Some(true)
    } else {
        None
    }
}

pub fn copy_range(bytes: &Vec<u8>, start: usize, end: usize) -> (out: Vec<u8>)
    requires
        start <= end,
        end <= bytes.len(),
    ensures
        out@ == bytes@.subrange(start as int, end as int),
{
    let mut out = Vec::new();
    let mut i = start;
    while i < end
        invariant
            start <= i <= end,
            end <= bytes.len(),
            out@ == bytes@.subrange(start as int, i as int),
        decreases end - i,
    {
        out.push(bytes[i]);
        i += 1;
    }
    out
}

pub fn append_bytes(out: &mut Vec<u8>, bytes: &Vec<u8>)
    requires
        old(out).len() + bytes.len() <= usize::MAX,
    ensures
        final(out)@ == old(out)@ + bytes@,
{
    let ghost before = out@;
    let mut i = 0usize;
    while i < bytes.len()
        invariant
            i <= bytes.len(),
            out@ == before + bytes@.subrange(0, i as int),
        decreases bytes.len() - i,
    {
        out.push(bytes[i]);
        i += 1;
    }
}

/// A byte string with its canonical eight-byte byte-count prefix.
pub open spec fn blob_bytes(payload: Seq<u8>) -> Seq<u8> {
    u64_bytes(payload.len() as u64) + payload
}

pub fn encode_blob(payload: &Vec<u8>) -> (r: Option<Vec<u8>>)
    ensures
        payload@.len() <= u64::MAX && payload@.len() + 8 <= usize::MAX ==> r is Some,
        r is Some ==> r->Some_0@ == blob_bytes(payload@),
{
    if payload.len() as u128 > u64::MAX as u128 {
        None
    } else {
        let mut out = encode_u64(payload.len() as u64);
        if out.len() > usize::MAX - payload.len() {
            None
        } else {
            append_bytes(&mut out, payload);
            Some(out)
        }
    }
}

pub open spec fn decode_blob_spec(bytes: Seq<u8>) -> Option<Seq<u8>> {
    if bytes.len() < 8 {
        None
    } else {
        match decode_u64_spec(bytes.subrange(0, 8)) {
            None => None,
            Some(n) => {
                if n <= usize::MAX && bytes.len() == 8 + n {
                    Some(bytes.subrange(8, bytes.len() as int))
                } else {
                    None
                }
            }
        }
    }
}

pub fn decode_blob(bytes: &Vec<u8>) -> (r: Option<Vec<u8>>)
    ensures
        r.deep_view() == decode_blob_spec(bytes@),
{
    if bytes.len() < 8 {
        None
    } else {
        let prefix = copy_range(bytes, 0, 8);
        match decode_u64(&prefix) {
            None => None,
            Some(n) => {
                if n > usize::MAX as u64 {
                    None
                } else {
                    let len = n as usize;
                    if len != bytes.len() - 8 {
                        None
                    } else {
                        proof {
                            assert(len as int == n as int);
                        }
                        Some(copy_range(bytes, 8, bytes.len()))
                    }
                }
            }
        }
    }
}

pub proof fn lemma_blob_round_trip(payload: Seq<u8>)
    requires
        payload.len() <= u64::MAX,
        payload.len() <= usize::MAX,
    ensures decode_blob_spec(blob_bytes(payload)) == Some(payload),
{
    lemma_u64_round_trip(payload.len() as u64);
    assert(blob_bytes(payload).subrange(0, 8) == u64_bytes(payload.len() as u64));
    assert(blob_bytes(payload).subrange(8, blob_bytes(payload).len() as int) == payload);
    assert((payload.len() as u64) as int == payload.len());
}

pub open spec fn option_blob_bytes(payload: Option<Seq<u8>>) -> Seq<u8> {
    match payload {
        None => seq![0u8],
        Some(bytes) => seq![1u8] + blob_bytes(bytes),
    }
}

pub open spec fn decode_option_blob_spec(bytes: Seq<u8>) -> Option<Option<Seq<u8>>> {
    if bytes.len() == 0 {
        None
    } else if bytes[0] == 0 {
        if bytes.len() == 1 { Some(None) } else { None }
    } else if bytes[0] == 1 {
        match decode_blob_spec(bytes.subrange(1, bytes.len() as int)) {
            Some(payload) => Some(Some(payload)),
            None => None,
        }
    } else {
        None
    }
}

pub fn encode_option_blob(payload: &Option<Vec<u8>>) -> (r: Option<Vec<u8>>)
    ensures
        payload.deep_view() is None ==> r is Some,
        r is Some ==> r->Some_0@ == option_blob_bytes(payload.deep_view()),
{
    match payload {
        None => {
            let mut out = Vec::new();
            out.push(0);
            Some(out)
        }
        Some(bytes) => {
            match encode_blob(bytes) {
                None => None,
                Some(framed) => {
                    let mut out = Vec::new();
                    out.push(1);
                    if framed.len() == usize::MAX {
                        None
                    } else {
                        append_bytes(&mut out, &framed);
                        Some(out)
                    }
                }
            }
        }
    }
}

pub fn decode_option_blob(bytes: &Vec<u8>) -> (r: Option<Option<Vec<u8>>>)
    ensures
        r.deep_view() == decode_option_blob_spec(bytes@),
{
    if bytes.len() == 0 {
        None
    } else if bytes[0] == 0 {
        if bytes.len() == 1 { Some(None) } else { None }
    } else if bytes[0] == 1 {
        let rest = copy_range(bytes, 1, bytes.len());
        match decode_blob(&rest) {
            Some(payload) => Some(Some(payload)),
            None => None,
        }
    } else {
        None
    }
}

pub proof fn lemma_option_blob_round_trip(payload: Option<Seq<u8>>)
    requires
        payload is Some ==> payload->Some_0.len() <= u64::MAX,
        payload is Some ==> payload->Some_0.len() <= usize::MAX,
    ensures
        decode_option_blob_spec(option_blob_bytes(payload)) == Some(payload),
{
    match payload {
        None => {}
        Some(bytes) => {
            lemma_blob_round_trip(bytes);
            assert(option_blob_bytes(payload).subrange(
                1, option_blob_bytes(payload).len() as int,
            ) == blob_bytes(bytes));
        }
    }
}

pub open spec fn blob_sequence_tail(items: Seq<Seq<u8>>) -> Seq<u8>
    decreases items.len(),
{
    if items.len() == 0 {
        Seq::empty()
    } else {
        blob_bytes(items[0]) + blob_sequence_tail(items.drop_first())
    }
}

pub open spec fn blob_sequence_bytes(items: Seq<Seq<u8>>) -> Seq<u8> {
    u64_bytes(items.len() as u64) + blob_sequence_tail(items)
}

pub fn encode_blob_sequence(items: &Vec<Vec<u8>>) -> (r: Option<Vec<u8>>)
    ensures
        r is Some ==> r->Some_0@ == blob_sequence_bytes(items.deep_view()),
{
    if items.len() as u128 > u64::MAX as u128 {
        return None;
    }
    let mut out = encode_u64(items.len() as u64);
    let mut i = 0usize;
    while i < items.len()
        invariant
            i <= items.len(),
            out@ == u64_bytes(items@.len() as u64)
                + blob_sequence_tail(items.deep_view().subrange(0, i as int)),
        decreases items.len() - i,
    {
        let framed = match encode_blob(&items[i]) {
            None => return None,
            Some(value) => value,
        };
        if out.len() > usize::MAX - framed.len() {
            return None;
        }
        append_bytes(&mut out, &framed);
        proof {
            assert(items.deep_view().subrange(0, (i + 1) as int)
                == items.deep_view().subrange(0, i as int).push(
                    items.deep_view()[i as int],
                ));
            lemma_blob_sequence_tail_push(
                items.deep_view().subrange(0, i as int),
                items.deep_view()[i as int],
            );
        }
        i += 1;
    }
    proof {
        assert(items.deep_view().subrange(0, items.len() as int) == items.deep_view());
    }
    Some(out)
}

pub proof fn lemma_blob_sequence_tail_push(items: Seq<Seq<u8>>, item: Seq<u8>)
    ensures
        blob_sequence_tail(items.push(item))
            == blob_sequence_tail(items) + blob_bytes(item),
    decreases items.len(),
{
    if items.len() == 0 {
        assert(items == Seq::<Seq<u8>>::empty());
        assert(items.push(item) == seq![item]);
        assert(items.push(item).len() == 1);
        assert(items.push(item)[0] == item);
        assert(items.push(item).drop_first() == Seq::<Seq<u8>>::empty());
        assert(blob_sequence_tail(items) == Seq::<u8>::empty());
        assert(blob_sequence_tail(items.push(item))
            == blob_bytes(item) + Seq::<u8>::empty());
    } else {
        let first = items[0];
        let rest = items.drop_first();
        assert(items.push(item)[0] == first);
        assert(items.push(item).drop_first() == rest.push(item));
        lemma_blob_sequence_tail_push(rest, item);
        assert(blob_sequence_tail(items.push(item))
            == blob_bytes(first) + blob_sequence_tail(rest.push(item)));
        assert(blob_sequence_tail(items)
            == blob_bytes(first) + blob_sequence_tail(rest));
        assert(blob_bytes(first)
                + (blob_sequence_tail(rest) + blob_bytes(item))
            == (blob_bytes(first) + blob_sequence_tail(rest))
                + blob_bytes(item));
    }
}

pub open spec fn decode_blob_at_spec(
    bytes: Seq<u8>,
    pos: int,
) -> Option<(Seq<u8>, int)> {
    if pos < 0 || pos + 8 > bytes.len() {
        None
    } else {
        match decode_u64_spec(bytes.subrange(pos, pos + 8)) {
            None => None,
            Some(n) => {
                if n <= usize::MAX && pos + 8 + n <= bytes.len() {
                    Some((
                        bytes.subrange(pos + 8, pos + 8 + n),
                        pos + 8 + n,
                    ))
                } else {
                    None
                }
            }
        }
    }
}

pub fn decode_blob_at(
    bytes: &Vec<u8>,
    pos: usize,
) -> (r: Option<(Vec<u8>, usize)>)
    requires pos <= bytes.len(),
    ensures
        match r {
            None => decode_blob_at_spec(bytes@, pos as int) is None,
            Some((payload, end)) => decode_blob_at_spec(bytes@, pos as int)
                == Some((payload@, end as int)),
        },
{
    if pos > bytes.len() - 0 || bytes.len() - pos < 8 {
        None
    } else {
        let prefix = copy_range(bytes, pos, pos + 8);
        match decode_u64(&prefix) {
            None => None,
            Some(n) => {
                if n > usize::MAX as u64 {
                    None
                } else {
                    let len = n as usize;
                    if len > bytes.len() - (pos + 8) {
                        None
                    } else {
                        let end = pos + 8 + len;
                        proof {
                            assert(len as int == n as int);
                        }
                        Some((copy_range(bytes, pos + 8, end), end))
                    }
                }
            }
        }
    }
}

pub open spec fn decode_n_blobs_spec(
    bytes: Seq<u8>,
    pos: int,
    count: nat,
) -> Option<(Seq<Seq<u8>>, int)>
    decreases count,
{
    if count == 0 {
        Some((Seq::empty(), pos))
    } else {
        match decode_blob_at_spec(bytes, pos) {
            None => None,
            Some((first, next)) => {
                match decode_n_blobs_spec(bytes, next, (count - 1) as nat) {
                    None => None,
                    Some((rest, end)) => Some((seq![first] + rest, end)),
                }
            }
        }
    }
}

pub open spec fn decode_blob_sequence_spec(bytes: Seq<u8>) -> Option<Seq<Seq<u8>>> {
    if bytes.len() < 8 {
        None
    } else {
        match decode_u64_spec(bytes.subrange(0, 8)) {
            None => None,
            Some(count) => {
                if count > usize::MAX || count > MAX_SEQUENCE_ITEMS {
                    None
                } else {
                    match decode_n_blobs_spec(bytes, 8, count as nat) {
                        Some((items, end)) if end == bytes.len() => Some(items),
                        _ => None,
                    }
                }
            }
        }
    }
}

fn decode_n_blobs(
    bytes: &Vec<u8>,
    pos: usize,
    count: usize,
) -> (r: Option<(Vec<Vec<u8>>, usize)>)
    requires
        pos <= bytes.len(),
    ensures
        match r {
            None => decode_n_blobs_spec(bytes@, pos as int, count as nat) is None,
            Some((items, end)) => decode_n_blobs_spec(
                bytes@, pos as int, count as nat,
            ) == Some((items.deep_view(), end as int)),
        },
    decreases count,
{
    if count == 0 {
        Some((Vec::new(), pos))
    } else {
        match decode_blob_at(bytes, pos) {
            None => {
                assert(decode_blob_at_spec(bytes@, pos as int) is None);
                None
            }
            Some((first, next)) => {
                assert(decode_blob_at_spec(bytes@, pos as int)
                    == Some((first@, next as int)));
                match decode_n_blobs(bytes, next, count - 1) {
                    None => {
                        assert(decode_n_blobs_spec(
                            bytes@, next as int, (count - 1) as nat,
                        ) is None);
                        assert((count as nat - 1) as nat == (count - 1) as nat);
                        None
                    }
                    Some((mut rest, end)) => {
                        let ghost old_vec = rest@;
                        let ghost old_rest = rest.deep_view();
                        assert(decode_n_blobs_spec(
                            bytes@, next as int, (count - 1) as nat,
                        ) == Some((old_rest, end as int)));
                        rest.insert(0, first);
                        assert(rest.deep_view() =~= seq![first@] + old_rest) by {
                            assert(rest.deep_view().len() == old_rest.len() + 1);
                            assert forall|i: int| 0 <= i < rest.deep_view().len()
                                implies rest.deep_view()[i]
                                    == (seq![first@] + old_rest)[i] by {
                                if i == 0 {
                                    assert(rest@[0] == first);
                                } else {
                                    assert(rest@[i] == old_vec[i - 1]);
                                    assert(old_rest[i - 1] == old_vec[i - 1]@);
                                }
                            }
                        }
                        assert((count as nat - 1) as nat == (count - 1) as nat);
                        Some((rest, end))
                    }
                }
            }
        }
    }
}

pub fn decode_blob_sequence(bytes: &Vec<u8>) -> (r: Option<Vec<Vec<u8>>>)
    ensures
        r.deep_view() == decode_blob_sequence_spec(bytes@),
{
    if bytes.len() < 8 {
        None
    } else {
        let prefix = copy_range(bytes, 0, 8);
        match decode_u64(&prefix) {
            None => None,
            Some(count) => {
                if count > usize::MAX as u64 || count > MAX_SEQUENCE_ITEMS {
                    None
                } else {
                    let count_usize = count as usize;
                    proof {
                        assert(count_usize as nat == count as nat);
                    }
                    match decode_n_blobs(bytes, 8, count_usize) {
                        Some((items, end)) if end == bytes.len() => Some(items),
                        _ => None,
                    }
                }
            }
        }
    }
}

pub proof fn lemma_decode_blob_at_concat(
    prefix: Seq<u8>,
    payload: Seq<u8>,
    suffix: Seq<u8>,
)
    requires
        payload.len() <= u64::MAX,
        payload.len() <= usize::MAX,
    ensures
        decode_blob_at_spec(
            prefix + blob_bytes(payload) + suffix,
            prefix.len() as int,
        ) == Some((
            payload,
            (prefix.len() + blob_bytes(payload).len()) as int,
        )),
{
    lemma_u64_round_trip(payload.len() as u64);
    let all = prefix + blob_bytes(payload) + suffix;
    assert(all.subrange(prefix.len() as int, (prefix.len() + 8) as int)
        == u64_bytes(payload.len() as u64));
    assert(all.subrange(
        (prefix.len() + 8) as int,
        (prefix.len() + 8 + payload.len()) as int,
    ) == payload);
    assert((payload.len() as u64) as int == payload.len());
}

pub proof fn lemma_blob_sequence_round_trip(items: Seq<Seq<u8>>)
    requires
        items.len() <= u64::MAX,
        items.len() <= usize::MAX,
        items.len() <= MAX_SEQUENCE_ITEMS,
        forall|i: int| 0 <= i < items.len() ==> {
            &&& #[trigger] items[i].len() <= u64::MAX
            &&& items[i].len() <= usize::MAX
        },
    ensures
        decode_blob_sequence_spec(blob_sequence_bytes(items)) == Some(items),
{
    lemma_u64_round_trip(items.len() as u64);
    assert(blob_sequence_bytes(items).subrange(0, 8)
        == u64_bytes(items.len() as u64));
    let prefix = u64_bytes(items.len() as u64);
    lemma_decode_n_blob_sequence(items, prefix);
    assert(blob_sequence_bytes(items) == prefix + blob_sequence_tail(items));
    assert(decode_n_blobs_spec(
        blob_sequence_bytes(items),
        8,
        items.len() as nat,
    ) == Some((items, blob_sequence_bytes(items).len() as int)));
    assert((items.len() as u64) as nat == items.len());
}

proof fn lemma_decode_n_blob_sequence(
    items: Seq<Seq<u8>>,
    prefix: Seq<u8>,
)
    requires
        items.len() <= usize::MAX,
        forall|i: int| 0 <= i < items.len() ==> {
            &&& #[trigger] items[i].len() <= u64::MAX
            &&& items[i].len() <= usize::MAX
        },
    ensures
        decode_n_blobs_spec(
            prefix + blob_sequence_tail(items),
            prefix.len() as int,
            items.len() as nat,
        ) == Some((
            items,
            (prefix.len() + blob_sequence_tail(items).len()) as int,
        )),
    decreases items.len(),
{
    if items.len() == 0 {
        assert(items == Seq::<Seq<u8>>::empty());
        assert(blob_sequence_tail(items) == Seq::<u8>::empty());
        assert(prefix + blob_sequence_tail(items) == prefix);
    } else {
        let first = items[0];
        let rest = items.drop_first();
        let all = prefix + blob_sequence_tail(items);
        let next_prefix = prefix + blob_bytes(first);
        assert(blob_sequence_tail(items)
            == blob_bytes(first) + blob_sequence_tail(rest));
        assert(all == prefix + blob_bytes(first) + blob_sequence_tail(rest));
        lemma_decode_blob_at_concat(prefix, first, blob_sequence_tail(rest));
        assert(decode_blob_at_spec(all, prefix.len() as int)
            == Some((first, next_prefix.len() as int)));
        lemma_decode_n_blob_sequence(rest, next_prefix);
        assert(all == next_prefix + blob_sequence_tail(rest));
        assert(decode_n_blobs_spec(
            all,
            next_prefix.len() as int,
            rest.len() as nat,
        ) == Some((
            rest,
            (next_prefix.len() + blob_sequence_tail(rest).len()) as int,
        )));
        assert(seq![first] + rest == items);
        assert(items.len() - 1 == rest.len());
        assert(prefix.len() + blob_sequence_tail(items).len()
            == next_prefix.len() + blob_sequence_tail(rest).len());
    }
}

} // verus!
