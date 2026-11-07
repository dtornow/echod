include "../framework/framework.dfy"

// Keys, in lexicographic order, so a listing is a prefix of a sorted set.
module Lex {
  predicate Leq(a: string, b: string)
    decreases |a|
  {
    |a| == 0 || (|b| > 0 && (a[0] < b[0] || (a[0] == b[0] && Leq(a[1..], b[1..]))))
  }

  predicate Lt(a: string, b: string) { a != b && Leq(a, b) }

  predicate Sorted(xs: seq<string>) {
    forall i, j :: 0 <= i < j < |xs| ==> Lt(xs[i], xs[j])
  }

  lemma LeqRefl(a: string)
    ensures Leq(a, a)
    decreases |a|
  {
    if |a| != 0 { LeqRefl(a[1..]); }
  }

  lemma LeqTotal(a: string, b: string)
    ensures Leq(a, b) || Leq(b, a)
    decreases |a| + |b|
  {
    if |a| != 0 && |b| != 0 && a[0] == b[0] {
      LeqTotal(a[1..], b[1..]);
    }
  }

  lemma LeqAntisym(a: string, b: string)
    requires Leq(a, b) && Leq(b, a)
    ensures a == b
    decreases |a| + |b|
  {
    if |a| != 0 && |b| != 0 && a[0] == b[0] {
      LeqAntisym(a[1..], b[1..]);
    }
  }

  lemma LeqHead(a: string, b: string)
    requires |a| > 0 && |b| > 0 && Leq(a, b)
    ensures a[0] < b[0] || (a[0] == b[0] && Leq(a[1..], b[1..]))
  {
  }

  lemma LeqTrans(a: string, b: string, c: string)
    requires Leq(a, b) && Leq(b, c)
    ensures Leq(a, c)
    decreases |a| + |b| + |c|
  {
    if |a| > 0 && |b| > 0 && |c| > 0 {
      LeqHead(a, b);
      LeqHead(b, c);
      if a[0] == b[0] && b[0] == c[0] {
        LeqTrans(a[1..], b[1..], c[1..]);
      }
    }
  }

  lemma MinExists(keys: set<string>)
    requires keys != {}
    ensures exists k :: k in keys && forall k' :: k' in keys ==> Leq(k, k')
    decreases |keys|
  {
    var x :| x in keys;
    var rest := keys - {x};
    if rest == {} {
      LeqRefl(x);
    } else {
      MinExists(rest);
      var m :| m in rest && forall k' :: k' in rest ==> Leq(m, k');
      if Leq(x, m) {
        LeqRefl(x);
        forall k' | k' in keys
          ensures Leq(x, k')
        {
          if k' != x {
            assert k' in rest;
            LeqTrans(x, m, k');
          }
        }
      } else {
        LeqTotal(x, m);
        forall k' | k' in keys
          ensures Leq(m, k')
        {
          if k' != x { assert k' in rest; }
        }
      }
    }
  }

  function MinKey(keys: set<string>): string
    requires keys != {}
    ensures MinKey(keys) in keys
    ensures forall k :: k in keys ==> Leq(MinKey(keys), k)
  {
    MinExists(keys);
    assert forall a, b ::
      (a in keys && b in keys &&
       (forall k' :: k' in keys ==> Leq(a, k')) &&
       (forall k' :: k' in keys ==> Leq(b, k'))) ==>
      a == b
    by {
      forall a, b | a in keys && b in keys &&
        (forall k' :: k' in keys ==> Leq(a, k')) &&
        (forall k' :: k' in keys ==> Leq(b, k'))
        ensures a == b
      {
        LeqAntisym(a, b);
      }
    }
    var k :| k in keys && forall k' :: k' in keys ==> Leq(k, k');
    k
  }

  lemma MinUnique(keys: set<string>, a: string)
    requires keys != {} && a in keys
    requires forall k :: k in keys ==> Leq(a, k)
    ensures MinKey(keys) == a
  {
    var m := MinKey(keys);
    assert Leq(m, a);
    LeqAntisym(a, m);
  }

  lemma InCons(x: string, xs: seq<string>, y: string)
    ensures y in [x] + xs <==> y == x || y in xs
  {
  }

  lemma SortedCons(m: string, rest: seq<string>)
    requires Sorted(rest)
    requires forall i :: 0 <= i < |rest| ==> Lt(m, rest[i])
    ensures Sorted([m] + rest)
  {
    forall i, j | 0 <= i < j < |[m] + rest|
      ensures Lt(([m] + rest)[i], ([m] + rest)[j])
    {
      if i == 0 {
        assert ([m] + rest)[j] == rest[j - 1];
      } else {
        assert ([m] + rest)[i] == rest[i - 1];
        assert ([m] + rest)[j] == rest[j - 1];
      }
    }
  }

  function SortedKeys(keys: set<string>): (sorted: seq<string>)
    ensures |sorted| == |keys|
    ensures forall k :: k in sorted <==> k in keys
    ensures Sorted(sorted)
    decreases |keys|
  {
    if keys == {} then []
    else
      var m := MinKey(keys);
      var rest := SortedKeys(keys - {m});
      forall i | 0 <= i < |rest|
        ensures Lt(m, rest[i])
      {
        assert rest[i] in rest;
        assert rest[i] in keys && rest[i] != m;
      }
      SortedCons(m, rest);
      forall y | true
        ensures y in [m] + rest <==> y == m || y in rest
      {
        InCons(m, rest, y);
      }
      [m] + rest
  }

  function Take(xs: seq<string>, n: nat): (r: seq<string>)
    ensures |r| == if n < |xs| then n else |xs|
    ensures forall i :: 0 <= i < |r| ==> r[i] == xs[i]
    decreases n
  {
    if n == 0 || |xs| == 0 then []
    else [xs[0]] + Take(xs[1..], n - 1)
  }
}

// The bucket, as the store port the server speaks.
//
// Get, conditional get, conditional put, append, blind put, delete, list,
// list prefixes: `Store` in rust/impl/runtime/src/store.rs, and `spec_apply`
// in rust/spec/concrete/src/store.rs. A version is a function of the bytes.
// S3's ETag is that function; the port only compares versions, so the bytes
// themselves stand in for it. The same bytes are the same version, on every
// key, which is why a write that must move the version changes the bytes.
//
// The bucket answers one call with one reply. A dropped reply is a write
// that landed and an ack that did not; a duplicate delivery is a second
// call, and a conditional create then fails. Both are the network's Drop
// and Duplicate. The `(node, op)` memory in the concrete Rover store is not
// part of S3. The bucket is one system on the generic network: its ids, its
// Init, its Step, and a network that may drop or duplicate.
module S3 {
  import opened Network
  import opened Lex

  datatype Opt<T> = None | Some(value: T)

  type Bytes = seq<bv8>
  type Key = string
  type Etag = Bytes

  function EtagOf(body: Bytes): Etag { body }

  datatype State = Held(objects: map<Key, Bytes>, appendable: bool)

  datatype Pid = Bucket

  datatype Error =
    | PreconditionFailed
    | Unavailable(reason: string)

  datatype Read =
    | Absent
    | NotModified
    | Body(body: Bytes, etag: Etag)

  datatype Outcome =
    | Got(obj: Opt<(Bytes, Etag)>)
    | Read(read: Read)
    | Written(etag: Etag)
    | Done
    | Listed(keys: seq<Key>)
    | Failed(err: Error)

  datatype Applied = Applied(state: State, out: Outcome)

  datatype Op =
    | Get(key: Key)
    | GetIfNoneMatch(key: Key, etag: Etag)
    | PutIfMatch(key: Key, body: Bytes, etag: Etag)
    | PutIfNoneMatch(key: Key, body: Bytes)
    | AppendIfMatch(key: Key, offset: nat, body: Bytes, etag: Etag)
    | Put(key: Key, body: Bytes)
    | Delete(key: Key)
    | List(prefix: Key, maxKeys: nat)
    | ListPrefixes(prefix: Key)

  datatype Msg = Ask(op: Op) | Reply(out: Outcome)

  const Pids: set<Pid> := {Bucket}

  // A general-purpose bucket. A directory bucket is the same process with
  // the flag set: `AppendIfMatch` is the only call that reads it.
  function Init(self: Pid): State { Held(map[], false) }

  predicate HasPrefix(k: Key, p: Key) {
    |p| <= |k| && k[..|p|] == p
  }

  function SlashFrom(s: string, i: nat): Opt<nat>
    requires i <= |s|
    decreases |s| - i
  {
    if i == |s| then None
    else if s[i] == '/' then Some(i)
    else SlashFrom(s, i + 1)
  }

  lemma SlashSpec(s: string, i: nat)
    requires i <= |s|
    ensures var r := SlashFrom(s, i);
      && (r.Some? ==>
           i <= r.value < |s| && s[r.value] == '/' &&
           forall n :: i <= n < r.value ==> s[n] != '/')
      && (r.None? ==> forall n :: i <= n < |s| ==> s[n] != '/')
    decreases |s| - i
  {
    if i < |s| && s[i] != '/' { SlashSpec(s, i + 1); }
  }

  predicate HasChild(k: Key, prefix: Key) {
    HasPrefix(k, prefix) && SlashFrom(k, |prefix|).Some?
  }

  function ChildOf(k: Key, prefix: Key): Key
    requires HasChild(k, prefix)
  {
    SlashSpec(k, |prefix|);
    var j := SlashFrom(k, |prefix|).value;
    assert j < |k| && j + 1 <= |k|;
    k[..j + 1]
  }

  lemma ChildSpec(k: Key, prefix: Key)
    requires HasChild(k, prefix)
    ensures var c := ChildOf(k, prefix);
      && |c| > |prefix| && |c| <= |k| && c[|c| - 1] == '/'
      && HasPrefix(c, prefix) && HasPrefix(k, c)
      && forall n :: |prefix| <= n < |c| - 1 ==> c[n] != '/'
  {
    SlashSpec(k, |prefix|);
    var j := SlashFrom(k, |prefix|).value;
    assert k[..j + 1][j] == k[j];
  }

  ghost predicate SameElsewhere(a: map<Key, Bytes>, b: map<Key, Bytes>, key: Key) {
    forall k :: k != key ==> (k in a <==> k in b) && (k in a ==> a[k] == b[k])
  }

  function {:opaque} WithPrefix(keys: set<Key>, prefix: Key): set<Key> {
    set k | k in keys && HasPrefix(k, prefix)
  }

  lemma WithPrefixSpec(keys: set<Key>, prefix: Key, k: Key)
    ensures k in WithPrefix(keys, prefix) <==> k in keys && HasPrefix(k, prefix)
  {
    reveal WithPrefix();
  }

  function {:opaque} PrefixSet(keys: set<Key>, prefix: Key): set<Key>
    decreases |keys|
    ensures forall c :: c in PrefixSet(keys, prefix) ==>
      |c| > |prefix| && c[|c| - 1] == '/' && HasPrefix(c, prefix)
    ensures forall k :: k in keys && HasChild(k, prefix) ==>
      ChildOf(k, prefix) in PrefixSet(keys, prefix)
  {
    if keys == {} then {}
    else
      var m := MinKey(keys);
      var rest := PrefixSet(keys - {m}, prefix);
      if HasChild(m, prefix) then
        ChildSpec(m, prefix);
        var r := rest + {ChildOf(m, prefix)};
        forall c | c in r
          ensures |c| > |prefix| && c[|c| - 1] == '/' && HasPrefix(c, prefix)
        {
          if c != ChildOf(m, prefix) { assert c in rest; }
        }
        forall k | k in keys && HasChild(k, prefix)
          ensures ChildOf(k, prefix) in r
        {
          if k != m { assert k in keys - {m}; }
        }
        r
      else
        forall c | c in rest
          ensures |c| > |prefix| && c[|c| - 1] == '/' && HasPrefix(c, prefix)
        {
        }
        forall k | k in keys && HasChild(k, prefix)
          ensures ChildOf(k, prefix) in rest
        {
          assert k != m;
          assert k in keys - {m};
        }
        rest
  }

  lemma IndexIn(xs: seq<Key>, k: Key) returns (i: nat)
    requires k in xs
    ensures i < |xs| && xs[i] == k
    decreases |xs|
  {
    if xs[0] == k { return 0; }
    var j := IndexIn(xs[1..], k);
    return j + 1;
  }

  lemma ListingSpec(sorted: seq<Key>, max: nat, got: seq<Key>, objects: map<Key, Bytes>, prefix: Key)
    requires Sorted(sorted)
    requires forall k :: k in sorted ==> k in objects && HasPrefix(k, prefix)
    requires got == Take(sorted, max)
    ensures |got| <= max && Sorted(got)
    ensures forall k :: k in got ==> k in objects && HasPrefix(k, prefix)
    ensures forall k :: k in sorted ==>
      k in got || (|got| == max && forall r :: r in got ==> Lt(r, k))
  {
    var n := |got|;
    forall i, j | 0 <= i < j < n
      ensures Lt(got[i], got[j])
    {
      assert got[i] == sorted[i] && got[j] == sorted[j];
    }
    forall k | k in got
      ensures k in objects && HasPrefix(k, prefix)
    {
      var i := IndexIn(got, k);
      assert got[i] == sorted[i];
    }
    forall k | k in sorted
      ensures k in got || (n == max && forall r :: r in got ==> Lt(r, k))
    {
      var i := IndexIn(sorted, k);
      if i < n {
        assert got[i] == k;
      } else {
        assert n == max;
        forall r | r in got
          ensures Lt(r, k)
        {
          var j := IndexIn(got, r);
          assert sorted[j] == r && j < i;
        }
      }
    }
  }

  // The `maxKeys` smallest keys under `prefix`, ascending.
  function ListKeys(objects: map<Key, Bytes>, prefix: Key, max: nat): (got: seq<Key>)
    ensures |got| <= max && Sorted(got)
    ensures forall k :: k in got ==> k in objects && HasPrefix(k, prefix)
    ensures forall k :: k in objects && HasPrefix(k, prefix) ==>
      k in got || (|got| == max && forall r :: r in got ==> Lt(r, k))
  {
    var all := WithPrefix(objects.Keys, prefix);
    var sorted := SortedKeys(all);
    var got := Take(sorted, max);
    forall k | k in sorted
      ensures k in objects && HasPrefix(k, prefix)
    {
      WithPrefixSpec(objects.Keys, prefix, k);
      assert k in objects.Keys;
    }
    ListingSpec(sorted, max, got, objects, prefix);
    forall k | k in objects && HasPrefix(k, prefix)
      ensures k in got || (|got| == max && forall r :: r in got ==> Lt(r, k))
    {
      assert k in objects.Keys;
      WithPrefixSpec(objects.Keys, prefix, k);
      assert k in all && k in sorted;
    }
    got
  }

  // The sub-prefixes directly under `prefix`, up to the next `/`, ascending.
  // Each ends with `/`.
  function PrefixKeys(objects: map<Key, Bytes>, prefix: Key): (got: seq<Key>)
    ensures Sorted(got)
    ensures forall c :: c in got ==> |c| > |prefix| && c[|c| - 1] == '/' && HasPrefix(c, prefix)
    ensures forall k :: k in objects && HasChild(k, prefix) ==> ChildOf(k, prefix) in got
  {
    var ps := PrefixSet(objects.Keys, prefix);
    var got := SortedKeys(ps);
    forall c | c in got
      ensures |c| > |prefix| && c[|c| - 1] == '/' && HasPrefix(c, prefix)
    {
      reveal PrefixSet();
    }
    forall k | k in objects && HasChild(k, prefix)
      ensures ChildOf(k, prefix) in got
    {
      reveal PrefixSet();
    }
    got
  }

  function Observe(s: State, key: Key): Outcome {
    if key in s.objects then Got(Some((s.objects[key], EtagOf(s.objects[key]))))
    else Got(None)
  }

  function ObserveIf(s: State, key: Key, etag: Etag): Outcome {
    if key !in s.objects then Read(Absent)
    else if EtagOf(s.objects[key]) == etag then Read(NotModified)
    else Read(Body(s.objects[key], EtagOf(s.objects[key])))
  }

  function Create(s: State, key: Key, body: Bytes): (r: Applied)
    ensures r.state.appendable == s.appendable
    ensures key in s.objects ==> r.state == s && r.out == Failed(PreconditionFailed)
    ensures key !in s.objects ==>
      && r.out == Written(EtagOf(body))
      && key in r.state.objects && r.state.objects[key] == body
      && SameElsewhere(s.objects, r.state.objects, key)
  {
    if key in s.objects then Applied(s, Failed(PreconditionFailed))
    else
      var objects := s.objects[key := body];
      Applied(Held(objects, s.appendable), Written(EtagOf(body)))
  }

  function Replace(s: State, key: Key, body: Bytes, etag: Etag): (r: Applied)
    ensures r.state.appendable == s.appendable
    ensures key !in s.objects || EtagOf(s.objects[key]) != etag ==>
      r.state == s && r.out == Failed(PreconditionFailed)
    ensures key in s.objects && EtagOf(s.objects[key]) == etag ==>
      && r.out == Written(EtagOf(body))
      && key in r.state.objects && r.state.objects[key] == body
      && SameElsewhere(s.objects, r.state.objects, key)
  {
    if key in s.objects && EtagOf(s.objects[key]) == etag then
      var objects := s.objects[key := body];
      Applied(Held(objects, s.appendable), Written(EtagOf(body)))
    else Applied(s, Failed(PreconditionFailed))
  }

  function Append(s: State, key: Key, offset: nat, body: Bytes, etag: Etag): (r: Applied)
    ensures r.state.appendable == s.appendable
    ensures !s.appendable ==> r.state == s && r.out == Failed(Unavailable("this store does not append"))
    ensures s.appendable ==>
      (key in s.objects && EtagOf(s.objects[key]) == etag && offset == |s.objects[key]| ==>
        && r.out == Written(EtagOf(s.objects[key] + body))
        && key in r.state.objects && r.state.objects[key] == s.objects[key] + body
        && SameElsewhere(s.objects, r.state.objects, key)) &&
      (key !in s.objects || EtagOf(s.objects[key]) != etag || offset != |s.objects[key]| ==>
        r.state == s && r.out == Failed(PreconditionFailed))
  {
    if !s.appendable then Applied(s, Failed(Unavailable("this store does not append")))
    else if key in s.objects && EtagOf(s.objects[key]) == etag && offset == |s.objects[key]| then
      var joined := s.objects[key] + body;
      var objects := s.objects[key := joined];
      Applied(Held(objects, s.appendable), Written(EtagOf(joined)))
    else Applied(s, Failed(PreconditionFailed))
  }

  function Write(s: State, key: Key, body: Bytes): (r: Applied)
    ensures r.state.appendable == s.appendable
    ensures r.out == Done && key in r.state.objects && r.state.objects[key] == body && SameElsewhere(s.objects, r.state.objects, key)
  {
    Applied(Held(s.objects[key := body], s.appendable), Done)
  }

  function Remove(s: State, key: Key): (r: Applied)
    ensures r.state.appendable == s.appendable
    ensures r.out == Done && key !in r.state.objects && SameElsewhere(s.objects, r.state.objects, key)
  {
    var objects := if key in s.objects then s.objects - {key} else s.objects;
    Applied(Held(objects, s.appendable), Done)
  }

  function Apply(s: State, op: Op): (r: Applied)
    ensures r.state.appendable == s.appendable
  {
    match op
    case Get(key) => Applied(s, Observe(s, key))
    case GetIfNoneMatch(key, etag) => Applied(s, ObserveIf(s, key, etag))
    case PutIfNoneMatch(key, body) => Create(s, key, body)
    case PutIfMatch(key, body, etag) => Replace(s, key, body, etag)
    case AppendIfMatch(key, offset, body, etag) => Append(s, key, offset, body, etag)
    case Put(key, body) => Write(s, key, body)
    case Delete(key) => Remove(s, key)
    case List(prefix, maxKeys) => Applied(s, Listed(ListKeys(s.objects, prefix, maxKeys)))
    case ListPrefixes(prefix) => Applied(s, Listed(PrefixKeys(s.objects, prefix)))
  }

  function Step(self: Pid, s: State, i: Input<Pid, Msg>): Result<Pid, Msg, State>
    ensures Step(self, s, i).state.appendable == s.appendable
  {
    match i
    case Timeout => Result(s, [], Cancel)
    case Request(from, Ask(op)) =>
      var r := Apply(s, op);
      Result(r.state, [Send(from, Reply(r.out))], Keep)
    case Request(_, Reply(_)) => Result(s, [], Keep)
  }

  // -----------------------------------------------------------------
  // The port's contract, as the store tests state it.
  // -----------------------------------------------------------------

  function Octet(n: bv8): Bytes { [n] }

  lemma ConditionalWritesMatchThePort()
  {
    var one := Octet(1);
    var two := Octet(2);
    var s := Held(map[], false);

    var created := Apply(s, PutIfNoneMatch("doc", one));
    assert created.out == Written(EtagOf(one));
    assert created.state.objects["doc"] == one;

    var again := Apply(created.state, PutIfNoneMatch("doc", two));
    assert again.out == Failed(PreconditionFailed) && again.state == created.state;

    var updated := Apply(created.state, PutIfMatch("doc", two, EtagOf(one)));
    assert updated.out == Written(EtagOf(two));
    assert updated.state.objects["doc"] == two;

    var stale := Apply(updated.state, PutIfMatch("doc", one, EtagOf(one)));
    assert stale.out == Failed(PreconditionFailed) && stale.state == updated.state;

    var got := Apply(updated.state, Get("doc"));
    assert got.out == Got(Some((two, EtagOf(two))));

    var same := Apply(updated.state, GetIfNoneMatch("doc", EtagOf(two)));
    assert same.out == Read(NotModified);

    var newer := Apply(updated.state, GetIfNoneMatch("doc", EtagOf(one)));
    assert newer.out == Read(Body(two, EtagOf(two)));

    var absent := Apply(updated.state, GetIfNoneMatch("absent", EtagOf(one)));
    assert absent.out == Read(Absent);

    var missing := Apply(updated.state, PutIfMatch("absent", one, EtagOf(one)));
    assert missing.out == Failed(PreconditionFailed) && missing.state == updated.state;

    var gone := Apply(updated.state, Delete("doc"));
    assert gone.out == Done && "doc" !in gone.state.objects;
    var gone2 := Apply(gone.state, Delete("doc"));
    assert gone2.out == Done && gone2.state == gone.state;
  }

  lemma AVersionIsTheContent()
  {
    var body := Octet(1);
    var a := Apply(Held(map[], false), PutIfNoneMatch("a", body));
    var b := Apply(a.state, PutIfNoneMatch("b", body));
    assert a.out == Written(EtagOf(body)) && b.out == Written(EtagOf(body));
    var again := Apply(b.state, PutIfMatch("a", body, EtagOf(body)));
    assert again.out == Written(EtagOf(body));
    var other := Octet(2);
    var moved := Apply(again.state, PutIfMatch("a", other, EtagOf(body)));
    assert moved.out == Written(EtagOf(other)) && EtagOf(other) != EtagOf(body);
  }

  lemma BlindPutOverwritesAndDeleteOfNothingSucceeds()
  {
    var one := Octet(1);
    var two := Octet(2);
    var s := Held(map[], false);
    var w := Apply(s, Put("k", one));
    var w2 := Apply(w.state, Put("k", two));
    assert w2.out == Done && w2.state.objects["k"] == two;
    var d := Apply(w2.state, Delete("k"));
    var d2 := Apply(d.state, Delete("k"));
    assert d2.state.objects == map[] && Apply(d2.state, Get("k")).out == Got(None);
  }

  lemma AppendIsTheDirectoryHeld()
  {
    var one := Octet(1);
    var two := Octet(2);
    var plain := Held(map["k" := one], false);
    var refused := Apply(plain, AppendIfMatch("k", 1, two, EtagOf(one)));
    assert refused.out == Failed(Unavailable("this store does not append"));
    assert refused.state == plain;

    var dir := Held(map["k" := one], true);
    var off := Apply(dir, AppendIfMatch("k", 0, two, EtagOf(one)));
    assert off.out == Failed(PreconditionFailed) && off.state == dir;
    var stale := Apply(dir, AppendIfMatch("k", 1, two, EtagOf(two)));
    assert stale.out == Failed(PreconditionFailed);
    var ok := Apply(dir, AppendIfMatch("k", 1, two, EtagOf(one)));
    assert ok.out == Written(EtagOf(one + two));
    assert ok.state.objects["k"] == one + two;
  }

  lemma SortedPair(a: Key, b: Key)
    requires Lt(a, b)
    ensures SortedKeys({a, b}) == [a, b]
  {
    var keys := {a, b};
    LeqRefl(a);
    forall k | k in keys ensures Leq(a, k) {
      if k != a { assert k == b; }
    }
    MinUnique(keys, a);
    assert keys - {a} == {b};
    LeqRefl(b);
    MinUnique({b}, b);
    assert SortedKeys({b}) == [b];
    assert SortedKeys(keys) == [a] + [b];
  }

  lemma ListingsPageAndSort()
  {
    var empty: Bytes := [];
    var s := Held(map[], false);
    s := Apply(s, Put("b/2", empty)).state;
    s := Apply(s, Put("a/1", empty)).state;
    s := Apply(s, Put("b/1", empty)).state;
    assert s.objects.Keys == {"a/1", "b/1", "b/2"};

    assert Lt("b/1", "b/2");
    reveal WithPrefix();
    assert WithPrefix(s.objects.Keys, "b/") == {"b/1", "b/2"};
    SortedPair("b/1", "b/2");
    assert ListKeys(s.objects, "b/", 10) == ["b/1", "b/2"];
    assert ListKeys(s.objects, "b/", 1) == ["b/1"];
    assert Apply(s, List("b/", 10)).out == Listed(["b/1", "b/2"]);
    assert Apply(s, List("b/", 1)).out == Listed(["b/1"]);

    assert HasChild("a/1", "") && ChildOf("a/1", "") == "a/";
    assert HasChild("b/1", "") && ChildOf("b/1", "") == "b/";
    assert HasChild("b/2", "") && ChildOf("b/2", "") == "b/";
    reveal PrefixSet();
    var keys := s.objects.Keys;
    assert Lt("a/1", "b/1") && Lt("a/1", "b/2") && Lt("b/1", "b/2");
    LeqRefl("a/1");
    forall k | k in keys ensures Leq("a/1", k) {
      if k != "a/1" { assert k == "b/1" || k == "b/2"; }
    }
    MinUnique(keys, "a/1");
    assert keys - {"a/1"} == {"b/1", "b/2"};
    assert PrefixSet(keys, "") == PrefixSet({"b/1", "b/2"}, "") + {"a/"};
    LeqRefl("b/1");
    forall k | k in {"b/1", "b/2"} ensures Leq("b/1", k) {
      if k != "b/1" { assert k == "b/2"; }
    }
    MinUnique({"b/1", "b/2"}, "b/1");
    assert PrefixSet({"b/1", "b/2"}, "") == PrefixSet({"b/2"}, "") + {"b/"};
    LeqRefl("b/2");
    MinUnique({"b/2"}, "b/2");
    assert PrefixSet({"b/2"}, "") == {"b/"};
    assert PrefixSet(keys, "") == {"a/", "b/"};
    assert Lt("a/", "b/");
    SortedPair("a/", "b/");
    assert PrefixKeys(s.objects, "") == ["a/", "b/"];
    assert Apply(s, ListPrefixes("")).out == Listed(["a/", "b/"]);
  }

  // Faults are on: a request or a reply may be dropped or duplicated, and
  // that is the whole of transport failure. The bucket does not answer
  // "unknown".
  function World(): Sys<Pid, Msg, State> { Sys(Pids, true, Init, Step) }

  ghost predicate Stable(n: Net<Pid, Msg, State>) {
    && n.procs.Keys == Pids
    && Bucket in n.procs
    && n.procs[Bucket].appendable == Init(Bucket).appendable
  }

  // Boot is a timeout at time 0. The bucket has nothing to do then: the
  // timer is cancelled and the bucket stays empty.
  lemma BootCancelsTheTimer()
    ensures var w := World();
      exists n: Net<Pid, Msg, State>, n': Net<Pid, Msg, State> ::
        IsInit(w, n) && NextStep(w, n, n', Fire(Bucket)) &&
        n'.procs[Bucket].objects == map[] && Bucket !in n'.timers
  {
    var w := World();
    var n := Net(map[Bucket := Init(Bucket)], multiset{}, map[Bucket := 0], 0);
    var n' := Net(n.procs, multiset{}, map[], 0);
    assert IsInit(w, n);
    assert NextStep(w, n, n', Fire(Bucket));
  }

  lemma StableStep(n: Net<Pid, Msg, State>, n': Net<Pid, Msg, State>, a: Action<Pid, Msg>)
    requires Stable(n) && NextStep(World(), n, n', a)
    ensures Stable(n')
  {
    var w := World();
    assert w.step == Step;
    match a
    case Deliver(p) => {
      var r := Step(p.dst, n.procs[p.dst], Request(p.src, p.msg));
      assert r.state.appendable == n.procs[p.dst].appendable;
    }
    case Fire(pid) => {
      var r := Step(pid, n.procs[pid], Timeout);
      assert r.state.appendable == n.procs[pid].appendable;
    }
    case _ => { }
  }

  lemma StableTrace(t: seq<Net<Pid, Msg, State>>)
    requires IsTrace(World(), t)
    ensures forall i :: 0 <= i < |t| ==> Stable(t[i])
  {
    var w := World();
    forall n | IsInit(w, n) ensures Stable(n) { }
    forall n, n', a | Stable(n) && NextStep(w, n, n', a) ensures Stable(n') {
      StableStep(n, n', a);
    }
    assert Preserves(w, Stable);
    TraceSafety(w, Stable, Stable, t);
  }
}
