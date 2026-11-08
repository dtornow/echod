include "../framework/framework.dfy"

// The bucket the server speaks. Nine calls, as `Store` and `spec_apply`.
//
// Objects are a sequence in key order, so a listing is a scan: the first
// `maxKeys` keys under a prefix, and the prefixes up to the next `/`.
// A version is the bytes. Append is refused unless the bucket was started
// with that flag set, and a step does not change the flag. The bucket is
// one system on the network.
module S3 {
  import opened Network
  import opened Keys

  type Bytes = seq<bv8>
  type Key = string
  type Etag = Bytes

  function EtagOf(body: Bytes): Etag { body }

  datatype Entry = Entry(key: Key, body: Bytes)
  datatype State = Held(entries: seq<Entry>, appendable: bool)
  datatype Pid = Bucket

  datatype Opt<T> = None | Some(value: T)

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

  predicate Ordered(xs: seq<Entry>) {
    forall i, j :: 0 <= i < j < |xs| ==> Lt(xs[i].key, xs[j].key)
  }

  // Insert or replace, in order.
  function Put(xs: seq<Entry>, e: Entry): (ys: seq<Entry>)
    ensures e in ys
    ensures forall z :: z in ys ==> z == e || z in xs
    ensures forall z :: z in xs && z.key != e.key ==> z in ys
    ensures Ordered(xs) ==> Ordered(ys)
    decreases |xs|
  {
    if xs == [] then [e]
    else if xs[0].key == e.key then
      var ys := [e] + xs[1..];
      assert Ordered(xs) ==> Ordered(ys) by {
        if Ordered(xs) {
          forall i, j | 0 <= i < j < |ys|
            ensures Lt(ys[i].key, ys[j].key)
          {
            if i == 0 { assert ys[j] == xs[j] && Lt(xs[0].key, xs[j].key); }
          }
        }
      }
      ys
    else if Lt(xs[0].key, e.key) then
      var rest := Put(xs[1..], e);
      var ys := [xs[0]] + rest;
      assert Ordered(xs) ==> Ordered(ys) by {
        if Ordered(xs) {
          forall i, j | 0 <= i < j < |xs[1..]|
            ensures Lt(xs[1..][i].key, xs[1..][j].key)
          {}
          forall i, j | 0 <= i < j < |ys|
            ensures Lt(ys[i].key, ys[j].key)
          {
            if i == 0 {
              var z := rest[j - 1];
              if z != e {
                var k :| 0 <= k < |xs[1..]| && xs[1..][k] == z;
                assert Lt(xs[0].key, xs[k + 1].key);
              }
            }
          }
        }
      }
      ys
    else
      Earlier(xs[0].key, e.key);
      var ys := [e] + xs;
      assert Ordered(xs) ==> Ordered(ys) by {
        if Ordered(xs) {
          forall i, j | 0 <= i < j < |ys|
            ensures Lt(ys[i].key, ys[j].key)
          {
            if i == 0 && j > 1 { LtTrans(e.key, xs[0].key, xs[j - 1].key); }
          }
        }
      }
      ys
  }

  function DropKey(xs: seq<Entry>, key: Key): (ys: seq<Entry>)
    ensures forall z :: z in ys ==> z in xs
    ensures Ordered(xs) ==> Ordered(ys) && forall z :: z in ys ==> z.key != key
    decreases |xs|
  {
    if xs == [] then []
    else if xs[0].key == key then
      var ys := xs[1..];
      assert Ordered(xs) ==> Ordered(ys) && (forall z :: z in ys ==> z.key != key) by {
        if Ordered(xs) {
          forall i, j | 0 <= i < j < |ys|
            ensures Lt(ys[i].key, ys[j].key)
          {
            assert ys[i] == xs[i + 1] && ys[j] == xs[j + 1];
          }
          forall z | z in ys
            ensures z.key != key
          {
            var k :| 0 <= k < |ys| && ys[k] == z;
            assert Lt(key, xs[k + 1].key);
          }
        }
      }
      ys
    else
      var rest := DropKey(xs[1..], key);
      var ys := [xs[0]] + rest;
      assert Ordered(xs) ==> Ordered(ys) by {
        if Ordered(xs) {
          forall i, j | 0 <= i < j < |xs[1..]|
            ensures Lt(xs[1..][i].key, xs[1..][j].key)
          {}
          forall i, j | 0 <= i < j < |ys|
            ensures Lt(ys[i].key, ys[j].key)
          {
            if i == 0 {
              var z := rest[j - 1];
              assert z in rest && z in xs[1..];
              var k :| 0 <= k < |xs[1..]| && xs[1..][k] == z;
              assert Lt(xs[0].key, xs[k + 1].key);
            }
          }
        }
      }
      ys
  }

  function Find(xs: seq<Entry>, key: Key): (r: Opt<nat>)
    ensures r.Some? ==> r.value < |xs| && xs[r.value].key == key
    ensures r.None? ==> forall i :: 0 <= i < |xs| ==> xs[i].key != key
    decreases |xs|
  {
    if xs == [] then None
    else if xs[0].key == key then Some(0)
    else
      var t := Find(xs[1..], key);
      match t
      case None => None
      case Some(i) => Some(i + 1)
  }

  predicate HasPrefix(k: Key, p: Key) {
    |p| <= |k| && k[..|p|] == p
  }

  function SlashFrom(s: string, i: nat): (r: Opt<nat>)
    requires i <= |s|
    ensures r.Some? ==> i <= r.value < |s| && s[r.value] == '/'
    decreases |s| - i
  {
    if i == |s| then None
    else if s[i] == '/' then Some(i)
    else SlashFrom(s, i + 1)
  }

  // The prefix of `k` up to and including the next `/` after `prefix`.
  function Child(k: Key, prefix: Key): Opt<Key> {
    if !HasPrefix(k, prefix) then None
    else
      var r := SlashFrom(k, |prefix|);
      if r.None? then None
      else
        assert r.value < |k|;
        Some(k[..r.value + 1])
  }

  function Listing(xs: seq<Entry>, prefix: Key, max: nat, i: nat, acc: seq<Key>): (got: seq<Key>)
    requires i <= |xs| && |acc| <= max
    ensures |got| <= max
    decreases |xs| - i
  {
    if i == |xs| || |acc| == max then acc
    else if HasPrefix(xs[i].key, prefix) then
      Listing(xs, prefix, max, i + 1, acc + [xs[i].key])
    else
      Listing(xs, prefix, max, i + 1, acc)
  }

  function Prefixes(xs: seq<Entry>, prefix: Key, i: nat, acc: seq<Key>): seq<Key>
    requires i <= |xs|
    decreases |xs| - i
  {
    if i == |xs| then acc
    else
      var c := Child(xs[i].key, prefix);
      var acc' := if c.Some? && (|acc| == 0 || acc[|acc| - 1] != c.value) then acc + [c.value] else acc;
      Prefixes(xs, prefix, i + 1, acc')
  }

  function Init(self: Pid): State { Held([], false) }

  function Apply(s: State, op: Op): (r: Applied)
    ensures r.state.appendable == s.appendable
    ensures Ordered(s.entries) ==> Ordered(r.state.entries)
  {
    match op
    case Get(key) =>
      (match Find(s.entries, key)
       case None => Applied(s, Got(None))
       case Some(i) =>
         var body := s.entries[i].body;
         Applied(s, Got(Some((body, EtagOf(body))))))
    case GetIfNoneMatch(key, etag) =>
      (match Find(s.entries, key)
       case None => Applied(s, Read(Absent))
       case Some(i) =>
         var body := s.entries[i].body;
         if EtagOf(body) == etag then Applied(s, Read(NotModified))
         else Applied(s, Read(Body(body, EtagOf(body)))))
    case PutIfNoneMatch(key, body) =>
      (match Find(s.entries, key)
       case Some(_) => Applied(s, Failed(PreconditionFailed))
       case None => Applied(Held(Put(s.entries, Entry(key, body)), s.appendable), Written(EtagOf(body))))
    case PutIfMatch(key, body, etag) =>
      (match Find(s.entries, key)
       case Some(i) =>
         if EtagOf(s.entries[i].body) == etag then
           Applied(Held(Put(s.entries, Entry(key, body)), s.appendable), Written(EtagOf(body)))
         else Applied(s, Failed(PreconditionFailed))
       case None => Applied(s, Failed(PreconditionFailed)))
    case AppendIfMatch(key, offset, body, etag) =>
      if !s.appendable then Applied(s, Failed(Unavailable("this store does not append")))
      else
        (match Find(s.entries, key)
         case Some(i) =>
           var have := s.entries[i].body;
           if EtagOf(have) == etag && offset == |have| then
             var joined := have + body;
             Applied(Held(Put(s.entries, Entry(key, joined)), s.appendable), Written(EtagOf(joined)))
           else Applied(s, Failed(PreconditionFailed))
         case None => Applied(s, Failed(PreconditionFailed)))
    case Put(key, body) =>
      Applied(Held(Put(s.entries, Entry(key, body)), s.appendable), Done)
    case Delete(key) =>
      Applied(Held(DropKey(s.entries, key), s.appendable), Done)
    case List(prefix, maxKeys) =>
      Applied(s, Listed(Listing(s.entries, prefix, maxKeys, 0, [])))
    case ListPrefixes(prefix) =>
      Applied(s, Listed(Prefixes(s.entries, prefix, 0, [])))
  }

  function Step(self: Pid, s: State, i: Input<Pid, Msg>, now: nat): (r: Result<Pid, Msg, State>)
    ensures r.state.appendable == s.appendable
    ensures Ordered(s.entries) ==> Ordered(r.state.entries)
  {
    match i
    case Timeout => Result(s, [], Cancel)
    case Request(from, Ask(op)) =>
      var a := Apply(s, op);
      Result(a.state, [Send(from, Reply(a.out))], Keep)
    case Request(_, Reply(_)) => Result(s, [], Keep)
  }

  function World(): Sys<Pid, Msg, State> { Sys(Pids, true, Init, Step) }

  // Boot starts empty, in order, with append off. A step keeps both.
  ghost predicate HeldOk(n: Net<Pid, Msg, State>) {
    && n.procs.Keys == Pids
    && Bucket in n.procs
    && n.procs[Bucket].appendable == Init(Bucket).appendable
    && Ordered(n.procs[Bucket].entries)
  }

  lemma HeldStep(n: Net<Pid, Msg, State>, n': Net<Pid, Msg, State>, a: Action<Pid, Msg>)
    requires HeldOk(n) && NextStep(World(), n, n', a)
    ensures HeldOk(n')
  {
    var w := World();
    assert w.step == Step;
    match a
    case Deliver(p) =>
      var r := Step(p.dst, n.procs[p.dst], Request(p.src, p.msg), n.now);
      assert r.state.appendable == n.procs[p.dst].appendable;
      assert Ordered(r.state.entries);
    case Fire(pid) =>
      var r := Step(pid, n.procs[pid], Timeout, n.now);
      assert r.state.appendable == n.procs[pid].appendable;
      assert Ordered(r.state.entries);
    case _ =>
  }

  lemma HeldTrace(t: seq<Net<Pid, Msg, State>>)
    requires IsTrace(World(), t)
    ensures forall i :: 0 <= i < |t| ==> HeldOk(t[i])
  {
    var w := World();
    forall n | IsInit(w, n) ensures HeldOk(n) {}
    forall n, n', a | HeldOk(n) && NextStep(w, n, n', a) ensures HeldOk(n') {
      HeldStep(n, n', a);
    }
    assert Preserves(w, HeldOk);
    TraceSafety(w, HeldOk, HeldOk, t);
  }
}
