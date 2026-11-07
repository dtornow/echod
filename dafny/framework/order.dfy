// Keys are strings. `<` on a string means "proper prefix", so dictionary
// order is this comparison: character order, then the shorter string.
module Keys {
  predicate Leq(a: string, b: string)
    decreases |a|
  {
    |a| == 0 || (|b| > 0 && (a[0] < b[0] || (a[0] == b[0] && Leq(a[1..], b[1..]))))
  }

  predicate Lt(a: string, b: string) { a != b && Leq(a, b) }

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
    if |a| != 0 && |b| != 0 && a[0] == b[0] { LeqTotal(a[1..], b[1..]); }
  }

  lemma LeqAntisym(a: string, b: string)
    requires Leq(a, b) && Leq(b, a)
    ensures a == b
    decreases |a| + |b|
  {
    if |a| != 0 && |b| != 0 && a[0] == b[0] { LeqAntisym(a[1..], b[1..]); }
  }

  lemma LeqHead(a: string, b: string)
    requires |a| > 0 && |b| > 0 && Leq(a, b)
    ensures a[0] < b[0] || (a[0] == b[0] && Leq(a[1..], b[1..]))
  {}

  lemma LeqTrans(a: string, b: string, c: string)
    requires Leq(a, b) && Leq(b, c)
    ensures Leq(a, c)
    decreases |a| + |b| + |c|
  {
    if |a| > 0 && |b| > 0 && |c| > 0 {
      LeqHead(a, b);
      LeqHead(b, c);
      if a[0] == b[0] && b[0] == c[0] { LeqTrans(a[1..], b[1..], c[1..]); }
    }
  }

  lemma LtTrans(a: string, b: string, c: string)
    requires Lt(a, b) && Lt(b, c)
    ensures Lt(a, c)
  {
    LeqTrans(a, b, c);
    if a == c { LeqAntisym(b, a); }
  }

  lemma Earlier(a: string, b: string)
    requires a != b && !Lt(a, b)
    ensures Lt(b, a)
  {
    LeqTotal(a, b);
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
          if k' == x {
          } else {
            assert k' in rest;
          }
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
      a in keys && b in keys &&
      (forall k' :: k' in keys ==> Leq(a, k')) &&
      (forall k' :: k' in keys ==> Leq(b, k')) ==>
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

  // The keys in dictionary order: least, then the rest.
  function Sorted(keys: set<string>): seq<string>
    decreases |keys|
  {
    if keys == {} then []
    else
      var k := MinKey(keys);
      [k] + Sorted(keys - {k})
  }

  lemma SortedProps(keys: set<string>)
    ensures var s := Sorted(keys);
      |s| == |keys| &&
      (forall x :: x in s <==> x in keys) &&
      (forall i, j | 0 <= i < j < |s| :: Lt(s[i], s[j]))
    decreases |keys|
  {
    if keys != {} {
      var k := MinKey(keys);
      var rest := keys - {k};
      SortedProps(rest);
      var tail := Sorted(rest);
      var s := Sorted(keys);
      assert s == [k] + tail;
      assert |rest| == |keys| - 1;
      forall x | x in s
        ensures x in keys
      {
        if x != k { assert x in tail; }
      }
      forall x | x in keys
        ensures x in s
      {
        if x != k { assert x in rest && x in tail; }
      }
      forall i, j | 0 <= i < j < |s|
        ensures Lt(s[i], s[j])
      {
        if i == 0 {
          assert s[j] in tail && s[j] in rest && s[j] != k;
          assert Leq(k, s[j]);
        } else {
          assert 0 <= i - 1 < j - 1 < |tail|;
          assert s[i] == tail[i - 1] && s[j] == tail[j - 1];
        }
      }
    }
  }
}
