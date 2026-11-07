// Keys are strings. `<` on a string means "proper prefix", so dictionary
// order is this comparison: character order, then the shorter string.
module Keys {
  predicate Leq(a: string, b: string)
    decreases |a|
  {
    |a| == 0 || (|b| > 0 && (a[0] < b[0] || (a[0] == b[0] && Leq(a[1..], b[1..]))))
  }

  predicate Lt(a: string, b: string) { a != b && Leq(a, b) }

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
}
