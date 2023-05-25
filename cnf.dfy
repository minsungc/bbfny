/* 
CNFs in Dafny.
CNFs are represented as a sequence of sets of ints.
In particular we don't use arrays because they are immutable.
*/

module CNF {
  type CNF = seq<set<int>>

  const t : CNF := [];
  const f : CNF := [{}];

  // a CNF is true only if it has no clauses.
  predicate is_true (c : CNF) {
    c == t
  }

  // a CNF is false only if it has an empty clause.
  predicate is_false (c : CNF)
  {
    c == f
  }

  // This method simplifies the CNF.
  method Simp (c : CNF, i : int) returns (n : CNF)
    ensures is_true(c) ==> is_true(n)
    ensures is_false(c) ==> is_false(n)
  {
    // c is empty; it is true
    if c == t {return t;}
    if c == f {return f;}
    var k := 0;
    n := [];
    assert |n| == 0;
    assert |n| < |c|;
    while k < |c| 
      invariant 0 <= k <= |c|
    {
      if -i in c[k] {
        var elt := c[k] - {-i};
        // if elt is an empty clause then we derived false.
        if elt == {} {return f;}
        assert elt != {};
        n := n + [elt]; 
      }
      else if i !in c[k] {
        n := n + [c[k]];
      }
      k := k + 1;
    }
    return n;
  }
}