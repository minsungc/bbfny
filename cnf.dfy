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

  function NoDupes (s : set<int>) : bool
  {
    
  }
  method Abs(i : int) returns (j : int) 
    ensures j >= 0;
    ensures i >= 0 ==> i == j && i < 0 ==> j == -i;
    ensures j >= i;
    ensures i == j || i == -j;
  {
    if i >= 0 {return i;} else {return -i;}
  }

  // method MaxLitInClause(s : set<int>) returns (j : int) 
  //   requires s != {}
  // {
  //   var ss := s;
  //   j := 0;
  //   assert ss == s;
  //   while ss != {} 
  //     decreases |ss|
  //   {
  //     var i: int :| i in ss;
  //     var poss := Abs(i);
  //     assert poss == i || -poss == i;
  //     assert poss in ss || -poss in ss;
  //     if poss > j {
  //       j := poss;
  //       assert j in ss || -j in ss;
  //     }
  //     assert j >= i ;
  //     ss := ss - {i};
  //     assert s;
  //     print(s);
  //     assert i !in ss;
  //   }
  // }


  // This method is unit propagation.
  // It's a little smarter in the sense that
  // it short circuits when encountering an empty clause.
  // The responsibility is on the programmer to not have clauses like (1,-1).
  method UnitProp (c : CNF, i : int) returns (n : CNF)
    requires forall k :: 0 <= k < c.Length ==> NoDupes(c[k])
    ensures is_true(c) ==> is_true(n)
    ensures is_false(c) ==> is_false(n)
    ensures |n| <= |c|;
  {
    // c is empty; it is true
    if c == t {return t;}
    if c == f {return f;}
    var k := 0;
    n := [];
    assert |n| == 0;
    assert |n| < |c|;

    while k < |c| 
      decreases |c|-k;
      decreases |c|-|n|;
      invariant |n| <= k && 0<= k <= |c|;
      invariant |n| <= |c|;
    {
      if -i in c[k] {
        var elt := c[k] - {-i};
        assert |elt| <= |c[k]|;
        // if elt is an empty clause then we derived false. short circuit
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

method Main() {
  var s := {1, -5, 2};
  var y := CNF.MaxLitInClause(s);
  print(s);
}