// Swap the values of two variables
method Swap(a: int , b: int) returns (x: int , y: int) 
  ensures x == b && y == a
{
  x := b; 
  y := a; 
}

// Sort a tuple of three integers
method Sort(a: int, b: int, c: int) returns (x: int, y: int, z: int) 
  ensures x <= y <= z && multiset{a, b, c} == multiset{x, y, z}
{  
  x, y, z := a, b, c;
  if z < y { y, z := z, y; } 
  if y < x { x, y := y, x; } 
  if z < y { y, z := z, y; }
}

// Binary search
predicate sorted(a: array<int>)
  reads a
{
  forall j, k :: 0 <= j < k < a.Length ==> a[j] <= a[k]
}

method BinarySearch(a: array<int>, value: int) returns (index: int)
  requires sorted(a)
  ensures 0 <= index ==> index < a.Length && a[index] == value
  ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != value
{
  var low, high := 0, a.Length;
  while low < high
    invariant 0 <= low <= high <= a.Length
    invariant forall i ::
      0 <= i < a.Length && !(low <= i < high) ==> a[i] != value
  {
    var mid := (low + high) / 2;
    if a[mid] < value {
      low := mid + 1;
    } else if value < a[mid] {
      high := mid;
    } else {
      return mid;
    }
  }
  return -1;
}

// Sum of arithmetic progression
module ArithmeticProgression {
  
  // Compute 1 + 2 + ... + n
  function sum(n: nat) : nat
  decreases n
  { 
    if n == 0 then 0 else n + sum(n-1)
  }

  // A lemma proved by induction
  lemma sum_lemma(n : nat) 
    ensures (sum(n) == n * (n + 1)/2)
  {
    if n == 0 { } // base case
    else { 
      // with this recursive call we give a hint to the solver to use the 
      // the _induction hypothesis_, which is the lemma we are trying to prove with n - 1 as an argument.
      // From this it can derive it for n, and we are done.
      sum_lemma(n-1); 
    }
  }

  // Compute 1 + 2 + ... + n, quickly
  method FastSum(n: nat) returns (res: nat)
  ensures res == sum(n) // ensures that the result is correct
  {
    sum_lemma(n); // Instruct the solver to use the [sum_lemma]. 
                  // This "ghost method" call will be compiled away.
    res := (n * (n + 1))/2;
  }
}

module GeometricProgression {
  // compute 2^n
  function pow2(n: nat) : nat
  decreases n
  { 
    if n == 0 then 1 else 2 * pow2(n-1)
  }

  // compute 2^1 + .... + 2^n
  function sum(n:nat) : nat 
  decreases n
  {
    if n == 0 then 1  else pow2(n) + sum(n-1)
  }

  
  // A lemma proved by induction, unused
  lemma pow_mul_lemma(n : nat, m:nat) 
    ensures (pow2(n)*pow2(m) == pow2(n+m))
  {
    if n == 0 { }
    else { 
      pow_mul_lemma(n-1,m);  // use the IH
    }
  }

  // A lemma proved by induction
  lemma sum_lemma(n : nat) 
    ensures (sum(n) == pow2(n+1)-1)
  {
    if n == 0 { }
    else { 
      sum_lemma(n-1); // use the IH
    }
  }
  
  // compute n^2
  method Pow2(n:nat) returns (x:int)
	  ensures x == pow2(n) // functional specification
  { x := 1;
	  var i := n;

	  while i != 0
		invariant x == pow2(n-i)
	  { x := 2 * x ; 
        i := i - 1; }
} 

  // Compute 2^1 + .... + 2^n, quickly
  method FastSum(n: nat) returns (res: nat)
  ensures res == sum(n) // ensures that the result is correct
  {
    sum_lemma(n); // Instruct the solver to use the [sum_lemma]. 
                  // Since lemmas are "ghost methods", this call will be compiled away
    res := Pow2(n+1);
    res := res - 1;
  }
}

// Sum of geometric progression, general form. 
// WORK IN PROGRESS. PLEASE INGORE.
module GeometricProgressionGeneral {
  // Compute the power
  function pow(b: nat, e: nat) : nat
  decreases e
  { 
    if e == 0 then 1 else b * pow(b, e - 1)
  }

  // 
  lemma pow_mul_lemma(b:nat,n:nat,m:nat) 
    ensures (pow(b,n)*pow(b,m) == pow(b,n+m))
  {
    if n == 0 { }
    else { pow_mul_lemma(b,n-1,m); }
  }

  // compute a*r^1 + .... + a*r^n
  function sum(a:nat,r:nat,n:nat) : nat 
  decreases n
  {
    if n == 0 then a else a*pow(r,n) + sum(a,r,n-1)
  }

  lemma sum_lemma(a:nat,r:nat,n:nat) 
    requires r > 1
    requires n == 0
    ensures (sum(a,r,n) == a*(pow(r,n+1)-1)/(r-1))
  {
    if n == 0 { 
      // assert (a*(pow(r,1)-1)/(r-1) == a*(r-1)/(r-1));
      // assert (a*(r-1)/(r-1) == a*((r-1)/(r-1))); // why not?  
      // assert (a*(r-1)/(r-1) == a);
      // assert (sum(a,r,n) == a);
      // assert (a*(pow(r,1)-1)/(r-1) == a);
      assume {:axiom} (sum(a,r,n) == a*(pow(r,n+1)-1)/(r-1)); // this is like an "admit" in Coq
    }
    // else {  
      /*     
      sum_lemma(a,r,n-1); 
      assert(sum(a,r,n-1) == a*(pow(r,n)-a)/(r-1));
      // assume(sum(a,r,n) == a*(pow(r,n+1)-a)/(r-1));
      pow_mul_lemma(r,1,n); */
    // }
  }
}