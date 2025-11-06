// Purely functional Fibonacci
function fib(n: nat) : nat
{
  if n == 0 then 0
  else if n == 1 then 1
  else fib(n - 1) + fib(n - 2)
}

// Imperative computation of nth Fibonacci
method ComputeFib(n: nat) returns (b: nat)
requires true // can be ommited
ensures (b == fib(n)) // functional specification for the imperative Fibonacci computation
{
  if n == 0 { return 0; }
  var i := 1;
  
  var a := 0;
  b := 1;
  while i < n
    invariant (b == fib(i))
    invariant (a == fib(i - 1))
    invariant (i <= n)
  {
    a, b := b, a + b;
    i := i + 1;
  }

}

method Main()
{
  var n := ComputeFib(11);
  print "fib(11) = ", n, "\n";
}