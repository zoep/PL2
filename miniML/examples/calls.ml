let rec foo (n : int) : int = n * 2 in 
let rec bar (n : int) : int = n - 1 in 
let rec baz (x : int) : int = foo(bar 42) + 1 in 
baz 1