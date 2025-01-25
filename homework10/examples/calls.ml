let rec foo n = n * 2 in 
let rec bar n = n - 1 in 
let rec baz x = foo(bar 42) + 1 in 
print_int (baz 1)