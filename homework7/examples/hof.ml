let add : int -> int -> int = fun (x : int) -> fun (y : int) -> x + y in
let inc : int -> int = add 1 in
inc 5