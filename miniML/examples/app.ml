let rec app (f : int -> int) : int -> int = fun (x : int) -> f x in
let rec add2 (x : int) : int = x + 2 in
app add2 3