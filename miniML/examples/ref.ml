let r : ref int = ref 42 in
let z : () = r := !r + 1 in
let z : () = r := !r + 2 in
let f : ref int -> int = fun (x : ref int) -> let u : () = x := !x + 3 in !x in
(f r) + (f r)