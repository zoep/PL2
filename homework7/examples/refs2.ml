let x : ref int -> () = fun (r : ref int) -> r := !r + 1 in
let z : ref int = ref 10 in
let s : () = x z in
!z