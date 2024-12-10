let x : ref int = ref 42 in
let z : () = x := !x - 21 in
!x + 12