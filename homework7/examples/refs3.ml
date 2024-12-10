let r : ref int = ref 4 in
let clo : int -> () = (fun (n : int) -> r := n) in
let t : () = clo 7 in
!r