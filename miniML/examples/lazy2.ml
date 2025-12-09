let r : ref int = ref 1 in
let x : lazy int = lazy (let u : () = r := !r + 5 in !r) in
let y : lazy () = lazy (r := 24) in
let f : lazy int -> int = fun (x : lazy int) -> force x * (force x + 1) in
!r * f x