let r : ref int = ref 1 in
let x : lazy int = lazy (let u : () = r := !r + 1 in !r) in
let f : lazy int -> int = fun (z : lazy int) -> force z * (force z + 1) in
let y : lazy int = lazy (f x) in
let w : lazy () = lazy (let u : () = r := 1234 in ()) in
!r * f y