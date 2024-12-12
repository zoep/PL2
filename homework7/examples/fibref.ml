let curr : ref int = ref 0 in
let next : ref int = ref 1 in
let rec fib (n : int) : () =
  if n == 0 then ()
  else 
    let temp : int = !next in 
    let x : () = next := !curr + !next in
    let y : () = curr := temp in
    fib (n - 1)
in
let t : () = fib 8 in 
!curr
