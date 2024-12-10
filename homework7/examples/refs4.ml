let r : ref int = ref 4 in
let rec incrn (n : int) : () =
  if n == 0 then ()
  else let i : () = r := !r + 1 in
       incrn (n - 1)
in
let t : () = incrn 7 in
!r