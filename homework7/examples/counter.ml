let counter : () -> int = 
  let r : ref int = ref 0 in
  (fun (x : ()) -> 
    let z : int = !r in
    let y : () = r := !r + 1 in
    z)
in
(counter (), (counter (), counter ())) 