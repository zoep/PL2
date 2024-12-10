let r : ref (() -> ()) = ref (fun (x : ()) -> ()) in
let u : () = r := (fun (x : ()) -> !r ()) in 
!r ()