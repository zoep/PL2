let rec map (f : int -> int) : (int * int -> int * int)= 
  fun (p : int * int) -> (f (fst p), f (snd p))
in map (fun (x : int) -> x + 1) (1,2)