let map = fun f -> fun x -> (f (fst x), f (snd x))
in (map (fun x -> x + 1) (1,2), 
    map (fun x -> x || true) (true, false))