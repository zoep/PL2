let f = fun x -> 
  let app = fun f -> fun y -> (f y, x + 42) in
  app
in 
f true (fun x -> x) 3