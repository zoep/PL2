let f = fun x -> 
  let app = fun f -> fun y -> (f y, x + 42) in
  let z = ~ x in
  app
in 
f 11 (fun x -> x) 3