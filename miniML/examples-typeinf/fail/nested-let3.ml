fun x -> 
  let f = fun y -> if true then x else y in 
  (f 42, ~ x)