fun x -> 
  let f = fun y -> if true then y else x in 
  (f 42, ~ x)