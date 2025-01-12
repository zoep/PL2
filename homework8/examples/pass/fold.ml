let rec fold f = fun l -> fun acc ->
  case l of 
  | [] -> acc
  | x::xs -> fold f l (f x acc)
in
let add = fun x -> fun y -> x + y in
fold add (1::2::3::4::[]) 0