let rec fold (f : int -> int -> int) : list int -> int -> int = fun (l : list int) -> fun (acc : int) ->
  case l of 
  | nil -> acc
  | x::xs -> fold f xs (f x acc)
in
let add : int -> int -> int = fun (x : int) -> fun (y : int) -> x + y in
fold add (1::2::3::4::nil[int]) 0