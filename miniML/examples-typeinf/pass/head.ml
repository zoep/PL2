let head = fun l -> fun y ->
  case l of
  | nil -> y
  | x::xs -> x
in
(head (1::2::3::nil) 0, head (true::false::nil) false)