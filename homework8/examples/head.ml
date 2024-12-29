let head = fun l -> fun y ->
  case l of
  | [] -> y
  | x::xs -> x
in
(head (1::2::3::[]) 0, head (true::false::[]) false)