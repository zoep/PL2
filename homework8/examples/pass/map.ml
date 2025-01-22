let rec map f = fun x ->
  case x of
  | [] -> []
  | y::ys -> f y :: map f ys
in map
