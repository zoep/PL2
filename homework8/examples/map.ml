let rec map f = fun x ->
  case x of
  | [] -> []
  | y::ys -> f x :: map f ys
in map