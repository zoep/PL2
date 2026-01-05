let rec map f = fun x ->
  case x of
  | nil -> nil
  | y::ys -> f y :: map f ys
in map