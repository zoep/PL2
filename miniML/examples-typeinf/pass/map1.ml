let rec map f = fun x ->
  case x of
  | nil -> nil
  | y::ys -> f y :: map f ys
in 
let incr = fun x -> x + 1 in
(map incr (1::2::3::4::nil), 
 map (fun x -> ~ x) (true::false::nil))