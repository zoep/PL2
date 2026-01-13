let rec list_sum l = case l of
  | [] -> 0
  | x::xs -> x + list_sum xs
in
let rec make_list n =
  if n == 0 then [] else n :: (make_list (n - 1))
in
print_int (list_sum (make_list 1000))