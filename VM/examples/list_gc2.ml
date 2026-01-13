let rec list_sum l = case l of
  | [] -> 0
  | x::xs -> x + list_sum xs
in
let rec make_list n =
  if n == 0 then [] else n :: (make_list (n - 1))
in
let rec loop n =
  if n == 0 then 0
  else 
    let l = make_list 1000 in 
    list_sum (make_list 1000) + loop (n - 1)
in
print_int (loop 100)
