let rec read_list n = 
  if n == 0 then []
  else
    let x = read_int () in
    x :: read_list (n - 1)
in
let rec print_list l =
  case l of
  | [] -> ()
  | x :: xs -> 
    let _z = print_int x in
    print_list xs
in
let rec list_sum l = case l of
  | [] -> 0
  | x::xs -> x + list_sum xs
in
let l = read_list 10 in
let p = print_list l in
print_int (list_sum l)