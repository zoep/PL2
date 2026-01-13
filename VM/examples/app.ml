let rec app f = fun x -> f x in
let rec add2 x = x + 2 in
print_int (app add2 40)