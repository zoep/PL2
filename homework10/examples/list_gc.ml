let rec make_list n =
  if n == 0 then [] else n :: (make_list (n - 1))
in
print_int ((let l = make_list 1000 in 1) + 
  (let l = make_list 1000 in 1) +
  (let l = make_list 1000 in 1) +
  (let l = make_list 1000 in 1) +
  (let l = make_list 1000 in 1) +
  (let l = make_list 1000 in 1) +
  (let l = make_list 1000 in 1) +
  (let l = make_list 1000 in 1) +
  (let l = make_list 1000 in 1) +
  (let l = make_list 1000 in 1) +
  (let l = make_list 1000 in 1))