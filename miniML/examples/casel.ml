let l : list int = 1::2::3::nil[int] in
case l of 
| nil -> 42
| x :: xs -> x + 3