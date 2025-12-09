let rec fib (n : int) : int =
  if n == 0 then n
  else if n == 1 then 1
  else fib (n - 1) + fib (n - 2)
in fib 6