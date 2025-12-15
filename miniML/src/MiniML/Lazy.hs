module MiniML.Lazy where
{- 
Student name: 
Student ID:
-}

import MiniML.Syntax

implementLazy :: Exp -> Exp
implementLazy (Prim p "lazy" e) = error "TODO!"
implementLazy (Prim p "force" e) = error "TODO!"
implementLazy _ = error "TODO!"

{- Question1:  How would you define a stream (lazy list)?
Answer: 

Question 2: How would you implement a lazy computation of the n-th Fibonacci number?
Answer: 

-}