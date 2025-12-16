module SymbDiff where

-- A simple symbolic differentiation module in Haskell

data Expr
  = Const Double
  | Var String
  | Add Expr Expr
  | Sub Expr Expr
  | Mul Expr Expr
  | Pow Expr Int
  deriving (Show)


diff :: Expr -> String -> Expr
diff (Const _) _ = Const 0
diff (Var x) y | x == y = Const 1
               | otherwise = Const 0
diff (Add e1 e2) x = Add (diff e1 x) (diff e2 x)
diff (Sub e1 e2) x = Sub (diff e1 x) (diff e2 x)
diff (Mul e1 e2) x = Add (Mul e1 (diff e2 x)) (Mul (diff e1 x) e2)
diff (Pow e1 n) x = Mul (Const (fromIntegral n)) (Mul (Pow e1 (n-1)) (diff e1 x))


eval :: Expr -> [(String, Double)] -> Double
eval (Const n) _ = n
eval (Var x) env = 
    case lookup x env of
        Just v -> v
        Nothing -> error $ "Variable " <> x <> " not found"
eval (Add e1 e2) env = eval e1 env + eval e2 env
eval (Sub e1 e2) env = eval e1 env - eval e2 env
eval (Mul e1 e2) env = eval e1 env * eval e2 env
eval (Pow e1 n) env = eval e1 env ** fromIntegral n

approxRoot :: Expr -> String -> Double -> [Double]
approxRoot f var x = x:approxRoot f var next
  where
    fx = eval f [(var, x)]
    f'x = eval (diff f var) [(var, x)]
    next = x - fx / f'x


sqroot :: Double -> Double
sqroot y = head $ dropWhile cond (approxRoot f "x" 1)
  where
    cond x = abs (x * x - y) > 1e-12
    f = Sub (Pow (Var "x") 2) (Const y)

-- sqroot 2




{- 

-- Alternative implementation with iteration limit and error threshold, without an infinite list:

approxRoot :: Expr -> String -> Double -> Double -> Double -> [Double]
approxRoot f var x = guess :: approxRoot' f var guess erro
    where
        go x iter | iter >=  = x
        go x iter =
            let fx = eval [(var, x)] f
                f'x = eval [(var, x)] (diff f var)
                next = x - fx / f'x
            in if abs (next - x) < erro
               then next
               else go next (iter + 1)


sqroot :: Double -> Double
sqroot y = approxRoot (Sub (Pow (Var "x") 2) (Const y)) "x" (y / 2) 1e-7 100000000

-}