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
diff (Var x) var
    | x == var  = Const 1
    | otherwise = Const 0
diff (Add u v) var = Add (diff u var) (diff v var)
diff (Sub u v) var = Sub (diff u var) (diff v var)
diff (Mul u v) var = Add (Mul (diff u var) v) (Mul u (diff v var))
diff (Pow u n) var = Mul (Mul (Const (fromIntegral n)) (Pow u (n - 1))) (diff u var)


expr1 :: Expr
expr1 = Add (Pow (Var "x") 3)
            (Mul (Const 2) (Var "x"))

-- >>> diff expr1 "x" 
-- Add (Mul (Mul (Const 3.0) (Pow (Var "x") 2)) (Const 1.0)) (Add (Mul (Const 0.0) (Var "x")) (Mul (Const 2.0) (Const 1.0)))


eval :: [(String, Double)] -> Expr -> Double
eval _ (Const c) = c
eval env (Var x) = case lookup x env of
                        Just v  -> v
                        Nothing -> error ("Variable " ++ x ++ " not found in environment")
eval env (Add u v) = eval env u + eval env v
eval env (Sub u v) = eval env u - eval env v
eval env (Mul u v) = eval env u * eval env v
eval env (Pow u n) = eval env u ** fromIntegral n

-- >>> eval [("x", 2)] expr1
-- 12.0


approxRoot :: Expr -> String -> Double -> [Double]
approxRoot f var x = x:approxRoot f var next
  where
    fx = eval [(var, x)] f
    f'x = eval [(var, x)] (diff f var)
    next = x - fx / f'x

sqRoot :: Double -> Double
sqRoot y = head . dropWhile notClose $ approxRoot (Sub (Pow (Var "x") 2) (Const y)) "x" 1
  where
    notClose x = abs (x*x - y) > 1e-12

-- >>> sqRoot 9     
-- 3.0

-- >>> sqRoot 25
-- 5.0

-- >>> sqRoot 42
-- 6.48074069840786


{- 

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
