
{-# LANGUAGE ForeignFunctionInterface #-}
module Add where

import Foreign.C -- Includes mapping of C types to corresponding Haskell types

-- import a C function with a Haskell signature. This specifies that the foreign
-- code has a C calling convention. GHC will generate code to convert between
-- its internal calling convention and the foreign calling convention. 
foreign import ccall "my_add" my_add :: CInt -> CInt -> CInt

-- A wrapper that converts from and to CInt
add' :: Int -> Int -> Int
add' x y = fromIntegral $ my_add (fromIntegral x) (fromIntegral y)

main = do
  x <- readLn 
  y <- readLn
  let f = my_add x 
  print $ f y
