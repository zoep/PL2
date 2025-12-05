{-# LANGUAGE ForeignFunctionInterface #-}

module Main where

import Prelude hiding (sin)

import Foreign.C -- get the C types
import Foreign.Ptr (Ptr,nullPtr)

-- pure function
foreign import ccall "sin" c_sin :: CDouble -> CDouble
sin :: Double -> Double
sin d = realToFrac (c_sin (realToFrac d))

-- impure function
foreign import ccall "time" c_time :: Ptr a -> IO CTime
getTime :: IO CTime
getTime = c_time nullPtr

main = do
  print . sin =<< readLn
  print =<< getTime


-- {-# LANGUAGE CApiFFI #-}
-- module FFI where

-- import Foreign
-- import Foreign.C.Types

-- foreign import capi my_add :: CInt -> CInt -> CInt


-- main :: IO () 
-- main = 
--   putStrLn . show $ my_add 21 21