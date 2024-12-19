
{-# LANGUAGE ForeignFunctionInterface #-}
module Add where

import Foreign.C -- Includes mapping of C types to corresponding Haskell types
import Foreign.Ptr (Ptr,nullPtr)
import Foreign.Marshal.Alloc
import Foreign.Storable

-- import a C function with a Haskell signature. This specifies that the foreign
-- code has a C calling convention. GHC will generate code to convert between
-- its internal calling convention and the foreign calling convention. 
foreign import ccall "my_add" my_add :: CInt -> CInt -> Ptr CInt -> IO ()

main = do
  x <- readLn 
  y <- readLn 
  -- The memory is freed automatically after the continuation of alloca returns 
  alloca (\ptr -> do
    my_add x y ptr
    z <- peek ptr 
    print z)

  -- same with malloc
--   ptr <- malloc
--   my_add x y ptr
--   z <- peek ptr 
--   print z
--   free ptr