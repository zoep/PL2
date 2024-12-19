module Time where 

-- adapted from https://wiki.haskell.org/FFI_complete_examples

import Foreign.C -- get the C types
import Foreign.Ptr (Ptr,nullPtr)

-- time_t time( time_t *second );

-- impure function
foreign import ccall "time" c_time :: Ptr a -> IO CTime

-- impure function
foreign import ccall "sleep" c_sleep :: CInt -> IO CInt

foreign import ccall "difftime" tminus :: CTime -> CTime -> CDouble

getTime :: IO CTime
getTime = c_time nullPtr

main = do
  t1 <- getTime 
  _ <- c_sleep 5
  t2 <- getTime 
  print (tminus t2 t1)