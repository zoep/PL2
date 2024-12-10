module MiniML.Values where

import qualified Data.Map as M

import MiniML.Syntax

-- Values. The result of evaluation.
type Loc = Integer

data Value =
  -- A memory location
    Memloc Loc
  -- A unit value
  | VUnit
  -- A integer value
  | VNum Integer
  -- A boolean value
  | VBool Bool
  -- A closure. It must be annotated with the argument type and the result type
  -- so that values can be typechecked. The evaluation function should propagate
  -- this information that will be available as annotations in the input
  -- program.
  | VClo Env String String Type {- argument type -} Type {- result type -} Exp
  -- A pair
  | VPair Value Value
  -- A left injection
  | VInl Type Value
  -- A right injection
  | VInr Type Value
  deriving (Eq,Show)

-- The evaluation environment. Maps variables to values.
type Env = M.Map String Value

-- The execution "heap", mapping memory location to values.
type Store = M.Map Loc Value