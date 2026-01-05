module MiniML.Infer where

import qualified Data.Map as M
import Control.Monad.State
import Control.Monad (when)
import Data.List (nub)
import Prettyprinter
import Prettyprinter.Render.Text (renderStrict)
import qualified Data.Text as T (unpack)
import qualified Data.Text.IO as TIO (putStrLn)

import MiniML.Syntax
import MiniML.Error
import MiniML.Print


-- A type scheme is either a monomorphic type or a polymorphic type with
-- universally quantified type variables.
data TypeScheme = Type Type
                | Forall [String] Type
   deriving (Eq,Show)

-- | Pretty-print a type scheme
prettyTypeScheme :: TypeScheme -> Doc ann
prettyTypeScheme (Type ty) = prettyType 0 ty
prettyTypeScheme (Forall [] ty) = prettyType 0 ty
prettyTypeScheme (Forall xs ty) =
  pretty "forall " <> hsep (map pretty xs) <> pretty ". " <> prettyType 0 ty

-- A typing context maps variable names to type schemes
type Ctx = M.Map String TypeScheme

-- A type constraint is a pair of types that must be equal, along with the
-- position in the source code where the constraint arose, for error reporting.
type Constraints = [(Type, Type, Posn)]

-- A substitution maps type variables to types
type Substitution = M.Map String Type

-- Type inference error
typeError :: Posn -> String -> Error a
typeError p msg = Left (p, msg)

-- Show a type as a string
showTypeScheme :: TypeScheme -> String
showTypeScheme = T.unpack . renderStrict . layoutSmart optsShow . prettyTypeScheme

-- Print a type in stdout
printTypeScheme :: TypeScheme -> IO ()
printTypeScheme = TIO.putStrLn . renderStrict . layoutSmart optsPrint . prettyTypeScheme

-- Constraint unification
unify :: Constraints -> Error Substitution
unify = error "Implement me!"

-- Top-level type inference function. You will need to also define a type
-- inference fuction that works in a typing context and returns the inferred
-- type along with the generated constraints. You may need to define a monad for
-- generating fresh type variables, handling errors, propagating constraints,
-- etc. This function should then call that one with an empty context, unify the
-- resulting constraints, and generalize the resulting type.
inferTypeTop :: Exp -> Error TypeScheme
inferTypeTop e = error "Implement me!"

-- Various helper functions

-- Apply a substitution to a type
applySubst :: Type -> Substitution -> Type
applySubst TUnit _ = TUnit
applySubst TInt _ = TInt
applySubst TBool _ = TBool
applySubst (TArrow t1 t2) subst = TArrow (applySubst t1 subst) (applySubst t2 subst)
applySubst (TProd t1 t2) subst = TProd (applySubst t1 subst) (applySubst t2 subst)
applySubst (TSum t1 t2) subst = TSum (applySubst t1 subst) (applySubst t2 subst)
applySubst (TList t) subst = TList (applySubst t subst)
applySubst (TVar a) subst = case M.lookup a subst of
  Just ty -> ty
  Nothing -> TVar a

-- Apply a substitution to a set of constraints
applySubstCnstr :: Constraints -> Substitution -> Constraints
applySubstCnstr cnstr subst =
  (\(t1, t2, pos) -> (applySubst t1 subst, applySubst t2 subst, pos)) <$> cnstr

-- Apply a substitution to a type scheme
applySubstTypeScheme :: TypeScheme -> Substitution -> TypeScheme
applySubstTypeScheme (Type t) subst = Type $ applySubst t subst
applySubstTypeScheme (Forall xs t) subst = Forall xs $ applySubst t (foldr M.delete subst xs)

-- Apply a substitution to a typing environment
applySubstEnv :: Ctx -> Substitution -> Ctx
applySubstEnv ctx subst = M.map (flip applySubstTypeScheme subst) ctx


-- Extend a substitution. Essentially the composition of a substitution subst
-- with a singleton substitution [x -> typ].
extendSubst :: Substitution -> String -> Type -> Substitution
extendSubst = error "Implement me!"

-- Generalize a the free type variables in a type
generalize :: Ctx -> Type -> TypeScheme
generalize = error "Implement me!"


rename :: (String, String) -> Type -> Type
rename _ TUnit = TUnit
rename _ TInt = TInt
rename _ TBool = TBool
rename subst (TArrow t1 t2) = TArrow (rename subst t1) (rename subst t2)
rename subst (TProd t1 t2) = TProd (rename subst t1) (rename subst t2)
rename subst (TSum t1 t2) = TSum (rename subst t1) (rename subst t2)
rename subst (TRef t) = TRef (rename subst t)
rename subst (TList t) = TList (rename subst t)
rename (x, y) (TVar a) = if x == a then TVar y else TVar a
rename subst (TLazy t) = TLazy (rename subst t)


occursFreeType :: String -> Type -> Bool
occursFreeType x (TVar a) = x == a
occursFreeType _ TUnit = False
occursFreeType _ TInt = False
occursFreeType _ TBool = False
occursFreeType x (TSum t1 t2) = occursFreeType x t1 || occursFreeType x t2
occursFreeType x (TProd t1 t2) = occursFreeType x t1 || occursFreeType x t2
occursFreeType x (TArrow t1 t2) = occursFreeType x t1 || occursFreeType x t2
occursFreeType x (TRef t) = occursFreeType x t
occursFreeType x (TList t) = occursFreeType x t
occursFreeType x (TLazy t) = occursFreeType x t

occursFreeTypeScheme :: String -> TypeScheme -> Bool
occursFreeTypeScheme x (Type ty) = occursFreeType x ty
occursFreeTypeScheme x (Forall ys ty) = notElem x ys && occursFreeType x ty

occursFreeCtx :: String -> Ctx -> Bool
occursFreeCtx x =
  M.foldr ((||) . occursFreeTypeScheme x) False


{- Question (10 points)

The language in this assignment has both polymorphic types and references.

Write a well-typed example program in MiniML that demonstrates why naive
combination of polymorphic types and references can lead to type unsoundness.

Explain in a few sentences why your example leads to a type error at runtime.

What modifications to the type system would be necessary to prevent this?


Answer:

-}