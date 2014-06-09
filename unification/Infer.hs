module Infer where

-- Hint: You should use Data.HashMap of unordered-constainers instead of Data.Map.
--       this tutorial doesn't depend on except for standard modules of GHC.
--       this is why, this tutorial is not using it.
import qualified Data.Map.Strict as Map

import qualified Control.Monad.State as State
import qualified Unify

type Variable = String

data Term
  = NatT Int
  | BoolT Bool
  | VarT Variable
  | AbsT Variable Term
  | AppT Term Term
  deriving (Show)

data TypedTerm
  = NatTT Int Unify.Type
  | BoolTT Bool Unify.Type
  | VarTT Variable Unify.Type
  | AbsTT Variable TypedTerm Unify.Type
  | AppTT TypedTerm TypedTerm Unify.Type
  deriving (Show)

type VarList = [Unify.TypeVariable]

data InfererState
  = InfererState
    {
      environment :: Map.Map Variable Unify.Type
    , constraints :: [Unify.Constraint]
    , freshVariables :: VarList
    }

type Inferer a = State.State InfererState a

typeof :: TypedTerm -> Unify.Type
typeof (NatTT _ t) = t
typeof (BoolTT _ t) = t
typeof (VarTT _ t) = t
typeof (AbsTT _ _ t) = t
typeof (AppTT _ _ t) = t

mapTy :: (Unify.Type -> Unify.Type) -> TypedTerm -> TypedTerm
mapTy f (NatTT i t) = NatTT i (f t)
mapTy f (BoolTT b t) = BoolTT b (f t)
mapTy f (VarTT x t) = VarTT x (f t)
mapTy f (AbsTT x y t) = AbsTT x (mapTy f y) (f t)
mapTy f (AppTT x y t) = AppTT (mapTy f x) (mapTy f y) (f t)

gensym :: Inferer Unify.TypeVariable
gensym = do
  InfererState _ _ l <- State.get
  let i = head l
  State.modify (\s -> s { freshVariables = tail l })
  return i

getTypeOfVariable :: Variable -> Inferer Unify.Type
getTypeOfVariable x = do
  InfererState e _ _ <- State.get
  case Map.lookup x e of
    Just t -> return t
    Nothing -> do
      i <- gensym
      let t = Unify.VarTy i
      State.modify (\s -> s { environment = Map.insert x t e })
      return t

assignTypeAndMkConstraints :: Term -> Inferer TypedTerm
assignTypeAndMkConstraints (NatT i) = return (NatTT i Unify.NatTy)
assignTypeAndMkConstraints (BoolT b) = return (BoolTT b Unify.BoolTy)
assignTypeAndMkConstraints (VarT x) = do
  t <- getTypeOfVariable x
  return (VarTT x t)
assignTypeAndMkConstraints (AbsT x t) = do
  InfererState e _ _ <- State.get
  i <- gensym
  let paramTy = Unify.VarTy i
  State.modify (\s -> s { environment = Map.insert x paramTy e })
  t' <- assignTypeAndMkConstraints t
  State.modify (\s -> s { environment = e })
  return (AbsTT x t' (Unify.ArrTy paramTy (typeof t')))
assignTypeAndMkConstraints (AppT t m) = do
  i <- gensym
  let retType = Unify.VarTy i
  t' <- assignTypeAndMkConstraints t
  m' <- assignTypeAndMkConstraints m
  InfererState _ c _ <- State.get
  State.modify (\s -> s { constraints = Unify.Equal (typeof t') (Unify.ArrTy (typeof m') retType) : c })
  return (AppTT t' m' retType)

initialState :: InfererState
initialState
  = InfererState
    { environment = Map.empty
    , constraints = []
    , freshVariables = [0..]
    }

inferType :: Term -> Either Unify.Absurd TypedTerm
inferType t = do
  let (tt, InfererState _ c _) = State.runState (assignTypeAndMkConstraints t) initialState
  case Unify.unify c of
    Right σ -> do
      let tt' = mapTy (Unify.subst σ) tt
      Right tt'
    Left absurd ->
      Left absurd
