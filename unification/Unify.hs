module Unify where

import qualified Data.Maybe      as Maybe
-- Hint: You should use Data.HashMap of unordered-constainers instead of Data.Map.
--       this tutorial doesn't depend on except for standard modules of GHC.
--       this is why, this tutorial is not using it.
import qualified Data.Map.Strict as Map

type TypeVariable = Int

-- for example,
--    nat -> nat   = ArrTy NatTy NatTy
--    a -> b       = ArrTy (VarTy n) (VarTy m)     where n /= m
--    a -> a       = ArrTy (VarTy n) (VarTy n)
data Type
  = VarTy       -- variable type
      TypeVariable
  | NatTy       -- a simple type
  | BoolTy      -- a simple type
  | ArrTy       -- function type. T1->T2
      Type      -- T1
      Type      -- T2
  deriving (Eq)

instance Show Type where
  show (VarTy i) = show i
  show NatTy = "nat"
  show BoolTy = "bool"
  show (ArrTy x y) = "(-> " ++ show x ++ " " ++ show y ++ ")"

-- Constraint
data Constraint
  = Equal
      Type
      Type

-- Type error
data Absurd
  = Absurd
      Type -- expected type
      Type -- actual type
  deriving (Show)

-- 型代入
-- 型代入を表す変数としてσやγなどを使う。
-- Map.singleton X T = [X↦T]
-- Map.fromList [(X, T1), (Y, T2)] = [X↦T1, X↦T2]
type Substitution = Map.Map TypeVariable Type

-- subst σ γ = σγ
--
-- σ(X) =
--   {
--     T     where (X↦T) ∈ σ の場合
--     X     where (X↦T) ∉ σ の場合
--   }
-- σ(Nat) = Nat
-- σ(Bool) = Bool
-- σ(T1→T2) = σT1→σT2
--
-- ref: 型システム入門(p249) 22.1 型変数と型代入
subst :: Substitution -> Type -> Type
subst σ (VarTy x) = case Map.lookup x σ of
                      Just t -> t
                      Nothing -> VarTy x
subst _ NatTy = NatTy
subst _ BoolTy = BoolTy
subst σ (ArrTy t1 t2) = ArrTy (subst σ t1) (subst σ t2)

substConstraint :: Substitution -> Constraint -> Constraint
substConstraint σ (Equal t1 t2) = Equal (subst σ t1) (subst σ t2)

-- freeVariables T = FV(T)
freeVariables :: Type -> [TypeVariable]
freeVariables (VarTy v) = [v]
freeVariables NatTy = []
freeVariables BoolTy = []
freeVariables (ArrTy t1 t2) = freeVariables t1 ++ freeVariables t2

-- composeSubst σ γ = σ∘γ
-- subst (composeSubst σ γ) T = (σ∘γ)T = σ(γT)
--
-- ref: 型システム入門(p250)
(∘) :: Substitution -> Substitution -> Substitution
(∘) = Map.union

-- unify(C) = if C = ∅ then []
--            else let {S = T} ∪ C' = C in
--              if S = T
--                then unify(C')
--              else if S = X and X ∉ FV(T)
--                then unify([X↦T]C')∘[X↦T]
--              else if T = X and X ∉ FV(S)
--                then unify([X↦S]C')∘[X↦S]
--              else if S = S1→S2 and T = T1→T2
--                then unify(C' ∪ {S1 = T1, S2 = T2})
--              else fail
--
-- ref: 型システム入門(p257)
unify :: [Constraint] -> Either Absurd Substitution
unify [] = return Map.empty
unify (Equal s t:constraints) = do
  let cond1 = case s of
                VarTy x -> not (elem x (freeVariables t))
                _ -> False
  let cond2 = case t of
                VarTy x -> not (elem x (freeVariables s))
                _ -> False
  let cond3 = case (s, t) of
                (ArrTy _ _, ArrTy _ _) -> True
                _ -> False
  if s == t
    then unify constraints
    else
      if cond1
        then do
          let VarTy x = s
          σ <- unify (map (substConstraint (Map.singleton x t)) constraints)
          return (σ ∘ Map.singleton x t)
        else
          if cond2
            then do
              let VarTy x = t
              σ <- unify (map (substConstraint (Map.singleton x s)) constraints)
              return (σ ∘ Map.singleton x s)
            else
              if cond3
                then do
                  let ArrTy s1 s2 = s
                  let ArrTy t1 t2 = t
                  unify (Equal s1 t1 : Equal s2 t2 : constraints)
              else
                Left (Absurd s t)
