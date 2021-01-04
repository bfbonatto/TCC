{-# OPTIONS -fno-warn-tabs #-}

module Language where

import qualified Data.Map.Strict as Map

data Term = TBool Bool
			| TNum Int
			| TOp Term (Int -> Int -> Int) Term
			| TIf Term Term Term
			| TVar Var
			| TAbs Var Type Term
			| TApp Term Term
			| TEmpty
			| TList Term Term
			| TCase Term Term Term

type Var = String


data Value = VNum Int | VBool Bool | VFun Var Term | VEmpty | VList Value Value


bigstep :: Term -> Maybe Value
bigstep (TBool b) = Just (VBool b)
bigstep (TNum n) = Just (VNum n)

bigstep (TOp t1 op t2) = do
	VNum n1 <- bigstep t1
	VNum n2 <- bigstep t2
	return $ VNum (op n1 n2)

bigstep (TIf t1 t2 t3) = do
	VBool b <- bigstep t1
	if b then bigstep t2 else bigstep t3

bigstep (TAbs v _ t) = Just (VFun v t)

bigstep (TApp t1 t2) = do
	VFun x t <- bigstep t1
	bigstep $ subst x t2 t

bigstep TEmpty = Just VEmpty

bigstep (TList t1 t2) = do
	VNum n <- bigstep t1
	case bigstep t2 of
		Just VEmpty -> Just $ VList (VNum n) VEmpty
		Just l@(VList _ _) -> Just $ VList (VNum n) l
		_ -> Nothing

bigstep (TCase t1 t2 t3) =
	case bigstep t1 of
		Just VEmpty -> bigstep t2
		Just (VList _ _) -> bigstep t3
		_ -> Nothing

bigstep _ = Nothing


subst :: Var -> Term -> Term -> Term
subst _ (TNum n) _ = TNum n
subst _ (TBool b) _ = TBool b
subst x (TOp t1 op t2) arg = TOp (subst x t1 arg) op (subst x t2 arg)
subst x (TIf t1 t2 t3) arg = TIf (subst x t1 arg) (subst x t2 arg) (subst x t3 arg)
subst x (TVar y) arg = if x == y then arg else TVar y
subst _ TEmpty _ = TEmpty
subst x (TList t1 t2) arg = TList (subst x t1 arg) (subst x t2 arg)
subst x (TCase t1 t2 t3) arg = TCase (subst x t1 arg) (subst x t2 arg) (subst x t3 arg)
subst x (TApp t1 t2) arg = TApp (subst x t1 arg) (subst x t2 arg)
subst x t@(TAbs y typeY body) arg = if x == y then t else TAbs y typeY (subst x body arg)

data Type = TypeNat | TypeBool | TypeList | TypeFun Type Type deriving Eq

type Context = Map.Map Var Type

typecheck :: Context -> Term -> Maybe Type
typecheck _ (TBool _) = Just TypeBool
typecheck _ (TNum _) = Just TypeNat
typecheck g (TOp t1 _ t2) = do
	TypeNat <- typecheck g t1
	TypeNat <- typecheck g t2
	return TypeNat

typecheck g (TIf t1 t2 t3) = do
	TypeBool <- typecheck g t1
	x <- typecheck g t2
	y <- typecheck g t3
	if x == y then return x else Nothing

typecheck g (TVar x) = g Map.!? x

typecheck g (TAbs x t body) = do
	let g' = Map.insert x t g
	t' <- typecheck g' body
	return $ TypeFun t t'

typecheck g (TApp t1 t2) = do
	TypeFun type1 type2 <- typecheck g t1
	t <- typecheck g t2
	if type1 == t then return type2 else Nothing

typecheck _ TEmpty = Just TypeList

typecheck g (TList t1 t2) = do
	TypeNat <- typecheck g t1
	TypeList <- typecheck g t2
	return TypeList

typecheck g (TCase t1 t2 t3) = do
	TypeList <- typecheck g t1
	type2 <- typecheck g t2
	type3 <- typecheck g t3
	if type2 == type3 then return type2 else Nothing
