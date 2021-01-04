{-# OPTIONS -fno-warn-tabs #-}

module Language where

import Typing

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
