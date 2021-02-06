{-# OPTIONS -fno-warn-tabs #-}

module Language where

import Control.Monad.State
import Data.List

data Exp =
	  ENum Int
	| EBinOp Exp BinOp Exp
	| EUnOp UnOp Exp
	| EBool Bool
	| ECond Exp Exp Exp
	| EVar Var
	| EApp FunId Exp

type Var           = Int
data BinOp         = NtNB NatToNatBin | BtBB BoolToBoolBin | NtBB NatToBoolBin
data NatToNatBin   = Add | Sub | Mult
data NatToBoolBin  = Eq | LessEq
data BoolToBoolBin = And | Or
data UnOp          = Not

class TypedOperation a where
	getTypes :: a -> [Type]

resultType :: (TypedOperation op) => op -> Type
resultType = last . getTypes

instance TypedOperation BinOp where
	getTypes (NtNB op) = getTypes op
	getTypes (BtBB op) = getTypes op
	getTypes (NtBB op) = getTypes op

instance TypedOperation NatToNatBin where
	getTypes _ = [TInt, TInt, TInt]

instance TypedOperation NatToBoolBin where
	getTypes _ = [TInt, TInt, TBool]

instance TypedOperation BoolToBoolBin where
	getTypes _ = [TBool, TBool, TBool]

instance TypedOperation UnOp where
	getTypes _ = [TBool, TBool]

typeMach :: (TypedOperation op) => op -> [Type] -> Bool
typeMach op l = getTypes op == l

finalType :: (TypedOperation op) => op -> Type
finalType = last . getTypes

-- I wanted to use Vars in every variable-only position, but, during
-- the transformation into Share-Let-Normal form we need to consult
-- the free variables of sub-expressions, and letting arbitrary exps
-- in variable-only positions simplify the transformation a lot
data TExp =
	  TENum Int
	| TEBinOp TExp BinOp TExp Type
	| TEUnOp UnOp TExp Type
	| TEBool Bool
	| TECond TExp TExp TExp Type
	| TEVar Var Type
	| TEApp FunId TExp Type
	| TEShare Var Var Var TExp Type -- TEShare y y' x e T means x ~> y,y'
	| TELet Kind Var TExp TExp Type -- TELet kind x e e'  means (free)let x be e in e'

data Type  = TInt | TBool deriving Eq
data Kind  = Free | Normal
type FunId = String
-- Disallowing function declaration inside expressions simplifies the analysis

type SLTState = Int

freshVar :: State SLTState Var
freshVar = do
	n <- get
	put $ n+1
	return n

freshVars :: Int -> State SLTState [Var]
freshVars n = sequence [ freshVar | _ <- [1..n] ]

freeVars :: TExp -> [Var]
freeVars (TENum _)            = []
freeVars (TEBool _)           = []
freeVars (TEVar x _)          = [x]
freeVars (TEApp _ e _)        = freeVars e
freeVars (TEUnOp _ e _)       = freeVars e
freeVars (TEBinOp e1 _ e2 _)  = freeVars e1 `union` freeVars e2
freeVars (TELet _ x e1 e2 _)  = (freeVars e1 `union` freeVars e2) \\ [x]
freeVars (TECond e e1 e2 _)   = freeVars e `union` freeVars e1 `union` freeVars e2
freeVars (TEShare y y' x e _) = [x] `union` (freeVars e \\ [y,y'])

freeLets :: Monad m => [(Var, TExp)] -> TExp -> Type -> m TExp
freeLets [] exp _             = return exp
freeLets ((x,e):lets) exp typ = do
	exp' <- freeLets lets exp typ
	return $ TELet Free x e exp' typ

transform :: Exp -> State SLTState TExp
transform (ENum n)          = return $ TENum n
transform (EBool b)         = return $ TEBool b
transform (EBinOp e1 op e2) = do
	e1'			<- transform e1
	e2'			<- transform e2
	[n1,n2]		<- freshVars 2
	undefined
