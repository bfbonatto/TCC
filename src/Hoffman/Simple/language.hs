{-# OPTIONS -fno-warn-tabs #-}
{-# LANGUAGE FlexibleInstances #-}

module Language where

data Exp =
	  ENum Int
	| EBinOp Exp BinOp Exp
	| EUnOp UnOp Exp
	| EBool Bool
	| ECond Exp Exp Exp
	| EVar Var
	| ELet Var Exp Exp
	| EApp FunId Exp deriving (Eq, Show)

type Var   = Int
data BinOp = Add | Sub | Mult | Eq | LessEq | And | Or deriving (Eq, Show)
data UnOp  = Not deriving (Eq, Show)
data Value = VInt Int | VBool Bool deriving (Eq, Show)

wrap :: Value -> Exp
wrap (VInt n) = ENum n
wrap (VBool b) = EBool b

sub :: Exp -> Var -> Value -> Exp
sub (ELet x e1 e2) y v = ELet x (sub e1 y v) (if x == y then e2 else sub e2 y v)
sub (EVar x) y v = if x == y then wrap v else EVar x
sub (EBinOp e1 op e2) y v = EBinOp (sub e1 y v) op (sub e2 y v)
sub e _ _ = e

class Eval a where
	eval :: a -> Maybe Value

instance Eval Exp where
	eval (ENum n) = Just $ VInt n
	eval (EBool b) = Just $ VBool b
	eval (EBinOp e1 op e2) = eval (op, e1, e2)
	eval (ELet x e1 e2) = do
		e1' <- eval e1
		eval (sub e2 x e1')

instance (Eval a) => Eval (UnOp, a) where
	eval (Not, e) = do
		 (VBool b) <- eval e
		 return $ VBool (not b)

instance (Eval a) => Eval (BinOp, a, a) where
	eval (Add, e1, e2) = do
		 (VInt n1) <- eval e1
		 (VInt n2) <- eval e2
		 return $ VInt (n1+n2)

class Typed a where
	getTypes :: a -> [Type]
	getTypes a = [typeOf a]
	typeOf :: a -> Type
	typeOf = last . getTypes

instance Typed BinOp where
	getTypes Add    = [TInt  , TInt  , TInt ]
	getTypes Sub    = [TInt  , TInt  , TInt ]
	getTypes Mult   = [TInt  , TInt  , TInt ]
	getTypes LessEq = [TInt  , TInt  , TBool]
	getTypes Eq     = [TInt  , TInt  , TBool]
	getTypes And    = [TBool , TBool , TBool]
	getTypes Or     = [TBool , TBool , TBool]

instance Typed UnOp where
	getTypes Not	= [TBool , TBool]

typeMach :: (Typed op) => op -> [Type] -> Bool
typeMach op l = getTypes op == l


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
	-- | TEShare Var Var Var TExp Type -- TEShare y y' x e T means x ~> y,y'
	| TEShare [Var] Var TExp Type -- one share is better than many piece-wise shares
	| TELet Kind Var TExp TExp Type -- TELet kind x e e'  means (free)let x be e in e'
	deriving (Eq, Show)

data Type  = TInt | TBool deriving (Eq, Show)
data Kind  = Free | Normal deriving (Eq, Show)
type FunId = String
-- Disallowing function declaration inside expressions simplifies the analysis

instance Typed TExp where
	typeOf (TENum _)         = TInt
	typeOf (TEBool _)        = TBool
	typeOf (TEUnOp _ _ t)    = t
	typeOf (TEBinOp _ _ _ t) = t
	typeOf (TECond _ _ _ t)  = t
	typeOf (TEVar _ t)       = t
	typeOf (TEShare _ _ _ t) = t
	typeOf (TELet _ _ _ _ t) = t
	typeOf (TEApp _ _ t)     = t
