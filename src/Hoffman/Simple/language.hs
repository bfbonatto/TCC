{-# OPTIONS -fno-warn-tabs #-}

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

type Var           = Int
data BinOp         = NtNB NatToNatBin | BtBB BoolToBoolBin | NtBB NatToBoolBin deriving (Eq, Show)
data NatToNatBin   = Add | Sub | Mult deriving (Eq, Show)
data NatToBoolBin  = Eq | LessEq deriving (Eq, Show)
data BoolToBoolBin = And | Or deriving (Eq, Show)
data UnOp          = Not deriving (Eq, Show)

class Typed a where
	getTypes :: a -> [Type]
	getTypes a = [typeOf a]
	typeOf :: a -> Type
	typeOf = last . getTypes

instance Typed BinOp where
	getTypes (NtNB op) = getTypes op
	getTypes (BtBB op) = getTypes op
	getTypes (NtBB op) = getTypes op

instance Typed NatToNatBin where
	getTypes _ = [TInt, TInt, TInt]

instance Typed NatToBoolBin where
	getTypes _ = [TInt, TInt, TBool]

instance Typed BoolToBoolBin where
	getTypes _ = [TBool, TBool, TBool]

instance Typed UnOp where
	getTypes _ = [TBool, TBool]

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
