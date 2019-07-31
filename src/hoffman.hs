{-# OPTIONS -fno-warn-tabs #-}

module Hoffman where

import qualified Data.Map.Lazy as Map

type Var = String


data Binop = Plus | Minus | Times | Mod | Div | And | Or

optype :: Binop -> A
optype And = ABool
optype Or  = ABool
optype _   = AInt

(>>>) :: Maybe a -> Maybe a -> Maybe a
Nothing >>> a = a
a >>> _       = a

instance Show Binop where
	show Plus = "+"
	show Minus = "-"
	show Times = "*"
	show Mod = "mod"
	show Div = "div"
	show And = "and"
	show Or = "or"

data Expression =
	EmptyTuple												--
	| ETrue													--
	| EFalse												--
	| ENumber Int											--
	| EVar Var												--
	| EOp Var Binop Var										--
	| EApp Var Var											--
	| ELet Var Expression Expression
	| EIf Var Expression Expression
	| ETuple Var Var										--
	| ENil													--
	| ECons Var Var											--
	| ELeaf													--
	| ENode Var Var Var										--
	| EMatchTuple Var Var Var Expression
	| EMatchList Var Expression Var Var Expression
	| EMatchTree Var Expression Var Var Var Expression

instance Show Expression where
	show EmptyTuple = "()"
	show ETrue = "True"
	show EFalse = "False"
	show (ENumber n) = show n
	show (EVar x) = show x
	show (EOp x1 op x2) = show x1 ++ " " ++ show op ++ " " ++ show x2
	show (EApp f x) = show f ++ "(" ++ show x ++ ")"
	show (ELet x e1 e2) = "let " ++ show x ++ " = " ++ show e1 ++ " in " ++ show e2
	show (EIf x et ef) = "if " ++ show x ++ " then " ++ show et ++ " else " ++ show ef
	show (ETuple x1 x2) = "(" ++ show x1 ++ "," ++ show x2 ++ ")"
	show ENil = "nil"
	show (ECons x1 x2) = "cons(" ++ show x1 ++ "," ++ show x2 ++ ")"
	show ELeaf = "leaf"
	show (ENode x0 x1 x2) = "node(" ++ show x0 ++ "," ++ show x1 ++ "," ++ show x2 ++ ")"
	show (EMatchTuple x x1 x2 e) = "match " ++ show x ++ " with " ++ show (ETuple x1 x2) ++ " -> " ++ show e
	show (EMatchList x e1 xh xt e2) = "match " ++ show x ++ " | nil -> " ++ show e1 ++ " | " ++ show (ECons xh xt) ++ " -> " ++ show e2
	show (EMatchTree x e1 x0 x1 x2 e2) = "match " ++ show x ++ " | leaf -> " ++ show e1 ++ " | " ++ show (ENode x0 x1 x2) ++ " -> " ++ show e2

data A = Unit | ABool | AInt | L A | T A | ATuple A A deriving (Eq, Show)
data F = Arrow A A deriving (Eq, Show)

data Type = SimpleType A | FirstOrderType F deriving (Eq, Show)

type TypingContext = (Map.Map Var A)
type Signature = (Map.Map Var F)

substitution :: Var -> Expression -> Var -> Expression
substitution = undefined

etype :: Signature -> TypingContext -> Expression -> Maybe Type
etype _ _ EmptyTuple    = Just $ SimpleType (ATuple Unit Unit)
etype _ _ ETrue         = Just $ SimpleType ABool
etype _ _ EFalse        = Just $ SimpleType ABool
etype _ _ (ENumber _)   = Just $ SimpleType AInt
etype _ _ ENil          = Just $ SimpleType (L Unit)
etype _ _ ELeaf         = Just $ SimpleType (T Unit)
etype sig tc (EVar x)   = (Map.lookup x sig >>= Just . FirstOrderType) >>> (Map.lookup x tc >>= Just . SimpleType)

etype sig tc (EApp x y) = do
	(Arrow t1 t2) <- Map.lookup x sig
	ty <- Map.lookup y tc
	if t1 == ty then Just (SimpleType t2) else Nothing

etype _ tc (ETuple x y) = do
	tx <- Map.lookup x tc
	ty <- Map.lookup y tc
	Just (SimpleType (ATuple tx ty))

etype _ tc (ECons x y) = do
	tx <- Map.lookup x tc
	ty <- Map.lookup y tc
	if tx == ty then Just $ SimpleType $ L tx else Nothing

etype _ tc (ENode x y z) = do
	tx <- Map.lookup x tc
	(T ty) <- Map.lookup y tc
	(T tz) <- Map.lookup z tc
	if tx == ty && tx == tz then Just (SimpleType (T tx)) else Nothing

etype _ tc (EOp x op y) = do
	tx <- Map.lookup x tc
	ty <- Map.lookup y tc
	let t = optype op
	if tx == t && ty == t then Just (SimpleType t) else Nothing

etype sig tc (ELet x e y) = undefined
