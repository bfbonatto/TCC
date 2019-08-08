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
	EmptyTuple												
	| ETrue													
	| EFalse												
	| ENumber Int											
	| EVar Var												
	| EOp Var Binop Var										
	| EApp Var Var											
	| ELet Var Expression Expression						
	| EIf Var Expression Expression							
	| ETuple Var Var										
	| ENil													
	| ECons Var Var											
	| ELeaf													
	| ENode Var Var Var										
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
etype _ _ EmptyTuple    = return $ SimpleType (ATuple Unit Unit)
etype _ _ ETrue         = return $ SimpleType ABool
etype _ _ EFalse        = return $ SimpleType ABool
etype _ _ (ENumber _)   = return $ SimpleType AInt
etype _ _ ENil          = return $ SimpleType (L Unit)
etype _ _ ELeaf         = return $ SimpleType (T Unit)
etype sig tc (EVar x)   = (Map.lookup x sig >>= Just . FirstOrderType) >>> (Map.lookup x tc >>= Just . SimpleType)

etype sig tc (EApp x y) = do
	(Arrow t1 t2) <- Map.lookup x sig
	ty <- Map.lookup y tc
	if t1 == ty then return (SimpleType t2) else Nothing

etype _ tc (ETuple x y) = do
	tx <- Map.lookup x tc
	ty <- Map.lookup y tc
	return (SimpleType (ATuple tx ty))

etype _ tc (ECons x y) = do
	tx <- Map.lookup x tc
	ty <- Map.lookup y tc
	if tx == ty then return $ SimpleType $ L tx else Nothing

etype _ tc (ENode x y z) = do
	tx <- Map.lookup x tc
	(T ty) <- Map.lookup y tc
	(T tz) <- Map.lookup z tc
	if tx == ty && tx == tz then return (SimpleType (T tx)) else Nothing

etype _ tc (EOp x op y) = do
	tx <- Map.lookup x tc
	ty <- Map.lookup y tc
	let t = optype op
	if tx == t && ty == t then return (SimpleType t) else Nothing

etype sig tc (ELet x e1 e2) = do
	(SimpleType tx) <- etype sig tc e1
	let tc' = Map.insert x tx tc
	etype sig tc' e2

etype sig tc (EIf x e1 e2) = do
	ABool <- Map.lookup x tc
	t1 <- etype sig tc e1
	t2 <- etype sig tc e2
	if t1 == t2 then return t1 else Nothing

etype sig tc (EMatchTuple x x1 x2 e) = do
	t1 <- Map.lookup x1 tc
	t2 <- Map.lookup x2 tc
	let tc' = Map.insert x (ATuple t1 t2) tc
	etype sig tc' e

etype sig tc (EMatchList x e1 xh xt e2) = do
	te1 <- etype sig tc e1
	th <- Map.lookup xh tc
	(L tt) <- Map.lookup xt tc
	let tc' = Map.insert x (L th) tc
	te2 <- etype sig tc' e2
	if te1 == te2 && th == tt then return te1 else Nothing

etype sig tc (EMatchTree x e1 x0 x1 x2 e2) = do
	te1 <- etype sig tc e1
	tn <- Map.lookup x0 tc
	(T tl) <- Map.lookup x1 tc
	(T tr) <- Map.lookup x2 tc
	let tc' = Map.insert x (T tn) tc
	te2 <- etype sig tc' e2
	if te1 == te2 && tn == tl && tn == tr then return te1 else Nothing


