{-# OPTIONS -fno-warn-tabs #-}

module Hoffman where

import qualified Data.Map.Lazy as Map

type Var = String

data Binop = Plus | Minus | Times | Mod | Div | And | Or

optype :: Binop -> A
optype And = ABool
optype Or  = ABool
optype _   = AInt

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

type TypingContext = (Map.Map Var A)
type Signature = (Map.Map Var F)

etype :: Signature -> TypingContext -> Expression -> Maybe A
etype _ _ EmptyTuple = Just $ ATuple Unit Unit
etype _ _ ETrue = Just ABool
etype _ _ EFalse = Just ABool
etype _ _ (ENumber _) = Just AInt
etype _ tc (EVar x) = Map.lookup x tc

etype _ tc (EOp x op y) = do
	tx <- Map.lookup x tc
	ty <- Map.lookup y tc
	let top = optype op
	if tx == ty && tx == top then return top else Nothing

etype sig tc (EApp f x) = do
	(Arrow a b) <- Map.lookup f sig
	tx <- Map.lookup x tc
	if tx == a then return b else Nothing

etype sig tc (ELet x e1 e2) = do
	a <- etype sig tc e1
	let tc' = Map.insert x a tc
	etype sig tc' e2

etype sig tc (EIf x e1 e2) = do
	ABool <- Map.lookup x tc
	t1 <- etype sig tc e1
	t2 <- etype sig tc e2
	if t1 == t2 then return t1 else Nothing

etype _ tc (ETuple x y) = do
	tx <- Map.lookup x tc
	ty <- Map.lookup y tc
	return $ ATuple tx ty

etype _ _ ENil = Just $ L Unit

etype _ tc (ECons x y) = do
	tx <- Map.lookup x tc
	ty <- Map.lookup y tc
	if tx == ty || ty == L Unit then return (L tx) else Nothing

etype _ _ ELeaf = Just $ T Unit

etype _ tc (ENode x xl xr) = do
	a <- Map.lookup x tc
	(T tl) <- Map.lookup xl tc
	(T tr) <- Map.lookup xr tc
	if tl == tr && (tl == Unit || tl == a) then return (T a) else Nothing

etype sig tc (EMatchTuple x x1 x2 e) = do
	(ATuple a1 a2) <- Map.lookup x tc
	let tc' = Map.insert x1 a1 $ Map.insert x2 a2 tc
	etype sig tc' e

etype sig tc (EMatchList x e1 xh xt e2) = do
	(L a) <- Map.lookup x tc
	t1 <- etype sig tc e1
	let tc' = Map.insert xh a $ Map.insert xt (L a) tc
	t2 <- etype sig tc' e2
	if t1 == t2 then return t1 else Nothing

etype sig tc (EMatchTree x e1 x0 x1 x2 e2) = do
	(T a) <- Map.lookup x tc
	t1 <- etype sig tc e1
	let tc' = Map.insert x0 a $ Map.insert x1 (T a) $ Map.insert x2 (T a) tc
	t2 <- etype sig tc' e2
	if t1 == t2 then return t1 else Nothing
