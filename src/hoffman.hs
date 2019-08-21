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
type Signature     = (Map.Map Var F)

typecheck :: Signature -> TypingContext -> Expression -> Maybe A
typecheck _ _ EmptyTuple = Just $ ATuple Unit Unit
typecheck _ _ ETrue = Just ABool
typecheck _ _ EFalse = Just ABool
typecheck _ _ (ENumber _) = Just AInt
typecheck _ tc (EVar x) = Map.lookup x tc

typecheck _ tc (EOp x op y) = do
	tx <- Map.lookup x tc
	ty <- Map.lookup y tc
	let top = optype op
	if tx == ty && tx == top then return top else Nothing

typecheck sig tc (EApp f x) = do
	(Arrow a b) <- Map.lookup f sig
	tx <- Map.lookup x tc
	if tx == a then return b else Nothing

typecheck sig tc (ELet x e1 e2) = do
	a <- typecheck sig tc e1
	let tc' = Map.insert x a tc
	typecheck sig tc' e2

typecheck sig tc (EIf x e1 e2) = do
	ABool <- Map.lookup x tc
	t1 <- typecheck sig tc e1
	t2 <- typecheck sig tc e2
	if t1 == t2 then return t1 else Nothing

typecheck _ tc (ETuple x y) = do
	tx <- Map.lookup x tc
	ty <- Map.lookup y tc
	return $ ATuple tx ty

typecheck _ _ ENil = Just $ L Unit

typecheck _ tc (ECons x y) = do
	tx <- Map.lookup x tc
	ty <- Map.lookup y tc
	if tx == ty || ty == L Unit then return (L tx) else Nothing

typecheck _ _ ELeaf = Just $ T Unit

typecheck _ tc (ENode x xl xr) = do
	a <- Map.lookup x tc
	(T tl) <- Map.lookup xl tc
	(T tr) <- Map.lookup xr tc
	if tl == tr && (tl == Unit || tl == a) then return (T a) else Nothing

typecheck sig tc (EMatchTuple x x1 x2 e) = do
	(ATuple a1 a2) <- Map.lookup x tc
	let tc' = Map.insert x1 a1 $ Map.insert x2 a2 tc
	typecheck sig tc' e

typecheck sig tc (EMatchList x e1 xh xt e2) = do
	(L a) <- Map.lookup x tc
	t1 <- typecheck sig tc e1
	let tc' = Map.insert xh a $ Map.insert xt (L a) tc
	t2 <- typecheck sig tc' e2
	if t1 == t2 then return t1 else Nothing

typecheck sig tc (EMatchTree x e1 x0 x1 x2 e2) = do
	(T a) <- Map.lookup x tc
	t1 <- typecheck sig tc e1
	let tc' = Map.insert x0 a $ Map.insert x1 (T a) $ Map.insert x2 (T a) tc
	t2 <- typecheck sig tc' e2
	if t1 == t2 then return t1 else Nothing

type Loc = Int

data Value =
	VLoc Loc
	| VBool Bool
	| VInt Int
	| VNull
	| VPair (Value, Value)
	deriving (Eq, Show)

type Heap  = Map.Map Loc Value

freeLocation :: Heap -> Loc
freeLocation = undefined

type Stack = Map.Map Var Value

newtype Energy = Energy (Rational, Rational) deriving (Eq, Show)

instance Semigroup Energy where
	Energy (q, q') <> Energy (p, p')
		| q' <= p = Energy (q + p - q', p')
		| otherwise = Energy (q, p' + q' - p)

instance Monoid Energy where
	mempty = Energy (0, 0)

bigstep :: Stack -> Heap -> Expression -> Maybe (Value, Heap, Energy)
bigstep v h (EVar x) = do
	xval <- Map.lookup x v
	return (xval, h, kconst "var")

bigstep _ h EmptyTuple = return (VNull, h, kconst "unit")

bigstep _ h (ENumber n) = return (VInt n, h, kconst "int")

bigstep _ h ETrue = return (VBool True, h, kconst "bool")
bigstep _ h EFalse = return (VBool False, h, kconst "bool")

bigstep v h (EApp f x) = do
	v' <- Map.lookup x v
	-- Just (value, h', kconst <> q <> kconst)
	undefined

bigstep v h (EOp x1 Plus x2) = do
	(VInt v1) <- Map.lookup x1 v
	(VInt v2) <- Map.lookup x2 v
	let v' = v1 + v2
	return (VInt v', h, kconst "plus")
bigstep v h (EOp x1 Minus x2) = do
	(VInt v1) <- Map.lookup x1 v
	(VInt v2) <- Map.lookup x2 v
	let v' = v1 - v2
	return (VInt v', h, kconst "minus")
bigstep v h (EOp x1 Times x2) = do
	(VInt v1) <- Map.lookup x1 v
	(VInt v2) <- Map.lookup x2 v
	let v' = v1 * v2
	return (VInt v', h, kconst "times")
bigstep v h (EOp x1 Mod x2) = do
	(VInt v1) <- Map.lookup x1 v
	(VInt v2) <- Map.lookup x2 v
	let v' = v1 `mod` v2
	return (VInt v', h, kconst "mod")
bigstep v h (EOp x1 Div x2) = do
	(VInt v1) <- Map.lookup x1 v
	(VInt v2) <- Map.lookup x2 v
	let v' = v1 `div` v2
	return (VInt v', h, kconst "div")

bigstep v h (EOp x1 And x2) = do
	(VBool v1) <- Map.lookup x1 v
	(VBool v2) <- Map.lookup x2 v
	let v' = v1 && v2
	return (VBool v', h, kconst "and")
bigstep v h (EOp x1 Or x2) = do
	(VBool v1) <- Map.lookup x1 v
	(VBool v2) <- Map.lookup x2 v
	let v' = v1 || v2
	return (VBool v', h, kconst "or")


bigstep v h (ELet x e1 e2) = do
	(v1, h1, q) <- bigstep v h e1
	let v' = Map.insert x v1 v
	(v2, h2, p) <- bigstep v' h1 e2
	return (v2, h2, kconst "let1" <> q <> kconst "let2" <> p <> kconst "let3")

bigstep v h (ETuple x1 x2) = do
	vx1 <- Map.lookup x1 v
	vx2 <- Map.lookup x2 v
	return (VPair (vx1, vx2), h, kconst "pair")

bigstep v h (EMatchTuple x x1 x2 e) = do
	(VPair (v1, v2)) <- Map.lookup x v
	let v' = Map.insert x1 v1 $ Map.insert x2 v2 v
	(value, h', q) <- bigstep v' h e
	return (value, h', kconst "matchpair1" <> q <> kconst "matchpair2")

bigstep _ h ENil = return (VNull, h, kconst "nil")

bigstep v h (ECons xh xt) = do
	vh <- Map.lookup xh v
	vt <- Map.lookup xt v
	let value = VPair (vh, vt)
	let l = freeLocation h
	let h' = Map.insert l value h
	return (VLoc l, h', kconst "cons")

bigstep v h (EIf x et ef)
	| Just (VBool True) <- Map.lookup x v
	, Just (vt, h', q) <- bigstep v h et = return (vt, h', kconst "iftrue1" <> q <> kconst "iftrue2")
	| Just (VBool False) <- Map.lookup x v
	, Just (vf, h', q) <- bigstep v h ef = return (vf, h', kconst "iffalse1" <> q <> kconst "iffalse2")
	|otherwise = Nothing

bigstep v h (EMatchList x e1 xh xt e2)
	| Just VNull <- Map.lookup x v
	, Just (value, h', q) <- bigstep v h e1 
	= Just (value, h', kconst "matchnil1" <> q <> kconst "matchnil2")

	| Just (VLoc l) <- Map.lookup x v
	, Just (VPair (vh, vt)) <- Map.lookup l h
	, let v' = Map.insert xh vh $ Map.insert xt vt v
	, Just (value, h', q) <- bigstep v' h e2
	= Just (value, h', kconst "matchcons1" <> q <> kconst "matchcons2")

	| otherwise = Nothing
	
bigstep _ h ELeaf = Just (VNull, h, kconst "leaf")

bigstep v h (ENode x0 x1 x2) = do
	vx0 <- Map.lookup x0 v
	vx1 <- Map.lookup x1 v
	vx2 <- Map.lookup x2 v
	let l = freeLocation h
	let value = VPair (vx0, VPair (vx1, vx2))
	return (VLoc l, Map.insert l value h, kconst "node")

bigstep v h (EMatchTree x e1 x0 x1 x2 e2)
	| Just VNull <- Map.lookup x v
	, Just (value, h', q) <- bigstep v h e1
	= Just (value, h', kconst "matchtreeleaf1" <> q <> kconst "matchtreeleaf2")

	| Just (VLoc l) <- Map.lookup x v
	, Just (VPair (v0, VPair (v1, v2))) <- Map.lookup l h
	, let v' = Map.insert x0 v0 $ Map.insert x1 v1 $ Map.insert x2 v2 v
	, Just (value, h', q) <- bigstep v' h e2
	= Just (value, h', kconst "matchtreenode1" <> q <> kconst "matchtreenode2")

	| otherwise = Nothing

kconst :: String -> Energy
kconst = const mempty
