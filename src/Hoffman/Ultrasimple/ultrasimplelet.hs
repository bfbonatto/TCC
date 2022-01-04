{-# OPTIONS -fno-warn-tabs #-}
{-# LANGUAGE FlexibleInstances #-}

module UltraSimple where

import Prelude hiding (log)
import Data.List
import Data.Maybe (catMaybes)
import Control.Monad.State hiding (join)
import Control.Monad.Trans.Maybe
import qualified Data.Map.Strict as M

data Expr =
	  ENum Int
	| ELet String Expr Expr
	| EVar String
	| EPlus Expr Expr deriving (Eq, Show)

type Var = Int


newtype Pair = Pair (Int, Int) deriving (Eq, Show)

class Potential a where
	toPair :: a -> Pair

instance Potential Pair where
	toPair = id

instance Potential Int where
	toPair n
		| n >= 0    = Pair (n,0)
		| otherwise = Pair (0,-n)

(<.>) :: (Potential a, Potential b) => a -> b -> Pair
a <.> b
	| q' <= p   = Pair (q+p-q', p')
	| otherwise = Pair (q, p'+q'-p)
	where
		Pair (q,q') = toPair a
		Pair (p,p') = toPair b

data ResourceConstant =
	  KVar
	| KNum
	| KPlus
	| KLet1 | KLet2 | KLet3 deriving (Eq, Show)

type ResourceMetric = ResourceConstant -> Int

evalSteps :: ResourceMetric
evalSteps KLet2 = 0
evalSteps KLet3 = 0
evalSteps _		= 1

type EvalContext = M.Map String Int

bigstep :: Expr -> EvalContext -> ResourceMetric -> Maybe (Int, Pair)
bigstep (ENum n) _ metric = Just (n, toPair.metric $ KNum)
bigstep (EVar x) c metric = do
	v <- M.lookup x c
	return (v, toPair.metric $ KVar)
bigstep (EPlus e1 e2) c metric = do
	(v1, q) <- bigstep e1 c metric
	(v2, p) <- bigstep e2 c metric
	return (v1+v2, q <.> p <.> metric KPlus)
bigstep (ELet x e1 e2) c metric = do
	(v1, q) <- bigstep e1 c metric
	let c'  = M.insert x v1 c
	(v2, p) <- bigstep e2 c' metric
	return (v2, metric KLet1 <.> q <.> metric KLet2 <.> p <.> metric KLet3)

getPair :: Expr -> Maybe (Int, Pair)
getPair e = bigstep e M.empty (const 1)


-------------------------
-- Typing and Analysis --
-------------------------

data TExp =
	  TEVar Kind Var
	| TELet Kind Var TExp TExp -- freelet x = e in e'
	| TENum Int
	| TEShare Var Var Var TExp -- TEShare y1 y2 x e
	| TEPlus Var Var deriving (Eq, Show)

data Kind = Normal | Free deriving (Eq, Show)

freeVar :: State Int Int
freeVar = do
	n <- get
	put $ n+1
	return n

subst :: Var -> Var -> TExp -> TExp -- [x:=y] e == subst x y e
subst x y (TEVar t z)          = TEVar t (if z == x then y else z)
subst x y (TELet t z e1 e2)    = TELet t z (subst x y e1) (if x == z then e2 else subst x y e2)
subst _ _ (TENum n)            = TENum n
subst x y (TEShare z1 z2 z3 e) = TEShare (if z1 == x then y else z1) z2 z3 (subst x y e)
subst _ _ (TEPlus e1 e2)       = TEPlus e1 e2

shareVar :: Var -> TExp -> TExp -> State Int (TExp -> TExp, TExp, TExp)
shareVar x e1 e2 = do
	y1 <- freeVar
	y2 <- freeVar
	return (TEShare y1 y2 x, subst x y1 e1, subst x y2 e2)

shareVars :: [Var] -> TExp -> TExp -> State Int (TExp -> TExp, TExp, TExp)
shareVars [] e1 e2 = return (id, e1, e2)
shareVars (x:xs) e1 e2 = do
	(s, e1', e2')    <- shareVars xs e1 e2
	(s', e1'', e2'') <- shareVar x e1' e2'
	return (s . s', e1'', e2'')

shareFreeVars :: TExp -> TExp -> State Int (TExp -> TExp, TExp, TExp)
shareFreeVars e1 e2 = shareVars (freevars e1 `intersect` freevars e2) e1 e2

freevars :: TExp -> [Var]
freevars (TENum _)           = []
freevars (TEVar _ x)         = [x]
freevars (TEPlus _ _)        = []
freevars (TELet _ x e1 e2)   = freevars e1 `union` (freevars e2 \\ [x])
freevars (TEShare x y1 y2 e) = [x] `union` (freevars e \\ [y1,y2])

transform :: Expr -> M.Map String Var -> MaybeT (State Int) TExp
transform (ENum n) _ = return $ TENum n
transform (EVar v) context = do
	x <- MaybeT . return $ M.lookup v context
	return $ TEVar Normal x
transform (EPlus e1 e2) context = do
	x1  <- lift freeVar
	x2  <- lift freeVar
	e1' <- transform e1 context
	e2' <- transform e2 context
	(s,e1'',e2'') <- lift $ shareFreeVars e1' e2'
	return $ s $ TELet Free x1 e1'' $ TELet Free x2 e2'' $ TEPlus x1 x2
transform (ELet v e1 e2) context = do
	x   <- lift freeVar
	e1' <- transform e1 context
	let context' = M.insert v x context
	e2' <- transform e2 context'
	let c = (freevars e1' `intersect` freevars e2') \\ [x]
	(s,e1'',e2'') <- lift $ shareVars c e1' e2'
	return $ s $ TELet Normal x e1'' e2''

data CFact = CVar Int | CConst Int | CnVar Int Int -- CnVar 3 x --> 3*x

data Constraint =
	  CGeq String [CFact] [CFact] -- CGeq [x,1,4] [y,3] --> x + 1 + 4 >= y+3
	| CLeq String [CFact] [CFact] -- CLeq [x,1,4] [y,3] --> x + 1 + 4 <= y+3
	| CEq  String [CFact] [CFact] -- CEq  [x,1,4] [y,3] --> x + 1 + 4 == y+3
type Constraints = [Constraint]


constraintVars :: Constraints -> [Int]
constraintVars = foldr1 union . map (nub . catMaybes . join . cmap maybeVar)
	where
		maybeVar (CVar x)    = Just x
		maybeVar (CnVar _ x) = Just x
		maybeVar _           = Nothing
		join                 = uncurry union
		cmap f (CGeq s l1 l2)  = (map f l1, map f l2)
		cmap f (CLeq s l1 l2)  = (map f l1, map f l2)
		cmap f (CEq  s l1 l2)  = (map f l1, map f l2)


instance Show CFact where
	show (CVar n)    = 'x' : show n
	show (CConst n)  = show n
	show (CnVar n x) = if n == 1 then "x" ++ show x
                        else show n ++ " x" ++ show x

instance Show Constraint where
	show c = case c of
		(CGeq rule l1 l2) -> rule ++ ": " ++ s l1 ++ " >= " ++ s l2
		(CLeq rule l1 l2) -> rule ++ ": " ++ s l1 ++ " <= " ++ s l2
		(CEq  rule l1 l2) -> rule ++ ": " ++ s l1 ++ " = "  ++ s l2
		where
			s [] = ""
			s [n] = show n
			s (x:xs) = show x ++ " + " ++ s xs

data CState = CState { constraints :: Constraints
					 , varCounter  :: Int
					 , resMetric   :: ResourceMetric
					 , _log		   :: [String]
					 }
instance Show CState where
	show = show . constraints

log :: String -> State CState ()
log s = modify $ \cs@CState{_log = l} -> cs{_log = l ++ [s]}

freshVar :: State CState Int
freshVar = do
	cs@CState{ varCounter = n } <- get
	put cs{ varCounter = n+1 }
	return n

emit :: Constraint -> State CState ()
emit c = do
	cs@CState{constraints = current} <- get
	put $ cs{constraints = c : current}
	return ()


consume :: ResourceConstant -> Int -> Int -> State CState ()
consume k v1 v2 = do
	cs@CState{ constraints = current , resMetric = metric } <- get
	let newConstraint = CGeq (show k) [CVar v1] [CConst (metric k), CVar v2]
	put $ cs{constraints = newConstraint : current}
	return ()

data AType = AInt Var Var deriving (Eq, Show)

proj0 :: AType -> (Var -> Var -> AType)
proj0 (AInt _ _) = AInt

proj1 :: AType -> Var
proj1 (AInt q _) = q

proj2 :: AType -> Var
proj2 (AInt _ q) = q

type Context = M.Map Var AType

unwrap :: MaybeT (State b) a -> b -> (Maybe a, b)
unwrap s = runState (runMaybeT s)



test :: ResourceMetric -> Expr -> (Maybe AType, CState)
test m expr = do
	let (parsed, _) = unwrap (transform expr M.empty) 0
	let (Just texp) = parsed
	unwrap (annotate texp M.empty) (CState [] 0 m [])

annotate :: TExp -> Context -> MaybeT (State CState) AType
annotate = undefined
