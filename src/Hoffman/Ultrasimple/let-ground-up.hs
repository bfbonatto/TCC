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
evalSteps = const 1

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


data AType =
	  AInt

type Context = M.Map Var AType

data Constraint =
	  CGeq [CFact] [CFact]
	| CLeq [CFact] [CFact]
	| CEq  [CFact] [CFact]

data CFact =
	  CVar Var
	| CConst Int
	| CnVar Int Var

data CState = CState { _resMetric   :: ResourceMetric
					 , _constraints :: [Constraint]
					 , _varCounter  :: Int
					 }

emit :: Constraint -> State CState ()
emit c = do
	cs@CState{ _constraints = current } <- get
	put $ cs{ _constraints = c:current }

fresh :: State CState Var
fresh = do
	cs@CState{ _varCounter = n } <- get
	put $ cs{ _varCounter = n+1 }
	return n

annotate :: Expr -> Context -> State CState AType
annotate (ENum _) _ = do
	m <- gets _resMetric
	undefined
