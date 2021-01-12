{-# OPTIONS -fno-warn-tabs #-}

module UltraSimple where

import Control.Monad.State
import Control.Monad.Trans.Maybe
import qualified Data.Map.Strict as Map

data Expr =
	  ENum Int
	| EPlus Expr Expr deriving (Eq, Show)

bigstep :: Expr -> Int
bigstep (ENum n) = n
bigstep (EPlus n1 n2) = v1 + v2
	where
		v1 = bigstep n1
		v2 = bigstep n2

data ShareLetTerm =
	  SLVar Int
	| SLFreeLet Int ShareLetTerm ShareLetTerm
	| SLInt Int
	| SLAdd ShareLetTerm ShareLetTerm deriving (Eq, Show)

freeVar :: State Int Int
freeVar = do
	n <- get
	put $ n+1
	return n

transform :: Expr -> State Int ShareLetTerm
transform (ENum n) = return $ SLInt n
transform (EPlus e1 e2) = do
	e1' <- transform e1
	e2' <- transform e2
	n1 <- freeVar
	n2 <- freeVar
	return $ SLFreeLet n1 e1' $ SLFreeLet n2 e2' $ SLAdd (SLVar n1) (SLVar n2)


data ResourceConstant =
	  KInt
	| KPlus deriving Show

type ResourceMetric = ResourceConstant -> Int

sanityCheck :: Expr -> ResourceMetric -> Int
sanityCheck (ENum _) metric = metric KInt
sanityCheck (EPlus n1 n2) metric = kplus + k1 + k2
	where
		kplus = metric KPlus
		k1 = sanityCheck n1 metric
		k2 = sanityCheck n2 metric

data Constraint = CGeq [CFact] [CFact]

data CFact = CVar Int | CConst Int

data CState = CState { constraints :: [Constraint], varCounter :: Int, resMetric :: ResourceMetric }

freshVar :: State CState Int
freshVar = do
	cs@CState{ varCounter = n } <- get
	put cs{ varCounter = n+1 }
	return n


consume :: ResourceConstant -> Int -> Int -> State CState ()
consume k v1 v2 = do
	cs@CState{ constraints = current , resMetric = metric } <- get
	let newConstraint = CGeq [CVar v1] [CConst (metric k), CVar v2]
	put $ cs{constraints = newConstraint : current}
	return ()

data AType = AInt

type Context = Map.Map Int AType

annotate :: ShareLetTerm -> Context -> MaybeT (State CState) AType
annotate (SLInt _) _ = do
	q <- lift freshVar
	q' <- lift freshVar
	lift $ consume KInt q q'
	return AInt
annotate (SLAdd (SLVar x1) (SLVar x2)) env = do
	AInt <- MaybeT . return $ env Map.!? x1
	AInt <- MaybeT . return $ env Map.!? x2
	q <- lift freshVar
	q' <- lift freshVar
	lift $ consume KPlus q q'
	return AInt
annotate (SLFreeLet x e exp) env = do
	t <- annotate e env
	let env' = Map.insert x t env
	annotate exp env'

--data ShareLetTerm =
--	  SLVar Int
--	| SLFreeLet Int ShareLetTerm ShareLetTerm
--	| SLInt Int
--	| SLAdd ShareLetTerm ShareLetTerm deriving (Eq, Show)
