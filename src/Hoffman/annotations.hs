{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS -fno-warn-tabs #-}

module Annotations where

import Language
import Control.Monad.State

data ResourceConstant =
	  KNil
	| KBool
	| KInt
	| KOp
	| KVar
	| KConT1 | KConT2
	| KConF1 | KConF2
	| KApp1  | KApp2
	| KCons
	| KCaseN1 | KCaseN2 | KCaseC1 | KCaseC2 deriving Show

data ResourceMetric = ResourceMetric String (ResourceConstant -> Int)

data Constraint =
	  CLeq [CFact] [CFact]
	| CGeq [CFact] [CFact]
	| CEq  [CFact] [CFact]

data CFact = CVar Int | CConst Int

consume :: ResourceConstant -> Int -> Int -> ResourceMetric -> State TypeState ()
consume k v1 v2 (ResourceMetric _ metric) = constraint $ CGeq [CVar v1] [CConst (metric k), CVar v2]

constraint :: Constraint -> State TypeState ()
constraint cs = constraintss [cs]

constraintss :: [Constraint] -> State TypeState ()
constraintss cs = do
	ts@TypeState{ constraints = current } <- get
	put $ ts{constraints = cs ++ current}
	return ()


data TypeState = TypeState  { topLevelDecs :: Declarations
							, constraints :: [Constraint]
							, varCounter :: Int
							, resMetric :: ResourceMetric
							}

freshVar :: State TypeState Int
freshVar = do
	ts@TypeState{ varCounter = n } <- get
	put ts{ varCounter = n+1 }
	return n

data AType =   AUnit
			 | ABool
			 | AInt
			 | L Int AType

annotateE :: Term -> State TypeState (Maybe AType)
annotateE = undefined
