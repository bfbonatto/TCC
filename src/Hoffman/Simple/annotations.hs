{-# OPTIONS -fno-warn-tabs #-}

module Annotations where

import Language

data ResourceConstant =
	  KInt
	| KBool
	| KVar
	| KUnary UnOp
	| KBin BinOp
	| KApp1 | KApp2
	| KLet1 | KLet2 | KLet3
	| KConT1 | KConT2 | KConF1 | KConF2

type ResourceMetric = ResourceConstant -> Int

data CFact = CVar Var | CConst Int | CnVar Int Var -- CnVar 3 x --> 3*x

data Constraint =
	  CEq	[CFact] [CFact] -- CEq [x,1,4] [y,3] --> x + 1 + 4 == y + 3
	| CGeq	[CFact] [CFact]	-- CGeq [x,1,4] [y,3] --> x + 1 + 4 >= y + 3
	| CLeq	[CFact] [CFact] -- CLeq[x,1,4] [y,3] --> x + 1 + 4 <= y + 3

type Constraints = [Constraint]

annotateProg :: Exp -> ResourceMetric -> Constraints
annotateProg = undefined
