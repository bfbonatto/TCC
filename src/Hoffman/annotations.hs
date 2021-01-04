{-# OPTIONS -fno-warn-tabs #-}

module Annotations where

import Language
import qualified Data.Map.Strict as Map

data ResourceConstants =
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

rc2int _ = 1

data A = ABool | AInt | AL Int A | Unit deriving Show
data F = FFun A Int Int A deriving Show

type AnnotatedContext = Map.Map Var A
type FunctionContext = Map.Map Var F
