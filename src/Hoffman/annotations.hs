{-# OPTIONS -fno-warn-tabs #-}

module Annotations where

import Language
import Typing
import qualified Data.Map.Strict as Map

data A = ABool | AInt | AL Int A | Unit deriving Show
data F = FFun A Int Int A deriving Show

type AnnotatedContext = Map.Map Var A
type FunctionContext = Map.Map Var F

data AnnotatedTypingJudgement = ATJ Int A

annotate :: FunctionContext -> AnnotatedContext -> Term -> Maybe AnnotatedTypingJudgement
annotate = undefined

