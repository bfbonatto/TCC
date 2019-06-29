{-# OPTIONS -fno-warn-tabs #-}

module Compiler0 where

import qualified L0
import qualified SSM

compile :: L0.Term -> Maybe [SSM.Instruction]
compile term = case L0.typecheck term of
				Nothing -> Nothing
				_		-> Just $ step term

step :: L0.Term -> [SSM.Instruction]
step L0.TermTrue			= [SSM.Push 1]
step L0.TermFalse			= [SSM.Push 0]
step L0.TermZero			= [SSM.Push 0]
step (L0.TermSucc t)		= step t ++ [SSM.Inc]
step (L0.TermPred t)		= step t ++ [SSM.JumpIfZero 4, SSM.Dec, SSM.Jump 2, SSM.Push 0]
step (L0.TermIsZero 	t)	= step t ++ [SSM.JumpIfZero 3, SSM.Push 0, SSM.Jump 2, SSM.Push 1]
step (L0.TermIf t1 t2 t3)	= c1 ++ [SSM.JumpIfZero $ length c2 + 2] ++ c2 ++ [SSM.Jump $ length c3 + 1] ++ c3
	where
		c1 = step t1
		c2 = step t2
		c3 = step t3


main :: IO ()
main = undefined
