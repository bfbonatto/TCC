{-# OPTIONS -fno-warn-tabs #-}

module SSM where

import qualified Data.Vector as Vector

data Instruction = Push Int | Pop | Copy | Inc | Dec | Jump Int | JumpIfZero Int deriving (Eq, Show)

type Program = Vector.Vector Instruction

type State = ([Int], Int)

step :: Program -> State -> Either State State
step program (stack, pc) = case program Vector.!? pc of
							Nothing			-> Right (stack, pc)
							Just instruct	-> Left $ execute instruct (stack, pc)

execute :: Instruction -> State -> State
execute (Push n) (stack, pc)			= (n:stack, pc+1)
execute Pop (_:stack, pc)				= (stack, pc+1)
execute Copy (s:stack, pc)				= (s:s:stack, pc+1)
execute Inc (s:stack, pc)				= (s+1:stack, pc+1)
execute Dec (s:stack, pc)				= (s-1:stack, pc+1)
execute (Jump n) (stack, pc)			= (stack, pc+n)
execute (JumpIfZero n) (s:stack, pc)	= if s == 0 then (stack, pc+n) else (stack, pc+1)
execute _ ([], pc)						= ([], pc)

run :: [Instruction] -> Int
run instructions = head . fst $ multistep (Vector.fromList instructions) ([], 0)

multistep :: Program -> State -> State
multistep program state = case step program state of
							Right newState	-> newState
							Left nextState	-> multistep program nextState


main :: IO ()
main = undefined
