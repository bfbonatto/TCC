{-# OPTIONS -fno-warn-tabs #-}

module Clp where

import Language
import Annotations

import qualified Data.Map.Strict as M

import Text.ParserCombinators.Parsec hiding (State)

import System.Cmd as Cmd
import System.IO
import qualified GHC.IO.Exception as Exception

data Objective = Objective Int Var -- Objective 3 x --> Minimize 3*x

objective :: Constraints -> Objective
objective = undefined

parseClp :: Parser (M.Map String Double)
parseClp = undefined

data TempFileFlag = KeepFiles | DeleteFiles

mkClpInput :: Handle -> TempFileFlag -> Constraints -> IO ()
mkClpInput = undefined

solve :: Exp -> ResourceMetric -> TempFileFlag -> IO (Either String (M.Map String Double))
solve e metric = solve' cons "./"
	where
		cons = annotateProg e metric

solve' :: (Monad err) => Constraints -> FilePath -> TempFileFlag -> IO (err (M.Map String Double))
solve' constraints tempDir flag= do
	(constrFileName, constrFile) <- openTempFile tempDir "constr.lp"
	(solutionFileName, solutionFile) <- openTempFile tempDir "solution.clp"
	hClose solutionFile
	hSetBuffering constrFile (BlockBuffering Nothing)
	mkClpInput constrFile flag constraints
	hClose constrFile
	Cmd.system $ "clp " ++ constrFileName ++ " -solv -solution " ++ solutionFileName ++ " > /dev/null"
	solutionString <- readFile solutionFileName
	let solution = case parse parseClp solutionFileName solutionString of
		Left err -> fail $ "Clp finished unsuccessfull." ++ show err
		Right x -> return x
	case flag of
		DeleteFiles -> Cmd.system $ "rm " ++ constrFileName ++ " " ++ solutionFileName		
		KeepFiles -> return Exception.ExitSuccess
	return solution
