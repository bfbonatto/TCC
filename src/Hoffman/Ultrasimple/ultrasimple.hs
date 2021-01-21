{-# OPTIONS -fno-warn-tabs #-}

module UltraSimple where

import Data.List
import Data.Maybe (catMaybes)
import Control.Monad.State hiding (join)
import Control.Monad.Trans.Maybe
import qualified Data.Map.Strict as Map

import qualified System.Cmd as Cmd
import System.IO
import Text.ParserCombinators.Parsec hiding (State)
import qualified GHC.IO.Exception as Exception

data Expr =
	  ENum Int
	| EPlus Expr Expr deriving (Eq, Show)

bigstep :: Expr -> Int
bigstep (ENum n) = n
bigstep (EPlus n1 n2) = v1 + v2
	where
		v1 = bigstep n1
		v2 = bigstep n2

type Var = Int

data ShareLetTerm =
	  SLVar Var
	| SLFreeLet Var ShareLetTerm ShareLetTerm -- freelet x = e in e'
	| SLInt Int
	| SLAdd Var Var deriving (Eq, Show)

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
	return $ SLFreeLet n1 e1' $ SLFreeLet n2 e2' $ SLAdd n1 n2


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

data CFact = CVar Int | CConst Int | CnVar Int Int -- CnVar 3 x --> 3*x

data Constraint = CGeq [CFact] [CFact] -- CGeq [x,1,4] [y,3] --> x + 1 + 4 >= y+3
type Constraints = [Constraint]

cmap :: (CFact -> a) -> Constraint -> ([a], [a])
cmap f (CGeq l1 l2) = (map f l1, map f l2)

constraintVars :: Constraints -> [Int]
constraintVars = foldr1 union . map (nub . catMaybes . join . cmap maybeVar)


maybeVar :: CFact -> Maybe Int
maybeVar (CVar n) = Just n
maybeVar _ = Nothing

join :: (Eq a) => ([a], [a]) -> [a]
join = uncurry union

instance Show CFact where
	show (CVar n) = 'x' : show n
	show (CConst n) = show n
	show (CnVar n x) = if n == 1 then "x" ++ show x
                        else show n ++ " x" ++ show x

instance Show Constraint where
	show (CGeq l1 l2) = s l1 ++ " >= " ++ s l2
		where
			s [] = ""
			s [n] = show n
			s (x:xs) = show x ++ " + " ++ s xs

showConstr constr = case constr of
                     CGeq sum1 sum2 -> showSWithSep " + " sum1 . showString " >= " . showSWithSep " + " sum2

showSWithSep sep [] = showString ""
showSWithSep sep [t] = showString $ show t
showSWithSep sep (t:ts) = showString  (show t) . showString sep . showSWithSep sep ts

data CState = CState { constraints :: Constraints, varCounter :: Int, resMetric :: ResourceMetric }

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
	let newConstraint = CGeq [CVar v1] [CConst (metric k), CVar v2]
	put $ cs{constraints = newConstraint : current}
	return ()

data AType = AInt Int

type Context = Map.Map Int AType

annotate :: ShareLetTerm -> Context -> MaybeT (State CState) AType
annotate (SLInt _) _ = do
	q' <- lift freshVar
	q <- lift freshVar
	lift $ consume KInt q q'
	return $ AInt q
annotate (SLAdd x1 x2) env = do
	(AInt q1) <- MaybeT . return $ env Map.!? x1
	(AInt q2) <- MaybeT . return $ env Map.!? x2
	q' <- lift freshVar
	q <- lift freshVar
	lift $ emit $ CGeq [CVar q'] [CVar q1, CVar q2]
	lift $ consume KPlus q q'
	return $ AInt q
annotate (SLFreeLet x e exp) env = do
	t <- annotate e env
	let env' = Map.insert x t env
	annotate exp env'


annotateProg :: Expr -> ResourceMetric -> Constraints
annotateProg prog metric = case t of
							Nothing -> []
							_		-> constraints state'
	where
		(slt, _) = (runState $ transform prog) 0
		initialState = CState [] 0  metric
		(t, state') = (runState . runMaybeT $ annotate slt Map.empty) initialState


data Objective = Objective Int Int -- Objective Var Factor

instance Show Objective where
	show (Objective var factor) = show factor ++ " x" ++ show var 

objective :: Constraints -> Int -> Objective
objective cs = Objective (maximum $ constraintVars cs)

parseClp :: Parser (Map.Map String Double)
parseClp =	unsolvable <|>
			do	 { string "Optimal"
				 ; spaces
				 ; many anyChar
				 ; newline
				 ; variableValues
				 } <|>
			do { fail "Something went wrong with the Clp output." }
	where
		unsolvable = do { _ <- string "Infeasible" ; fail"The linear program is infeasible." }
		variableValues = do { map <- many varValue ; return $ Map.fromList map }
		varValue = do { spaces
					  ; many digit
					  ; varId <- varName
					  ; spaces
					  ; value <- double
					  ; many anyChar
					  ; newline
					  ; return (varId, value)}
		varName = do { l <- letter ; ls <- many alphaNum ; return $ l:ls }
		double = do	 { sign <- do { char '-' ; return "-" }
							<|> do { char '+' ; return "+" }
							<|> return ""
					 ; ds <- many digit
					 ; do { char '.' ; es <- many digit ; return (read (sign ++ ds ++ "."++ es) :: Double)}
					 <|> (return ((read $ sign ++ ds) :: Double))}

lpInput :: Handle -> Constraints -> Objective -> IO ()
lpInput file constraints objective = do
	hPutStr file "Minimize\n"
	hPutStr file $ show objective
	hPutStr file "\n"
	hPutStr file "Subject To\n"
	let constrString = (foldr (\c s -> (normalizeConstr c) . s)  (showString "")  constraints ) ""
	hPutStr file constrString
	hPutStr file "End"

normalizeConstr constraint =
    case constraint of
       CGeq lhs rhs -> let (lhs',q) = normalize lhs rhs in
                       (showConstr $ CGeq lhs' [CConst q]) . (showString "\n")
  where
    normalize lhs rhs = 
      let (varsL,qL) = foldl processLhs ([],0) lhs
          (varsR,qR) = foldl processRhs ([],0) rhs
      in  (varsL++varsR,qL+qR)

    processLhs (vars,q) constr = case constr of
      CConst c -> (vars,q-c)
      var -> (var:vars,q)

    processRhs (vars,q) constr = case constr of
      CVar x -> (CnVar (-1) x:vars,q)
      CnVar n x -> (CnVar (-n) x:vars,q)
      CConst c -> (vars,q+c)


data Flag = DeleteFiles | KeepFiles

solve :: Expr -> Flag -> IO (Either String (Map.Map String Double))
solve e = solve' cs obj current
	where
		cs = annotateProg e (const 1)
		obj = objective cs 1
		current = "./"

solve' :: (Monad err) => Constraints -> Objective -> FilePath -> Flag -> IO (err (Map.Map String Double))
solve' constraints objective tempDir flag = do
	print $ "Constraints: " ++ show constraints
	print $ "Objective: " ++ show objective
	(constrFileName, constrFile) <- openTempFile tempDir "constr.lp"
	(solutionFileName, solutionFile) <- openTempFile tempDir "solution.clp"
	hClose solutionFile
	hSetBuffering constrFile (BlockBuffering Nothing)
	lpInput constrFile constraints objective
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

e :: Expr
e = EPlus (ENum 1) (ENum 1)

main :: IO (Either String (Map.Map String Double))
main = solve e KeepFiles
