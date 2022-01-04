{-# OPTIONS -fno-warn-tabs #-}

module Transform where

import Language
import Data.List
import qualified Data.Map.Strict as M
import Control.Monad.State

data SLTState = SLTState{ varCounter :: Int, varContext :: M.Map Var Type }

instance Show SLTState where
	show (SLTState _ gamma) = show (M.toList gamma)

initialState = SLTState 0 M.empty

freshVar :: State SLTState Var
freshVar = do
	s@SLTState{ varCounter = n } <- get
	put s{varCounter = n +1}
	return n

freshVars :: Int -> State SLTState [Var]
freshVars n = sequence [ freshVar | _ <- [1..n] ]

freeVars :: TExp -> [Var]
freeVars (TENum _)            = []
freeVars (TEBool _)           = []
freeVars (TEVar x _)          = [x]
freeVars (TEApp _ e _)        = freeVars e
freeVars (TEUnOp _ e _)       = freeVars e
freeVars (TEBinOp e1 _ e2 _)  = freeVars e1 `union` freeVars e2
freeVars (TELet _ x e1 e2 _)  = (freeVars e1 `union` freeVars e2) \\ [x]
freeVars (TECond e e1 e2 _)   = freeVars e `union` freeVars e1 `union` freeVars e2
freeVars (TEShare ys x e _) = [x] `union` (freeVars e \\ ys)

subst :: TExp -> Var -> Var -> TExp
subst (TEVar x t) y z			 = TEVar (if x == y then z else x) t
subst (TEApp f e t) y z        	 = TEApp f (subst e y z) t
subst (TEUnOp op e t) y z      	 = TEUnOp op (subst e y z) t
subst (TEBinOp e1 op e2 t) y z 	 = TEBinOp (subst e1 y z) op (subst e2 y z) t
subst (TECond e et ef t) y z   	 = TECond (subst e y z) (subst et y z) (subst ef y z) t
subst (TEShare xs x e t) y z   	 = TEShare xs (if x == y then z else x) (subBound xs e y z) t
subst (TELet kind x e1 e2 t) y z = TELet kind x (subst e1 y z) (subBound [x] e2 y z) t
subst e _ _						 = e

subBound :: [Var] -> TExp -> Var -> Var -> TExp
subBound xs e y z = if y `elem` xs then e else subst e y z

freeLets :: Monad m => [(Var, TExp)] -> TExp -> Type -> m TExp
freeLets [] exp _             = return exp
freeLets ((x,e):lets) exp typ = do
	exp' <- freeLets lets exp typ
	return $ TELet Free x e exp' typ


shareVar :: Var -> [TExp] -> State SLTState ([TExp], TExp -> TExp)
shareVar x ts = do
	ys <- freshVars (length ts)
	let s' e = subst e x
	let ts'  = zipWith s' ts ys
	return (ts', \t -> TEShare ys x t (typeOf t))

shareVars :: [Var] -> [TExp] -> State SLTState ([TExp], TExp -> TExp)
shareVars [] ts = return (ts, id)
shareVars (x:xs) ts = do
	(ts', fs) <- shareVars xs ts
	(ts2, fs') <- shareVar x ts'
	return (ts2, fs' . fs)

shareFreeVars :: [TExp] -> State SLTState ([TExp], TExp -> TExp)
shareFreeVars ts = shareVars (foldr1 intersect (map freeVars ts)) ts

setTypeOf :: Var -> Type -> State SLTState ()
setTypeOf x t = do
	s@SLTState{ varContext = gamma } <- get
	let gamma' = M.insert x t gamma
	put $ s{ varContext = gamma' }

testTransform :: Exp -> TExp
testTransform e = evalState (transform e) initialState

testStateTransform :: Exp -> SLTState
testStateTransform e = execState (transform e) initialState

transform :: Exp -> State SLTState TExp
transform (ENum n)          = return $ TENum n
transform (EBool b)         = return $ TEBool b
transform (EBinOp e1 op e2) = do
	e1'			<- transform e1
	e2'			<- transform e2
	[n1,n2]		<- freshVars 2
	([s1, s2], f) <- shareFreeVars [e1', e2']
	let typ = typeOf op
	let term = TEBinOp (TEVar n1 (typeOf e1')) op (TEVar n2 (typeOf e2')) typ
	term' <- freeLets [(n1,s1), (n2,s2)] term typ
	return $ f term'
transform (ELet x e1 e2) = undefined
	-- x' <- freshVar
	-- e1' <- transform e1
	-- setTypeOf x' (typeOf e1')
	-- e2' <- transform e2
	-- let e2'' = subst e2' x x'
	-- let commonVars = (freeVars e1' `intersect` freeVars e2'') \\ [x]
	-- ([s1,s2], f) <- shareVars commonVars [e1', e2'']
	-- return $ f $ TELet Normal x' s1 s2 (typeOf e2'')
transform (EVar x) = do
	gamma <- gets varContext
	t <- case M.lookup x gamma of
			Just t -> return t
			Nothing -> fail $ "Unbound variable " ++ show x ++ " in " ++ show (M.toList gamma)
	return $ TEVar x t
