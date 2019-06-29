{-# OPTIONS -fno-warn-tabs #-}

module L0 where

data Term = TermTrue | TermFalse | TermIf Term Term Term | TermZero | TermSucc Term | TermPred Term | TermIsZero Term deriving (Eq, Show)

toString :: Term -> String
toString TermTrue = "TmTrue"
toString TermFalse = "TmFalse"
toString (TermIf t t1 t2) = "TmIf " ++ toString t ++ " " ++ toString t1 ++ " " ++ toString t2
toString TermZero = "TmZero"
toString (TermSucc t) = "TmSucc " ++ toString t
toString (TermPred t) = "TmPred " ++ toString t
toString (TermIsZero t) = "TmIsZero " ++ toString t

isNumber :: Term -> Bool
isNumber TermZero		= True
isNumber (TermSucc t)	= isNumber t
isNumber _				= False

step :: Term -> Maybe Term
step (TermIf TermTrue t _)		= Just t
step (TermIf TermFalse _ t)		= Just t
step (TermIf t t1 t2)			= case step t of
									(Just t')	-> Just (TermIf t' t1 t2)
									Nothing		-> Nothing
step (TermSucc t)				= case step t of
									(Just t')	-> Just (TermSucc t')
									Nothing		-> Nothing
step (TermPred TermZero)		= Just TermZero
step (TermPred (TermSucc nv))
	| isNumber nv				= Just nv
	| otherwise					= Nothing
step (TermPred t)				= case step t of
									(Just t')	-> Just (TermPred t')
									Nothing		-> Nothing
step (TermIsZero TermZero)		= Just TermTrue
step (TermIsZero (TermSucc nv))
	| isNumber nv				= Just TermFalse
	| otherwise					= Nothing
step (TermIsZero t)				= case step t of
									(Just t')	-> Just (TermIsZero t')
									Nothing		-> Nothing
step _							= Nothing

eval :: Term -> Term
eval t = case step t of
			(Just t')	-> eval t'
			Nothing		-> t

eval' :: Term -> String
eval' t	= case typecheck t of
			Nothing		-> toString t ++ " is an error"
			_			-> toString t ++ " is valid and evaluates to " ++ toString (eval t)

testTermt1 :: Term
testTermt1 = TermIsZero TermZero

testTermt2 :: Term
testTermt2 = TermZero

testTermt3 :: Term
testTermt3 = TermSucc TermZero

testTermtif :: Term
testTermtif = TermIf testTermt1 testTermt2 testTermt3

testTermt4 :: Term
testTermt4 = TermIsZero (TermSucc TermZero)

testTermt5 :: Term
testTermt5 = TermIsZero TermFalse


data Type = LNum | LBool deriving (Eq, Show)

typecheck :: Term -> Maybe Type
typecheck TermTrue											= Just LBool
typecheck TermFalse											= Just LBool
typecheck TermZero											= Just LNum
typecheck (TermSucc t)		= case typecheck t of
								Just LNum					-> Just LNum
								_							-> Nothing
typecheck (TermPred t)		= case typecheck t of
								Just LNum					-> Just LNum
								_							-> Nothing
typecheck (TermIsZero t)	= case typecheck t of
								Just LNum					-> Just LBool
								_							-> Nothing
typecheck (TermIf t t1 t2)	= case (typecheck t, typecheck t1, typecheck t2) of
								(Just LNum, _, _)			-> Nothing
								(_, Just LNum, Just LNum)	-> Just LNum
								(_, Just LBool, Just LBool)	-> Just LBool
								(_,_,_)						-> Nothing


main :: IO ()
main = undefined
