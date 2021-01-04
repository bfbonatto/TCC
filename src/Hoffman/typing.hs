{-# OPTIONS -fno-warn-tabs #-}

module Typing where

import qualified Data.Map.Strict as Map
import Language

data Type = TypeNat | TypeBool | TypeList | TypeFun Type Type deriving Eq

type Context = Map.Map Var Type

typecheck :: Context -> Term -> Maybe Type
typecheck _ (TBool _) = Just TypeBool
typecheck _ (TNum _) = Just TypeNat
typecheck g (TOp t1 _ t2) = do
	TypeNat <- typecheck g t1
	TypeNat <- typecheck g t2
	return TypeNat

typecheck g (TIf t1 t2 t3) = do
	TypeBool <- typecheck g t1
	x <- typecheck g t2
	y <- typecheck g t3
	if x == y then return x else Nothing

typecheck g (TVar x) = g Map.!? x

typecheck g (TAbs x t body) = do
	let g' = Map.insert x t g
	t' <- typecheck g' body
	return $ TypeFun t t'

typecheck g (TApp t1 t2) = do
	TypeFun type1 type2 <- typecheck g t1
	t <- typecheck g t2
	if type1 == t then return type2 else Nothing

typecheck _ TEmpty = Just TypeList

typecheck g (TList t1 t2) = do
	TypeNat <- typecheck g t1
	TypeList <- typecheck g t2
	return TypeList

typecheck g (TCase t1 t2 t3) = do
	TypeList <- typecheck g t1
	type2 <- typecheck g t2
	type3 <- typecheck g t3
	if type2 == type3 then return type2 else Nothing
