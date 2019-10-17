
bigstep :: Stack -> Heap -> Expression -> Maybe (Value, Heap, Energy)
bigstep v h (EVar x) = do
	xval <- Map.lookup x v
	return (xval, h, kconst "var")
bigstep v h (ELet x e1 e2) = do
	(v1, h1, q) <- bigstep v h e1
	let v' = Map.insert x v1 v
	(v2, h2, p) <- bigstep v' h1 e2
	return (v2, h2, kconst "let1" <> q <> kconst "let2" <> p <> kconst "let3")
bigstep v h (EIf x et ef)
	| Just (VBool True) <- Map.lookup x v
	, Just (vt, h', q) <- bigstep v h et = return (vt, h', kconst "iftrue1" <> q <> kconst "iftrue2")
	| Just (VBool False) <- Map.lookup x v
	, Just (vf, h', q) <- bigstep v h ef = return (vf, h', kconst "iffalse1" <> q <> kconst "iffalse2")
	|otherwise = Nothing
