From Coq Require Import FSets.FMapList.


Definition watermark : Type := (nat*nat).

Definition dot (w1 w2: watermark) : watermark :=
  match w1,w2 with
  | (q,q') , (p,p') => if Nat.ltb p q' then (q, p' + q' - p) else (q + p - q', p')
  end.

Notation "x <.> y" := (dot x y) (at level 50, left associativity).






























