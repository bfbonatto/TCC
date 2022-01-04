From Coq Require Import Arith.
Require Import Psatz.
From TCC Require Import CpdtTactics.
Require Import List.
Import ListNotations.

From TCC Require Import Maps.

Ltac inv H := inversion H; clear H; subst.

Notation "A :: B" := (cons A B).
Notation "[]" := nil.
Notation "[[ A ]]" := (A :: nil).

Definition watermark : Type := (nat * nat).


Definition dot (w1 w2: watermark) : watermark :=
  match w1,w2 with
  | (q,q') , (p,p') => if Nat.ltb p q' then (q, p' + q' - p) else (q + p - q', p')
  end.

Notation "x <.> y" := (dot x y) (at level 50, left associativity).

Module First.

Definition eval_context := partial_map nat.

Inductive usl :=
  | ENum : nat -> usl
  | EVar : string -> usl
  | EAdd : usl -> usl -> usl
  | ELet : string -> usl -> usl -> usl.


Inductive afi : string -> usl -> Prop :=
  | afiv  : forall x, afi x (EVar x)
  | afia1 : forall x e1 e2, afi x e1 -> afi x (EAdd e1 e2)
  | afia2 : forall x e1 e2, afi x e2 -> afi x (EAdd e1 e2)
  | afil1 : forall x e1 e2 y, afi x e1 -> afi x (ELet y e1 e2)
  | afil2 : forall x e1 e2 y, x <> y -> afi x e2 -> afi x (ELet y e1 e2).


Inductive bigstep : eval_context -> usl -> (nat*watermark) -> Prop :=
  | En : forall (n: nat) (c: eval_context), bigstep c (ENum n) (n,(1,0))
  | Ev : forall (x: string) (n: nat) (c: eval_context), (c x = Some n) -> bigstep c (EVar x) (n, (1,0))
  | Ea : forall (e1 e2: usl) (n1 n2: nat) (c: eval_context) (w1 w2: watermark),
      bigstep c e1 (n1,w1) -> bigstep c e2 (n2, w2) ->
      bigstep c (EAdd e1 e2) (n1+n2, w1 <.> w2 <.> (1,0) )
  | El : forall (x: string) (e1 e2: usl) (c: eval_context) (v1 v2: nat) (w1 w2: watermark),
      bigstep c e1 (v1,w1) -> bigstep (update c x v1) e2 (v2, w2) ->
      bigstep c (ELet x e1 e2) (v2, (1,0) <.> w1 <.> (1,0) <.> w2 <.> (1,0)).

Fixpoint subst (x: string) (t: usl) (s: usl) : usl :=
  match s with
  | ENum x => s
  | EVar y => if eqb_string x y then t else s
  | EAdd e1 e2 => EAdd (subst x t e1) (subst x t e2)
  | ELet y e1 e2 => ELet y (subst x t e1) (if eqb_string x y then e2 else (subst x t e2))
  end.


Inductive type :=
  | I.

Definition context := partial_map type.

Inductive analyse : context -> usl -> (type*watermark) -> Prop :=
  | Ln : forall (n: nat) (c: context), analyse c (ENum n) (I,(1,0))
  | Lv : forall (x: string) (t: type) (c: context), c x = Some t -> analyse c (EVar x) (t,(1,0))
  | La : forall (e1 e2: usl) (c: context) (w1 w2: watermark),
      analyse c e1 (I,w1) -> analyse c e2 (I,w2) -> analyse c (EAdd e1 e2) (I, w1 <.> w2 <.> (1,0))
  | Ll : forall (e1 e2: usl) (x: string) (c: context) (w1 w2: watermark) (a b: type),
      analyse c e1 (a,w1) -> analyse (update c x a) e2 (b,w2) ->
      analyse c (ELet x e1 e2) (b, (1,0) <.> w1 <.> (1,0) <.> w2 <.> (1,0)).




Theorem tight_bound : forall e v w c1 c2,
  bigstep c1 e (v,w) -> (forall (x:string) (v:nat), afi x e -> c1 x = Some v -> c2 x = Some I)
  -> analyse c2 e (I,w).
Proof.
  induction e; intros.
  - inv H; apply Ln.
  - inv H. eapply Lv. eapply H0; eauto. apply afiv.
  - inv H. eapply La. eapply IHe1; eauto. intros; subst. eapply H0.
    apply afia1; auto. eauto. eapply IHe2; eauto; intros; subst; eapply H0.
    apply afia2; auto; eauto. eauto.
  - inv H. eapply Ll. eapply IHe1; eauto. intros.
    eapply H0. apply afil1. auto. eauto. eapply IHe2; eauto. intros.
    destruct (eqb_string x s) eqn:eq. rewrite eqb_string_true_iff in eq; subst.
    apply update_eq. rewrite eqb_string_false_iff in eq. rewrite update_neq.
    rewrite update_neq in H1. eapply H0; eauto. apply afil2. auto. auto.
    auto. auto.
Qed.

Lemma equal_bounds : forall w e v,
  bigstep empty e (v,w) -> analyse empty e (I,w).
Proof.
  intros. eapply tight_bound. apply H.
  intros. inv H1.
Qed.

End First.


Definition weakened (w1 w2: watermark) : Prop :=
  (fst w1 >= fst w2) /\ ((fst w1 - fst w2) >= (snd w1 - snd w2)).

Lemma max_choice : forall x y, max x y = x \/ max x y = y.
Proof.
  induction x,y; lia.
Qed.

Lemma min_choice : forall x y, min x y = x \/ min x y = y.
Proof.
  induction x,y; lia.
Qed.

Ltac rew :=
  match goal with
  | H: ?n1 <? ?n2 = true |- _ => rewrite Nat.ltb_lt in H
  | H: ?n1 <? ?n2 = false |- _ => rewrite Nat.ltb_ge in H
  end.

Ltac destr n1 n2 := destruct (n1 <? n2) eqn:?.
Ltac dd n := destruct n eqn:?.


Ltac sl := simpl; try lia.



Lemma ge_weak : forall q q' p w, p >= q -> weakened (q,q') w -> weakened (p, q') w.
Proof.
  induction q; intros.
  - inv H0. unfold weakened. simpl in *. inv H1. rewrite H3.
    lia.
  - inv H0. unfold weakened. simpl in *. dd (fst w). lia.
    lia.
Qed.

Lemma weak_trans : forall w1 w2 w3, weakened w1 w2 -> weakened w2 w3 -> weakened w1 w3.
Proof.
  intros. destruct w1, w2, w3. induction n; intros.
  - inv H; inv H0; simpl in *. inv H1. inv H2. inv H. inv H3.
    unfold weakened. simpl. rewrite H1. rewrite H0. lia.
  - unfold weakened in *. simpl in *. dd n1; dd n3; lia.
Qed.

Lemma weak_dot : forall w1 w2 w3, weakened w1 w2 -> weakened (w1 <.> w3) (w2 <.> w3).
Proof.
  intros. destruct w1, w2, w3. unfold weakened in *.
  simpl in *. inv H. destr n3 n0; destr n3 n2; simpl; repeat rew; lia.
Qed.


Lemma weak_dot' : forall w1 w2 w3 w4, weakened w1 w2 -> weakened w3 w4 -> weakened (w1 <.> w3) (w2 <.> w4).
Proof.
  intros. destruct w1, w2, w3, w4. inv H; inv H0. unfold weakened. simpl in *.
  destr n3 n0; destr n5 n2; simpl; repeat rew; lia.
Qed.

Lemma dot_left_assoc : forall w1 w2 w3, w1 <.> (w2 <.> w3) = (w1 <.> w2) <.> w3.
Proof.
  intros. destruct w1, w2, w3. simpl. destr n3 n2; destr n1 n0; simpl;
  try (rewrite Heqb); simpl; destr n3 (n2 + n0 - n1); destr (n1 + n3 - n2) n0;
  simpl; repeat rew; crush. Qed.

Lemma weak_S : forall q q' p p', weakened (p,p') (q,q') -> weakened (S p, p') (S q, q').
Proof.
  intros. inv H. unfold weakened. simpl in *. lia.
Qed.


Module Booleans.


Inductive usl :=
  | ENum  : nat -> usl
  | EVar  : string -> usl
  | EAdd  : usl -> usl -> usl
  | ELet  : string -> usl -> usl -> usl
  | EBool : bool -> usl
  | ECond : usl -> usl -> usl -> usl.

Inductive afi : string -> usl -> Prop :=
  | afiv  : forall x, afi x (EVar x)
  | afia1 : forall x e1 e2, afi x e1 -> afi x (EAdd e1 e2)
  | afia2 : forall x e1 e2, afi x e2 -> afi x (EAdd e1 e2)
  | afil1 : forall x e1 e2 y, afi x e1 -> afi x (ELet y e1 e2)
  | afil2 : forall x e1 e2 y, x <> y -> afi x e2 -> afi x (ELet y e1 e2)
  | afii1 : forall x e1 e2 e3, afi x e1 -> afi x (ECond e1 e2 e3)
  | afii2 : forall x e1 e2 e3, afi x e2 -> afi x (ECond e1 e2 e3)
  | afii3 : forall x e1 e2 e3, afi x e3 -> afi x (ECond e1 e2 e3).


Inductive val :=
  | Vn : nat -> val
  | Vb : bool -> val.

Definition eval_context := partial_map val.

Inductive bigstep : eval_context -> usl -> (val*watermark) -> Prop :=
  | En : forall (n: nat) (c: eval_context), bigstep c (ENum n) (Vn n,(1,0))
  | Ev : forall (x: string) (v: val) (c: eval_context), (c x = Some v) -> bigstep c (EVar x) (v, (1,0))
  | Ea : forall (e1 e2: usl) (n1 n2: nat) (c: eval_context) (w1 w2: watermark),
      bigstep c e1 (Vn n1,w1) -> bigstep c e2 (Vn n2, w2) ->
      bigstep c (EAdd e1 e2) (Vn (n1+n2), w1 <.> w2 <.> (1,0))
  | El : forall (x: string) (e1 e2: usl) (c: eval_context) (v1 v2: val) (w1 w2: watermark),
      bigstep c e1 (v1,w1) -> bigstep (update c x v1) e2 (v2, w2) ->
      bigstep c (ELet x e1 e2) (v2, (1,0) <.> w1 <.> (1,0) <.> w2 <.> (1,0))
  | Eb : forall (b: bool) (c: eval_context), bigstep c (EBool b) (Vb b, (1,0))
  | Et : forall (c: eval_context) (w1 w2: watermark) (e1 e2 e3: usl) (v: val),
      bigstep c e1 (Vb true, w1) -> bigstep c e2 (v,w2) ->
      bigstep c (ECond e1 e2 e3) (v, w1 <.> (1,0) <.> w2)
  | Ef : forall (c: eval_context) (w1 w3: watermark) (e1 e2 e3: usl) (v: val),
      bigstep c e1 (Vb false, w1) -> bigstep c e3 (v,w3) ->
      bigstep c (ECond e1 e2 e3) (v, w1 <.> (1,0) <.> w3).

Fixpoint subst (x: string) (t: nat) (s: usl) : usl :=
  match s with
  | ENum  x => s
  | EVar  y => if eqb_string x y then (ENum t) else s
  | EAdd  e1 e2 => EAdd (subst x t e1) (subst x t e2)
  | ELet  y e1 e2 => ELet y (subst x t e1) (if eqb_string x y then e2 else (subst x t e2))
  | EBool b => s
  | ECond e1 e2 e3 => ECond (subst x t e1) (subst x t e2) (subst x t e3)
  end.


Inductive type :=
  | I
  | B.

Definition context := partial_map type.


Inductive analyse : context -> usl -> (type*watermark) -> Prop :=
  | Ln : forall (n: nat) (c: context), analyse c (ENum n) (I,(1,0))
  | Lv : forall (x: string) (t: type) (c: context), c x = Some t -> analyse c (EVar x) (t,(1,0))
  | La : forall (e1 e2: usl) (c: context) (w1 w2: watermark),
      analyse c e1 (I,w1) -> analyse c e2 (I,w2) -> analyse c (EAdd e1 e2) (I, w1 <.> w2 <.> (1,0))
  | Ll : forall (e1 e2: usl) (x: string) (c: context) (w1 w2: watermark) (a b: type),
      analyse c e1 (a,w1) -> analyse (update c x a) e2 (b,w2) ->
      analyse c (ELet x e1 e2) (b, (1,0) <.> w1 <.> (1,0) <.> w2 <.> (1,0))
  | Lb : forall (b: bool) (c: context), analyse c (EBool b) (B,(1,0))
  | Lc : forall (e1 e2 e3: usl) (w: watermark) (q1 q2 q1' q2' : nat) (c: context) (t: type),
      analyse c e1 (B,w) -> analyse c e2 (t,(q1,q1')) -> analyse c e3 (t,(q2,q2')) ->
      analyse c (ECond e1 e2 e3) (t, w <.> (1,0) <.> (max q1 q2, min q1' q2')).


Definition typeOf (v: val) : type :=
  match v with
  | Vn n => I
  | Vb b => B
  end.


Definition equiv_c (c1: eval_context) (c2: context) : Prop :=
  forall x v, c1 x = Some v -> c2 x = Some (typeOf v).

Lemma extend_equiv_c :
  forall c1 c2 x v, equiv_c c1 c2 -> equiv_c (x |-> v ; c1) (x |-> (typeOf v) ; c2).
Proof.
  intros. unfold equiv_c in *. intros. destruct (eqb_string x x0) eqn:eq.
  - rewrite eqb_string_true_iff in eq. subst. rewrite update_eq in H0. inv H0.
    rewrite update_eq. auto.
  - rewrite eqb_string_false_iff in eq. rewrite update_neq. apply H.
    rewrite update_neq in H0. auto. auto. auto.
Qed.

Theorem preservation : forall e v t w1 w2 c1 c2, equiv_c c2 c1 ->
  analyse c1 e (t,w1) -> bigstep c2 e (v,w2) -> t = typeOf v.
Proof.
  induction e; intros v t w1 w2 c1 c2 ceq H1 H2;
  try (solve [inv H1; inv H2; auto]).
  - inv H1. inv H2. unfold equiv_c in ceq. pose (ceq s v H3).
    rewrite e in H4. inv H4; auto.
  - inv H1; inv H2. assert (a = typeOf v1). eapply IHe1; eauto.
    subst. eapply IHe2. eapply extend_equiv_c. apply ceq.
    apply H8. apply H9.
  - inv H1; inv H2.
    + eapply IHe2; eauto.
    + eapply IHe3; eauto.
Qed.





Theorem bound : forall e v t w1 w2 c1 c2, equiv_c c2 c1 ->
  analyse c1 e (t, w1) -> bigstep c2 e (v,w2) -> weakened w1 w2.
Proof.
  Hint Unfold weakened : core.
  induction e; intros v t w1 w2 c1 c2 ceq H1 H2;
  try (solve [inv H1; inv H2; auto]).
  - inv H1; inv H2. assert (weakened w0 w1).
    eapply IHe1; eauto. assert (weakened w3 w4).
    eapply IHe2; eauto. destruct w0, w1, w3, w4.
    eapply weak_dot'. inv H; inv H0. unfold weakened. simpl in *.
    destr n5 n0; destr n7 n4; repeat rew; simpl; lia. auto.
  - inv H1; inv H2. assert (weakened w0 w1); eauto.
    assert (a = typeOf v1). eapply preservation; eauto.
    subst. assert (weakened w3 w4). eapply IHe2. eapply extend_equiv_c. apply ceq.
    eapply H8. eapply H9. destruct w0, w1, w3, w4.
    repeat (rewrite <- dot_left_assoc). eapply weak_dot'.
    apply weak_S; auto. repeat rewrite dot_left_assoc.
    assert ((1, 0) <.> (n3, n4) <.> (1, 0) = (S n3, n4) <.> (1,0)).
    auto. rewrite H1. assert  ((1, 0) <.> (n5, n6) <.> (1, 0) = (S n5, n6) <.> (1,0)).
    auto. rewrite H2. eapply weak_dot. apply weak_S. apply H0.
  - inv H1; inv H2; assert (weakened w w1); eauto;
    destruct w, w1; [destruct w0 | destruct w3];
    [assert (weakened (q1, q1') (n3, n4)); eauto |
    assert (weakened (q2, q2') (n3, n4)); eauto].
    eapply weak_dot'. apply weak_dot; auto.
    + destruct (max_choice q1 q2), (min_choice q1' q2');
      rewrite H1, H2; try (solve [apply H0]);
      try (rewrite Nat.min_r_iff in H2);
      try (rewrite Nat.min_l_iff in H2);
      try (rewrite Nat.max_r_iff in H1);
      try (rewrite Nat.max_l_iff in H1);
      inv H0; inv H2; unfold weakened; split; simpl in *; try lia.
      dd n4. lia. lia. dd n4. lia. lia.
    + eapply weak_dot'. apply weak_dot; eauto.
      destruct (max_choice q1 q2), (min_choice q1' q2');
      rewrite H1, H2; try (solve [apply H0]);
      try (rewrite Nat.min_r_iff in H2);
      try (rewrite Nat.min_l_iff in H2);
      try (rewrite Nat.max_r_iff in H1);
      try (rewrite Nat.max_l_iff in H1);
      inv H0; inv H2; unfold weakened; split; simpl in *; try lia.
      dd n4. lia. lia. dd n4. lia. lia.
Qed.

End Booleans.

Module FixedCosts.


Definition eval_context := partial_map nat.

Inductive usl :=
  | ENum : nat -> usl
  | EVar : string -> usl
  | EAdd : usl -> usl -> usl
  | ELet : string -> usl -> usl -> usl.


Inductive afi : string -> usl -> Prop :=
  | afiv  : forall x, afi x (EVar x)
  | afia1 : forall x e1 e2, afi x e1 -> afi x (EAdd e1 e2)
  | afia2 : forall x e1 e2, afi x e2 -> afi x (EAdd e1 e2)
  | afil1 : forall x e1 e2 y, afi x e1 -> afi x (ELet y e1 e2)
  | afil2 : forall x e1 e2 y, x <> y -> afi x e2 -> afi x (ELet y e1 e2).


Inductive bigstep : eval_context -> usl -> (nat*watermark) -> Prop :=
  | En : forall (n: nat) (c: eval_context), bigstep c (ENum n) (n,(1,0))
  | Ev : forall (x: string) (n: nat) (c: eval_context), (c x = Some n) -> bigstep c (EVar x) (n, (1,0))
  | Ea : forall (e1 e2: usl) (n1 n2: nat) (c: eval_context) (w1 w2: watermark),
      bigstep c e1 (n1,w1) -> bigstep c e2 (n2, w2) ->
      bigstep c (EAdd e1 e2) (n1+n2, w1 <.> w2 <.> (3,0) )
  | El : forall (x: string) (e1 e2: usl) (c: eval_context) (v1 v2: nat) (w1 w2: watermark),
      bigstep c e1 (v1,w1) -> bigstep (update c x v1) e2 (v2, w2) ->
      bigstep c (ELet x e1 e2) (v2, w1 <.> (2,0) <.> w2 <.> (1,0)).

Fixpoint subst (x: string) (t: usl) (s: usl) : usl :=
  match s with
  | ENum x => s
  | EVar y => if eqb_string x y then t else s
  | EAdd e1 e2 => EAdd (subst x t e1) (subst x t e2)
  | ELet y e1 e2 => ELet y (subst x t e1) (if eqb_string x y then e2 else (subst x t e2))
  end.


Inductive type :=
  | I.

Definition context := partial_map type.

Inductive analyse : context -> usl -> (type*watermark) -> Prop :=
  | Ln : forall (n: nat) (c: context), analyse c (ENum n) (I,(1,0))
  | Lv : forall (x: string) (t: type) (c: context), c x = Some t -> analyse c (EVar x) (t,(1,0))
  | La : forall (e1 e2: usl) (c: context) (w1 w2: watermark),
      analyse c e1 (I,w1) -> analyse c e2 (I,w2) -> analyse c (EAdd e1 e2) (I, w1 <.> w2 <.> (3,0))
  | Ll : forall (e1 e2: usl) (x: string) (c: context) (w1 w2: watermark) (a b: type),
      analyse c e1 (a,w1) -> analyse (update c x a) e2 (b,w2) ->
      analyse c (ELet x e1 e2) (b, w1 <.> (2,0) <.> w2 <.> (1,0)).




Theorem tight_bound : forall e v w c1 c2,
  bigstep c1 e (v,w) -> (forall (x:string) (v:nat), afi x e -> c1 x = Some v -> c2 x = Some I)
  -> analyse c2 e (I,w).
Proof.
  induction e; intros.
  - inv H; apply Ln.
  - inv H. eapply Lv. eapply H0; eauto. apply afiv.
  - inv H. eapply La. eapply IHe1; eauto. intros; subst. eapply H0.
    apply afia1; auto. eauto. eapply IHe2; eauto; intros; subst; eapply H0.
    apply afia2; auto; eauto. eauto.
  - inv H. eapply Ll. eapply IHe1; eauto. intros.
    eapply H0. apply afil1. auto. eauto. eapply IHe2; eauto. intros.
    destruct (eqb_string x s) eqn:eq. rewrite eqb_string_true_iff in eq; subst.
    apply update_eq. rewrite eqb_string_false_iff in eq. rewrite update_neq.
    rewrite update_neq in H1. eapply H0; eauto. apply afil2. auto. auto.
    auto. auto.
Qed.

Lemma equal_bounds : forall w e v,
  bigstep empty e (v,w) -> analyse empty e (I,w).
Proof.
  intros. eapply tight_bound. apply H.
  intros. inv H1.
Qed.



Definition ide := string.
Definition env := partial_map.

Inductive inst :=
  | NAT : nat -> inst
  | ADD : inst
  | LET : ide -> inst
  | RET : inst
  | VAR : ide -> inst.

Definition code := list inst.
Definition stack := list nat.
Definition environment := list (env nat).

Definition ssm : Type := (code * stack * environment).

Fixpoint compile (e: usl) : code :=
  match e with
  | ENum n => [[NAT n]]
  | EVar x => [[VAR x]]
  | EAdd e1 e2 => (compile e1) ++ (compile e2) ++ [[ADD]]
  | ELet x e1 e2 => (compile e1) ++ [[LET x]] ++ (compile e2) ++ [[RET]]
  end.

Lemma compile_not_empty : forall e, ~(compile e = []).
Proof.
  induction e; simpl; intro; inv H.
  eapply app_eq_nil in H1.
  destruct H1. eapply app_eq_nil in H0. destruct H0.
  inv H1. eapply app_eq_nil in H1. destruct H1. destruct IHe1.
  auto. Qed.

Lemma app_nil : forall (T: Type) (a b : list T), a ++ b = b -> a = [].
Proof.
  induction a; intros; auto.
   simpl in H. assert (Datatypes.length (a :: a0 ++ b) = Datatypes.length b).
   rewrite H. auto. simpl in H0. Search (Datatypes.length (?a ++ ?b)).
   rewrite app_length in H0. lia. Qed.

Reserved Notation "A |> B" (at level 90, no associativity).
Inductive ssm_op : ssm -> ssm -> Prop :=
  | push_nat : forall n c s e, ((NAT n) :: c, s, e) |> (c, n :: s, e)
  | apply_add : forall c s e n1 n2,
      (ADD :: c, n1 :: n2 :: s, e) |> (c, (n1+n2)::s, e)
  | var_lookup : forall c s e es x n,
      e x = Some n ->
      ((VAR x) :: c, s, e::es) |> (c, n :: s, e::es)
  | apply_let : forall x c v s e es,
      ((LET x) :: c, v::s, e::es) |> (c, s, (x|->v; e)::e::es)
  | apply_ret : forall c s e es,
      (RET :: c, s, e::es) |> (c, s, es)
  | apply_ret_empty : forall c s e,
      (RET :: c, s, [[e]]) |> (c, s, [[e]])
where "A |> B" := (ssm_op A B).


Import Coq.Relations.Relation_Operators.

Definition multi := clos_refl_trans.

Definition multi_op := multi ssm ssm_op.

Notation "A |*> B" := (multi_op A B) (at level 90, no associativity).

Theorem strong_correct_compilation : forall e v w env,
  bigstep env e (v,w) ->
  forall code stack envs, (compile e ++ code, stack, env::envs) |*>
    (code, v::stack, env::envs).
Proof.
  induction e; intros; simpl.
  - inv H. eapply rt_step. eapply push_nat.
  - inv H. eapply rt_step. eapply var_lookup. auto.
  - inv H. repeat (rewrite <- app_assoc).
    eapply rt_trans. eapply IHe1. apply H4.
    eapply rt_trans. eapply IHe2. apply H6.
    rewrite Nat.add_comm. eapply rt_step.
    apply apply_add.
  - inv H. repeat (rewrite <- app_assoc).
    eapply rt_trans. eapply IHe1. apply H3.
    eapply rt_trans. eapply rt_step. simpl. eapply apply_let.
    eapply rt_trans. rewrite <- app_assoc.
    eapply IHe2. apply H7. eapply rt_step.
    apply apply_ret.
Qed.

Theorem correct_compilation : forall e v w,
  bigstep empty e (v, w) -> (compile e, [], [[empty]])
    |*> ([], [[v]], [[empty]]).
Proof.
  intros. pose (strong_correct_compilation e v w empty).
  pose (m H [] [] []). rewrite app_nil_r in m0.
  apply m0.
Qed.

Inductive ssm_cost : ssm -> ssm -> watermark -> Prop :=
  | nat_cost : forall n c s e ssm, ((NAT n)::c, s, e) |> ssm ->
      ssm_cost ((NAT n)::c, s, e) ssm (1,0)
  | add_cost : forall c s e ssm, (ADD::c, s, e) |> ssm ->
      ssm_cost (ADD::c, s, e) ssm (3,0)
  | var_cost : forall x c s e ssm, ((VAR x)::c, s, e) |> ssm ->
      ssm_cost ((VAR x)::c, s, e) ssm (1,0)
  | let_cost : forall x c s e ssm, ((LET x)::c, s, e) |> ssm ->
      ssm_cost ((LET x)::c, s, e) ssm (2,0)
  | ret_cost : forall c s e ssm, (RET :: c,s,e) |> ssm ->
      ssm_cost (RET :: c,s,e) ssm (1,0).

Notation "[ A | B | w ]" := (ssm_cost A B w).

Inductive ssm_multi_cost : ssm -> ssm -> watermark -> Prop :=
  | smc_refl : forall ssm, ssm_multi_cost ssm ssm (0,0)
  | smc_step : forall ssm1 ssm2 w, [ssm1 | ssm2 | w] ->
      ssm_multi_cost ssm1 ssm2 w
  | smc_trans : forall ssm1 ssm2 ssm3 w1 w2, ssm_multi_cost ssm1 ssm2 w1 ->
      ssm_multi_cost ssm2 ssm3 w2 -> ssm_multi_cost ssm1 ssm3 (w1 <.> w2).

Notation "[ A | B | w ]*" := (ssm_multi_cost A B w).

Theorem strong_cost_correct : forall e v w env,
  bigstep env e (v,w) ->
  forall code stack envs, [(compile e ++ code, stack, env::envs) | (code, v::stack, env::envs) | w]*.
Proof.
  induction e; intros.
  - inv H. simpl. apply smc_step. apply nat_cost. apply push_nat.
  - inv H. simpl. apply smc_step. apply var_cost. apply var_lookup. auto.
  - inv H. simpl. pose (IHe1 n1 w1 env0 H4). pose (IHe2 n2 w2 env0 H6).
    eapply smc_trans. eapply smc_trans. repeat rewrite <- app_assoc.
    eapply s. eapply s0. eapply smc_step. apply add_cost. rewrite Nat.add_comm.
    eapply apply_add.
  - inv H. simpl. pose (IHe1 v1 w1 env0 H3). pose (IHe2 v w2 (s|->v1; env0) H7).
    eapply smc_trans. eapply smc_trans. eapply smc_trans.
    assert (((compile e1 ++ LET s :: compile e2 ++ [[RET]]) ++ code0 =
     compile e1 ++ [[LET s]] ++ compile e2 ++ [[RET]] ++ code0)). crush.
     rewrite H. eapply s0. eapply smc_step. apply let_cost. apply apply_let.
     eapply s1. eapply smc_step. apply ret_cost. apply apply_ret.
Qed.

End FixedCosts.

Module ConditionalCosts.

Inductive usl :=
  | ENum  : nat -> usl
  | EVar  : string -> usl
  | EAdd  : usl -> usl -> usl
  | ELet  : string -> usl -> usl -> usl
  | EBool : bool -> usl
  | ECond : usl -> usl -> usl -> usl.

Inductive afi : string -> usl -> Prop :=
  | afiv  : forall x, afi x (EVar x)
  | afia1 : forall x e1 e2, afi x e1 -> afi x (EAdd e1 e2)
  | afia2 : forall x e1 e2, afi x e2 -> afi x (EAdd e1 e2)
  | afil1 : forall x e1 e2 y, afi x e1 -> afi x (ELet y e1 e2)
  | afil2 : forall x e1 e2 y, x <> y -> afi x e2 -> afi x (ELet y e1 e2)
  | afii1 : forall x e1 e2 e3, afi x e1 -> afi x (ECond e1 e2 e3)
  | afii2 : forall x e1 e2 e3, afi x e2 -> afi x (ECond e1 e2 e3)
  | afii3 : forall x e1 e2 e3, afi x e3 -> afi x (ECond e1 e2 e3).


Inductive val :=
  | Vn : nat -> val
  | Vb : bool -> val.

Definition eval_context := partial_map val.

Inductive bigstep : eval_context -> usl -> (val*watermark) -> Prop :=
  | En : forall (n: nat) (c: eval_context), bigstep c (ENum n) (Vn n,(1,0))
  | Ev : forall (x: string) (v: val) (c: eval_context), (c x = Some v) -> bigstep c (EVar x) (v, (1,0))
  | Ea : forall (e1 e2: usl) (n1 n2: nat) (c: eval_context) (w1 w2: watermark),
      bigstep c e1 (Vn n1,w1) -> bigstep c e2 (Vn n2, w2) ->
      bigstep c (EAdd e1 e2) (Vn (n1+n2), w1 <.> w2 <.> (3,0))
  | El : forall (x: string) (e1 e2: usl) (c: eval_context) (v1 v2: val) (w1 w2: watermark),
      bigstep c e1 (v1,w1) -> bigstep (update c x v1) e2 (v2, w2) ->
      bigstep c (ELet x e1 e2) (v2, w1 <.> (2,0) <.> w2 <.> (1,0))
  | Eb : forall (b: bool) (c: eval_context), bigstep c (EBool b) (Vb b, (1,0))
  | Et : forall (c: eval_context) (w1 w2: watermark) (e1 e2 e3: usl) (v: val),
      bigstep c e1 (Vb true, w1) -> bigstep c e2 (v,w2) ->
      bigstep c (ECond e1 e2 e3) (v, w1 <.> (1,0) <.> w2)
  | Ef : forall (c: eval_context) (w1 w3: watermark) (e1 e2 e3: usl) (v: val),
      bigstep c e1 (Vb false, w1) -> bigstep c e3 (v,w3) ->
      bigstep c (ECond e1 e2 e3) (v, w1 <.> (1,0) <.> w3).

Fixpoint subst (x: string) (t: nat) (s: usl) : usl :=
  match s with
  | ENum  x => s
  | EVar  y => if eqb_string x y then (ENum t) else s
  | EAdd  e1 e2 => EAdd (subst x t e1) (subst x t e2)
  | ELet  y e1 e2 => ELet y (subst x t e1) (if eqb_string x y then e2 else (subst x t e2))
  | EBool b => s
  | ECond e1 e2 e3 => ECond (subst x t e1) (subst x t e2) (subst x t e3)
  end.


Inductive type :=
  | I
  | B.

Definition context := partial_map type.


Inductive analyse : context -> usl -> (type*watermark) -> Prop :=
  | Ln : forall (n: nat) (c: context), analyse c (ENum n) (I,(1,0))
  | Lv : forall (x: string) (t: type) (c: context), c x = Some t -> analyse c (EVar x) (t,(1,0))
  | La : forall (e1 e2: usl) (c: context) (w1 w2: watermark),
      analyse c e1 (I,w1) -> analyse c e2 (I,w2) -> analyse c (EAdd e1 e2) (I, w1 <.> w2 <.> (3,0))
  | Ll : forall (e1 e2: usl) (x: string) (c: context) (w1 w2: watermark) (a b: type),
      analyse c e1 (a,w1) -> analyse (update c x a) e2 (b,w2) ->
      analyse c (ELet x e1 e2) (b, w1 <.> (2,0) <.> w2 <.> (1,0))
  | Lb : forall (b: bool) (c: context), analyse c (EBool b) (B,(1,0))
  | Lc : forall (e1 e2 e3: usl) (w: watermark) (q1 q2 q1' q2' : nat) (c: context) (t: type),
      analyse c e1 (B,w) -> analyse c e2 (t,(q1,q1')) -> analyse c e3 (t,(q2,q2')) ->
      analyse c (ECond e1 e2 e3) (t, w <.> (1,0) <.> (max q1 q2, min q1' q2')).


Definition typeOf (v: val) : type :=
  match v with
  | Vn n => I
  | Vb b => B
  end.


Definition equiv_c (c1: eval_context) (c2: context) : Prop :=
  forall x v, c1 x = Some v -> c2 x = Some (typeOf v).

Lemma extend_equiv_c :
  forall c1 c2 x v, equiv_c c1 c2 -> equiv_c (x |-> v ; c1) (x |-> (typeOf v) ; c2).
Proof.
  intros. unfold equiv_c in *. intros. destruct (eqb_string x x0) eqn:eq.
  - rewrite eqb_string_true_iff in eq. subst. rewrite update_eq in H0. inv H0.
    rewrite update_eq. auto.
  - rewrite eqb_string_false_iff in eq. rewrite update_neq. apply H.
    rewrite update_neq in H0. auto. auto. auto.
Qed.

Theorem preservation : forall e v t w1 w2 c1 c2, equiv_c c2 c1 ->
  analyse c1 e (t,w1) -> bigstep c2 e (v,w2) -> t = typeOf v.
Proof.
  induction e; intros v t w1 w2 c1 c2 ceq H1 H2;
  try (solve [inv H1; inv H2; auto]).
  - inv H1. inv H2. unfold equiv_c in ceq. pose (ceq s v H3).
    rewrite e in H4. inv H4; auto.
  - inv H1; inv H2. assert (a = typeOf v1). eapply IHe1; eauto.
    subst. eapply IHe2. eapply extend_equiv_c. apply ceq.
    apply H8. apply H9.
  - inv H1; inv H2.
    + eapply IHe2; eauto.
    + eapply IHe3; eauto.
Qed.





Theorem bound : forall e v t w1 w2 c1 c2, equiv_c c2 c1 ->
  analyse c1 e (t, w1) -> bigstep c2 e (v,w2) -> weakened w1 w2.
Proof.
  Hint Unfold weakened : core.
  induction e; intros v t w1 w2 c1 c2 ceq H1 H2;
  try (solve [inv H1; inv H2; auto]).
  - inv H1; inv H2. assert (weakened w0 w1).
    eapply IHe1; eauto. assert (weakened w3 w4).
    eapply IHe2; eauto. destruct w0, w1, w3, w4.
    eapply weak_dot'. inv H; inv H0. unfold weakened. simpl in *.
    destr n5 n0; destr n7 n4; repeat rew; simpl; lia. auto.
  - inv H1; inv H2. assert (weakened w0 w1); eauto.
    assert (a = typeOf v1). eapply preservation; eauto.
    subst. assert (weakened w3 w4). eapply IHe2. eapply extend_equiv_c. apply ceq.
    eapply H8. eapply H9. destruct w0, w1, w3, w4.
    repeat (rewrite <- dot_left_assoc). eapply weak_dot'.
    auto. repeat rewrite dot_left_assoc.
    eapply weak_dot. apply weak_S. apply weak_S. apply H0.
  - inv H1; inv H2; assert (weakened w w1); eauto;
    destruct w, w1; [destruct w0 | destruct w3];
    [assert (weakened (q1, q1') (n3, n4)); eauto |
    assert (weakened (q2, q2') (n3, n4)); eauto].
    eapply weak_dot'. apply weak_dot; auto.
    + destruct (max_choice q1 q2), (min_choice q1' q2');
      rewrite H1, H2; try (solve [apply H0]);
      try (rewrite Nat.min_r_iff in H2);
      try (rewrite Nat.min_l_iff in H2);
      try (rewrite Nat.max_r_iff in H1);
      try (rewrite Nat.max_l_iff in H1);
      inv H0; inv H2; unfold weakened; split; simpl in *; try lia.
      dd n4. lia. lia. dd n4. lia. lia.
    + eapply weak_dot'. apply weak_dot; eauto.
      destruct (max_choice q1 q2), (min_choice q1' q2');
      rewrite H1, H2; try (solve [apply H0]);
      try (rewrite Nat.min_r_iff in H2);
      try (rewrite Nat.min_l_iff in H2);
      try (rewrite Nat.max_r_iff in H1);
      try (rewrite Nat.max_l_iff in H1);
      inv H0; inv H2; unfold weakened; split; simpl in *; try lia.
      dd n4. lia. lia. dd n4. lia. lia.
Qed.


Definition ide := string.
Definition env := partial_map.

Inductive inst :=
  | NAT : nat -> inst
  | ADD : inst
  | LET : ide -> inst
  | RET : inst
  | JZ  : nat -> inst
  | JMP : nat -> inst
  | VAR : ide -> inst.

Definition code := list inst.
Definition stack := list nat.
Definition environment := list (env nat).

Definition ssm : Type := (code * stack * environment).

Fixpoint compile (e: usl) : code :=
  match e with
  | ENum n => [[NAT n]]
  | EVar x => [[VAR x]]
  | EAdd e1 e2 => (compile e1) ++ (compile e2) ++ [[ADD]]
  | ELet x e1 e2 => (compile e1) ++ [[LET x]] ++ (compile e2) ++ [[RET]]
  | EBool true => [[NAT 1]]
  | EBool false => [[NAT 0]]
  | ECond e1 e2 e3 => let n := Datatypes.length (compile e2) in
                      let m := Datatypes.length (compile e3) in
      (compile e1) ++ [[JZ (S n)]] ++ (compile e2) ++ [[JMP m]] ++ (compile e3)
  end.


Lemma compile_not_empty : forall e, ~(compile e = []).
Proof.
  induction e; simpl; intro; inv H.
  eapply app_eq_nil in H1.
  destruct H1. eapply app_eq_nil in H0. destruct H0.
  inv H1. eapply app_eq_nil in H1. destruct H1. destruct IHe1.
  auto.
  destruct b. inv H1. inv H1. eapply app_eq_nil in H1. destruct H1.
  destruct IHe1. apply H. Qed.

Lemma app_nil : forall (T: Type) (a b : list T), a ++ b = b -> a = [].
Proof.
  induction a; intros; auto.
   simpl in H. assert (Datatypes.length (a :: a0 ++ b) = Datatypes.length b).
   rewrite H. auto. simpl in H0. Search (Datatypes.length (?a ++ ?b)).
   rewrite app_length in H0. lia. Qed.


Reserved Notation "A |> B" (at level 90, no associativity).
Inductive ssm_op : ssm -> ssm -> Prop :=
  | push_nat : forall n c s e, ((NAT n) :: c, s, e) |> (c, n :: s, e)
  | apply_add : forall c s e n1 n2,
      (ADD :: c, n1 :: n2 :: s, e) |> (c, (n1+n2)::s, e)
  | var_lookup : forall c s e es x n,
      e x = Some n ->
      ((VAR x) :: c, s, e::es) |> (c, n :: s, e::es)
  | apply_let : forall x c v s e es,
      ((LET x) :: c, v::s, e::es) |> (c, s, (x|->v; e)::e::es)
  | apply_ret : forall c s e es,
      (RET :: c, s, e::es) |> (c, s, es)
  | apply_ret_empty : forall c s e,
      (RET :: c, s, [[e]]) |> (c, s, [[e]])
  | apply_jmp : forall c s e n,
      (JMP n :: c, s, e) |> (skipn n c, s, e)
  | apply_jmp_zero : forall c s e n,
      (JZ n :: c, 0 :: s, e) |> (skipn n c, s, e)
  | apply_jmp_one : forall c s e n x,
      (JZ n :: c, S x :: s, e) |> (c, s, e)
where "A |> B" := (ssm_op A B).


Import Coq.Relations.Relation_Operators.

Definition multi := clos_refl_trans.

Definition multi_op := multi ssm ssm_op.

Notation "A |*> B" := (multi_op A B) (at level 90, no associativity).

Definition value_match (v: val) : nat :=
  match v with
  | Vn n => n
  | Vb true => 1
  | Vb false => 0
  end.

Definition env_ssm_equiv (e1: eval_context) (e2: env nat) : Prop :=
  forall x v, (e1 x = None -> e2 x = None) /\
              (e1 x = Some v -> e2 x = Some (value_match v)).


Lemma extend_ssm_equiv : forall s v e1 e2,
  env_ssm_equiv e1 e2 ->
  env_ssm_equiv (s |-> v; e1)
                (s |-> value_match v; e2).
Proof.
  intros. unfold env_ssm_equiv. intros. split.
  - intro. destruct (eqb_string s x) eqn:eq.
    rewrite eqb_string_true_iff in eq. subst.
    rewrite update_eq in H0. inv H0.
    rewrite eqb_string_false_iff in eq.
    rewrite update_neq in H0; auto. rewrite update_neq; auto.
    apply H; auto.
  - intro. destruct (eqb_string s x) eqn:eq.
    rewrite eqb_string_true_iff in eq. subst.
    rewrite update_eq in H0. inv H0.
    rewrite update_eq. auto.
    rewrite eqb_string_false_iff in eq.
    rewrite update_neq in H0; auto. rewrite update_neq; auto.
    apply H; auto. Qed.


Lemma jmp_everything : forall e c s env,
  ((JMP (Datatypes.length (compile e))) :: compile e ++ c, s, env) |>
  (c, s, env).
Proof.
  intros. remember (Datatypes.length (compile e)) as n.
  assert (skipn n (compile e ++ c) = c). pose (skipn_app n (compile e) c).
  rewrite e0. assert (skipn n (compile e) = []). rewrite Heqn.
  apply skipn_all. rewrite H. rewrite Heqn. simpl. rewrite <- Heqn.
  assert (n - n = 0). lia. rewrite H0. apply skipn_O.
  assert ((c,s,env0) = (skipn n (compile e ++ c), s, env0)).
  rewrite H. auto. rewrite H0. apply apply_jmp. Qed.

Lemma jz_everthing : forall e c s env m,
  (JZ (S (Datatypes.length (compile e))) :: (compile e) ++ [[JMP m]] ++ c, 0 :: s, env) |>
  (c, s, env).
Proof.
  intros. remember (Datatypes.length (compile e)) as n.
  assert ((JZ (S n) :: compile e ++ [[JMP m]] ++ c, 0::s, env0) |>
  (skipn (S n) (compile e ++ [[JMP m]] ++ c), s, env0)).
  apply apply_jmp_zero. assert (skipn (S n) (compile e ++ [[JMP m]] ++ c) =
  c). rewrite Heqn. rewrite skipn_app.
  rewrite skipn_all2. rewrite app_nil_l.
  rewrite <- Heqn. assert (S n - n = 1). lia.
  rewrite H0. simpl. auto. lia. rewrite H0 in H.
  apply H. Qed.

Theorem strong_correct_compilation : forall e v w env1 env2,
  bigstep env1 e (v,w) ->
  env_ssm_equiv env1 env2 ->
  forall code stack envs, (compile e ++ code, stack, env2::envs) |*>
    (code, (value_match v)::stack, env2::envs).
Proof.
  induction e; intros; simpl.
  - inv H. eapply rt_step. eapply push_nat.
  - inv H. eapply rt_step. eapply var_lookup.
    apply H0. auto.
  - inv H. repeat (rewrite <- app_assoc).
    eapply rt_trans. eapply IHe1. apply H5.
    auto. eapply rt_trans. eapply IHe2. apply H7. auto.
    rewrite Nat.add_comm. eapply rt_step.
    apply apply_add.
  - inv H. repeat (rewrite <- app_assoc).
    eapply rt_trans. eapply IHe1. apply H4. auto.
    eapply rt_trans. eapply rt_step. simpl. eapply apply_let.
    eapply rt_trans. rewrite <- app_assoc.
    eapply IHe2. apply H8. apply extend_ssm_equiv; auto.
    eapply rt_step. apply apply_ret.
  - inv H. destruct b; apply rt_step; apply push_nat.
  - inv H.
    + repeat rewrite <- app_assoc. eapply rt_trans.
      eapply IHe1. apply H4. apply H0. eapply rt_trans.
      eapply rt_step. simpl. eapply apply_jmp_one.
      eapply rt_trans. repeat rewrite <- app_assoc.
      eapply IHe2. apply H8. apply H0. eapply rt_step.
      eapply jmp_everything.
    + repeat rewrite <- app_assoc. eapply rt_trans.
      eapply IHe1. apply H4. apply H0. eapply rt_trans.
      eapply rt_step. simpl. rewrite <- app_assoc. apply
      jz_everthing. eapply IHe3. apply H8. apply H0.
Qed.


Inductive ssm_cost : ssm -> ssm -> watermark -> Prop :=
  | nat_cost : forall n c s e ssm, ((NAT n)::c, s, e) |> ssm ->
      ssm_cost ((NAT n)::c, s, e) ssm (1,0)
  | add_cost : forall c s e ssm, (ADD::c, s, e) |> ssm ->
      ssm_cost (ADD::c, s, e) ssm (3,0)
  | var_cost : forall x c s e ssm, ((VAR x)::c, s, e) |> ssm ->
      ssm_cost ((VAR x)::c, s, e) ssm (1,0)
  | let_cost : forall x c s e ssm, ((LET x)::c, s, e) |> ssm ->
      ssm_cost ((LET x)::c, s, e) ssm (2,0)
  | ret_cost : forall c s e ssm, (RET :: c,s,e) |> ssm ->
      ssm_cost (RET :: c,s,e) ssm (1,0)
  | jmp_cost : forall c1 c2 s e n, (JMP n :: c1, s, e) |> (c2, s, e) ->
      ssm_cost (JMP n :: c1, s, e) (c2,s,e) (1,0)
  | jz_cost  : forall c1 c2 s ss e n, (JZ n :: c1, s::ss, e) |> (c2, ss, e) ->
      ssm_cost (JZ n :: c1, s::ss, e) (c2, ss, e) (1,0).

Notation "[ A | B | w ]" := (ssm_cost A B w).

Inductive ssm_multi_cost : ssm -> ssm -> watermark -> Prop :=
  | smc_refl : forall ssm, ssm_multi_cost ssm ssm (0,0)
  | smc_step : forall ssm1 ssm2 w, [ssm1 | ssm2 | w] ->
      ssm_multi_cost ssm1 ssm2 w
  | smc_trans : forall ssm1 ssm2 ssm3 w1 w2, ssm_multi_cost ssm1 ssm2 w1 ->
      ssm_multi_cost ssm2 ssm3 w2 -> ssm_multi_cost ssm1 ssm3 (w1 <.> w2).

Notation "[ A | B | w ]*" := (ssm_multi_cost A B w).



End ConditionalCosts.






















