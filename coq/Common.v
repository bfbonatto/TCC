From TCC Require Import CpdtTactics.
Require Import Psatz.
From Coq Require Import Arith.



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

Lemma le_weak : forall q q' p w, p <= q -> weakened (q',q) w -> weakened (q', p) w.
Proof.
  intros. inv H0. unfold weakened. simpl in *.
  split; auto. lia. Qed.

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

Lemma zero_null : forall w, w <.> (0,0) = w.
Proof. intros. destruct w. simpl.
  destr 0 n0; rew; simpl. rewrite Nat.sub_0_r. auto.
  Search (?x <= 0). apply le_n_0_eq in Heqb. rewrite <- Heqb.
  rewrite Nat.add_0_r. rewrite Nat.sub_0_r. auto.
Qed.

Lemma weak_refl : forall w, weakened w w.
Proof.
  intros; unfold weakened; destruct w; simpl; lia.
Qed.

Lemma dot_ge_fst : forall w1 w2, fst (w1 <.> w2) >= fst w1.
Proof.
  intros; destruct w1,w2; simpl. destr n1 n0; rew; simpl.
  auto. lia. Qed.

Lemma dot_ge_snd : forall w1 w2, snd (w1 <.> w2) >= snd w2.
Proof.
  intros. destruct w1,w2; simpl. destr n1 n0; rew; simpl. lia. lia. Qed.

Definition mnx (w1 w2: watermark) : watermark :=
  match w1, w2 with
  | (p,q), (p',q') => (max p p', min q q')
  end.

Lemma mnx_comm : forall w1 w2,
  mnx w1 w2 = mnx w2 w1.
Proof.
  intros. destruct w1,w2; unfold mnx. rewrite Nat.max_comm.
  rewrite Nat.min_comm. auto.
Qed.

Lemma mnx_choice_l : forall w1 w2, (fst (mnx w1 w2) = fst w1) \/
  (fst (mnx w1 w2) = fst w2).
Proof.
  intros. destruct w1,w2. simpl. apply max_choice.
Qed.

Lemma mnx_choice_r : forall w1 w2, (snd (mnx w1 w2) = snd w1) \/
  (snd (mnx w1 w2) = snd w2).
Proof.
  intros. destruct w1,w2. simpl. apply min_choice.
Qed.

Lemma mnx_fst_implies : forall w1 w2 v,
  (fst (mnx w1 w2) = v) -> (v >= fst w1 /\ v >= fst w2).
Proof.
  intros. destruct w1,w2; simpl in *. lia. Qed.

Lemma mnx_snd_implies : forall w1 w2 v,
  (snd (mnx w1 w2) = v) -> (v <= snd w1 /\ v <= snd w2).
Proof.
  intros; destruct w1,w2; simpl in *. lia. Qed.

Lemma mnx_weakened_trans : forall w1 w2 w3,
  weakened w1 w3 -> weakened (mnx w1 w2) w3.
Proof.
  intros. pose (mnx_choice_l w1 w2).
  pose (mnx_choice_r w1 w2).
  unfold weakened in *.
  pose (mnx_fst_implies w1 w2); pose (mnx_snd_implies w1 w2).
  destruct H. destruct o; [pose (a (fst w1) H1) | pose (a (fst w2) H1)]; destruct a1;
  destruct o0; [pose (a0 (snd w1) H4) | pose (a0 (snd w2) H4)
  | pose (a0 (snd w1) H4) | pose (a0 (snd w2) H4)]; split;
  try (rewrite H1); try (rewrite H4); auto; try lia.
Qed.

Lemma mnx_weakened_trans' : forall w1 w2 w3,
  weakened w1 w3 -> weakened (mnx w2 w1) w3.
Proof.
  intros. rewrite mnx_comm. apply mnx_weakened_trans; auto.
Qed.

Definition minx (w1 w2: watermark) : watermark :=
  match w1, w2 with
  | (p,q), (p',q') => (min p p', max q q')
  end.

Lemma mnx_minx_weak : forall w1 w2,
  weakened (mnx w1 w2) (minx w1 w2).
Proof.
  intros.
  destruct w1,w2. unfold mnx,minx.
  unfold weakened. split. simpl.
  lia. simpl. lia. Qed.

Lemma mnx_minx_weak_ultra : forall w1 w2 w3 w4,
  weakened w1 w3 ->
  weakened w2 w4 ->
  weakened (mnx w1 w2) (minx w3 w4).
Proof.
  intros.
  assert (weakened (mnx w1 w2) (minx w1 w2)). apply mnx_minx_weak.
  destruct w1,w2,w3,w4. unfold weakened in *.
  simpl in *. destruct H,H0,H1. split; sl. Qed.



















