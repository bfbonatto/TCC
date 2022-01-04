From TCC Require Import Maps.
From TCC Require Import Common.


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

Definition equiv_c (c1: eval_context) (c2: context) : Prop :=
  forall x, c1 x <> None <-> c2 x <> None.

Lemma extend_equiv_c :
  forall c1 c2 x v, equiv_c c1 c2 -> equiv_c (x |-> v ; c1) (x |-> I ; c2).
Proof.
  intros. unfold equiv_c in *. intros. destruct (eqb_stringP x x0); split; intros; subst.
  - rewrite update_eq. discriminate.
  - rewrite update_eq; discriminate.
  - rewrite update_neq in H0; auto. apply H in H0.
  rewrite update_neq; auto.
  - rewrite update_neq in H0; auto. apply H in H0.
  rewrite update_neq; auto.
Qed.


Theorem tight_bound : forall e v w c1 c2,
  bigstep c1 e (v,w) -> equiv_c c1 c2 -> analyse c2 e (I,w).
  Hint Constructors bigstep.
  Hint Constructors analyse.
  Hint Unfold equiv_c.
Proof.
  induction e; intros; inv H; eauto;
  [|eapply Ll; [eapply IHe1; eauto | eapply IHe2; eauto]; eapply extend_equiv_c; auto]. apply Lv. unfold equiv_c in H0.
  assert (c1 s <> None). rewrite H4; discriminate. apply H0 in H.
  apply not_none_implies_some in H. inv H. destruct x. auto.
Qed.

Lemma equal_bounds : forall w e v,
  bigstep empty e (v,w) -> analyse empty e (I,w).
Proof.
  intros; eapply tight_bound; [apply H |].
  unfold equiv_c; split; intros; destruct H0; auto.
Qed.

Theorem tight_bound_inv : forall e v w1 w2 c1 c2,
  analyse c2 e (I,w1) -> equiv_c c1 c2
  -> bigstep c1 e (v,w2) -> w1 = w2.
Proof.
  induction e; intros; inv H; inv H1; auto;
  [eapply IHe1 with (w1:=w0) in H5; eapply IHe2 with (w1:=w3) in H9;
    eauto; subst; auto |
  destruct a; eapply IHe1 with (w1:=w0) in H4; eauto;
    assert (equiv_c  (s |-> v1; c1)(s |-> I; c2));
    [eapply extend_equiv_c; auto | eapply IHe2 with (w1:=w3) in H10; eauto;
    subst; auto] ].
Qed.

Lemma equal_bounds_inv : forall e v w1 w2,
  analyse empty e (I,w1) -> bigstep empty e (v,w2) -> w1 = w2.
Proof.
  intros; eapply tight_bound_inv; eauto; unfold equiv_c; split; intros;
  destruct H1; auto.
Qed.

Theorem sound_typing : forall e w c,
  analyse c e (I,w) -> forall c', equiv_c c' c -> exists v, bigstep c' e (v,w).
Proof.
  induction e; intros.
  - exists n. inv H. apply En.
  - inv H. unfold equiv_c in H0. pose (H0 s).
    assert (c s <> None). rewrite H4. discriminate.
    apply i in H. apply not_none_implies_some in H.
    inv H. exists x. apply Ev. auto.
  - inv H. eapply IHe1 in H5. inv H5. eapply IHe2 in H6.
    inv H6. exists (x+x0). apply Ea. apply H. apply H1. auto. auto.
  - inv H. destruct a. apply IHe1 with (c' := c') in H4.
    inv H4. apply IHe2 with (c' := (s |-> x; c')) in H8.
    inv H8. exists x0. eapply El. apply H. apply H1.
    eapply extend_equiv_c. auto. auto.
Qed.























