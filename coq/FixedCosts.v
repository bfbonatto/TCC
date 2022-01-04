From TCC Require Import Maps.
From TCC Require Import Common.
From TCC Require Import CpdtTactics.

From Coq Require Import Arith.
Require Import Psatz.
Require Import List.
Import ListNotations.
Import Coq.Relations.Relation_Operators.


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

Lemma cost_correct : forall e v w,
  bigstep empty e (v,w) -> [(compile e, [], [[empty]]) | ([], [[v]], [[empty]]) | w]*.
  Proof. intros. eapply strong_cost_correct with (stack0:=[])
  (code:=[]) (envs:=[]) in H. rewrite app_nil_r in H. auto.
Qed.

Theorem strong_analysis : forall e c1 c2 w,
  analyse c1 e (I,w) -> equiv_c c2 c1 ->
  forall code stack envs, exists v, [(compile e ++ code, stack, c2::envs) | (code, v::stack, c2::envs) | w]*.
Proof.
  intros. eapply sound_typing in H. inv H. eapply strong_cost_correct in H1.
  exists x. apply H1. auto. Qed.

Lemma analysis_correct : forall e w,
  analyse empty e (I,w) -> exists v,
  [(compile e, [], [[empty]]) | ([], [[v]], [[empty]]) | w]*.
Proof.
  intros. eapply strong_analysis with (stack0:=[]) (code:=[]) (envs:=[]) in H.
  inv H. exists x. rewrite app_nil_r in H0. apply H0. unfold equiv_c.
  intros. split; auto.
Qed.



















