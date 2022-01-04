From TCC Require Import Maps.
From TCC Require Import Common.
From TCC Require Import CpdtTactics.

From Coq Require Import Arith.
Require Import Psatz.
Require Import List.
Import ListNotations.
Import Coq.Relations.Relation_Operators.



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
      bigstep c (ECond e1 e2 e3) (v, w1 <.> (1,0) <.> w2 <.> (1,0))
  | Ef : forall (c: eval_context) (w1 w3: watermark) (e1 e2 e3: usl) (v: val),
      bigstep c e1 (Vb false, w1) -> bigstep c e3 (v,w3) ->
      bigstep c (ECond e1 e2 e3) (v, w1 <.> (1,0) <.> w3).


Fixpoint max_cost (t: usl) : watermark :=
  match t with
  | ENum _ => (1,0)
  | EVar _ => (1,0)
  | EAdd e1 e2 => (max_cost e1) <.> (max_cost e2) <.> (3,0)
  | ELet _ e1 e2 => (max_cost e1) <.> (2,0) <.> (max_cost e2) <.> (1,0)
  | EBool _ => (1,0)
  | ECond e1 e2 e3 => (max_cost e1) <.> (1,0) <.> (mnx ((max_cost e2) <.> (1,0)) (max_cost e3))
  end.


Fixpoint min_cost (t: usl) : watermark :=
  match t with
  | ENum _ => (1,0)
  | EVar _ => (1,0)
  | EAdd e1 e2 => (min_cost e1) <.> (min_cost e2) <.> (3,0)
  | ELet _ e1 e2 => (min_cost e1) <.> (2,0) <.> (min_cost e2) <.> (1,0)
  | EBool _ => (1,0)
  | ECond e1 e2 e3 => (min_cost e1) <.> (1,0) <.> (minx ((min_cost e2) <.> (1,0)) (min_cost e3))
  end.



Lemma max_min_weak : forall t w1 w2,
  max_cost t = w1 -> min_cost t = w2 -> weakened w1 w2.
Proof.
  induction t; intros.
  - inv H. apply weak_refl.
  - inv H. apply weak_refl.
  - inv H. simpl. apply weak_dot.
    apply weak_dot'. apply IHt1; auto. apply IHt2; auto.
  - inv H. simpl. apply weak_dot. apply weak_dot'.
    apply weak_dot. apply IHt1; auto. apply IHt2; auto.
  - inv H. apply weak_refl.
  - inv H. simpl.
    apply weak_dot'. apply weak_dot. apply IHt1; auto.
    eapply mnx_minx_weak_ultra. apply weak_dot. apply IHt2; auto.
    apply IHt3; auto.
Qed.




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
  | Lc : forall (e1 e2 e3: usl) (w1 w2 w3: watermark) (c: context) (t: type),
      analyse c e1 (B,w1) -> analyse c e2 (t,w2) -> analyse c e3 (t,w3) ->
      analyse c (ECond e1 e2 e3) (t, w1 <.> (1,0) <.> mnx (w2 <.> (1,0)) w3).

Theorem analyse_reflects_cost :
  forall c e t w1 w2,
    analyse c e (t,w1) -> max_cost e = w2 -> w1 = w2.
Proof.
  intros. generalize dependent c. generalize dependent t.
  generalize dependent w1. generalize dependent w2. induction e; intros.
  - inv H. auto.
  - inv H. auto.
  - inv H. simpl. replace (max_cost e1) with w0.
    replace (max_cost e2) with w3. auto.
    eapply IHe2; auto. apply H7. eapply IHe1. auto. apply H5.
  - inv H. simpl. replace (max_cost e1) with w0.
    replace (max_cost e2) with w3. auto.
    eapply IHe2. auto. apply H8. eapply IHe1. auto. apply H4.
  - inv H. auto.
  - inv H. simpl. replace (max_cost e1) with w0. replace (max_cost e2) with
    w3. replace (max_cost e3) with w4. auto.
    eapply IHe3; eauto. eapply IHe2; eauto. eapply IHe1; eauto.
Qed.

Lemma analyse_min_weak : forall t e w1 w2 T,
  analyse e t (T,w1) -> min_cost t = w2 -> weakened w1 w2.
Proof.
  induction t; intros.
  - inv H. simpl. apply weak_refl.
  - inv H; apply weak_refl; auto.
  - inv H. simpl. apply weak_dot. apply weak_dot'.
    eapply IHt1. apply H5. auto. eapply IHt2. apply H7. auto.
  - inv H. simpl. apply weak_dot. apply weak_dot'. apply weak_dot.
    eapply IHt1. apply H4. auto. eapply IHt2. apply H8. auto.
  - inv H. apply weak_refl; auto.
  - inv H. simpl. replace (min_cost t1) with w0.
    replace (min_cost t2) with w3. replace (min_cost t3) with w4.
    eapply weak_dot'. apply weak_refl; auto.
    



Definition type_eq (t1 t2: type) : bool :=
  match t1,t2 with
  | I,I => true
  | B,B => true
  | _,_ => false
  end.

Fixpoint analyse_f (c: context) (e: usl) : option (type*watermark) :=
  match e with
  | ENum n => Some (I,(1,0))
  | EVar x => match (c x) with
              | None => None
              | Some t => Some (t, (1,0))
              end
  | EAdd e1 e2 => match (analyse_f c e1), (analyse_f c e2) with
                  | None, _ => None
                  | _, None => None
                  | Some (I,w1), Some (I,w2) => Some (I,w1 <.> w2 <.> (3,0))
                  | _,_ => None
                  end
  | ELet x e1 e2 => match (analyse_f c e1) with
                    | None => None
                    | Some (t1, w1) => match (analyse_f (x|->t1; c) e2) with
                                       | None => None
                                       | Some (t2,w2) => Some (t2, w1 <.> (2,0) <.> w2 <.> (1,0))
                                       end
                    end
  | EBool b => Some (B, (1,0))
  | ECond e1 e2 e3 => match (analyse_f c e1), (analyse_f c e2), (analyse_f c e3) with
                      | None, _, _ => None
                      | _, None, _ => None
                      | _, _, None => None
                      | Some (B,w1), Some (t1,w2), Some (t2, w3) => if type_eq t1 t2 then Some (t1, w1 <.> (1,0) <.> mnx (w2 <.> (1,0)) w3) else None
                      | _, _, _ => None
                      end
  end.


Definition typeOf (v: val) : type :=
  match v with
  | Vn n => I
  | Vb b => B
  end.

Definition fmap {T1 T2: Type} (f: T1 -> T2) (x: option T1) : option T2 :=
  match x with
  | None => None
  | Some x' => Some (f x')
  end.

Lemma fmap_some_implies : forall (T1 T2: Type) (v1: option T1) (v2: T2) f, fmap f v1 = Some v2 ->
  exists v, v1 = Some v.
Proof.
  intros. destruct v1. exists t. auto.
  inv H. Qed.

Definition equiv_c (c1: eval_context) (c2: context) : Prop :=
  forall x, fmap typeOf (c1 x) = c2 x.

Lemma extend_equiv_c :
  forall c1 c2 x v, equiv_c c1 c2 -> equiv_c (x |-> v ; c1) (x |-> (typeOf v) ; c2).
Proof.
  intros. unfold equiv_c in *. intros. destruct (eqb_stringP x x0); subst.
  - repeat (rewrite update_eq); auto.
  - repeat (rewrite update_neq); auto.
Qed.



Theorem preservation : forall e v t w1 w2 c1 c2, equiv_c c2 c1 ->
  analyse c1 e (t,w1) -> bigstep c2 e (v,w2) -> t = typeOf v.
Proof.
  induction e; intros; try (solve [inv H0; inv H1; auto]).
  - inv H0. inv H1. unfold equiv_c in H. pose (H s).
    rewrite H5 in e; rewrite H4 in e. inv e; auto.
  - inv H0; inv H1. assert (a = typeOf v1). eapply IHe1; eauto.
    subst. pose (extend_equiv_c c2 c1 s v1 H). eapply IHe2.
    apply e. apply H9. apply H10.
  - inv H0; inv H1; [eapply IHe2 | eapply IHe3]; eauto.
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
  - inv H1; inv H2.
    + repeat (rewrite <- dot_left_assoc).
      eapply weak_dot'. eapply IHe1; eauto.
      eapply weak_dot'. auto.
      assert (weakened (w3 <.> (1,0)) (w5 <.> (1,0))).
      apply weak_dot. eapply IHe2; eauto.
      eapply mnx_weakened_trans. apply H.
    + repeat (rewrite <- dot_left_assoc).
      eapply weak_dot'; eauto. eapply weak_dot';
      eauto. eapply mnx_weakened_trans'; eauto.
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
  forall x, e2 x = fmap value_match (e1 x).


Lemma extend_ssm_equiv : forall s v e1 e2,
  env_ssm_equiv e1 e2 ->
  env_ssm_equiv (s |-> v; e1)
                (s |-> value_match v; e2).
Proof.
  intros. unfold env_ssm_equiv in *. intros. destruct (eqb_stringP x s); subst.
  - repeat (rewrite update_eq); auto.
  - repeat (rewrite update_neq); auto.
Qed.


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
  induction e; intros.
  - simpl. inv H. apply rt_step. apply push_nat.
  - inv H. simpl. apply rt_step. apply var_lookup.
    unfold env_ssm_equiv in H0. pose (H0 s).
    rewrite H4 in e. simpl in e. apply e.
  - inv H. simpl; repeat (rewrite <- app_assoc);
    eapply rt_trans. eapply IHe1; eauto.
    eapply rt_trans. eapply IHe2; eauto.
    eapply rt_step. simpl. rewrite Nat.add_comm. apply apply_add.
  - inv H; simpl; repeat (rewrite <- app_assoc). eapply rt_trans.
    eapply IHe1; eauto. simpl. eapply rt_trans. eapply rt_step.
    eapply apply_let. repeat (rewrite <- app_assoc).
    eapply rt_trans. eapply IHe2; eauto. eapply extend_ssm_equiv; auto.
    simpl. eapply rt_step. apply apply_ret.
  - simpl; destruct b; inv H; simpl; eapply rt_step; apply push_nat.
  - simpl. inv H; repeat (rewrite <- app_assoc).
    + eapply rt_trans. eapply IHe1; eauto. simpl.
      eapply rt_trans. eapply rt_step. apply apply_jmp_one.
      eapply rt_trans. repeat (rewrite <- app_assoc).
      eapply IHe2; eauto. simpl. eapply rt_step. eapply jmp_everything.
    + eapply rt_trans. eapply IHe1; eauto. simpl.
      eapply rt_trans. eapply rt_step. simpl. repeat (rewrite <- app_assoc).
      eapply jz_everthing. eapply IHe3; eauto.
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
  | smc_step : forall ssm1 ssm2 w, [ssm1 | ssm2 | w] ->
      ssm_multi_cost ssm1 ssm2 w
  | smc_trans : forall ssm1 ssm2 ssm3 w1 w2, (ssm_multi_cost ssm1 ssm2 w1) ->
    (ssm_multi_cost ssm2 ssm3 w2) -> (ssm_multi_cost ssm1 ssm3 (w1 <.> w2)).

Notation "[ A | B | w ]*" := (ssm_multi_cost A B w).

Lemma cons_diff : forall {T: Type} (x: T) (xs: list T),
  x :: xs <> xs.
Proof.
  induction xs. discriminate.
  intro. inv H. destruct IHxs. auto.
Qed.

Theorem strong_cost_correct : forall e v w env1 env2,
  bigstep env1 e (v,w) ->
  env_ssm_equiv env1 env2 ->
  forall code stack envs, [(compile e ++ code, stack, env2::envs) |
    (code, (value_match v)::stack, env2::envs) | w]*.
Proof.
  induction e; intros; inv H; simpl.
  - eapply smc_step. apply nat_cost. apply push_nat.
  - eapply smc_step. eapply var_cost. eapply var_lookup.
    unfold env_ssm_equiv in H0. pose (H0 s).
    rewrite e. rewrite H4. auto.
  - repeat (rewrite <- app_assoc). eapply smc_trans.
    eapply smc_trans. eapply IHe1; eauto.
    eapply IHe2; eauto. eapply smc_step. simpl.
    apply add_cost. rewrite Nat.add_comm.
    apply apply_add.
  - repeat (rewrite <- app_assoc). eapply smc_trans.
    eapply smc_trans. eapply smc_trans. eapply IHe1; eauto.
    simpl. eapply smc_step. eapply let_cost.
    eapply apply_let. repeat (rewrite <- app_assoc).
    eapply IHe2; eauto. eapply extend_ssm_equiv; eauto.
    simpl. eapply smc_step. eapply ret_cost.
    eapply apply_ret.
  - destruct b; simpl; eapply smc_step; eapply nat_cost;
    eapply push_nat.
  - repeat (rewrite <- app_assoc). eapply smc_trans.
    eapply smc_trans. eapply smc_trans. eapply IHe1; eauto.
    eapply smc_step. simpl. eapply jz_cost. eapply apply_jmp_one.
    rewrite <- app_assoc. eapply IHe2; eauto.
    simpl. eapply smc_step. eapply jmp_cost. eapply jmp_everything.
  - repeat (rewrite <- app_assoc). eapply smc_trans.
    eapply smc_trans. eapply IHe1; eauto.
    simpl. eapply smc_step. eapply jz_cost. simpl.
    repeat (rewrite <- app_assoc). eapply jz_everthing.
    eapply IHe3; eauto.
Qed.















