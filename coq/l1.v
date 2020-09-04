From Coq Require Import Arith.
From Coq Require Import Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical_Prop.
Require Import Classical_Prop Classical_Pred_Type.
Require Import Logic.Classical_Prop.
Require Import Classical.
From Coq Require Import omega.Omega.
Require Import Nat.
Require Import List.
Require Import FunInd.
Require Import Recdef.
Require Export Coq.Program.Wf.




Ltac inv H := inversion H; clear H; subst.

Lemma exists_not_forall : forall (X : Type) (P : X -> Prop),
  (exists x, ~ P x) -> ~ (forall x, P x).
Proof.
  intros. intro. inversion H. auto.
Qed.

Lemma not_forall_exists : forall (X : Type) (P : X -> Prop),
  ~ (forall x, P x) -> (exists x, ~ P x).
Proof.
  intros. apply Peirce. intros. exfalso.
  unfold not in H. apply H. intros.
  apply Peirce. intros. exfalso. apply H0.
  exists x. auto.
Qed.

Lemma not_exists_forall : forall (X : Type) (P : X -> Prop),
  ~ (exists x, P x) -> (forall x, ~ P x).
Proof.
  intros. destruct (classic (P x)).
  - assert (exists x, P x). exists x. auto.
  contradiction.
  - auto.
Qed.

Lemma not_false_true : forall (P : Prop),
  (~ (P -> False)) -> P.
Proof.
  intros. unfold not in H. destruct (classic P).
  auto. unfold not in H0. apply H in H0. contradiction.
Qed.



(* Maps *)

Definition total_map (A : Type) := nat -> A.

Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

Definition t_update {A : Type} (m : total_map A)
                    (x : nat) (v : A) :=
  fun x' => if beq_nat x x' then v else m x'.

Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).

Notation "x '!->' v ';' m" := (t_update m x v)
                              (at level 100, v at next level, right associativity).


Lemma t_apply_empty : forall (A : Type) (x : nat) (v : A),
    (_ !-> v) x = v.
Proof.
  intros. auto. Qed.


Lemma t_update_eq : forall (A : Type) (m : total_map A) x v,
    (x !-> v ; m) x = v.
Proof.
  intros. unfold t_update. rewrite <- beq_nat_refl. auto.
Qed.

Lemma eqb_true_iff : forall (x y : nat), x = y -> (x =? y) = true.
Proof.
  intros. rewrite H. rewrite Nat.eqb_refl. auto.
Qed.

Lemma eqb_false_iff : forall (x y : nat), x <> y -> (x =? y) = false.
Proof.
  intros. pose (Nat.eqb_neq x y). destruct i. apply H1 in H. auto.
Qed.


Theorem t_update_neq : forall (A : Type) (m : total_map A) x1 x2 v,
    x1 <> x2 ->
    (x1 !-> v ; m) x2 = m x2.
Proof.
  intros. unfold t_update. rewrite eqb_false_iff. auto. auto.
Qed.

Lemma t_update_shadow : forall (A : Type) (m : total_map A) x v1 v2,
    (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
Proof.
  intros. apply functional_extensionality_dep.
  intros. unfold t_update. pose (classic (x = x0)).
  destruct o.
  - subst. rewrite <- beq_nat_refl. auto.
  - apply eqb_false_iff in H. rewrite H. auto.
Qed.



Theorem t_update_same : forall (A : Type) (m : total_map A) x,
    (x !-> m x ; m) = m.
Proof.
  intros. apply functional_extensionality_dep.
  intros. pose (classic (x = x0)). destruct o; unfold t_update.
  - rewrite eqb_true_iff; auto.
  - rewrite eqb_false_iff; auto.
Qed.



Theorem t_update_permute : forall (A : Type) (m : total_map A)
                                  v1 v2 x1 x2,
    x2 <> x1 ->
    (x1 !-> v1 ; x2 !-> v2 ; m)
    =
    (x2 !-> v2 ; x1 !-> v1 ; m).
Proof.
  intros. apply functional_extensionality_dep.
  intros. destruct (classic (x = x1)); destruct (classic (x = x2)); subst.
  - destruct H. auto.
  - repeat (rewrite t_update_eq). rewrite t_update_neq. rewrite t_update_eq; auto. auto.
  - rewrite t_update_neq; auto. rewrite t_update_eq. rewrite t_update_eq. auto.
  - repeat (rewrite t_update_neq; auto).
Qed.


Definition partial_map (A : Type) := total_map (option A).

Definition empty {A : Type} : partial_map A :=
  t_empty None.

Definition update {A : Type} (m : partial_map A)
           (x : nat) (v : A) :=
  (x !-> Some v ; m).

(** We introduce a similar notation for partial maps: *)
Notation "x '|->' v ';' m" := (update m x v)
  (at level 100, v at next level, right associativity).

(** We can also hide the last case when it is empty. *)
Notation "x '|->' v" := (update empty x v)
  (at level 100).

Lemma update_eq : forall (A : Type) (m : partial_map A) x v,
    (x |-> v ; m) x = Some v.
Proof.
  intros. unfold update. rewrite t_update_eq.
  reflexivity.
Qed.

Theorem update_neq : forall (A : Type) (m : partial_map A) x1 x2 v,
    x2 <> x1 ->
    (x2 |-> v ; m) x1 = m x1.
Proof.
  intros A m x1 x2 v H.
  unfold update. rewrite t_update_neq. reflexivity.
  apply H. Qed.

Lemma update_shadow : forall (A : Type) (m : partial_map A) x v1 v2,
    (x |-> v2 ; x |-> v1 ; m) = (x |-> v2 ; m).
Proof.
  intros A m x v1 v2. unfold update. rewrite t_update_shadow.
  reflexivity.
Qed.

Theorem update_same : forall (A : Type) (m : partial_map A) x v,
    m x = Some v ->
    (x |-> v ; m) = m.
Proof.
  intros A m x v H. unfold update. rewrite <- H.
  apply t_update_same.
Qed.

Theorem update_permute : forall (A : Type) (m : partial_map A)
                                x1 x2 v1 v2,
    x2 <> x1 ->
    (x1 |-> v1 ; x2 |-> v2 ; m) = (x2 |-> v2 ; x1 |-> v1 ; m).
Proof.
  intros A m x1 x2 v1 v2. unfold update.
  apply t_update_permute.
Qed.


Definition eq_context (A : Type) (c1 c2 : partial_map A) :=
  forall (n : nat), (c1 n) = (c2 n).

Definition contained (A : Type) (c1 c2 : partial_map A) :=
  forall (n : nat) (a : A), c1 n = Some a -> c2 n = Some a.

Lemma eq_context_eq : forall (A : Type) (c1 c2 : partial_map A),
  eq_context A c1 c2 -> c1 = c2.
Proof.
  intros. apply functional_extensionality_dep. unfold eq_context in H.
   auto.
Qed.


(************************* L1 ******************************)


(* Abstract Syntax *)

Inductive op :=
  | op_arith : (nat -> nat -> nat) -> op
  | op_comp  : (nat -> nat -> bool) -> op.

Inductive type : Type :=
  | type_nat : type
  | type_bool : type
  | type_fun : type -> type -> type.


Inductive term :=
  | t_num  : nat -> term
  | t_bool : bool -> term
  | t_op   : term -> op -> term -> term
  | t_if   : term -> term -> term -> term
  | t_var  : nat -> term
  | t_app  : term -> term -> term
  | t_fun  : nat -> type -> term -> term
  | t_let  : nat -> type -> term -> term -> term
  | t_rec  : nat -> type -> type -> nat -> term -> term -> term.

Inductive value : term -> Prop :=
  | val_nat : forall n : nat , value (t_num n)
  | val_bool : forall b : bool, value (t_bool b)
  | val_fun : forall (x: nat) (t: type), forall e: term, value (t_fun x t e).



(* Substitution *)
Reserved Notation "'[' x ':=' s ']' t" (at level 20).
Fixpoint f_subst (x : nat) (s : term) (t : term) : term :=
  match t with
  | (t_num n) => t_num n
  | (t_bool b) => t_bool b
  | (t_op t1 op t2) => t_op ([x:=s]t1) op ([x:=s]t2)
  | (t_if t1 t2 t3) => t_if ([x:=s]t1) ([x:=s]t2) ([x:=s]t3)
  | (t_var y) => if beq_nat x y then s else t
  | (t_app t1 t2) => t_app ([x:=s]t1) ([x:=s]t2)
  | (t_fun y T f) => if beq_nat x y then t else t_fun y T ([x:=s]f)
  | (t_let y T t1 t2) => if beq_nat x y then t_let y T ([x:=s]t1) t2 else t_let y T ([x:=s]t1) ([x:=s]t2)
  | (t_rec f T1 T2 y e1 e2) => t_rec f T1 T2 y (if beq_nat x f then e1 else
    (if beq_nat x y then e1 else ([x:=s] e1)) ) (if beq_nat x y then e2 else ([x:=s] e2))
end

where "'[' x ':=' s ']' t" := (f_subst x s t).




(* Operational Semantics *)

Reserved Notation "A ---> B" (at level 90, no associativity).
Inductive step : term -> term -> Prop :=
  | e_op1      : forall (o : op), forall (e1 e2 e1' : term),
      e1 ---> e1' -> (t_op e1 o e2) ---> (t_op e1' o e2)

  | e_op2      : forall (o : op), forall (e1 e2 e2' : term),
      e2 ---> e2' -> value e1 -> (t_op e1 o e2) ---> (t_op e1 o e2')

  | e_op_arith : forall (n1 n2 : nat) (f : (nat -> nat -> nat)),
      (t_op (t_num n1) (op_arith f) (t_num n2)) ---> t_num (f n1 n2)

  | e_op_comp  : forall (n1 n2 : nat) (f : (nat -> nat -> bool)),
      (t_op (t_num n1) (op_comp f) (t_num n2)) ---> t_bool (f n1 n2)

  | e_if_t     : forall (e2 e3 : term), (t_if (t_bool true) e2 e3) ---> e2
  | e_if_f     : forall (e2 e3 : term), (t_if (t_bool false) e2 e3) ---> e3
  | e_if       : forall (e1 e1' e2 e3 : term),
      e1 ---> e1' -> (t_if e1 e2 e3) ---> (t_if e1' e2 e3)

  | e_beta     : forall (x : nat) (T : type) (e v : term), value v -> t_app (t_fun x T e) v ---> [x:=v]e
  | e_app2     : forall (e1 e2 e2' : term),
      e2 ---> e2' -> value e1 -> (t_app e1 e2) ---> (t_app e1 e2')

  | e_app1     : forall (e1 e2 e1' : term),
      e1 ---> e1' -> (t_app e1 e2) ---> (t_app e1' e2)

  | e_let1     : forall (x : nat), forall (T : type), forall (v e : term),
      value v -> t_let x T v e ---> [x:=v]e

  | e_let2     : forall (x : nat), forall (T : type), forall (e1 e1' e2 : term),
      e1 ---> e1' -> t_let x T e1 e2 ---> t_let x T e1' e2

  | e_rec      : forall (f y : nat) (T1 T2 : type) (e1 e2 : term),
      t_rec f T1 T2 y e1 e2 ---> [f:=(t_fun y T1 (t_rec f T1 T2 y e1 e1))]e2

where "A ---> B" := (step A B).




(* Type system *)


Definition context := partial_map type.


Reserved Notation "G |: A ===> B" (at level 90, no associativity).
Inductive check : context -> term -> type -> Prop :=
  | tp_num   : forall (n : nat) (g : context), g |: t_num n ===> type_nat

  | tp_bool  : forall (b : bool) (g : context), g |: t_bool b ===> type_bool

  | tp_arith : forall (f : nat -> nat -> nat) (g : context) (e1 e2 : term),
      (g |: e1 ===> type_nat) -> (g |: e2 ===> type_nat) -> 
       g |: (t_op e1 (op_arith f) e2) ===> type_nat

  | tp_comp  : forall (f : nat -> nat -> bool) (g : context) (e1 e2 : term),
      (g |: e1 ===> type_nat) -> (g |: e2 ===> type_nat) ->
       g |: (t_op e1 (op_comp f) e2) ===> type_bool

  | tp_if    : forall (t1 t2 t3 : term) (g : context) (T : type),
      (g |: t1 ===> type_bool) -> (g |: t2 ===> T) -> (g |: t3 ===> T) -> g |: t_if t1 t2 t3 ===> T
  | tp_var   : forall (n : nat) (g : context) (T : type), g n = Some T -> g |: t_var n ===> T
  | tp_fun   : forall (x : nat) (g : context) (T T' : type) (e : term),
      (x |-> T ; g) |: e ===> T' -> g |: (t_fun x T e) ===> (type_fun T T')
  | tp_app   : forall (e1 e2 : term) (g : context) (T T' : type),
      g |: e1 ===> (type_fun T T') -> g |: e2 ===> T -> g |: (t_app e1 e2) ===> T'
  | tp_let   : forall (x : nat) (e1 e2 : term) (T T' : type) (g : context),
      g |: e1 ===> T -> (x |-> T ; g) |: e2 ===> T' -> g |: (t_let x T e1 e2) ===> T'
  | tp_rec   : forall (f x : nat) (T1 T2 T : type) (e1 e2 : term) (G : context),
      f <> x ->
      (x |-> T1 ; (f |-> type_fun T1 T2; G)) |: e1 ===> T2 ->
      (f |-> type_fun T1 T2 ; G) |: e2 ===> T ->
      G |: t_rec f T1 T2 x e1 e2 ===> T

where "G |: A ===> B" := (check G A B).





(* Properties *)




Lemma value_nat_is_num : forall (g : context) (t : term),
  g |: t ===> type_nat -> value t -> exists n: nat, t = t_num n.
Proof.
  intros. inversion H0; subst. exists n. auto.
  inversion H. inversion H.
Qed.

Lemma value_bool_is_bool : forall (g : context) (t : term),
  g |: t ===> type_bool -> value t -> (t = t_bool true) \/ (t = t_bool false).
Proof.
  intros. inversion H0; subst.
  - inversion H.
  - destruct b. auto. auto.
  - inversion H.
Qed.

Lemma value_fun_is_fun : forall (g : context) (t : term) (T T' : type),
  g |: t ===> (type_fun T T') -> value t ->
  exists (x : nat) (e : term), t = (t_fun x T e).
Proof.
  intros. inversion H0; subst.
  - inversion H.
  - inversion H.
  - exists x. exists e. assert (T = t0).
    + inversion H. subst. auto.
    +  subst. auto.
Qed.


Theorem progress: forall (t : term) (T : type),
  empty |: t ===> T -> value t \/ exists t':term, t ---> t'.
Proof.
Hint Constructors step.
Hint Constructors check.
Hint Constructors term.
Hint Constructors value.
Hint Constructors type.
Hint Constructors op.



  intros. remember (@empty type) as gamma. induction H; auto;
  right; auto; try (pose (IHcheck1 Heqgamma)); try (pose (IHcheck2 Heqgamma));
  try (pose (IHcheck3 Heqgamma)).
  - destruct o; destruct o0; clear IHcheck1; clear IHcheck2.
    + subst. eapply value_nat_is_num in H1. eapply value_nat_is_num in H2.
      inv H1. inv H2. exists (t_num (f x x0)). auto. apply H0. apply H.
    + subst. inv H2. exists (t_op e1 (op_arith f) x). auto.
    + subst. inv H1. exists (t_op x (op_arith f) e2). auto.
    + inv H1. exists (t_op x (op_arith f) e2). auto.
  - subst. destruct o; destruct o0; clear IHcheck1; clear IHcheck2.
    + eapply value_nat_is_num in H; eapply value_nat_is_num in H0; auto.
      inv H0. inv H. exists (t_bool (f x0 x)). auto.
    + inv H2. exists (t_op e1 (op_comp f) x). auto.
    + inv H1. exists (t_op x (op_comp f) e2). auto.
    + inv H1. exists (t_op x (op_comp f) e2). auto.
  - destruct o. eapply value_bool_is_bool in H2.
    destruct H2. exists t2. rewrite H2. auto.
    exists t3. rewrite H2. auto. apply H.
    inv H2. exists (t_if x t2 t3). auto.
  - subst. inv H.
  - destruct o; destruct o0; clear IHcheck1; clear IHcheck2.
    apply value_fun_is_fun with (g := empty) (T := T) (T' := T') in H1.
    inv H1. inv H3. exists ([x:=e2]x0). auto.
    subst. auto. inv H2. exists (t_app e1 x). auto.
    inv H1. exists (t_app x e2). auto.
    inv H1. exists (t_app x e2). auto.
  - destruct o; clear IHcheck1; clear IHcheck2.
    + exists ([x:=e1]e2). auto.
    + inv H1. exists (t_let x T x0 e2). auto.
  - subst. clear IHcheck1; clear IHcheck2.
    exists ([f:=(t_fun x T1 (t_rec f T1 T2 x e1 e1))]e2).
    auto.
Qed.


Inductive appears_free_in : nat -> term -> Prop :=
  | afi_var  : forall x, appears_free_in x (t_var x)
  | afi_op1  : forall x t1 t2 o,
      appears_free_in x t1 -> appears_free_in x (t_op t1 o t2)
  | afi_op2  : forall x t1 t2 o,
      appears_free_in x t2 -> appears_free_in x (t_op t1 o t2)
  | afi_if1  : forall x t1 t2 t3,
      appears_free_in x t1 -> appears_free_in x (t_if t1 t2 t3)
  | afi_if2  : forall x t1 t2 t3,
      appears_free_in x t2 -> appears_free_in x (t_if t1 t2 t3)
  | afi_if3  : forall x t1 t2 t3,
      appears_free_in x t3 -> appears_free_in x (t_if t1 t2 t3)
  | afi_app1 : forall x t1 t2,
      appears_free_in x t1 -> appears_free_in x (t_app t1 t2)
  | afi_app2 : forall x t1 t2,
      appears_free_in x t2 -> appears_free_in x (t_app t1 t2)
  | afi_fun  : forall f x T t,
      f <> x -> appears_free_in x t ->
      appears_free_in x (t_fun f T t)
  | afi_let1 : forall x e T t1 t2,
      appears_free_in x t1 ->
      appears_free_in x (t_let e T t1 t2)
  | afi_let2 : forall x e T t1 t2,
      e <> x ->
      appears_free_in x t2 ->
      appears_free_in x (t_let e T t1 t2)
  | afi_rec1 : forall x f T1 T2 y e1 e2,
      y <> x ->
      f <> x ->
      appears_free_in x e1 ->
      appears_free_in x (t_rec f T1 T2 y e1 e2)
  | afi_rec2 : forall x f T1 T2 y e1 e2,
      f <> x ->
      appears_free_in x e2 ->
      appears_free_in x (t_rec f T1 T2 y e1 e2).

Definition closed (t: term) :=
  forall x, ~ (appears_free_in x t).


Lemma free_in_context : forall x t T Gamma,
  appears_free_in x t ->
  Gamma |: t ===> T ->
  exists T', Gamma x = Some T'.
Proof.
  intros. generalize dependent Gamma.
  generalize dependent T.
  induction H; intros; try solve [inversion H0; eauto].
  - inversion H1; subst. apply IHappears_free_in in H7.
    rewrite update_neq in H7; auto.
  - inversion H1; subst. apply IHappears_free_in in H9.
    rewrite update_neq in H9; auto.
  - inversion H2; subst. apply IHappears_free_in in H12; auto.
    rewrite update_neq in H12; auto. rewrite update_neq in H12; auto.
  - inversion H1; subst. apply IHappears_free_in in H12.
    rewrite update_neq in H12; auto.
Qed.

Corollary typable_empty_closed : forall t T,
    empty |: t ===> T  ->
    closed t.
Proof.
  intros. unfold closed. intros. intro. generalize dependent T.
  induction H0; intros; try inversion H; subst; auto; try (solve [inversion H2]);
    eapply IHappears_free_in; eauto.
  - inversion H1; subst; auto. pose (free_in_context x t T' (f |-> T) H0 H7).
    inversion e; subst; auto. unfold update in H2. unfold t_update in H2.
    Search eqb. apply eqb_false_iff in H. rewrite H in H2.
    inversion H2.
  - inversion H1; subst; auto. pose (free_in_context x t2 T0 (e|->T) H0
    H9). inversion e0. unfold update in H2. unfold t_update in H2.
    apply eqb_false_iff in H. rewrite H in H2. inversion H2.
  - inversion H2; subst; auto.
    apply free_in_context with (T := T2) (Gamma := (y |-> T1; f |-> type_fun T1 T2)) in H1.
    inv H1. rewrite update_neq in H3. rewrite update_neq in H3. inv H3.
    auto. auto. auto.
  - inv H1. apply free_in_context with (T := T) (Gamma := (f |-> type_fun T1 T2)) in H0.
    inv H0. rewrite update_neq in H1. inv H1. auto. auto.
  Unshelve. apply T. apply T. apply T. apply T. Qed.

  
  
  
  

Lemma context_invariance : forall Gamma Gamma' t T,
     Gamma |: t ===> T  ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x) ->
     Gamma' |: t ===> T.
Proof.
  intros. generalize dependent Gamma'.  induction H; intros; auto.
  - apply tp_arith; [apply IHcheck1 | apply IHcheck2]; intros; apply H1;
    [apply afi_op1 | apply afi_op2]; auto.
  - apply tp_comp; [apply IHcheck1 | apply IHcheck2]; intros; apply H1;
    [apply afi_op1 | apply afi_op2]; auto.
  - apply tp_if; [apply IHcheck1 | apply IHcheck2 | apply IHcheck3]; intros;
    apply H2; [apply afi_if1 | apply afi_if2 | apply afi_if3];
    auto.
  - apply tp_var. rewrite <- H0. auto.
    apply afi_var.
  - apply tp_fun. apply IHcheck. intros.
    unfold update. unfold t_update. destruct eqb eqn:eqxx0.
    auto. apply H0. apply afi_fun. rewrite Nat.eqb_neq in eqxx0.
    auto. auto.
  - apply tp_app with (T := T) (T' := T').
    apply IHcheck1. intros. apply H1. apply afi_app1.
    auto. apply IHcheck2. intros. apply H1. apply afi_app2.
    auto.
  - apply tp_let. apply IHcheck1. intros. apply H1.
    apply afi_let1. auto. apply IHcheck2.
    intros. unfold update. unfold t_update.
    destruct eqb eqn:eqxx0. auto. apply H1. apply afi_let2.
    rewrite Nat.eqb_neq in eqxx0. auto. auto.
  - apply tp_rec. auto. apply IHcheck1. intros.
    unfold update. unfold t_update. destruct (x =? x0) eqn:eqxx0;
    destruct (f =? x0) eqn:eqfx0.
    auto. auto. auto. apply H2. apply afi_rec1. rewrite <- Nat.eqb_neq.
    auto. rewrite <- Nat.eqb_neq. auto. auto.
    apply IHcheck2. intros. unfold update. unfold t_update.
    destruct (f =? x0) eqn:eqfx0. auto. apply H2.
    apply afi_rec2. rewrite <- Nat.eqb_neq. auto. auto.
Qed.



Lemma substitution_lemma : forall Gamma x U t v T,
  (x |-> U ; Gamma) |: t ===> T ->
  empty |: v ===> U   ->
  Gamma |: [x:=v]t ===> T.
Proof.
  intros. generalize dependent T. generalize dependent Gamma.
  induction t; intros; auto; simpl.
  - eapply context_invariance. apply H. intros.
    inv H1.
  - eapply context_invariance. apply H. intros.
    inv H1.
  - inv H; [eapply tp_arith; apply IHt1 in H6; auto | eapply tp_comp; apply IHt2 in H7; auto].
  - inv H. apply tp_if; [apply IHt1 in H5 |
    apply IHt2 in H7 | apply IHt3 in H8]; auto.
  - destruct (x =? n) eqn:Heqx. rewrite Nat.eqb_eq in Heqx.
    subst. inv H. rewrite update_eq in H3. inv H3.
    eapply context_invariance in H0. apply H0.
    intros. apply typable_empty_closed in H0.
    unfold closed in H0. apply H0 in H. inv H.
    eapply context_invariance in H. apply H.
    intros. rewrite Nat.eqb_neq in Heqx.
    inv H1. rewrite update_neq; auto.
  - inv H. eapply tp_app. apply IHt1. apply H4.
    apply IHt2. auto.
  - destruct (x =? n) eqn:Heq. rewrite Nat.eqb_eq in Heq.
    subst. inv H. eapply tp_fun. rewrite update_shadow in H6.
    auto. inv H. eapply tp_fun. apply IHt.
    rewrite Nat.eqb_neq in Heq. rewrite update_permute.
    auto. auto.
  - destruct (x =? n) eqn:Heq. rewrite Nat.eqb_eq in Heq.
    subst. eapply tp_let. apply IHt1. inv H.
    apply H7. inv H. rewrite update_shadow in H8. auto.
    rewrite Nat.eqb_neq in Heq. eapply tp_let. apply IHt1.
    inv H. auto. apply IHt2. inv H. rewrite update_permute.
    auto. auto.
  - destruct (x =? n) eqn:Heq1; destruct (x =? n0) eqn:Heq2.
    + rewrite Nat.eqb_eq in Heq1. rewrite Nat.eqb_eq in Heq2.
      subst. inv H. destruct H9. auto.
    + rewrite Nat.eqb_eq in Heq1. subst.
      inv H. eapply tp_rec. auto. rewrite update_shadow in H10.
      auto. apply IHt2. clear Heq2.
      eapply context_invariance.
      apply H11. intros. rewrite update_same in H11. Admitted.


Theorem preservation : forall (t t' : term) (T : type),
  empty |: t ===> T -> t ---> t' -> empty |: t' ===> T.
Proof.
  intros t t' T Ht. remember (@empty type) as g. generalize dependent t'.
  induction Ht; intros t' He; try subst g; subst;
  try solve [inversion He; subst; auto].
  - pose (IHHt1 eq_refl). pose (IHHt2 eq_refl).
    inversion He; subst.
    Admitted.


Notation "A :: B" := (cons A B).
Notation "[]" := nil.
Notation "[[ A ]]" := (A :: nil).



Definition ident := nat.
Definition int := nat.

Definition lookup_list (A : Type) := list (ident * A).


Fixpoint lookup (A : Type) (x: ident) (l : lookup_list A) : option A :=
  match l with
  | nil => None
  | ((y, v) :: ys) => if (beq_nat x y) then Some v
    else lookup A x ys
  end.

Inductive Instruction : Type :=
  | INT : int -> Instruction
  | BOOL : bool -> Instruction
  | POP : Instruction
  | COPY : Instruction
  | ADD : Instruction
  | EQ : Instruction
  | GT : Instruction
  | AND : Instruction
  | NOT : Instruction
  | JUMP : nat -> Instruction
  | JUMPIFTRUE : nat -> Instruction
  | VAR : ident -> Instruction
  | FUN : ident -> list Instruction -> Instruction
  | RFUN : ident -> ident -> list Instruction -> Instruction
  | APPLY : Instruction.


Inductive StorableValue : Type :=
  | st_int : int -> StorableValue
  | st_bool : bool -> StorableValue
  | st_clos : Environment -> ident -> list Instruction -> StorableValue
  | st_rec_clos : Environment -> ident -> ident -> list Instruction -> StorableValue
  with Environment : Type :=
  | env : (lookup_list StorableValue) -> Environment.

Definition Code := list Instruction.

Fixpoint code_length (c : Code) : nat :=
  length c.

Fixpoint env_length (e: Environment) : nat :=
  match e with
  | env e' => length e'
  end.

Fixpoint sv_size (sv : StorableValue) : nat :=
  match sv with
  | st_int _ => 1
  | st_bool _ => 1
  | st_clos e _ c => 1 + (env_length e) + (code_length c)
  | st_rec_clos e _ _ c => 1 + (env_length e) + (code_length c)
  end.

Definition Stack := list StorableValue.
Definition Dump := list (Code * Stack * Environment).
Definition State : Type := (Code * Stack * Environment * Dump).

Definition initial_state (c: Code) : State :=
  (c, [], env [], []).



Scheme sv_mut := Induction for StorableValue Sort Prop
with env_mut := Induction for Environment Sort Prop.


Reserved Notation "A |> B" (at level 90, no associativity).
Inductive SSM_OP : State -> State -> Prop :=
  | push_int : forall (z : int), forall (c : list Instruction),
           forall (s : Stack), forall (e : Environment),
           forall (d : Dump),
    ((cons (INT z) c), s, e, d) |> (c, cons (st_int z) s, e, d)
  | push_bool : forall (b : bool), forall (c : list Instruction),
           forall (s : Stack), forall (e : Environment),
           forall (d : Dump),
    ((cons (BOOL b) c), s, e, d) |> ( c, cons (st_bool b) s, e, d)
  | pop_value : forall (c : list Instruction),
                forall (sv : StorableValue), forall (s : Stack),
                forall (e : Environment), forall (d : Dump),
    ( (cons POP c), cons sv s, e, d) |> ( c, s, e, d)
  | copy_value : forall (c : list Instruction),
                forall (sv : StorableValue), forall (s : Stack),
                forall (e : Environment), forall (d : Dump),
    ( (cons COPY c), cons sv s, e, d) |> ( c, cons sv (cons sv s), e, d)
  | add_value : forall (c : list Instruction),
                forall (z1 z2 : int), forall (s : Stack),
                forall (e: Environment), forall (d: Dump),
     ( (cons ADD c), cons (st_int z1) (cons (st_int z2) s), e, d)
     |> ( c, cons (st_int (z1 + z2)) s, e, d)
  
  | eq_value :  forall (c : list Instruction),
                forall (z1 z2 : int), forall (s : Stack),
                forall (e: Environment), forall (d: Dump),
                ( (EQ :: c), st_int z1 :: st_int z2 :: s, e, d)
                |> ( c, st_bool (beq_nat z1 z2) :: s, e, d)

  | gt_value: forall (c: list Instruction),
              forall (z1 z2 : int), forall (s: Stack),
              forall (e: Environment), forall (d: Dump),
              ( (GT :: c), st_int z1 :: st_int z2 :: s, e, d)
              |> ( c, st_bool (negb (z1 <? z2)) :: s, e, d)

  | and_value : forall (c : list Instruction),
              forall (b1 b2 : bool), forall (s: Stack),
              forall (e: Environment), forall (d: Dump),
              ( (AND :: c), st_bool b1 :: st_bool b2 :: s, e, d)
              |> ( c, st_bool (andb b1 b2) :: s, e, d)
  | not_value : forall (c : list Instruction),
              forall (b : bool), forall (s: Stack),
              forall (e: Environment), forall (d: Dump),
              ( (NOT :: c), st_bool b :: s, e, d)
              |> ( c, st_bool (negb b) :: s, e, d)
   | jump:    forall (c : list Instruction),
              forall (s : Stack), forall (e: Environment),
              forall (d : Dump), forall (n : nat),
              (List.length c) >= n+1 ->
              ( (JUMP n :: c), s, e, d) |>
              ( (List.skipn n c), s, e, d)
   | jump_true : forall (c : list Instruction),
              forall (s : Stack), forall (e: Environment),
              forall (d : Dump), forall (n : nat),
              List.length c >= n+1 ->
              ( (JUMPIFTRUE n :: c), st_bool true :: s, e, d)
              |> ( (List.skipn n c), s, e, d)
   | jump_false : forall (c : list Instruction),
              forall (s : Stack), forall (e: Environment),
              forall (d : Dump), forall (n : nat),
              ( (JUMPIFTRUE n :: c), st_bool false :: s, e, d)
              |> ( c, s, e, d)
   | var_lookup : forall (c : list Instruction),
              forall (s : Stack), forall (e: lookup_list StorableValue),
              forall (d: Dump), forall (x : ident),
              forall (sv : StorableValue), lookup StorableValue x e = Some sv -> 
              ( (VAR x :: c), s, env e, d) |>
              ( c, sv :: s, env e, d)
   | closure : forall (c : list Instruction), forall (c' : Code),
              forall (x : ident), forall (e: lookup_list StorableValue), forall (d: Dump),
              forall (s : Stack), ( (FUN x c' :: c), s, (env e), d) |>
              ( c, (st_clos (env e) x c') :: s, (env e), d)
   | r_closure : forall (c : list Instruction), forall (c' : Code),
              forall (x f : ident), forall (e: lookup_list StorableValue), forall (d: Dump),
              forall (s : Stack), ( (RFUN f x c' :: c), s, env e, d) |>
              ( c, (st_rec_clos (env e) f x c') :: s, (env e), d)
   | apply_normal : forall (c: list Instruction) (e' : lookup_list StorableValue)
              (x : ident) (c' : Code) (sv : StorableValue) (s : Stack)
              (e : Environment) (d : Dump),
              ( (APPLY :: c), (st_clos (env e') x c') :: sv :: s, e, d)
              |>
              (c', nil, env ((x, sv) :: e'), ( c, s, e) :: d)
    | apply_rec : forall (c: list Instruction) (e' : lookup_list StorableValue)
              (x f : ident) (c' : Code) (sv : StorableValue) (s : Stack)
              (e : Environment) (d : Dump),
              ( (APPLY :: c), (st_rec_clos (env e') f x c') :: sv :: s, e, d)
              |>
              (c', nil, env ((f, st_rec_clos (env e') f x c') :: (x,sv) :: e'), ( c, s, e) :: d)
    | pop_closure : forall (sv : StorableValue) (s' : Stack) (e e' : Environment)
                    (c' : Code) (d : Dump),
                    ( nil, sv :: nil, e, (c', s', e') :: d) |>
                    (c', sv :: s', e', d)


where "A |> B" := (SSM_OP A B).

Inductive state_value : State -> Prop :=
  | s_value : forall (sv : StorableValue) (e  : Environment), 
  state_value ( nil, sv :: nil, e, nil).

Reserved Notation "A |>* B" (at level 90, no associativity).
Inductive SSM_OP_Star : State -> State -> Prop :=
  | sos_refl : forall (s : State), s |>* s
  | sos_trans : forall (s1 s2 s3 : State), s1 |> s2 -> s2 |>* s3 -> s1 |>* s3
where "A |>* B" := (SSM_OP_Star A B).




Definition which_comp (op : nat -> nat -> bool) :=
  match (op 1 1) with
  | true => EQ
  | false => GT
  end.

Lemma which_comp_value : forall f, which_comp f = EQ \/ which_comp f = GT.
Proof. intros. unfold which_comp. destruct (f 1 1). left. auto. right. auto.
Qed.



Fixpoint compile (t : term) : Code :=
match t with
  | t_num n =>  [[INT n]]
  | t_bool b =>  [[BOOL b]]
  | t_op t1 (op_arith _) t2 =>  (( (compile t1)) ++ ( (compile t2)) ++ [[ ADD ]])
  | t_op t1 (op_comp c) t2 =>  (( (compile t1)) ++ ( (compile t2)) ++ [[ (which_comp c)]])
  | t_if e1 e2 e3 =>  (
                            ( (compile e1)) ++
                            [[JUMPIFTRUE (code_length (compile e3))]] ++
                            ( (compile e3)) ++
                            [[JUMP (code_length (compile e2))]] ++
                            ( (compile e2))
                           )
  | t_var x => [[VAR x]]
  | t_app e1 e2 => (
                          ( (compile e2)) ++
                          ( (compile e1)) ++
                          [[APPLY]]
                        )
  | t_fun y T e1 => [[FUN y (compile e1)]]
  | t_let y T e1 e2 => (
                              ( (compile e1)) ++
                              [[FUN y (compile e2)]] ++
                              [[APPLY]]
                            )
  | t_rec f T1 T2 y e1 e2 => (
                                    (RFUN f y (compile e1)) ::
                                    (FUN f (compile e2)) ::
                                    APPLY :: nil)
end.

Inductive multi_cost_language : term -> nat -> term -> Prop :=
  | multi_costl_refl : forall (t: term), multi_cost_language t 0 t
  | multi_costl_trans: forall (t1 t2 t3: term) (n: nat),
      (t1 ---> t2) -> multi_cost_language t2 n t3 -> multi_cost_language t1 (n+1) t3.

Inductive multi_cost_code : State -> nat -> State -> Prop :=
  | multi_costc_refl : forall (s : State), multi_cost_code s 0 s
  | multi_costc_trans: forall (s1 s2 s3 : State) (n: nat),
    (s1 |> s2) -> multi_cost_code s2 n s3 -> multi_cost_code s1 (n+1) s3.

Print term.

Inductive term_has_recursion : term -> Prop :=
  | rec_has_rec : forall x t1 t2 y t3 t4, term_has_recursion (t_rec x t1 t2 y t3 t4)
  | op_has_rec1 : forall t1 op t2, term_has_recursion t1 -> term_has_recursion (t_op t1 op t2)
  | op_has_rec2 : forall t1 op t2, term_has_recursion t2 -> term_has_recursion (t_op t1 op t2)
  | app_has_rec1 : forall t1 t2, term_has_recursion t1 -> term_has_recursion (t_app t1 t2)
  | app_has_rec2 : forall t1 t2, term_has_recursion t2 -> term_has_recursion (t_app t1 t2)
  | fun_has_rec : forall x tp t, term_has_recursion t -> term_has_recursion (t_fun x tp t)
  | let_has_rec1 : forall x tp t1 t2, term_has_recursion t1 -> term_has_recursion (t_let x tp t1 t2)
  | let_has_rec2 : forall x tp t1 t2, term_has_recursion t2 -> term_has_recursion (t_let x tp t1 t2)
  | if_has_rec1 : forall t1 t2 t3, term_has_recursion t1 -> term_has_recursion (t_if t1 t2 t3)
  | if_has_rec2 : forall t1 t2 t3, term_has_recursion t2 -> term_has_recursion (t_if t1 t2 t3)
  | if_has_rec3 : forall t1 t2 t3, term_has_recursion t3 -> term_has_recursion (t_if t1 t2 t3).

Lemma not_rec_subst : forall x t1 t2, ~ term_has_recursion t1 -> ~ term_has_recursion t2 ->
  ~ term_has_recursion ([x := t1] t2).
Proof.
  induction t2.
  - intros. intro. simpl in H1. inv H1.
  - intros. intro. simpl in H1. inv H1.
  - intros. assert (~ term_has_recursion t2_1). intro. apply H0. apply op_has_rec1. auto.
    assert (~ term_has_recursion t2_2). intro. apply H0. apply op_has_rec2. auto.
    apply IHt2_1 in H1. apply IHt2_2 in H2. intro. simpl in H3. inv H3. apply H1; auto.
    apply H2; auto. auto. auto.
  - intros. assert (~ term_has_recursion t2_1). intro. apply H0. apply if_has_rec1. auto.
    assert (~ term_has_recursion t2_2). intro. apply H0. apply if_has_rec2. auto.
    assert (~ term_has_recursion t2_3). intro. apply H0. apply if_has_rec3. auto.
    intro. simpl in H4. inv H4. apply IHt2_1 in H1. apply H1. auto. auto.
    apply IHt2_2 in H2. apply H2. auto. auto. apply IHt2_3. auto. auto.
    auto.
  - intros. intro. simpl in H1. destruct (x =? n) eqn:eq. apply H; auto.
    apply H0; auto.
  - intros. simpl. intro. assert (~ term_has_recursion t2_1). intro. apply H0.
    apply app_has_rec1. auto. assert (~ term_has_recursion t2_2). intro. apply H0.
    apply app_has_rec2. auto. inv H1. apply IHt2_1; auto. apply IHt2_2; auto.
  - intros. simpl. intro. assert (~ term_has_recursion t2). intro. apply H0.
    apply fun_has_rec. auto. destruct (x =? n) eqn:eq. apply H0; auto. inv H1.
    apply IHt2. auto. auto. auto.
  - intros. simpl. intro. assert (~ term_has_recursion t2_1). intro. apply H0.
    apply let_has_rec1; auto. assert (~ term_has_recursion t2_2). intro. apply H0.
    apply let_has_rec2; auto. destruct (x=?n). inv H1. apply IHt2_1; auto.
    apply H3; auto. inv H1. apply IHt2_1; auto. apply IHt2_2; auto.
  - intros. intro. apply H0. apply rec_has_rec. Qed.

Lemma not_rec_preservation : forall t t', ~ term_has_recursion t ->
  t ---> t' -> ~ term_has_recursion t'.
Proof.
  induction t.
  - intros. inv H0.
  - intros. inv H0.
  - intros. inv H0. assert (~ term_has_recursion t1 /\ ~ term_has_recursion t2). split;
    intro; apply H; [apply op_has_rec1 | apply op_has_rec2]; auto. destruct H0.
    eapply IHt1 in H0. intro. inv H2. destruct H0. eauto. destruct H1; auto. auto.
    intro. inv H0. apply H. apply op_has_rec1. auto. eapply IHt2.
    intro. apply H. apply op_has_rec2. auto. apply H5. auto. assert (~ term_has_recursion (t_num n1)
    /\ ~ term_has_recursion (t_num n2)). split; intro; apply H; [apply op_has_rec1 | apply op_has_rec2];
    auto. destruct H0. intro. inv H2. intro. inv H0.
  - intros. assert (~ term_has_recursion t1 /\ ~ term_has_recursion t2 /\ ~ term_has_recursion t3).
    split. intro. apply H. eapply if_has_rec1. auto. split; intro; apply H; [eapply if_has_rec2 |
    eapply if_has_rec3]; eauto. destruct H1. destruct H2. inversion H0. subst. auto. subst.
    auto. subst. intro. inv H4. eapply IHt1. auto. apply H8. auto.
    apply H2; auto. apply H3; auto.
  - intros. inv H0.
  - intros. assert (~ term_has_recursion t1 /\ ~ term_has_recursion t2). split; intro;
    apply H; [apply app_has_rec1 | apply app_has_rec2]; auto. destruct H1.
    inv H0. apply not_rec_subst; auto. intro. apply H1. apply fun_has_rec. auto.
    intro. apply IHt2 in H5. inv H0; auto. auto. intro. inv H0; auto.
    apply IHt1 in H6. apply H6; auto. auto.
  - intros. inv H0.
  - intros. assert (~ term_has_recursion t2). intro. apply H. apply let_has_rec1; auto.
    assert (~ term_has_recursion t3). intro. apply H. apply let_has_rec2; auto.
    inv H0. apply not_rec_subst; auto. apply IHt1 in H8; auto. intro.
    inv H0; auto.
  - intros. assert (term_has_recursion (t_rec n t1 t2 n0 t3 t4)). apply rec_has_rec.
    destruct H. auto. Qed.


Theorem cost_relation : forall t n m t' c', ~ term_has_recursion t ->
  multi_cost_language t n t' ->
  value t' ->
  multi_cost_code (initial_state (compile t)) m c' ->
  state_value c' ->
  m <= 10*n + 10.
Proof. induction t.
  - intros. assert (t' = (t_num n)). inv H0. auto. inv H4. subst.
    assert (n0 = 0). inv H0. auto. inv H4. subst. simpl. inv H2. omega.
    inv H4. inv H5. omega. inv H2.
  - intros. inv H0. inv H2. omega. inv H0. inv H4. omega. inv H0. inv H4.
  - intros.





Fixpoint term_size (t: term) : nat :=
  match t with
  | t_num _ => 1
  | t_bool _ => 1
  | t_op t1 _ t2 => 1 + (term_size t1) + (term_size t2)
  | t_if t1 t2 t3 => 1 + (term_size t1) + (term_size t2) + (term_size t3)
  | t_var _ => 1
  | t_app t1 t2 => 1 + (term_size t2) + (term_size t1)
  | t_fun _ _ t1 => 2 + (term_size t1)
  | t_let _ _ t1 t2 => 2 + (term_size t1) + (term_size t2)
  | t_rec _ _ _ _ t1 t2 => 3 + (term_size t1) + (term_size t2)
  end.


Fixpoint add_list (l: list nat) : nat :=
  match l with
  | [] => 0
  | n :: l' => n + (add_list l')
  end.

Fixpoint inst_depth (i: Instruction) : nat :=
  match i with
  | FUN _ l => 1 + (add_list (map inst_depth l))
  | RFUN _ _ l => 1 + (add_list (map inst_depth l))
  | _ => 1
  end.

Definition code_depth (c: Code) := add_list (map inst_depth c).
Definition code_depth_plus (c: Code) := (length c) + (add_list (map inst_depth c)).


Function code_size (c: Code) {measure code_depth c} : nat :=
  match c with
  | [] => 0
  | INT _ :: c' => 2 + (code_size c')
  | BOOL _ :: c' => 2 + (code_size c')
  | JUMP _ :: c' => 2 + (code_size c')
  | JUMPIFTRUE _ :: c' => 2 + (code_size c')
  | VAR _ :: c' => 2 + (code_size c')
  | FUN _ ci :: c' => 2 + (code_size ci) + (code_size c')
  | RFUN _ _ ci :: c' => 3 + (code_size ci) + (code_size c')
  | _ :: c' => 1 + (code_size c')
  end.
Proof.
  - intros; subst; auto.
  - intros; subst; auto.
  - intros; subst; auto.
  - intros; subst; auto.
  - intros; subst; auto.
  - intros; subst. unfold code_depth. simpl. omega.
  - intros; subst; auto.
  - intros; subst. unfold code_depth. simpl. omega.
  - intros; subst. unfold code_depth. simpl. omega.
  - intros; subst; auto.
  - intros; subst; auto.
  - intros; subst; auto.
  - intros; subst. unfold code_depth. simpl. omega.
  - intros; subst. unfold code_depth. simpl. omega.
  - intros; subst; auto. unfold code_depth. simpl. omega.
  - intros; subst; auto. unfold code_depth. simpl. omega.
  - intros; subst; auto.
Defined.


Lemma length_distr : forall A (l1 l2 : list A), length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  intros. induction l1; induction l2; auto.
  - simpl. Search app. rewrite <- app_nil_end. auto.
  - simpl. rewrite IHl1. simpl. auto. Qed.

Lemma code_size_distr1 : forall a c, code_size (a :: c) = code_size [[a]] + code_size c.
Proof.
  intros. induction a; rewrite code_size_equation; auto. simpl. assert (code_size [[FUN i l]] =
  2 + (code_size l)). rewrite code_size_equation. auto. rewrite H. auto.
  assert (code_size [[RFUN i i0 l]] = 3 + code_size l). rewrite code_size_equation. auto.
  rewrite H. auto. Qed.

Lemma code_size_distr : forall c1 c2, code_size (c1 ++ c2) = (code_size c1) + (code_size c2).
Proof.
  intros. induction c1; auto. destruct a; rewrite code_size_equation; simpl;
  rewrite IHc1; rewrite code_size_distr1; auto.
  assert (code_size [[FUN i l]] = 2 + code_size l). rewrite code_size_equation. auto.
  rewrite H. omega. assert (code_size [[RFUN i i0 l]] = 3 + code_size l). rewrite code_size_equation.
  auto. rewrite H. omega. Qed.



Theorem length_relation :
  forall t, (code_size (compile t)) < 3 * (term_size t).
Proof.
  intros. induction t; try (solve [simpl; unfold code_size; simpl; omega]).
  - destruct o.
    + simpl compile. repeat (rewrite code_size_distr). simpl term_size.
      assert (code_size [[ADD]] = 1). auto. rewrite H. omega.
    + simpl compile. repeat (rewrite code_size_distr). simpl term_size.
      pose (which_comp_value b). destruct o; rewrite H. cbn. omega. cbn. omega.
  - simpl compile. rewrite code_size_distr. rewrite  code_size_distr1. rewrite code_size_distr.
    assert (code_size (JUMP (code_length (compile t2)) :: compile t2) =
    code_size [[JUMP (code_length (compile t2))]] + code_size (compile t2)).
    apply code_size_distr1. rewrite H. clear H. cbn. omega.
  - simpl compile. repeat (rewrite code_size_distr). cbn; omega.
  - simpl compile. rewrite code_size_equation. cbn. omega.
  - simpl compile. rewrite code_size_distr. rewrite code_size_distr1.
    simpl term_size. assert (code_size [[FUN n (compile t3)]] = 2 + code_size (compile t3)).
    rewrite code_size_equation. auto. rewrite H; clear H. cbn. omega.
  - simpl compile. rewrite code_size_distr1. assert (code_size (FUN n (compile t4) :: [[APPLY]]) =
    code_size [[FUN n (compile t4)]] + code_size [[APPLY]]). apply code_size_distr1.
    rewrite H; clear H. assert (code_size [[RFUN n n0 (compile t3)]] = 3 + code_size (compile t3)).
    rewrite code_size_equation. auto. rewrite H; clear H. assert (code_size [[FUN n (compile t4)]] =
    2 + code_size (compile t4)). rewrite code_size_equation; auto. rewrite H; clear H.
    cbn; omega.
Qed.









































































