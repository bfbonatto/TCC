
From Coq Require Import Arith.
From Coq Require Import Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical_Prop.
From Coq Require Import omega.Omega.
Require Import Nat.


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
  intros. assert (x = x0 -> (x !-> v2; x !-> v1; m) x0 = (x !-> v2; m) x0).
  - intros. rewrite H. unfold t_update. rewrite Nat.eqb_refl. auto.
  - assert (x <> x0 -> (x !-> v2; m) x0 = m x0).
    + intros. unfold t_update. rewrite eqb_false_iff. auto. auto.
    + assert (x <> x0 -> (x !-> v2; x !-> v1; m) x0 = m x0).
      * intros. unfold t_update. rewrite eqb_false_iff. auto. auto.
      * pose (classic (x = x0)). destruct o.
        apply H in H2. auto. pose (H0 H2). pose (H1 H2). rewrite e.
        rewrite e0. auto.
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
  intros. assert ((x1 !-> v1; x2 !-> v2; m) x1 = v1).
  unfold t_update. rewrite Nat.eqb_refl. auto.
  assert ((x1 !-> v1; x2 !-> v2; m) x2 = v2).
  unfold t_update. rewrite Nat.eqb_refl. rewrite eqb_false_iff.
  auto. auto. assert ((x2 !-> v2; x1 !-> v1; m) x2 = v2).
  unfold t_update. rewrite Nat.eqb_refl. auto.
  assert ((x2 !-> v2; x1 !-> v1; m) x1 = v1). unfold t_update.
  rewrite eqb_false_iff. rewrite Nat.eqb_refl. auto. auto.
  assert (forall x:nat, x <> x1 -> x <> x2 -> (x1 !-> v1; x2 !-> v2; m) x =
(x2 !-> v2; x1 !-> v1; m) x).
  - intros. unfold t_update. rewrite eqb_false_iff. rewrite eqb_false_iff. auto.
    auto. auto.
  - apply functional_extensionality_dep. intros. assert (x = x1 -> (x1 !-> v1; x2 !-> v2; m) x =
(x2 !-> v2; x1 !-> v1; m) x). intros. rewrite H5. rewrite H0. rewrite H3. auto.
    assert (x = x2 -> (x1 !-> v1; x2 !-> v2; m) x =
(x2 !-> v2; x1 !-> v1; m) x). intros. rewrite H6. rewrite H1. rewrite H2. auto.
    pose (classic (x = x1)). destruct o.
    + apply H5 in H7. auto.
    + pose (classic (x = x2)). destruct o.
      * apply H6 in H8. auto.
      * pose (H4 x H7 H8). auto.
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

(*
Inductive i_subst (s : term) (x : nat) : term -> term -> Prop :=
  | s_num : forall (n : nat), i_subst s x (t_num n) (t_num n)
  | s_bool : forall (b : bool), i_subst s x (t_bool b) (t_bool b)
  | 
 TODO *)



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

  | e_beta     : forall (x : nat) (T : type) (e v : term), t_app (t_fun x T e) v ---> [x:=v]e
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
  intros. remember (@empty type) as gamma. induction H.
  - left. apply val_nat.
  - left. apply val_bool.
  - right. pose (IHcheck1 Heqgamma). pose (IHcheck2 Heqgamma).
    destruct o; destruct o0; subst.
    + pose (value_nat_is_num empty e1 H H1). inversion e. subst.
      pose (value_nat_is_num empty e2 H0 H2). inversion e0. subst.
      exists (t_num (f x x0)). apply e_op_arith.
    + inversion H2. exists (t_op e1 (op_arith f) x).
      apply e_op2; auto.
    + inversion H1. exists (t_op x (op_arith f) e2). apply e_op1.
      auto.
    + inversion H1. exists (t_op x (op_arith f) e2). apply e_op1.
      auto.
  - right. pose (IHcheck1 Heqgamma). pose (IHcheck2 Heqgamma). destruct o;
    destruct o0; subst.
    + pose (value_nat_is_num empty e1 H H1). inversion e. subst.
      pose (value_nat_is_num empty e2 H0 H2). inversion e0. subst.
      exists (t_bool (f x x0)). apply e_op_comp.
    + inversion H2. exists (t_op e1 (op_comp f) x). apply e_op2; auto.
    + inversion H1. exists (t_op x (op_comp f) e2). apply e_op1; auto.
    + inversion H1. exists (t_op x (op_comp f) e2). apply e_op1; auto.
  - right. pose (IHcheck1 Heqgamma). pose (IHcheck2 Heqgamma).
    pose (IHcheck3 Heqgamma); subst.
    destruct o. pose (value_bool_is_bool empty t1 H H2). destruct o; subst.
    exists t2. apply e_if_t. exists t3. apply e_if_f.
    inversion H2. exists (t_if x t2 t3). apply e_if.
    auto.
  - subst. inversion H.
  - left. apply val_fun.
  - right. pose (IHcheck1 Heqgamma). pose (IHcheck2 Heqgamma).
    destruct o.
    + subst. destruct o0; subst.
      * pose (value_fun_is_fun empty e1 T T' H H1). inversion e.
        inversion H3. subst. exists ([x:=e2]x0). apply e_beta.
      * inversion H2. exists (t_app e1 x). apply e_app2. auto.
        auto.
    + inversion H1. exists (t_app x e2). apply e_app1. auto.
  - pose (IHcheck1 Heqgamma). destruct o; subst.
    + assert (t_let x T e1 e2 ---> [x:=e1]e2). apply e_let1. auto.
      right. exists ([x:=e1]e2). auto.
    + inversion H1. right. exists (t_let x T x0 e2). apply e_let2.
      auto.
  - subst. right. exists ([f:=(t_fun x T1 (t_rec f T1 T2 x e1 e1))]e2).
    apply e_rec.
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

Lemma context_invariance : forall Gamma Gamma' t T,
  Gamma |: t ===> T ->
  (forall x, appears_free_in x t -> Gamma x = Gamma' x) ->
  Gamma' |: t ===> T.
Proof.
  intros. generalize dependent Gamma'.
  induction H; intros; auto.
  - apply tp_num.
  - apply tp_bool.
  - apply tp_arith; auto. apply IHcheck1.
    intros. assert (appears_free_in x (t_op e1 (op_arith f) e2)).
    apply afi_op1. auto. apply H1 in H3. auto.
    apply IHcheck2. intros. assert (appears_free_in x (t_op e1 (op_arith f) e2)).
    apply afi_op2. auto. apply H1 in H3. auto.
  - apply tp_comp; auto. apply IHcheck1.
    intros. assert (appears_free_in x (t_op e1 (op_comp f) e2)).
    apply afi_op1. auto. apply H1 in H3. auto.
    apply IHcheck2. intros. assert (appears_free_in x (t_op e1 (op_comp f) e2)).
    apply afi_op2. auto. apply H1 in H3. auto.
  - apply tp_if.
    apply IHcheck1. intros. apply H2. apply afi_if1. auto.
    apply IHcheck2. intros. apply H2. apply afi_if2. auto.
    apply IHcheck3. intros. apply H2. apply afi_if3. auto.
  - apply tp_var. pose (H0 n). assert (appears_free_in n (t_var n)).
    apply afi_var. apply e in H1. rewrite <- H. auto.
  - apply tp_fun. apply IHcheck. intros. destruct (classic (x = x0)).
    + subst. rewrite update_eq. rewrite update_eq. auto.
    + rewrite update_neq; auto. rewrite update_neq; auto.
      apply H0. apply afi_fun; auto.
  - apply tp_app with T.
    apply IHcheck1. intros. apply H1. apply afi_app1. auto.
    apply IHcheck2. intros. apply H1. apply afi_app2. auto.
  - apply tp_let. apply IHcheck1. intros. apply H1. apply afi_let1; auto.
    apply IHcheck2. intros. destruct (classic (x = x0)).
    + subst. rewrite update_eq. rewrite update_eq. auto.
    + rewrite update_neq; auto. rewrite update_neq; auto.
      apply H1. apply afi_let2; auto.
  - apply tp_rec; auto.
    + apply IHcheck1. intros. destruct (classic (x = x0)).
      subst. rewrite update_eq. rewrite update_eq. auto.
      destruct (classic (f = x0)). subst.
      rewrite update_neq. rewrite update_eq.
      rewrite update_neq. rewrite update_eq.
      auto. auto. auto. rewrite update_neq; auto.
      rewrite update_neq; auto. rewrite update_neq; auto.
      rewrite update_neq; auto. apply H2.
      apply afi_rec1; auto.
    + apply IHcheck2; subst. intros. destruct (classic (f = x0)).
      subst. rewrite update_eq. rewrite update_eq. auto.
      rewrite update_neq; auto. rewrite update_neq; auto.
      apply H2. apply afi_rec2; auto.
Qed.



Lemma empty_context : forall t T Gamma,
  empty |: t ===> T ->
  Gamma |: t ===> T.
Proof.
  intros. remember (@empty type) as g. induction H.
  - apply tp_num.
  - apply tp_bool.
  - apply tp_arith; auto.
  - apply tp_comp; auto.
  - apply tp_if; auto.
  - apply tp_var; auto. subst. inversion H.
  - apply tp_fun. subst. subst.
    pose (context_invariance (x |-> T) (x |-> T ; Gamma)
    e T' H). apply c. intros. destruct (classic (x = x0)).
    + subst. repeat rewrite update_eq. auto.
    + repeat rewrite update_neq; auto.
      pose (free_in_context x0 e T' (x|->T) H0 H).
      inversion e0. rewrite update_neq in H2; auto.
      inversion H2.
  - pose (tp_app e1 e2 Gamma T T'). subst.
    auto.
  - apply tp_let. auto. subst.
    pose (context_invariance (x|->T) (x|->T;Gamma) e2 T').
    apply c; auto. clear c. intros. destruct (classic (x = x0)).
    + subst. repeat rewrite update_eq; auto.
    + repeat rewrite update_neq; auto.
      pose (free_in_context x0 e2 T' (x|->T) H1 H0).
      inversion e. rewrite update_neq in H3; auto. inversion H3.
  - apply tp_rec; auto.
    + subst. pose (context_invariance (x|->T1;f|->type_fun T1 T2)
      (x|->T1;f|->type_fun T1 T2; Gamma) e1 T2 H0). apply c; auto.
      clear c. intros. destruct (classic (x = x0)).
      * subst. destruct (classic (f = x0)).
        { subst. unfold not in H. assert (x0 = x0). auto.
          apply H in H3. inversion H3. }
        { repeat rewrite update_eq; auto. }
      * destruct (classic (f = x0)).
        { subst. rewrite update_neq; auto. rewrite update_eq; auto.
          rewrite update_neq; auto. rewrite update_eq; auto. }
        { repeat rewrite update_neq; auto.
          pose (free_in_context x0 e1 T2 (x|->T1;f|->type_fun T1 T2)
          H2 H0). inversion e. rewrite update_neq in H5; auto.
          rewrite update_neq in H5; auto. inversion H5. }
    + subst. clear IHcheck1. clear IHcheck2.
      pose (context_invariance (f|->type_fun T1 T2)
      (f|->type_fun T1 T2; Gamma) e2 T H1).
      apply c. clear c. intros.
      pose (free_in_context x0 e2 T (f|->type_fun T1 T2) H2 H1).
      inversion e. destruct (classic (f = x0)).
      * subst. repeat rewrite update_eq; auto.
      * rewrite update_neq in H3. inversion H3. auto.
Qed.




Lemma substitution_lemma : forall Gamma x U t v T,
  (x |-> U ; Gamma) |: t ===> T ->
  empty |: v ===> U   ->
  Gamma |: [x:=v]t ===> T.
Proof.
  (*intros. generalize dependent Gamma. generalize dependent T.
  induction t.
  - intros. inversion H. subst. assert (([x:=v] t_num n) = t_num n).
    auto. assert (Gamma |: t_num n ===> type_nat). apply tp_num.
    rewrite H1. auto.
  - intros. inversion H. subst. assert (([x:=v] t_bool b) = t_bool b).
    auto. assert (Gamma |: t_bool b ===> type_bool). apply tp_bool.
    auto.
  - intros. inversion H. subst. pose (IHt1 type_nat Gamma H6).
    pose (IHt2 type_nat Gamma H7).
    assert (([x:=v] t_op t1 (op_arith f) t2) = (t_op ([x:=v]t1) (op_arith f) ([x:=v]t2))).
    auto. rewrite H1. apply tp_arith; auto. subst.
    assert (([x:=v] t_op t1 (op_comp f) t2) = (t_op ([x:=v]t1) (op_comp f) ([x:=v]t2))).
    auto. rewrite H1. apply tp_comp; auto.
  - intros. inversion H. subst.
    pose (IHt1 type_bool Gamma H5).
    pose (IHt2 T Gamma H7).
    pose (IHt3 T Gamma H8).
    assert (([x:=v] t_if t1 t2 t3) = (t_if ([x:=v]t1) ([x:=v]t2) ([x:=v]t3))).
    auto. rewrite H1. apply tp_if; auto.
  - intros. destruct (classic (x = n)).
    + subst. destruct (classic (U = T)).
      * subst. assert (([n:=v] t_var n) = v).
        unfold f_subst. rewrite Nat.eqb_refl. auto.
        rewrite H1. apply empty_context. auto.
      * inversion H. subst. inversion H4. pose (update_eq type Gamma n U).
        rewrite e in H3. inversion H3. contradiction.
    + assert (([x:=v] t_var n) = t_var n). unfold f_subst.
      pose (eqb_false_iff x n H1). rewrite e. auto.
      rewrite H2. apply tp_var. inversion H. subst.
      unfold update in H5. unfold t_update in H5.
      pose (eqb_false_iff x n H1). rewrite e in H5. auto.
  - intros. inversion H. subst.
    assert (([x:=v] t_app t1 t2) = t_app ([x:=v]t1) ([x:=v]t2)).
    auto. rewrite H1. apply tp_app with T0.
    pose (IHt1 (type_fun T0 T) Gamma H4). auto.
    pose (IHt2 T0 Gamma H6). auto.
  - intros. destruct (classic (x = n)).
    + subst. destruct (classic (U = T)).
      * subst. unfold f_subst. rewrite Nat.eqb_refl.
        inversion H. subst. apply tp_fun.
        pose (update_shadow type Gamma n (type_fun t T') t ).
        rewrite e in H6. auto.
      * unfold f_subst. rewrite Nat.eqb_refl. inversion H.
        subst. apply tp_fun.
        pose (update_shadow type Gamma n U t). rewrite e in H7.
        auto.
    + assert (([x:=v] t_fun n t t0) = (t_fun n t ([x:=v]t0))).
      pose (eqb_false_iff x n H1). unfold f_subst. rewrite e.
      auto. rewrite H2. inversion H. subst. apply tp_fun.
      pose (update_permute type Gamma n x t U H1). rewrite e in H8.
      pose (IHt T' (n |-> t; Gamma) H8). auto.
  - intros. destruct (classic (x = n)).
    + subst. inversion H. subst.
      assert (([n:=v] t_let n t1 t2 t3) = (t_let n t1 ([n:=v]t2) t3)).
      unfold f_subst. rewrite Nat.eqb_refl. auto.
      rewrite H1. apply tp_let.
      pose (IHt1 t1 Gamma H7). auto.
      pose (update_shadow type Gamma n U t1). rewrite e in H8.
      auto.
    + inversion H. subst.
      assert (([x:=v] t_let n t1 t2 t3) = (t_let n t1 ([x:=v]t2) ([x:=v]t3))).
      unfold f_subst. pose (eqb_false_iff x n H1). rewrite e. auto.
      rewrite H2. apply tp_let. pose (IHt1 t1 Gamma H8). auto.
      pose (update_permute type Gamma n x t1 U H1).
      rewrite e in H9. pose (IHt2 T (n |-> t1 ; Gamma) H9).
      auto.
  - intros. destruct (classic (x = n)); destruct (classic (x = n0)).
    { subst. inversion H; subst. contradiction. }
    { subst. pose (eqb_false_iff n n0 H2). assert
      (([n := v] t_rec n t1 t2 n0 t3 t4) =
       (t_rec n t1 t2 n0 t3 ([n := v] t4))).
      unfold f_subst. rewrite e. rewrite Nat.eqb_refl. auto.
      rewrite H1. clear e. clear H1. apply tp_rec; auto.
      inversion H; subst. rewrite update_shadow in H11; auto.
      apply IHt2. inversion H; subst. }
    { subst. }
    { auto. }*)

  intros. generalize dependent Gamma. generalize dependent T.
  induction t.
  - intros. assert (([x:=v] t_num n) = t_num n).
    auto. rewrite H1. inversion H. subst. apply tp_num.
  - intros. inversion H. subst. apply tp_bool.
  - intros. destruct o.
    + assert (([x:=v] t_op t1 (op_arith n) t2) = (t_op ([x:=v] t1) (op_arith n) ([x:=v] t2))).
      auto. rewrite H1. inversion H. subst. apply tp_arith; auto.
    + assert (([x:=v] t_op t1 (op_comp b) t2) = (t_op ([x:=v] t1) (op_comp b) ([x:=v] t2))).
      auto. rewrite H1. inversion H. subst. apply tp_comp; auto.
  - intros. inversion H; subst. apply tp_if; auto.
  - intros. destruct (classic (x = n)).
    + subst. destruct (classic (U = T)).
      * subst. assert (([n:=v] t_var n) = v).
        unfold f_subst. rewrite Nat.eqb_refl. auto.
        rewrite H1. apply empty_context. auto.
      * inversion H. subst. inversion H4. pose (update_eq type Gamma n U).
        rewrite e in H3. inversion H3. contradiction.
    + assert (([x:=v] t_var n) = t_var n). unfold f_subst.
      pose (eqb_false_iff x n H1). rewrite e. auto.
      rewrite H2. apply tp_var. inversion H. subst.
      unfold update in H5. unfold t_update in H5.
      pose (eqb_false_iff x n H1). rewrite e in H5. auto.
  - intros. inversion H; subst. apply IHt1 in H4. apply IHt2 in H6.
    assert (([x := v] t_app t1 t2) = (t_app ([x:=v] t1) ([x:=v] t2))).
    auto. rewrite H1. apply tp_app with (T:=T0). auto. auto.
  - intros. inversion H; subst. 


Admitted.




Theorem preservation : forall (t t' : term) (T : type),
  empty |: t ===> T -> t ---> t' -> empty |: t' ===> T.
Proof.
  intros t t' T Ht. remember (@empty type) as g. generalize dependent t'.
  induction Ht; intros t' He; try subst g; subst;
  try solve [inversion He; subst; auto].
  - pose (IHHt1 eq_refl). pose (IHHt2 eq_refl).
    inversion He; subst.
    + apply tp_arith. pose (c e1' H3). auto.
      auto.
    + apply tp_arith. auto. pose (c0 e2' H3). auto.
    + apply tp_num.
  - pose (IHHt1 eq_refl). pose (IHHt2 eq_refl).
    inversion He; subst.
    + apply tp_comp. pose (c e1' H3); auto. auto.
    + apply tp_comp. pose (c0 e2' H3). auto. auto.
    + apply tp_bool.
  - pose (IHHt1 eq_refl). pose (IHHt3 eq_refl). pose (IHHt2 eq_refl).
    inversion He; subst.
    + auto.
    + auto.
    + apply tp_if. pose (c e1' H3). auto. auto. auto.
  - inversion He; subst.
    + pose (substitution_lemma empty x T e e2 T').
      inversion Ht1. subst. pose (c H1 Ht2). auto.
    + pose (IHHt2 eq_refl). pose (c e2' H1). apply tp_app with T. auto.
      auto.
    + pose (IHHt1 eq_refl). pose (c e1' H2). apply tp_app with T. auto.
      auto.
  - inversion He; subst.
    + pose (substitution_lemma empty x T e2 e1 T').
      pose (c Ht2 Ht1). auto.
    + apply tp_let. pose (IHHt1 eq_refl). pose (c e1' H4). auto.
      auto.
  - clear IHHt1. clear IHHt2. inversion He; subst.
    remember (type_fun T1 T2) as tpf.
    remember (t_fun x T1 (t_rec f T1 T2 x e1 e1)) as frec.
    pose (substitution_lemma empty f tpf e2 frec T).
    apply c in Ht2. auto. clear c. subst. apply tp_fun.
    apply tp_rec.
    + pose (update_permute type empty f x (type_fun T1 T2) T1).
      auto.
    + rewrite update_permute; auto. rewrite update_shadow; auto.
      rewrite update_permute; auto.
    + rewrite update_permute; auto.

Qed.
































