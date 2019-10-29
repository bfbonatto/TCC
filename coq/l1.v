
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
  - destruct o. destruct o0.
    + subst. pose (value_nat_is_num empty e1 H H1).
      inversion e. subst. pose (value_nat_is_num empty e2 H0 H2).
      inversion e0. subst. exists (t_num (f x x0)). auto.
    + inversion H2. exists (t_op e1 (op_arith f) x). auto.
    + inversion H1. exists (t_op x (op_arith f) e2). auto.
  - destruct o. destruct o0.
    + subst. pose (value_nat_is_num empty e1 H H1).
      inversion e. subst. pose (value_nat_is_num empty e2 H0 H2).
      inversion e0. subst. exists (t_bool (f x x0)). auto.
    + inversion H2. exists (t_op e1 (op_comp f) x). auto.
    + inversion H1. exists (t_op x (op_comp f) e2). auto.
  - destruct o. apply value_bool_is_bool in H. destruct H; subst.
    exists t2; auto. exists t3; auto. auto. inversion H2.
    exists (t_if x t2 t3). auto.
  - inversion Heqgamma. subst. inversion H.
  - destruct o. apply value_fun_is_fun in H. inversion H. inversion H2.
    subst. destruct o0. exists ([x:=e2]x0). auto.
    inversion H3. exists (t_app (t_fun x T x0) x1). auto.
    auto. inversion H1. exists (t_app x e2). auto.
  - destruct o. exists ([x:=e1] e2). auto.
    inversion H1. exists (t_let x T x0 e2). auto.
  - clear IHcheck1. clear IHcheck2.
    exists ([f:=(t_fun x T1 (t_rec f T1 T2 x e1 e1))]e2). auto.
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

Lemma free_is_equal : forall x t e,
  ~ appears_free_in x t ->
  [x := e]t = t.
Proof.
Hint Constructors step.
Hint Constructors check.
Hint Constructors term.
Hint Constructors value.
Hint Constructors type.
Hint Constructors op.
Hint Constructors appears_free_in.

  intros. induction t; auto.
  Admitted.





Lemma substitution_lemma : forall Gamma x U t v T,
  (x |-> U ; Gamma) |: t ===> T ->
  empty |: v ===> U   ->
  Gamma |: [x:=v]t ===> T.
Proof.

Hint Constructors step.
Hint Constructors check.
Hint Constructors term.
Hint Constructors value.
Hint Constructors type.
Hint Constructors op.


  intros. generalize dependent Gamma. generalize dependent T.
  induction H0.
  - intros. destruct (classic (appears_free_in x t)).
    + admit.
    Admitted.




Theorem preservation : forall (t t' : term) (T : type),
  empty |: t ===> T -> t ---> t' -> empty |: t' ===> T.
Proof.
  intros t t' T Ht. remember (@empty type) as g. generalize dependent t'.
  induction Ht; intros t' He; try subst g; subst;
  try solve [inversion He; subst; auto].
  - pose (IHHt1 eq_refl). pose (IHHt2 eq_refl).
    inversion He; subst.
    Admitted.


Definition ident := nat.
Definition int := nat.


Inductive StorableValue : Set :=
  | st_int : int -> StorableValue
  | st_bool : bool -> StorableValue
  | st_clos : Environment -> ident -> Code -> StorableValue
  | st_rec_clos : Environment -> ident -> ident -> Code -> StorableValue
  with Environment : Set :=
  | env : list (ident * StorableValue) -> Environment
  with Code : Set :=
  | code : list Instruction -> Code
  with Instruction : Set :=
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
  | JMPIFTRUE : nat -> Instruction
  | VAR : ident -> Instruction
  | FUN : ident -> Code -> Instruction
  | RFUN : ident -> ident -> Code -> Instruction
  | APPLY : Instruction.

Definition Stack := list StorableValue.
Definition Dump := list (Code * Stack * Environment).
Definition State : Set := (Code * Stack * Environment * Dump).

Scheme sv_mut := Induction for StorableValue Sort Prop
with env_mut := Induction for Environment Sort Prop
with code_mut := Induction for Code Sort Prop
with inst_mut := Induction for Instruction Sort Prop.


Reserved Notation "A |> B" (at level 90, no associativity).
Inductive SSM_OP : State -> State -> Prop :=
  | push_int : forall (z : int), forall (c : list Instruction),
           forall (s : Stack), forall (e : Environment),
           forall (d : Dump),
    (code (cons (INT z) c), s, e, d) |> (code c, cons (st_int z) s, e, d)
  | push_bool : forall (b : bool), forall (c : list Instruction),
           forall (s : Stack), forall (e : Environment),
           forall (d : Dump),
    (code (cons (BOOL b) c), s, e, d) |> (code c, cons (st_bool b) s, e, d)
  | pop_value : forall (c : list Instruction),
                forall (sv : StorableValue), forall (s : Stack),
                forall (e : Environment), forall (d : Dump),
    (code (cons POP c), cons sv s, e, d) |> (code c, s, e, d)
  | copy_value : forall (c : list Instruction),
                forall (sv : StorableValue), forall (s : Stack),
                forall (e : Environment), forall (d : Dump),
    (code (cons COPY c), cons sv s, e, d) |> (code c, cons sv (cons sv s), e, d)
  | 


where "A |> B" := (SSM_OP A B).





























































