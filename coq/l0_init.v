(* Bibliotecas importadas *)
Require Import Arith ZArith Znat List Classical_Prop Classical_Pred_Type.
Require Import Coq.Setoids.Setoid.
Require Import Coq.omega.Omega.
Require Import Coq.Program.Equality.

(*****************************************************************)
(*                  Sintaxe abstrata de L0                       *)
(*****************************************************************)


(* Termos *)
Inductive term :=
 | zero   : term
 | succ   : term -> term
 | true   : term
 | false  : term
 | iszero : term -> term
 | pred   : term -> term
 | ifte   : term -> term -> term -> term.



(* Valores num\u00e9ricos *)
Inductive nv : term -> Prop :=
 | zeroNum : nv zero
 | succNum : forall n, (nv n) -> nv (succ n).


(* Valores *)
Inductive value : term -> Prop :=
 | trueVal  : value true
 | falseVal : value false
 | numVal   : forall n, (nv n) -> (value n).




(*****************************************************************)
(*              Sem\u00e2ntica operacional small-step                 *)
(*****************************************************************)


(* Rela\u00e7\u00e3o de avalia\u00e7\u00e3o em um passo *)
Reserved Notation "A ---> B" (at level 90, no associativity).
Inductive step : term -> term -> Prop :=
 | e_iftrue     : forall t2 t3,                        ifte true  t2 t3 ---> t2  
 | e_iffalse    : forall t2 t3,                        ifte false t2 t3 ---> t3
 | e_if         : forall t1 t2 t3 t1', t1 ---> t1' ->  ifte t1    t2 t3 ---> ifte t1' t2 t3
 | e_succ       : forall (t t':term),  t  ---> t'  ->  succ t           ---> succ t'
 | e_predzero   :                                      pred zero        ---> zero 
 | e_predsucc   : forall t,            nv t        ->  pred (succ t)    ---> t
 | e_pred       : forall t t',         t  ---> t'  ->  pred t           ---> pred t'
 | e_iszerozero :                                      iszero zero      ---> true
 | e_iszerosucc : forall t,            nv t        ->  iszero (succ t)  ---> false
 | e_iszero     : forall t t',         t  ---> t'  ->  iszero t         ---> iszero t'
where "A ---> B" := (step A B).

(* Rela\u00e7\u00e3o de avalia\u00e7\u00e3o em zero ou mais passos *)
Reserved Notation "A -*-> B" (at level 90, no associativity). 
Inductive multistep : term -> term -> Prop :=
 | m_refl    : forall t,     t -*-> t
 | m_cons    : forall t1 t2 t3, (t1 ---> t2) -> (t2 -*-> t3) -> (t1 -*-> t3)
where "A -*-> B" := (multistep A B). 



Lemma l3 : forall t t': term, t -*-> t' ->
  (forall u, (t = succ u) ->
    exists u', (t' = succ u') /\ (u -*-> u')).
Proof.
  Admitted.






(* Forma normal *)
Definition NF (t:term)    : Prop :=  not (exists t', t ---> t').


(* Possuir forma normal *)
Definition HasNF (t:term) : Prop :=  exists t', (t -*-> t') /\ (NF t').


(* Termo preso *)
Definition Stuck (t:term) : Prop :=  NF(t) /\ not (value t).


(* Termo leva a erro *)
Definition Error (t:term) : Prop :=  exists t', (t -*-> t') /\ Stuck(t').


(* Termo diverge *)
Definition Diverge (t:term) : Prop := forall t', t -*-> t' -> exists t'', t' ---> t''.

Inductive type : Type :=
  |   typeNat   : type
  |   typeBool  : type.


Reserved Notation "A ===> B" (at level 90, no associativity).
Inductive check : term -> type -> Prop :=
  | t_zero      :       zero  ===> typeNat
  | t_true      :       true  ===> typeBool
  | t_false     :       false ===> typeBool
  | t_succ      :       forall (t:term), t ===> typeNat -> succ t ===> typeNat
  | t_isZero    :       forall (t:term), t ===> typeNat -> iszero t ===> typeBool
  | t_pred      :       forall (t:term), t ===> typeNat -> pred t ===> typeNat
  | t_if        :       forall (t1 t2 t3: term), t1 ===> typeBool -> forall T:type, (t2 ===> T) -> (t3 ===> T) -> ifte t1 t2 t3 ===> T
where "A ===> B" := (check A B).


Fixpoint typecheck (t : term) : option type :=
  match t with
    | zero => Some typeNat
    | true => Some typeBool
    | false => Some typeBool
    | succ t'         => match typecheck t' with
                         | Some typeNat => Some typeNat
                         | _ => None
                         end
    | pred t'         =>  match typecheck t' with
                          | Some typeNat => Some typeNat
                          | _ => None
                          end
    | iszero t'       =>  match typecheck t' with
                          | Some typeNat => Some typeBool
                          | _ => None
                          end
    | ifte t1 t2 t3   =>  match typecheck t1, typecheck t2, typecheck t3 with
                          | Some typeBool, Some typeNat, Some typeNat => Some typeNat
                          | Some typeBool, Some typeBool, Some typeBool => Some typeBool
                          | _, _, _ => None
                          end
  end.



Theorem Progress : forall t : term, forall T : type,
  (t ===> T) -> (value t \/ (exists t', t ---> t')).

Proof.
  intros t T H. induction H.
  + left. apply numVal; apply zeroNum.
  + left. apply trueVal.
  + left. apply falseVal.
  + destruct IHcheck.
    - inversion H0.
      * subst. inversion H.
      * subst. inversion H.
      * subst. left. apply numVal; apply succNum. assumption.
    - inversion H0. right. exists (succ x). apply e_succ. assumption.
  + destruct IHcheck.
    - destruct H0.
      * inversion H.
      * inversion H.
      * right. destruct H0. exists true. apply e_iszerozero.
        exists false. apply e_iszerosucc. assumption.
    - right. inversion H0. exists (iszero x). apply e_iszero.
      assumption.
  + destruct IHcheck.
    - right. inversion H0.
      * subst. inversion H.
      * subst. inversion H.
      * subst. destruct H1. exists zero. apply e_predzero.
        exists n. apply e_predsucc. assumption.
    - inversion H0. right. exists (pred x).
      apply e_pred. assumption.
  + destruct IHcheck1.
    - inversion H2.
      * right. exists t2. apply e_iftrue.
      * right. exists t3. apply e_iffalse.
      * subst. destruct H3. inversion H. inversion H.
    - right. inversion H2. exists (ifte x t2 t3).
      apply e_if. assumption.
Qed.

Lemma nv_is_nat : forall t : term , nv t -> t ===> typeNat.
Proof.
  intros. induction H.
  - apply t_zero.
  - apply t_succ. assumption.
Qed.

Theorem Preservation : forall t : term, forall T : type , t ===> T -> 
  forall t' : term, t ---> t' -> t' ===> T.
Proof.
  intros t T H. induction H.
  - intros. inversion H.
  - intros. inversion H.
  - intros. inversion H.
  - intros. inversion H0. subst. apply IHcheck with (t':=t'0) in H2.
    apply t_succ. assumption.
  - intros. inversion H0. subst.
    + apply t_true.
    + subst. apply t_false.
    + subst. apply t_isZero. apply IHcheck in H2. assumption.
  - intros. inversion H0.
    + subst. apply t_zero.
    + subst. apply nv_is_nat in H2. assumption.
    + subst. apply t_pred. apply IHcheck in H2. assumption.
  - intros. inversion H2.
    + subst. auto.
    + subst. auto.
    + subst. pose (IHcheck1 t1' H7). apply t_if. auto.
      auto. auto.
Qed.

Fixpoint term_size (t : term) : nat :=
  match t with
  | true => 1
  | false => 1
  | zero => 1
  | succ t' => 1 + term_size t'
  | pred t' => 1 + term_size t'
  | iszero t' => 1 + term_size t'
  | ifte t1 t2 t3 => 1 + (term_size t1) + (term_size t2) + (term_size t3)
  end.

Theorem reduction : forall t t' : term ,
  t ---> t' -> term_size t > term_size t'.
Proof.
  intros. induction H.
  - simpl. destruct (term_size t2).
    + simpl. omega.
    + simpl. omega.
  - simpl. destruct (term_size t2). simpl. omega. simpl.
    omega.
  - simpl. destruct (term_size t1). simpl. omega. simpl.
    omega.
  - simpl. omega.
  - simpl. omega.
  - simpl. omega.
  - simpl. omega.
  - simpl. omega.
  - simpl. omega.
  - simpl. omega.
Qed.

Lemma Preservation' : forall t : term, forall T : type , t ===> T ->
  forall t' : term, t -*-> t' -> t' ===> T.
Proof.
  intros. induction H0. assumption.
  apply Preservation with (t:=t1) (t':=t2) in H. apply IHmultistep in H.
  assumption. assumption.
Qed.

Lemma reduction' : forall t t': term,
  t -*-> t' -> term_size t >= term_size t'.
Proof.
  intros. induction H.
  - omega.
  - apply reduction in H. omega.
Qed.

Lemma finalValues : forall t : term, value(t) -> forall t' : term,
  ~ (t ---> t').
Proof.
  intros. unfold not. intros.
  induction H.
  - inversion H0.
  - inversion H0.
  - induction H0.
    + inversion H.
    + inversion H.
    + inversion H.
    + inversion H. subst. apply IHstep in H2. auto.
    + inversion H.
    + inversion H.
    + inversion H.
    + inversion H.
    + inversion H.
    + inversion H.
Qed.

Lemma allValues : forall v : term, value(v) -> nv v \/ v = true \/ v = false.
  intros. induction v.
  - left. apply zeroNum.
  - left. inversion H. subst. auto.
  - right; left. auto.
  - right; right. auto.
  - right. inversion H. subst. inversion H0.
  - inversion H. subst. inversion H0.
  - inversion H. subst. inversion H0.
Qed.

Lemma l2 : forall t t', succ t ---> succ t' -> t ---> t'.
Proof.
  intros. inversion H. subst. auto.
Qed.

Theorem termination' : forall t : term, exists t' : term,
  t -*-> t' -> value(t') \/ Stuck(t').
Proof.
  intros. induction t.
  - exists zero. intros. left. apply numVal; apply zeroNum.
  - inversion IHt. exists (succ x). intros. pose (l3 (succ t) (succ x) H0 t).
    assert (succ t = succ t). auto. apply e in H1. inversion H1.
    destruct H2. inversion H2. subst. apply H in H3. destruct H3.
    + pose (classic (nv x0)). destruct o. left.
      apply numVal. apply succNum. auto. right. unfold Stuck.
      split.
      * unfold NF. intro. inversion H5. inversion H6. subst.
        apply finalValues with(t':= t') in H3. contradiction.
      * intro. inversion H5. subst. inversion H6. subst. auto.
    + right. unfold Stuck in *. split.
      * destruct H3. unfold NF in *. intro. inversion H5.
        inversion H6. subst. assert (exists t' : term, x0 ---> t').
        exists t'. auto. auto.
      * destruct H3. intro. inversion H5. subst. inversion H6.
        subst. assert (value x0). apply numVal. auto. auto.
  - exists true. intros. left. apply trueVal.
  - exists false; intros; left; apply falseVal.
  - pose (classic (exists x, ((t -*-> x) /\ (nv x)))).
    destruct o.
    + inversion H. destruct H0. inversion H1. subst. exists true.
      intros. left. apply trueVal.
      subst. exists false. intros. left. apply falseVal.
    + pose not_ex_all_not. pose (n term (fun x => (t -*-> x) /\ nv x) H).
      inversion IHt. pose (n0 x). simpl in n1. apply not_and_or in n1.
      destruct n1.
      * 
Theorem termination : forall t : term, ~ Diverge(t).
Proof.
  intros. unfold not. intros. in



































































