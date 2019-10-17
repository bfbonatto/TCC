(* Bibliotecas importadas *)
Require Import Arith ZArith Znat List Classical_Prop.
Require Import Coq.Setoids.Setoid.

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


(*****************************************************************)
(*          Propriedades relacionando  --->  e  -*->             *)
(*****************************************************************)


(* Inclus\u00e3o de ---> em -*-> *)
Theorem m_inc :

  forall t1 t2,   t1 ---> t2   ->   t1 -*-> t2. 

Proof.
  Hint Constructors multistep.
  intros. apply m_cons with (t2:=t2); auto.
Qed.


(* Transitividade de -*-> *)
Theorem m_trans :

  forall t1 t2 t3,   t1 -*-> t2   ->   t2 -*-> t3   ->   t1 -*-> t3.

Proof.
  Hint Constructors multistep.
  intros. induction H; auto; subst. pose (IHmultistep H0).
  apply m_cons with (t2 := t2); auto.
Qed. 



(* rela\u00e7\u00e3o -*-> sob succ *)
Lemma m_succ : 

  forall t1 t2,   t1 -*-> t2   ->   succ(t1) -*-> succ(t2).

Proof. 
  intros. induction H. apply m_refl. assert (succ t1 ---> succ t2).
  apply e_succ. auto. apply m_cons with (t2:=succ t2). auto. auto.
Qed.




(* rela\u00e7\u00e3o -*-> sob pred *)
Lemma m_pred : 

  forall t1 t2,   t1 -*-> t2   ->   pred(t1) -*-> pred(t2).

Proof. 
  intros. induction H. apply m_refl. assert (pred t1 ---> pred t2).
  apply e_pred. auto. apply m_cons with (t2:=pred t2). auto. auto.
Qed.



(* rela\u00e7\u00e3o -*-> sob iszero *) 
Lemma m_iszero : 

  forall t1 t2,   t1 -*-> t2   ->   iszero(t1) -*-> iszero(t2).

Proof. 
  intros. induction H. apply m_refl. assert (iszero t1 ---> iszero t2).
  apply e_iszero. auto. apply m_cons with (t2:=iszero t2). auto. auto.
Qed.



(* rela\u00e7\u00e3o -*-> sob if-then-else *)  
Lemma m_ifte : 

  forall t1 t1' t2 t3,   t1 -*-> t1'   ->   ifte t1 t2 t3 -*-> ifte t1' t2 t3.

Proof. 
  intros. induction H. apply m_refl. assert (ifte t1 t2 t3 ---> ifte t0 t2 t3).
  apply e_if. auto. apply m_cons with (t2:=ifte t0 t2 t3). auto. auto.
Qed.




(*****************************************************************)
(*             Propriedades da sem\u00e2ntica small-step              *)
(*****************************************************************)


(* Todo valor num\u00e9rico \u00e9 formal normal *)

Theorem nv_NF : 

  forall (t:term), nv t -> NF t.

Proof.
  intro. intro. induction H. intro. inversion H. inversion H0. intro. 
  inversion H0. inversion H1. subst. apply ex_intro with (x:=t') in H3. 
  contradiction.
Qed.


(* Todo valor \u00e9 formal normal *)

Theorem value_NF : 

  forall (t:term), value t -> NF t. 

Proof. 
  intros. induction H. intro. inversion H. inversion H0. intro. 
  inversion H. inversion H0. intro. apply nv_NF in H. contradiction.
Qed.


(* Sem\u00e2ntica small-step \u00e9 determin\u00edstica *)

Theorem determinismo : 

  forall t t1 t2,   t ---> t1   ->   t ---> t2   ->   t1 = t2.

Proof.
  induction t. intros. inversion H. intros. inversion H. subst. 
  intros. inversion H. inversion H0. subst. apply f_equal. apply IHt. auto. auto.
  intros. inversion H. intros. inversion H. intros. inversion H. inversion H0.
  subst. auto. subst. inversion H3. subst. inversion H4. subst.  
  apply nv_NF in H2. inversion H0. auto. subst. inversion H3. subst. 
  apply ex_intro with (x:=t'0) in H4. contradiction. auto.
  subst. inversion H0. subst. inversion H2. subst. 
  apply nv_NF in H3. inversion H2. subst. apply ex_intro with (x:=t'0) in H4. contradiction. auto.
  subst. apply f_equal. apply IHt. auto. auto. 
  intros. inversion H. inversion H0. subst. auto. subst. inversion H3. subst.  inversion H4.
  subst.  inversion H0. subst. auto. subst.  inversion H3. subst.  
  apply ex_intro with (x:=t'0) in H4. apply nv_NF in H2. contradiction. auto.
  subst. inversion H0. subst. inversion H2. subst. inversion H2. subst.  
  apply ex_intro with (x:=t'0) in H4. apply nv_NF in H3. contradiction. auto.
  subst. apply f_equal. apply IHt. auto. auto.
  intros. inversion H. subst. inversion H0. subst. auto. subst. inversion H5. subst. 
  inversion H0. subst.  auto. subst. inversion H5. subst. 
  inversion H0.  subst. inversion H5. subst. inversion H5. subst. 
  assert (t1'=t1'0). apply IHt1. auto. auto. subst. auto.
Qed.






(*****************************************************************)
(*                    Sistema de tipos                           *)
(*****************************************************************)


Inductive type := 
 | tnat  : type
 | tbool : type.



Reserved Notation "|- A :_ B" (at level 90, no associativity). 
Inductive hasType : term -> type -> Prop :=
 | t_true       :                                         |- true          :_ tbool
 | t_false      :                                         |- false         :_ tbool
 | t_zero       :                                         |- zero          :_ tnat
 | t_if         : forall t1 t2 t3 T, |- t1 :_ tbool -> 
                                     |- t2 :_ T     -> 
                                     |- t3 :_ T     ->   |- ifte t1 t2 t3 :_ T
 | t_succ       : forall t,          |- t  :_ tnat  ->   |- succ t        :_ tnat
 | t_pred       : forall t,          |- t  :_ tnat  ->   |- pred t        :_ tnat
 | t_iszero     : forall t,          |- t  :_ tnat  ->   |- iszero t      :_ tbool
where "|- A :_ B" := (hasType A B).
 


(*****************************************************************)
(*          Propriedades do sistema de tipos                     *)
(*****************************************************************)

Theorem unicidade_de_tipos : 

  forall t T1 T2,   |- t :_ T1   ->   |- t :_ T2   ->   T1 = T2.

Proof.
Hint Constructors step.
Hint Constructors hasType.
Hint Constructors value.
Hint Constructors nv.
  intros. induction H; try (inversion H0; auto).
Qed.


Lemma natIsNv: forall t, value(t) -> |- t :_ tnat -> nv t.
Hint Constructors step.
Hint Constructors hasType.
Hint Constructors value.
Hint Constructors nv.
Proof.
  intros. induction H; auto; inversion H0.
Qed.

Theorem progresso : 

  forall t T,   |- t :_ T   ->   (value t \/ exists t', t ---> t').  

Proof.
Hint Constructors step.
Hint Constructors hasType.
Hint Constructors value.
Hint Constructors nv.
  intros. induction H; auto.
  - right. inversion IHhasType1; inversion H2; subst.
    + exists t2. auto.
    + exists t3. auto.
    + inversion H; subst; inversion H3.
    + exists (ifte x t2 t3). auto.
  - inversion IHhasType; subst.
    + left. apply numVal. apply succNum. apply natIsNv; auto.
    + inversion H0. right. exists (succ x). auto.
  - right. inversion IHhasType. pose (natIsNv t H0 H). inversion n; subst.
    + exists zero; auto.
    + exists n0; auto.
    + inversion H0. exists (pred x); auto.
  - inversion IHhasType.
    + apply natIsNv in H; auto. inversion H; subst.
      * right. exists true; auto.
      * right. exists false; auto.
    + right. inversion H0. exists (iszero x); auto.
Qed.


Theorem preservacao : 

  forall t t',   t ---> t'   ->   forall T,   |- t :_ T   ->   |- t' :_ T.

Hint Constructors step.
Hint Constructors hasType.
Hint Constructors value.
Hint Constructors nv.

Proof.
  intros. generalize dependent T. induction H; intros; inversion H0; auto.
  subst. inversion H2; auto.
Qed.

Lemma presos_sao_maltipados: 

  forall t,   Stuck(t)   ->   forall T,   not (|- t :_ T).

Proof.
  intros. intro. pose H0. apply progresso in h. destruct h.
  destruct H. contradiction. destruct H. unfold NF in H. contradiction. 
Qed. 


Theorem seguranca : 

  forall t T,   hasType t T   ->   not (Error t).

Proof.
  intros. intro. unfold Error in H0. inversion H0. destruct H1. induction H1. 
  assert (~ |- t:_T). apply presos_sao_maltipados. auto. contradiction. 
  assert (|- t2 :_ T). apply preservacao with (t:=t1). auto. auto. 
  apply IHmultistep.  auto. exists t3. split. auto. auto. auto. 
Qed.







(*****************************************************************)
(*              Algoritmo de Infer\u00eancia de Tipos                 *)
(*****************************************************************)


Fixpoint typeEq (b1 b2:type) := 
match b1 with
| tnat => match b2 with
          | tnat  => Datatypes.true
          | tbool => Datatypes.false
          end
| tbool => match b2 with
          | tnat  => Datatypes.false
          | tbool => Datatypes.true
          end
end.


Fixpoint typeInfer (t:term) : option type :=
match t with 
  | true   =>  Some tbool
  | false  =>  Some tbool
  | zero   =>  Some tnat
  | ifte t1 t2 t3 => match typeInfer t1 with
                     | Some tbool => match (typeInfer t2,typeInfer t3) with
                                     | (Some a2,Some a3) => if typeEq a2 a3 then Some a2 else None
                                     | _                 => None
                                     end
                     | _          => None
                     end
  | succ t1   => match typeInfer t1 with
                 | Some tnat => Some tnat
                 | _         => None
                 end
  | pred t1   => match typeInfer t1 with
                 | Some tnat => Some tnat
                 | _         => None
                 end
  | iszero t1 => match typeInfer t1 with
                 | Some tnat => Some tbool
                 | _         => None
                 end
end.


(*****************************************************************)
(*                 Corretude de typeInfer                        *)
(*****************************************************************)

Lemma typeEq_true :

  forall b1 b2, typeEq b1 b2 = Datatypes.true <-> b1=b2.

Proof.
intros. split.
intros. destruct b1. destruct b2. auto. inversion H. destruct b2. inversion H. auto.
intros. destruct b1. destruct b2. auto. inversion H. destruct b2. inversion H. auto.
Qed.

Lemma typeEq_false :

  forall b1 b2, typeEq b1 b2 = Datatypes.false <-> (b1<>b2).

Proof.
intros. split.
intros. destruct b1. destruct b2. inversion H. discriminate. destruct b2. discriminate. inversion H.
intros. destruct b1. destruct b2. assert (tnat=tnat). auto. contradiction. simpl. auto.
destruct b2.  simpl. auto. assert (tbool=tbool). auto. contradiction.
Qed.
  

Lemma typeInfer_sound :

  forall t T, typeInfer t = Some T -> |- t :_ T.

Proof.
induction t.
intros. simpl in H. inversion H. apply t_zero.
intros. simpl in H.
  destruct (typeInfer t). destruct t0. inversion H. subst. apply t_succ. apply IHt. auto. 
  inversion H. inversion H. 
intros. simpl in H. inversion H. apply t_true.
intros. simpl in H. inversion H. apply t_false.
intros. inversion H. destruct (typeInfer t). destruct t0. inversion H1. subst.
  apply t_iszero. apply IHt. auto. inversion H1. inversion H1.
intros. inversion H. destruct (typeInfer t). destruct t0. inversion H1. subst.
  apply t_pred. apply IHt. auto. inversion H1. inversion H1.
intros. 
  apply t_if. apply IHt1. inversion H. destruct (typeInfer t1). destruct t. inversion H1.
  destruct (typeInfer t2). destruct (typeInfer t3). destruct (typeEq t t0). auto. auto. auto. auto. inversion H1.
  inversion H.  destruct (typeInfer t1). destruct t. inversion H1.
  destruct (typeInfer t2). destruct (typeInfer t3). destruct (typeEq t t0). apply IHt2. auto. inversion H1. inversion H1. inversion H1. inversion H1.
  inversion H. destruct (typeInfer t1). destruct t. inversion H1.
  destruct (typeInfer t2). destruct (typeInfer t3). case_eq (typeEq t t0).
  intros. apply typeEq_true in H0. subst.  apply IHt3. destruct (typeEq t0 t0). auto. inversion H1.
  intros. rewrite H0 in H1. inversion H1. inversion H1. inversion H1. inversion H1. 
Qed. 


Lemma typeInfer_complete :

  forall t T,  |- t :_ T  ->  typeInfer t = Some T.

Proof.
intro. intro. intro. 
induction H. 
simpl. auto.
simpl. auto.
simpl. auto.
simpl. rewrite IHhasType1. rewrite IHhasType2. rewrite IHhasType3.
assert (typeEq T T = Datatypes.true). apply typeEq_true. auto. 
rewrite H2. auto.
simpl. rewrite IHhasType. auto.
simpl. rewrite IHhasType. auto.
simpl. rewrite IHhasType. auto. 
Qed. 


Theorem typeInfer_correct:

  forall t T,  typeInfer t = Some T <-> |- t :_ T.

Proof. 
intros. split. 
intros. apply typeInfer_sound. auto.
intros. apply typeInfer_complete. auto.
Qed.
  







(*****************************************************************)
(*              Sem\u00e2ntica operacional big-step                   *)
(*****************************************************************)


Reserved Notation "A ===> B" (at level 90, no associativity).
Inductive natsem : term -> term -> Prop :=
 | b_value      : forall t,            value(t)       ->              t ===> t
 | b_iftrue     : forall t1 t2 t3 v2,  value(v2)      -> 
                                       t1 ===> true   -> 
                                       t2 ===> v2     ->  ifte t1 t2 t3 ===> v2
 | b_iffalse    : forall t1 t2 t3 v3,  value(v3)      -> 
                                       t1 ===> false  -> 
                                       t3 ===> v3     ->  ifte t1 t2 t3 ===> v3
 | b_succ       : forall t v, nv v  -> t ===> v       ->  succ t        ===> succ v
 | b_predzero   : forall t,            t ===> zero    ->  pred t        ===> zero
 | b_predsucc   : forall t v, nv v  -> t ===> succ v  ->  pred t        ===> v
 | b_iszerozero : forall t,            t ===> zero    ->  iszero t      ===> true
 | b_iszerosucc : forall t v, nv v  -> t ===> succ v  ->  iszero t      ===> false
where "A ===> B" := (natsem A B).




(*****************************************************************)
(*     Propriedades relacionando small-step e big-step           *)
(*****************************************************************)


Lemma num_natsem : 

  forall t1, nv t1 -> forall t2,  t1 ===> t2  ->  t1 = t2.

Proof.
  intro. intro. induction H.
  intros. inversion H. subst.  auto.
  intros. inversion H0.  subst. auto.
  subst. apply f_equal. apply IHnv. auto.
Qed.


Lemma value_natsem : 

  forall t1, value t1 -> forall t2,  t1 ===> t2  ->  t1 = t2.

Proof.
  intro. intro. intro. induction H.
  intros. inversion H. subst. auto.
  intros. inversion H. subst. auto.
  intro. apply num_natsem. auto. auto.
Qed.


Theorem step_natsem :

  forall t v, value(v)   ->   t ---> v  ->  t ===> v.
Hint Constructors step.
Hint Constructors hasType.
Hint Constructors value.
Hint Constructors nv.
Hint Constructors natsem.
Proof with auto.
  intros. induction H.
  - inversion H0; auto.
  - inversion H0; auto.
    subst. apply b_iszerosucc with (v:=t0); auto.
  - 



intro. intro. intro. intro.
induction H0.
  apply b_iftrue.  auto. apply b_value. apply trueVal. apply b_value. auto.
  apply b_iffalse. auto. apply b_value. apply falseVal. apply b_value. auto.
  inversion H. subst. inversion H1.
  inversion H. subst. inversion H1. subst. auto.  assert (value t'). apply numVal. auto.
  apply b_succ. auto. apply IHstep. auto.
  apply b_predzero. apply b_value. auto.
  apply b_predsucc.  auto.
  assert (nv (succ t)). apply succNum. auto. assert (value (succ t)). apply numVal. auto. 
  apply b_value. auto. inversion H. subst. inversion H1.
  apply b_iszerozero. apply b_value. apply numVal. apply zeroNum.
  apply b_iszerosucc with (v:=t). auto. 
  assert (nv (succ t)). apply succNum. auto.
  assert (value (succ t)). apply numVal. auto.
  apply b_succ. auto. apply b_value. auto. apply numVal. auto. 
  inversion H. subst. inversion H1.
Qed.


Theorem backstep_natsem :

  forall t1 t2 v,  value(v) ->  t1 ---> t2  ->   t2 ===> v  ->  t1 ===> v.

Proof.
  induction t1. intros. inversion H0. intros. inversion H0. subst. inversion H1. subst. 
  inversion H. subst. inversion H4. subst. apply b_succ. auto. apply step_natsem. apply numVal. auto. auto.
  subst. apply b_succ. auto. apply IHt1 with (t2:=t'). inversion H. subst. apply numVal. auto. auto. auto.
  intros. inversion H0. intros. inversion H0. intros. inversion H0. subst. inversion H1. subst. 
  apply step_natsem. auto. auto. subst. inversion H1. subst. apply step_natsem. auto. auto. subst. 
  inversion H1. subst.  inversion H. subst. inversion H4. subst. apply b_iszerozero. apply IHt1 with (t2:=t'). 
  apply numVal. apply zeroNum. auto. auto. subst. apply b_iszerosucc with (v:=v0). auto. apply IHt1 with (t2:=t'). 
  apply numVal. apply succNum. auto. auto. auto. intros. inversion H0. subst. inversion H1. subst. apply step_natsem.
  auto. auto. subst. apply b_predsucc. inversion H3. subst. inversion H1. subst. apply zeroNum. subst. inversion H1. 
  subst.  auto. subst. apply succNum. auto. assert (value t2). apply numVal. auto. assert (t2=v). apply num_natsem. 
  auto. auto. subst. apply b_value. apply numVal. apply succNum. auto. subst. inversion H1. subst. inversion H. 
  subst. inversion H4. subst. assert (t1 ===> zero).  apply IHt1 with (t2:=t'). auto. auto. auto. apply b_predzero. 
  auto. subst. assert (t1===>succ v). apply IHt1 with (t2:=t'). subst. apply numVal. apply succNum. auto. auto. auto. 
  apply b_predsucc. auto. auto. intros. inversion H0. subst. apply b_iftrue. auto. apply b_value. apply trueVal. auto.
  subst. apply b_iffalse. auto. apply b_value. apply falseVal. auto. subst. inversion H1. subst. inversion H. 
  inversion H. inversion H5. subst. assert (t1_1 ===> true). apply IHt1_1 with (t2:=t1'). apply trueVal. auto. auto.
  apply b_iftrue. auto. auto. auto. subst. assert (t1_1 ===> false). apply IHt1_1 with (t2:=t1'). apply falseVal. 
  auto. auto. apply b_iffalse. auto. auto. auto.
Qed.


Theorem multistep_natsem :

  forall t v, value(v) ->  t -*-> v  ->  t ===> v.

Proof. 
  intro. intro. intro. intro. induction H0. apply b_value. auto. assert (t2===>t3). 
  apply IHmultistep. auto. apply backstep_natsem with (t2:=t2). auto. auto. auto. 
Qed.


Theorem natsem_multistep :

  forall t v, value(v)  ->  t ===> v  ->  t -*-> v. 

Proof.  
  intros. induction H0. apply m_refl.
  assert (t1 -*-> true). apply IHnatsem1. apply trueVal.
  assert (t2 -*-> v2). apply IHnatsem2. auto. 
  assert (ifte t1 t2 t3 -*-> ifte true t2 t3).
  apply m_ifte. auto. 
  assert (ifte true t2 t3 ---> t2). apply e_iftrue.
  assert (ifte true t2 t3 -*-> v2). apply m_cons with (t2:=t2). auto. auto. 
  apply m_trans with (t2:=ifte true t2 t3). auto. auto. 
  assert (ifte t1 t2 t3 -*-> ifte false t2 t3).
  apply m_ifte. apply IHnatsem1. apply falseVal.
  assert (ifte false t2 t3 ---> t3). apply e_iffalse.
  assert (ifte false t2 t3 -*-> v3). apply m_cons with (t2:=t3). auto. 
  apply IHnatsem2. auto. apply m_trans with (t2:=ifte false t2 t3). 
  auto. auto. apply m_succ. apply IHnatsem. apply numVal. auto.
  assert (pred t -*-> pred zero). apply m_pred. apply IHnatsem. auto.
  assert (pred zero -*-> zero). apply m_inc. apply e_predzero.
  apply m_trans with (t2:=pred zero). auto. auto. 
  assert (t -*-> succ v). apply IHnatsem. apply numVal. apply succNum. auto. 
  assert (pred t -*-> pred (succ v)). apply m_pred. auto.  
  assert (pred (succ v) -*-> v). apply m_inc. apply e_predsucc. auto. 
  apply m_trans with (t2:=pred (succ v)). auto. auto. 
  assert (iszero t -*-> iszero zero). apply m_iszero.  apply IHnatsem.  apply numVal. apply zeroNum.  
  assert (iszero zero -*-> true). apply m_inc.  apply e_iszerozero. apply m_trans with (t2:=iszero zero).
  auto. auto. assert (iszero t -*-> iszero (succ v)). apply m_iszero.  apply IHnatsem.  apply numVal. 
  apply succNum. auto. assert (iszero (succ v) -*-> false). apply m_inc.  apply e_iszerosucc. auto.  
  apply m_trans with (t2:=iszero (succ v)). auto. auto.
Qed.  


Theorem bigstep_smallstep :

  forall t v, value(v)  ->  ( t ===> v  <->  t -*-> v ).

Proof. 
  intro. intro. intro. split. 
  intro. apply natsem_multistep. auto. auto. 
  intro. apply multistep_natsem. auto. auto.  
Qed.







(*****************************************************************)
(*                       Normaliza\u00e7\u00e3o                            *)
(*****************************************************************)


(* Tamanho de um termo *)
Fixpoint size (t:term) : nat :=
match t with
 | true          => 1
 | false         => 1
 | zero          => 1
 | succ t'       => 1 + (size t')
 | ifte t1 t2 t3 => 1 + (size t1) + (size t2) + (size t3)
 | pred t'       => 1 + (size t')
 | iszero t'     => 1 + (size t')
end.



(* Todos os tamanhos de termos s\u00e3o positivos *)
Theorem term_pos_size :

   forall t, size(t) > 0.

Proof. 
  induction t.  simpl. omega. simpl. omega. simpl. omega. 
  simpl. omega. simpl. omega. simpl. omega. simpl. omega. 
Qed.



(* Avalia\u00e7\u00e3o reduz o tamanho dos termos *)
Theorem step_reduz : 

   forall t t',  t ---> t' ->  size(t') < size(t) .

Proof.
  intros. induction H. simpl. omega. simpl. omega. simpl. 
  omega. simpl. omega. simpl. omega. simpl. omega. simpl. 
  omega. simpl. omega. simpl. omega. simpl. omega. 
Qed.


Inductive revstep (y x:term) : Prop :=
| rev1 : step x y -> revstep y x
.
Notation "Y <--- X" := (revstep Y X) (at level 70).


Theorem wf_revstep : well_founded revstep. 

Proof. 
apply well_founded_lt_compat with (f:=size).
intros. inversion H. apply step_reduz.
auto. 
Qed.  



(*
Theorem strong_normalization : forall t, not (Diverge t).
Proof. 
intros. 
intro.
unfold Diverge in H. 
... falta mostrar a contradi\u00e7\u00e3o com well founded e divergente ...
Qed.
*)




(*****************************************************************)
(*              CONTEXTOS DE AVALIA\u00c7\u00c3O                           *)
(*****************************************************************)


(* Contextos *)
Inductive ctx :=
 | hole   :   ctx
 | c_ifte :   ctx -> term -> term -> ctx
 | c_succ :   ctx -> ctx
 | c_pred :   ctx -> ctx
 | c_iszero : ctx -> ctx.


(* Substitui\u00e7\u00e3o de contextos *)
Reserved Notation "C [ E ]" (at level  5).
Fixpoint compose_ctx (ct:ctx) (t:term) : term :=
match ct with
  | hole             => t
  | (c_ifte c t2 t3) => ifte   c[t] t2 t3
  | (c_succ c)       => succ   c[t]
  | (c_pred c)       => pred   c[t]
  | (c_iszero c)     => iszero c[t]
end
where "C [ E ]" := (compose_ctx C E).


(* Sem\u00e2ntica operacional small-step com contextos de avalia\u00e7\u00e3o *)
Reserved Notation "A -c-> B" (at level 90, no associativity).
Inductive c_step : term -> term -> Prop :=
 | c_iftrue     : forall t2 t3,                    ifte true  t2 t3 -c-> t2
 | c_iffalse    : forall t2 t3,                    ifte false t2 t3 -c-> t3
 | c_predzero   :                                         pred zero -c-> zero
 | c_predsucc   : forall t,                nv t ->    pred (succ t) -c-> t
 | c_iszerozero :                                       iszero zero -c-> true
 | c_iszerosucc : forall t,                nv t ->  iszero (succ t) -c-> false
 | c_ctx        : forall ctx t t',  (t -c-> t') ->          (ctx[t] -c-> ctx[t'])
where "A -c-> B" := (c_step A B).


(* Avalia\u00e7\u00e3o em m\u00faltiplos passos com contextos *)
Reserved Notation "A -c*-> B" (at level 90, no associativity). 
Inductive c_multistep : term -> term -> Prop :=
 | cm_refl    : forall t,     t -c*-> t
 | cm_cons    : forall t1 t2 t3, (t1 -c-> t2) -> (t2 -c*-> t3) -> (t1 -c*-> t3)
where "A -c*-> B" := (c_multistep A B). 


(* Compatibilidade small-step COM e SEM contextos de avalia\u00e7\u00e3o *)
Theorem compatibilidade_contextos :

  forall t t',  t ---> t'  <->  t -c-> t'.

Proof. 
  intro. intro. split. 
  (* -> *)
  intro. induction H. apply c_iftrue. apply c_iffalse.
  assert ( (c_ifte hole t2 t3)[t1]  = ifte t1  t2 t3).
  compute. auto. assert ( (c_ifte hole t2 t3)[t1'] = ifte t1' t2 t3).
  compute. auto. rewrite <- H0. rewrite <- H1. apply c_ctx. auto.
  assert ( (c_succ hole)[t]  = succ t ). simpl. auto.
  assert ( (c_succ hole)[t'] = succ t'). simpl. auto.
  rewrite <- H0. rewrite <- H1. apply c_ctx. auto.
  apply c_predzero. apply c_predsucc. auto. 
  assert ( (c_pred hole)[t]  = pred t ). simpl. auto.
  assert ( (c_pred hole)[t'] = pred t'). simpl. auto.
  rewrite <- H0. rewrite <- H1. apply c_ctx. auto.
  apply c_iszerozero. apply c_iszerosucc. auto.
  assert ( (c_iszero hole)[t]  = iszero t ). simpl. auto.
  assert ( (c_iszero hole)[t'] = iszero t'). simpl. auto.
  rewrite <- H0. rewrite <- H1. apply c_ctx. auto. 
  (* <- *)
  intro. induction H. apply e_iftrue. apply e_iffalse.
  apply e_predzero. apply e_predsucc. auto. apply e_iszerozero.
  apply e_iszerosucc. auto. induction ctx0. simpl. auto.
  simpl. apply e_if. auto. simpl. apply e_succ. auto.
  simpl. apply e_pred. auto. simpl. apply e_iszero. auto.
Qed. 


(* Multistep sob contextos *)
Theorem multistep_contextos :

  forall c t t',  t -c*-> t'  ->  c[t] -c*-> c[t'].

Proof.
intros. induction H. apply cm_refl. assert (c[t1] -c-> c[t2]). 
apply c_ctx. auto. apply cm_cons with (t2:=c[t2]). auto. auto.
Qed.





(**************************************************************)
(***        Abstract machine specification                  ***)
(**************************************************************)


Inductive inst :=
| PUSH : Z -> inst
| POP  : inst
| COPY : inst
| INC  : inst
| DEC  : inst
| JUMP : nat -> inst
| JMPIFZERO : nat -> inst
.

(* Drop n elements from a list *)
Fixpoint drop (n:nat) (l:list inst) : list inst :=
match n with
  | O        =>  l
  | (S x)    =>  match l with
                  | nil     =>  nil
                  | (h::t)  =>  drop x t
                 end
end.


Reserved Notation "A |> B" (at level 90, no associativity).
Inductive llstep: (list inst*list Z) -> (list inst*list Z) -> Prop :=
 | l_push       : forall c s z,                       (PUSH z     ::c,        s) |> (       c,           z::s)
 | l_pop        : forall c s z,                       (POP        ::c,     z::s) |> (       c,              s)
 | l_copy       : forall c s z,                       (COPY       ::c,     z::s) |> (       c,        z::z::s)
 | l_inc        : forall c s z,                       (INC        ::c,     z::s) |> (       c, (Z.add 1 z)::s)
 | l_dec        : forall c s z,                       (DEC        ::c,     z::s) |> (       c, (Z.add (-1%Z) z)::s)
 | l_jump       : forall c s n,   (n <= length c) ->  (JUMP n     ::c,        s) |> (drop n c,              s)
 | l_jmpifzero1 : forall c s n,   (n <= length c) ->  (JMPIFZERO n::c,   0%Z::s) |> (drop n c,              s)
 | l_jmpifzero2 : forall c s n z,      (z <> 0%Z) ->  (JMPIFZERO n::c,     z::s) |> (       c,              s)
where "A |> B" := (llstep A B).



Reserved Notation "A |*> B" (at level 90, no associativity). 
Inductive llmultistep : (list inst*list Z) -> (list inst*list Z) -> Prop :=
 | l_refl    : forall s,     s |*> s
 | l_cons    : forall s1 s2 s3, (s1 |> s2) -> (s2 |*> s3) -> (s1 |*> s3)
where "A |*> B" := (llmultistep A B). 


Lemma l_include : forall s1 s2, (s1 |> s2) -> (s1 |*> s2).
Proof. 
  intros. apply l_cons with (s2:=s2). auto. apply l_refl.
Qed.


Lemma l_trans : forall s1 s2 s3, (s1 |*> s2) -> (s2 |*> s3) -> (s1 |*> s3).
Proof. 
  intro. intro. intro. intro. induction H. intro. auto.
  intro. assert (s2 |*> s3). apply IHllmultistep. auto. 
  apply l_cons with (s2:=s2). auto. auto. 
Qed.


Fixpoint compile (t:term) : (list inst) :=
match t with 
 | true            => PUSH 1%Z::nil
 | false           => PUSH 0%Z::nil
 | zero            => PUSH 0%Z::nil
 | (succ t1)       => (compile t1) ++ INC::nil
 | (ifte t1 t2 t3) => let c1 := compile t1 in
                      let c2 := compile t2 in
                      let c3 := compile t3 in
                      let n2 := length  c2 in
                      let n3 := length  c3 in
                      c1 ++ (JMPIFZERO (n2+1)::nil) ++ c2 ++ (JUMP n3::nil) ++ c3
 | (iszero t1)     => (compile t1) ++ (JMPIFZERO 2::PUSH 0::JUMP 1::PUSH 1::nil)
 | (pred   t1)     => (compile t1) ++ (COPY::JMPIFZERO 1::DEC::nil)
end.


Fixpoint rho (t:term) : Z :=
match t with
  | true     => 1%Z
  | false    => 0%Z
  | zero     => 0%Z
  | (succ n) => Z.add 1 (rho n)
  | _        => 0%Z
end.





(*************************************************************************)
(*                       CORRECT COMPILATION                             *)
(*************************************************************************)


Lemma rho_succ : 

  forall n, Z.add 1%Z (rho n)  = (rho (succ n)).

Proof. intro. simpl. auto. Qed. 


Lemma rho_notneg :

  forall t, ((rho t) >= 0)%Z. 

Proof.
induction t. 
simpl. omega.
rewrite <- rho_succ. omega. 
simpl. omega. 
simpl. omega. 
simpl. omega. 
simpl. omega. 
simpl. omega. 
Qed.


Lemma succ_rho_not_zero:

  forall t, ((1 + (rho t)) <> 0)%Z. 

Proof.
intros.
assert ((rho t) >= 0)%Z. apply rho_notneg. omega. 
Qed.  


Lemma correct_compile_nv:

  forall v, nv v -> 
        forall code stack, (compile v ++ code, stack) |*> (code, rho(v)::stack).
Proof.
  intros v H.
  induction H.
    intros. simpl. apply l_include. apply l_push.
    intros. simpl compile. rewrite app_assoc_reverse. simpl app. apply l_trans with (s2:= (INC::code,rho n::stack)). 
     apply IHnv. rewrite <- rho_succ. apply l_include.  apply l_inc. 
Qed.



Lemma drop_initial: 

  forall l1 n l2, n = length l1 -> drop n (l1++l2) = l2.
      
Proof.
induction l1.
intros. simpl. rewrite H. simpl. auto. 
intros. simpl in H. rewrite H. simpl. apply IHl1. auto.  
Qed. 



Lemma drop_initial_add: 

  forall l1 n1 n2 l2, n1 = length l1 -> drop (n1+n2) (l1++l2) = drop n2 l2.
      
Proof.
induction l1. 
intros. simpl. rewrite H. simpl. auto. 
intros. simpl in H. rewrite H. simpl. apply IHl1. auto.  
Qed. 



Theorem preservation_of_correct_evaluation:

  forall t v,   
    value v -> t ===> v ->   
    forall code stack, (compile t ++ code, stack) |*> (code, rho(v)::stack).

Proof.
intro. intro. intro. intro.  
induction H0.
  (* bvalue *)
  induction H.
  simpl. intros. apply l_include. apply l_push.
  simpl. intros. apply l_include. apply l_push.
  apply correct_compile_nv. auto.
  (* iftrue *) 
  intros. simpl compile.  rewrite app_assoc_reverse. simpl app. 
  apply l_trans with (s2:=(JMPIFZERO (length (compile t2) + 1) :: (compile t2 ++ JUMP (length (compile t3)) :: compile t3) ++ code, rho true::stack)).
  apply IHnatsem1. apply trueVal. simpl app.
  apply l_trans with 
  (s2:= (compile t2 ++ JUMP (length (compile t3)) :: compile t3 ++ code, stack)).
  apply l_include. simpl. rewrite app_assoc_reverse.    apply l_jmpifzero2. discriminate.
  apply l_trans with 
  (s2:= (JUMP (length (compile t3)) :: compile t3 ++ code, rho v2::stack)).
  apply IHnatsem2. auto. 
  apply l_trans with 
  (s2:= (drop (length (compile t3)) (compile t3 ++ code), rho v2::stack)). 
  apply l_include. apply l_jump. 
  rewrite app_length. omega. 
  rewrite drop_initial. apply l_refl. auto.  
  (* iffalse *) 
  intros. simpl compile.  rewrite app_assoc_reverse. simpl app. 
  apply l_trans with (s2:=(JMPIFZERO (length (compile t2) + 1) :: (compile t2 ++ JUMP (length (compile t3)) :: compile t3) ++ code, rho false::stack)).
  apply IHnatsem1. apply falseVal. simpl.
  simpl. rewrite app_assoc_reverse.  simpl. 
  apply l_trans with (s2:=(compile t3 ++ code,stack)).
  simpl.
  apply l_trans with (s2:=(drop (length (compile t2) + 1) (compile t2 ++ JUMP (length (compile t3)) :: compile t3 ++ code),stack)).
  apply l_include. apply l_jmpifzero1.  
  rewrite app_length. simpl. rewrite app_length. simpl. omega. 
  rewrite drop_initial_add. simpl. apply l_refl. auto. 
  apply IHnatsem2. auto.  
  (* succ *)
  intros. simpl compile. rewrite app_assoc_reverse. simpl app.
  apply l_trans with (s2:=  (INC::code, rho v :: stack)). apply IHnatsem. apply numVal. auto.
  rewrite <- rho_succ. apply l_include. apply l_inc.
  (* predzero *) 
  intros. simpl compile. 
  apply l_trans with (s2:= ((COPY :: JMPIFZERO 1 :: DEC :: nil) ++ code, rho zero::stack)).
  rewrite app_assoc_reverse. simpl. apply IHnatsem. auto. 
  simpl. 
  apply l_cons with (s2:=(JMPIFZERO 1 :: DEC :: code, 0%Z ::0%Z :: stack)).
  apply l_copy. 
  apply l_cons with (s2:=(drop 1  (DEC :: code),  0%Z :: stack)).
  apply l_jmpifzero1. simpl. omega.
  simpl. apply l_refl.
  (* predsucc *)  
  intros. 
  simpl compile. rewrite app_assoc_reverse. simpl. 
  apply l_trans with (s2:=(COPY :: JMPIFZERO 1 :: DEC :: code, rho(succ v)::stack)).
  apply IHnatsem.  apply numVal. apply succNum. auto. 
  apply l_cons with (s2:=(JMPIFZERO 1 :: DEC :: code, rho(succ v)::rho(succ v)::stack)).
  apply l_copy. rewrite <- rho_succ.  
  apply l_cons with (s2:=(DEC :: code, (1 + rho v)%Z::stack)).
  apply l_jmpifzero2. apply succ_rho_not_zero. 
  apply l_cons with (s2:=(code, (-1 + (1 + rho v))%Z::stack)).
  apply l_dec. rewrite Z.add_assoc. simpl. apply l_refl. 
  (* iszerozero *)  
  intros. simpl compile. rewrite app_assoc_reverse. simpl app.
  apply l_trans with (s2:=(JMPIFZERO 2 :: PUSH 0 :: JUMP 1 :: PUSH 1 :: code, (rho zero)::stack)).
  apply IHnatsem. apply numVal. apply zeroNum. simpl rho.
  apply l_cons with (s2:=(drop 2 (PUSH 0 :: JUMP 1 :: PUSH 1 :: code), stack)).
  apply l_jmpifzero1. simpl. omega. simpl. 
  apply l_include. 
  apply l_push.
  (* iszerosucc *)  
  intros. simpl compile. rewrite app_assoc_reverse.
  apply l_trans with (s2:=(JMPIFZERO 2 :: PUSH 0 :: JUMP 1 :: PUSH 1 :: code, (rho (succ v))::stack)).
  apply IHnatsem.  apply numVal. apply succNum. auto. 
  rewrite <-  rho_succ.
  apply l_cons with (s2:=(PUSH 0 :: JUMP 1 :: PUSH 1 :: code, stack)).
  apply l_jmpifzero2. apply succ_rho_not_zero.
  apply l_cons with (s2:=(JUMP 1 :: PUSH 1 :: code, 0%Z::stack)).
  apply l_push.
  apply l_cons with (s2:=(drop 1 (PUSH 1 :: code), 0%Z::stack)).
  apply l_jump. simpl. omega.
  simpl. apply l_refl. 
Qed. 
