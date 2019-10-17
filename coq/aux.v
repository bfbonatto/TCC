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
