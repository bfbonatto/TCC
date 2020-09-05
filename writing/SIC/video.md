---
author:
	- Bruno Bonatto
	- Álvaro Moreira
	- Rodrigo Machado
title: Estudando análise estática de programas com Coq
date: Setembro de 2020
---

## Objetivo do trabalho

- Estudar análise estática de programas
- Criar ferramentas para análise
- Verificar formalmente, usando Coq, essas análises

::: notes
O objetivo deste trabalho é o estudo e desenvolvimento dessas técnicas de análise, especialmente análises de tempo de gasto de energia, a criação de ferramentas para executar essas análises e a verificação formal dessa análise usando a ferramenta Coq.
:::

## Etapas anteriores

- Formalização da L1
- Prova da segurança da linguagem, preservação e progresso

::: notes
Em etapas anteriores do projeto formalizamos a L1, uma linguagem funcional, no assistente de provas Coq e provamos algumas propriedades dessa linguagem.
:::

## Análise Estática

É uma etapa do processo de compilação que visa obter informações sobre programas sem que estes sejam executados.

Usadas para guiar transformações de código com o objetivo de melhorar o desempenho de programas.

### Exemplo: RaML

- Ferramenta de análise estática para programas OCAML
- Várias métricas de análise possíveis
	- Passos de avaliação
	- Espaço de *heap*
	- Ciclos


::: notes
Um exemplo de uso de técnicas de análise estática que estudamos durante o projeto é a ferramenta RaML, ou *Resource Aware ML*.

Essa ferramenta analisa programas escritos na linguagem OCAML e para várias métricas como tempo de execução ou espaço de memória usado, se para a métrica analisada o programa tem um custo polinomial a ferramenta obtém *bounds* superiores precisos do programa.
:::

## RaML

![raml](Untitled.png){ height=90% }


## Formalização SSM1

- Baseada na SECD
- Definida em Coq

::: notes
Durante essa nova etapa do projeto implementamos a máquina abstrata SSM1 desenvolvida na cadeira de semântica formal da UFRGS, que é baseada na máquina SECD, na linguagem COQ.
:::

## Formalização SSM1

~~~
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
  | RFUN : ident -> ident -> list Instruction
	-> Instruction
  | APPLY : Instruction.
~~~

## Formalização SSM1

~~~
Inductive StorableValue : Type :=
  | st_int : int -> StorableValue
  | st_bool : bool -> StorableValue
  | st_clos : Environment -> ident -> list Instruction
	-> StorableValue
  | st_rec_clos : Environment -> ident -> ident
	-> list Instruction -> StorableValue
  with Environment : Type :=
  | env : (lookup_list StorableValue) -> Environment.

Definition Code := list Instruction.
Definition Stack := list StorableValue.
Definition Dump := list (Code * Stack * Environment).
Definition State : Type :=
	(Code * Stack * Environment * Dump).
~~~

## Compilação

~~~
Fixpoint compile (t : term) : Code :=
match t with
  | t_num n =>  [[INT n]]
  | t_bool b =>  [[BOOL b]]
  | t_op t1 (op_arith _) t2 =>  (( (compile t1))
	++ ( (compile t2)) ++ [[ ADD ]])
  ...
~~~

::: notes
Também implementamos a função de compilação da linguagem fonte L1 para a máquina SSM1.
:::

## Relação de Tamanho

Definimos e provamos uma relação de tamanho

::: notes
Com a máquina SSM1 formalizada e uma função de compilação definida, criamos e provamos uma relação formal entre o tamanho do código fonte em L1 para o tamanho do código compilado para SSM1, uma primeira análise estática.
:::

~~~
Theorem length_relation :
  forall t, (code_size (compile t)) < 3 * (term_size t).
~~~

## Próximos passos

Prova de uma relação de custo

::: notes
Estamos agora no processo de provar uma relação entre o número de passos da semântica *smallstep* L1 e o número de ciclos da maquina SSM1 para programas sem recursão.
:::

~~~
Theorem cost_relation : forall t n m t' c',
  ~ term_has_recursion t ->
  multi_cost_language t n t' ->
  value t' ->
  multi_cost_code (initial_state (compile t)) m c' ->
  state_value c' ->
  m <= 10*n + 10.
~~~

# Obrigado pela atenção

## Patrocínio

![inf logo](Identidade Visual INF UFRGS.png){ height=40% width=40% }
![fapergs logo](Identidade Visual FAPERGS.png){ height=40% width=40% }
