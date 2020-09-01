
---
title: Relatório Parcial
date: Maio de 2019
bibliography: bibliography.bib
author:
	- Bruno Bonatto
---

## Introdução
Este documento tem por objetivo resumir as atividades completadas pelo aluno Bruno de Freitas Bonatto no período de fevereiro de 2019 até maio de 2019 sob a orientação do professor Dr. Álvaro Freitas Moreira. Durante o trabalho o bolsista formalizou as linguagens L0 e L1, duas linguagens de programação funcionais desenvolvidas para a disciplina de Semântica Formal na ferramenta Coq[@CoqManual]. Para isso foi necessário que o bolsista se familiarizar com a ferramenta e com técnicas de formalização, para isso foi utilizado como material de referência o livro *Programming Languages Foundations*[@Pierce]

## Atividades Completadas


### Formalização L0
No processo de formalizar a linguagem L0 foi decidido implementar a semântica operacional no estilo *small-step* com sistema de tipos como uma relação binária, seguindo o padrão da ferramenta; para a linguagem foram provadas as propriedades principais de *Progresso* e *Preservação*. Usando essas propriedades foi possível provar uma versão mais forte do teorema da preservação, que garante a preservação de tipos para todos os termos derivados, e, com o uso de uma definição de tamanho de termos, a prova de terminação da linguagem.

### Formalização L1
Para formalizar a linguagem L1 também foi implementada a semântica operacional *small-step* como relação, devido a maior complexidade da linguagem foi necessária a definição de um ambiente de tipos, este foi implementado como uma função parcial de identificadores para tipos, seguindo o exemplo de Pierce. Para implementar a operação de substituição de variáveis foi decidido utilizar uma função *fixpoint* ao invés de uma relação pois, para esta linguagem, não são relevantes os passos da substituição de variáveis. Para a linguagem L1 também foram provadas as propriedades de *Progresso* e *Preservação*, para a *Preservação* foi necessário provar o *lema da substituição*, que garante que a substituição de variáveis não altera o tipo de um termo, esse lema foi definido e provado em termos de variáveis livres, como no livro de Pierce. Como a L1 permite a definição de funções recursivas arbitrárias não é possível provar a terminação da linguagem.

## Referências
