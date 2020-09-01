---
title: Relatório Parcial
date: Abril de 2020
bibliography: bib.bib
author:
	- Bruno Bonatto
---

## Introdução

A análise estática é a etapa do processo de compilação que visa obter informações sobre programas sem que estes sejam executados.
Essas informações, tipicamente, são usadas para guiar transformações com o objetivo de melhorar o desempenho de programas.
O objetivo deste trabalho é o estudo e desenvolvimento dessas técnicas de análise, especialmente análises de tempo de gasto de energia.

Em etapas anteriores do projeto formalizamos a L1, uma linguagem funcional, no assistente de provas Coq[@CoqManual] e provamos algumas propriedades dessa linguagem.
Para essa etapa do projeto tínhamos planejado uma maior pesquisa sobre o análise estática, formalizar a máquina abstrata SSM1, que executa código compilado da L1, em Coq e
a implementação dessa função de compilação. Durante esse período da bolsa concluímos todos os objetivos, o texto a seguir detalha os resultados obtidos.

## Resultados

### Formalização SSM1

A máquina abstrata SSM1 foi criada na cadeira de Semântica Formal na UFRGS como exemplo de máquina abstrata, baseada na máquina SECD[@Landin] ela
permite a execução de código compilado da linguagem L1 de forma assemelhada à código executável de outras linguagens.
A formalização da SSM1 nos permite provar propriedades sobre a execução de código L1 e sobre seu comportamento.

### Compilação

A função de compilação de código L1 para código executável SSM1 é bem definida nas notas de aula da cadeira de Semântica Formal,
com a implementação dela em Coq podemos utilizá-la em provas e provar a sua corretude.


### Publicações

Durante este período da bolsa participamos do Workshop Escola de Informática Teórica 2019[@WEIT] em Passo Fundo,
com uma versão preliminar do trabalho sendo publicada nos anais da conferência.
E apresentamos nosso progresso no Salão de Iniciação Cientifica da UFRGS.

## Referências
