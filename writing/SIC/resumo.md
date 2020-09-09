---
author: Bruno de Freitas Bonatto
title: Resumo da Apresentação do SIC
date: Setembro de 2020
---

A análise estática é a etapa do processo de compilação que visa obter informações sobre programas sem que estes sejam executados.
Essas informações, tipicamente, são usadas para guiar transformações de código com o objetivo de melhorar o desempenho do programa.
Os objetivos do nosso trabalho são: o estudo e desenvolvimento dessas técnicas de análise, especialmente análises de tempo de gasto de energia; o desenvolvimento de ferramentas para automatizar essas análises; e a verificação da corretude dessas ferramentas usando o assistente de provas Coq.
Em etapas anteriores do projeto formalizamos uma linguagem funcional simples, L1, e provamos propriedades dessa linguagem na ferramente Coq. Na etapa atual do projeto implementamos a máquina abstrata SSM1 e uma função de compilação da linguagem fonte L1 para a SSM1. Então provamos uma relação entre o tamanho do código fonte L1 para o tamanho do código compilado para SSM1, especificamente: para todo programa L1 compilado para a máquina SSM1, o código compilado será entre duas e três vezes maior que o código fonte.
