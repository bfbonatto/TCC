
---
author: Bruno de Freitas Bonatto
title: Estudando análise estática de programas com Coq
date: Setembro de 2020
---


# Objetivo do trabalho

O objetivo deste trabalho é o estudo e desenvolvimento dessas técnicas de análise, especialmente análises de tempo de gasto de energia, a criação de ferramentas para executar essas análises e a verificação formal dessa análise usando a ferramenta Coq.

# Etapas anteriores

Em etapas anteriores do projeto formalizamos a L1, uma linguagem funcional, no assistente de provas Coq[@CoqManual] e provamos algumas propriedades dessa linguagem.

# Análise Estática

A análise estática é a etapa do processo de compilação que visa obter informações sobre programas sem que estes sejam executados.

Essas informações, tipicamente, são usadas para guiar transformações com o objetivo de melhorar o desempenho de programas.

## Exemplo: RaML

Um exemplo de uso de técnicas de análise estática que estudamos durante o projeto é a ferramenta RaML, ou *Resource Aware ML*.

Essa ferramenta analisa programas escritos na linguagem OCAML e para várias métricas como tempo de execução ou espaço de memória usado, se para a métrica analisada o programa tem um custo polinomial a ferramenta obtém *bounds* superiores precisos do programa.


# Formalização SSM1

Durante essa nova etapa do projeto implementamos a máquina abstrata SSM1 desenvolvida na cadeira de semântica formal da UFRGS, que é baseada na máquina SECD, na linguagem COQ.

# Compilação

Também implementamos a função de compilação da linguagem fonte L1 para a máquina SSM1.

# Relação de Tamanho

Com a máquina SSM1 formalizada e uma função de compilação definida, criamos e provamos uma relação formal entre o tamanho do código fonte em L1 para o tamanho do código compilado para SSM1, uma primeira análise estática.

# Próximos passos

Estamos agora no processo de definir uma relação entre o número de passos da semântica *smallstep* L1 e o número de ciclos da maquina SSM1 para programas sem recursão.
