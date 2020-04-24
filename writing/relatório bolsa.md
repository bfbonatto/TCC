---
title: Relatório Parcial
date: Abril de 2020
bibliography: bib.bib
author:
	- Bruno Bonatto
---

## Introdução
Este documento descreve o progresso feito pelo aluno Bruno de Freitas Bonatto durante o período de Maio de 2019 até Abril de 2020 sob a orientação do professor Dr. Álvaro Freitas Moreira.
Durante esse período o aluno: formalizou a máquina abstrata SSM1, criada na disciplina de semântica formal para a linguagem L1, na ferramenta Coq[@CoqManual];
implementou uma função de compilação da L1 para essa máquina;
fez uma pesquisa bibliográfica sobre técnicas de análise estática de programas;
criou uma métrica básica de tamanho e tempo de execução para a linguagem L1 e para a máquina SSM1;
e participou do WEIT[@WEIT].

## Resultados
Com a formalização da SSM1 e a implementação de uma função de compilação temos agora um objeto mais concreto sobre o qual fazer análise de performance.
Para esse fim implementamos duas medidas simples de performance para a L1 e SSM1, sendo estas a contagem de transições da relação smallstep da semântica operacional e
a contagem de passos que a SSM1 faz durante sua execução.
Depois da formalização da SSM1 provamos que o tamanho do código compilado é limitado por duas vezes o tamanho do termo L1.

## WEIT
Durante os dias de 9 a 11 de Outubro de 2019 o aluno foi à Passo Fundo com apoio financeiro da FAPERGS para participar do Workshop Escola de Informática Teórica.
Nesse evento o aluno assistiu a todas as palestras oferecidas, participou dos minicursos de semântica formal, lógica fuzzy e introdução à data science.
O aluno apresentou uma versão preliminar do trabalho publicado nos anais do evento, estes podem ser encontrados no site do WEIT.

## Referências
