# Sobre alguns artigos interessantes

## A Static Cost Analysis for a Higher-order Language

Análise de custo automática, em função do tamanho dos termos

Linguagem simples sobre inteiros e listas de inteiros, com recursão estrutural

~~~
ins (x, nil) = [x]
ins (x, y::ys) =
	if (x<=y) then x::y::ys else y::(ins (x, ys))
~~~

---------

Análise gera o custo óbvio:

`ins_c`$(0) = c_0$

`ins_c`$(n+1) = c_1 + (c_2 \vee (c_3 +$`ins_c`$(n)))$

Mas isso não é o suficiente

---------

Como usar `ins_c` para analisar `ins_sort`?

`ins_sort xs = fold ins x nil`

Definimos o *potencial* do termo

---------

O potencial representa o custo de aplicar o termo

`ins_p`$(0) = 1$

`ins_p`$(n+1) = (n+1) \vee (1 +$`ins_p`$(n))$

--------

Definimos a *complexidade* então como a tupla $(Custo, Potencial)$,
e traduzimos da linguagem alvo para uma linguagem de complexidade,
onde obtemos uma relação recursiva que representa a complexidade
da expressão.

## Mechanical program analysis

Mapeamento direto de uma *Lisp* para relações recursivas,
estas são então resolvidas usando equações de diferença,
as não qualificadas possuem soluções exatas, as qualificadas
(possuem o termo *when*) produzem expressões de performance

