---
author: Bruno Bonatto
title: Documentation of Implementation Decisions
---

# Introduction
Because the SSM1 is not a physical machine some important details are abstracted by the
operational semantics, most of which are essential for the correct estimation of the
cost of running a program in the machine.

This document aims to identify those abstractions and determine the actual cost of
running a program on a physical version of the SSM1 machine.

# Abstractions
- The cost for pushing a value to a stack is 1
- The cost for popping a value from a stack is 1
- The cost for copying a value is 0
- The machine has pointers
- Stacks and lists are implemented using pointers
- The cost for pushing a list to a stack is 1
- The cost for popping a list from a stack is 1
- All copies are shallow
- Because every instruction has at least the cost of popping its op code from the code stack
	we disregard it

# Costs
- INT has cost 1
	+ pushing into S: 1
- BOOL has cost 1
	- pushing into S: 1
- POP has cost 1
	+ popping S: 1
- COPY has cost 1
	+ copying: 0
	+ pushing into S: 1

# Costs
- ADD has cost 4
	+ popping the two values: 2
	+ adding: 1
	+ pushing the result: 1
- EQ has cost 4
	+ popping the two values: 2
	+ comparing: 1
	+ pushing the result: 1
- GT and AND are the same
- NOT has cost 3
	+ popping *one* value: 1
	+ negating it: 1
	+ pushing the result: 1

# Costs
Assuming that a jump can occur, that the length of the list of
instructions is at least $n+1$

- JUMP n has cost $n$
	+ popping n instructions from C
- JUMPIFTRUE n has cost $n+2$, if the value is true
	+ popping from S: 1
	+ testing the value: 1
	+ popping n instructions from C: n
- JUMPIFTRUE n has cost $2$
	+ popping from S: 1
	+ testing the value: 1

# Costs
- VAR x has cost $m+1$
	+ assuming that $x \in e$
	+ assuming that e has length $m$
	+ looking up x in e: $m$
	+ pushing the value of x into S: 1
- FUN x c' has cost $m+1$
	+ assuming that e has length $m$
	+ copying the environment: $m$
	+ pushing the closure into S: 1
- RFUN f x c' has cost $m+1$
	+ assuming that e has length $m$
	+ copying the environment: $m$
	+ pushing the closure into S: 1

# Costs
The APPLY instruction has two possible costs depending on if the closure is recursive
or not

- Non-recursive APPLY has cost $c+s+e+3$
	+ popping the closure: 1
	+ copying C: $c$
	+ copying S: $s$
	+ copying e: $e$
	+ pushing into d: 1
	+ updating e': 1
- Recursive APPLY has cost $c+s+e+4$
	+ popping the closure: 1
	+ copying C: $c$
	+ copying S: $s$
	+ copying e: $e$
	+ pushing into d: 1
	+ updating e' twice: 2

# Costs
- The cost of returning from a function is $5$
	+ moving c': 1
	+ moving s': 1
	+ moving e': 1
	+ popping d: 1
	+ pushing into s': 1
