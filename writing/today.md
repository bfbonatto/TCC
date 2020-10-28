### Motivational Example

A classic example: a *FIFO* queue data structure implemented using two lists:

~~~{#example .ocaml}
let enqueue a (back, front) = (a::back, front)

let rec transfer f t = match f with
| [] -> t
| x :: xs -> transfer xs (x::t)

let reverse l = transfer l []

let dequeue q = match q with
| ([],[]) -> None
| (back, f::fs) = Some ((back, fs), f)
| (back, []) = let b::bs = reverse back in
						   Some (([], bs), b)
~~~

### The Problem

The variable cost of the *dequeue* function.

### The Solution: Amortized Analysis

The idea is to, someway, assign a constant cost to the variable function.
We will use what is called the *potential* method.

Based in the idea of potential energy in physics we introduce a new function $\Phi$ called the *potential function* that can balance out the variable cost of the analysed function.

Formally speaking we assign a function $\Phi(D)$ that maps the data structure $D$ to the positive
integers, and we analyse the amortized cost $A(op(D))$ of an operation $op$ over $D$ defined as
the actual cost of the operation $K(op(D))$ and the difference in potentials before and after its
evaluation:
$$  A(op(D)) = K(op(D)) + \Phi(op(D)) - \Phi(D) $$.

### Analysing the example

We will discuss how to determine a valid potential function in a later section, for now we will
use $\Phi(L_{in}, L_{out}) = 2\cdot|L_{in}|$ and see if it solves our problem.

For the *enqueue* operation we have an amortized cost of:
$A(enqueue((L_{in}, L_{out}))) = 1 + 2 \cdot (|L_{in}| + 1) - 2 \cdot |L_{in}| = 3$

For the *dequeue* operation we have two distinct cases:

* For the case where $L_{out}$ is not empty we have: $A(dequeue((L_{in},L_{out}))) = 1 + 2 \cdot |L_{in}| - 2 \cdot |L_{in}|$
* For the case where $L_{out}$ is empty we have: $A(dequeue((L_{in},L_{out}))) = 1 + 2 \cdot |L_{in}| + 0 - 2 \cdot |L_{in}|$


## Towards Automation

### How can we _algorithmically_ determine a potential function?

Hoffman's answer was to augment the type system with performance information and use the
type inference function to collect that information and feed it into some procedure that
could calculate a potential function.

### Resource-Aware Semantics

Before we begin our discussion of the new type system we must take a slight detour, into a modified Big-step
operational semantics capable of expressing the use of machine resources during execution.


### Linear Potential

In order to automatize the amortized analysis we must choose a set of potential functions,
at this time we will only use functions linear in relation to its input, and represent
them in the type system.

$$ A ::= unit | bool | int | L^{q}(A) | T^{q}(A) | (A,A) $$
$$ \Phi(a:A) = 0, A \in \{int, bool, unit\} $$
$$ \Phi(a:(A_1, A_2)) = \Phi(a_1:A_1) + \Phi(a_2:A_2) $$
$$ \Phi(l:L^q(B))) = q\cdot n + \sum_{i=1,..,n}{\Phi(a_i:B)} $$
$$ \Phi(t:T^q(B)) = q\cdot n + \sum_{i=1,..,n}{\Phi(a_i:B)} $$

### Typing Rules
A typing context for annotated types is a $\Gamma:$VID$\rightarrow A$ and the _linear resource annotated first-order types_ are:
$F::= A$  $\overrightarrow{q/q'}$  $A$, where $q, q'$ are non-zero positive rationals. A _resource-annotated signature_
$\Sigma$ is a finite, partial, mapping of function identifiers to _non-empty sets_ of resource-annotated types.
As a result a _resource-annotated typing judgement_ takes the form of:
$$ \Sigma;\Gamma\vdash^{q}_{q'} e:A $$

meaning that if there are more than $q+\Phi(\Gamma)$ resources available, where $\Phi(\Gamma) = \sum_{x\in\text{dom}}{\Phi_{H}(V(x);\Gamma(x))}$, then
there will be more than $q'+\Phi(v:A)$ if $e$ evaluates to $v$.

### Typing Rules

![Linear resource-annotated type rules (1 of 2)](rules1.png "Linear resource-annotated type rules (1 of 2)")

### Typing Rules

![Linear resource-annotated type rules (2 of 2)](rules2.png "Linear resource-annotated type rules (2 of 2)")

### Type Inference - how to collect resource information

Because we have annotated the language types with resource information we just have to retrieve them during
the execution of a normal type inference algorithm and send the resulting inequalities into a
linear programming solver.

![Augmented type rules](rules3.png "augmented rules")


### An example

~~~{#example2 .ocaml}
last(acc, l) = match l with
	| nil -> acc
	| x :: xs -> last(x,xs)
~~~

![Derivation](derivation.png "Derivation")

### An example

The resulting inference is:

![Inference](inference.png "Inference")
