### Motivational Example

A classic example: a *FIFO* queue data structure implemented using two lists:

~~~{#example .haskell}
type Queue = ([Int], [Int])

enqueue :: Int -> Queue -> Queue
enqueue a (back, front) = (a:back, front)

dequeue :: Queue -> Maybe (Queue, Int)
dequeue ([],[]) = Nothing
dequeue (back, f:fs) = Just ((back,fs), f)
dequeue (back, []) = Just (([], bs), b)
	where b:bs = reverse back
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
evaluation: $A(op(D)) = K(op(D)) + \Phi(op(D)) - \Phi(D)$.

### Analysing the example

We will discuss how to determine a valid potential function in a later section, for now we will
use $\Phi(L_{in}, L_{out}) = 2\cdot|L_{in}|$ and see if it solves our problem.

For the *enqueue* operation we have an amortized cost of:
$A(enqueue((L_{in}, L_{out}))) = 1 + 2 \cdot (|L_{in}| + 1) - 2 \cdot |L_{in}| = 3$

For the *dequeue* operation we have two distinct cases:

* For the case where $L_{out}$ is not empty we have: $A(dequeue((L_{in},L_{out}))) = 1 + 2 \cdot |L_{in}| - 2 \cdot |L_{in}|$
* For the case where $L_{out}$ is empty we have: $A(dequeue((L_{in},L_{out}))) = 1 + 2 \cdot |L_{in}| + 0 - 2 \cdot |L_{in}|$


### Towards Automation
