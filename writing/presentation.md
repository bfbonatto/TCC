### Amortized Analysis

In order to analyse the cost of a sequence of operations on a given data structure we use
the potential method. Inspired by the concept of potential energy in physics, the idea is
to assign a function $\Phi(D)$ that maps the data structure $D$ to the positive integers.
Operations on $D$ may cause it to gain or lose potential. The amortized cost
$A(op(D))$ of an operation $op(D)$ is defined as its actual cost $K(op(D))$ and the
difference in potentials before and after its evaluation, $A(op(D)) = K(op(D)) + \Phi(op(D)) - \Phi(D)$

### Amortized Analysis

The sum of the amortized costs taken over a sequence of operations plus the potential
of the initial data structure then furnishes an upper bound for the actual cost
of that sequence

$$ \Phi(D_0) + \sum_{1 \leq i \leq n}{A(op(D_i))} = \Phi(D_0) + \sum_{1 \leq i \leq n}{K(op(D_i)) + \Phi(D_i) - \Phi(D_{i-1})} $$
$$ = \Phi(D_n) + \sum_{1 \leq i \leq n}{K(op(D_i))} \geq \sum_{1 \leq i \leq n}{K(op(D_i))} $$


### Example

The classical example for the potential method of amortized analysis is the functional queue,
implemented as two lists $L_{in}$ and $L_{out}$ acting as stacks.
Trying to determine the number of list operations required to perform a sequence of
*enqueue* and *dequeue* operations we find a problem: the cost of a *dequeue* is not constant.
Whenever $L_{out}$ is empty, we transfer elements from $L_{in}$ before removing an element.

To aid our analysis we introduce the potential $\Phi(L_{in}, L_{out}) = 2\cdot|L_{in}|$.
The amortized cost of *enqueue* is then $A(enqueue) = 3$, one to pay for the attachment
to $L_{in}$ and two to pay for the increase in potential.
The amortized cost of *dequeue* is $A(dequeue) = 1$, to see why consider the two cases:
if $L_{out}$ is not empty then we just detach the first element of $L_{out}$ and the
potential is unchanged; if $L_{out}$ is not empty then we have to move the elements in $L_{in}$ to
$L_{out}$, the actual cost is then $2 \cdot |L_{in}|$ but because $L_{in}$ is now empty
$2 \cdot |L_{in}|$ is exactly the decrease in potential.
So the amortized cost is $1$.

### Example

Finally we can conclude that given a queue with $|L_{in}|$ equal to $k$,
the number of list operations in a sequence of $m$  $enqueue$ and $n$  $dequeue$
operations is less than $3 \cdot m + n + 2\cdot k$

### Automatizing Amortized Analysis



### Examples

~~~
type nat =
	| O
	| S of nat

let rec add n m =
	match n with
	| O -> m
	| S n1 -> (add n1 (S m))

let rec mult n m =
	match n with
	| O -> O
	| S n1 -> add m (mult n1 m)

let rec square n = mult n n
~~~

### Results

~~~
== add :

  [nat; nat] -> nat

  Non-zero annotations of the argument:
		8  <--  ([S(*)], [])
		3  <--  ([], [])

  Non-zero annotations of result:

  Simplified bound:
	3 + 8*M
   where
	M is the number of S-nodes of the
	1st component of the argument
~~~

### Results

~~~
== mult :

  [nat; nat] -> nat

  Non-zero annotations of the argument:
		8  <--  ([S(*)], [S(*)])
		12  <--  ([S(*)], [])
		3  <--  ([], [])

  Non-zero annotations of result:

  Simplified bound:
	3 + 8*L*M + 12*M
   where
	L is the number of S-nodes of the
	2nd component of the argument
	M is the number of S-nodes of the
	1st component of the argument
~~~

### Results

~~~
== square :

  nat -> nat

  Non-zero annotations of the argument:
		16  <--  [S(*); S(*)]
		20  <--  [S(*)]
		7  <--  []

  Non-zero annotations of result:

  Simplified bound:
	7 + 12*M + 8*M^2
   where
	M is the number of S-nodes of the argument
~~~
