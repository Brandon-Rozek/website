---
title: "Definitional CNF"
math: true
---

Satisfiability algorithms have been optimized to accept formulas in Conjunctive Normal Form (CNF).
One issue is that depending on the algorithm used to convert the formula, it can take either exponential
time or space. To get around this we will use an algorithm to produce an equisatisfiable algorithm albeit
non-equivalent. This will create a linear increase in the size of the formula, however, it also only
takes linear time to compute.


Procedure:
1. First convert the formula to Negation Normal Form (NNF). This is done by making it so that negations are only applied to propositions and there is no implication or bi-implication symbols in the formula.
2. Starting from the inner-most part of the expression to the outermost, define a new variable that describes the connective and add that definition to the expression.

Consider the expression $b + ac$. Then,

$$
\begin{align*}
\text{Define } x \iff ac \\\\
(b + x) * (x \iff ac) \\\\
\text{Define } y \iff b + x \\\\
y * (x \iff ac) * (y \iff b + x)
\end{align*}
$$

3. Finally, convert the bi-implifications using the following tautologies:

$$
\begin{align*}
x \iff (y * z) &\equiv (-x + y) (-x + z)(x+-y+-z) \\\\
x \iff (y + z) &\equiv (-x + y + z)(x + -y)(x + -z)
\end{align*}
$$

Extending the example,
$$
y(-x + a)(-x + c)(x + -a + -c)(y \iff b + x) \\\\
y(-x + a)(-x + c)(x + -a + -c)(-y + b + x)(y + -b)(y + -x)
$$
