---
title: "Syntactic Unification"
math: true
---
PAGE IS UNDER CONSTRUCTION...

Unification is the more generalized form of equation solving that you might have learned in school. The goal is to find substitutions for variables to make the equality true. Syntactic unification is the simplest case, where we do not assume properties such as associativity, commutativity, distribution, etc. exist.

In this post we're going to follow convention that constants are in the beginning half of the alphabet, while variables are in the later half.

Constants: $a, b, c$

Variables: $x, y, z$



Algorithm:

- Check for Occurs Check
- Check for Function Clash
- Orrient
- Decompose



Examples: (TODO: Walk through the algorithm)
$$
f(g(a, b)) =_? f(x)
$$
The solution to this problem is: $x \mapsto g(a, b)$ 


$$
f(g(a, b)) =_? x
$$
This has no solution.

