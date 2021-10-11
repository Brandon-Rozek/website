---
Title: Term Reasoning
Description: Techniques that allow reasoning about term algebras.
math: true
---

In this page, I wish to highlight techniques that are used to manipulate terms.

## Unification
Unification is a generalized form of equation solving taught in an algebra class. The goal is to find substitutions for variables such that the relation is true. 

Example:
$$
f(a, x) = f(a, b)
$$
Result: $\sigma = \\{ x \mapsto b \\}$



In the most general case, no theories or properties are assumed. Different unification algorithms are used based on the equational theory assumed. Most types of theories are denoted by a combination of letters:

| Letter | Description           |
| ------ | --------------------- |
| A      | Associativity         |
| C      | Commutativity         |
| $D_l$  | Left Distributivity   |
| $D_r$  | Right Distributivity  |
| $I$    | Idempotence           |
| $N_l$  | Left Neutral Element  |
| $N_r$  | Right Neutral Element |

The theory AC therefore has the associative and commutative property with respect to an operation. For a more complete reading on the subject, feel free to take a look at the Unification Theory chapter under "Handbook of Automated Reasoning, 2001".

Additional Notes:
- [Syntactic Unification](unification/syntactic)



## Term Rewriting
Term Rewriting is the study of replacing subterms of a formula. Normally they are described by a Rewrite Rule which in combination create a Rewrite System. 

Example of a Rewrite Rule: $r_1 = f(a, x) \mapsto a$

Example of a Rewrite System: $R = \\{r_0, r_2\\} = \\{ f(a, x) \mapsto a, f(x, b) \mapsto x \\}$

Applying $r_1$ to $f(a, c)$ results in the term $c$. There are cases though when applying a rewrite rule to a term can create multiple results. This has to do with the subterm that is matched. For example, applying $r_1$ to $f(f(a, x), x)$ can result in either $f(a, x)$ or $a$ dependng on if you match the whole term or just the inner $f(a, x)$.

The variants of a term is a set of terms reachable by applying a specified set of rewrite rules to the term. If the set of variants is finite for every term, then the Rewrite System is said to have the Finite Variant Property (FVP). 

A great source for this topic is the book "Term Rewriting and All That" by Franz Baader and Tobias Nipkow.

Additional Notes:
- [Rewriting Algorithm](rewriting/algorithm)
- [Variants Algorithm](rewriting/variants)
- [Folding Variant Narrowing](rewriting/fv-narrowing)



