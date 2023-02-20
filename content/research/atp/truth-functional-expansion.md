---
title: Finding Counter-Models through Truth Functional Expansions
math: true
---

The best way to disprove a statement is to find a counter-example.
For first order formulas, the quantifiers are over some *universe of discourse* $\mathcal{D}$.

For example, $\forall x, P(x)$ says that for every $x$ within the universe of discourse, $x$ has property $P$. Let's say that our universe of discourse consists of two elements $c_1$ and $c_2$. Then the statement $\forall x, P(x)$ is equivalent to $P(c_1) \wedge P(c_2)$. That is, both elements in the universe of discourse hold property $P$. This equivalence is called the *truth-functional expansion*.

Let $\mathcal{D} = \\{ c_1, \dots, c_n \\}$ be the universe of discourse. Then the following equivalences hold:
$$
    \forall x P(x) \iff P(c_1) \wedge \dots \wedge P(c_n)
$$
$$
    \exists x P(x) \iff P(c_1) \vee \dots \vee P(c_n)
$$

To find a counter-example, you'll need to find a model in which the formula does not hold. A model consists of a universe of discourse and whether or not each possible predicate holds. For example, let's take a binary predicate $F$. For a domain of discourse of size two, the following predicates may hold: $F(c_1, c_1), F(c_1, c_2), F(c_2, c_1), F(c_2, c_2)$. For any given model, each of those instantiations can hold or not, amounting to $2^4 = 16$ possible models for a domain of discourse of size $2$ with one binary predicate.

Now let's find a counter-example for an invalid formula. Consider $\exists x F(x, x) \implies \forall x F(x, x)$.
To perform a truth functional expansion, we need to first convert to [prenex normal form](https://en.wikipedia.org/wiki/Prenex_normal_form). This works out to be $\forall x \forall y (F(x, x) \implies F(y, y))$

{{<details "Details">}}
$$
\begin{align*}
\exists x F(x, x) \implies \forall x F(x, x) &\iff \forall x (F(x, x) \implies \forall y F(y, y)) \\\\
&\iff \forall x \forall y (F(x, x) \implies F(y, y))
\end{align*}
$$
{{</details>}}

Let $\mathcal{D} = \\{ c_1 \\}$. The truth functional expansion is $F(c_1, c_1) \implies F(c_1, c_1)$. This is a tuatlogy so the formula is valid for domain of size 1.

Now let $\mathcal{D} = \\{ c_1, c_2 \\}$. After removing the tautologies, the truth functional expansion works out to be $(F(c_1, c_1) \implies F(c_2, c_2)) \wedge (F(c_2, c_2) \implies F(c_1, c_1))$

{{<details "Details">}}
$$
\forall x \forall y (F(x, x) \implies F(y, y)) \\\\
(\forall y (F(c_1, c_1) \implies F(y, y))) \wedge (\forall y (F(c_2, c_2) \implies F(y, y))) \\\\
((F(c_1, c_1) \implies F(c_1, c_1)) \wedge (F(c_1, c_1) \implies F(c_2, c_2))) \wedge ((F(c_2, c_2) \implies F(c_1, c_1)) \wedge (F(c_2, c_2) \implies F(c_2, c_2))) \\\\
(F(c_1, c_1) \implies F(c_2, c_2)) \wedge (F(c_2, c_2) \implies F(c_1, c_1))
$$
</details>
{{</details>}}

Consider the model $\\{ F(c_1, c_1), \neg F(c_1, c_2), \neg F(c_2, c_1), \neg F(c_2, c_2) \\}$. This causes the left hand side of the conjunction to fail. Hence the formula is invalid and we have found a counterexample.
