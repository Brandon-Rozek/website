---
title: "Introduction to Dempster-Shafer Theory"
date: 2024-10-29T12:38:21-04:00
draft: false
tags: []
math: true
medium_enabled: false
---

Imagine sitting by a tree full of birds. You know the tree only has a Yellow Rumped Warbler ($w$), a Northern Cardinal ($c$), and an American Goldfinch ($g$). These birds are respectful in that they don't call at the same time.

You make the following observations of bird calls:
$$
obs = w, w, c, g, g, w
$$
What's the probability that we hear a Warbler next assuming the calls are independent from each other?
$$
count_w = 3, total = 6, P(w) = \frac{3}{6} = 0.5
$$
This example assumes that we're bird call experts and are able to uniquely determine each bird call. What happens if our observations are *imprecise*? 

## Dempster-Shafer Theory (DST)

DST, otherwise known as belief functions theory or the theory of evidence, looks at what happens if we allow each observation to be a disjunction ($\vee$)?
$$
obs = w \vee c \vee g, c, w \vee c, w \vee g
$$
There can be many reasons for this. Maybe our hearing isn't so good. There's additional noise around you disrupting your sensing.

Formally, let us define $\Omega$ to be our event space. In this example, this is the set of possible bird calls.
$$
\Omega = \\{w, c, g\\}
$$
**The mass function** $m: A \rightarrow [0, 1], \forall A \subseteq \Omega$ assigns a value between 0 and 1 to every possible subset of our event space. The set $\\{w, g\\}$ represents the observation $w \vee g$.

An important property is that the sum of all the masses are equal to 1.
$$
\sum_{A \subseteq \Omega} m(A) = 1
$$
In order to derive this mass function, we can normalize our observations from earlier.
$$
m(\\{w, c, g\\}) = \frac{1}{4}, m(\\{c\\}) = \frac{1}{4}, m(\\{w, c\\}) = \frac{1}{4}, m(\\{w, g\\}) = \frac{1}{4}
$$
We assign the value $0$ to all other subsets of $\Omega$. By definition, $m(\\{\\}) = 0$.

**The plausibility measure** for a disjunctive set $A$ is the sum of all the mass values of the subets of $\Omega$ that intersect with $A$.
$$
Pl(A) = \sum_{B \cap A \ne \emptyset}{m(B)}
$$
In our example,
$$
\begin{align*}
Pl(\\{w\\}) &= m(\\{w, c, g\\}) + m(\\{w, c\\}) + m(\\{w,g\\}) + m(\\{w\\}) \\\\
		  &= \frac{3}{4}
\end{align*}
$$
**The necessity measure** is more restrictive in that we only look at the summation of the masses of the subsets of $A$.
$$
Nec(A) = \sum_{B \subseteq A}{m(B)}
$$
Consider an arbitrary event $a \in \Omega$. Then,
$$
\begin{align*}
Nec(\\{a\\}) &= m(\\{a\\}) + m(\\{\\}) \\\\
             &= m(\\{a\\})
\end{align*}
$$
Therefore in our example,
$$
Nec(\\{w\\}) = 0, Nec(\\{c\\}) = \frac{1}{4}, Nec(\\{g\\}) = 0
$$
Another example,
$$
\begin{align*}
Nec(\\{w, c\\}) &= m(\\{w, c\\}) + m(\\{c\\}) + m(\\{w\\}) + m(\\{\\}) \\\\
                &= \frac{1}{4} + \frac{1}{4} + 0 + 0 \\\
                &= 0.5
\end{align*}
$$
**The probability measure** is bounded by the necessity and plausibility measures.

For a disjunctive set $A$,
$$
Nec(A) \le P(A) \le Pl(A)
$$
Extending probability to a range of values gives us a way to model *ignorance*. We say an agent is completely ignorant if $|\Omega| > 1$ and $m(\Omega) = 1$.

Consider a completely ignorant agent where $\Omega = \\{w, c, g\\}$.

Then,
$$
\begin{align*}
Nec(\\{w\\}) \le P(\\{w\\}) &\le Pl(\\{w\\}) \\\\
m(\\{w\\}) \le P(\\{w\\}) &\le m(\\{w\\}) + m(\\{w, c\\}) + m(\\{w, g\\}) + m(\\{w, c, g\\}) \\\\
0 \le P(\\{w\\}) &\le 1
\end{align*}
$$
Probability theory is a subset of Dempster-Shafer theory. In order to see this, let us look at an example of observations where there is no disjunction.
$$
obs = w, w, c, g, g, w
$$
Normalize our observations to derive the mass function:
$$
m(\\{w\\}) = \frac{1}{2}, m(\\{c\\}) = \frac{1}{6}, m(\\{g\\}) = \frac{1}{3}
$$
The mass function in this example is $0$ for every non-singleton subset of $\Omega$.

What is the probability range for $w$?
$$
\begin{align*}
Nec(\\{w\\}) \le P(\\{w\\}) &\le Pl(\\{w\\}) \\\\
m(\\{w\\}) \le P(\\{w\\}) &\le m(\\{w\\}) + m(\\{w, g\\}) + m(\\{w, c\\}) + m(\\{w, c, g\\}) \\\\
\frac{1}{2} \le P(\\{w\\}) &\le \frac{1}{2} + 0 + 0 + 0
\end{align*}
$$
Therefore, $P(w) = \frac{1}{2}$ as expected in probability theory.

## Conclusion

Dempster-Shafer theory is an attempt at addressing *imprecise observations* through disjunctive events. It extends probability theory to consider not just a single value, but a range of possible values. This allows the model to decouple uncertainty from *ignorance*.
