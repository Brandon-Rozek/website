---
title: "Introduction to Possibility Theory"
date: 2024-10-30T10:25:31-04:00
draft: false
tags: []
math: true
medium_enabled: false
---

Possibility theory is a subset of Dempster-Shafer theory (DST). If you're not already familiar with DST, I recommend you check out my [previous blog post](/blog/intro-dempster-shafer/) since we'll reuse a lot of the same concepts.

---

In Dempster-Shafer theory we start off with a mass function $m$ which is defined over all subsets of our event space $\Omega$. When approximating $m$, we need to make $2^\Omega$ estimates. This can be quite costly depending on the size of $\Omega$.

Possibility theory makes the estimation of $m$ tractable at the cost of expressivity. As a subset of DST, the mass function is positive only on a sequence of nested subsets. Recall that a set represents a disjunctive observation. That is, $\\{w, g\\}$ represents $w \vee g$.

Take for example, the following observations
$$
obs = c, w \vee c, w \vee c \vee g
$$
We can use possibility theory to reason about these since $c \subseteq \\{w, c\\} \subseteq \\{w, c, g\\}$ We cannot, however, use possibility theory to reason about
$$
obs = c, w \vee c, g \vee c
$$
since $\\{w, c\\} \not\subseteq \\{g, c\\}$.

Informally, possibility theory describes uncertainty through ordering the plausibility of elementary events and constraints uncertainty such that the elementary events that are not the most plausible are never necessary.

## Properties of Possibility Theory	

Let's walk through an example so that we can illustrate different properties of possibility theory.
$$
obs = w \vee c \vee g, c, c, w \vee c
$$
From this, we can derive the following mass function
$$
m(\\{c\\}) = \frac{1}{2}, m(\\{w, c\\}) = \frac{1}{4}, m(\\{w, c, g\\}) = \frac{1}{4}
$$
The plausibility values are as follows:
$$
Pl(\\{g\\}) = \frac{1}{4}, Pl(\\{w\\}) = \frac{1}{2}, Pl(\\{c\\}) = 1 \\\\
Pl(\\{w, g\\}) = \frac{1}{2}, Pl(\\{w, c\\}) = 1, Pl(\\{g, c\\}) = 1 \\\\
Pl(\\{w, c, g\\}) = 1
$$
This leads us to the first property regarding plausibility:
$$
Pl(A \cup B) = max(Pl(A), Pl(B)) \tag{0.1}
$$
In order to build an intuition of this formula, let's look at the mass function pictorally.

![](/files/images/blog/focalsets.svg)

Other than the concentric rings shown, all other subsets of $\Omega$ have a mass value of zero. When computing the plausibility value graphically, we start at the outer edge of the ring and keep summing inwards until we hit a ring that does not intersect with our set. Therefore, when it comes to the union of two sets, we keep summing until neither $A$ or $B$ intersect with the ring.

Now let's analyze necessity:
$$
N(\\{w\\}) = 0, N(\\{g\\}) = 0, N(\\{c\\}) = \frac{1}{2} \\\\
N(\\{w, g\\}) = 0, N(\\{w, c\\}) = \frac{3}{4}, N(\\{c, g\\}) = \frac{1}{2} \\\\
N(\\{w, g, c\\}) = 1
$$
The necessity of two sets intersected is smallest necessity of the individual sets.
$$
N(A \cap B) = min(N(A), N(B)) \tag{0.2}
$$
Pictorially when calculating the necessity of a set, we start from the inner circle and sum until the ring is no longer a subset of the set.

Necessity is also related to plausibility
$$
N(A) = 1 - Pl(\bar{A}) \tag{0.3}
$$
where $\bar{A}$ is the compliment of $A$ with respect to $\Omega$.

Recall from my last blog post that $N(\\{a\\}) = m(\\{a\\})$ for all $a \in \Omega$. Therefore, given the plausibility of elementary events, we can use equations 0.1 and 0.3 to uniquely determine the mass function.

## Deriving mass function from plausibility values

Consider the following plausibility values
$$
Pl(\\{c\\}) = 1, Pl(\\{w\\}) = b_1, Pl(\\{g\\}) = b_2
$$
From this, we can derive the other plausibility values from Equation 0.1:
$$
Pl(\\{c, w\\}) = 1, Pl(\\{c, g\\}) = 1, Pl(\\{w, g\\}) = max(b_1, b_2) \\\\
Pl(\\{c, w, g\\}) = 1
$$
Using Equation 0.3, we can derive the necessity values
$$
N(\\{c\\}) = 1 - max(b_1, b_2), N(\\{w\\}) = 0, N(\\{g\\}) = 0 \\\\
N(\\{c, g\\}) = 1 - b_1, N(\\{c, w\\}) = 1 - b_2, N(\\{w, g\\}) = 0 \\\\
N(\\{c, w, g\\}) = 1
$$
In order to calculate the mass values, I often work backwards starting from smaller sets from the necessity definition.
$$
N(A) = \sum_{B \subseteq A}{m(B)}
$$
Therefore in our example,
$$
m(\\{w\\}) = 0, m(\\{g\\}) = 0 \\\\
m(\\{c\\}) = 1 - max(b_1, b_2) \\\\
m(\\{c, w\\}) = max(b_1, b_2) - b_2 \\\\
m(\\{c, g\\}) = max(b_1, b_2) - b_1 \\\\
m(\\{g, w\\}) = 0 \\\\
m(\\{g, w, c\\}) = b_1 + b_2 - max(b_1, b_2)
$$
You can verify that indeed the sum of all the mass values are equal to 1.

## Conclusion

Possibility theory is a subset of Dempster-Shafer theory that makes estimation tractable. Instead of needing to come up with $2^{|\Omega|}$ estimates to approximate the mass function, we only need to come up with $|\Omega|$ plausiblity values in order to derive the rest of the mass function.

This makes it a useful representation of uncertainty computationally, when we want to model imprecise sensor data or make use of qualitative or subjective measurements.
