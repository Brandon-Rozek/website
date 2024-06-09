---
title: "Representing Uncertainty under the Closed World Assumption"
date: 2023-09-18T19:01:56-04:00
draft: false
tags:
    - Logic
    - Automated Planning
math: true
medium_enabled: false
---

The [closed world assumption](https://en.wikipedia.org/wiki/Closed-world_assumption) is used in many practical applications of logic (planning, prolog, databases) in order to lower the complexity class of the reasoning algorithms used. This assumes that any predicates that are stated are true and the ones that aren't are false.

For example, given the state: `(color shirt1 red) (color shirt2 blue)`, we know that `(color shirt1 blue)` is false solely because it wasn't listed in the state.

This means that for an individual predicate $P$, it can either represent true or false. To represent uncertainty, we need to extend to the use of two predicates instead of one.

This approach is popular within conformant planning citing back to Palacios and Geffner in 2006. Consider our predicate $P$ for example. Instead of that predicate existing imagine we have the predicates. $K P$ and $K \neg P$. Note that $K$ is not a higher-order predicate or operator but is instead part of the predicate name. Then our truth value for $P$ is as follows:

| $K P$ | $K \neg P$ | $P$           |
| ----- | ---------- | ------------- |
| True  | False      | True          |
| False | True       | False         |
| False | False      | Unknown       |
| True  | True       | Contradiction |

We're still in the closed world assumption setting. The intuition behind this compilation is that the agent "knows what it knows and knows what it doesn't know." This approach doesn't include any epistemic axions, but may be good enough to get started modeling within some of these systems.

This is one way of encoding uncertainty in some predicate of $P$, but not the only way. An alternative is what I call the *discovery encoding*, mainly since I haven't seen it in use in literature. If you have a citation with this encoding being used, please share with me.

| $\mathit{P\\_Value}$ | $P\\_Discovered$ | $P$           |
| -------------------- | ---------------- | ------------- |
| True                 | True             | True          |
| False                | True             | False         |
| False                | False            | Unknown       |
| True                 | False            | Contradiction |

This operates very similarly to [optionals](https://en.wikipedia.org/wiki/Option_type) within functional programming. The idea is that one shouldn't even consider the valuation of $P\\_Value$ until $P\\_Discovered$ is true. Since once $P\\_Discovered$ is true, then $P\\_Value = P$.

**References**

Palacios, Héctor, and Hector Geffner. "Compiling uncertainty away:  Solving conformant planning problems using a classical planner  (sometimes)." *AAAI*. 2006.
