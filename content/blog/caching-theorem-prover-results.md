---
title: "Caching Theorem Prover Results"
date: 2024-03-02T11:15:04-05:00
draft: false
tags: ["Logic"]
math: true
medium_enabled: false
---

[Spectra](https://github.com/rairlab/spectra) is an automated planner that uses theorem proving to decide which actions to try out and determine when the goal is reached. Given an execution of Spectra on a problem within a domain, it's current architecture involves making many calls of similar structure to a theorem prover.

For example we know that $\\{ P, P \rightarrow Q \\} \vdash Q$ holds. In classical first order logic, it is also the case that $\\{ P, P \rightarrow Q, R\\} \vdash Q$ holds. 

That is to say, adding additional formulae does not affect the result. In fact in classical first order logic, adding contradictory formulae also does not affect the provability of a given statement. This is due to the principle of explosion which states that from a contradiction we can derive anything.

What can we say about the other direction? How do we know when something does not hold? Let's say we know the following statement: $\\{ R, Z, P \rightarrow Q \\} \not\vdash Q$. What can we say about $\\{ Z, P \rightarrow Q \\} \not\vdash Q$?

Intuitively, if we cannot show a formula $Q$  given some set of information. Then in classical first order logic, it goes to show that we cannot show $Q$ with less information.

Let's discuss how this works in practice. Let $P$ be the set of assumptions which prove a corresponding goal. That is, given $(\Gamma_i, G_i) \in P, \Gamma_i \vdash G_i$. On the other hand, let $N$ be the set of assumptions which don't prove a corresponding goal, i.e. $(\Gamma_i, G_i) \in N, \Gamma_i \not\vdash G_i$.

Given a problem $\Gamma \vdash G$. We perform two caching checks before calling the full automated theorem prover. 

1) If there exists a $(\Gamma_i, G_i) \in P$ such that $G = G_i$ and $\Gamma_i \subseteq \Gamma$, then we know that $\Gamma \vdash G$ holds.
2) On the other hand, if there exists a $(\Gamma_i, G_i) \in N$ such that $G = G_i$ and $\Gamma \subseteq \Gamma_i$, then we know that $\Gamma \not\vdash G$.

If either of those two conditions don't get matched, then we can call the full automated theorem prover to determine the result and cache it in either $P$ or $N$.

This caching technique might not work well in your application. It works well in Spectra since we're trying to prove a small set of goals and action preconditions and the assumptions consist of state variables which don't vary by much between steps.

Though keep in mind that this technique will give you flawed answers if the corresponding logic is non-monotonic. Classical first-order and propositional logic is monotonic, however, so this caching technique is safe to use in those settings.

In non-monotonic or defeasible logic, you could have a statement $B^2(\neg P)$ which defeats another statement $B^1(P)$. We can read the last example as "I have a strong belief that P does not holds and a weak belief that P holds". This depending on the defeasible logic, can change whether of not given $B^\sigma(P \rightarrow Q)$, if $B^{\sigma_i}(Q)$ holds.



