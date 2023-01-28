---
title: "Readable Lean 3 Proofs"
date: 2023-01-27T22:01:54-05:00
draft: false
tags: ["Formal Methods"]
math: true
medium_enabled: true
---

*Important Note: This blog post uses the Lean 3 syntax*

Interactive theorem provers are notorious for showcasing unreadable proofs. Let's illustrate our point with a couple examples and discuss various ways we can make it more readable.

## Disjunction Elimination

Disjunction Elimination or proof by cases is a rule of inference that states the following. Consider you have the following three proofs:

1. $p \vee q$
2. $p \rightarrow r$
3. $q \rightarrow r$

Then it doesn't matter if it is $p$ rather than $q$ that holds, in the end $r$ holds.  Wikipedia has a [nice example](https://en.wikipedia.org/wiki/Disjunction_elimination) of this concept. I numbered the statements to correspond to the above.

>     1. It is true that either I'm inside or I'm outside.
>     2. If I'm inside, I have my wallet on me.
>     3. If I'm outside, I have my wallet on me.
>     
>     Therefore, I have my wallet on me.

Now let's go over a corresponding proof in Lean.

```lean
example (p q r : Prop) : ((p → r) ∧ (q → r) ∧  (p ∨ q)) → r := begin
  intro H,
  cases H,
  cases H_right,
  cases H_right_right,
  case or.inl
  {
    exact H_left H_right_right,
  },
  case or.inr
  {
    exact H_right_left H_right_right,
  },
end
```

We can see a rough example of proof by cases at work. However, it's extremely hard to follow unless we try to emulate the proof state ourselves. What if I say that it doesn't have to be this way? That in fact, we can have proofs that are more readable. First let's start by replacing `intro` with `assume` and add labels to each of our cases.

```lean
example (p q r : Prop) : ((p → r) ∧ (q → r) ∧  (p ∨ q)) → r := begin
  assume H : ((p → r) ∧ (q → r) ∧  (p ∨ q)),
  cases H with H_pr H_rest,
  cases H_rest with H_qr H_pq,
  cases H_pq,
  case or.inl : H_p
  {
    exact H_pr H_p,
  },
  case or.inr : H_q
  {
    exact H_qr H_q,
  },
end
```

Now we know what `H` is just by looking at the proof. Sadly the cases don't exactly tell us what is contained in each of the hypotheses. But at least they're labeled to give us a clue. We can do better by replacing the initial `cases` statements with `have` and `exact` with `show`.

```lean
example (p q r : Prop) : ((p → r) ∧ (q → r) ∧  (p ∨ q)) → r := begin
  assume H : ((p → r) ∧ (q → r) ∧  (p ∨ q)),
  have H_pr : p → r := and.left H,
  have H_qr : q → r := and.left (and.right H),
  have H_pq : p ∨ q := and.right (and.right H),
  cases H_pq,
  case or.inl : H_p
  {
    show r, from H_pr H_p,
  },
  case or.inr : H_q
  {
    show r, from H_qr H_q,
  },
end
```

Now we have almost a complete picture of what all of our hypotheses are. The only two that are left unspecified are `H_p` and `H_q`. Though we can easily infer what they are by the label. Also by replacing `exact` with `show`, we have insight on what is trying to be proved at that given point. 

The whole beginning of the proof is setting up the problem. Luckily, Lean provides a more concise syntax that better matches how the problem would be presented.

```lean
example {p q r : Prop} (H_pr : p → r) (H_qr : q → r) (H_pq : p ∨ q) : r := begin
  cases H_pq,
  case or.inl : H_p
  {
    show r, from H_pr H_p,
  },
  case or.inr : H_q
  {
    show r, from H_qr H_q,
  },
end
```

Finally, if we wanted to condense this more, we can make use of the built in `or.elim` theorem.

```lean
example {p q r : Prop} (H_pr : p → r) (H_qr : q → r) (H_pq : p ∨ q) : r := begin
  show r, from or.elim H_pq H_pr H_qr,
end
```

## Negation Introduction

Now let's showcase a more complicated example. Negation introduction or proof by contradiction. Consider that we have the following two proofs:

1. $p \rightarrow q$
2. $p \rightarrow \neg q$

Then by negation introduction, we have a proof of $\neg p$.

The proof is going to rely on the law of excluded middle. That is $p \vee \neg p$ holds.

```lean
axiom LEM {p : Prop}: p ∨ ¬ p
```

The proof also relies on the following property about negation
$$
\neg p \iff (p \rightarrow false)
$$
Now let's try to prove negation introduction using the  `cases` tactic.

```lean
example {p q : Prop} (H_pq : p → q) (H_nq : p → ¬q) : ¬p := begin
  have H_LEM : p ∨ ¬p := LEM,
  cases H_LEM,
  case or.inl : H_p
  {
    have H_nq : ¬q := H_nq H_p,
    have H_qf : q → false := H_nq,
    have H_q : q := H_pq H_p,
    have H_f : false := H_qf H_q,
    -- Can prove anything with a falsity
    -- (Reductio ad absurdum)
    show ¬p, from false.rec (¬p) H_f,
  },
  case or.inr : H_np
  { 
    show ¬p, from H_np,
  },
end
```

Sadly this proof is too complicated to condense in one line with `or.elim`. However, we can set it up by creating subproofs with `have`.

```lean
example {p q : Prop} (H_pq : p → q) (H_nq : p → ¬q) : ¬p := begin
  have H_LEM : p ∨ ¬p := LEM,
  have H_npp : ¬p → ¬p := by {
    assume H_np : ¬p,
    show ¬p, from H_np,
  },
  have H_pp : p → ¬p := by {
    assume H_p : p,
    have H_nq : ¬q := H_nq H_p,
    have H_qf : q → false := H_nq,
    have H_q : q := H_pq H_p,
    have H_f : false := H_qf H_q,
    show ¬p, from false.rec (¬p) H_f,
  },
  show ¬p, from or.elim H_LEM H_pp H_npp,
end
```

## Conclusion

When most people are taught how to write proofs in an interactive theorem prover, they are shown tactics such as `cases`, `split`, `left`, `right`, etc. These tactics manipulate the proof state which is shown to the developer when creating the proof. However, as a line in a proof it provides minimal insight.

We can take the guesswork out of figuring out the proof state by carefully selecting tactics which allow us to explicitely show the object being constructed. In Lean, these are `assume`, `have`, and `show`. Also making use of the inference rules themselves such as `or.elim` is a great alternative to `cases`, and `and.intro` is a great alternative to split.

If you have any other techniques on making ITP proofs more readable, please let me know.
