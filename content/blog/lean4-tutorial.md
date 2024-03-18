---
title: "Lean 4 Tutorial"
date: 2024-03-17T22:27:32-04:00
draft: false
tags: ["Formal Methods"]
math: true
medium_enabled: false
---

Lean is an interactive theorem prover created by Microsoft.
In 2021, they performed a major transition from Lean 3 to Lean 4.
This transition changed the syntax and tactics used within proofs
and caused major library developers such as Mathlib to transition.

Last year I wrote a [Lean 3 tutorial](/blog/lean3-tutorial) which showcases
how to go about constructing proofs for several small problems.
After revisiting Lean 4 recently,
I decided that Mathlib support is comprehensive and stable enough to make
the switch.

This post is the same as the Lean 3 tutorial that I wrote last year, except
that the examples have been updated to the latest syntax.


## Propositional Logic (Intuitionist Fragment)

To prove something in Lean, we need to construct an object of that type.

### Conjunctive Introduction
To start off let us prove the statement $P \wedge Q$ given both $P$ and $Q$ individually.

```lean
example {p q : Prop} (H_p : p) (H_q : q) : (p ∧ q) := by
  exact show p ∧ q from And.intro H_p H_q
```

This shows an application of conjunctive introduction. We created the object $P \wedge Q$ by applying the theorem `And.intro` to both hypotheses `H_p` which contains $P$ and `H_q` which contains $Q$.


Another way of going about this proof is by *transforming the goal to another equivalent one*.

```lean
example {p q : Prop} (H_p : p) (H_q : q) : (p ∧ q) := by
  constructor
  case left =>
    exact show p from H_p
  case right =>
    exact show q from H_q
```

In this proof, we make use of the `constructor` tactic. Given a conjunctive goal $P \wedge Q$, this tactic replaces it with two subgoals $P$ and $Q$. We can then apply the hypotheses to solve the problem.

### Conjunctive Elimination

Given the proof of $P \wedge Q$, we can derive $P$ from it.

```lean
example {p q : Prop} (H_pq : p ∧ q) : p := by
  exact show p from And.left H_pq
```

In the example above, we apply the inference `And.left` to be able to derive the left side of a conjunct. Similarly to the last inference rule, there is a tactic based way to go about it. Tactic based methods are generally more prevalent within the ITP community.

```lean
example {p q : Prop} (H_pq : p ∧ q) : p := by
  cases' H_pq with H_p H_q -- p, q
  exact show p from H_p
```

Given a conjunctive hypothesis, the `cases'` tactic will create two new hypothesis from it. The two labels after the `with` is to specify the names of these hypotheses. The string `--` denotes the start of a comment; I left a small comment to remind me the ordering of the conjuncts.

### Disjunctive Introduction

Given any statement $P$, we can introduce an arbitrary formula as a disjunct. More intuitively, if Jarold is above the age of 10, then he is above the age of 10 or he likes lollipops. It does not change the truth value of the statement.

The inference based way of representing this is as follows:

```lean
example {p q : Prop} (H_p : p) : (p ∨ q) := by
  exact show p ∨ q from Or.intro_left q H_p
```

In the more popular tactic based notion. We use the tactic `left` or `right` to denote which side we're going to attempt to prove. If we're trying to prove $P \vee Q$ and we have $P$ then we will prove the left side.

```lean
example {p q : Prop} (H_p : p) : (p ∨ q) := by
  left
  exact show p from H_p
```

### Disjunctive Elimination

The form of disjunctive elimination included in Lean is more commonly known as *proof by cases*. That is if you know either $A$ or $B$ is true. That is, $A \vee B$. And, you can derive $C$ from $A$ as well as $C$ from $B$. Then it doesn't matter which of $A$ or $B$ is true, because you can derive $C$ regardless.

[Wikipedia](https://en.wikipedia.org/wiki/Disjunction_elimination) has a nice intuitive example:
> If I'm inside, I have my wallet on me.
>
> If I'm outside, I have my wallet on me.
>
> It is true that either I'm inside or I'm outside.
>
> Therefore, I have my wallet on me.

To achieve this in Lean using the inference based approach.

```lean
example {p q r : Prop} (H_pr : p → r) (H_qr : q → r) (H_pq : p ∨ q) : r := by
  exact show r from Or.elim H_pq H_pr H_qr
```

Alternatively, via the tactic based approach

```lean
example {p q r : Prop} (H_pr : p → r) (H_qr : q → r) (H_pq : p ∨ q) : r := by
  cases' H_pq with H_p H_q
  case inl =>
    -- Assume p, apply modus ponens with H_pr
    exact show r from H_pr H_p
  case inr =>
    -- Assume q, apply modus ponens with H_qr
    exact show r from H_qr H_q
```

## Negation

Traditional interactive theorem provers such as Coq focused on the constructivist approach to theorem proving.
This allows them to export proofs as programs in OCaml.
Lean places less of an emphasis on this approach and instead supports the proof by contradiction style
you see in classical theorem proving.

For this tutorial, I decided to make this distinction
explicit by declaring a new axiom for the law of
excluded middle.
By default, Lean has the axiom of choice which
they use to prove the law of excluded middle
through the proof `Classical.em`.

In other words, if you want to perform a proof by contradiction, don't use the techniques shown in this section and instead use the `by_contra` tactic or directly use `Classical.em`.

Declare the axiom of law of excluded middle:

```lean
axiom LEM {p : Prop}: p ∨ ¬ p
```

### Negation Introduction

For negation introduction, let's say we have some proposition $P$. If we can use $P$ to derive a falsity, let's say $Q \wedge \neg Q$ then $P$ must be false. That is, we introduce a negation to make it $\neg P$.

The structure of the proof will a proof by cases on the law of exclude middle.

```lean
lemma negation_intro {p q : Prop} (H_pq : p → q) (H_pnq : p → ¬q) : ¬p := by
  have H_LEM : p ∨ ¬p := LEM

  -- Assuming ¬p derive ¬p
  have H_npp : ¬p → ¬p := by
    intro (H_np : ¬p)
    exact show ¬p from H_np

  -- Assuming p derive ¬p
  have H_pp : p → ¬p := by
    -- Use hypotheses to obtain q and ¬q
    intro (H_p : p)
    have H_q : q := H_pq H_p
    have H_nq : ¬q := H_pnq H_p

    -- We can derive falsity from a direct contradiction
    have H_false : False := H_nq H_q

    -- You can derive anything from false
    have H_UNUSED: p ∧ ¬p := False.elim H_false

    -- Including what we want, ¬p
    exact show ¬p from False.elim H_false

  -- By proof by cases, we derive ¬p
  exact show ¬p from Or.elim H_LEM H_pp H_npp
```

Lean can tell us which axioms our proof depends on as well.

```lean
#print axioms negation_intro
```

This returns `'negation_intro' depends on axioms: [LEM]`.

Alternatively, the tactic based approach

```lean
example {p q : Prop} (H_pq : p → q) (H_pnq : p → ¬q) : ¬p := by
  have H_LEM : p ∨ ¬p := LEM
  cases' H_LEM with H_p H_np

  case inl =>
    have H_q : q := H_pq H_p
    have H_nq : ¬q := H_pnq H_p
    have H_false : False := H_nq H_q
    exact show ¬p from False.elim H_false

  case inr =>
    exact show ¬p from H_np
```

As I mentioned before, we do not have to explicitly declare the
axiom of excluded middle. Instead we can make use of Lean's builtin
classical reasoning.

```lean
example {p q : Prop} (H_pq : p → q) (H_pnq : p → ¬q) : ¬p := by
  by_contra H_p
  have H_q : q := H_pq H_p
  have H_nq : ¬q := H_pnq H_p
  exact show False from H_nq H_q
```

### Double Negation Elimination

One common representation of negation elimination is to remove any double negations.
That is $\neg \neg P$ becomes $P$.

We'll similarly show this by performing a proof by cases on the law of excluded middle.

```lean
example {p: Prop} (H_nnp : ¬¬p) : p := by
  have H_LEM : p ∨ ¬p := LEM

  -- Assuming ¬p derive p
  have H_np2p : ¬p → p := by
    intro (H_np : ¬p)
    -- ¬p and ¬¬p are a direct contradiction
    have H_false : False := H_nnp H_np
    -- Derive our goal from a falsity
    exact show p from False.elim H_false

  -- Assuming p derive p
  have H_p2p : p → p := by
    intro (H_p : p)
    exact show p from H_p

  -- By proof by cases, we derive p
  exact show p from Or.elim H_LEM H_p2p H_np2p
```

Alternatively for the tactic based approach.

```lean
example {p: Prop} (H_nnp : ¬¬p) : p := by
  have H_LEM : p ∨ ¬p := LEM
  cases' H_LEM with H_p H_np

  -- Assuming p, derive p
  case inl =>
    exact show p from H_p

  -- Assuming ¬p derive p
  case inr =>
    -- ¬p and ¬¬p are a direct contradiction
    have H_false : False := H_nnp H_np
    exact show p from False.elim H_false
```

Lean has this theorem built-in with `Classical.not_not`.

## First Order

Lean is also capable of reasoning over first order logic. In this section, we'll start seeing objects/terms and predicates instead of just propositions.

For example `{α : Type} {P : α → Prop} ` means that $P$ is a predicate of arity one and takes an object of type $\alpha$.


### Forall Elim

If we have a forall statement, then we can replace the bound variable with an object of that type and remove the forall. Lets say for our example we have the following forall statement: $\forall x \in \mathbb{N}: x \ge 0$. Then we can replace the $x$ with $2$ and get the following formula: $2 \ge 0$.

```lean
example {α : Type} {P : α → Prop} {y : α} (H : ∀ x : α,  P x) : P y := by
  exact show P y from H y
```

### Forall Intro

To show that some property holds for all $x$ of a type α, you need to show that it holds
for an arbitrary $x$ of that type. We can introduce this object, by the `intro` command.

```lean
example {α : Type} {P Q R : α → Prop} (H_pq : ∀ x : α, P x → Q x) (H_qr : ∀ x : α, Q x → R x) : ∀ x : α, P x → R x := by
  intro (y: α)
  have H_pqx : P y → Q y := H_pq y
  have H_qrx : Q y → R y := H_qr y
  intro (H_py : P y)
  have H_qy : Q y := H_pqx H_py
  exact show R y from H_qrx H_qy
```

### Exists Intro

To introduce an existential, you need to show that the formula holds for any object of a certain type.

```lean
example {α : Type} {P : α → Prop} {y : α} (H: P y) : ∃ x: α, P x := by
  exact show ∃ x, P x from Exists.intro y H
```

In the tactic based approach, this is done via `exists`:

```lean
example {α : Type} {P : α → Prop} {y : α} (H: P y) : ∃ x: α, P x := by
  exact show ∃ x, P x from by exists y
```

### Exists Elim

Lets say we have the following forall statement: $\forall a \in \alpha: p a \implies b$.

Now lets say we have the following existential: $\exists x, p x$.

Using these, we can derive $b$.

```lean
example {α : Type} {p : α → Prop} {b : Prop} (H_epx : ∃ x, p x) (H_pab : ∀ (a : α), p a → b) : b := by
  exact show b from Exists.elim H_epx H_pab
```

Alternatively for the tactic based approach:

```lean
example {α : Type} {p : α → Prop} {b : Prop} (H_epx : ∃ x, p x) (H_pab : ∀ (a : α), p a → b) : b := by
  cases' H_epx with c H_pc
  have H_pcb : p c → b := H_pab c
  exact show b from H_pcb H_pc
```

## Inductive Types

One of the biggest use cases of an interactive
theorem prover is in program verification.
To help represent recursive data structures, we
have the notion of an *inductive type*.

Let's create a custom representation of a list.
A list can either by empty (`cnil`) or be an element `hd` combined with the rest of some list `tl`.

```lean
inductive CustomList (T : Type) where
| cnil : CustomList T
| ccons (hd : T) -> (tl : CustomList T) : CustomList T
```

Some examples of a list here include `cnil`,
`ccons(0, cnil)`, and `ccons(1, ccons(0, cnil))`.

For convenience, we'll open the `CustomList` namespace
so that we don't have to refer each constructor
(`cnil`/`ccons`) by it.

```lean
open CustomList
```

### Functions over Inductive Types

To define a function over an inductive type,
we need to cover each of the constructors.

For example, let's consider the notion of a list's length.
- If the list is `cnil` then the length is $0$.
- If the list starts with `ccons` then we add 1 to the length of the tail `tl`.

```lean
def clength {α : Type}:  CustomList α → Nat
  | cnil => 0
  | (ccons _ as) => 1 + clength as
```

We can see the output of a function via the `#eval` command.

```lean
#eval clength (@cnil Nat)
#eval clength (ccons 2 (ccons 1 cnil))
```

For another example, let us look at appending two lists. As an example if we have the list `[1, 2, 3]` and the list `[4, 5, 6]`, then appending those two lists will create `[1, 2, 3, 4, 5, 6]`.

```lean
def cappend {α : Type} (as bs : CustomList α) : CustomList α :=
  match as with
  | cnil => bs
  | ccons a as => ccons a (cappend as bs)
```

Example evaluations, make sure these come out to what you expect.

```lean
#eval cappend (ccons 1 cnil) (ccons 2 cnil)
#eval clength (cappend (ccons 1 cnil) (ccons 2 cnil))
```


### Theorems over Inductive Types

Now that we have a data structure and some methods over it. We can now prove some interesting properties.

First let's start off with the following theorem.

> Appending `cnil` to a list `as` is equivalent to the list `as`.

When instantiating an inductive type, the inductive hypothesis is created for it via `recOn`.
Therefore, we can rely on that for the proof.


```lean
theorem append_nil {α : Type} (as : CustomList α) : cappend as cnil = as := by
  -- Base Case
  have H_BASE : (cappend cnil cnil = (@cnil α)) := by rfl

  -- Inductive Step
  have H_Inducive : ∀ (hd : α) (tl : CustomList α), cappend tl cnil = tl → cappend (ccons hd tl) cnil = ccons hd tl := by
    intro (hd : α)
    intro (tl : CustomList α)
    intro (IH : cappend tl cnil = tl)
    calc
        cappend (ccons hd tl) cnil = ccons hd (cappend tl cnil) := by rw [cappend]
        _ = ccons hd tl := by rw [IH]

  -- Apply induction principle
  exact CustomList.recOn  (motive := fun x => cappend x cnil = x)
    as
    H_BASE
    H_Inducive
```

The `rewrite`/`rw` command allows us to replace instances of functions with their definitions. The goal is to get both sides of the equality to be syntactically the same.
The `calc` environment allows us to perform multiple rewrites in order to get closer to that end.


Instead of explicitly making use of `recOn`, we can use the `induction` tactic.

```lean
theorem append_nil2 {α : Type} (as : CustomList α) : cappend as cnil = as := by
  induction as

  case cnil =>
    calc
      cappend cnil cnil = cnil := by rw [cappend]
      _ = cnil := by exact rfl

  case ccons hd tl IH =>
    calc
      cappend (ccons hd tl) cnil = ccons hd (cappend tl cnil) := by rw [cappend]
      _ = ccons hd tl := by rw [IH]

```

### Double Induction

For our next example, we'll need to perform induction on two lists.

> Given two lists `as` and `bs`. The length of their append is the same as the length of each individual list added together.

```lean
theorem length_append_sum {α : Type} (as bs : CustomList α) : clength (cappend as bs) = clength as + clength bs := by
  induction as
  induction bs

  case cnil.cnil =>
    calc
      clength (cappend cnil cnil) = clength cnil := by rw [cappend]
      _ = 0 := by rw [clength]
      _ = 0 + 0 := by linarith
      _ = (clength cnil) + (clength cnil) := by rw [clength]

  case cnil.ccons hd tl _ =>
    calc
      clength (cappend cnil (ccons hd tl)) = clength (ccons hd tl) := by rw [cappend]
      _ = 0 + clength (ccons hd tl) := by linarith
      _ = clength cnil + clength (ccons hd tl) := by rw [clength]

  case ccons hd tl IH =>
    calc
      clength (cappend (ccons hd tl) bs) = clength (ccons hd (cappend tl bs)) := by rw [cappend]
      _ = 1 + clength (cappend tl bs) := by rw [clength]
      _ = 1 + (clength tl + clength bs) := by rw [IH]
      _ = (1 + clength tl) + clength bs := by linarith
      _ = clength (ccons hd tl) + clength bs := by rw [clength]

  -- Lean intelligently wlogs the fourth case
```

Notice that a couple times in the proof, make use of a tactic called `linarith`. This stands for "linear arithmetic" and helps solve goals involving numbers. I generally employ this rather than figuring out which definitions I need to perform commutativity and associativity rules.

## Conclusion

One of my favorite things about Lean is the ability to make proofs
more readable by making use of the `have`, `calc`, and `rewrite`
tactics. I do find it easier, however, to use the `induction` tactic
for inductive proofs. Especially when dealing with nested
inductions as writing out the cases explicitly can be daunting.

If you catch any mistakes in me converting this post, let me know.
Otherwise feel free to email me if you have any questions.

Lastly, I want to give my thanks to James Oswald for helping proofread
this post and making it better.
