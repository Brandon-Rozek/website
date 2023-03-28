---
title: "Lean 3 Tutorial"
date: 2023-03-27T13:27:32-04:00
draft: false 
tags: ["Formal Methods"]
math: true
medium_enabled: false
---

Lean is an interactive theorem prover created by Microsoft.
As part of the RPI logic group, I gave a tutorial introducing Lean and showcasing how to prove some statements within it.
This post aims to cover the concepts I went over at the time and can be used as an initial reference.

## Propositional Logic (Intuitionist Fragment)

To prove something in Lean, we need to construct an object of that type.

### Conjunctive Introduction
To start off let us prove the statement $P \wedge Q$ given both $P$ and $Q$ individually.

```lean
example {p q : Prop} (H_p : p) (H_q : q) : (p ∧ q) := begin
  show p ∧ q, from and.intro H_p H_q,
end
```

This shows an application of conjunctive introduction. We created the object $P \wedge Q$ by applying the hypothesis `and.intro` to both `H_p` which contains $P$ and `H_q` which contains $Q$.


Another way of going about this proof is by *transforming the goal to another equivalent one*.

```lean
example {p q : Prop} (H_p : p) (H_q : q) : (p ∧ q) := begin
  split,
  {
    show p, from H_p
  },
  {
    show q, from H_q
  }
end
```

In this proof, we make use of the `split` tactic. Given a conjunctive goal $P \wedge Q$, this tactic replaces it with two subgoals $P$ and $Q$. We can then apply the hypotheses to solve the problem.

### Conjunctive Elimination

Given the proof of $P \wedge Q$, we can derive $P$ from it.

```lean
example {p q : Prop} (H_pq : p ∧ q) : p := begin
  show p, from and.left H_pq,
end
```

In the example above, we apply the inference `and.left` to be able to derive the left side of a conjunct. Similarly to the last inference rule, there is a tactic based way to go about it. Tactic based methods are generally more prevalent within the ITP community. 

```lean
example {p q : Prop} (H_pq : p ∧ q) : p := begin
  cases H_pq with H_p H_q, -- p, q
  show p, from H_p,
end
```

Given a conjunctive hypothesis, the `cases` tactic will create two new hypothesis from it. The two labels after the `with` is to specify the names of these hypotheses. The string `--` denotes the start of a comment; I left a small comment to remind me the ordering of the conjuncts.

### Disjunctive Introduction

Given any statement $P$, we can introduce an arbitrary formula as a disjunct. More intuitively, if Jarold is above the age of 10, then he is above the age of 10 or he likes lolipops. It does not change the truth value of the statement.

The inference based way of representing this is as follows:

```lean
example {p q : Prop} (H_p : p) : (p ∨ q) := begin 
  show p ∨ q, from or.intro_left q H_p,
end
```

In the more popular tactic based notion. We use the tactic `left` or `right` to denote which side we're going to attempt to prove. If we're trying to prove $P \vee Q$ and we have $P$ then we will prove the left side.

```lean
example {p q : Prop} (H_p : p) : (p ∨ q) := begin 
  left,
  show p, from H_p,
end
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

To acheive this in Lean using the inference based approach.

```lean
example {p q r : Prop} (H_pr : p → r) (H_qr : q → r) (H_pq : p ∨ q) : r := begin
  show r, from or.elim H_pq H_pr H_qr,
end
```

Alternatively, via the tactic based approach

```lean
example {p q r : Prop} (H_pr : p → r) (H_qr : q → r) (H_pq : p ∨ q) : r := begin
  cases H_pq,
  case or.inl : H_p
  { -- Assume p
    show r, from H_pr H_p,
  },
  case or.inr : H_q
  { -- Assume q
    show r, from H_qr H_q,
  },
end
```

In the tactic based method the case labels are optional. 
If you are using the mathlib library, you can automatically
generate the labels using the `pretty_cases` command.


## Negation

Traditional interactive theorem provers such as Coq focused on the constructivist approach to theorem proving.
This allows them to export proofs as programs in OCaml.
Lean places less of an emphasis on this approach and instead supports the proof by contradiction style
you see in classical theorem proving. 

During the tutorial, I decided to make this distinction explicit by making use of the law of excluded middle. By default, Lean uses the axiom of choice which can then be used to derive the law of excluded middle, but I cut that part out for brevity.

In other words, if you want to perform a proof by contradiction, don't use the techniques shown in this section and instead use the `by_contradiction` tactic.

Declare the axiom of law of excluded middle:

```lean
axiom LEM {p : Prop}: p ∨ ¬ p
```

### Negation Introduction

For negation introduction, let's say we have some proposition $P$. If we can use $P$ to derive a falsity, let's say $Q \wedge \neg Q$ then $P$ must be false. That is, we introduce a negation to make it $\neg P$.

The structure of the proof will a proof by cases on the law of exclude middle.

```lean
example {p q : Prop} (H_pq : p → q) (H_pnq : p → ¬q) : ¬p := begin
  have H_LEM : p ∨ ¬p := LEM,

  -- Assuming ¬p derive ¬p
  have H_npp : ¬p → ¬p := by {
    assume H_np : ¬p,
    show ¬p, from H_np,
  },
  
  -- Assuming p derive ¬p
  have H_pp : p → ¬p := by {
    -- Use hypotheses to obtain q and ¬q
    assume H_p : p,
    have H_q : q := H_pq H_p,
    have H_nq : ¬q := H_pnq H_p,

    -- In Lean ¬q is the same as q → false
    have H_qf : q → false := H_nq,

    -- We have q, so we can derive a falsity
    have H_f : false := H_qf H_q,

    -- You can derive anything from false
    have H_UNUSED: p ∧ ¬p := false.rec (p ∧ ¬p) H_f,

    -- Including what we want, ¬p 
    show ¬p, from false.rec (¬p) H_f,
  },
  
  -- By proof by cases, we derive ¬p
  show ¬p, from or.elim H_LEM H_pp H_npp,
end
```

Alternatively, the tactic based approach

```lean
example {p q : Prop} (H_pq : p → q) (H_pnq : p → ¬q) : ¬p := begin
  have H_LEM : p ∨ ¬p := LEM,
  cases H_LEM,
  case or.inl : H_p
  {
    have H_q : q := H_pq H_p,
    have H_nq : ¬q := H_pnq H_p,
    have H_qf : q → false := H_nq,
    have H_f : false := H_qf H_q,
    show ¬p, from false.rec (¬p) H_f,
  },
  case or.inr : H_np
  { 
    show ¬p, from H_np,
  },
end
```

### Negation Elimination

One common representation of negation elimination is to remove any double negations.
That is $\neg \neg P$ becomes $P$.

We'll similarly show this by performing a proof by cases on the law of excluded middle.

```lean
example {p: Prop} (H_nnp : ¬¬p) : p := begin
  have H_LEM : p ∨ ¬p := LEM,

  -- Assuming p derive p
  have H_pp : p → p := by {
    assume H_p : p,
    show p, from H_p,
  },

  -- Assuming ¬p derive p
  have H_npp : ¬p → p := by {
    assume H_np : ¬p,

    -- Recall ¬p is the same as p → false
    have H_pff : (p → false) → false := H_nnp,
    have H_pf : p → false := H_np,

    -- Apply conditional elimination or modus ponens
    have H_f : false := H_pff H_pf,

    -- Derive our goal from a falsity
    show p, from false.rec p H_f,
  },

  -- By proof by cases, we derive p
  show p, from or.elim H_LEM H_pp H_npp,
end
```

Alternatively for the tactic based approach.

```lean
example {p: Prop} (H_nnp : ¬¬p) : p := begin
  have H_LEM : p ∨ ¬p := LEM,
  cases H_LEM,
  case or.inl : H_p
  { 
    show p, from H_p,
  },
  case or.inr : H_np
  { 
    have H_pff : (p → false) → false := H_nnp,
    have H_pf : p → false := H_np,
    have H_f : false := H_pff H_pf,
    show p, from false.rec p H_f,
    
  },
end
```

## First Order

Lean is also capable of reasoning over first order logic. In this section, we'll start seeing objects/terms and predicates instead of just propositions.

For example `{α : Type} {P : α → Prop} ` means that $P$ is a predicate of arity one and takes an object of type $\alpha$.


### Forall Elim

If we have a forall statement, then we can replace the bound variable with an object of that type and remove the forall. Lets say for our example we have the following forall statement: $\forall x \in \mathbb{N}: x \ge 0$. Then we can replace the $x$ with $2$ and get the following formula: $2 \ge 0$. 

```lean
example {α : Type} {P : α → Prop} {y : α} (H : ∀ x : α,  P(x)) : P(y) := begin
  show P y, from H y,
end
```

### Forall Intro

To show that some property holds for all $x$ of a certain type, you need to show that it holds
for an arbitrary $x$ of that type. We can introduce this object, by the command `assume x`. 

```lean
example {α : Type} {P Q R : α → Prop} (H_pq : ∀ x : α, P x → Q x) (H_qr : ∀ x : α, Q x → R x) : ∀ x : α, P x → R x := begin
  assume x,
  have H_pqx : P x → Q x := H_pq x,
  have H_qrx : Q x → R x := H_qr x,
  assume H_px : P x,
  have H_qx : Q x := H_pqx H_px,
  show R x, from H_qrx H_qx,
end
```

### Exists Intro

To introduce an existential, you need to show that the formula holds for any object of a certain type.

```lean
example {α : Type} {P : α → Prop} {y : α} (H: P y) : ∃ x: α, P x := begin
  show ∃ x: α, P x, from exists.intro y H,
end
```

In the tactic based approach, this is done via `existsi`:

```lean
example {α : Type} {P : α → Prop} {y : α} (H: P y) : ∃ x: α, P x := begin
  existsi y,
  show P y, from H,
end
```

### Exists Elim

Lets say we have the following forall statement: $\forall a \in \alpha: p a \implies b$.

Now lets say we have the follwing existential: $\exists x, p x$.

Using these, we can derive $b$.

```lean
example {α : Type} {p : α → Prop} {b : Prop} (H_epx : ∃ x, p x) (H_pab : ∀ (a : α), p a → b) : b := begin
  show b, from exists.elim H_epx H_pab,
end
```

Alternatively for the tactic based approach:

```lean
example {α : Type} {p : α → Prop} {b : Prop} (H_epx : ∃ x, p x) (H_pab : ∀ (a : α), p a → b) : b := begin
  cases H_epx with x H_px,
  have H_pxb := H_pab x,
  show b, from H_pxb H_px,
end

```

## Inductive Types

One of the biggest use cases of an interactive
theorem prover is in program verification.
To help represent recursive data strcutres, we
have the notion of an *inductive type*.

Let's create a custom representation of a list.
A list can either by empty (`cnil`) or be an element `hd` combined with the rest of some list `tl`.

```lean
inductive CustomList (T : Type)
| cnil : CustomList
| ccons (hd : T) (tl : CustomList) : CustomList
```

Some examples of a list here include `cnil`,
`ccons(0, cnil)`, and `ccons(1, ccons(0, cnil))`.

For convinience, we'll open the `CustomList` namespace
so that we don't have to refer each constructor
(`cnil`/`ccons`) by it.

```lean
open CustomList
```

### Functions over Inductive Typess

To define a function over an inductive type,
we need to cover each of the constructors.

For example, let's consider the notion of a list's
length.
- If the list is `cnil` then the length is $0$.
- If the list starts with `ccons` then we add 1 to the length of the tail `tl`.

```lean
def clength {α : Type}:  CustomList α → ℕ 
  | cnil := 0
  | (ccons b as) := 1 + clength as

```

We can see the output of a function via the `#eval` command.

```lean
#eval @cnil nat
#eval clength (ccons 2 (ccons 1 cnil))
```

For another example, let us look at appending two lists. As an example if we have the list `[1, 2, 3]` and the list `[4, 5, 6]`, then appending those two lists will create `[1, 2, 3, 4, 5, 6]`.

```lean
def cappend {α : Type} : CustomList α → CustomList α → CustomList α
  | cnil         bs := bs
  | (ccons a as) bs := ccons a (cappend as bs)
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

When instantiating an inductive type, the inductive hypothesis is created for it via `rec_on`.
Therefore, we can rely on that for the proof.


```lean
theorem append_nil2 {α : Type} (as : CustomList α) : cappend as cnil = as := begin
  -- Base Case
  have H_base : cappend cnil cnil = (@cnil α) := by {
    rewrite [cappend],
  },

  -- Inductive Step
  have H_ind : ∀ (hd : α) (tl : CustomList α), cappend tl cnil = tl → cappend (ccons hd tl) cnil = ccons hd tl
 := by {
    assume hd : α,
    assume tl : CustomList α,
    assume H : cappend tl cnil = tl,
    calc
      cappend (ccons hd tl) cnil = ccons hd (cappend tl cnil) : by rewrite [cappend]
      ... = ccons hd tl : by rewrite H,
  },

  -- Apply induction principle
  show cappend as cnil = as, from CustomList.rec_on as H_base H_ind,
end
```

The `rewrite` command allows us to replace instances of functions with their definitions. The goal is to get both sides of the equality to be syntactically the same.
The `calc` environment allows us to perform multiple rewrites in order to get closer to that end.


Instead of explicitely making use of `rec_on`, we can use the `induction` tactic.

```lean
theorem append_nil2 {α : Type} (as : CustomList α) : cappend as cnil = as := begin
  induction as,
  case CustomList.cnil
  { 
    show cappend cnil cnil = cnil, from by rewrite [cappend],
  },
  case CustomList.ccons : hd tl ih
  {
    -- Great for equational rewrite proofs
    calc
      cappend (ccons hd tl) cnil = ccons hd (cappend tl cnil) : by rewrite [cappend]
      ...                        = ccons hd tl : by rewrite [ih]
    ,
  },
end
```

Lean also supports writing the theorems in a similar inducive syntax as the definitions. Though to me it looks slightly confusing.

```lean
theorem append_nil3 {α : Type} : ∀ as : CustomList α, cappend as cnil = as
| (@cnil α) := show cappend cnil cnil = cnil, from by rewrite [cappend]
| (ccons hd tl) := show cappend (ccons hd tl) cnil = (ccons hd tl), from by {
    calc
      cappend (ccons hd tl) cnil = ccons hd (cappend tl cnil) : by rewrite [cappend]
      ...                        = ccons hd tl : by rewrite append_nil3
}
```

### Double Induction

For our next example, we'll need to perform induction on two lists.

> Given two lists `as` and `bs`. The length of their append is the same as the length of each individual list added together.

```lean

theorem length_append_sum {α : Type} (as bs : CustomList α) : clength (cappend as bs) = clength as + clength bs := begin
  induction as with aa ab ac,
  induction bs with ba bb bc,
  case CustomList.cnil
  {     
    calc
      clength (cappend cnil cnil) = clength (@cnil α) : by rewrite [cappend]
      ...                         = 0 : by rewrite [clength]
      ...                         = 0 + 0 : by linarith
      ...                         = clength cnil + clength cnil : by refl,
  
  },
  case CustomList.ccons : bs_hd bs_tl bs_ih
  { 
    calc
      clength (cappend (ccons bs_hd bs_tl) bs) = clength (ccons bs_hd (cappend bs_tl bs)) : by rewrite [cappend]
      ... = 1 + clength (cappend bs_tl bs) : by rewrite [clength]
      ... = 1 + (clength bs_tl + clength bs) : by rewrite bs_ih
      ... = (1 + clength bs_tl) + clength bs : by linarith
      ... = clength (ccons bs_hd bs_tl) + clength bs : by rewrite [clength],
  },
  case CustomList.ccons : bs_hd bs_tl bs_ih
  { 
    calc
      clength (cappend cnil (ccons bs_hd bs_tl)) = clength (ccons bs_hd bs_tl) : by rewrite [cappend]
      ... = 0 + clength (ccons bs_hd bs_tl) : by linarith
      ... = clength cnil + clength (ccons bs_hd bs_tl) : by refl,
  },
  -- It intelligently wlogs the fourth case
end
```

In the alternative inductive style:

```lean
theorem length_append_sum2 {α : Type}: ∀ (as bs : CustomList α), clength (cappend as bs) = clength as + clength bs
| cnil cnil := by {
      calc
      clength (cappend cnil cnil) = clength (@cnil α) : by rewrite [cappend]
      ...                         = 0 : by rewrite [clength]
      ...                         = 0 + 0 : by linarith
      ...                         = clength cnil + clength cnil : by refl,
}
| (ccons hd tl) bs := by {
      calc
      clength (cappend (ccons hd tl) bs) = clength (ccons hd (cappend tl bs)) : by rewrite [cappend]
      ... = 1 + clength (cappend tl bs) : by rewrite [clength]
      ... = 1 + (clength tl + clength bs) : by rewrite length_append_sum2
      ... = (1 + clength tl) + clength bs : by linarith
      ... = clength (ccons hd tl) + clength bs : by rewrite [clength],
}
| cnil (ccons hd tl) := by {
      calc
      clength (cappend cnil (ccons hd tl)) = clength (ccons hd tl) : by rewrite [cappend]
      ... = 0 + clength (ccons hd tl) : by linarith
      ... = clength cnil + clength (ccons hd tl) : by refl,
}
```

Notice that a couple times in the proof, make use of a tactic called `linarith`. This stands for "linear arithmetic" and helps solve goals involving numbers. I generally employ this rather than figuring out which definitions I need to perform commutativity and associativity rules.

## Conclusion

That concludes the examples I gave for my talk. For each proof, you can see that I included at least two different ways of going about proving it. I generally prefer the inference style method where we explicitely call on `Or.elim` and the like. Though when it comes to double induction, I have not figured out how to apply `rec_on` multiple times in a clean way. 

In the process of making this tutorial, I released other lean posts. One that I recommend checking out is ["Readable Lean 3 Proofs"](/blog/readable-lean3-proofs). In it, I give my opinions on how to make the written out proofs more human friendly.
