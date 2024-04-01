---
title: "Working with integer sets in Lean 4"
date: 2024-03-31T21:10:23-04:00
draft: false
tags: ["Formal Methods"]
math: true
medium_enabled: false
---

Recently I was convinced by [James Oswald](https://jamesoswald.dev/) to work with him on proving some lemmas about specific integer sets in Lean 4. Since we have different styles in going about Lean proofs, I present my version here.

We'll go over three proofs today:

- $\\{x \mid x \in \mathbb{Z} \wedge x^2 = 9\\} = \\{-3, 3\\}$
- $\\{x \mid x \in \mathbb{Z} \wedge -4 \le n \wedge n \le 15 ∧ Even~n \\} = \\{-4, -2, 0, 2, 4, 6, 8, 10, 12, 14\\}$
- $\\{x \mid x \in \mathbb{Z} \wedge x^2 = 6\\} = \emptyset$

## Example 1

First, let's define our set $A$

```lean4
def A : Set Int := {x : Int | x^2 = 9}
```

We want to prove the following lemma:

```lean4
lemma instA : A = ({3, -3} : Finset ℤ)
```

Recall that for sets, $A = S \iff A \subseteq S \wedge S \subseteq A$.

Since we're given a specific Finset for $S$, it would be really nice if we can compute whether $S$ is a subset of $A$. In fact we can, as long as we prove a couple theorems first.

```lean4
instance (n: Int) : Decidable (n ∈ A) := by
  suffices Decidable (n^2 = 9) by
    rewrite [A, Set.mem_setOf_eq]
    assumption
  apply inferInstance
```

First as shown above, we need to decide whether an integer is in $A$. Given how $A$ is defined, this is equivalent to seeing if $n^2 = 9$. Luckily for us, the core of Lean already has a decision procedure for this. We can have Lean apply the appropriate one by calling `apply inferInstance`.

With this, we can now use `#eval` to see if elements are in $A$ or not.

```lean4
#eval List.Forall (· ∈ A) [-3, 3]
```

To say that a finite set $S$ is a subset of $A$, is to say that all the elements of $S$ are in $A$. Using the last theorem, we can prove that checking subsets in this direction is decidable.

```lean4
instance (S : Finset Int) : Decidable (↑S ⊆ A) := by
  rewrite [A]
  rewrite [Set.subset_def]
  show Decidable (∀ x ∈ S, x ∈ {x | x ^ 2 = 9})
  apply inferInstance
```

Keep in mind that at this point it's not necessarily decidable if $A \subseteq S$. This is because we haven't established if $A$ is finite. However instead of trying to prove finiteness, let's skip to the main proof and show that $A = \\{3, -3\\}$ classically.

```lean4
lemma instA : A = ({3, -3} : Finset ℤ) := by
  let S : Finset ℤ := {3, -3}
  change (A = ↑S)
```

As stated before, set equality is making sure both are subsets of each other

```lean4
suffices A ⊆ ↑S ∧ ↑S ⊆ A by
  rewrite [Set.Subset.antisymm_iff]
  assumption
```

Lets make use of our decidability proof to show $S \subseteq A$ in one line!

```lean4
have H2 : ↑S ⊆ A := by decide
```

For the other side,

```lean4
have H1 : A ⊆ ↑S := by
  intro (n : ℤ)
  -- Goal is now (n ∈ A → n ∈ {3, -3})
  intro (H1_1: n ∈ A)
```

Let's change `H1_1` to be in a form easier to work with

```lean4
have H1_1 : n^2 = 9 := by
  rewrite [A, Set.mem_setOf_eq] at H1_1
  assumption
```

To show that $n \in \\{3, -3\\}$, then it's the same as saying that $n = 3$ or $n = -3$.

```lean4
suffices n = 3 ∨ n = -3 by
  show n ∈ S
  rewrite [Finset.mem_insert, Finset.mem_singleton]
  assumption
```

We can show this using a theorem from mathlib!

```lean4
exact eq_or_eq_neg_of_sq_eq_sq n 3 H1_1
```

[(Quite the long name...)](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/GroupPower/Ring.html#eq_or_eq_neg_of_sq_eq_sq)

Lastly, we combine the two subset proofs to show equality

```lean4
exact And.intro H1 H2
```

All together the proof looks like:

```lean4
lemma instA : A = ({3, -3} : Finset ℤ) := by
  let S : Finset ℤ := {3, -3}
  change (A = ↑S)

  suffices A ⊆ ↑S ∧ ↑S ⊆ A by
    rewrite [Set.Subset.antisymm_iff]
    assumption

  have H1 : A ⊆ ↑S := by
    intro (n : ℤ)
    -- Goal is now (n ∈ A → n ∈ {3, -3})
    intro (H1_1: n ∈ A)
    have H1_1 : n^2 = 9 := by
      rewrite [A, Set.mem_setOf_eq] at H1_1
      assumption

    suffices n = 3 ∨ n = -3 by
      show n ∈ S
      rewrite [Finset.mem_insert, Finset.mem_singleton]
      assumption

    exact eq_or_eq_neg_of_sq_eq_sq n 3 H1_1

  have H2 : ↑S ⊆ A := by decide

  exact And.intro H1 H2
```

## Example 2

We got to cheat a little by applying a `mathlib` theorem in the last example. This one will require a little more technique. First, let's start by defining our set $B$.

```lean4
def B : Set Int := {n | -4 ≤ n ∧ n ≤ 15 ∧ n % 2 = 0}
```

As before, we can show that set membership in $B$ is decidable. We can make use of the fact that each condition within it is decidable through `And.decidable`.

```lean4
instance (n : Int) : Decidable (n ∈ B) := by
  suffices Decidable (-4 ≤ n ∧ n ≤ 15 ∧ n % 2 = 0) by
    rewrite [B, Set.mem_setOf_eq]
    assumption

  exact And.decidable
```

Sanity check to see that everything works as expected.

```lean4
#eval List.Forall (· ∈ B) [-4, -2, 0, 2, 4, 6, 8, 10, 12, 14]
```

We can also show that checking if a finset is a subset of $B$ is decidable.

```lean4
instance (S : Finset Int) : Decidable (↑S ⊆ B) := by
  suffices Decidable (∀ x ∈ S, -4 ≤ x ∧ x ≤ 15 ∧ x % 2 = 0) by
    rewrite [Set.subset_def, B]
    assumption
  apply inferInstance
```

The beginning of our proof stays the same

```lean4
lemma instB : B = ({-4, -2, 0, 2, 4, 6, 8, 10, 12, 14} : Finset Int) := by
  let S : Finset Int := {-4, -2, 0, 2, 4, 6, 8, 10, 12, 14}
  change (B = ↑S)

  -- To show equality, we need to show that
  -- each is a subset of each other
  suffices ((B ⊆ ↑S) ∧ (↑S ⊆ B)) by
    rewrite [Set.Subset.antisymm_iff]
    assumption
 
  have H2 : ↑S ⊆ B := by decide
```

For the other direction we want to show that is $n$ meets the condition to be in $B$, then it must be in $S$.

```lean4
have H1 : B ⊆ ↑S := by
  intro (n : ℤ)
  intro (H : n ∈ B)

  have H1 : -4 ≤ n ∧ n ≤ 15 ∧ n % 2 = 0 := by
    rewrite [B] at H; assumption
  clear H

  show n ∈ S
```

Since $S$ is a finset, we can say that $n$ must be equal to one of the elements of $S$. 

```lean4
repeat rewrite [Finset.mem_insert]
rewrite [Finset.mem_singleton]
```

At this point, the problem is integer arithmetic and we can call the `omega` tactic to finish the subproof.

```lean4
omega
```

With both sides subset proven, we use and introduction to prove the goal

```lean4
exact show ((B ⊆ ↑S) ∧ (↑S ⊆ B)) from And.intro H1 H2
```

The full proof is below.

```lean4
lemma instB : B = ({-4, -2, 0, 2, 4, 6, 8, 10, 12, 14} : Finset Int) := by
  let S : Finset Int := {-4, -2, 0, 2, 4, 6, 8, 10, 12, 14}
  change (B = ↑S)

  -- To show equality, we need to show that
  -- each is a subset of each other
  suffices ((B ⊆ ↑S) ∧ (↑S ⊆ B)) by
    rewrite [Set.Subset.antisymm_iff]
    assumption

  have H1 : B ⊆ ↑S := by
    intro (n : ℤ)
    intro (H : n ∈ B)

    have H1 : -4 ≤ n ∧ n ≤ 15 ∧ n % 2 = 0 := by
      rewrite [B] at H; assumption
    clear H

    show n ∈ S
    repeat rewrite [Finset.mem_insert]
    rewrite [Finset.mem_singleton]
    omega

  have H2 : ↑S ⊆ B := by decide

  exact show ((B ⊆ ↑S) ∧ (↑S ⊆ B)) from And.intro H1 H2
```

## Example 3

Finally let's define our last set.

```lean4
def C : Set Int := {n | n^2 = 6}
```

We're aiming to show that $C$ is equivalent to the empty set. Therefore, we don't have a need to show decidability for membership or finite subsets. We can't make use of the mathlib theorem from Example 1, so how will we go about proving this?

Analyzing the last example more carefully, we had upper and lower bounds to work with. We can similarly identify these bounds for this example.

Let's define the integer squared to be the upper bound.

```lean4
lemma IntPow2GeSelf (H : (a : Int)^2 = z) : a ≤ z := by
  have H1 : a ≤ a ^ 2 := Int.le_self_sq a
  rewrite [H] at H1
  assumption
```

For the lower bound, take its negation.

```lean4
lemma NegIntPow2LeSelf (H : (a : Int)^2 = z) : a ≥ -z := by
```

To prove the lower bound, split up between positives and negatives using the law of excluded middle

```lean4
have H1 : a ≥ 0 ∨ a < 0 := le_or_lt 0 a
```

For a positive $a$, we can rely on the `linarith` tactic

```lean4
have H_LEFT : a ≥ 0 → a ≥ -z := by
  have HL1 : a ≤ z := IntPow2GeSelf H
  intro (HL2 : a ≥ 0)
  linarith
```

For a negative $a$, we need to prove it by induction

```lean4
have H_RIGHT : a < 0 → a ≥ -z := by
  intro (HR1: a < 0)
  have HR1 : a ≤ -1 := Int.le_sub_one_iff.mpr HR1
  revert HR1

  suffices a ≤ -1 → a ≥ -(a^2) by
    rewrite [<- H]; assumption

  let P : ℤ → Prop := fun x => x ≥ -(x^2)

  have H_base : P (-1) := by decide

  have H_ind : ∀ (n : ℤ), n ≤ -1 → P n → P (n - 1) := by
    intro (n : ℤ)
    intro (H21 : n ≤ -1)
    intro (H22 : P n)
    simp_all
    linarith

  exact Int.le_induction_down H_base H_ind a
```

We have shown that this lower bound holds for both positive and negative $a$, therefore we can show that it holds for all $a$.

```lean4
exact Or.elim H1 H_LEFT H_RIGHT
```

All together the lower bound proof is the following

```lean4
lemma NegIntPow2LeSelf (H : (a : Int)^2 = z) : a ≥ -z := by
  have H1 : a ≥ 0 ∨ a < 0 := by omega

  have H_LEFT : a ≥ 0 → a ≥ -z := by
    have HL1 : a ≤ z := IntPow2GeSelf H
    intro (HL2 : a ≥ 0)
    linarith

  have H_RIGHT : a < 0 → a ≥ -z := by
    intro (HR1: a < 0)
    have HR1 : a ≤ -1 := Int.le_sub_one_iff.mpr HR1
    revert HR1

    suffices a ≤ -1 → a ≥ -(a^2) by
      rewrite [<- H]; assumption

    let P : ℤ → Prop := fun x => x ≥ -(x^2)

    have H_base : P (-1) := by decide

    have H_ind : ∀ (n : ℤ), n ≤ -1 → P n → P (n - 1) := by
      intro (n : ℤ)
      intro (H21 : n ≤ -1)
      intro (H22 : P n)
      simp_all
      linarith

    exact Int.le_induction_down H_base H_ind a


  exact Or.elim H1 H_LEFT H_RIGHT
```

With our lower and upper bounds in place, we can look at the original problem. That is, we want to prove that $C = \emptyset$. We'll start the same proof like before.

```lean4
example : C = (∅ : Set Int) := by
  suffices C ⊆ ∅ ∧ ∅ ⊆ C by
    rewrite [Set.Subset.antisymm_iff]
    assumption
  have H2 : ∅ ⊆ C := Set.empty_subset C
```

We start the other direction the same as well.

```lean4
have H1 : C ⊆ ∅ := by
  intro (n : ℤ)
  intro (H1_1 : n ∈ C)
  have H1_1 : n^2 = 6 := by
    rewrite [C, Set.mem_setOf_eq] at H1_1
    assumption
```

Now bring in our bounds

```lean4
have H1_2 : n ≤ 6 := by apply IntPow2GeSelf H1_1
have H2_3 : n ≥ -6 := by apply NegIntPow2LeSelf H1_1
```

We can use `omega` to show that if the integer is within these bounds then $n$ must equal one of the integers. 

```lean4
have H1_4 :  n ∈ ({-6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6} : Finset ℤ) := by
  repeat rewrite [Finset.mem_insert]
  rewrite [Finset.mem_singleton]
  omega
```

Turn this set into a disjunction

```lean4
-- Make H1_4 a disjunction (n = -6 ∨ ... ∨ n = 6)
repeat rewrite [Finset.mem_insert] at H1_4
rewrite [Finset.mem_singleton] at H1_4
```

Trying to show that $n$ is within the empty set is the same as trying to prove a contradiction

```lean4
show False
```

So let's go through each disjunct in `H1_4` and show that we derive a contradiction.

```lean4
repeat (
  cases' H1_4 with H1_4H H1_4
  -- Plug in n = ?? to n^2 = 6
  rewrite [H1_4H] at H1_1
  contradiction
)
```

The last $n = 6$ is under a different name

```lean4
rewrite [H1_4] at H1_1
contradiction
```

We can finally put it all together with and introduction

```lean4
exact show C ⊆ ∅ ∧ ∅ ⊆ C from And.intro H1 H2
```

All together it's the following:

```lean4
example : C = (∅ : Set Int) := by

  suffices C ⊆ ∅ ∧ ∅ ⊆ C by
    rewrite [Set.Subset.antisymm_iff]
    assumption

  have H1 : C ⊆ ∅ := by
    intro (n : ℤ)
    intro (H1_1 : n ∈ C)
    have H1_1 : n^2 = 6 := by
      rewrite [C, Set.mem_setOf_eq] at H1_1
      assumption

    show False

    have H1_2 : n ≤ 6 := by apply IntPow2GeSelf H1_1
    have H2_3 : n ≥ -6 := by apply NegIntPow2LeSelf H1_1


    have H1_4 :  n ∈ ({-6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6} : Finset ℤ) := by
      repeat rewrite [Finset.mem_insert]
      rewrite [Finset.mem_singleton]
      omega

    -- Make H3 a disjunction (n = -6 ∨ ... ∨ n = 6)
    repeat rewrite [Finset.mem_insert] at H1_4
    rewrite [Finset.mem_singleton] at H1_4

    -- Try each one, plug in n = a into n^2 = 6 and show it doesn't work
    repeat (
      cases' H1_4 with H1_4H H1_4
      rewrite [H1_4H] at H1_1
      contradiction
    )

    -- Last n = 6 has a different name
    rewrite [H1_4] at H1_1
    contradiction


  have H2 : ∅ ⊆ C := Set.empty_subset C

  exact show C ⊆ ∅ ∧ ∅ ⊆ C from And.intro H1 H2
```

## Conclusion

We gave three examples on working with finite integer sets. The two key lessons from this post are:

**1. If the set is equal to a non-empty finite set, then try to prove decidability of membership and if a finset is a subset of it.**

If you're looking at a set of integers and this set is constructed with conditions that are mostly built-in (such as the `<` relation), then this is hopefully not too difficult. Unfold the definitions of your set using `rewrite` and have Lean auto-infer which decidability instance to call using `apply inferInstance`

**2. Try to establish a lower and upper bound for the elements of your set.**

This gives the `omega` tactic something additional to work with. In the second example, `omega` was able to close out the goal completely given the linear inequalities presented. In our last example, we only used `omega` to construct a finite set of possible integers.

If you develop any other general techniques for dealing with integer sets let me know. Otherwise, feel free to get in touch with any questions you have.

