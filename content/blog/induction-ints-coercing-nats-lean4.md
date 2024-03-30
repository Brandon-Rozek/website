---
title: "Coercing Ints to Nats for Induction in Lean 4"
date: 2024-03-27T21:51:02-04:00
draft: false
tags: ["Formal Methods"]
math: true
medium_enabled: false
---

Warning: This post is what happens when I solve a problem that's already solved within Mathlib. I find it interesting enough to share though. Hopefully this will inspire techniques to use within your own proofs.

---

Before getting into how to do induction on integers through nat coercion, let's discuss the proper way of solving this problem using `mathlib`.

Let $x$ be an integer greater than some integer $m$. Show that $x$ satisfies some property. For example, prove $x > -5 \rightarrow x > -10$.

Okay, I hear you, `linarith` can do this for us. Let's pretend that doesn't exist for now and show how we can go about solving this using `mathlib`.

```lean4
example (x : ℤ):  x > -5 → x > -10 := by
  -- Int.le_induction expects something of the form m ≤ x → ...
  show -4 ≤ x → x > -10
	
  -- Int.le_induction doesn't let you specify the
  -- motive so you need to make it easy for it to induce
  let P : ℤ → Prop := fun x => x > -10
	
  -- Base Case
  have H_base : P (-4) := by decide
	
  -- Inductive case
  have H_ind : ∀ (n : ℤ), -4 ≤ n → P n → P (n + 1) := by
    intro (n : ℤ)
    intro (HH1 : -4 ≤ n)
    intro (HH2 : n > -10)
    show n + 1 > -10
    exact lt_add_of_lt_of_pos HH2 (show 0 < 1 by decide)
   
 -- Use the induction principle
 exact show (-4 ≤ x → x > -10) from Int.le_induction H_base H_ind x
```

`Int.le_induction` is a nice and clean solution which I highly recommend you use. It makes sense too, prove that the property works for the lower bound and then prove the induction case holds.

Now what if for some reason you couldn't rely `Int.le_induction` and you wanted to find another way to go about this? This is where coercion comes in.

Starting from the beginning of the proof, this time let's introduce the hypothesis.

```lean
intro (H : x > -5)
```

Now we want to create a natural number which we'll perform induction over. Similar to the mathlib proof, we want to start with the lower bound as the base case. Therefore, make it so when $x$ is the lower bound our new natural number variable $n$ is 0.

```lean4
let n : ℕ := Int.toNat (x + 5)
```

Our goal `x > -10` is still written in terms of the original variable $x$. To rewrite this, we'll need to prove the following relationship:

```lean4
have H1 : x = n - 5 := by
  -- We should start off by saying this relationship
  -- holds for the integer version of n
  let nz : ℤ := x + 5
  have H1_1 : x = nz - 5 := eq_sub_of_add_eq (show nz = x + 5 by rfl)
  suffices nz - 5 = n - 5 by rewrite [H1_1]; assumption

  -- Through congruence closure we can ignore the (- 5)
  suffices nz = n by
    let Minus5 : ℤ → ℤ := fun x => x - 5
    show Minus5 nz = Minus5 n
    exact congrArg Minus5 this

  -- An integer coercion is only equal to a nat
  -- if the integer was 0 or positive to begin with
  have H1_2 : nz ≥ 0 := by
    have H : nz - 5 > 0 - 5 := by rewrite [<- H1_1]; assumption
    have H1 : nz - 5 ≥ 0 - 5 := Int.le_of_lt H
    exact (Int.add_le_add_iff_right (-5)).mp H1

  exact show nz = n from (Int.toNat_of_nonneg H1_2).symm
```

With $x$ written in terms of $n$, we can now rewrite our goal using our natural number.

```lean4
suffices n - 5 > (-10: ℤ) by rewrite [H1]; assumption
```

Here's the rest of the induction. Of course like before, I avoid  the use of `linarith` so I wouldn't be cheating ;)

```lean4
have H_base : 0 - 5 > -10 := by decide

have H_ind : ∀ n : ℕ, n - 5 > (-10 : ℤ) → (n + 1) - 5 > (-10: ℤ) := by
  intro n
  intro (IH : n - 5 > (-10 : ℤ))
  have IH : (-10: ℤ) < n - 5 := IH
  show (-10: ℤ) < n + 1 - 5

  have IH_2 : n + 1 - (5: ℤ) = n + (-5 : ℤ) + 1 := by calc
    n + 1 - (5: ℤ) = n + 1 + (-5 : ℤ) := rfl
    _ = n + (1 + (-5: ℤ))  := Int.add_assoc (↑n) 1 (-5)
    _ = n + ((-5 : ℤ) + 1) := rfl
    _ = n + (-5 : ℤ) + 1 := (Int.add_assoc (↑n) (-5) 1).symm
    _ = n - (5: ℤ) + 1 := rfl

  suffices -10 < n - (5: ℤ) + 1 by rewrite [IH_2]; assumption

  exact lt_add_of_lt_of_pos IH (show 0 < 1 by decide)

exact show n - 5 > (-10: ℤ) from Nat.recOn
  (motive := fun x: ℕ => x - (5 : ℤ) > (-10: ℤ))
  n
  H_base
  H_ind
```

This version is slightly longer than the `Int.le_induction` version as we had to carry forward the `- 5` portion of the equations. While it might not make sense in the integer case to perform this coercion, I'm hopeful that I can use a technique similar to this on other inductive types in the future.

Let me know if you end up using this or if you have any other cool induction techniques in your tool belt. Until next time.
