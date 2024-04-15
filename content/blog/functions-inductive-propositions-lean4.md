---
title: "Functions and Inductive Propositions in Lean 4"
date: 2024-04-14T19:25:52-04:00
draft: false
tags: ["Formal Methods"]
math: true
medium_enabled: false
---

This blog post is inspired by the book [Logical Foundations](https://softwarefoundations.cis.upenn.edu/lf-current/index.html) where it goes over similar content in the Coq proof assistant. Instead, we will look at Lean 4.

Functions in Lean are required to be total and terminating. This means that there are some mathematical functions that cannot be represented. An example of which is the collatz conjecture.

```lean
def collatz_fail (n : Nat) : Nat :=
  match n with
  | (0: Nat) => (0: Nat)
  | (1: Nat) => (1: Nat)
  | x =>
      if x % 2 = 0 then collatz_fail (x / 2)
      else collatz_fail (3 * x + 1)
```

If you type the above function in Lean, you'll get the following error:

```
fail to show termination for
  collatz_fail
```

I can't tell you how we would go about showing termination. After all, many brilliant mathematicians are attempting to solve this [conjecture](https://en.wikipedia.org/wiki/Collatz_conjecture). Instead, we can represent the collatz procedure as an inductive proposition.

```lean
inductive collatz : Nat → Nat → Prop where
  | c0 : collatz 0 0
  | c1 : collatz 1 1
  | ceven (n r : Nat) : ¬(n = 0) → n % 2 = 0 → collatz (n / 2) r → collatz n r
  | codd (n r : Nat) : ¬(n = 1) → ¬(n % 2 = 0) → collatz (3 * n + 1) r → collatz n r
```

Our inductive proposition `collatz` is built with the first argument representing our input `n` and the second argument representing the result. Note that the first two constructors `c0` and `c1` denote the base cases. The second two constructors `ceven` and `codd` have various conditions on them:

- For `ceven`, we first require that $n \ne 0$, and that $n$ is even.  If that's the case, then whatever `r` is in the inductive proposition `collatz (n / 2) r`, that `r` will be the result in `collatz n r`.
- Similarly, for `codd`, the inductive proposition requires that $n \ne 1$ and that $n$ is odd. Then `r` holds whatever value `collatz (3 * n + 1) r` holds.

To use this inductive proposition, we need to build up a proof.

```lean
example : collatz 5 1 := by
  apply collatz.codd; trivial; trivial
  show collatz 16 1
  apply collatz.ceven; trivial; trivial
  show collatz 8 1
  apply collatz.ceven; trivial; trivial
  show collatz 4 1
  apply collatz.ceven; trivial; trivial
  show collatz 2 1
  apply collatz.ceven; trivial; trivial
  show collatz 1 1
  apply collatz.c1
```

For inductive propositions, Lean does not require that it's definition is total or terminating. In fact, in general perhaps a different ordering of constructors can be called in order to produce two different results for `r`! Our specific definition, however, only produces one `r` for a given `n`, and we can prove that in Lean.

```lean
theorem collatz_deterministic (n r1 r2: Nat) (H1: collatz n r1) (H2: collatz n r2) : r1 = r2 := by
  revert r2
  -- Look at each of the possible
  -- constructors for collatz
  induction H1
  case c0 =>
    intro r
    intro (H: collatz 0 r)
    cases H
    case c0 => rfl
    -- automatically detects c1 as a contradiction
    case ceven => contradiction
    case codd => contradiction

  case c1 =>
    intro r
    intro (H: collatz 1 r)
    cases H
    -- automatically detects c0 as a contradiction
    case c1 => rfl
    case ceven => contradiction
    case codd => contradiction

  case ceven n r1 N0 NE H IH =>
    -- N0 : n ≠ 0
    -- NE : n % 2 = 0
    -- IH : ∀ (r2 : ℕ), collatz (n / 2) r2 → r1 = r2
    intro r2
    intro (H: collatz n r2)
    cases H
    case c0 => contradiction
    case c1 => contradiction
    case ceven H2 => apply IH r2 H2
    case codd => contradiction

  case codd n r1 N1 NO H IH =>
    -- N1 : n ≠ 1
    -- NO : n % 2 = 1
    -- IH : ∀ (r2 : ℕ), collatz (3 * n + 1) r2 → r1 = r2
    intro r2
    intro (H: collatz n r2)
    cases H
    case c0 => contradiction
    case c1 => contradiction
    case ceven => contradiction
    case codd H2 => apply IH r2 H2
```

This means that we don't have to worry about calling the wrong constructor. If it fails, we backtrack and try a different one. This leads to an effective proof strategy:

```lean
example : collatz 5000 1 := by
  repeat (first |
    apply collatz.c0 |
    apply collatz.c1 |
    apply collatz.codd; trivial; trivial; simp |
    apply collatz.ceven; trivial; trivial; simp
  )
```

Let's return to our function `collatz_fail`. The reason this function didn't work is that it wasn't obvious that the function terminates. We can force it to terminate by introducing a new variable `t` that denotes the number of remaining steps before giving up and returning `none`.

```lean
def collatz_fun (n t : Nat) : Option Nat :=
  if t = 0 then none else
  match n with
  | (0: Nat) => (0: Nat)
  | (1: Nat) => (1: Nat)
  | x =>
      if x % 2 = 0 then collatz_fun (x / 2) (t - 1)
      else collatz_fun (3 * x + 1) (t - 1)
```

Instead of having to do the proof search from above, we can call `eval` on this function

```lean
#eval collatz_fun 5 6
#eval collatz_fun 5000 29
```

Is there any relationship between the inductive proposition version and the function we just built? Ideally we would want to prove the following relationship:
$$
\exists t, collatzfun(n , t) = some(r) \iff collatz(n, r)
$$
Since we don't know how to show whether collatz terminates, we can't at this time prove the backwards direction. We can, however, prove the forward direction through induction on the number of steps.

```lean 
theorem collatz_sound (n r : Nat) : (∃ t, collatz_fun n t = some r) → collatz n r := by
  intro (H: ∃ t, collatz_fun n t = some r)
  cases' H with t H
  revert H n r
  show ∀ (n r : Nat), collatz_fun n t = some r → collatz n r

  let motive := fun x : Nat => ∀ (n r: Nat), collatz_fun n x = some r → collatz n r

  apply Nat.recOn (motive := motive) t

  -- t = 0
  case intro.zero =>
    intro r n
    intro (HFalse : collatz_fun r 0 = some n)
    contradiction

  -- t = S t1
  case intro.succ =>
    intro t
    intro (IH : ∀ (n r : ℕ), collatz_fun n t = some r → collatz n r)
    intro n r
    intro (H : collatz_fun n (t + 1) = some r)
    show collatz n r

    unfold collatz_fun at H
    -- Go into else case since (t1 + 1 ≠ 0)
    simp [ite_false] at H
    -- Consider each case for n
    split at H

    -- n = 0
    case h_1 =>
        -- H : some 0 = some r
        have H : 0 = r := by
          rewrite [Option.some.injEq] at H; assumption
        suffices collatz 0 0 by
          rewrite [<- H]; assumption
        apply collatz.c0

    -- n = 1
    case h_2 =>
        -- H : some 1 = some r
        have H : 1 = r := by
          rewrite [Option.some.injEq] at H; assumption
        suffices collatz 1 1 by
          rewrite [<- H]; assumption
        apply collatz.c1

    case h_3 N0 N1 =>
      -- N0 : n ≠ 0
      -- N1 : n ≠ 1
      split at H
      -- n % 2 = 0
      case inl NE =>
      	-- NE : n % 2 = 0
        -- H : collatz_fun (n / 2) t = some r
        suffices collatz (n / 2) r by
          apply collatz.ceven n r N0 NE; assumption
        apply IH (n / 2) r H

      -- n % 2 = 1
      case inr NO =>
      	-- NO : n % 2 = 1
        -- H : collatz_fun (3 * n + 1) t = some r
        suffices collatz (3 * n + 1) r by
          apply collatz.codd n r N1 NO; assumption
        apply IH (3 * n + 1) r H

```

