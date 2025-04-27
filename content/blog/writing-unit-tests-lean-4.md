---
title: "Writing Unit Tests in Lean 4"
date: 2024-08-05T20:43:52-07:00
draft: false
tags: ["Formal Methods"]
math: false
medium_enabled: false
---

When writing Lean code, it's easier to iterate with unit tests than to prove properties about the function off the bat.

I mean if the unit test doesn't even pass, why bother with the proof?

Luckily, Lean 4 let's us do unit tests with a cool command called `#guard`

```lean4
#guard 1 = 1
```

This checks whether the following expression evaluates to `true`. Note that this does not provide a proof since this check is done using the untrusted evaluator.

What does need to be proven, however, is that the expression given is decidable.

One issue I faced is that I often use the `Except` type for error handling in my code. 

```lean4
inductive Except (ε : Type u) (α : Type v) where
  /-- A failure value of type `ε` -/
  | error : ε → Except ε α
  /-- A success value of type `α` -/
  | ok    : α → Except ε α
```

For a simple (somewhat silly) example, look at the following function

```lean4
def gt_0 (n : Nat) : Except String Bool :=
  if n = 0 then .error s!"{n} is not greater than zero"
  else .ok true
```

We can evaluate our function on a given input:

```lean4
#eval gt_0 1 -- Except.ok true
```

However, we can't guard against it without encountering an error. This is because we haven't shown that the equality is decidable.

To help with this, I wrote up a function that we can apply generically.

```lean4
def Except.deq [DecidableEq α] [DecidableEq β] : DecidableEq (Except α β) := by
  unfold DecidableEq
  intro a b
  cases a <;> cases b <;>
  -- Get rid of obvious cases where .ok != .err
  try { apply isFalse ; intro h ; injection h }
  case error.error c d =>
    match decEq c d with
      | isTrue h => apply isTrue (by rw [h])
      | isFalse _ => apply isFalse (by intro h; injection h; contradiction)
  case ok.ok c d =>
    match decEq c d with
      | isTrue h => apply isTrue (by rw [h])
      | isFalse _ => apply isFalse (by intro h; injection h; contradiction)
```

We can then show that equality of `Except String Bool` is decidable, since Lean already knows that string and boolean equality is decidable.

```lean4
instance: DecidableEq (Except String Bool) := Except.deq
```

From here, we can use `#guard` 

```lean4
#guard gt_0 1 = (Except.ok true)
```

When a `#guard` fails, it will throw an error during compilation. This is great for ensuring that our unit tests pass during compilation.

