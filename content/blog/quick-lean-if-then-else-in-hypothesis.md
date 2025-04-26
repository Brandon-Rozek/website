---
title: "Quick Lean: if-then-else statement in hypothesis"
date: 2025-04-26T10:58:42-04:00
draft: false
tags: []
math: false
medium_enabled: false
---

When verifying proofs about code, I often end up with a hypothesis that has an if statement in it. Depending on how long it's been since I last used Lean, I forget how to deal with it. This is a quick post to remind me how.

Example:

```lean
example (b: Bool) (n: Nat) (H1: if b then (n = 5) else (n = 3)) : n > 0 := by sorry
```

We want to show that for an arbitrary boolean and natural number `n`, that `n` will always be greater than zero. 

Note that the condition of an arbitrary if statement can take a proposition instead of a boolean. However for this to work the proposition must be *decidable*. Checking the condition of a boolean is decidable, so we'll use that to simplify our example.

From here, we use `by_cases (b = true)` to give us two new subgoals. One where it's true and one where it's false.

```lean
by_cases H2 : (b = true)
case pos =>
  sorry
case neg =>
  sorry
```

First let's consider the positive case. We can simplify `H1` to `n = 5` by using `H2` which states that `b` is true.

```lean
replace H1 : n = 5 := by
  rwa [if_pos (by exact H2)] at H1
```

For this example, you don't need the parenthesis saying `(by exact H2)`. However, depending on your setup the proof that `b` is true might be too difficult for the rewrite system to infer. In those cases, you are required to specify the proof for it to work.

Then, we can substitute `n` to have our subgoal as `5 > 0`.

```lean
subst n
```

This is the same as showing that `0 < 5`.

```lean
suffices 0 < 5 by exact gt_iff_lt.mpr this
```

From here we can apply one of the builtin theorems

```lean
exact Nat.zero_lt_succ 4
```

For the negative case, we will follow a similar pattern except instead of invoking `if_pos` to eliminate the if-statement, we will invoke `if_neg`.

Thus, the complete proof for this is

```lean
example (b : Bool) (n : Nat) (H1: if b then (n = 5) else (n = 3)) : n > 0 := by
  by_cases H2 : (b = true)
  case pos =>
    replace H1 : n = 5 := by
      rwa [if_pos (by exact H2)] at H1
    subst n
    suffices 0 < 5 by exact gt_iff_lt.mpr this
    exact Nat.zero_lt_succ 4
  case neg =>
    replace H1 : n = 3 := by
      rwa [if_neg (by exact H2)] at H1
    subst n
    suffices 0 < 3 by exact gt_iff_lt.mpr this
    exact Nat.zero_lt_succ 2
```

