---
title: "Lean Theorem Prover Tactics"
date: 2021-10-10T23:52:41-04:00
draft: false
tags: ["Formal Methods"]
math: false
medium_enabled: true
---

I've recently been playing with the Lean Theorem Prover.  I am impressed with how some of the mathematics community decided to extend this project via [mathlib](https://leanprover-community.github.io/) and really make proving theorems in this framework easy and enjoyable.

Normally one of the most frustrating parts of theorem proving is having to justify what may seem to be a simple goal. Luckily, mathlib helps us out by [introducing tactics](https://leanprover-community.github.io/mathlib_docs/tactics.html) that can take some of these simple goals to the finish line.

## Tactics

Here is a subset of tactics that I find myself using the most:

|                |               |              |          |
| -------------- | ------------- | ------------ | -------- |
| [hint](#hint)  | [cases_type*](#cases_type*)  | [have](#have)   | [itauto](#itauto)     |
| [pretty_cases](#pretty_cases)   |  [squeeze_simp](#squeeze_simp)      | [tidy](#tidy)         | [solve_by_elim](#solve_by_elim)  |
| [finish](#finish)  |  [linarith](#linarith)     |              |          |



### `hint`

The first command to reach for. This will give you a tactic that is guaranteed to succeed.

```lean
theorem running_example1: ∀ P Q : Prop,
  Q ∧ (Q → P) → P
:=
begin
  intros P Q H,
  hint,
-- the following tactics solve the goal:
-- Try this: tauto
-- Try this: itauto
-- Try this: finish
-- Try this: solve_by_elim
```

Documentation: https://leanprover-community.github.io/mathlib_docs/tactics.html#hint

### `cases_type*`

The following destructs all (con/dis)junctions in the current context

```lean
cases_type* or and,
```

Example:

```lean
theorem running_example1: ∀ P Q : Prop,
  Q ∧ (Q → P) → P
:=
begin
  intros P Q H,
  cases_type* or and,
```

The tactic state before:

```
P Q: Prop
H : Q ∧ (Q → P)
⊢ P
```

The tactic state after:

```
P Q: Prop
H_left: Q
H_right: (Q → P)
⊢ P
```

Documentation: https://leanprover-community.github.io/mathlib_docs/tactics.html#cases_type

### `have`

If you want to add a hypothesis, this is a great way to introduce that and solve that goal. Combine this with `library_search` to try to find simple tactics to justify the hypothesis.

```lean
have H : EXAMPLE := by library_search,
```

Example:
```lean
theorem running_example1: ∀ P Q : Prop,
  Q ∧ (Q → P) → P
:=
begin
  intros P Q H,
  cases_type* or and,
  have H_P : P := by library_search,
-- Try this: exact H_right H_left
```

Documentation: https://leanprover-community.github.io/mathlib_docs/tactics.html#have

### `itauto`

Tries to use [intuitionist](https://plato.stanford.edu/entries/logic-intuitionistic/) propositional logic to solve the goal. Also called constructivist logic, it does not allow the use of the [law of excluded middle](https://en.wikipedia.org/wiki/Law_of_excluded_middle).

Example:

```lean
theorem running_example1: ∀ P Q : Prop,
  Q ∧ (Q → P) → P
:=
begin
  intros P Q H,
  cases_type* or and,
  itauto,
end
```

Documentation: https://leanprover-community.github.io/mathlib_docs/tactics.html#itauto

### `pretty_cases`

Great to call after `destruct`, `induction`, `injection`, etc. This will give you a cleaner way of representing cases.

Example:

```lean
theorem running_example2: ∀ n : ℕ,
  (∃ m : ℕ, n = 2 * m) ∨ (∃ m : ℕ, n = 2 * m + 1)
:=
begin
intros,
induction n,
pretty_cases,
-- Try this:
  -- case nat.zero
  -- { admit },
  -- case nat.succ : n_n n_ih
  -- { admit }
end
```

Documentation: https://leanprover-community.github.io/mathlib_docs/tactics.html#pretty_cases

### `squeeze_simp`

This tactic will give you the sequence of rewrite rules that can simplify an expression.

Example:

```lean
theorem running_example2: ∀ n : ℕ,
  (∃ m : ℕ , n = 2 * m) ∨ (∃ m : ℕ, n = 2 * m + 1)
  :=
begin
intros,
induction n,
case nat.zero
{
  left,
  existsi 0,
  squeeze_simp,
  -- Try this: simp only [mul_zero]
 },
```

Documentation: https://leanprover-community.github.io/mathlib_docs/tactics.html#squeeze_simp%20/%20squeeze_simpa%20/%20squeeze_dsimp%20/%20squeeze_scope

### `tidy`

Applies simple tactics to try to solve the goal. I like to use the query variant `tidy?` in order to get a list of tactics back.

The tactics it uses are: `id_rhs`, `refl`, `exact`, `trivial`, `dismp`, `simp`, `injections_and_clear`, `solve_by_elim`, `norm_cast`, `unfold`, `fsplit`.


Example:

```lean
theorem running_example3: ∀ n : ℕ,
  (∃ m : ℕ , n = 2 * m) ∨ (∃ m : ℕ, n = 2 * m + 1)
  :=
begin
intros,
induction n,
case nat.zero
{
  left,
  existsi 0,
  simp only [mul_zero],
 },
case nat.succ : n IH
{
  cases_type* or,
  case or.inl : IH
  {
    right,
    cases IH with m IH,
    tidy?,
    -- Try this: fsplit, work_on_goal 1 { solve_by_elim }
  },
```

Documentation: https://leanprover-community.github.io/mathlib_docs/tactics.html#tidy


### `solve_by_elim`
This tactic tries to apply the current hypotheses in the context and apply congruence closure algorithms to solve your goal.

If you have multiple goals you can call `solve_by_elim*` to try to solve them all at once. I find though that it is often more successful to do `all_goals{solve_by_elim}` instead, unless you need results from one of the subproofs in the other.

This tactic is non-deterministic so it bounds the number of attempts to discharge subgoals. Here is how you increase the bound: `solve_by_elim { max_depth := 5 }`

Example:

```lean
theorem running_example3: ∀ n : ℕ,
  (∃ m : ℕ , n = 2 * m) ∨ (∃ m : ℕ, n = 2 * m + 1)
  :=
begin
intros,
induction n,
case nat.zero
{
  left,
  existsi 0,
  simp only [mul_zero],
 },
case nat.succ : n IH
{
  cases_type* or,
  case or.inl : IH
  {
    right,
    cases IH with m IH,
    fsplit, work_on_goal 1 { solve_by_elim },
  },
  case or.inr : IH
  {
    left,
    cases IH with m IH,
    rewrite IH,
    existsi m + 1,
    solve_by_elim,
  },
}
end
```

Documentation: https://leanprover-community.github.io/mathlib_docs/tactics.html#solve_by_elim

### `finish`

This tactic is like a black box to me, mainly because it performs many subtactics. It tries to finish off the goal. To give a hint of its power, it can actually solve the first theorem.

```lean
theorem running_example1: ∀ P Q: Prop,
  Q ∧ (Q → P) → P :=
begin
  finish,
end
```

Source: https://leanprover-community.github.io/mathlib_docs/tactics.html#finish%20/%20clarify%20/%20safe

### `linarith`

This tactic solves linear (in)equalities.

Example:

```lean
theorem example3: ∀ n m : ℕ,
  n > m → m < n :=
begin
  intros,
  linarith,
end
```

Documentation: https://leanprover-community.github.io/mathlib_docs/tactics.html#linarith

## Conclusion
A common pattern of writing proofs for me is to use a combination of `hint` and `have` with `library_search`. Especially when you are not an expert in a theorem prover, it's nice to have the system fill in some of the simpler steps. I generally prefer tactics that give you a list of simpler tactics back as opposed to solving the goal in the background without any proof. Regardless, I'm glad that many of these decision procedures exist to help me deal with what can sometimes be the verbosity of theorem proving.
