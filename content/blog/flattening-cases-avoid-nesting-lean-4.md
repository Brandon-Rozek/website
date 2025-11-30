---
title: "Flattening Cases to Avoid Nesting in Lean 4"
date: 2025-10-05T19:38:20-04:00
draft: false
tags:
  - Lean
  - Proof assistant
  - Formal Proof
math: true
medium_enabled: false
---

Nested cases in proofs increase cognitive load for the reader since they have to process not only the case recently stated but also all the case splits prior. That's why if I can, I prefer to flatten out my cases so that we can see in one step all the variables we're segmenting.

I came across this recently in Lean when working on Lattice proofs over integers with $\infty$ and $-\infty$  In Lean, we can define this "extended integer" (`EInt`) by using `WithTop` and `WithBot`

```lean4
import Mathlib.Order.Interval.Basic

-- An Integer with a top (∞) and bottom (-∞) element
def EInt : Type := WithBot (WithTop Int)
deriving LinearOrder

@[simp] def EInt.ninf : EInt := (⊥ : WithBot (WithTop Int))
@[simp] def EInt.inf : EInt := (WithBot.some ⊤ : WithBot (WithTop Int))

notation "-∞" => EInt.ninf
notation "∞" => EInt.inf

-- Helper instances so I can later write numbers and have them casted
instance: IntCast EInt where
  intCast n := WithBot.some (WithTop.some n)

instance: OfNat EInt n where
  ofNat := some (some (Int.ofNat n))
```

Unfortunately, using `WithBot` and `WithTop` is just weird. Look at how we would define functions and write proofs using them.

```lean4
def EIntFun : EInt → ℤ
  | none => 0
  | some ⊤ => 0
  | some (some _) => 0

lemma EIntFunIsZero (e: EInt) : EIntFun e = 0 := by
  cases e
  case none =>
    rfl
  case some e =>
    cases e
    case top =>
      rfl
    case coe e =>
      rfl
```

What's more intuitive is to break it up based on whether it's $-\infty$, $\infty$ or some integer $z$. Luckily, we're able to define our own way of splitting up cases in Lean.

```lean4
def EInt.casesOn.{u} {motive : EInt -> Sort u} (a : EInt)
  (ninf : motive -∞)
  (int : ∀ n : Int, motive ↑n)
  (pinf : motive ∞) :
motive a := by
  cases a
  case none =>
    exact ninf
  case some v =>
    cases v
    case top =>
      exact pinf
    case coe n =>
      exact int n
```

When we're doing a proof by cases, we're trying to prove some `motive a`. What the above definition says, is that if we're given some EInt `a` and three proofs regarding the motive of each of the cases, then performing the cases successfully proves the motive.

Notice how the proof now no longer has any nested cases:

```lean4
lemma EIntFunIsZero2 (e: EInt) : EIntFun e = 0 := by
  cases e using EInt.casesOn
  case ninf =>
    rfl
  case int z =>
    rfl
  case pinf =>
    rfl
```

In fact, we can even use this trick to simplify our function

```lean4
def EIntFun2 (e: EInt) : ℤ := by
  cases e using EInt.casesOn with
  | ninf =>
    exact 0
  | int z =>
    exact 0
  | pinf =>
    exact 0
```

## A more complicated example

Personally I find utility in defining how we want our cases to go prior to the proof itself. For example, let's break up the domain further by considering the sign of our integers.

```lean4
def EInt.casesOnSigns.{u} {motive : EInt -> Sort u} (a : EInt)
  (ninf : motive -∞)
  (nint : ∀ n : Int, n < 0 → motive ↑n)
  (zero: ∀ n : Int, n = 0 → motive ↑n)
  (pint : ∀ n : Int, n > 0 → motive ↑n)
  (pinf : motive ∞) :
motive a := by
  cases a
  case none =>
    exact ninf
  case some v =>
    cases v
    case top =>
      exact pinf
    case coe n =>
      by_cases n < 0
      case pos H =>
        exact nint n H
      case neg H =>
        by_cases n = 0
        case pos H2 =>
          exact zero n H2
        case neg H2 =>
          have H3 : n > 0 := by
            have HH : n ≥ 0 := Int.not_lt.mp H
            have HH2 : n ≠ 0 := H2
            have HH3 : 0 ≠ n := Ne.symm HH2
            exact lt_of_le_of_ne HH HH3
          exact pint n H3
```

The more complicated we make our cases, the more Lean will struggle to establish definitional equality. I personally find it useful to create helper lemmas for each of the cases to later help establish our motive.

**Negative Infinity Case**

```lean4
@[simp]
lemma EInt.casesOnSigns.is_ninf.{u} {motive : EInt -> Sort u}
  (ninf : motive -∞)
  (nint : ∀ n : Int, n < 0 → motive ↑n)
  (zero: ∀ n : Int, n = 0 → motive ↑n)
  (pint : ∀ n : Int, n > 0 → motive ↑n)
  (pinf : motive ∞) : EInt.casesOnSigns (-∞) ninf nint zero pint pinf = ninf := rfl
```

The above says that if we perform a cases on $-\infty$ then the result will be equivalent to the `ninf` case.

**Negative Integer Case**

```lean4
lemma EInt.casesOnSigns.is_nint.{u} {motive : EInt -> Sort u}
  (z : Int)
  (Hz : z < 0)
  (ninf : motive -∞)
  (nint : ∀ n : Int, n < 0 → motive ↑n)
  (zero: ∀ n : Int, n = 0 → motive ↑n)
  (pint : ∀ n : Int, n > 0 → motive ↑n)
  (pinf : motive ∞) :
  EInt.casesOnSigns (↑z) ninf nint zero pint pinf = nint z Hz := by
  unfold casesOnSigns
  show (casesOn (↑z) ninf (fun n => if h : n < 0 then nint n h
                                    else if h : n = 0 then zero n h
                                    else pint n (by omega : n > 0)) pinf) = nint z Hz
  change (if h : z < 0 then nint z h
          else if h : z = 0 then zero z h
          else pint z (by omega : z > 0)) = nint z Hz
  rw [dif_pos Hz]
```

With our usage of inequalities, we have to help guide Lean through this proof. We first unfold the `casesOnSigns` definition to get the goal shown in the `show` tactic. From there, we already know that our EInt is the integer `z`, so we can simplify the cases to our nested if-then-else statement.  After that, since we have the hypothesis that our integer `z` is negative, we can directly get the `nint z h` case from the consequent of the outer ite.

**Zero Case**

```lean4
@[simp]
lemma EInt.casesOnSigns.is_zero.{u}  {motive : EInt -> Sort u}
  (z : Int)
  (Hn : z = 0)
  (ninf : motive -∞)
  (nint : ∀ n : Int, n < 0 → motive ↑n)
  (zero: ∀ n : Int, n = 0 → motive ↑n)
  (pint : ∀ n : Int, n > 0 → motive ↑n)
  (pinf : motive ∞) : (EInt.casesOnSigns (z) ninf nint zero pint pinf)  = zero z Hn := by
    subst z
    rfl
```

Once we substitute zero in, Lean can automatically establish definitional equality.

**Positive Case**

```lean4
lemma EInt.casesOnSigns.is_pint.{u}  {motive : EInt -> Sort u}
  (z : Int)
  (Hz : z > 0)
  (ninf : motive -∞)
  (nint : ∀ n : Int, n < 0 → motive ↑n)
  (zero: ∀ n : Int, n = 0 → motive ↑n)
  (pint : ∀ n : Int, n > 0 → motive ↑n)
  (pinf : motive ∞) : (EInt.casesOnSigns (z) ninf nint zero pint pinf)  = pint z Hz := by
  unfold casesOnSigns
  show (casesOn (↑z) ninf (fun n => if h : n < 0 then nint n h
                                    else if h : n = 0 then zero n h
                                    else pint n (by omega : n > 0)) pinf) = pint z Hz
  change (if h : z < 0 then nint z h
          else if h : z = 0 then zero z h
          else pint z (Hz : z > 0)) = pint z Hz
  have HH: ¬(z < 0) := not_lt_of_gt Hz
  rw [dif_neg HH]
  have HH2: ¬(z = 0) := Int.ne_of_gt Hz
  rw [dif_neg HH2]
```

Similar to the negative case, but we need to do slightly more work to get to the last alternative within the nested if-then-else statement.

**Infinity Case**

```lean4
@[simp]
lemma EInt.casesOnSigns.is_pinf.{u} {motive : EInt -> Sort u}
  (ninf : motive -∞)
  (nint : ∀ n : Int, n < 0 → motive ↑n)
  (zero: ∀ n : Int, n = 0 → motive ↑n)
  (pint : ∀ n : Int, n > 0 → motive ↑n)
  (pinf : motive ∞) : EInt.casesOnSigns (∞) ninf nint zero pint pinf = pinf := rfl
```

---

Like before, now that we have our new definition `EInt.casesOnSigns`, we can create our function which determines whether an EInt is positive cleanly.

```lean4
def EInt.isPos (e: EInt) : Bool := by
  cases e using EInt.casesOnSigns with
  | ninf => exact false
  | nint _ => exact false
  | zero => exact false
  | pint _ => exact true
  | pinf => exact true
```

This is much better than if we worked with the original `WithTop` and `WithBot` version! Now let's prove that our EInt is positive iff it is greater than zero. To do this we'll need one helper lemma.

```lean4
lemma EInt.coe_lt_coe {a b : Int}:  ((↑a : EInt) < (↑b: EInt)) ↔ a < b := by
  have H1 : ((↑a : EInt) < (↑b: EInt)) → a < b := by
    intro (H: (↑a : EInt) < (↑b: EInt))
    apply WithTop.coe_lt_coe.mp
    exact WithBot.coe_lt_coe.mp H
  have H2 : a < b → ((↑a : EInt) < (↑b: EInt)) := by
    clear H1
    intro (H : a < b)
    apply WithBot.coe_lt_coe.mpr
    exact WithTop.coe_lt_coe.mpr H
  exact Iff.intro H1 H2
```

The above lemma states that if the integer $a$ is less than the integer $b$, then the EInt version of $a$ is less than the EInt version of $b$ and vice versa.  Now for the main proof

**Soundness**

If our EInt `e` is positive, then `e` is greater than zero.

```lean4
lemma EInt.isPos_sound (e: EInt) : e.isPos = true → e > 0 := by
  intro H
  cases e using EInt.casesOnSigns
  case ninf =>
    contradiction
  case nint n Hn =>
    unfold EInt.isPos at H
    rw [EInt.casesOnSigns.is_nint n Hn] at H
    contradiction
  case zero n Hz =>
    unfold EInt.isPos at H
    rw [EInt.casesOnSigns.is_zero n Hz] at H
    contradiction
  case pint n Hp =>
    apply EInt.coe_lt_coe.mpr Hp
  case pinf =>
    exact Batteries.compareOfLessAndEq_eq_lt.mp rfl
```

**Completeness**

If our EInt `e` is greater than zero, then `e` is positive.

```lean4
lemma EInt.isPos_complete (e: EInt) : e > 0 → e.isPos = true := by
  intro H
  cases e using EInt.casesOnSigns
  case ninf =>
    contradiction
  case nint n Hn =>
    have H2 : n > 0 := EInt.coe_lt_coe.mp H
    have H3 : ¬(n > 0) := not_lt_of_gt Hn
    contradiction
  case zero n Hz =>
    have H2 : n > 0 := EInt.coe_lt_coe.mp H
    have H3 : ¬(n > 0) := Eq.not_gt Hz
    contradiction
  case pint n Hp =>
    unfold EInt.isPos
    rw [EInt.casesOnSigns.is_pint n Hp _ _ _ _ _ ]
  case pinf =>
    unfold EInt.isPos
    rw [EInt.casesOnSigns.is_pinf]

```

