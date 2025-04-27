---
title: "Polymorphic Functions w/ Wildcard Matching in Lean 4"
date: 2024-08-04T07:21:07-07:00
draft: false
tags: ["Formal Methods"]
math: false
medium_enabled: false
---

I was reading through the [Polymorphism](https://lean-lang.org/functional_programming_in_lean/getting-to-know/polymorphism.html) section in the Functional programming in Lean textbook and came across the following example:

```lean4
inductive Sign where
  | pos
  | neg

def posOrNegThree (s : Sign) : match s with | Sign.pos => Nat | Sign.neg => Int :=
  match s with
  | Sign.pos => (3 : Nat)
  | Sign.neg => (-3 : Int)
```

The function `posOrNegThree` depending on the input, can either return an expression of type `Nat` or an expression of type `Int`. That's super neat!

What happens if we add a wildcard to the match? 

For example, let's say we want a type based on the number of bits of precision specified. If we don't support the number of bits, we return the arbitrary precision `Nat` as our default.

```lean4
def UIntN (n: Nat) : Type := match n with
  | 32 => UInt32
  | 64 => UInt64
  | _ => Nat
```

Now let's write a function that returns the zero element of our specified type:

```lean4
def u0 (x: Nat) : UIntN x := match x with
  | 32 => (0: UInt32)
  | 64 => (0: UInt64)
  | _ => Nat.zero
```

This will result in the following error:

```lean4
type mismatch
  Nat.zero
has type
  ℕ : Type
but is expected to have type
  UIntN x✝ : Type
```

I got stuck on this for a while, so I asked on the really helpful Lean Zulip and got a [great response](https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/.E2.9C.94.20Polymorphic.20Functions.20w.2F.20Wildcard.20Match.20Type)

```lean4
def u0 (x: Nat) : UIntN x := dite (x=32) (λ h ↦ by
    subst h
    exact (0 : UInt32)
  ) (dite (x = 64) (λ h ↦ by
    intro h2
    subst h
    exact (0: UInt64)
    )
    (λ h ↦ by
    intro h2
    have : UIntN x = Nat := by
      unfold UIntN
      simp only
    rw [this]
    exact 0
  ))
```

Unfortunately this doesn't look pretty, but this was a massive clue in finding the prettier syntax to solve this problem!

```lean4
def u0 (x: Nat) : UIntN x :=
  if h: x = 6 then by
    subst h
    exact (0: UInt32)
  else if h2: x = 4 then by
    subst h2
    exact (0: UInt64)
  else by
    have : UIntN x = Nat := by
      unfold UIntN
      simp only
    rw [this]
    exact 0
```



