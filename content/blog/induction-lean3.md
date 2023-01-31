---
title: "Induction in Lean 3: Three Techniques"
date: 2023-01-30T21:07:43-05:00
draft: false 
tags: ["Formal Methods"]
math: true
medium_enabled: true
---

When proving properties of an inductive data type, chances are that we need to perform the induction tactic on the data structure. There are multiple ways to approach this though and each comes with its own pros and cons.

In this post we'll consider the following list structure

```lean
inductive CustomList (T : Type)
| cnil : CustomList
| ccons (hd : T) (tl : CustomList) : CustomList
```

A function that takes a length of the list

```lean
def clength {α : Type}:  CustomList α → ℕ 
  | cnil := 0
  | (ccons b as) := 1 + clength as
```

And a function that appends two lists

```lean
def cappend {α : Type} : CustomList α → CustomList α → CustomList α
  | cnil         bs := bs
  | (ccons a as) bs := ccons a (cappend as bs)
```

Now lets say we want to prove the following theorem:
$$
\forall \mathit{as} \in \mathit{CustomList}~\alpha, \mathit{cappend}~\mathit{as}~\mathit{cnil} = as
$$

That is, appending `cnil` to a list will produce the same list.

## `induction` tactic

The first method that is commonly taught is to use the `induction` tactic.

```lean
theorem append_nil1 {α : Type} (as : CustomList α) : cappend as cnil = as := begin
  induction as,

-- Base Case
  case CustomList.cnil
  { 
    show cappend cnil cnil = cnil, from by rewrite [cappend],
  },

-- Recursive Case
  case CustomList.ccons : hd tl ih
  {
    calc
      cappend (ccons hd tl) cnil = ccons hd (cappend tl cnil) : by rewrite [cappend]
      ...                        = ccons hd tl : by rewrite [ih]
    ,
  },
end
```

The upside to this approach is that the theorem prover determines for you the subgoals to prove. The issue is that the subgoals aren't explicit within the proof written out. This can harm readability among others. As much as we want to imagine that we're writing code only for computers. We're writing code for other people to read as well.

## Pattern Matching

Lean has a built in pattern matcher which makes the proof more concise and even reports back to us if we don't consider all the cases.

```lean
theorem append_nil3 {α : Type} : ∀ as : CustomList α, cappend as cnil = as
| (@cnil α) := show cappend cnil cnil = cnil, from by rewrite [cappend]
| (ccons hd tl) := show cappend (ccons hd tl) cnil = (ccons hd tl), from by {
    calc
      cappend (ccons hd tl) cnil = ccons hd (cappend tl cnil) : by rewrite [cappend]
      ...                        = ccons hd tl : by rewrite append_nil3
}
```

Note that we had to change the definition header to the $\forall$ syntax in order for the pattern matching to work. For the base case, we needed to provide the implicit parameter which is why it's stated as `@cnil a` as opposed to only `cnil`.

This is by far the more concise syntax. Mostly readable, however it can be intimidating to parse it initially.

## Applying `rec_on`

Every inductive data type in Lean has a built in `rec_on` property which allows for recursion to happen. Similarly to applying `or.elim` as opposed to `cases`. We can organize the proof slightly more than the last two approaches.

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

Personally, this one is the easiest for me to follow. The main issue that I haven't figured out yet is how to cleanly perform double recursion. For example to prove that $\mathit{clength}~(\mathit{cappend}~\mathit{as}~\mathit{bs}) = \mathit{clength}~\mathit{as} + \mathit{clength}~\mathit{bs}$, we would need to perform induction on both the $\mathit{as}$ data structure as well as the $\mathit{bs}$ datastructure. I haven't quite figured out how to do this appropriately, so if you have suggestions please let me know.

## Conclusion

Each approach comes with its tradeoffs. The `rec_on` approach looks clean for single induction proofs. Meanwhile, the pattern matching approach works great with multiple induction. The easiest approach to determining the appropriate subgoals is to use the `induction` tactic. In fact, it sometimes is more efficient to write the entire proof via tactics first and then work towards making it more readable with additional subproofs and rewriting.
