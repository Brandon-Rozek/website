---
title: "Verifying Proofs with Type Checkers"
date: 2025-05-27T09:27:59-04:00
draft: false
tags: ["Formal Methods"]
math: true
medium_enabled: false
---

The [Curry-Howard Correspondance](https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence) establishes a direct connection between computer programs and mathematical proofs.

| Programs                      | Proofs                  |
| ----------------------------- | ----------------------- |
| Type                          | Formula                 |
| Term                          | Proof                   |
| Type has an element           | Formula is provable     |
| Type does not have an element | Formula is not provable |

When we think about traditional type systems, however, most are uncapable of expressing interesting formula. This ultimately limits the formulas we can prove.

For example, consider the simply typed lambda calculus. In that system we have base types like `int` and `bool`, as well as function types $t1 \rightarrow t2$ which take a type and return a type.

From that system, we can then create a proof of an integer by showing the term `0`.  The following shows how to use the Lean 4 type checker to verify that `0` is an integer:

```lean4
#check (0: Int)
```

This, however, isn't a very interesting proof or formula. What would be more interesting is if we can use a type checker to verify the following:

```lean4
#check (by exists [] : ∃ (x : List Int), x.length = 0)
```

Sadly, we can't verify this with the simply typed lambda calculus. This does not mean that we cannot design a type system that can. 

Interactive theorem provers (ITPs) or [proof assistants](https://en.wikipedia.org/wiki/Proof_assistant) help fill this void. Equipped with sophisticated type systems, they allow us to prove a formula by writing a program of that type. Some of the most popular ones include [Lean](https://lean-lang.org/), [Rocq](https://rocq-prover.org/), [Isabelle](https://isabelle.in.tum.de/), [Agda](https://wiki.portal.chalmers.se/agda/pmwiki.php), and [F*](https://fstar-lang.org/).

The underlying type system of each proof assistant is different. However, there are many similarities. In general, most aim to be at least as powerful as the calculus of constructions developed by Thierry Coquand.

To get an idea of how expressive these type systems are, we can analyze the [Lambda cube](https://en.wikipedia.org/wiki/Lambda_cube). Developed by Henk Barendregt,  this characterizes the space between the simply typed lambda calculus and the calculus of constructions.

![](/files/images/blog/Lambda_Cube_img.svg)

[Image courtesy of Tellofou on Wikipedia](https://commons.wikimedia.org/wiki/File:Lambda_Cube_img.svg).

Each dimension corresponds to an extension of the simply typed lambda calculus:
- X Axis: Dependent types (Types that depend on terms)
- Y Axis: Polymorphic types (Terms that depend on types)
- Z Axis: Type Operators (Types that depend on types)

**Dependent Type**

A dependent type is a type that depends on some term. We can use this to, for example, write functions that return entirely different base types depending on the outcome of some conditional.

Here's an example function you can write in Lean 4:

```lean4
def isZeroOrMore (n : Nat) : (if n == 0 then Bool else Nat) :=
  if H: n == 0 then by
    rw [if_pos (by exact H)]
    exact true
  else by
    rw [if_neg (by exact H)]
    exact n
```

The function `isZeroOrMore` will return `true` if the parameter `n` is equal to zero, otherwise it'll return the natural number parameter itself.

**Type Operators**

A type operator takes a type and produces a type. For example, we can create a triple type that represents the product of three base types.

```lean4
structure Triple {A B C : Type} where
  a: A
  b: B
  c: C
```

Let's say that we want to enforce that all three elements of the triple are of type `Int`. Then we can create a new type `IntTriple` as follows:

```Lean 4
def IntTriple := @Triple Int Int Int
```

From here, we can use `IntTriple` when type checking values.

```
#check (Triple.mk 1 2 3 : IntTriple)
````


**Type Polymorphism**

Type polymorphism allows us to write one function which covers many different types. There are two common places that we see this often.

Identity function:
```lean4
def iden {α : Type} (x : α) : α := x
```

Here we're saying that the parameter a can be of any arbitrary type α, and the function `iden` will then just return the parameter itself.

We also see this often when defining operations over lists

```lean4
def map {α β : Type} (f: α → β) (as: List α): List β :=
  match as with
  | [] => []
  | (head::tail) => f head :: map f tail
```

The calculus of constructions support all of these three extensions.  We've introduced enough here to write a more interesting proof.

```lean4
theorem map_iden_idempotent {α : Type} (as: List α) : (map iden as = as) := by
  unfold iden
  induction as
  case nil =>
    unfold map
    rfl
  case cons h t IH =>
    unfold map
    rw [IH]
```

We've invoked the Lean type checker to verify that for a list of any arbitrary type, when you map over it with the identity function you get back the list itself.

You might ask, why don't all programming languages support this? By adding expressivity to our type system, we sacrifice computational efficiency. For most standard programming tasks, we want our type checker to be as fast as possible. However when we require stronger guarentees of correctness about our code, proof assistants are a great tool for the job. Many of them even generate code for mainstream programming languages.

That's all for today. I'd like to thank James Oswald for the inspiration to write this post and some of its examples. This was adapted from a presentation we gave last month to our weekly seminar series.
