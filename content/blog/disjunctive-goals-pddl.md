---
title: "Disjunctive Goals in PDDL"
date: 2024-04-16T11:26:28-04:00
draft: false
tags: []
math: true
medium_enabled: false
---

Classical AI planning tries to find a sequence of actions that takes an agent from their initial state to a state that satisfies some goal.

Let's say, for example,  that you want to deliver a package that's currently sitting at location `A`. The recipient said that you can drop it off at either their workplace `B` or their home `C`. 

If you drop it off at a some location, then people will be nice enough to let you retrieve the package and place it back at location `A`.  Graphically, we can represent it as follows:

![](/files/images/blog/disjunctive-packages.svg)

A state in classical planning is a set of atomic formulas. For our problem it will look like:

```lisp
(:init 
    (at-package A) 
 
 	; Delivery Paths
    (CONNECTED A B)
    (CONNECTED A C)
    (CONNECTED A D)
 
 	; Retrieval paths
    (CONNECTED B A)
 	(CONNECTED C A)
 	(CONNECTED D A)
)
```

The goal in classical planning is a set of ground atomic formulas and the negations of ground atomic formulas. That means, the following isn't a "valid" goal in the classical planning model.

```lisp
(:goal (or (at-package B) (at-package C)))
```

I put valid in quotation marks since if you use the [Fast Downward](https://www.fast-downward.org/) planner, it will behind the scenes compile it to a valid planning problem. But what if you're not fortunate enough to have a planner automatically do that for you? We'll discuss three different techniques for handling disjunctive goals.

## (1) Plan for each Disjunct

A plan that delivers a package to `B` is valid for the goal of delivering it to either `B` or `C`. The same goes for delivering it to `C`. Therefore, the set of valid plans for the disjunctive goal is the union of all the plans that satisfy either of the disjuncts.

Domain File:

```lisp
(define (domain test-disjunct)
    (:requirements :typing)
    (:types location - object)

    (:predicates (at-package ?l - location) (CONNECTED ?l1 ?l2 - location)


    (:action move-package
        :parameters (?l1 ?l2 - location)
        :precondition (and 
            (at-package ?l1) 
            (CONNECTED ?l1 ?l2)
        )
        :effect (and 
            (at-package ?l2)
            (not (at-package ?l1))
        )
    )
)
```

Problem File:

```lisp
(define (problem test-disjunct)
    (:domain test-disjunct)
    (:requirements :typing)
    (:objects
        A B C D - location
    )
    (:init 
    	(at-package A) 
    	(CONNECTED A B)
    	(CONNECTED A C)
    	(CONNECTED A D)
    	(CONNECTED B A)
 		(CONNECTED C A)
 		(CONNECTED D A)
    )
    (:goal (at-package B))
    ; (:goal (at-package C))
) 
```

Call Planner:

```bash
./fast-downward.sif --alias lama-first domain-disjunct.pddl problem-disjunct.pddl
```

Result:

```
move-package a b
```

## (2) Derived Predicates (Axioms)

Axioms or derived predicates are atomic ground formula that can only appear in the precondition of actions and the goal. That is, it cannot appear in the effect.

We can create a new derived predicate `done` which when true means that we have satisfied the goal.

```lisp
(:derived (done) (or (at-package B) (at-package C)))
```

Domain File:

```lisp
(define (domain test-derived)
    (:requirements :derived-predicates :typing )
    (:types location - object)

    (:predicates (at-package ?l - location) (CONNECTED ?l1 ?l2 - location) (done))
    
    (:derived (done) (or (at-package B) (at-package C)))

    (:action move-package
        :parameters (?l1 ?l2 - location)
        :precondition (and 
            (at-package ?l1) 
            (CONNECTED ?l1 ?l2)
        )
        :effect (and 
            (at-package ?l2)
            (not (at-package ?l1))

        )
    )
)
```

Problem File:

```lisp
(define (problem test-derived)
    (:domain test-derived)
    (:requirements :typing)
    (:objects
        A B C D - location
    )
    (:init 
    	(at-package A) 
    	(CONNECTED A B)
    	(CONNECTED A C)
    	(CONNECTED A D)
    	(CONNECTED B A)
 		(CONNECTED C A)
 		(CONNECTED D A)
    )
    (:goal (done))
) 
```

Call Planner:

```bash
./fast-downward.sif benchmarks/domain-derived.pddl benchmarks/problem-derived.pddl \
	--search "astar(blind())"
```

Result:

```
move-package a b
```

**Note:** Not all heuristics in FastDownward support axioms. In fact this problem is not limited to FastDownward. The planner call above uses the blind heuristic which supports axioms and is safe.

Before replacing that evaluator, however, make sure to [read the docs](https://www.fast-downward.org/Doc/Evaluator) to make sure that the heuristic states that it supports axioms, and that it is safe in the presence of them.


## (3) Compilation

The core idea of this technique is to push the disjunction onto the search space. As with the last technique we create a new predicate `done`. However, instead of automatically deriving `done` through an axiom, we create an action for every disjunct whose precondition is that disjunct, and whose effect is `done`.

Example:

```lisp
(:action goal-B
    :parameters ()
    :precondition (at-package B)
    :effect (done)
)

(:action goal-C
    :parameters ()
    :precondition (at-package C)
    :effect (done)
)
```

Our new goal will be `(:goal (done))`.  After you plan using the compiled version of the problem, drop the actions `goal-B` and `goal-C` and you have a plan for the disjunctive problem.

This technique works great when you're grabbing the first optimal plan, however, there are two considerations that need to be made when you grab more than just one plan[^1].

[^1]: The field of diverse planning looks at generating multiple plans for a given planning problem. The introduction to ["Reshaping Diverse Planning"](https://ojs.aaai.org/index.php/AAAI/article/view/6543) by Michael Katz and Shirin Sohrabi covers well the motivations behind this. 

(1) There's nothing guarding against an infinite chain of `goal-B` action calls. Hence the following is a valid plan:

```
move-package a b
goal-B
goal-B
goal-B
```

We can address this by adding `(not (done))` to the preconditions of each of the goal actions.

(2) We have no effects that remove `done`, so a valid plan can move to a state that satisfies the goal and then move away.

```
move-package a b
move-package b a
```

We can address this by adding `(not (done))` to the effect of every action that is not the goal actions.

Domain File:

```lisp
(define (domain test-compile)
    (:requirements :typing)
    (:types location - object)

    (:predicates (at-package ?l - location) (CONNECTED ?l1 ?l2 - location) (done))

    (:action move-package
        :parameters (?l1 ?l2 - location)
        :precondition (and 
            (at-package ?l1) 
            (CONNECTED ?l1 ?l2)
        )
        :effect (and 
            (at-package ?l2)
            (not (at-package ?l1))
            (not (done))
        )
    )

    (:action goal-B
        :parameters ()
        :precondition (and
            (at-package B)
            (not (done))
        )
        :effect (done)
    )

    (:action goal-C
        :parameters ()
        :precondition (and 
            (at-package C)
            (not (done))
        )
        :effect (done)
    )
)
```

Problem File:

```lisp
(define (problem test-compile)
    (:domain test-compile)
    (:requirements :strips)
    (:objects
        A B C D - location
    )
    (:init 
    	(at-package A) 
    	(CONNECTED A B)
    	(CONNECTED A C)
    	(CONNECTED A D)
    	(CONNECTED B A)
 		(CONNECTED C A)
 		(CONNECTED D A)
    )

    (:goal (done))
) 
```

Planner Call:

To retrieve multiple plans, we can use the [Kstar](https://github.com/IBM/kstar) package by IBM. In particular, I had success with their [Python package](https://pypi.org/project/kstar-planner/).

```python
from kstar_planner import planners
from pathlib import Path

domain_file = Path("domain-compile.pddl")
problem_file = Path("problem-compile.pddl")

plans = planners.plan_topk(
    domain_file=domain_file,
    problem_file=problem_file,
    number_of_plans_bound=3,
    timeout=30
)
print(plans)
```

Output:

```
===
move-package a b
goal-b
===
move-package a c
goal-c
===
move-package a b
move-package b a
move-package a b
goal-b
```

Not sure why you would want to execute the last plan, but at least the package got to its destination at the end :D

