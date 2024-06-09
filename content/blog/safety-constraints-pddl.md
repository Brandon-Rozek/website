---
title: "Constraints and Safety in PDDL"
date: 2024-06-09T08:00:00-07:00
draft: false
tags: ["Automated Planning"]
math: true
medium_enabled: false
---

Sometimes the end goal is not what only matters but the journey along the way. If I was able to drive to my destination safely, but I scrapped three cars along the way, then the drive isn't successful.

In this post, we'll go over how to encode constraints and safety into an automated planning domain. As they're inherently similar, we'll look at it in the lens of constraints for the rest of the post.

- Constraints are goals that must be satisfied in every state along the plan.
- Safety are invalid partial states that must be avoided along every state in the plan.

**Running Example:** Suppose we're in a three room domain laid out in the following way:

```
kitchen <-> Living Room <-> Dining Room
```

You're currently in the kitchen holding dinner for tonight. The goal is to get dinner ready. You first need to set the table with the plates, and you need two hands for that. You can walk between the three rooms, but it's slow and incurs extra action cost. To get around faster, you can dash. However, dashing when holding food leads to spilling some of it and making a mess. You can cleanup the mess in any room you're in.

The PDDL domain will look like the following:

```pddl
(define (domain dinner)
    (:requirements :typing)
    (:types location - object)

    (:predicates 
        (at ?1 - location) (CONNECTED ?l1 ?l2 - location) 
        (table-set) (dinner-ready) (mess-made ?l - location)
        (holding-food) (at-food ?l - location)
    )

    (:action walk
        :parameters (?l1 ?l2 - location)
        :precondition (and 
            (at ?l1) 
            (CONNECTED ?l1 ?l2)
        )
        :effect (and 
            (at ?l2)
            (not (at ?l1))
            (increase (total-cost) 10)
        )
    )

    (:action dash
        :parameters (?l1 ?l2 - location)
        :precondition (and 
            (at ?l1) 
            (CONNECTED ?l1 ?l2)
        )
        :effect (and 
            (at ?l2)
            (not (at ?l1))
            (when (holding-food) (mess-made ?l2))
        )
    )

    (:action set-table
        :precondition (and 
            (at dining-room) 
            (not (holding-food))
        )
        :effect (table-set)
    )

    (:action present-dinner
        :precondition (and 
            (at dining-room)
            (holding-food)
            (table-set)
        )
        :effect (dinner-ready)
    )

    (:action drop
        :parameters (?l1 - location)
        :precondition (and 
            (holding-food)
            (at ?l1)
        )
        :effect (and
            (not (holding-food))
            (at-food ?l1)
        )
    )

    (:action pickup
        :parameters (?l1 - location)
        :precondition (and 
            (not (holding-food))
            (at ?l1)
            (at-food ?l1)
        )
        :effect (and 
            (holding-food)
            (not (at-food ?l1))
        )
    )

    (:action cleanup
        :parameters (?l - location)
        :precondition (at ?l)
        :effect (not (mess-made ?l))
    )

)
```

For the goal of having dinner ready, the problem file is the following:

```pddl
(define (problem dinner)
    (:domain dinner)
    (:requirements :typing)
    (:objects
        kitchen living-room dining-room - location
    )
    (:init 
    	(CONNECTED kitchen living-room)
    	(CONNECTED living-room kitchen)
    	(CONNECTED living-room dining-room)
    	(CONNECTED dining-room living-room)
        (at kitchen)
        (holding-food)
    )
    (:goal (dinner-ready))
    (:metric minimize (total-cost))
) 
```

## Avoiding messes with Constraints

Let's say that we don't want any messes to be made. One way to go about this is encoding this as a goal.

```pddl
(:goal (and
  (dinner-ready)
  (forall (?l - location) (not (mess-made ?l)))
))
```

Let's ask [Fast Downward](https://www.fast-downward.org/) to find an optimal plan.

```bash
fast-downward.sif domain.pddl problem.pddl --search "astar(blind())"
```

It produces the following:

```
dash kitchen living-room
cleanup living-room
dash living-room dining-room
cleanup dining-room
drop dining-room
set-table
pickup dining-room
present-dinner
```

Note that it still made several messes, but it cleaned up after itself to satisfy the goal. If we want to avoid making messes at all during the plan, we'll have to use a constraint. We can add the following to the problem file:

```pddl
(:goal (dinner-ready))
(:constraints (and
    (forall (?l - location) (not (mess-made ?l)))
))
```

Not all planners support this PDDL 3.0 feature. Fast Downward [does not](https://www.fast-downward.org/PddlSupport). In this case, we'll need to do a *compilation trick*.

- Add an additional predicate called `check`
- Add to to the precondition of every action `(not check)`
- Add to the effect of every action `(check)`
- Create a new action that removes `check` in the effect if the constraint is satisfied.
- Add `(not (check))` to the goal.

For example, our new action for making sure that messes aren't made is the following:

```pddl
(:action check-constraint
    :precondition (and 
        (check)
        (forall (?l - location) (not (mess-made ?l)))
    )
    :effect ((not (check)))
)
```

Our new domain file needs to modify every prior action: 

```pddl
(define (domain dinner)
    (:requirements :typing)
    (:types location - object)

    (:predicates 
        (at ?1 - location) (CONNECTED ?l1 ?l2 - location) 
        (table-set) (dinner-ready) (mess-made ?l - location)
        (holding-food) (at-food ?l - location) (check)
    )

    (:action walk
        :parameters (?l1 ?l2 - location)
        :precondition (and 
            (at ?l1) 
            (CONNECTED ?l1 ?l2)
            (not (check))
        )
        :effect (and 
            (at ?l2)
            (not (at ?l1))
            (check)
            (increase (total-cost) 10)
        )
    )

    (:action dash
        :parameters (?l1 ?l2 - location)
        :precondition (and 
            (at ?l1) 
            (CONNECTED ?l1 ?l2)
            (not (check))
        )
        :effect (and 
            (at ?l2)
            (not (at ?l1))
            (when (holding-food) (mess-made ?l2))
            (check)
        )
    )

    (:action set-table
        :precondition (and 
            (at dining-room) 
            (not (holding-food))
            (not (check))
        )
        :effect (and (table-set) (check))
    )

    (:action present-dinner
        :precondition (and 
            (at dining-room)
            (holding-food)
            (table-set)
            (not (check))
        )
        :effect (and (dinner-ready) (check))
    )

    (:action drop
        :parameters (?l1 - location)
        :precondition (and 
            (holding-food)
            (at ?l1)
            (not (check))
        )
        :effect (and
            (not (holding-food))
            (at-food ?l1)
            (check)
        )
    )

    (:action pickup
        :parameters (?l1 - location)
        :precondition (and 
            (not (holding-food))
            (at ?l1)
            (at-food ?l1)
            (not (check))
        )
        :effect (and 
            (holding-food)
            (not (at-food ?l1))
            (check)
        )
    )

    (:action cleanup
        :parameters (?l - location)
        :precondition (and (at ?l) (not (check)))
        :effect (and (not (mess-made ?l)) (check))
    )

    (:action check-constraint
        :precondition (and 
            (check)
            (forall (?l - location) (not (mess-made ?l)))
        )
        :effect (not (check))
    )

)
```

New Problem File:

```pddl
(define (problem dinner)
    (:domain dinner)
    (:requirements :typing )
    (:objects
        kitchen living-room dining-room - location
    )
    (:init 
    	(CONNECTED kitchen living-room)
    	(CONNECTED living-room kitchen)
    	(CONNECTED living-room dining-room)
    	(CONNECTED dining-room living-room)
        (at kitchen)
        (holding-food)
    )
    (:goal (and
     (dinner-ready)
     (not (check))
    ))
) 
```

Fast Downward will find us a plan satisfying the constraint, but with a lot of `check-constraint` actions.

```pddl
drop kitchen
check-constraint
dash kitchen living-room
check-constraint
dash living-room dining-room
check-constraint
set-table
check-constraint
dash dining-room living-room
check-constraint
dash living-room kitchen
check-constraint
pickup kitchen
check-constraint
walk kitchen living-room
check-constraint
walk living-room dining-room
check-constraint
present-dinner
check-constraint
```

## Allowing some messes

Perhaps we want to introduce some mercy and instead use a *strike system*. This would allow an agent to break a constraint at most $X$ times before saying they failed at a task.

For this example, let us use the two-strike system. That is once they make the second mess, it is considered that the agent has failed at the task.

We adjust the `check-constraint` action from before to capture this new system:

```pddl
(:action check-constraint
    :precondition (check)
    :effect (and 
        ; We haven't striked out and satisfy the constraint
        (when
            (and 
                (forall (?l - location) (not (mess-made ?l)))
                (not (strike-max)) 
            )
            (not (check))
        )
        ; First time breaking the constraint
        (when 
            (and
                (not (forall (?l - location) (not (mess-made ?l))))
                (not (strike-one))
            )
            (and 
                (strike-one)
                (not (check))
            )
        )
        ; Second time breaking the constraint
        (when 
            (and
                (not (forall (?l - location) (not (mess-made ?l))))
                (strike-one)
            )
            (strike-max)
        )             
    )
)
```

Notice that each of these conditional effects are mutually exclusive from each other. We can use a different encoding, but having only one conditional effect fire after each execution makes it easier to reason about.

 The problem file stays the same as the last example, and asking Fast Downward for an optimal plan results in the following:

```
dash kitchen living-room
check-constraint
cleanup living-room
check-constraint
drop living-room
check-constraint
dash living-room dining-room
check-constraint
set-table
check-constraint
dash dining-room living-room
check-constraint
pickup living-room
check-constraint
walk living-room dining-room
check-constraint
present-dinner
check-constraint
```

The main difference between this plan and the last one is that it makes use of the strike system to first dash from the kitchen to the living room, creating a mess. Then it avoids messes for the rest of the plan.





