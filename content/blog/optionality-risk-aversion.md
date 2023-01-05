---
title: "Optionality and Risk in Decision Making"
date: 2022-10-12T01:10:42-04:00
draft: false
tags: []
math: true
medium_enabled: true
---

One technique for making decisions in uncertain situations is to look for *optionality*. This is one of the tips given in Russ Robert's book [Wild problems: a guide to the decisions that define us](https://www.worldcat.org/title/1321820629). Let's start off with the two definitions listed on [Wiktionary](https://en.wiktionary.org/wiki/optionality) at my time of writing.

## Definitions and Formalisms

> 1. (finance, business) The value of additional optional investment opportunities available only after having made an initial investment.
> 2. Quality of state in which choice or discretion is allowed.

To get to the meanings in the context of decision theory, we'll unpack these two definitions individually.

### For definition (1):

After having made an action, additional actions are made available as well as its associated value or utility.

Let's call $A_t$ the action set at time $t$. After having made some action $a$, the action set $A_{t + 1}$ contains the actions in $A_t$ as well as some additional actions $a_{n + 1}, \dots, a_{n + m}$. The values for the new state action are also known, e.g $V(s, a_{n + 1}), \dots, V(s, a_{n + m})$.

In this definition, optionality gives us additional actions and more information.

### For definition (2):

In the current state, the agent is free to choose any of the available actions. In other words, they are not obligated to choose any particular action.

### From the book:

Now let's discuss how the book uses the word optionality.

> Optionality is when you have the freedom to do something but not the obligation.

In the context of decision making, what do we consider the obligation of a choice or action? One way to approach this is through the lens of automated planning. Within that field, each action has a precondition and effect. For an action to be applicable (or available to choose), the precondition must be met. Once you perform the action, the effects are made true.

We can then roughly define obligation as the commitment to the effects of an action.[^1] In other words, after getting an effect from the performance of an action, we do not change the effect later on.

#### Vampire Problem

Now consider the [Vampire problem](/blog/value-shift/). If an agent $\mathfrak{a}$ who is currently human performs the action $a_{transform}$, the agent loses the property human and becomes a vampire. In the context of this problem, there is no going back. The agent cannot change from being a vampire. In other words, the agent is committed to being a vampire. Thus, the agent is obligated after transforming.

In a more technical sense, obligation enforces monotonicity. If an agent is obligated, once a property is gained, it cannot be lost.

Many choices, however, do not incur an obligation. Let's say I perform the action of moving my coffee mug from the living room to the kitchen. I am not obligated after performing that action. In fact, I'm free to move it back to the living room.

#### Revertability

This gets to a property that is *stronger* than optionality but bears mentioning. Revertability.

In this context, an action $a$ is revertible if the agent can perform a sequence of actions that *undos* the effects of $a$.  Non-obligation (in our definition) is weaker since we only need to be able to change one effect of $a$.

My proposed formalism of the book's definition is different than the other two formalisms. If I had to categorize it, I would say that it is a stricter form of (2).

## Risk Aversion

Parts of optionality can be captured by risk aversion. Though I have not formally considered the topic yet, my preliminary thoughts go in two directions when considering risk:[^2]

1. Maximize the possible actions available in the future.
2. Minimize negative consequences

 In the face of uncertainty, how do we maximize the possible actions available in the future? One solution I propose is to choose actions that are revertable.

Why? Let's say that we're in a state $s_t$ and the available actions are $\{a, b, c\}$. Now let's say we take action $a$ which takes us to state $s_{t + 1}$. Within the new state, the available actions are $\{d, e, f\}$ where applying $d$ takes us back to state $s_t$. Notice that the action $a$ is revertable. Performing the action unlocked additional actions while keeping $b,c$ only a revert action ($d$) away.

## Conclusion

When reasoning about an uncertain situation, consider selecting the action that does not commit you to the effects of said action. Look for actions that are revertable, as that expands the possible choices in the future.

Acknowledgements: Thanks to Clare for helping me understand the definitions from Wiktionary.

[^1]: There are other ways we can define obligation. In particular, we can take into account each individual effect as opposed to it collectively. Though we'll leave that for another time.

[^2]: I do not discuss minimizing negative consequences in this post as it has little connection to the concept of optionality. 



