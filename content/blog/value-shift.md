---
title: "Explaining the Shift in Values"
date: 2022-10-11T20:19:01-04:00
draft: false 
tags: []
math: true
medium_enabled: true
---

In the book [Wild problems : a guide to the decisions that define us](https://www.worldcat.org/title/1321820629), Russ Roberts analyzes decision making on difficult life problems. These types of problems don't have straightforward or measurable goals, and there's no set procedure for success. Examples of these problems are choosing whether to marry, have kids, or switch jobs.


Russ Roberts is an economist, however, he starts the book
by showing how economic principles cannot be easily
applied to arrive at a decision for these problems.
Economic principles are grounded in the utilitarian approach to ethics. In it, a utility function is defined which measures how much benefits outweighs the costs within a certain situation.

In a mathematical formulation, we would define it like the following:
$$
u_\mathfrak{a}(s) \rightarrow \mathbb{R}
$$

If the utility is positive, then we say that there are more benefits than downsides. If negative, then vice versa. As differing agents have different preferences,
the utility function is dependent upon the agent $\mathfrak{a}$. The input of the function is some *state* $s$ which represents the environment that the agent is in. The output is a continuous real number. 

A rational action in this context is the one that provides the highest utility in the next state.
$$
a_{rational} = argmax_a(u_\mathfrak{a}(P(s,a)))
$$
In the last equation $P(s, a)$ provides the state that the agent finds themselves in after performing the action $a$ in their current state $s$.

In sequential decision making, a popular formalism is the Markov Decision Process. This defines a tuple $\langle S,A, P, R \rangle$ where:

- $S$ represents the set of states
- $A$ represents the set of actions
- $P$ represents the transition function between states via the actions
- $R$ represents the reward function based on a state and action

Initially, I'll talk about deterministic MDPs. This means that the state after performing a state and action pair is always the same.

One popular approach to solving these problems is through value iteration. This approach is characterized by the Bellman Equation:
$$
V(s) = max_a(R(s,a) + \gamma V(P(s,a)))
$$
This says that the value of the current state is the highest combination possible between the direct reward for some action $a$ and the discounted value of the next state.

Russ Roberts didn't mention MDPs in his book, but I think he had something similar in mind when he writes about the difficulty of computing utility given a wild problem. One example he uses, comes from L.A. Paul and her book [Transformative Experience](https://www.worldcat.org/title/872342141).

**The Vampire Problem**

> Before you become a vampire, you can't really imagine what it will be like. Your current experience doesn't include what it's like to subsist on blood and sleep in a coffin when the sun is shining. Sounds dreary? But most, maybe all, of the vampires you meet speak quite highly of the experience. Surveys of vampires reveal a high degree of happiness.

Russ then remarks on one of his key points.

> One of the weirdest parts of the decision, as Paul pints out, is that once you become a vampire, what you like and what you dislike change.

Let's look at it in terms of value iteration. The value of becoming a vampire is equal to the reward during the initial transformation plus the discounted value of living life after the transformation.
$$
V(s_{human}, a_{transform}) = R(s_{human}, a_{transform}) + \gamma V(P(s_{human}, a_{transform}))
$$
We know that the state after transforming as a human is becoming a vampire so,
$$
V(s_{human}, a_{transform})  = R(s_{human}, a_{transform}) + \gamma V(s_{vampire})
$$
The issue, Russ implies, is that an agent has no way of approximating $V(s_{human}, a_{transform})$.

Given the formalism, what are some possible reasons why we don't know this?

1. The agent does not know the action it performed.
2. The agent doesn't fully know the function $R$.
3. The agent does not have knowledge about the entire state.

## Not Knowing the Action

When an agent performs the action $a_{transform}$ does it know that it performed that specific action? One way of looking at this is to see if the agent is able to tell apart any two arbitrary actions, say $a_{transform}$ and $a_{morph}$. I don't believe this problem is well studied in literature. Do let me know if you know of any literature covering an agent confusing actions.

In the case of the vampire problem, it's likely safe to assume that the human knows the transformation action.

## Not Knowing $R$

Previously, we assumed that the agent knows
the reward for any given state action pair.
Now let's relax that assumption. One way we can
do that is by considering non-deterministic
MDPs.

Imagine there is a slot machine that either provides
\\$20 or consumes your \\$1 coin with some probability.
Traditionally, we would represent the reward function
as an expected value.

$$
R(s, a) = \Sigma_{p, s^\prime \in P(s, a)}{(p * R(s,a,s^\prime))}
$$

In many real world situations, the probabilities ($p$) of
states are not specified. One popular approach to
this issue is by sampling. If we can simulate the outcomes, then we can roughly know the probabilities
of each transition with some level of certainty.

Simulating the state transition may be impossible.
In my daily life, I often make use of testimonial
evidence when making decisions. These can serve
as a rough estimation of value, though the states
of the other party may not line up exactly with yours.


## Partial Observability

Are we able to perceive the entirety of
a state? If not, within the field of
sequential decision making, we call the
problem *partially observable*.

Two reasons immediately come to mind for why partial observability exists.
- Compromised Perception: A state in which the agent's perception only captures a subset of the total information. For example, heavy fog covers the roadway
limiting visibility of other traffic.
- Group Decision Making: Agents often don't have insight to other's thought processes or perceptions.


One popular way of modeling this is through
the introduction of belief states. A belief
state encapsulates the set of possible states.
For example, let's say that I prefer heads on a
quarter than tails. I don't know what my friend
prefers, but I can capture the possibilities in a
belief state.

$$
b = \{ (Me_{heads}, Friend_{heads}), (Me_{heads}, Friend_{tails}) \}
$$

The hope is that by keeping track of the
list of possible states, when we are interacting
with the environment, we can filter out impossible
transitions until we get to a single possibility.
However, there's no guarantee that this will occur.
Also the initial belief state may be infinitely long.

Another way that we can hope to tackle this issue
is by only focusing on important information in the
state or observation. Many details in our daily lives
are irrelevant for a specific task at hand.
We can perform a state reduction in order to have a
smaller set of possible states to work with.
This involves identifying what pieces of information
are important to a task, and what we can disregard.


## Conclusion

Overall this book has been a great read so far
and has gotten me thinking about decision making
in a general sense again. There are some promising
research directions that come from this:
- How can you approximate a reward from testimonial evidence?
- Techniques for performing state reduction and modeling transitions via these reductions.

Thank you to both Clare and James for helping me brainstorm the ideas in this post.
