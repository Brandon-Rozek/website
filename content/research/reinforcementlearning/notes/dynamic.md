---
title: Chapter 4 - Dynamic Programming
showthedate: false
math: true
---

Dynamic programming refers to a collection of algorithms that can be used to compute optimal policies given a perfect model of the environment as a Markov decision process (MDP).

Classic DP algorithms are of limited utility due to their assumption of a perfect model and their great computational expense.

Let's assume that the environment is a finite MDP. We assume its state, action, and reward sets, $\mathcal{S}, \mathcal{A}, \mathcal{R}$ are finite, and that its dynamics are given by a set of probabilities $p(s^\prime, r | s , a)$.

The key idea of dynamic programming, and of reinforcement learning is the use of value functions to organize and structure the search for good policies. In this chapter, we show how dynamic programming can be used to compute the value functions defined in Chapter 3. We can easily obtain optimal policies once we have found the optimal value functions which satisfy the Bellman optimality equations.

## Policy Evaluation

First we consider how to compute the state-value function for an arbitrary policy. The existence and uniqueness of a state-value function for an arbitrary policy are guaranteed as long as either the discount rate is less than one or eventual termination is guaranteed from all states under the given policy.

Consider a sequence of approximate value functions. The initial approximation, $v_0$, is chosen arbitrarily (except that the terminal state must be given a value of zero) and each successive approximation is obtained by using the Bellman equation for $v_\pi$ as an update rule:
$$
v_{k + 1} = \sum_{a}{\pi(a |s)\sum_{s^\prime, r}{p(s^\prime,r|s,a)[r + \gamma v_k(s^\prime)]}}
$$
This algorithm is called *iterative policy evaluation*.

To produce each successive approximation, $v_{k + 1}$ from $v_k$, iterative policy evaluation applies the same operation to each state $s$: it replaces the old value of $s$ with a new value obtained from the old values of the successor states of $s$, and the expected immediate rewards, along all the one-step transitions possible under the policy being evaluated.

<u>**Iterative Policy Evaluation**</u>

```
Input π, the policy to be evaluated
Initialize an array V(s) = 0, for all s ∈ S+
Repeat
  ∆ ← 0
  For each s ∈ S:
    v ← V(s)
    V(s) ← ∑_a π(a|s) ∑_s′,r p(s′,r|s,a)[r+γV(s′)]
    ∆ ← max(∆,|v−V(s)|)
until ∆ < θ (a small positive number)
Output V ≈ v_π
```

### Grid World Example

Consider a grid world where the top left and bottom right squares are the terminal state. Now consider that every other square, produces a reward of -1, and the available actions on each state is {up, down, left, right} as long as that action keeps the agent on the grid. Suppose our agent follows the equiprobable random policy. 

![1540262811089](/home/rozek/Documents/Research/Reinforcement Learning/1540262811089.png)

## Policy Improvement

One reason for computing the value function for a policy is to help find better policies. Suppose we have determined the value function $v_\pi$ for an arbitrary deterministic policy $\pi$. For some state $s$ we would like to know whether or not we should change the policy to determinatically chose another action. We know how good it is to follow the current policy from $s$, that is $v_\pi(s)$, but would it be better or worse to change to the new policy? 

One way to answer this question is to consider selecting $a$ in $s$ and thereafter follow the existing policy, $\pi$. The key criterion is whether the this produces a value greater than or less than $v_\pi(s)$. If it is greater, then one would expect it to be better still to select $a$ every time $s$ is encountered, and that the new policy would in fact be a better one overall.

That this is true is a special case of a general result called the *policy improvement theorem*. Let $\pi$ and $\pi^\prime$ be any pair of deterministic policies such that for all $s \in \mathcal{S}$.
$$
q_\pi(s, \pi^\prime(s)) \ge v_\pi(s)
$$
So far we have seen how, given a policy and its value function, we can easily evaluate a change in the policy at a single state to a particular action. It is a natural extension to consider changes at all states and to all possible actions, selecting at each state the action that appears best according to $q_\pi(s, a)$. In other words, to consider the new *greedy* policy, $\pi^\prime$, given by:
$$
\pi^\prime = argmax (q_\pi(s, a))
$$
So far in this section we have considered the case of deterministic policies. We will not go through the details, but in fact all the ideas of this section extend easily to stochastic policies.

## Policy Iteration

Once a policy, $\pi$, has been improved using $v_\pi$ to yield a better policy, $\pi^\prime$, we can then compute $v_{\pi^\prime}$ and improve it again to yield an even better $\pi^{\prime\prime}$. We can thus obtain a sequence of monotonically improving policies and value functions.

Each policy is guaranteed to be a strict improvement over the previous one (unless its already optimal). Since a finite MDP has only a finite number of policies, this process must converge to an optimal policy and optimal value function in a finite number of iterations.

This way of finding an optimal policy is called *policy iteration*.

<u>Algorithm</u>

```
1.  Initialization
  V(s) ∈ R and π(s) ∈ A(s) arbitrarily for all s ∈ S
2.  Policy Evaluation
  Repeat
    ∆ ← 0
    For each s∈S:
      v ← V(s)
      V(s) ← ∑_{s′,r} p(s′,r|s,π(s))[r + γV(s′)]
      ∆ ← max(∆,|v − V(s)|)
  until ∆ < θ (a small positive number)
3.  Policy Improvement
  policy-stable ← true
  For each s ∈ S:
    old-action ← π(s)
    π(s) ← arg max_a ∑_{s′,r} p(s′,r|s,a)[r + γV(s′)]
    If old-action != π(s), then policy-stable ← false
  If policy-stable, then stop and return V ≈ v_∗,
  and π ≈ π_∗; else go to 2
```

## Value Iteration

One drawback to policy iteration is that each of its iterations involve policy evaluation, which may itself be a protracted iterative computation requiring multiple sweeps through the state set. If policy evaluation is done iteratively, then convergence exactly to $v_\pi$ occurs only in the limit. Must we wait for exact convergence, or can we stop short of that?

In fact, the policy evaluation step of policy iteration can be truncated in several ways without losing the convergence guarantee of policy iteration. One important special case is when policy evaluation is stopped after one sweep. This algorithm is called value iteration. 

Another way of understanding value iteration is by reference to the Bellman optimality equation. Note that value iteration is obtained simply by turning the Bellman optimality equation into an update rule. Also note how value iteration is identical to the policy evaluation update except that it requires the maximum to be taken over all actions.

Finally, let us consider how value iteration terminates. Like policy evaluation, value iteration formally requires an infinite number of iterations to converge exactly. In practice, we stop once the value function changes by only a small amount.

```
Initialize array V arbitrarily (e.g., V(s) = 0 for all
s ∈ S+)

Repeat
  ∆ ← 0
  For each s ∈ S:
    v ← V(s)
    V(s) ← max_a∑_{s′,r} p(s′,r|s,a)[r + γV(s′)]
    ∆ ← max(∆, |v − V(s)|)
until ∆ < θ (a small positive number)

Output a deterministic policy, π ≈ π_∗, such that
  π(s) = arg max_a ∑_{s′,r} p(s′,r|s,a)[r + γV(s′)]
```

Value iteration effectively combines, in each of its sweeps, one sweep of policy evaluation and one sweep of policy improvement. Faster convergence is often achieved by interposing multiple policy evaluation sweeps between each policy improvement sweep. 

## Asynchronous Dynamic Programming

*Asynchronous* DP algorithms are in-place DP algorithms that are not organized in terms of systematic sweeps of the state set. These algorithms update the values of states in any order whatsoever, using whatever value of other states happen to be available.

To converge correctly, however, an asynchronous algorithm must continue to update the value of all the states: it can't ignore any state after some point in the computation.

## Generalized Policy Iteration

Policy iteration consists of two simultaneous, iterating processes, one making the value function consistent with the current policy (policy evaluation) and the other making the policy greedy with respect to the current value function (policy improvement).

We use the term *generalized policy iteration* (GPI) to competing and cooperating. They compete in the sense that they pull in opposing directions. Making the policy greedy with respect to the value function typically makes the value function incorrect for the changed policy. Making the value function consistent with the policy typically causes the policy to be greedy. In the long run, however, the two processes interact to find a single joint solution. 

