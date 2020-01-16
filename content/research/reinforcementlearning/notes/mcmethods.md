# Chapter 5: Monte Carlo Methods

Monte Carlo methods do not assume complete knowledge of the environment. They require only *experience* which is a sample sequence of states, actions, and rewards from actual or simulated interaction with an environment. 

Monte Carlo methods are ways of solving the reinforcement learning problem based on averaging sample returns. To ensure that well-defined returns are available, we define Monte Carlo methods only for episodic tasks. Only on the completion of an episode are value estimates and policies changed. 

Monte Carlo methods sample and average returns for each state-action pair is much like the bandit methods explored earlier. The main difference is that there are now multiple states, each acting like a different bandit problems and the problems are interrelated. Due to all the action selections undergoing learning, the problem becomes nonstationary from the point of view of the earlier state.

## Monte Carlo Prediction

Recall that the value of a state is the expected return -- expected cumulative future discounted reward - starting from that state. One way to do it is to estimate it from experience by averaging the returns observed after visits to that state.

Each occurrence of state $s$ in an episode is called a *visit* to $s$. The *first-visit MC method* estimates $v_\pi(s)$ as the average of the returns following first visits to $s$, whereas the *every-visit MC method* averages the returns following all visits to $s$. These two Monte Carlo methods are very similar but have slightly different theoretical properties. 

<u>First-visit MC prediction</u>

```
Initialize:
  π ← policy to be evaluated
  V ← an arbitrary state-value function
  Returns(s) ← an empty list, for all s ∈ S

Repeat forever:
  Generate an episode using π 
  For each state s appearing in the episode:
    G ← the return that follows the first occurrence of
s
    Append G to Returns(s)
    V(s) ← average(Returns(s))
```

## Monte Carlo Estimation of Action Values

If a model is not available then it is particularly useful to estimate *action* values rather than state values. With a model, state values alone are sufficient to define a policy. Without a model, however, state values alone are not sufficient. One must explicitly estimate the value of each action in order for the values to be useful in suggesting a policy. 

The only complication is that many state-action pairs may never be visited. If $\pi$ is a deterministic policy, then in following $\pi$ one will observe returns only for one of the actions from each state. With no returns to average, the Monte Carlo estimates of the other actions will not improve with experience. This is a serious problem because the purpose of learning action values is to help in choosing among the actions available in each state. 

This is the general problem of *maintaining exploration*. For policy evaluation to work for action values, we must assure continual exploration. One way to do this is by specifying that the episodes *start in a state-action pair*, and that each pair has a nonzero probability of being selected as the start. We call this the assumption of *exploring starts*.

## Monte Carlo Control

We made two unlikely assumptions above in order to easily obtain this guarantee of convergence for the Monte Carlo method. One was that the episodes have exploring starts, and the other was that policy evaluation could be done with an infinite number of episodes. 

<u>Monte Carlo Exploring Starts</u>

```
Initialize, for all s ∈ S, a ∈ A(s):
  Q(s,a) ← arbitrary
  π(s) ← arbitrary
  Returns(s,a) ← empty list

Repeat forever:
  Choose S_0 ∈ S and A_0 ∈ A(S_0) s.t. all pairs have probability > 0
  Generate an episode starting from S_0,A_0, following
π
  For each pair s,a appearing in the episode:
    G ← the return that follows the first occurrence of
s,a
    Append G to Returns(s,a)
    Q(s,a) ← average(Returns(s,a))
  For each s in the episode:
    π(s) ← arg max_a Q(s,a)
```

## Monte Carlo Control without Exploring Starts

The only general way to ensure that actions are selected infinitely often is for the agent to continue to select them. There are two approaches ensuring this, resulting in what we call *on-policy* methods and *off-policy* methods. 

On-policy methods attempt to evaluate or improve the policy that is used to make decisions, whereas off-policy methods evaluate or improve a policy different from that used to generate the data.

In on-policy control methods the policy is generally *soft*, meaning that $\pi(a|s)$ for all $a \in \mathcal{A}(s)$. The on-policy methods in this section uses $\epsilon$-greedy policies, meaning that most of the time they choose an action that has maximal estimated action value, but with probability $\epsilon$ they instead select an action at random. 

<u>On-policy first-visit MC control (for $\epsilon$-soft policies)</u>

```

```

Initialize, for all $s \in \mathcal{S}$, $a \in \mathcal{A}(s)$:

  $Q(s, a)$ ← arbitrary

  $Returns(s,a)$ ← empty list

  $\pi(a|s)$ ← an arbitrary $\epsilon$-soft policy

Repeat forever:

  (a) Generate an episode using $\pi$

  (b) For each pair $s,a$ appearing in the episoe

​    $G$ ← the return that follows the first occurance of s, a

​    Append $G$ to $Returns(s,a)$

​    $Q(s, a)$ ← average($Returns(s,a)$)

  (c) For each $s$ in the episode:

​    $A^*$ ← argmax$_a Q(s,a)$       (with ties broken arbitrarily)

​    For all $a \in \mathcal{A}(s)$:

​      $\pi(a|s)$ ← $\begin{cases} 1 - \epsilon + \epsilon / |\mathcal{A}(s)| &  a = A^* \\ \epsilon / | \mathcal{A}(s)| & a \neq A^*  \end{cases}$

```

```

