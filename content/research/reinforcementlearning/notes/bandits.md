---
title: Chapter 2 - Multi-armed Bandits
showthedate: false
math: true
---

Reinforcement learning *evaluates* the actions taken rather than accepting $instructions$ of the correct actions. This creates the need for active exploration. 

This chapter of the book goes over a simplified version of the reinforcement learning problem, that does not involve learning to act in more than one situation. This is called a *nonassociative* setting.

In summation, the type of problem we are about to study is a nonassociative, evaluative feedback problem that is a simplified version of the $k$-armed bandit problem.

##  $K$-armed bandit problem

Consider the following learning problem. You are faced repeatedly with a choice among $k$ different options/actions. After each choice you receive a numerical reward chosen from a stationary probability distribution that depends on the action you selected.

Your objective (if you choose to accept it) is to maximize the expected total reward over some time period. Let's say $1000$ time steps.

### Analogy

This is called the $k$-armed bandit problem because it's an analogy of a slot machine. Slot machines are nick-named the "one-armed bandit", and the goal here is to play the slot machine that has the greatest value return.

### Sub-goal

We want to figure out which slot machine produces the greatest value. Therefore, we want to be able to estimate the value of a slot machine as close to the actual value as possible.

### Exploration vs Exploitation

If we maintain estimates of the action values, then at any time step there is at least one action whose estimated value is the greatest. We call these *greedy* actions. When you select one of these actions we say that you are *exploiting* your current knowledge of the values of the actions. 

If you instead select a non-greedy action, then you are *exploring*, because this enables you to better improve your estimate of the non-greedy action's value.

Uncertainty is such that at least one of the other actions probably better than the greedy action, you just don't know which one yet.

## Action-value Methods

In this section, we will look at simple balancing methods in how to gain the greatest reward through exploration and exploitation.

We begin by looking more closely at some simple methods for estimating the values of actions and for using said estimates to make action selection decisions.

### Sample-average method

One natural way to estimate this is by averaging the rewards actually received
$$
Q_t(a) = \frac{\sum_{i = 1}^{t - 1}R_i * \mathbb{I}_{A_i = 1}}{\sum_{i = 1}^{t - 1}\mathbb{I}_{A_i = 1}}
$$
where $\mathbb{I}_{predicate}$ denotes the random variable that is 1 if the predicate is true and 0 if it is not. If the denominator is zero (we have not experienced the reward), then we assume some default value such as zero. 

### Greedy action selection

This is where you choose greedily all the time.
$$
A_t = argmax_a(Q_t(a))
$$

###  $\epsilon$-greedy action selection

This is where we choose greedily most of the time, except for a small probability $\epsilon$. Where instead of selecting greedily, we select randomly from among all the actions with equal probability.

### Comparison of greedy and $\epsilon$-greedy methods

The advantage of $\epsilon$-greedy over greedy methods depends on the task. With noisier rewards it takes more exploration to find the optimal action, and $\epsilon$-greedy methods should fare better relative to the greedy method. However, if the reward variances were zero, then the greedy method would know the true value of each action after trying it once.

Suppose the bandit task were non-stationary, that is, the true values of actions changed over time. In this case exploration is needed to make sure one of the non-greedy actions has not changed to become better than the greedy one.

### Incremental Implementation

There is a way to update averages using small constant computations rather than storing the the numerators and denominators separate.

Note the derivation for the update formula
$$
\begin{align}
Q_{n + 1} &= \frac{1}{n}\sum_{i = 1}^n{R_i} \\
&= \frac{1}{n}(R_n + \sum_{i = 1}^{n - 1}{R_i}) \\
&= \frac{1}{n}(R_n + (n - 1)\frac{1}{n-1}\sum_{i = 1}^{n - 1}{R_i}) \\
&= \frac{1}{n}{R_n + (n - 1)Q_n} \\
&= \frac{1}{n}(R_n + nQ_n - Q_n) \\
&= Q_n + \frac{1}{n}(R_n - Q_n) \tag{2.3}
\end{align}
$$
With formula 2.3, the implementation requires memory of only $Q_n$ and $n$.

This update rule is a form that occurs frequently throughout the book. The general form is
$$
NewEstimate = OldEstimate + StepSize(Target - OldEstimate)
$$

### Tracking a Nonstationary Problem

As noted earlier, we often encounter problems that are nonstationary, in such cases it makes sense to give more weight to recent rewards than to long-past rewards. One of the most popular ways to do this is to use a constant value for the $StepSize​$ parameter. We modify formula 2.3 to be
$$
\begin{align}
Q_{n + 1} &= Q_n + \alpha(R_n - Q_n) \\
&= \alpha R_n + Q_n - \alpha Q_n \\
&= \alpha R_n + (1 - \alpha)Q_n \\
&= \alpha R_n + (1 - \alpha)(\alpha R_{n - 1} + (1-\alpha)Q_{n - 1}) \\
&= \alpha R_n + (1 - \alpha)(\alpha R_{n - 1} + (1-\alpha)(\alpha R_{n - 2} + (1 - a)Q_{n - 2})) \\
&= \alpha R_n + (1-\alpha)\alpha R_{n - 1} + (1-\alpha)^2\alpha R_{n - 2} + \dots + (1-\alpha)^nQ_1 \\
&= (1-\alpha)^nQ_1 + \sum_{i = 1}^n{\alpha(1-\alpha)^{n - i}R_i}
\end{align}
$$
This is a weighted average since the summation of all the weights equal one. Note here that the farther away a value is from the current time, the more times $(1-\alpha)$ gets multiplied by itself. Hence making it less influential. This is sometimes called an *exponential recency-weighted average*.

### Manipulating $\alpha_n(a)$

Sometimes it is convenient to vary the step-size parameter from step to step. We can denote $\alpha_n(a)$ to be a function that determines the step-size parameter after the $n$th selection of action $a$. As noted before $\alpha_n(a) = \frac{1}{n}$ results in the sample average method which is guaranteed to converge to the truth action values assuming a large number of trials. 

A well known result in stochastic approximation theory gives us the following conditions to assure convergence with probability 1:
$$
\sum_{n = 1}^\infty{\alpha_n(a) = \infty} \and \sum_{n = 1}^{\infty}{\alpha_n^2(a) \lt \infty}
$$
The first condition is required to guarantee that the steps are large enough to overcome any initial conditions or random fluctuations. The second condition guarantees that eventually the steps become small enough to assure convergence.

**Note:** Both convergence conditions are met for the sample-average case but not for the constant step-size parameter. The latter condition is violated in the constant parameter case. This is desirable since if the rewards are changing then we don't want it to converge to any one parameter.

### Optimistic Initial Values

The methods discussed so far are biased by their initial estimates. Another downside  is that these values are another set of parameters that must be chosen by the user. Though these initial values can be used as a simple way to encourage exploration.

Let's say you set an initial estimate that is wildly optimistic. Whichever actions are initially selected, the reward is less than the starting estimates. Therefore, the learner switches to other actions, being *disappointed* with the rewards it was receiving. 

The result of this is that all actions are tried several times before their values converge. It even does this if the algorithm is set to choose greedily most of the time!  

![1536284892566](/home/rozek/Pictures/1536284892566.png)

This simple trick is quite effective for stationary problems. Not so much for nonstationary problems since the drive for exploration only happens at the beginning. If the task changes, creating a renewed need for exploration, this method would not catch it.

### Upper-Confidence-Bound Action Selection

Exploration is needed because there is always uncertainty about the accuracy of the action-value estimates. The greedy actions are those that look best at the present but some other options may actually be better. Let's choose options that have potential for being optimal, taking into account how close their estimates are to being maximal and the uncertainties in those estimates.
$$
A_t = argmax_a{(Q_t(a) + c\sqrt{\frac{ln(t)}{N_t(a)}})}
$$
where $N_t(a)$ denotes the number of times that $a$ has been selected prior to time $t$ and $c > 0$ controls the degree of exploration.

###Associative Search (Contextual Bandits)

So far, we've only considered nonassociative tasks, where there is no need to associate different actions with different situations. However, in a general reinforcement learning task there is more than one situation and the goal is to learn a policy: a mapping from situations to the actions that are best in those situations.

For sake of continuing our example, let us suppose that there are several different $k$-armed bandit tasks, and that on each step  you confront one of these chosen at random. To you, this would appear as a single, nonstationry $k$-armed bandit task whose true action values change randomly from step to step. You could try using one of the previous methods, but unless the true action values change slowly, these methods will not work very well.

Now suppose, that when a bandit task is selected for you, you are given some clue about its identity. Now you can learn a policy association each task, singled by the clue, with the best action to take when facing that task.

This is an example of an *associative search* task, so called because it involves both trial-and-error learning to *search* for the best actions, and *association* of these actions with situations in which they are best. Nowadays they're called *contextual bandits* in literature.

If actions are allowed to affect the next situation as well as the reward, then we have the full reinforcement learning problem. This will be presented in the next chapter of the book with its ramifications appearing throughout the rest of the book.

![1536321791927](/home/rozek/Pictures/1536321791927.png)
