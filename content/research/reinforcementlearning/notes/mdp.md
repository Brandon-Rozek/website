# Chapter 3: Finite Markov Decision Processes

Markov Decision processes are a classical formalization of sequential decision making, where actions influence not just immediate rewards, but also subsequent situations, or states, and through those future rewards. Thus MDPs involve delayed reward and the need to trade-off immediate and delayed reward. Whereas in bandit problems we estimated the value of $q_*(a)$ of each action $a$, in MDPs we estimate the value of $q_*(s, a)$ of each action $a$ in state $s$. 

MDPs are a mathematically idealized form of the reinforcement learning problem. As we will see in artificial intelligence, there is often a tension between breadth of applicability and mathematical tractability. This chapter will introduce this tension and discuss some of the trade-offs and challenges that it implies. 

## Agent-Environment Interface

The learner and decision maker is called the *agent*. The thing it interacts with is called the *environment*. These interact continually, the agent selecting actions and the environment responding to these actions and presenting new situations to the agent.

The environment also give rise to rewards, special numerical values that the agent seeks to maximize over time through its choice of actions.

![1536511147205](/home/rozek/Documents/Research/Reinforcement Learning/1536511147205.png)

To make the future paragraphs clearer, a Markov Decision Process is a discrete time stochastic control process. It provides a mathematical framework for modeling decision making in situations where outcomes are partly random and partly under the control of the decision maker.

In a *finite* MDP, the set of states, actions, and rewards all have a finite number of elements. In this case, the random variables R_t and S_t have a well defined discrete probability distribution dependent only on the preceding state and action.
$$
p(s^\prime | s,a) = \sum_{r \in \mathcal{R}}{p(s^\prime, r|s, a)}
$$
Breaking down the above formula, it's just an instantiation of the law of total probability. If you partition the probabilistic space by the reward, if you sum up each partition you should get the overall space. This formula has a special name: the *state-transition probability*.

From this we can compute the expected rewards for each state-action pair by multiplying each reward with the probability of getting said reward and summing it all up.
$$
r(s, a) = \sum_{r \in \mathcal{R}}{r}\sum_{s^\prime \in \mathcal{S}}{p(s^\prime, r|s,a)}
$$
The expected reward for a state-action-next-state triple is
$$
r(s, a, s^\prime) = \sum_{r \in \mathcal{R}}{r\frac{p(s^\prime, r|s,a)}{p(s^\prime|s,a)}}
$$
I wasn't able to piece together this function in my head like the others. Currently I imagine it as if we took the formula before and turned the universe of discourse from the universal set to the state where $s^\prime$ occurred.

The MDP framework is abstract and flexible and can be applied to many different problems in many different ways. For example, the time steps need not refer to fixed intervals of real time; they can refer to arbitrary successive states of decision making and acting.

### Agent-Environment Boundary

In particular, the boundary between agent and environment is typically not the same as the physical boundary of a robot's or animals' body. Usually, the boundary is drawn closer to the agent than that. For example, the motors and mechanical linkages of a robot and its sensing hardware should usually be considered parts of the environment rather than parts of the agent.

The general rule we follow is that anything that cannot be changed arbitrarily by the agent is considered to be outside of it and thus part of its environment. We do not assume that everything in the environment is unknown to the agent. For example, the agent often knows quite a bit about how its rewards are computed as a function of its actions and the states in which they are taken. But we always consider the reward computation to be external to the agent because it defines the task facing the agent and thus must be beyond its ability to change arbitrarily. The agent-environment boundary represents the limit of the agent's absolute control, not of its knowledge.

This framework breaks down whatever the agent is trying to achieve to three signals passing back and forth between an agent and its environment: one signal to represent the choices made by the agent, one signal to represent the basis on which the choices are made (the states), and one signal to define the agent's goal (the rewards).

### Example 3.4: Recycling Robot MDP

Recall that the agent makes a decision at times determined by external events. At each such time the robot decides whether it should

(1) Actively search for a can

(2) Remain stationary and wait for someone to bring it a can

(3) Go back to home base to recharge its battery

Suppose the environment works as follows: the best way to find cans is to actively search for them, but this runs down the robot's battery, whereas waiting does not. Whenever the robot is searching the possibility exists that its battery will become depleted. In this case, the robot must shut down and wait to be rescued (producing a low reward.)

The agent makes its decisions solely as a function of the energy level of the battery, It can distinguish two levels, high and low, so that the state set is $\mathcal{S} = \{high, low\}$.  Let us call the possible decisions -- the agent's actions -- wait, search, and recharge. When the energy level is high, recharging would always be foolish, so we do not include it in the action set for this state. The agent's action sets are
$$
\begin{align*}
\mathcal{A}(high) &= \{search, wait\} \\
\mathcal{A}(low)  &= \{search, wait, recharge\}
\end{align*}
$$
If the energy level is high, then a period of active search can always be completed without a risk of depleting the battery. A period of searching that begins with a high energy level leaves the energy level high with a probability of $\alpha$ and reduces it to low with a probability of $(1 - \alpha)$. On the other hand, a period of searching undertaken when the energy level is low leaves it low with a probability of $\beta$ and depletes the battery with a probability of $(1 - \beta)$. In the latter case, the robot must be rescued, and the batter is then recharged back to high.

Each can collected by the robot counts as a unit reward, whereas a reward of $-3$ occurs whenever the robot has to be rescued. Let $r_{search}$ and $r_{wait}$ with $r_{search } > r_{wait}$, respectively denote the expected number of cans the robot will collect while searching and waiting. Finally, to keep things simple, suppose that no cans can be collected ruing a run home for recharging and that no cans can be collected on a step in which the battery is depleted.

| $s$  | $a$      | $s^\prime$ | $p(s^\prime   | s, a)$       | $r(s|
| ---- | -------- | ---------- | ------------- | ------------ | --- |
| high | search   | high       | $\alpha$      | $r_{search}$ |
| high | search   | low        | $(1-\alpha)$  | $r_{search}$ |
| low  | search   | high       | $(1 - \beta)$ | -3           |
| low  | search   | low        | $\beta$       | $r_{search}$ |
| high | wait     | high       | 1             | $r_{wait}$   |
| high | wait     | low        | 0             | $r_{wait}$   |
| low  | wait     | high       | 0             | $r_{wait}$   |
| low  | wait     | low        | 1             | $r_{wait}$   |
| low  | recharge | high       | 1             | 0            |
| low  | recharge | low        | 0             | 0            |

A *transition graph* is a useful way to summarize the dynamics of a finite MDP. There are two kinds of nodes: *state nodes* and *action nodes*. There is a state node for each possible state and an action node for reach state-action pair. Starting in state $s$ and taking action $a$ moves you along the line from state node $s$ to action node $(s, a)$. The the environment responds with a transition ot the next states node via one of the arrows leaving action node $(s, a)$. 

![1537031348278](/home/rozek/Documents/Research/Reinforcement Learning/1537031348278.png)

## Goals and Rewards

The reward hypothesis is that all of what we mean by goals and purposes can be well thought of as the maximization of the expected value of the cumulative sum of a received scalar signal called the reward.

Although formulating goals in terms of reward signals might at first appear limiting, in practice it has proved to be flexible and widely applicable. The best way to see this is to consider the examples of how it has been, or could be used. For example:

- To make a robot learn to walk, researchers have provided reward on each time step proportional to the robot's forward motion. 
- In making a robot learn how to escape from a maze, the reward is often $-1$ for every time step that passes prior to escape; this encourages the agent to escape as quickly as possible.
- To make a robot learn to find and collect empty soda cans for recycling, one might give it a reward of zero most of the time, and then a reward of $+1$ for each can collected. One might also want to give the robot negative rewards when it bumps into things or when somebody yells at it. 
- For an agent to play checkers or chess, the natural rewards are $+1$ for winning, $-1$ for losing, and $0$ for drawing and for all nonterminal positions.

It is critical that the rewards we set up truly indicate what we want accomplished. In particular, the reward signal is not the place to impart to the agent prior knowledge about *how* to achieve what we want it to do. For example, a chess playing agent should only be rewarded for actually winning, not for achieving subgoals such as taking its opponent's pieces. If achieving these sort of subgoals were rewarded, then the agent might find a way to achieve them without achieving the real goal. The reward signal is your way of communicating what you want it to achieve, not how you want it achieved.

## Returns and Episodes

In general, we seek to maximize the *expected return*, where the return is defined as some specific function of the reward sequence. In the simplest case, the return is the sum of the rewards:
$$
G_t = R_{t + 1} + R_{t + 2} + R_{t + 3} + \dots + R_{T}
$$
where $T$ is the final time step. This approach makes sense in applications in which there is a natural notion of a final time step. That is when the agent-environment interaction breaks naturally into subsequences or *episodes*, such as plays of a game, trips through a maze, or any sort of repeated interaction.

### Episodic Tasks

Each episode ends in a special state called the *terminal state*, followed by a reset to the standard starting state or to a sample from a standard distribution of starting states. Even if you think of episodes as ending in different ways the next episode begins independently of how the previous one ended. Therefore, the episodes can all be considered to ending the same terminal states with different rewards for different outcomes. 

Tasks with episodes of this kind are called *episodic tasks*. In episodic tasks we sometimes need to distinguish the set of all nonterminal states, denoted $\mathcal{S}$, from the set of all states plus the terminal state, denoted $\mathcal{S}^+$. The time of termination, $T$, is a random variable that normally varies from episode to episode.

### Continuing Tasks

On the other hand, in many cases the agent-environment interaction goes on continually without limit. We call these *continuing tasks*. The return formulation above is problematic for continuing tasks because the final time step would be $T = \infty$, and the return which we are trying to maximize, could itself easily be infinite. The additional concept that we need is that of *discounting*. According to this approach, the agent tries to select actions so that the sum of the discounted rewards it receives over the future is maximized. In particular, it chooses $A_t$ to maximize the expected discounted return.
$$
G_t= \sum_{k = 0}^\infty{\gamma^kR_{t+k+1}}
$$
where $\gamma$ that is a parameter between $0$ and $1$ is called the *discount rate*.

#### Discount Rate

The discount rate determines the present value of future rewards: a reward received $k$ time steps in the future is worth only $\gamma^{k - 1}$ time what it would be worth if it were received immediately. If $\gamma < 1$, the infinite sum has a finite value as long as the reward sequence is bounded. 

If $\gamma = 0$, the agent is "myopic" in being concerned only with maximizing immediate rewards. But in general, acting to maximize immediate reward can reduce access to future rewards so that the return is reduced. 

As $\gamma$ approaches 1, the return objective takes future rewards into account more strongly; the agent becomes more farsighted.

### Example 3.5 Pole-Balancing

The objective in this task is to apply forces to a car moving along a track so as to keep a pole hinged to the cart from falling over.

A failure is said to occur if the pole falls past a given angle from the vertical or if the cart runs off the track.

![1537500975060](/home/rozek/Documents/Research/Reinforcement Learning/1537500975060.png)

#### Approach 1

The reward can be a $+1$ for every time step on which failure did not occur. In this case, successful balancing would mean a return of infinity.

#### Approach 2

The reward can be $-1$ on each failure and zero all other times. The return at each time would then be related to $-\gamma^k$ where $k$ is the number of steps before failure.



Either case the return is maximized by keeping the pole balanced for as long as possible. 

## Policies and Value Functions

Almost all reinforcement learning algorithms involve estimating *value functions* which estimate what future rewards can be expected. Of course the rewards that the agent can expect to receive is dependent on the actions it will take. Accordingly, value functions are defined with respect to particular ways of acting, called policies.

Formally, a *policy* is a mapping from states to probabilities of selecting each possible action. The *value* of a state s under a policy \pi, denoted $v_{\pi}(s)$ is the expected return when starting in $s$ and following $\pi$ thereafter. For MDPs we can define $v_{\pi}$ as

$$
v_{\pi}(s) = \mathbb{E}_{\pi}[G_t | S_t = s] = \mathbb{E}_{\pi}[\sum_{k = 0}^\infty{\gamma^kR_{t+k+1} | S_t = s}]
$$

We call this function the *state-value function for policy $\pi$*. Similarly, we define the value of taking action $a$ in state $s$ under a policy $\pi$, denoted as $q_\pi(s,a)$ as the expected return starting from $s$, taking the action $a$, and thereafter following the policy $\pi$. Succinctly, this is called the *action-value function for policy $\pi$*.

### Optimality and Approximation

For some kinds of tasks we are interested in,optimal policies can be generated only with extreme computational cost. A critical aspect of the problemfacing the agent is always teh computational power available to it, in particular, the amount of computation it can perform in a single time step.

The memory available is also an important constraint. A large amount of memory is often required to build up approximations of value functions, policies, and models. In the case of large state sets, functions must be approximated using some sort of more compact parameterized function representation.

This presents us with unique oppurtunities for achieving useful approximations. For example, in approximating optimal behavior, there may be many states that the agent faces with such a low probability that selecting suboptimal actions for them has little impact on the amount of reward the agent receives.

The online nature of reinforcement learning which makes it possible to approximate optimal policies in ways that put more effort into learning to make good decisions for frequently encountered states at the expense of infrequent ones is the key property that distinguishes reinforcement learning from other approaches to approximately solve MDPs.

### Summary

Let us summarize the elements of the reinforcement learning problem.

Reinforcement learning is about learning from interaction how to behave in order to achieve a goal. The reinforcement learning *agent* and its *environment* interact over a sequence of discrete time steps.

The *actions* are the choices made by the agent; the states are the basis for making the choice; and the *rewards* are the basis for evaluating the choices.

Everything inside the agent is completely known and controllable by the agent; everything outside is incompletely controllable but may or may not be completely known.

A *policy* is a stochastic rule by which the agent selects actions as a function of states.

When the reinforcement learning setup described above is formulated with well defined transition probabilities it constitutes a Markov Decision Process (MDP)

The *return* is the function of future rewards that the agent seeks to maximize. It has several different definitions depending on the nature of the task and whether one wishes to *discount* delayed reward. 

- The un-discounted formulation is appropriate for *episodic tasks*, in which the agent-environment interaction breaks naturally into *episodes*
- The discounted formulation is appropriate for *continuing tasks* in which the interaction does not naturally break into episodes but continue without limit

A policy's *value functions* assign to each state, or state-action pair, the expected return from that state, or state-action pair, given that the agent uses the policy. The *optimal value functions* assign to each state, or state-action pair, the largest expected return achievable by any policy. A policy whose value unctions are optimal is an *optimal policy*.

Even if the agent has a complete and accurate environment model, the agent is typically unable to perform enough computation per time step to fully use it. The memory available is also an important constraint. Memory may be required to build up accurate approximations of value functions, policies, and models. In most cases of practical interest there are far more states that could possibly be entries in a table, and approximations must be made.




