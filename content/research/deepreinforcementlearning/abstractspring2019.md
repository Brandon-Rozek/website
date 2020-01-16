---
showthedate: false
---

**Name:** Brandon Rozek

Department of Computer Science

**Mentor:** Dr. Ron Zacharski

QEP: The Q-Value Policy Evaluation Algorithm



*Abstract.* In Reinforcement Learning, sample complexity is often one of many concerns when designing algorithms. This concern outlines the number of interactions with a given environment that an agent needs in order to effectively learn a task. The Reinforcement Learning framework consists of finding a function (the policy) that maps states/scenarios to actions while maximizing the amount of reward from the environment. For example in video games, the reward is often characterized by some score. In recent years a variety of algorithms came out falling under the categories of Value-based methods and Policy-based methods. Value-based methods create a policy by approximating how much reward an agent is expected to receive if it performs the best actions from a given state. It is then common to choose the actions that maximizes such values. Meanwhile, in Policy-based methods, the policy function produces probabilities that an agent performs each action given a state and this is then optimized for the maximum reward. As such, Value-based methods produce deterministic policies while policy-based methods produce stochastic/probabilistic policies. Empirically, Value-based methods have lower sample complexity than Policy-based methods. However, in decision making not every situation has a best action associated with it. This is mainly due to the fact that real world environments are dynamic in nature and have confounding variables affecting the result. The QEP Algorithm combines both the Policy-based methods and Value-based methods by changing the policy's optimization scheme to involve approximate value functions. We have shown that this combines the benefits of both methods so that the sample complexity is kept low while maintaining a stochastic policy.