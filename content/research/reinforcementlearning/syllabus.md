---
title: Reinfrocement Learning Syllabus
---

The goal of this independent study is to gain an introduction to the topic of Reinforcement Learning. 

As such the majority of the semester will be following the textbook to gain an introduction to the topic, and the last part applying it to some problems.


## Textbook

The majority of the content of this independent study will come from the textbook. This is meant to lessen the burden on the both us of as I already experimented with curating my own content.

The textbook also includes examples throughout the text to immediately apply what's learned.

Richard S. Sutton and Andrew G. Barto, "Reinforcement Learning: An Introduction" http://incompleteideas.net/book/bookdraft2017nov5.pdf

## Discussions and Notes

Discussions and notes will be kept track of and published on my tilda space as time and energy permits. This is for easy reference and since it's nice to write down what you learn.

## Topics to be Discussed

###The Reinforcement Learning Problem (3 Sessions)

In this section we will get ourselves familiar with the topics that are commonly discussed in Reinforcement learning problems.

In this section we will learn the different vocab terms such as:

- Evaluative Feedback 
- Non-Associative Learning
- Rewards/Returns
- Value Functions
- Optimality
- Exploration/Exploitation
- Model
- Policy
- Value Function
- Multi-armed Bandit Problem

### Markov Decision Processes (4 Sessions)

This is a type of reinforcement learning problem that is commonly studied and well documented. This helps form an environment for which the agent can operate within. Possible subtopics include:

- Finite Markov Decision Processes
- Goals and Rewards
- Returns and Episodes
- Optimality and Approximation

### Dynamic Programming (3 Sessions)

Dynamic Programming refers to a collection of algorithms that can be used to compute optimal policies given an environment. Subtopics that we are going over is:

- Policy Evaluation
- Policy Improvement
- Policy Iteration
- Value Iteration
- Asynchronous DP
- Generalized policy Iteration 
- Bellman Expectation Equations

### Monte Carlo Methods (3 Sessions)

Now we move onto not having complete knowledge of the environment. This will go into estimating value functions and discovering optimal policies. Possible subtopics include:

- Monte Carlo Prediction
- Monte Carlo Control
- Importance Sampling
- Incremental Implementation
- Off-Policy Monte Carlo Control

### Temporal-Difference Learning (4-5 Sessions)

Temporal-Difference learning is a combination of Monte Carlo ideas and Dynamic Programming. This can lead to methods learning directly from raw experience without knowledge of an environment. Subtopics will include:

- TD Prediction
- Sarsa: On-Policy TD Control
- Q-Learning: Off-Policy TD Control
- Function Approximation
- Eligibility Traces
