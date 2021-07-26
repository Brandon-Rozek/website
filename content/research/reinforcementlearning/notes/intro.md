---
title: Introduction to Reinforcement Learning Day 1
showthedate: false
---

Recall that this course is based on the book -- 

Reinforcement Learning: An Introduction by Richard S. Sutton and Andrew G. Barto



These notes really serve as talking points for the overall concepts described in the chapter and are not meant to stand for themselves. Check out the book for more complete thoughts :)



**Reinforcement Learning** is learning what to do -- how to map situations to actions -- so as to maximize a numerical reward signal. There are two characteristics, trial-and-error search and delayed reward, that are the two most important distinguishing features of reinforcement learning.



Markov decision processes are intended to include just these three aspects: sensation, action, and goal(s).



Reinforcement learning is **different** than the following categories

- Supervised learning: This is learning from a training set of labeled examples provided by a knowledgeable external supervisor. In interactive problems it is often impractical to obtain examples of desired behavior that are both correct and representative of all situations in which the agent has to act.
- Unsupervised learning: Reinforcement learning is trying to maximize a reward signal as opposed to finding some sort of hidden structure within the data.



One of the challenges that arise in reinforcement learning is the **trade-off** between exploration and exploitation. The dilemma is that neither exploration nor exploitation can be pursued exclusively without failing at the task.



Another key feature of reinforcement learning is that it explicitly considers the whole problem of a goal-directed agent interacting with an uncertain environment. This is different than supervised learning since they're concerned with finding the best classifier/regression without explicitly specifying how such an ability would finally be useful.



A complete, interactive, goal-seeking agent can also be a component of a larger behaving system. A simple example is an agent that monitors the charge level of a robot's battery and sends commands to the robot's control architecture. This agent's environment is the rest of the robot together with the robot's environment.



## Definitions

A policy defines the learning agent's way of behaving at a given time



A reward signal defines the goal in a reinforcement learning problem. The agent's sole objective is to maximize the total reward it receives over the long run



A value function specifies what is good in the long run. Roughly speaking, the value of a state is the total amount of reward an agent can expect to accumulate over the future, starting from that state. Without rewards there could be no value,s and the only purpose of estimating values is to achieve more reward. We seek actions that bring about states of highest value. 



Unfortunately, it is much harder to determine values than it is to determine rewards. The most important component of almost all reinforcement learning algorithms we consider is a method for efficiently estimating values.



**Look at Tic-Tac-Toe example**



Most of the time in a reinforcement learning algorithm, we move greedily, selecting the move that leads to the state with greatest value. Occasionally, however, we select randomly from amoung the other moves instead. These are called exploratory moves because they cause us to experience states that we might otherwise never see.



Summary: Reinforcement learning is learning by an agent from direct interaction wit its environment, without relying on exemplary supervision or complete models of the environment.
