---
title: Weekly Progress Jan 29
showthedate: false
math: true
---

## 1. Training From Demonstrations

Training from demonstrations is the act of using previous data to help speed up the learning process.

I read two papers on the topic:

(1) Gabriel V. de la Cruz Jr., Yunshu Du, Matthew E. Taylor. **Pre-training Neural Networks with Human Demonstrations for Deep Reinforcement Learning**.

https://arxiv.org/abs/1709.04083

The authors showed how you can speed up the training of a DQN network, especially under problems involving computer vision, if you first train the convolution layers by using a supervised loss between the actions the network would choose and the actions from the demonstration data given a state.

(2) Todd Hester, Matej Vecerik, Olivier Pietquin, Marc Lanctot, Tom Schaul, Bilal Piot, Dan Horgan, John Quan, Andrew Sendonaris, Gabriel Dulac-Arnold, Ian Osband, John Agapiou, Joel Z. Leibo, Audrunas Gruslys. **Deep Q-learning from Demonstrations.**

https://arxiv.org/abs/1704.03732

The authors showed how from "expert" demonstrations we can speed up the training of a DQN by incorporating the supervised loss into the loss function.

### Supervised Loss

What is supervised loss in the context of DQNs?
$$
Loss = max(Q(s, a)+l(s,a )) - Q(s, a_E)
$$
Where $a_E$ is the expert action, and $l(s, a)$ is a vector of positive values with an entry of zero for the expert action.

The intuition behind this is that for the loss to be zero, the network would've had to have chosen the same action as the expert. The $l(s, a)$ term exists to ensure that there are no ties.

### What I decided to do

The main environment I chose to test these algorithms is Acrobot. It is a control theory problem and it has several physics related numbers as input. (Not image based)

I noticed when implementing (1) at least for the non-convolution case, there's no point in trying to train earlier layers. Perhaps I'll try again when I move onto the atari gameplays...

I decided against following (2) exactly. It's not that I disagree with the approach, but I don't like the need for "expert" data. If you decide to proceed anyways with non-expert data, you need to remember that it is incorporated into the loss function. Which means that you fall risk into learning sub-optimal policies. 

In the end, what I decided to do was the following

1. Train a neural network that maps states->actions from demonstration data
2. Use that network to play through several simulated runs of the environment, state the (state, action, reward, next_state, done) signals and insert it into the experience replay buffer and train from those (**Pretrain step**)
3. Once the pretrain step is completed, replace the network that maps from demonstration data with the one you've been training in the pre-training step and continue with the regular algorithm



## 2. Noisy Networks

Based on this paper...

Meire Fortunato, Mohammad Gheshlaghi Azar, Bilal Piot, Jacob Menick, Ian Osband, Alex Graves, Vlad Mnih, Remi Munos, Demis Hassabis, Olivier Pietquin, Charles Blundell, Shane Legg. **Noisy Networks for Exploration.**

This paper describes adding parametric noise to the weights and biases and how it aids in exploration. The parameters of the noise are learned with gradient descent along with the other network parameters.



For the noise distribution I used the Gaussian Normal. One property that's handy to know about it is the following
$$
N(\mu, \sigma) = \mu + \sigma*N(0, 1)
$$
In our case, the $\mu$ would be the typical weights and biases, and the $\sigma$ is a new parameter representing how much variation or uncertainty needs to be added.

The concept is that as the network grows more confident about it's predictions, the variation in the weights start to decrease. This way the exploration is systematic and not something randomly injected like the epsilon-greedy strategy.

The paper describes replacing all your linear densely connected layers with this noisy linear approach.
