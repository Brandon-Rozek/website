---
Title: Deep Reinforcement Learning 
Description: Combining Reinforcement Learning with Deep Learning
---

I am interested in sample-efficient reinforcement learning.
That is, decreases the number of interactions an agent needs
with an environment to achieve some goal. In the Fall of 2019,
I approached this by integrating interactive demonstration
data into the optimized Deep Q-Networks algorithm. 

The results are positive and are heavily documented through the following:

[Undergraduate Honors Thesis](/files/research/honorsthesis.pdf)

[Undergraduate Honors Defense](/files/research/ExpeditedLearningInteractiveDemo.pptx)

Thanks to my advisor Dr. Ron Zacharksi and my committee members for all their feedback on my work!

The semester prior, I built a [reinforcement learning library](https://github.com/brandon-rozek/rltorch) with implementations of several popular papers. ([Semi-Weekly Progress](weeklyprogress)).

I also presented at my school's research symposium. ([Slides](/files/research/QEP.pptx)) ([Abstract](abstractspring2019))

In the summer of 2019, I became interested in having the interactions with the environment be in a separate process. This inspired two different implementations, [ZeroMQ](https://github.com/brandon-rozek/zerogym) and [HTTP](https://github.com/brandon-rozek/gymhttp). Given the option, you should use the ZeroMQ implementation since it contains less communication overhead.
