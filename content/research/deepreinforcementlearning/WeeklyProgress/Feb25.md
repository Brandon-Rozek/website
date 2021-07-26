---
title: Weekly Progress for February 25th
showthedate: false
math: true
---

## Evolutionary Algorithms

### Genetic Algorithm

I worked towards implementing the Genetic Algorithm into PyTorch. I got a working implementation which operates like the following:

Generate $n$ perturbations of the model by taking the tensors in the model dictionary and add some random noise to them.

- Calculate the fitness of each model
- Keep the $k$ best survivors
- Sample (with replacement) $2(n - k)$ parents based on their fitness. (Higher fitness -> More likely to be sampled)

  - Easy way to do this is: $prob = fitness / sum(fitness)$ 
- Split the parents in half to $parent1$ and $parent2$
- Perform crossover in order to make children

  - For every tensor in the model dictionary

    - Find a point in where you want the split to happen
    - Create a new tensor: the left part of the split comes from $parent1$, the other side from $parent2$
    - Mutate the child with $\epsilon$ probability
      - Add random noise to the tensor

Normally if you perform this algorithm with many iterations, your results start to converge towards a particular solution.

The main issue with this algorithm is that you need to carry with you $n$ models of the environment throughout the entire training process. You also need to have a somewhat good definition of the bounds of which your weights and biases can be otherwise the algorithm might not converge to the true value.

Due to these reasons, I didn't end up adding this functionality to RLTorch.

### Evolutionary Strategies

To combat these issues, I knocked into a paper by OpenAI Called "Evolutionary Strategies"

Tim Salimans, Jonathan Ho, Xi Chen, Szymon Sidor, Ilya Sutskever. **Evolution Strategies as a Scalable Alternative to Reinforcement Learning**

https://arxiv.org/abs/1703.03864

*This paper mostly describes the efforts made to make a certain evolutionary strategy scalable to many nodes.  I ended up using only the algorithm from the paper and I didn't implement any of the scalable considerations.*

The following code below explains the process for maximizing a simple function

```python
white_noise = np.random.randn(population_size, *current_solution.shape)
noise = sigma * white_noise
candidate_solutions = current_solution + noise

# Calculate fitness, mean shift, and scale
fitness_values = calculate_fitness(candidate_solutions)
fitness_values = (fitness_values - np.mean(fitness_values)) / (np.std(fitness_values) + np.finfo('float').eps)

new_solution = current_solution + learning_rate * np.mean(white_noise.T * fitness_values, axis = 1) / sigma
```

To explain further, suppose you have a guess as to what the solution is. To generate new guesses, let us add random noise around our guess like the image below.

![1551158699648](/home/rozek/Documents/Research/Deep RL/WeeklyProgress/1551158699648.png)

Now calculate the fitness of all the points, let us represent that by the intensity of blue in the background,

![1551158802225](/home/rozek/Documents/Research/Deep RL/WeeklyProgress/1551158802225.png)

What ends up happening is that your new solution, the black square, will move towards the areas with higher reward.

## Q-Evolutionary Policies

**Motivation**

So this brings up the point, why did I bother studying these algorithms? I ran into a problem when I was looking to implement the DDPG algorithm. Primarily that it required your action space to be continuous, which is not something I'm currently on.

Then I thought, why can I not make it work with discrete actions? First let us recall the loss of a policy function under DDPG:
$$
loss_\pi = -Q(s, \pi(s))
$$
For the discrete case, your Q-function is going to be a function of the state and output the values of each action taken under that state. In mathematical terms,
$$
loss_\pi = -Q(s)[\pi(s)]
$$
Indexing into another array, however, is not a differentiable function. Meaning I cannot then calculate $loss_\pi$ with respect to $\pi$.

Evolutionary Strategies are non-gradient based methods. Meaning that I can bypass this restriction with the traditional methods.

**How it works**

Train your Value function with the typical DQN loss. 

Every 10 Value function updates, update the policy. This gives time for the Value function to stabilize so that the policy is not chasing suboptimal value functions. Update the policy according to the $loss_\pi$ written above.

**Results**

![1551160033552](/home/rozek/Documents/Research/Deep RL/WeeklyProgress//1551160033552.png)

The orange line is the QEP performance

Blue is DQN

## Future Direction

I would like to look back towards demonstration data and figure out a way to pretrain a QEP model.

It's somewhat easy to think of a way to train the policy. Make it a cross-entropy loss with respect to the actions the demonstrator took.
$$
loss_\pi = -\sum_{c=1}^M{y_{o,c}\ln{(p_{o,c})}}
$$
Where $M$ is the number of classes, $y$ is the binary indicator for whether the correction classification was observed, and $p$ is the predicted probability observation for class c.

It's harder to think about how I would do it for a Value function. There was the approach we saw before where the loss function was like so,
$$
loss_Q = max(Q(s, a) + l(s,a)) - Q(s, a_E)
$$
Where $l(s, a)$ is a vector that is positive for all values except for what the demonstrator took which is action $a_E$.

The main issue with this loss function for the Value is that it does not capture the actual output values of the functions, just how they are relative to each other. Perhaps adding another layer can help transform it to the values it needs to be. This will take some more thought.



