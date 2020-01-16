# Weekly Progress Feb 12

## Finished writing scripts for data collection

- Playing a game now records	
  - Video
  - State / Next-State as pixel values
  - Action taken
  - Reward Received
  - Whether the environment is finished every turn
- Wrote scripts to gather and preprocess the demonstration data
  - Now everything is standardized on the npy format. Hopefully that stays consistent for a while.

## Wrote code to create an actor that *imitates* the demonstrator

Tweaked the loss function to be a form of cross-entropy loss
$$
loss = max(Q(s, a) + l(s,a)) - Q(s, a_E)
$$
Where $l(s, a)$ is zero for the action the demonstrator took and positive elsewhere.

Turns out, that as with a lot of deep learning applications, you need a lot of training data. So the agent currently does poorly on mimicking the performance of the demonstrator.

### Aside : Pretraining with the Bellman Equation

Based off the paper: 

Todd Hester, Matej Vecerik, Olivier Pietquin, arc Lanctot, Tom Schaul, Bilal Piot, Andrew Sendonaris, Gabriel Dulac-Arnold, Ian OsbandI, John Agapiou, Joel Z. Leibo, Audrunas Gruslys. **Learning from Demonstrations for Real World Reinforcement Learning**



This paper had the demonstration not include include the $(state, action)$ pairs like I did, but also the $(next_state, reward, done)$ signals. This way, they can pretrain with both supervised loss and with the general Q-learning loss.

That way, they can use the result of the pretraining as a starting ground for the actual training. The way I implemented it, I would first train an imitator which would then be used as the actor during the simulations from which we would collect data and begin training another net.

## Prioritized Replay

Instead of uniform sampling of experiences, we can sample by how surprised we were about the outcome of the Q-value loss.

I had a previous implementation of this, but it was faulty, so I took the code from OpenAI baselines and integrated it with my library.

It helps with games like Pong, because there are many states where the result is not surprising and inconsequential. Like when the ball is around the center of the field.

## Schedulers

There are some people who use Linear Schedulers to change the value of various parameters throughout training.

I implemented it as an iterator in python and called *next* for each time the function uses the hyper-parameter.

The two parameters I use schedulers in normally are:

- Epsilon - Gradually decreases exploration rate
- Beta - Decreases the importance of the weights of experiences that get frequently sampled



## Layer Norm

"Reduces training by normalizes the activities of the neurons." 

Jimmy Lei Ba, Jamie Ryan Kiros, Geoffrey E. Hinton. **Layer Normalization.**

It's nicely implemented in PyTorch already so I threw that in for each layer of the network. Reduces the average loss.