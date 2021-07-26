---
title: Progress Report for Week of April 2nd
showthedate: false
---

## Added Video Recording Capability to MinAtar environment

You can now use the OpenAI Monitor Wrapper to watch the actions performed by agents in the MinAtar suite. (Currently the videos are in grayscale)

Problems I had to solve:

- How to represent the channels into a grayscale value
- Getting the tensor into the right format (with shape and dtype)
- Adding additional meta information that OpenAI expected

## Progress Towards \#Exploration

After getting nowhere trying to combine the paper on Random Network Distillation and Count-based exploration and Intrinsic Motivation, I turned the paper \#Exploration: A Study of Count-Based Exploration for Deep Reinforcement Learning. 

This paper uses the idea of an autoencoder to learn a smaller latent state representation of the input. We can then use this smaller representation as a hash and count states based on these hashes. 

Playing around with the ideas of autoencoders, I wanted a way to discretized my hash more than just what floating point precision allows. Of course this turns it into a non-differential function which I then tried turning towards Evolutionary methods to solve. Sadly the rate of optimization was drastically diminished using the Evolutionary approach. Therefore, my experiments for this week failed. 

I'll probably look towards implementing what the paper did for my library and move on to a different piece.

