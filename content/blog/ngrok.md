---
title: "Ngrok"
date: 2019-11-20T20:56:19-05:00
draft: false
---

Let's say you want to spin up a quick demo for a client and you don't want to use a VPS, and they can't access your laptop through the network. 

The easiest way I've known for the past few years to allow another person to access a specific port on your machine is through [ngrok](https://ngrok.com/). Ngrok is nice because not only do they offer a free plan, but they also offer paid plans. This means that you can trust that it'll at least be in business for a little while longer ;)

## The Process

You'll need to sign up for an account first. I was then going to write about some of the following steps, but `ngrok` has a really nice quad chart when you login

![steps](/files/images/0932485094325.png)

Just note that in step (3) you will actually have a random sequence of characters after `authtoken`. 

Something else you might want to know is how to enable TLS support, luckily that's a simple command line argument.

```bash
ngrok http -bind-tls=true port
```

