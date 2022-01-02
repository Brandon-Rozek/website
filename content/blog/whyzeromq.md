---
title: "Why ZeroMQ"
date: 2019-06-16T19:26:50-04:00
draft: false
tags: [ "Networking" ]
---

I've been playing around with ZeroMQ recently and it's been really exciting. This blog post is going to outline why I think you should be using ZeroMQ today.

First of all, before you compare this to other products like RabbitMQ, DDS, etc. Realize that this is a static library that you link to in your application as opposed to a broker you run. This means that you can get the benefits with this library for very little overhead.

## Easier Sockets

Instead of talking about how easy ZeroMQ is to use, I'm going to just show you the code to implement a server-client relationship in Python.

**Server.py**

```python
import zmq
import time

port = "5556"
context = zmq.Context()
socket = context.socket(zmq.REP)
socket.bind("tcp://*:%s" % port)

while True:
    msg = socket.recv()
    print(msg)
    time.sleep(1)
    socket.send_string("Server Message To Client")
```

**Client.py**

```python
import zmq
import time

port = "5556"
context = zmq.Context()
socket = context.socket(zmq.REQ)
socket.connect("tcp://localhost:%s" % port)

while True:
    socket.send_string("client message to server")
    time.sleep(1)
    msg = socket.recv()
    print(msg)

```

And just like that we have a way to transport messages back and forth. No need to make a special header before each message to know the appropriate size of the packets. ZeroMQ abstracts those details from you.

## Different Transports Available

You're not limited to only `TCP`. You can use `inproc` for thread-to-thread messaging, `ipc` for inter-process communication, and `epgm` or `pgm` for multicast messaging. Most of the time, just changing the connection string in `socket.connect` just works!

## Common Networking Patterns Built In

Sometimes we just want a dumb pipe between two ends (`pipe`) but most of the times we're writing applications that follow the `server-client` or `publisher-subscriber` architecture. That gets defined in `context.socket`.

Ex: `context.socket(zmq.PAIR)`