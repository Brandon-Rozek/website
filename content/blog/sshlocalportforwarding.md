---
title: "SSH Local Port Forwarding"
date: 2019-08-06T16:50:00-04:00
draft: false
tags: [ "SSH" ]
---

There are some services that I don't want to run all the time which makes me not want to open a port for it. One good example of this is [Jupyter Notebooks](https://jupyter.org/). Therefore, what I sometimes do is run it locally and forward the port so that another machine can access it.

Example command:

```bash
ssh -L 8888:localhost:8888 -N 192.168.0.2
```

The `-L` flag allows you to specify the `localsocket:host:remotesocket`. 

`-N` makes it so that it doesn't execute any additional commands

Then finally you put the address of the machine you wish to connect to.
