---
title: "Limit Bandwidth through Terminal"
date: 2020-01-15T19:51:45-05:00
draft: false
tags: [ "Linux", "Networking" ]
medium_enabled: true
---

Have you ever wondered how an application or a system would operate under low bandwidth environments? Luckily `wondershaper` is a tool to help with just that!

```bash
sudo apt install wondershaper
```

To get started, first find out the network `interface` that you want to throttle.

```bash
ip addr show
```

To show the state of the interface,

```bash
sudo wondershaper [interface]
```

To set the bandwidth,

```bash
sudo wondershaper [interface] [downlink] [uplink]
```
where downlink and uplink are defined in kilobits per second. 

To clear the rules,

```bash
sudo wondershaper clear [interface]
```
