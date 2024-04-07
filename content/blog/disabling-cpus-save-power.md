---
title: "Disabling CPUs to Save Power"
date: 2024-04-06T20:48:52-04:00
draft: false
tags: []
math: false
medium_enabled: false
---

Looking for ways to reduce the power usage of my home server? This post shows a not-so-scientific look at how disabling CPUs can help save some power.

I run a Dell PowerEdge R430 with an Intel Xeon E5-2643 v3 CPU. This gives me 12 physical cores, and with hyperthreading this presents itself as 24 logical cores.

Given that I mostly use my server as media storage, most of those CPUs sit idle most of the time. My thought is, how much power can I save if I disable some of these unused cores?

For idle workloads disabling the CPU does not result in any noticeable power savings. The power savings is significant, however, if you analyze the system under load.

To conduct this experiment, I used a [Kill a Watt](https://en.wikipedia.org/wiki/Kill_A_Watt) measuring device which monitors the power usage of whatever is plugged into it.

To disable a CPU in Linux, use the following command:

```bash
# Disable CPU 23
echo 0 | sudo tee /sys/devices/system/cpu/cpu23/online > /dev/null
```

Repeat for any CPUs you want to disable. You can see which CPUs are available using `ls /sys/devices/system/cpu`. The `htop` tool will display in addition to the CPU utilization, which CPUs are offline.

To get the system under load, I used the `stress` tool.

```bash
# Spin off 24 dummy tasks that max out each CPU
stress -c 24
```

I ran the stress tool with the corresponding number of logical CPUs I had online to come up with the following table:

| # Online Logical CPU | Power (Watts) |
| -------------------- | ------------- |
| 24                   | 360           |
| 12                   | 295           |
| 6                    | 194           |
| 4                    | 173           |

Cutting down to 4 logical CPUs can cut the power usage under load in half! Do note though, that this exchanges performance for power savings. If you are running a low amount of services on your home server or can wait a bit of extra time for a computation to finish, consider disabling some of your CPUs.
