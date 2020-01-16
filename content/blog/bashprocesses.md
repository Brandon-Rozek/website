---
title: "Handling Background Processes in Bash"
date: 2019-06-17T19:50:30-04:00
draft: false
---

For multi-process applications, I want to be able to start it up using the `bash` command processor and be able to stop all the processes just by hitting `CTRL-C`.

As a quick reminder, to have a task run in the background you need to add a `&` at the end of the line.

```bash
execute_app &
```

Previously, I was grabbing the PID of this background process, trapping the interrupt signal and taking the time to send the interrupt signal to all of the background processes.

You can get the child pid by referencing the variable `$!` after sending a process to the background.

Now I just use `setsid` to set the process group of the background processes to be the same as the bash process itself.  The following demo script here will show the capability.

```bash
#!/bin/bash
setsid sleep 5 &
setsid sleep 10 &
wait
```

This script will send two processes to the background and will wait until all the processes are finished. Hitting `CTRL-C` during execution will send the interrupt signal to all of the processes achieving my goal.
