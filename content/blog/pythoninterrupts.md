---
title: "Quick Python: Interrupts"
date: 2020-01-25T09:51:34-05:00
draft: false
tags: [ "Python" ]
medium_enabled: true
---

This post is part of a new series I'm starting where I quickly outline small Python snippets.

If you have an application that you want to gracefully exit when the user presses CTRL-C here's the short snippet
```python
import signal
import sys

# Function that gets called when interrupt is found
def signal_handler(sig, frame):
  print('You pressed Ctrl+C!')
  sys.exit(0)

# Attach the function to the interrupt signal
signal.signal(signal.SIGINT,signal_handler)

print('Press Ctrl+C')
```
