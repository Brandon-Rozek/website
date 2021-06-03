---
title: "Print Statements with Frame Information"
date: 2021-06-03T13:54:39-04:00
draft: false
tags: []
---

I find it extremely useful to include frame information such as filename, line number, and current function in my print statements. Here's a couple ways that I've done that in the past.

In C:

```c
#include <stdio.h>

#define DEBUGLOG(msg) (printf("[%s:%d %s] %s\n", __FILE__, __LINE__, __PRETTY_FUNCTION__, msg))

int main() {
    DEBUGLOG("Hello World");
}
```



In Python:

```python
from inspect import currentframe, getframeinfo

def debuglog(m):
    frame = currentframe()
    frame_info = getframeinfo(frame)
    last_frame = frame.f_back
    last_frame_info = getframeinfo(last_frame)
    filename = last_frame_info.filename if last_frame_info is not None else "<stdin>"
    lineno = last_frame_info.lineno if last_frame_info is not None else 1
    function_name = last_frame_info.function if last_frame_info is not None else "<module>"
    print(f"[{filename}:{lineno} {function_name}] {m}")
```

