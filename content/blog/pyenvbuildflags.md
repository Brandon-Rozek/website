---
title: "Pyenv Build Flags"
date: 2020-03-24T16:58:42-04:00
draft: false
tags: []
---

I ran into an issue with PyMC3 where it was expecting a certain symbol that Python wasn't compiled with.

```
Exception: Compilation failed (return status=1): /usr/bin/ld: /home/rozek/.pyenv/versions/3.8.2/lib/libpython3.8.a(floatobject.o): relocation R_X86_64_PC32 against symbol `PyFloat_Type' can not be used when making a shared object; recompile with -fPIC. /usr/bin/ld: final link failed: bad value. collect2: error: ld returned 1 exit status. 
```

Since I use [`pyenv`](https://brandonrozek.com/blog/pyenv/) for Python version management, it turned out that I only needed to modify the `CFLAGS` variable to get this working

```bash
CFLAGS="-fPIC" pyenv install 3.8.2
```

Turns out you can configure other flags during Python installation as well such as `CPPFLAGS` and `LDFLAGS`.