---
title: "Debugging and Performance"
date: 2019-06-15T10:59:30-04:00
draft: false 
---

I've come to like the GNU Debugger (GDB) and the `perf` tool recently. This post will be a short summary of the various interesting commands you can use.

## GNU Debugger

To attach gbd to an existing process do the following

```bash
gdb -p pid_of_process
```

Otherwise you can start a new application

```bash
gdb name_of_executable
```

Once it loads it will bring you into it's own `REPL` environment. Usually once this comes up I find it useful to add breakpoints to the program. You can either do it by function name or by line number.

```bash
(gdb) break FunctionName
```

```bash
(gdb) break code.cpp:81
```

If you just started a new application you can begin running the program with whatever arguments you wish

```bash
(gdb) run -arg1 -arg2
```

If you have attached to a process then you can continue its execution.

```bash
(gdb) continue
```

### Breakpoints

If you have set a breakpoint, it will stop the processes' execution when it lands on the breakpoint. From here, we can take a look at what's on the stack, print variables, and do whatever other debugging we wish.

**Print variables on stack:**

```bash
(gdb) info locals
```

**Print a specific variable:**

```bash
(gdb) print variable_name
```

**Show backtrace:**

```bash
(gdb) bt
```

**Continue on with program execution:**

```bash
(gdb) continue
```

## Perf

I haven't played with `perf` as much but one thing I found that was cool was the `perf top` command. This command gives you samples of which function calls keeps the program the most busy.

To attach to a process and show samples:

```bash
perf top -p pid -K
```





