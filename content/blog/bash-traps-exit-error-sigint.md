---
title: "Bash Traps: Exit, Error, Sigint"
date: 2024-01-02T11:26:06-05:00
draft: false
tags:
  - Bash
math: false
medium_enabled: false
---

Traps in bash listen for interrupts and signals and performs a bash command in response to it. This post will go over three use cases I've encountered so far in my bash scripting journey.

## `SIGINT`

If we have a while loop within a bash script

```bash
while sleep 0.1; do
  do_something
done
```

We probably want to be able to CTRL-C to exit the whole script.

```bash
finish () {
  exit 0
}
trap finish SIGINT

while sleep 0.1; do
  do_something
done
```

## `ERR`

If we encounter an error in a bash script, one thing we might want to do is dump the environment information and other things that can be useful for debugging.

```bash
set -o errexit
set -o nounset
set -o pipefail

print_debug () {
  declare exit_code=$?
  env >&2
  other_debug_info >&2
  exit "$exit_code"
}

trap print_debug ERR

command_that_may_fail
```

## `EXIT`

Like the last one, this function will occur if the script fails. However, this also occurs if the script is successful. It's similar to the `finally` clause within a `try-catch` programming paradigm.

This is useful for cleaning up build files, de-provisioning services, etc.

```bash
cleanup () {
  rm a.tmp b.tmp
  deprovision
}

trap cleanup EXIT

long_compile_may_fail
```

## Other Resources

http://redsymbol.net/articles/bash-exit-traps/

https://jakski.github.io/pages/error-handling-in-bash.html
