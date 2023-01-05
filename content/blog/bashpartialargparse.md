---
title: "Partial Argument Parse and Passing in Bash"
date: 2020-09-07T21:33:26-04:00
draft: false
tags: ["Bash"]
medium_enabled: true
---

Let's say we want to augment an existing terminal command (like for example `wget`). We then want to be able to add or edit command line options. The rest of this post provides an example that hopefully you can use in your bash script.

```bash
#!/bin/bash

# Custom help function
show_help() {
  echo "Usage: custom_command [arguments]"
  echo "    --name <name>"
  echo "    --flag_example"
  echo "    <additional arguments to be passed along>"
  exit 0
}

# Defaults for our custom flags or parameters.
name=""
flag_example=0

# Loop through and take out our custom parameters
# from the parameter list.
i=0
numargs=$#
while test $i -lt "$numargs"
do
  case "$1" in
    "--help")
      show_help
      ;;
    "--name")
      shift
      name=$1
      ;;
    "--flag_example")
      flag_example=1
      ;;
    *)
      set -- "$@" "$1"
      ;;
  esac
  shift
  i=$((i+1))
done

# Do something here using our custom parameters

# Pass our non-custom parameters to the application
wget "$@"
```



