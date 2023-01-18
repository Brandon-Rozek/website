---
title: "Parsing CLI Flags in Bash"
date: 2019-08-06T16:55:47-04:00
draft: false
tags: [ "Bash" ]
medium_enabled: true
---

I was creating a bash script and was looking around for a solution for parsing command line arguments. [This StackOverflow post](https://stackoverflow.com/questions/192249/how-do-i-parse-command-line-arguments-in-bash) has a variety of different solutions available. I want to describe my favorite of these posts.

[Inanc Gumus](https://stackoverflow.com/users/115363/inanc-gumus) proposed the following:

```bash
#!/bin/bash

while [[ "$#" -gt 0 ]]; do case $1 in
  -d|--deploy) deploy="$2"; shift;;
  -u|--uglify) uglify=1;;
  *) echo "Unknown parameter passed: $1"; exit 1;;
esac; shift; done

echo "Should deploy? $deploy"
echo "Should uglify? $uglify"
```

Let me quickly describe what it does. While the number of arguments left to process is greater than zero....

- Check to see if the argument matches any of the flags
  - If it does...
    - If the flag requires an additional argument grab it. Then discard an argument.
  - If it doesn't. Error out.
  - Then get rid of an argument.

At the end of the while loop, you would've evaluated all the arguments!
