---
date: 2022-02-26 20:02:53-05:00
draft: false
math: false
medium_enabled: true
medium_post_id: 7ca070e54955
tags:
- Java
title: JUnit Script
---

Running a JUnit test on the terminal is a little annoying. Here is a quick script to make it easier, make it executable and drop it in [`~/.local/bin`](/blog/customexec/) for easy use.

```bash
#!/bin/sh

set -o errexit
set -o nounset
set -o pipefail

JUNIT_PATH="/usr/share/java/junit4.jar"

show_usage() {
    echo "Usage: junit [class file path]"
    exit 1
}

# Check argument count
if [ "$#" -ne 1 ]; then
    show_usage
fi

java -cp "$JUNIT_PATH":. org.junit.runner.JUnitCore "$1"

```

 Replacing `JUNIT_PATH` with the location of the `junit4.jar` on your system.