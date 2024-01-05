---
title: "Run a command when a file in a directory changes"
date: 2024-01-05T16:00:53-05:00
draft: false
tags: []
math: false
medium_enabled: false
---

When editing code or adding content to a HTML file for a website, it can be very useful to see the changes right away after you save the file. We'll show a lightweight way of accomplishing this task with `entr` and a bit of bash scripting.

First if you don't already have it, install `entr`.

```bash
sudo dnf install entr
```

This terminal application works by monitoring files passed within standard in. Therefore, to run a `$command`  if any file under some `$directory` changes run the following:

```bash
find $directory -type f | entr $command
```

An example can be running a build script if anything under the source folder changes:

```bash
find src -type f | entr ./build.sh
```

Now this doesn't capture files that get added to the directory. To do this, we need to get `entr` to monitor the parent folder for any changes. We can do this with the `-d` flag.

From the man page:

> **-d**    Track the directories of regular files provided as input and exit if 
>        a new file is added. 

Since `entr` exits when a file gets added with this flag, the [common solution](https://superuser.com/a/665208) on the internet is to wrap it in a `while` loop.

```bash
$ while sleep 0.1 ; do find $directory -type f | entr -d $command ; done
```

This solution works great as a one-liner, but it doesn't let me CTRL-C out when I'm finished. Therefore, I wrote a shell script that incorporates this solution while also adding a `trap`.

```bash
#!/bin/bash

set -o nounset
set -o pipefail

show_usage() {
    echo "Usage: entr-dir [dir] [command]"
    exit 1
}

# Check argument count
if [ "$#" -lt 2 ]; then
    show_usage
fi

# Make sure that the command entr exists
if ! command -v entr > /dev/null ; then
    echo "entr not found. Exiting..."
    exit 1
fi

DIR="$1"; shift

if [[ ! -d "$DIR" ]]; then
    echo "First argument must be a directory. Exiting..."
    exit 1
fi

# Allow for CTRL-C to exit script
trap "exit 0;" SIGINT

while sleep 0.1; do
    find "$DIR" -type f | entr -d "$@"
done
```

I plopped this in `~/.local/bin/entr-dir`, gave it the `+x` permission, and now I can easily monitor and build projects when files get changed/added/deleted.

```bash
entr-dir src ./build.sh
```

