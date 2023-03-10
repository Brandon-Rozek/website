---
date: 2020-12-15 14:25:11
draft: false
medium_enabled: true
medium_post_id: ac38c9d9d896
tags:
- Bash
title: 'Quick Bash: Check Argument Count'
---

I've been writing more bash scripts recently and I noticed that I often check for the number of arguments before validating them in my scripts. I'll share that small snippet here for my future self.

```bash
#!/bin/sh

set -o errexit
set -o nounset
set -o pipefail

show_usage() {
    echo "Usage: script [arg1]"
    exit 1
}

# Check argument count
if [ "$#" -ne 1 ]; then
    show_usage
fi

```