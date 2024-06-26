---
date: 2021-07-25 14:38:43
draft: false
math: false
medium_enabled: true
medium_post_id: 610d337c8783
tags: []
title: Parallel SCP with LFTP
---

Segmented file transfer allows you to split up a file into multiple chunks and download them in parallel. There is a program written for Linux called LFTP which can accomplish this task and supports FTP, HTTP, SFTP, BitTorrent, among others. The syntax is a little funky, so I wrote a wrapper I call `pget` which allows for segmented file transfers using SCP.

Usage:
```bash
pget [user@host] [file] [segments?]
```
where `segments?` is optional.

Example:
```bash
pget user@127.0.0.1 Documents/todo.txt 3
```


The full script:
```bash
#!/bin/sh
# set -xv

show_usage() {
    echo "Usage: pget [user@host] [file] [segments?]"
    echo "Example: pget user@127.0.0.1 Documents/todo.txt 3"
    echo "Currently only supports sftp. Segments value are optional."
    exit 1
}

contains_help_flag() {
    if [ "$1" = "-h" ] || [ "$1" = "--help" ]; then
        return 0
    fi
    return 1
}

if [ "$#" -lt 2 ] ||
   [ "$#" -gt 3 ] ||
   contains_help_flag "$1" ||
   contains_help_flag "$2" ||
   contains_help_flag "$3" ; then
    show_usage
fi

REMOTE_HOST="$1"
FILE_LOCATION="$2"

if [ "$#" -eq 3 ]; then
    NUM_SEGMENTS="$3"
else
    NUM_SEGMENTS="1"
fi

LFTP_COMMAND="pget -n $NUM_SEGMENTS $FILE_LOCATION;bye"
lftp -e "$LFTP_COMMAND" sftp://"$REMOTE_HOST"
```