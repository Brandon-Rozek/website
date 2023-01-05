---
title: "Extract All the Things"
date: 2020-06-14T22:23:37-04:00
draft: false
tags: ["Linux"]
medium_enabled: true
---

[Sandra Henry-Stocker](https://www.networkworld.com/author/Sandra-Henry_Stocker/) from Network World wrote a [great post](https://www.networkworld.com/article/3244007/extracting-from-compressed-files-on-linux.html) on how to standardize extracting files on Linux. It's a shell script that works so well, that I placed it in my [`~/.local/bin` directory](https://brandonrozek.com/blog/customexec/) in order to call upon it at any time. Here's part of it, check out the post for more.

```bash
#!/bin/bash
if [ -f $1 ] ; then
  case $1 in
    *.tar.bz2)  tar xjf $1   ;;
    *.tar.gz)   tar xzf $1   ;;
    *.tar.xz)   tar zxvf $1  ;;
    *.bz2)      bunzip2 $1   ;;
    *.rar)      rar x $1     ;;
    *.gz)       gunzip $1    ;;
    *.tar)      tar xf $1    ;;
    *.tbz2)     tar xjf $1   ;;
    *.tgz)      tar xzf $1   ;;
    *.xz)       xz -d $1     ;;
    *.zip)      unzip $1     ;;
    *.Z)        uncompress $1;;
    *)          echo "contents of '$1' cannot be extracted" ;;
  esac
else
  echo "'$1' is not recognized as a compressed file"
fi
```

