---
title: "Aliases for Snaps and Flatpaks"
date: 2022-02-04T20:29:04-05:00
draft: false
tags: ["Linux"]
math: false
medium_enabled: true
---

Sometimes snap packages and flatpaks come with unmemorable names to run their commands. Luckily for snap packages, you can easily alias them. For example, to rename the .NET executable to `dotnet` run.

```bash
sudo snap alias dotnet-sdk.dotnet dotnet
```

Sadly the same cannot be said for Flatpaks. There is a [Github issue](https://github.com/flatpak/flatpak/issues/1565) open at the moment. I'll update this post when they successfully close the issue. In the meantime, we can use a script made by Seth Kenlon over at [Red Hat's blog](https://www.redhat.com/sysadmin/launch-flatpaks-terminal-fuzzpak). The script is at the bottom of the post for posterity. You can save it to `~/.local/bin`, `chmod +x ~/.local/bin`, and then run `fuzzpak [appname]` where `appname` is the last part of the flatpak name. For example, the package`io.typora.Typora` can be called with `fuzzpak typora`.

```bash
# parse opts
while [ True ]; do
if [ "$1" = "--help" -o "$1" = "-h" ]; then
    echo " "
    echo "$0 [OPTIONS]"
    echo "--directory, -d   Location of flatpaks (default: $HOME/.var/app"
    echo " "
    exit
elif [ "$1" = "--directory" -o "$1" = "-d" ]; then
    DIR=$DIR
    shift 2
else
    break
fi
done

# main
launch_app "${1}"
```

