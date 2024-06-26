---
title: "Zsh and Snaps"
date: 2020-01-25T09:46:23-05:00
draft: false
tags: [ "Linux" ]
medium_enabled: true
---

In case I forget again, by default when snaps are installed it doesn't populate in the `zsh` shell. To enable this add the following to `/etc/zsh/zprofile`

```bash
emulate sh -c 'source /etc/profile.d/apps-bin-path.sh'
```

In case you don't have `apps-bin-path.sh` in `/etc/profile.d/`, then here's the file as of this date:

```bash
# shellcheck shell=sh

# Expand $PATH to include the directory where snappy applications go.
snap_bin_path="/snap/bin"
if [ -n "${PATH##*${snap_bin_path}}" -a -n "${PATH##*${snap_bin_path}:*}" ]; then
    export PATH=$PATH:${snap_bin_path}
fi

# Ensure base distro defaults xdg path are set if nothing filed up some
# defaults yet.
if [ -z "$XDG_DATA_DIRS" ]; then
    export XDG_DATA_DIRS="/usr/local/share:/usr/share"
fi

# Desktop files (used by desktop environments within both X11 and Wayland) are
# looked for in XDG_DATA_DIRS; make sure it includes the relevant directory for
# snappy applications' desktop files.
snap_xdg_path="/var/lib/snapd/desktop"
if [ -n "${XDG_DATA_DIRS##*${snap_xdg_path}}" -a -n "${XDG_DATA_DIRS##*${snap_xdg_path}:*}" ]; then
    export XDG_DATA_DIRS="${XDG_DATA_DIRS}:${snap_xdg_path}"
fi
```

Source: [hackel](https://askubuntu.com/users/263969/hackel) on [Ask Ubuntu](https://askubuntu.com/questions/910821/programs-installed-via-snap-not-showing-up-in-launcher).

