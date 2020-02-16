---
title: "Nested X Sessions with Xephyr"
date: 2019-12-25T00:52:02-05:00
draft: false
tags: [ "linux" ]
---

The X Window System was designed at a time when applications that ran on your computer were assumed to be trusted. Therefore there are minimal restrictions in place to prevent applications from grabbing images of whats on another applications screens. This feature as you might imagine is quite useful for screen clipper applications.

Now I know that we're slowly moving towards Wayland on the Linux desktop, but X11 is still a reality even in my KDE Neon version that's based on Ubuntu 18.04.

So in the meantime, we can put our untrusted applications into a nested X server using `Xephyr`.

First, we need to find an empty display variable. Chances are this would be `:1` for you. Though if you have multiple of these nested X-sessions running, then this script will be handy.

```bash
for ((DNum=1 ; DNum <= 100 ; DNum++)) ; do
  [ -e /tmp/.X11-unix/X$DNum ] || break
done
```

At the end, `DNum` will be set to an empty display variable.

Then to start your nested X session,

```bash
Xephyr :$DNum \
        -extension MIT-SHM \
        -extension XTEST \
        -nolisten tcp \
        -screen 1920x1080 \
        -resizeable &
```

If we're going to be using this nested X server for one application, then I recommend using the `ratpoison` window manager as it will make the application full screen and supports the reizability of the Xephyr window.

```bash
ratpoison -d :$DNum &
```

Finally, you should set your display variable so that any future GUI applications you execute from the terminal will show up in your new Xephyr window.

```bash
DISPLAY=:$DNum
```

Now if you want to run multiple applications, you're likely better off using your native window manager. 

```bash
# Set the display before starting the window manager
DISPLAY=:$DNum
x-window-manager &
```

Of course you can replace ratpoison and your native x-window manager with any other window manager of your choice. It actually makes it a great way to test different environments.
