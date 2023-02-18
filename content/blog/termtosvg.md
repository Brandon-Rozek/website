---
date: 2022-01-17 10:14:22-05:00
draft: false
math: false
medium_enabled: true
medium_post_id: ad8c533610b5
tags: []
title: Terminal Output To SVG Animations
---

With [`termtosvg`](https://github.com/nbedos/termtosvg) made by Nicolas Bedo we can make SVG animations from terminal output in the style of  [asciinema](https://asciinema.org/). To install use [pipx](/blog/managepythonapps/).

```bash
pipx install termtosvg
```

To start recording, run the command `termtosvg`

```bash
termtosvg
```

It first outputs:

```
Recording started, enter "exit" command or Control-D to end
```

At "exit", by default it will save the animation to a random filename in the tmp folder.

```
Rendering ended, SVG animation is /tmp/termtosvg_xmadgf9y.svg
```

To control the default save location, pass in a filename after `termtosvg`

```bash
termtosvg /path/to/savefile.svg
```

To record only the execution of a particular command, use the flag `-c`

```bash
termtosvg -c neofetch
```

I recommend that you resize the terminal window so that the frames generated match the desired width and height. You can instead use the `-g` flag to pass in a geometry. ("100x30" creates a screen with 100 colums and 30 rows)

Lastly, if you don't want an animation, you can pass in `-s` and the result will be a folder of SVG files representing each frame.

```bash
termtosvg -s
```

Here is an example of an animation I made with this tool:

![](/files/images/blog/202201171031.svg)