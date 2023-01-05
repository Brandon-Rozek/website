---
title: "Videos and GIFs"
date: 2019-12-04T10:13:35-05:00
draft: false
tags: ["Audio-Video"]
medium_enabled: true
---

I like using GIFs in Google Slides because it doesn't require any interaction to start playing right away. Therefore, I looked at a couple resources to add a GIF from a video into my presentation. Of course this is all using one of my favorite terminal tools `ffmpeg`.

First of all, I wanted to include a video of a bot playing Pong. The video was a little long, so I decided speed it up for a more time-lapse type feel.

[From the FFMPEG website](https://trac.ffmpeg.org/wiki/How%20to%20speed%20up%20/%20slow%20down%20a%20video): To 10x the speed `ffmpeg -i input.mkv -filter:v "setpts=0.1*PTS" output.mkv` 

You just need to replace the `0.1` with the appropriate decimal number to change the speed.

Giphy has a great [writeup](https://engineering.giphy.com/how-to-make-gifs-with-ffmpeg/) describing the commands to use in order to make your GIF look nice.

```bash
ffmpeg -i inputvideo.mp4 -filter_complex "[0:v] palettegen" palette.png
ffmpeg -i inputvideo.mp4 -i palette.png -filter_complex "[0:v][1:v] paletteuse" output.gif
```

