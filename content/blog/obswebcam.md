---
title: "OBS Webcam"
date: 2020-05-25T23:53:56-04:00
draft: false
tags: ["Audio-Video"]
---

[Open Broadcaster Software](https://obsproject.com/) is a great piece of software for recording and live streaming different video content. It would be nice to use the same level of professional software in video calling software as well.

Now there already exists a [OBS plugin](https://github.com/CatxFish/obs-v4l2sink) for this purpose, but it does require recompiling OBS with this plugin. This post will outline a possible technique to get around this, at a cost of performance.

To see discussion around this topic, check out this [Github thread](https://github.com/CatxFish/obs-virtual-cam/issues/17).

OBS has two different options, streaming and recording. Since I want the ability to record a high fidelity version of my feed, we will use streaming to push video to a local RTMP server. This local RTMP server will then re-encode the video to a [v4l2 video device](https://brandonrozek.com/blog/fakewebcam/).

We will use `ffmpeg` as our RTMP server

```bash
ffmpeg -hwaccel vdpau \
       -fflags nobuffer \
       -listen 1 \
       -i rtmp://localhost:12345/live/app/ \
       -f v4l2 /dev/video20
```

| Flag               | Description                                                  |
| ------------------ | ------------------------------------------------------------ |
| `-hwaccel vdpau`   | (Optional) Allows `ffmpeg` to use GPU for acceleration       |
| `-fflags nobuffer` | Tells `ffmpeg` to not bother buffering the video and work with the latest frame possible. |
| `-listen 1`        | Starts a server to listen for video.                         |

Then from OBS you will want to use the Auto-Configuration wizard to have it figure out the right set of parameters to use for the lowest latency. Once that is set you can hit the stream button and you are all set to use the fake video device for your calls! Depending on your hardware, you might notice a few seconds of latency.

To quickly verify that you can see your OBS video from the video device.

```bash
ffplay -fflags nobuffer /dev/video20
```

