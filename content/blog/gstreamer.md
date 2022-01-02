---
title: "GStreamer"
date: 2020-02-08T20:46:36-05:00
draft: false
tags: [ "Audio-Video" ]
---

GStreamer is a pipeline based multimedia framework that goes from capture, processing, to a sink such as a X window or UDP sink.

To install on Ubuntu run,

```bash
sudo apt install gstreamer1.0-tools
```

Pipelines are indicated via `!`.

To capture your webcam feed and display it in a X window, run the following:

```bash
gst-launch-1.0 v4l2src device=/dev/video0 ! videoconvert ! ximagesink
```

For the PiCar project I'm on, I need to send the video from the raspberry pi over the network as fast as possible. The next couple commands have options that reflect this.

On the PiCar, I send h264 video over the network. You might need to install an additional package for h264 encoding to work.

```bash
sudo apt install gstreamer1.0-plugins-ugly
```

To send h264 video over the network,

```bash
gst-launch-1.0 \
  v4l2src device=/dev/video0 ! \
  videoconvert ! \
  x264enc ! \
  rtph264pay ! \
  udpsink host=192.168.0.2 port=5000
```

To send it as fast as you can,

```bash
gst-launch-1.0 \
  v4l2src device=/dev/video0 ! \
  videoconvert ! \
  x264enc interlaced=true tune=zerolatency speed-preset=ultrafast ! \
  rtph264pay ! \
  udpsink host=192.168.0.2 port=5000
```

To send it as fast as possible under a given framerate (ex: 30)
```bash
gst-launch-1.0 \
  v4l2src device=/dev/video0 ! \
  videoconvert ! \
  videorate ! \
  video/x-raw,framerate=30/1 ! \
  x264enc interlaced=true tune=zerolatency speed-preset=ultrafast ! \
  rtph264pay ! \
  udpsink host=192.168.0.2 port=5000
```



To receive it and display it on an X-window,

```bash
gst-launch-1.0 \
  udpsrc port=5000 ! \
  application/x-rtp,payload=96 ! \
  rtph264depay ! \
  decodebin ! \
  videoconvert n-threads=4 ! \
  ximagesink
```

