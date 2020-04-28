---
title: "Replace Audio in Video"
date: 2020-04-20T20:32:26-04:00
draft: false
tags: []
---

I recorded a video and wanted to touch up my audio in audacity. Here's how I used `ffmpeg` to extract the audio, and then replace it with a modified version.

## Extract Audio

If you know the format of the audio (mp3, ogg, aac) then it's possible to do a byte copy of the audio track into a file:

```bash
ffmpeg -i input_video.mkv -vn -acodec copy output.aac
```

| Argument       | Description                |
| -------------- | -------------------------- |
| `-i`           | Input                      |
| `-vn`          | No Video                   |
| `-acodec copy` | Copy audio stream directly |

If you don't know the audio codec and have `mediainfo` installed, then run

```bash
mediainfo --Inform="Audio;%Format%" input_video.mkv
```

If you gave up, then you can transcode the audio (will take longer than direct copy)

```bash
ffmpeg -i input_video.mkv -vn output.aac
```

## Replacing Audio

Once you're done touching up the audio (`touchup.mp3`), you'll want to replace the existing audio with it.

```bash
ffmpeg -i input_video.mkv \
       -i touchup.mp3 \
       -c:v copy \
       -map 0:v:0 \
       -map 1:a:0 \
       output_video.mp4
```

| Argument               | Description                                                  |
| ---------------------- | ------------------------------------------------------------ |
| `-i`                   | Inputs                                                       |
| `-c:v copy`            | Make this a copy operation                                   |
| `-c:v copy -map 0:v:0` | Map the video from the first input to the first video output |
| `-map 1:a:0`           | Map the audio from the second input to the first video output |

