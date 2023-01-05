---
title: "How to trim a video using FFMPEG"
date: 2022-09-28T18:46:32-04:00
draft: false
tags: ["Audio-Video"]
math: false
medium_enabled: true
---

Recently I came across a video that I wanted to split up into multiple files. Given my love for `ffmpeg` the video/audio swiss army knife, I knew there had to be a solution for cutting a video on the terminal. Luckily on [AskUbuntu](https://askubuntu.com/a/56044), Luis Alvarado provides a command snippet. This post will go into slightly more detail on the flags used in the command

```bash
ffmpeg -ss 00:00:00 \
	-t 00:30:00 \
	-i input.mp4 \
	-vcodec copy \
	-acodec copy \
	output.mp4
```

| Command   | Description                                                  |
| --------- | ------------------------------------------------------------ |
| `-ss`     | Position within the input file. Most file formats do not allow exact seeking, so ffmpeg will pick the closest seek point. Format is in *time duration* notation. |
| `-t`      | Limits the duration of data read from the input file.  Format is in *time duration* notation. |
| `-vcodec` | Format used to transcribe the video. Use `copy` to not transcribe to a different format. |
| `-acodec` | Format used to transcribe the audio. Use `copy` to not transcribe to a different format. |

Time duration notation follows the format `<HH>:<MM>:<SS>` where `HH` is the number of hours, `MM` is the number of minutes, and `SS` is the number of seconds.

For this command in general, the output video length would be the same time duration as specified in the `-t` flag.