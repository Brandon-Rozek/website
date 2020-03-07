---
title: "Espeak"
date: 2020-03-01T10:33:33-05:00
draft: false
tags: [ "linux" ]
---

`espeak` is a command line tool that lets you type in messages and have it said back to you.

To install on Ubuntu

```bash
sudo apt install espeak
```

It's as simple as running it and typing out what you want to say

![](/files/images/20200301113507984.png)

{{< addaudio "/files/audio/20200301113507984.mp3" >}}

[Delightly Linux](https://delightlylinux.wordpress.com/2015/03/23/linux-has-voice-with-espeak/) wrote a great post describing the different features `espeak` has.

Playing around with different voices and I can get something like this:

![](/files/images/20200301115220550.png)

{{< addaudio "/files/audio/20200301115220550.mp3" >}}

You can also replicate the sound above by piping the text into `espeak`

```bash
echo "Warning warning the build has failed" | espeak -s 140 -v en+f4
```

## Subset of Arguments

| Argument | Description                                  |
| -------- | -------------------------------------------- |
| -f       | Text file to speak                           |
| -p       | Pitch adjustment from 0 to 99 (default: 50)  |
| -s       | Speed in words per minute (default: 160)     |
| -v       | Voice file from `espeak-data/voices`         |
| -w       | Write output to WAV file instead of speakers |

