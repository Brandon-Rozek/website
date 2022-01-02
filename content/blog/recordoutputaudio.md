---
title: "Record Output Audio via Terminal"
date: 2020-03-01T10:38:06-05:00
draft: false
tags: [ "Linux", "Audio-Video" ]
---

This post is specific to `PulseAudio` on Linux. 

I know of GUI based solutions like [PulseAudio Volume Control](https://freedesktop.org/software/pulseaudio/pavucontrol/) that lets you set up monitor devices. But, what if you want to do this through the terminal?

Luckily, [b-ak](https://askubuntu.com/a/850174) on AskUbuntu gave an elegant answer to this question!

First make sure you have `pulseaudio-utils` installed,

```bash
sudo apt install pulseaudio-utils
```

Next we need to search for the speaker we wish to monitor

```bash
pacmd list-sinks | grep -e 'name:' \
                        -e 'index' \
                        -e 'Speakers'
```

It will output something similar to this:

```bash
  * index: 0
        name: <alsa_output.pci-0000_00_1b.0.analog-stereo>
                analog-output-speaker: Speakers (priority 10000, latency offset 0 usec, available: unknown)
```

From here note the name in `<>` of the speaker you wish to monitor. For example for my output above, I wish to monitor `alsa_output.pci-0000_00_1b.0.analog-stereo`.

Next we will use the `parec` command to record the raw audio stream from the PulseAudio server.

```bash
parec --device alsa_output.pci-0000_00_1b.0.analog-stereo.monitor | encoder_command
```

Notice the addition of `.monitor` at the end of the device.

## `lame`

For the `encoder_command`, b-ak used `lame`.

```bash
lame -r -V0 - out.mp3
```

This command takes in a raw pcm `-r` and enables variable bit rates for the highest quality `-V0`. From there it encodes it and puts it in `out.mp3`.

Now `lame` actually makes a couple assumptions about your raw pcm if you didn't specify additional arguments:

- The Raw PCM is formatted in signed 16-bit little endian samples
- The Raw PCM has 2 channels

If you're assumptions don't meet the above, then you will need to add additional arguments.

## `ffmpeg`

We can replace `lame` with the more featureful `ffmpeg` if we take note of the same assumptions above.

```bash
ffmpeg -f s16le \
       -ac 2 \
       -i pipe:0 \
       -b:a 0 \
       out.mp3
```

Where we can replace the `.mp3` with whatever file extension `ffmpeg` supports.

Now to show the entire command

```bash
parec --device alsa_output.pci-0000_00_1b.0.analog-stereo.monitor | \
  ffmpeg -f s16le \
         -ac 2 \
         -i pipe:0 \
         -b:a 0 \
         out.mp3
```

