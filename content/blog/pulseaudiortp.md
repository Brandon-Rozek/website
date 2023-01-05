---
title: "Streaming PulseAudio over RTP"
date: 2020-11-23T23:41:41-05:00
draft: false
tags: ["Audio-Video"]
medium_enabled: true
---

With PulseAudio, we can send a RTP stream over multicast UDP. Here is the bash commands to setup a sink where anything sent to it gets broadcasted to the multicast address 224.0.0.56 at port 46416.

```bash
pacmd load-module module-null-sink sink_name=RTP
pacmd update-sink-proplist RTP device.description=RTP
pacmd load-module module-rtp-send \
  source=RTP.monitor \
  destination_ip=224.0.0.56 \
  port=46416
```

Then in `pavucontrol`, you can push the audio of any application to the RTP sink we just created.