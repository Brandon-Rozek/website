---
date: 2020-11-24 04:41:41
draft: false
medium_enabled: true
medium_post_id: 334b857013b9
tags:
- Audio-Video
title: Streaming PulseAudio over RTP
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