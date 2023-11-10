---
title: "Transcoding Plex Video in RAM"
date: 2023-11-09T21:58:55-05:00
draft: false
tags: []
math: false
medium_enabled: false
---

One not so secret trick I recently learned is that you can have Plex transcode video in RAM to speed it up. This is especially useful if like me, your server runs on spinning rust hard drives and you have many GBs of RAM to spare.

**Step 1:** Set a transcode location in Plex.

Log into your admin account. Then go to Settings -> Transcoder.

From there select the "Show Advanced" button and scroll down to the "Set Transcoder temporary directory".

I've set it to `/transcode` and then hit the Save button.

**Step 2: Setup `tmpfs`**

We can use `tmpfs` to setup a filesystem that will be stored in RAM at the transcode directory. If you have Plex installed not in a container, then you can follow the [Arch Wiki Instructions](https://wiki.archlinux.org/title/Tmpfs) for setting it up.

I use `docker-compose` for my setup, so it involved adding some limes to my yaml.

```yaml
  plex:
    image: lscr.io/linuxserver/plex:1.32.5
    # ...
    tmpfs:
      - /transcode
    # ...
```

I don't promise massive performance increase by setting up Plex this way, but I do think it makes sense:

- Improved write speeds for the transcoded files
- The transcoded files aren't persistent

If you're of a different opinion, let me know.
