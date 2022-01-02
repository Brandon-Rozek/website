---
title: "Backing Up YouTube Content"
date: 2020-02-17T23:17:47-05:00
draft: false
tags: [ "Archive" ]
---

There are great content on YouTube that I would be sad if it went away. Therefore, I did some digging around and found a [great discussion](https://www.reddit.com/r/DataHoarder/comments/863aid/what_is_your_method_of_viewing_youtubedl_backed/dw25vnm/) on Reddit on backing up YouTube videos. The solution is based on `youtube-dl` and I modified the script a little to fit my needs. 

The options added to `youtube-dl` makes it so that meta information such as subtitles, thumbnails, etc get added to the video. 

```bash
youtube-dl --ignore-errors \
           --playlist-reverse \
           --output "%(uploader)s/%(uploader)s - %(title)s - %(upload_date)s.%(ext)s" \
           --format "bestvideo[ext=mp4]+bestaudio[ext=m4a]" \
           --merge-output-format mp4 \
           --all-subs \
           --embed-subs \
           --embed-thumbnail \
           --add-metadata \
           URL_HERE
```

## Audio Only

To extract only audio here's the modified command

```bash
youtube-dl --ignore-errors \
           --playlist-reverse \
           --output "%(uploader)s/%(uploader)s - %(title)s - %(upload_date)s.%(ext)s" \
           --format "bestvideo[ext=mp4]+bestaudio[ext=m4a]" \
           --merge-output-format mp4 \
           --embed-thumbnail \
           --add-metadata \
           --extract-audio
           URL_HERE
```

