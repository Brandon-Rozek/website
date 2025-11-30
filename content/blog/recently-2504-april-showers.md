---
title: "Recently: April Showers Bring..."
date: 2025-04-12T10:38:45-04:00
draft: false
tags:
  - homelab
math: false
medium_enabled: false
---

I woke up this morning to a small layer of snow outside. In the Northeastern part of the United States, it's said that we have [12 seasons](https://12seasons.nyc/).

- Winter
- Fool's Spring
- Second Winter
- Spring of Deception
- Third Winter
- The Pollening
- Actual Spring
- Summer
- Hell's Front Porch
- False Fall
- Second Summer
- Actual Fall

At the time of this post, we're at "Third Winter". I look forward to warm weather again soon.

---

*Homelab Updates!*

**Nextcloud:** I moved away from the Nextcloud all-in-one and instead maintain a LXC container. Unfortunately for me, the all-in-one was too much of a black box. My current deployment is significantly less stateless, but I understand it better.

While I was doing that, I've been exploring use-cases for MinIO so I thought maybe I'll try [configuring my object storage as the primary storage](https://docs.nextcloud.com/server/latest/admin_manual/configuration_files/primary_storage.html). However, I neglected to read the third paragraph...

> All metadata (filenames, directory structures, etc) is stored in Nextcloud and not in the object store

This makes performing backups significantly harder! So, I switched back to the normal filesystem backend for Nextcloud.

**Immich:** Multiple people have told me that Immich is the way to go for viewing your photos. Previously, I was scared to try it out because of the banner at the top of their page.

> The project is under **very active** development. Expect bugs and changes. Do not use it as **the only way** to store your photos and videos.

However, I have backups so what am I afraid of?

I have to say, the setup was flawless. The software is not buggy at all, and everything is snappy and works as expected.

To import my photos, I mounted my existing directory on a *different* mountpoint than the one Immich uses to store files.

Example Docker-Compose Configuration

```yaml
immich-server:
  container_name: immich_server
  image: ghcr.io/immich-app/immich-server:release
  env_file:
    - /etc/immich/immich.env
  volumes:
    - /home/user/immich/pictures:/usr/src/app/upload
    - /home/user/storage/pictures:/pictures:ro # Existing photo library
    - /etc/localtime:/etc/localtime:ro
  depends_on:
    - immich-redis
    - immich-database
  restart: unless-stopped

# Copy immich-redis and immich-database from the Github repo
# ...
```

Then I had to log onto the Immich webapp to create a user and an API key. After that, we can  `exec` into the container.

```bash
docker exec -it immich_server /bin/bash
```

Login with the API key

```bash
immich login http://localhost:2283/api <APIKEY>
```

Then upload the photos

```bash
immich upload --recursive /pictures
```

*Warning:* You need enough space to have two copies of your photos. If you don't then you'll need to iteratively upload and delete as you go instead of doing this all at once.

After a bit, you should see thumbnails on the app!

**Music Streaming:** Since I listen to Japanese music, not all music services work for me. Currently I pay for YT Music, though I've been slowly trying to buy albums directly from Qobuz to (1) better support the artists, and (2) guarantee that it won't disappear from my library. This is only recent, so I don't fully endorse my workflow, but it's been working so far and I think it's great.

1. Buy flac from [Qobuz](https://www.qobuz.com/us-en/shop)
2. Transfer the files to my home server
3. Run [`beet import`](https://beets.io/) to copy the music into my library with all the metadata sorted out.
4. Use [Navidrome](https://www.navidrome.org/), an open-source server software, to provide a subsonic API to stream the music.
   - It even transcodes on the fly for you if your device doesn't support the format it's stored in.
5. Use [Symfonium](https://symfonium.app/) on Android as my music app and set it to search for music on my Navidrome server.



Both Immich and setting up this music streaming is very new to me! So if you have any suggestions or comments about your workflow feel free to reach out :)
