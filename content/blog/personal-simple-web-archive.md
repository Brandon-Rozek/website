---
date: 2022-12-24 10:01:16-04:00
draft: false
medium_enabled: true
medium_post_id: 9b2818a6e154
tags:
- Archive
title: Personal Web Archive and How I Archive Single Web pages
---

The [Internet Archive](https://web.archive.org/) is great for providing a centralized database of snapshots of websites throughout time. What happens though when you want to have
your own offline copy during times of little to no internet
access? [Archivebox](https://archivebox.io/) is one solution
to such problem. It behaves similarly to the Internet
archive and also allows importing of RSS feeds to save local copies of blog posts. To install it, you can use `pipx`.
```bash
pipx install archivebox
```

For the rest of this post, however, I want to talk about a simpler tool. A combination of `wget` and `python -m http.server`. In the past, I've used `wget` to [mirror entire websites](/blog/archivingsites/). We can adjust the command slightly so that it doesn't follow links and instead only looks at a single webpage.

```bash
wget --convert-links \
     --adjust-extension \
     --no-clobber \
     --page-requisites \
     INSERT_URL_HERE
```

Now assume we have a folder full of downloaded websites. To view them, we can use any HTTP server. One of the easiest to temporarily setup currently is Python's built in one.

To serve all the files in the current directory
```bash
python -m http.server OPTIONAL_PORT_NUM
```
If you leave the port number field empty, then this returns
```
Serving HTTP on 0.0.0.0 port 8000 (http://0.0.0.0:8000/) ...
```

A few nice side-effects of using `wget` and `python`.
- Python's default webserver shows a list of files in the directory. This can make it easier to browse around the web archive.
- The `wget` flags make it so that if you want to archive `https://brandonrozek.com/blog/personal-simple-web-archive/` then all you need to access is `http://localhost:8000/brandonrozek.com/blog/personal-simple-web-archive`. In other words, it preserves URLs.


Now this approach isn't perfect, if a webpage makes heavy use of javascript or server side features then it'll be incomplete. Though for the majority of the wiki pages or blog posts I want to save for future reference, this approach works well.

My full script is below:
```bash
#!/bin/sh

set -o errexit
set -o nounset
set -o pipefail

ARCHIVE_FOLDER="$HOME/webarchive"

show_usage() {
    echo "Usage: archivesite [URL]"
    exit 1
}

# Check argument count
if [ "$#" -ne 1 ]; then
    show_usage
fi

cd "$ARCHIVE_FOLDER"

wget --convert-links \
     --adjust-extension \
     --page-requisites \
     --no-verbose \
     "$1"

# Keep track of requested URLs
echo "$1" >> saved_urls.txt
```