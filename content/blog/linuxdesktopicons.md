---
title: "Linux Desktop Icons"
date: 2019-06-03T21:05:37-04:00
draft: false
tags: [ "Linux" ]
---

I get asked a decent number of times how to add desktop icons on Linux. Luckily it's incredibly easy. [It's a `freedesktop` standard](http://standards.freedesktop.org/desktop-entry-spec/latest/).

In fact the simplest file would follow the format:

```yaml
[Desktop Entry]
Name=Application Name
Exec=/path/to/executable -randomFlag
Icon=/optional/path/to/icon
Terminal=false
Type=Application
```

Once you have this saved to `yourapplication.desktop` move it to either `/usr/share/applications` if you want it system-wide or `/home/user/.local/share/applications` if you want it just for your `user`.

