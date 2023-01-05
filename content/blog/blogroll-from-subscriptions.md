---
date: 2022-12-18 13:05:49-05:00
draft: false
math: false
medium_enabled: true
medium_post_id: 913b5fa85507
tags: []
title: Blogroll From Subscriptions
---

While I was browsing around personal websites, I found a fun little piece of code from Jake Bauer's [links page](https://www.paritybit.ca/links). 

```bash
grep "xmlUrl" static/subscriptions.opml |\
sed 's/.*text=\"\(.*\)\" xmlUrl=\"\(https\?:\/\/[^\/]*\/\)\(.*\)\" .*/<li><a href=\"\2\">\1<\/a> (<a href=\"\2\3\">feed<\/a>)<\/li>/g'
```

This takes the subscriptions exported from [yarr](https://github.com/nkanaev/yarr) and generates a HTML list which you can then include in a blogroll page.

Running this script on my export from [Feedbin](https://feedbin.com/) yielded some extra metadata being shown in the HTML.  For example: `Joke Bauer type="rss" (Feed)`. So let's edit the code snippet above so that it works for my subscription export.

From my `subscriptions.xml` here's an example entry:

```xml
<outline text="Jake Bauer" title="Jake Bauer" type="rss" xmlUrl="https://www.paritybit.ca/feed.xml" htmlUrl="https://www.paritybit.ca/"/>
```

It looks like I need to extract the `title`, `xmlUrl`, and `htmlUrl` attributes in that specific order. I'll use the same technique from a previous post on [capturing quoated strings](/capturing-quoted-string-sed).

```bash
grep "xmlUrl" subscriptions.xml |\
sed 's/.*title=\"\([^\"]*\)\".*xmlUrl=\"\([^\"]*\)\".*htmlUrl=\"\([^\"]*\)\".*/<li><a href=\"\3\">\1<\/a> (<a href=\"\2\">feed<\/a>)<\/li>/g'
```

We can then clean this up into a `create_blogroll` script saved within [`~/.local/bin`](/blog/customexec/).

```bash
#!/bin/sh

set -o errexit
set -o nounset

show_usage() {
    echo "Usage: create_blogroll [subscriptions.xml]"
    exit 1
}

# Check argument count
if [ "$#" -ne 1 ]; then
    show_usage
fi

QUOTED_STR="\"\([^\"]*\)\""
XML_EXPR=".*title=$QUOTED_STR.*xmlUrl=$QUOTED_STR.*htmlUrl=$QUOTED_STR.*"
HTML_EXPR="<li><a href=\"\3\">\1<\/a> (<a href=\"\2\">feed<\/a>)<\/li>"
REPLACE_EXPR="s/$XML_EXPR/$HTML_EXPR/g"

grep "xmlUrl" "$1" | sed "$REPLACE_EXPR"
```