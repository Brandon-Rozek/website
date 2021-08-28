---
title: "Convert DJVU to PDF"
date: 2021-08-27T22:00:00-04:00
draft: false
tags: []
math: false
---

I've recently come across the DJVU file format before and needed to convert it to a PDF. The most reliable way I've found to do it is via the following command.

```bash
djvups FILENAME | ps2pdf - OUTPUT_FILE
```

Where FILENAME first gets converted to the PS file format which then gets converted to a PDF with the name OUTPUT_FILE. To make things easier, I wrote a little script that does this process automatically while preserving the filename.

```bash
#!/bin/bash

set -o errexit
set -o nounset
set -o pipefail

show_usage() {
    echo "Usage: djvu2pdf [FILENAME]"
    exit 1
}

if [ "$#" -ne 1 ]; then
    show_usage
fi

if ! command -v djvups > /dev/null ; then
    echo "djvups not found. Exiting..."
    exit 1
fi

if ! command -v ps2pdf > /dev/null ; then
    echo "ps2pdf not found. Exiting..."
    exit 1
fi

djvups "$1" | ps2pdf - "${1%.*}.pdf"
```

