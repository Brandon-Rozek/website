#!/bin/bash

# 800px is the width of the content on my site
WIDTH=800

set -o errexit
set -o nounset
set -o pipefail

show_usage() {
    echo "Usage: jpg4web.bash [imagefile]"
    exit 1
}

# Check argument count
if [ "$#" -ne 1 ]; then
    show_usage
fi

# Check that it ends in .jpg
if [[ "$1" != *.jpg ]]; then
    echo "Argument [imagefile] must end in .jpg"
    show_usage
fi

# Check that relevant commands exist
if ! command -v magick > /dev/null; then
    echo "Command magick not found. Exiting..."
fi
if ! command -v jpegoptim > /dev/null; then
    echo "Command jpegoptim not found. Exiting..."
fi

cp "$1" "$1.bak"
magick mogrify -resize "$WIDTH" "$1"
jpegoptim "$1"

