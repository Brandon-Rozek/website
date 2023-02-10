---
date: 2022-06-19 19:01:35-04:00
draft: false
math: false
medium_enabled: true
medium_post_id: 45193055c22d
tags:
- GPS
title: Retreiving GPS data in decimal format from EXIF data in photos
---

For a new feature that I'm cooking up for my website, I need to grab the GPS information from the EXIF data stored in my images. Luckily, `imagemagick`
comes to our rescue.

```bash
identify -verbose $IMAGE_FILE | grep GPS
```

This will return something like the following:
```
exif:GPSAltitude: 1250/100
exif:GPSAltitudeRef: .
exif:GPSDateStamp: 2022:06:12
exif:GPSImgDirection: 137/1
exif:GPSImgDirectionRef: M
exif:GPSInfo: 1004
exif:GPSLatitude: 40/1, 50/1, 1815/100
exif:GPSLatitudeRef: N
exif:GPSLongitude: 73/1, 53/1, 3625/100
exif:GPSLongitudeRef: W
exif:GPSTimeStamp: 17/1, 32/1, 30/1
exif:GPSVersionID: ....
```

To request a specific field, for example Latitude:
```bash
identify -format "%[EXIF:GPSLatitude]\n" "$IMAGE_FILE"
```

As with the verbose flag, it will return the information in degrees format
```
40/1, 50/1, 1815/100
```

The following bash function will take the degrees format and convert
it to the more common decmial format:
```bash
DegreesToDecimal() {
        L0=$(echo "$1" | cut -d "," -f 1)
        L1=$(echo "$1" | cut -d "," -f 2)
        L2=$(echo "$1" | cut -d "," -f 3)
        echo "scale=6;$L0 + $L1/60 + $L2/3600" | bc
}
```

For example:
```bash
LAT=$(identify -format "%[EXIF:GPSLatitude]\n" "$IMAGE_FILE")
LAT_DEC=$(DegreesToDecimal "$LAT")
echo "$LAT_DEC"
```
will output:
```
40.838374
```

We can then package this into a script which will output the latitude, longitude, and altitude (m) of an image in decmial format.
```bash
#!/bin/sh

set -o errexit
set -o nounset
set -o pipefail

show_usage() {
    echo "Usage: getLLA.sh [imagefile]"
    exit 1
}

# Check argument count
if [ "$#" -ne 1 ]; then
    show_usage
fi

# Check that relevant command exist
if ! command -v identify > /dev/null; then
    echo "Command identify from imagemagick not found. Exiting..."
fi

IMAGE_FILE="$1"
LAT=$(identify -format "%[EXIF:GPSLatitude]\n" "$IMAGE_FILE")
LAT_DIR=$(identify -format "%[EXIF:GPSLatitudeRef]\n" "$IMAGE_FILE")
LON=$(identify -format "%[EXIF:GPSLongitude]\n" "$IMAGE_FILE")
LON_DIR=$(identify -format "%[EXIF:GPSLongitudeRef]\n" "$IMAGE_FILE")
ALT=$(identify -format "%[EXIF:GPSAltitude]\n" "$IMAGE_FILE")

DegreesToDecimal() {
        L0=$(echo "$1" | cut -d "," -f 1)
        L1=$(echo "$1" | cut -d "," -f 2)
        L2=$(echo "$1" | cut -d "," -f 3)
        echo "scale=6;$L0 + $L1/60 + $L2/3600" | bc
}

LAT_DEC=$(DegreesToDecimal "$LAT")
LON_DEC=$(DegreesToDecimal "$LON")
ALT_DEC=$(echo "scale=6;$ALT" | bc)

LAT_PREFIX=$([ $LAT_DIR == "S" ] && echo "-" || echo "")
LON_PREFIX=$([ $LON_DIR == "W" ] && echo "-" || echo "")

echo "$LAT_PREFIX$LAT_DEC"
echo "$LON_PREFIX$LON_DEC"
echo "$ALT_DEC"
```