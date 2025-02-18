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
if ! command -v magick > /dev/null; then
    echo "Command magick from imagemagick not found. Exiting..."
fi

IMAGE_FILE="$1"
LAT=$(magick identify -format "%[EXIF:GPSLatitude]\n" "$IMAGE_FILE")
LAT_DIR=$(magick identify -format "%[EXIF:GPSLatitudeRef]\n" "$IMAGE_FILE")
LON=$(magick identify -format "%[EXIF:GPSLongitude]\n" "$IMAGE_FILE")
LON_DIR=$(magick identify -format "%[EXIF:GPSLongitudeRef]\n" "$IMAGE_FILE")
ALT=$(magick identify -format "%[EXIF:GPSAltitude]\n" "$IMAGE_FILE")

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

