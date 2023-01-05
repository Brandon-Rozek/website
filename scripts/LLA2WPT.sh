#!/bin/sh

set -o errexit
set -o nounset
set -o pipefail

show_usage() {
    echo "Usage: LLA2WPT.sh [LAT] [LON] [ALT] [?NAME]"
    exit 1
}

# Check argument count
if [ "$#" -ne 3 ] | [ "$#" -ne 4 ]; then
    show_usage
fi


LAT="$1"
LON="$2"
ALT="$3"
NAME=${4-""}

echo "<wpt lat=\"$LAT\" lon=\"$LON\">"
echo -e "\t<ele>$ALT</ele>"
echo -e "\t<name>$4</name>"
echo "</wpt>"

