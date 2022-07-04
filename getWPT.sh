#!/bin/sh

set -o errexit
set -o nounset
set -o pipefail

show_usage() {
    echo "Usage: getWPT.sh [imagefile] [?name]"
    exit 1
}

# Check argument count
if [ "$#" -ne 1 ]; then
    show_usage
fi

getLLA="$(dirname $0)/getLLA.sh"
LLA=$("$getLLA" "$1" | tr " " "\n")
IMAGE_NAME="&lt;img src=&quot;$(basename "$1")&quot;/&gt;"
NAME_ARG=${2-""}
NAME=$([ "$NAME_ARG" != "" ] && echo "$NAME_ARG" || echo "$IMAGE_NAME")

echo -e "$LLA\n$NAME" | xargs -d "\n" $(dirname $0)/LLA2WPT.sh

