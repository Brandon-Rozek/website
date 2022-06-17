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
LLA=$("$getLLA" "$1")
IMAGE_NAME=$(basename "$1")
NAME_ARG=${2-""}
NAME=$([ "$NAME_ARG" != "" ] && echo "$NAME_ARG" || echo "$IMAGE_NAME")

echo -e "$LLA\n$NAME" | xargs $(dirname $0)/LLA2WPT.sh

