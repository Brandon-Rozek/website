#!/usr/bin/env sh
mv static/data/toots.json static/data/toots.old.json
SERVER=https://fosstodon.org
MID=108219415927856966
curl "$SERVER/api/v1/accounts/$MID/statuses" -o static/data/toots.json
echo "Done"
