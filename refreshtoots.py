#!/usr/bin/env python
"""
Script to update a stored
copy of Mastodon toots
"""

from urllib import request
from http.client import HTTPResponse
from pathlib import Path
from typing import Optional
import json
import os
import sys

TOOT_SAVE_FILE = "static/data/toots.json"
BACKUP_LOCATION = "static/data/toots.backup.json"
SERVER="https://fosstodon.org"
# Quick way to find user id: https://prouser123.me/mastodon-userid-lookup/
MUID=108219415927856966
# Server default (when < 0) is 20
RETRIEVE_NUM_TOOTS=-1

toots_data = []

# Read in former toot data
has_save = False
try:
    with open(TOOT_SAVE_FILE) as f:
        toots_data = json.load(f)
        has_save = True
        print("Successfully read saved toot data")
except OSError:
    print("Unable to read saved toot data")
except Exception:
    print("Unable to parse saved toot data")

# Check JSON format...
if not isinstance(toots_data, list):
    print("Unexpected JSON format in saved toot data, should be of type list.")
else:
    has_save = True


# Present the user the ability to continue without save data
if not has_save:
    user_input = input("Continue without saved data? (y/n) ")
    if user_input != "y":
        sys.exit(-1)


# Parse former toot ids
saved_toot_ids = set()
for toot in toots_data:
    if 'id' in toot:
        saved_toot_ids.add(toot['id'])


# Grab toots from Mastodon
limit_param = "?limit=" + str(RETRIEVE_NUM_TOOTS) \
    if RETRIEVE_NUM_TOOTS > 0 else ""
url = SERVER + "/api/v1/accounts/" + str(MUID) + "/statuses" + limit_param
response: Optional[HTTPResponse] = None

try:
    response = request.urlopen(url)
except Exception:
    print("Unable to grab toots from Mastodon.")

if response is None:
    sys.exit(-1)

# Parse server response
server_data: Optional[list] = None
try:
    server_data = json.loads(response.read())
except Exception:
    print("Malformed JSON response from server.")

if server_data is None:
    sys.exit(-1)

if not isinstance(server_data, list):
    print("Unexpected JSON response, should be of form list.")
    sys.exit(-1)


print("Successfully grabbed toots from server")


# Add new toots to saved toots
for toot in server_data:
    if 'id' in toot and toot['id'] not in saved_toot_ids:
        toots_data.append(toot)

# Create a backup of the old toots
try:
    os.rename(TOOT_SAVE_FILE, BACKUP_LOCATION)
except:
    print("Unable to create backup of last toot file")
    sys.exit(-1)

# Write toots_data to the disk
try:
    with open(TOOT_SAVE_FILE, "w") as f:
        json.dump(toots_data, f)
except:
    print("Unable to write to save location.")
    print("Grab backup at", BACKUP_LOCATION)


print("Saved toot data to", TOOT_SAVE_FILE)
