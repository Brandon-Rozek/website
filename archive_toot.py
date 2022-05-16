#!/usr/bin/env python
"""
Saves a toot to reference as a shortcode
in a post.
"""
from http.client import HTTPResponse
from urllib.parse import urlparse
from urllib import request
from typing import Optional
import argparse
import json
import sys

SAVE_DIR = "static/data/toots"

# Grab arguments
parser = argparse.ArgumentParser(description="Save a toot")
parser.add_argument("toot_url", type=str, help="URL to specific toot")
args = vars(parser.parse_args())

parsed_url = urlparse(args['toot_url'])

# Parse Arguments
SERVER = f"{parsed_url.scheme}://{parsed_url.netloc}"
TOOT_ID = parsed_url.path.split("/")[-1]

# Query server
url = SERVER + "/api/v1/statuses/" + TOOT_ID
response: Optional[HTTPResponse] = None

try:
    response = request.urlopen(url)
except Exception:
    print("Unable to grab toots from Mastodon.")
if response is None:
    sys.exit(-1)

# Parse server response
server_data: Optional[dict] = None
try:
    server_data = json.loads(response.read())
except Exception:
    print("Malformed JSON response from server.")

if server_data is None:
    sys.exit(-1)

if not isinstance(server_data, dict):
    print("Unexpected JSON response, should be of form dict.")
    sys.exit(-1)

# Save toot
TOOT_REFERENCE = f"{parsed_url.netloc.replace('.', '-')}-{TOOT_ID}"
TOOT_SAVE_FILE = f"{SAVE_DIR}/{TOOT_REFERENCE}.json"

try:
    with open(TOOT_SAVE_FILE, "w", encoding="UTF-8") as f:
        json.dump(server_data, f)
except:
    print("Unable to write to save location.")
    sys.exit(-1)

print("Saved Toot Reference", TOOT_REFERENCE)
