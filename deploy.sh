#!/usr/bin/env sh
set -e

: "${AWS_ACCESS_KEY_ID:?AWS_ACCESS_KEY_ID is not set}"
: "${AWS_SECRET_ACCESS_KEY:?AWS_SECRET_ACCESS_KEY is not set}"
: "${AWS_ENDPOINT_URL:?AWS_ENDPOINT_URL is not set}"
: "${S3_BUCKET:?S3_BUCKET is not set}"
: "${S3_PATH:?S3_PATH is not set}"

if [ ! -d "public" ] || [ -z "$(ls -A public)" ]; then
  echo "public/ is empty or missing"
  exit 1
fi

aws s3 sync public/ "s3://${S3_BUCKET}/${S3_PATH}/" \
  --delete \
  --exclude "*.bak"