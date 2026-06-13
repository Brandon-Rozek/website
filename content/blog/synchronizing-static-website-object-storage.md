---
title: "Synchronizing my Static Website with Object Storage"
date: 2026-06-13T17:51:08-04:00
draft: false 
tags: []
math: false
medium_enabled: false
---

I recently updated all my [geo-distributed](/blog/implementing-cdn-geodns/) web servers to run on Fedora CoreOS ([yes, I still love it](/blog/fedora-coreos-first-impressions/)). This gave me an opportunity to revisit how I handle synchronization. Before, I used [Syncthing](https://syncthing.net/) which while awesome is a pain to configure. I don't update my website or certs too frequently so having an always online setup seemed overkill.

So this time I went with an object storage setup.

![](/files/images/blog/website-object-store.svg)

I created a bucket (e.g `my-website`) and within it I have the following directories

```
my-website
├── etc
    └── letsencrypt
        └── live
            └── example.com
                ├── cert.pem
                ├── chain.pem
                ├── fullchain.pem
                └── privkey.pem
└── var
    └── www
        ├── website1
        ├── website2
        └── websiten
```

The core idea is that the webservers will read from this object store to stay up to date with my SSL certificates and my static website files. The rest of the post will go over how I 1) modified my deployment pipeline to push to the object store, 2) push the SSL certificates which are renewed, and 3) pull both the SSL certificates and the website files.

## Deploying my website files

Currently, I use [Github Actions](https://brandonrozek.com/blog/deploying-hugo-website-through-gh-actions/) (labeled as `CI/CD` in the diagram) to build and deploy my website. Beforehand, I had to create a special SSH key-pair and lock it down in case it leaked. For this new setup, we can instead use application keys to authenticate with our object store. 

To lower the threat surface further, we can limit the buckets the application key has access to, whether it has read/write permissions, and what file prefixes the application can access.

For my Github action, I created an application key which has read/write permissions to the prefix `var/www/website`. We need both permissions if we want to delete files that don't exist in the build anymore. Here's the script that I use within the GitHub action to synchronize with the object store after I built the website.

```bash
#!/usr/bin/env sh
set -e

# Environmental variables we need to set within the runner
: "${AWS_ACCESS_KEY_ID:?AWS_ACCESS_KEY_ID is not set}"
: "${AWS_SECRET_ACCESS_KEY:?AWS_SECRET_ACCESS_KEY is not set}"
: "${AWS_ENDPOINT_URL:?AWS_ENDPOINT_URL is not set}"
: "${S3_BUCKET:?S3_BUCKET is not set}"
: "${S3_PATH:?S3_PATH is not set}"

# Safety check so we don't wipe our website!
if [ ! -d "public" ] || [ -z "$(ls -A public)" ]; then
  echo "public/ is empty or missing"
  exit 1
fi

aws s3 sync public/ "s3://${S3_BUCKET}/${S3_PATH}/" \
  --delete \
  --exclude "*.bak"
```

Summarizing how the script works:

- The environmental variables at the beginning are used to authenticate with the object store.
- We sanity check that the `public` folder exists after running `hugo` and that it's non-empty so that we don't accidentally wipe the object store's files.
- We use the `aws` command to perform the sync. Note that this command is [baked into](https://github.com/actions/runner-images/blob/main/images/ubuntu/Ubuntu2404-Readme.md) the default Ubuntu image used by GitHub's runners, so no installation step is required.

## Pushing SSL Certificates

I use [Certbot](https://certbot.eff.org/) to request SSL certificates from Let's Encrypt. After a renewal certificate is issued, the client will run any scripts located within `/etc/letsencrypt/renewal-hooks/deploy` ([documentation](https://eff-certbot.readthedocs.io/en/stable/using.html#renewing-certificates)). In that case, we want to add a `push-certs-to-object-store.sh` file which does just that.

```bash
#!/bin/bash
set -u

S3_BUCKET="INSERT_BUCKET_NAME"
ENDPOINT="INSERT_ENDPOINT_URL"
AWS_ACCESS_KEY_ID="INSERT_KEY_ID_HERE"
AWS_SECRET_ACCESS_KEY="INSERT_SECRET_KEY_HERE"

podman run --rm \
  -e AWS_ACCESS_KEY_ID="${AWS_ACCESS_KEY_ID}" \
  -e AWS_SECRET_ACCESS_KEY="${AWS_SECRET_ACCESS_KEY}" \
  -v "${RENEWED_LINEAGE}:${RENEWED_LINEAGE}:ro,z" \
  -v "/etc/letsencrypt/archive:/etc/letsencrypt/archive:ro,z" \
  docker.io/amazon/aws-cli s3 cp "${RENEWED_LINEAGE}/" \
  "s3://${S3_BUCKET}/${RENEWED_LINEAGE#/}/" \
  --recursive \
  --endpoint-url "${ENDPOINT}"

if [ $? -ne 0 ]; then
  # Insert failure notification technique here
  exit 1
fi

```

Make sure that this script is executable after saving it. This script is different from the last in that it uses `podman` to run `aws-cli` as opposed to executing it directly. This is because I'm using Fedora CoreOS an immutable distribution which [highly discourages overlaying packages](https://docs.fedoraproject.org/en-US/fedora-coreos/faq/#_how_do_i_run_custom_applications_on_fedora_coreos).

Going over the script:

- `${RENEWED_LINEAGE}` is the folder path which contains the renewed certs (e.g `/etc/letsencrypt/live/example.com`)
- We need to mount the `${RENEWED_LINEAGE}` path as well as `/etc/letsencrypt/archive` since the live folder only contains symbolic links to the files which are actually stored in the archive.
- Since we're not modifying these files, we can treat them as read-only (the `ro` flag). Since I have SELinux enabled I threw in the `z` flag so that Podman can automatically handle the contexts for me.
- We're using `cp` instead of `sync` since the renewal procedure will overwrite all the existing files with new ones. Meaning that we don't need read permissions for this application key to update the certificates. 
- Personally for alerting, I send a curl request to a webhook on failure.

## Pulling the files

We can create an application key with read-only permissions in order to pull the SSL certificates and the website files. 

### Website Files

Here's the script that I use to synchronize the local copy with that of the object store:

```bash
#!/bin/bash
set -e

: "${AWS_ACCESS_KEY_ID:?AWS_ACCESS_KEY_ID is not set}"
: "${AWS_SECRET_ACCESS_KEY:?AWS_SECRET_ACCESS_KEY is not set}"
: "${AWS_ENDPOINT_URL:?AWS_ENDPOINT_URL is not set}"
: "${S3_BUCKET:?S3_BUCKET is not set}"

sync_site() {
    local path="$1"

    mkdir -p "/${path}"

    podman run --rm \
      -e AWS_ACCESS_KEY_ID="${AWS_ACCESS_KEY_ID}" \
      -e AWS_SECRET_ACCESS_KEY="${AWS_SECRET_ACCESS_KEY}" \
      -v "/${path}:/${path}:z" \
      docker.io/amazon/aws-cli s3 sync \
      "s3://${S3_BUCKET}/${path}/" "/${path}/" \
      --delete \
      --endpoint-url "${AWS_ENDPOINT_URL}"
}

sync_site "var/www/website1"
sync_site "var/www/website2"
sync_site "var/www/websiten"
```

I have a corresponding systemd unit file and timer which runs every 15 minutes to check for changes.

### SSL Certificates

For my certificates, I only check for new ones daily. The script is very similar...

```bash
#!/bin/bash
set -e

: "${AWS_ACCESS_KEY_ID:?AWS_ACCESS_KEY_ID is not set}"
: "${AWS_SECRET_ACCESS_KEY:?AWS_SECRET_ACCESS_KEY is not set}"
: "${AWS_ENDPOINT_URL:?AWS_ENDPOINT_URL is not set}"
: "${S3_BUCKET:?S3_BUCKET is not set}"
: "${S3_PATH:?S3_PATH is not set}"

mkdir -p -m 700 "/${S3_PATH}"

podman run --rm \
  -e AWS_ACCESS_KEY_ID="${AWS_ACCESS_KEY_ID}" \
  -e AWS_SECRET_ACCESS_KEY="${AWS_SECRET_ACCESS_KEY}" \
  -v "/${S3_PATH}/":"/${S3_PATH}/":z \
  docker.io/amazon/aws-cli s3 cp \
  "s3://${S3_BUCKET}/${S3_PATH}/" \
  "/${S3_PATH}/" \
  --recursive \
  --endpoint-url "${AWS_ENDPOINT_URL}"

```

## Conclusion

That's at least how I have it set up at the time of writing. I've only been running this setup for two days, so we'll see how I feel ultimately. Right now, I'm happy that it simplifies my Ansible setup for these servers. Before this, I had to manually setup Syncthing using their webui.

This updated method allows me to copy a few scripts and systemd unit files over and call it a day. I'm also happy that I don't have to deal with creating a special `build` user and making sure that's locked down. Now we'll see if I can be patient for 15 minutes to see my website changes ;D



