---
title: "Digital Ocean API"
date: 2020-05-06T22:45:30-04:00
draft: false
tags: ["Deployment"]
medium_enabled: true
---

This post is meant for the times that you want to quickly query the Digital Ocean API v2, but do not want to download their great client [`doctl`](https://github.com/digitalocean/doctl). The prerequisite for this post is that you have a [personal access token](https://www.digitalocean.com/docs/apis-clis/api/create-personal-access-token/) configured inside the `$DO_TOKEN` environmental variable.

## List SSH Keys

```bash
curl --silent \
     --request GET \
     --header "Authorization: Bearer $DO_TOKEN" \
     https://api.digitalocean.com/v2/account/keys
```

If you have [`jq`](https://stedolan.github.io/jq/) configured:

```bash
curl --silent \
     --request GET \
     --header "Authorization: Bearer $DO_TOKEN" \
     https://api.digitalocean.com/v2/account/keys |
jq '.ssh_keys[] | "\(.name): \(.id)"'
```

## List Images

```bash
curl --silent \
     --request GET \
     --header "Authorization: Bearer $DO_TOKEN" \
     https://api.digitalocean.com/v2/images?type=distribution
```

If you have [`jq`](https://stedolan.github.io/jq/) configured:

```bash
curl --silent \
     --request GET \
     --header "Authorization: Bearer $DO_TOKEN" \
     https://api.digitalocean.com/v2/images?type=distribution |
jq '.images[] | .slug'
```

## List Regions
```bash
curl --silent \
     --request GET \
     --header "Authorization: Bearer $DO_TOKEN" \
     https://api.digitalocean.com/v2/regions
```

If you have [`jq`](https://stedolan.github.io/jq/) configured:

```bash
curl --silent \
     --request GET \
     --header "Authorization: Bearer $DO_TOKEN" \
     https://api.digitalocean.com/v2/regions |
jq '.regions[] | "\(.name): \(.slug)"'
```


## List Snapshots
```bash
curl --silent \
     --request GET \
     --header "Authorization: Bearer $DO_TOKEN" \
     https://api.digitalocean.com/v2/snapshots
```

If you have [`jq`](https://stedolan.github.io/jq/) configured:

```bash
curl --silent \
     --request GET \
     --header "Authorization: Bearer $DO_TOKEN" \
     https://api.digitalocean.com/v2/snapshots |
jq '.snapshots[] | .name'
```


## Bash Script

Here is a small bash script that combines the functionality above into one file.

``` bash
#!/bin/bash
JQ_INSTALLED=$(command -v jq > /dev/null)

function show_usage {
        echo "Usage: ./do-list (keys|images|regions|snapshots)"
}

function query_api {
    curl --silent \
         --request GET \
         --header "Authorization: Bearer $DO_TOKEN" \
         https://api.digitalocean.com/v2/"$1"
}

function list_keys {
    output=$(query_api account/keys)
    if $JQ_INSTALLED; then
        echo "$output" | jq '.ssh_keys[] | "\(.name): \(.id)"'
    else
        echo "$output"
    fi
}

function list_images {
    output=$(query_api images?type=distribution)
    if $JQ_INSTALLED; then
        echo "$output" | jq '.images[] | .slug'
    else
        echo "$output"
    fi
}

function list_regions {
    output=$(query_api regions)
    if $JQ_INSTALLED; then
        echo "$output" | jq '.regions[] | "\(.name): \(.slug)"'            
    else
        echo "$output"
    fi
}

function list_snapshots {
    output=$(query_api snapshots)
    if $JQ_INSTALLED; then
        echo "$output" | jq '.snapshots[] | .name' 
    else
        echo "$output"  
    fi
}

case $1 in
    keys)
        list_keys;;

    images)
        list_images;;

    regions)
        list_regions;;

    snapshots)
        list_snapshots;;

    *)
        echo Unknown Parameter "'$1'"
        show_usage;;
esac
```

