---
date: 2022-12-04 22:02:08-05:00
draft: false
math: false
medium_enabled: true
medium_post_id: b08e82293bd2
tags:
- Hugo
title: Deploying my Hugo Website through GitHub Actions
---

For the longest time I've held out on deploying my website through GitHub actions. My rationale at the time was:

>  If I have to execute `git push`, I might as well run a `./sync` script afterwards.

What convinced me otherwise is automated commits. I currently have GitHub actions that sync my [Mastodon toots](/toots) and [iNaturalist observations](/observations). As part of the sync process, a git commit is made. This commit should then trigger a site rebuild.

How do we create a GitHub action that builds a Hugo website and deploys it via `rsync`? The rest of this post will go over the components of the GitHub action that triggers when I update my website.

## Triggers

I currently have three triggers for my deployment GitHub action:

- Manual (`workflow_dispatch`)
- Pushes to the `main` branch
- Daily schedule via `cron`

```yml
on:
  workflow_dispatch:
  push:
    branches: main
  schedule:
    - cron: "21 11 * * *"
```

## Steps

I call my job `build_and_publish` and have it run on top of the latest Ubuntu image.

```yml
jobs:
  build_and_publish:
    runs-on: ubuntu-latest
```

### Step 1: Checkout the Repository

Here we can rely on Github's `checkout` action to provide the latest version of the code.

```yml
steps:
  - name: Checkout
    uses: actions/checkout@v3
    with:
      submodules: true
      fetch-depth: 0
```

Since my website relies on submodules, we need to make sure that its included in the checkout. The `fetch-depth` flag denotes how many commits to retrieve. By default (`fetch-depth: 1`) it only fetches the latest commit, however setting it to `0` retrieves all commits. This is needed for Hugo's last modified feature to work. 

### Step 2: Update the submodules

Even though we checked out the whole repository with its associated submodules, they may be out of date. This step makes sure that we're using the latest version of the submodule.

```yaml
- name: Git submodule update
  run: |
    git pull --recurse-submodules
    git submodule update --remote --recursive
```

### Step 3: Setup Hugo

Since Hugo is a static binary, we can pull it straight from their website.

```yaml
- name: Setup Hugo
  env:
    HUGO_VERSION: 0.105.0
  run: |
    curl -L "https://github.com/gohugoio/hugo/releases/download/v${HUGO_VERSION}/hugo_${HUGO_VERSION}_Linux-64bit.tar.gz" --output hugo.tar.gz
    tar -xvzf hugo.tar.gz
    sudo mv hugo /usr/local/bin
```

### Step 4: Build the website

We can use a separate step to build the website. This along with the deployment are among the few  places where this script can fail, so it's nice to separate it out in case.

```yaml
- name: Build Hugo Website
  run: hugo
```

### Step 5: Install the SSH key

```yaml
- name: Install SSH Key
  run: |
    install -m 600 -D /dev/null ~/.ssh/id_rsa
    echo "${{ secrets.BUILD_SSH_KEY }}" > ~/.ssh/id_rsa
    echo "${{ secrets.HOST_KEY }}" > ~/.ssh/known_hosts
    echo "Host brandonrozek.com
        Hostname brandonrozek.com
        user build
        IdentityFile ~/.ssh/id_rsa" > ~/.ssh/config
```

At this point in our script we need to handle [secrets](https://docs.github.com/en/actions/security-guides/encrypted-secrets). The post I linked to will likely have the most up to date information, but as of this time of writing, you can add secrets by going to the `Settings` tab of the repository. A secret is a key-value pair,  therefore to access your secret in the GH action, you need to reference the key.

```yaml
${{ secrets.YOUR_KEY_HERE }}
```

We need secrets for the SSH key used to deploy the website and the known hosts file so that I don't have to do host verification. The first line ensures that the permissions of the SSH key is correct, and the last line makes it so that the `rsync ` command within my `sync.sh` script is simpler. I use my `sync.sh` not only in the next step of this action but on my own machine which has a different config associated with it.

### Step 6: Deployment

```yaml
- name: Deploy
  run: ./deploy.sh
```

In my repository there is a `deploy.sh` with the following contents

```bash
#!/usr/bin/env sh
rsync -Pazc --exclude=*.bak --delete public/ build@brandonrozek.com:brandonrozek/
```

This syncs everything within the `public` build folder up to my webserver excluding files ended in `.bak` and removing any files on the webserver that aren't in the build folder.

## Conclusion

Other than the `checkout` action, each step does not depend on an external library  to provide the functionality. I think it's important to implement each of the steps ourselves, as opposed to relying on a `hugo` GH action library or a `SFTP` library. Not only does this safeguard us against supply side attacks, it also makes these actions more portable. I am not counting on GitHub to always allow the usage of their build infrastructure for free.

GitHub action in its entirety:

```yaml
name: Build and Deploy Hugo Website

on:
  workflow_dispatch:
  push:
    branches: main
  schedule:
    - cron: "21 11 * * *"

jobs:
  build_and_publish:
    runs-on: ubuntu-latest

    steps:
      - name: Checkout
        uses: actions/checkout@v3
        with:
          submodules: true
          fetch-depth: 0

      - name: Git submodule update
        run: |
          git pull --recurse-submodules
          git submodule update --remote --recursive

      - name: Setup Hugo
        env:
          HUGO_VERSION: 0.105.0
        run: |
          curl -L "https://github.com/gohugoio/hugo/releases/download/v${HUGO_VERSION}/hugo_${HUGO_VERSION}_Linux-64bit.tar.gz" --output hugo.tar.gz
          tar -xvzf hugo.tar.gz
          sudo mv hugo /usr/local/bin

      - name: Build Hugo Website
        id: build
        run: |
          hugo

      - name: Install SSH Key
        run: |
          install -m 600 -D /dev/null ~/.ssh/id_rsa
          echo "${{ secrets.BUILD_SSH_KEY }}" > ~/.ssh/id_rsa
          echo "${{ secrets.HOST_KEY }}" > ~/.ssh/known_hosts
          echo "Host brandonrozek.com
              Hostname brandonrozek.com
              user build
              IdentityFile ~/.ssh/id_rsa" > ~/.ssh/config
      
      - name: Deploy
        run: ./deploy.sh
```