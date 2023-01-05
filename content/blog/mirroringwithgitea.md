---
title: "Mirroring with Gitea"
date: 2020-12-07T23:46:21-05:00
draft: false
tags: ["Archive"]
medium_enabled: true
---

Sites like Github, Gitlab, and BitBucket have nice UIs that make looking at commit diffs and issue tracking easier. However, this requires an internet connection. What if we can mirror the content from these sites locally? Gitea comes to the rescue!

## Installation

Download gitea and make it executable.
```bash
wget -O gitea https://dl.gitea.io/gitea/1.13.0/gitea-1.13.0-linux-amd64
chmod +x gitea
```

Create the stow directory
```bash
sudo mkdir /usr/local/stow/gitea-1.13.0
```

Start by moving the executable to this directory
```bash
sudo mkdir /usr/local/stow/gitea-1.13.0/bin
sudo mv gitea-1.13.0-linux-amd64 \
        /usr/local/gitea-1.13.0/bin/
```

Add a `git` user that gitea will use.
```bash
sudo adduser \
   --system \
   --shell /bin/bash \
   --gecos 'Git Version Control' \
   --group \
   --disabled-password \
   --home /home/git \
   git
```

Create directories gitea expects.
```bash
sudo mkdir -p /usr/local/stow/gitea-1.13.0/var/lib/gitea/{custom,data,log}
sudo chown -R git:git /usr/local/stow/gitea-1.13.0/var/lib/gitea
sudo chmod -R 750 /usr/local/stow/gitea-1.13.0/var/lib/gitea

sudo mkdir -p /usr/local/stow/gitea-1.13.0/etc/gitea
sudo chown root:git /usr/local/stow/gitea-1.13.0/etc/gitea
sudo chmod 770 /usr/local/stow/gitea-1.13.0/etc/gitea
```

Stow gitea
```bash
cd /usr/local/stow
sudo stow gitea-1.13.0
```

## Systemd Service
Edit `/usr/lib/systemd/system/gitea.service`.
```ini
[Unit]
Description=Gitea (Git with a cup of tea)
After=syslog.target
After=network.target
Requires=nginx.service

[Service]
Type=simple
User=git
Group=git
WorkingDirectory=/usr/local/var/lib/gitea
ExecStart=/usr/local/bin/gitea web --config /usr/local/etc/gitea/app.ini
Environment=USER=git HOME=/home/git GITEA_WORK_DIR=/usr/local/var/lib/gitea

[Install]
WantedBy=multi-user.target
```
Start and enable gitea.
```bash
sudo systemctl start gitea
sudo systemctl enable gitea
```

## Gitea Setup
Go to http://localhost:3000/install

Check "Enable Local Mode"
For security, check "Disable Self-Registration" and "Require Sign-In to View Pages"
Setup the "Administrator Account Settings"

## Nginx Setup
Edit `/etc/nginx/sites-available/gitea.conf`
```nginx
location /gitea/ {
    proxy_pass http://localhost:3000/;
    proxy_http_version 1.1;
    proxy_set_header X-Real-IP  $remote_addr;
    proxy_set_header X-Forwarded-For $remote_addr; 
    proxy_set_header Host $host;
}
```
Enable the site
```bash
sudo ln -s \
        /etc/nginx/sites-available/gitea.conf \
        /etc/nginx/sites-enabled/
sudo systemctl restart nginx
```

## Apache HTTPD Setup
Edit `/etc/httpd/conf.d/gitea.conf`
```
<Location /gitea>
    ProxyPass http://localhost:3000 retry=0 timeout=5
    ProxyPassReverse http://localhost:3000
    ProxyPreserveHost On

    Order allow,deny
    Allow from all
</Location>
```
Restart httpd
```bash
sudo systemctl restart httpd
```

## Mirroring
To mirror a repo, first click on the plus sign and select "New Migration", then make sure to check the "This repository will be a mirror".
