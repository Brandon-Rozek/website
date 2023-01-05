---
title: "Mirror a Hugo Site"
date: 2020-12-07T22:41:17-05:00
draft: false
tags: ["Archive", "Hugo"]
medium_enabled: true
---

I'm a big proponent of having offline copies of content. Especially when I'm on travel and don't have easy Internet access. Using the built in hugo webserver and a reverse proxy, I will show how we can host a local mirror of a Hugo site.

## Systemd Service

To begin with, let's create a systemd service that will start up the Hugo webserver automatically. To demonstrate this, I will show a mirror of my website.

Edit `/usr/lib/systemd/system/brandonrozek.service`

```ini
[Unit]
Description=Mirror of brandonrozek.com
Wants=httpd.service
After=httpd.service

[Service]
User=brandon
Type=simple
WorkingDirectory=/home/brandon/repo/brandonrozek.com
ExecStart=/usr/bin/hugo serve --appendPort=false -D -p 22160 -b http://localhost/brandonrozek

[Install]
WantedBy=multi-user.target
```

Replace `httpd` with whatever reverse proxy service this depends on. For every site you mirror, you need to make sure that the port (specified by `-p`) is different. 

Now let's start and enable the service.

```bash
sudo systemctl start brandonrozek
sudo systemctl enable brandonrozek
```

## Nginx Config

If you are using Nginx as your reverse proxy, we will need to create a config at `/etc/nginx/sites-available/brandonrozek.conf`.

```nginx
server {
    location /brandonrozek {
        proxy_pass http://localhost:22160;
        proxy_http_version 1.1;
        proxy_set_header X-Real-IP  $remote_addr;
        proxy_set_header X-Forwarded-For $remote_addr; 
        proxy_set_header Host $host;
    }
}
```

Then to enable it.

```bash
sudo ln -s \
        /etc/nginx/sites-available/brandonrozek.conf \
        /etc/nginx/sites-enabled/
sudo systemctl restart httpd
```

## Apache HTTPD Config

If you are using apache as your reverse proxy, create a config at `/etc/httpd/conf.d/brandonrozek.conf`

```
<Location /brandonrozek>
    ProxyPass http://localhost:22160/brandonrozek retry=0 timeout=5
    ProxyPassReverse http://localhost:22160/brandonrozek
    ProxyPreserveHost On

    Order allow,deny
    Allow from all
</Location>
```

Then restart the `httpd` service.

```bash
sudo systemctl restart httpd
```

