---
title: "How to use Nginx under Traefik"
date: 2019-12-16T19:55:47-05:00
draft: false
medium_enabled: true
---

I've been enjoying Traefik for its auto-discovery of containers. The only problem is that for a couple containers such as Plex and HomeAssistant I have host networking enabled. This usually results in Traefik failing to forward the traffic properly.

Having more fine grained control is exactly what Nginx is for!  I don't want to switch my whole setup to Nginx since that would be a lot of configuration files for every docker container. But I think having configuration files for containers that use host networking is manageable.

In your docker-compose file first make sure that Traefik is disabled for containers that use host networking by adding the label `traefik.enable=false`

```yaml
  homeassistant:
    image: homeassistant/home-assistant
    container_name: homeassistant
    hostname: homeassistant
    network_mode: host
    environment:
      - PUID=1000
      - PGID=1000
    volumes:
      - /Volumes/homeassistant/config:/config
    restart: always
    labels:
      - traefik.enable=false
```

Then add a new section for `nginx` adding the domains that you wish it to manage in the labels

```yaml
nginx:
 image: linuxserver/nginx
 container_name: nginx
 environment:
   - PUID=1000
   - PGID=1000
 volumes:
   - /Volumes/nginx/config:/config
 restart: always
 labels:
   - traefik.http.routers.my-container.rule=Host(`plex.example.com`,`homeassistant.example.com`)
```

Now on the host system add the configuration files for nginx to consume. Example:

```nginx
server {
    listen 80;
    listen [::]:80;

    server_name plex.example.com;

    location / {
        proxy_pass http://homelanip:32400;
        proxy_http_version 1.1;
        proxy_set_header Upgrade $http_upgrade;
        proxy_set_header Connection 'upgrade';
        proxy_set_header Host $host;
        proxy_cache_bypass $http_upgrade;
    }
}
```

Similarly add a configuration file for `homeassistant` or any other service you have.

Now for this example, the subdomains `plex.example.com` and `homeassistant.example.com` are managed by Nginx.

To finish it off, `docker-compose start nginx`.
