---
date: 2023-01-20 21:14:03-05:00
draft: false
math: false
medium_enabled: true
medium_post_id: b86160f97df9
tags:
- Git
title: Deploying a Lightweight Git Server with CGit using Docker-Compose
---

In this post, I'll talk about how we can setup CGit within a docker-compose setup. We'll be using the [ClearLinux CGit](https://hub.docker.com/r/clearlinux/cgit) container.

## Configuring Apache Webserver

Within the CGit container, an apache webserver is setup to execute the CGit CGI scripts. This configuration is very similar to the [default one](https://github.com/clearlinux/dockerfiles/blob/256680f7c6be8423081e67153de0bff1206f6b63/cgit/httpd-cgit.conf) provided by ClearLinux. However, the default holds your repositories in the `/cgit` subfolder as I wanted it on the root `/` folder.

/etc/httpd-cgit.conf

```apache
ServerName localhost

# Next two lines changed for new document root
DocumentRoot /var/www/cgit
<Directory "/var/www/cgit">
    AllowOverride None
    Options ExecCGI FollowSymLinks
    Require all granted
</Directory>

# cgid module is required to run the cgit binary
LoadModule cgid_module lib/httpd/modules/mod_cgid.so
<IfModule cgid_module>
        ScriptSock /var/run/cgid.sock
</IfModule>

# Path to cgit stylesheet, graphics
Alias /cgit-data /usr/share/cgit
<Directory "/usr/share/cgit">
    AllowOverride None
    Options None
    Require all granted
</Directory>

# Path to cgit binary
# Next line changed
ScriptAlias / /usr/libexec/cgit/cgi-bin/cgit/
<Directory "/usr/libexec/cgit/cgi-bin">
    AllowOverride None
    Options None
    Require all granted
</Directory>
```

## Configuring CGit

Now to configure `cgit` itself, we need to create a file called `cgitrc`. Order matters in the declarations, and from what I can gather you should have your `scan-path` near the end of the file.

To enable cloning and have it discoverable:
```ini
enable-http-clone=1
clone-prefix=https://URL/TO/WEBSITE
```

To download snapsots of the references
```ini
snapshots=tar.gz zip
```

To enable the git config to override the owner and description fields
```ini
enable-git-config=1
```

Cache up to 1000 output entries
```ini
cache-size=1000
```

Root Page configuration
```ini
root-title=Brandon Rozek's Repositories
root-desc=
repository-sort=age

# Start all URLs from the root directory
virtual-root=/
```

Server the appropriate mime-types of certain files
```ini
mimetype.gif=image/gif
mimetype.html=text/html
mimetype.jpg=image/jpeg
mimetype.jpeg=image/jpeg
mimetype.pdf=application/pdf
mimetype.png=image/png
mimetype.svg=image/svg+xml
```

Styles for the website
```ini
css=/cgit-data/cgit.css
logo=/cgit-data/cgit.png
favicon=/cgit-data/favicon.ico
source-filter=/usr/libexec/cgit/filters/syntax-highlighting.sh
about-filter=/usr/libexec/cgit/filters/about-formatting.sh
readme=:README.md
readme=:README
```

Where to find the repositories

```ini
scan-path=/var/www/cgit/
```

## Setting up the container

I prefer using `docker-compose` to help manage all my containers. The first two volumes map the configuration files we created and the last volume holds our repositories.


```yaml
cgit:
  image: docker.io/clearlinux/cgit
  container_name: cgit
  hostname: cgit
  volumes:
    - /etc/cgitrc:/etc/cgitrc
    - /etc/httpd-cgit.conf:/etc/httpd/conf.d/httpd-cgit.conf
    - /var/www/cgit:/var/www/cgit
  restart: always
```

## Populating it with Repositories

Within `/var/www/cgit`, start cloning your repositories:

```bash
git clone --bare REPO_URL
```

If you enabled gitinfo then for each repository you can run `git config -e` and add the following

```ini
[gitweb]
	owner = Name <Email>
	description = Insert your project description here
```

### Aside: Reverse Proxy
In my setup, I have an `nginx` container that handles all of the traffic. Therefore, I don't have users enter to the cgit container directly. I handle this by adding the following reverse proxy configuration.
```nginx
server {
    listen 80;
    listen [::]:80;
    server_name GIT.SERVER.URL

    location / {
        return 301 https://$host$request_uri;
    }
}

server {
    listen 443 ssl;
    listen [::]:443 ssl;
    http2 on;
    server_name GIT.SERVER.URL;

    ssl_certificate /path/to/chain;
    ssl_certificate_key /path/to/private/key;
    include /etc/letsencrypt/options-ssl-nginx.conf;
    ssl_dhparam /etc/letsencrypt/ssl-dhparams.pem;

    location / {
        proxy_pass  http://cgit;
        proxy_set_header Host $host;
        proxy_set_header X-Real-IP $remote_addr;
        proxy_set_header X-Forwarded-For $proxy_add_x_forwarded_for;
        proxy_set_header X-Forwarded-Host $server_name;
       	# Needed to get around HTTP2 Streaming Errors
        proxy_hide_header Upgrade;
    }
}
```

## Conclusion

After all the configuration, you should be able to pull it up using `docker-compose`.

```bash
docker-compose up cgit
```

## References

These references talked about setting up cgit outside of docker, but they helped me understand the various configuration files needed.

- https://russellhaering.com/running-cgit-under-nginx/
- https://jakesthoughts.xyz/blog/setting-up-cgit.html
- https://www.yaroslavps.com/weblog/minimal-git-server/
- https://blog.stefan-koch.name/2020/02/16/installing-cgit-nginx-on-debian
- https://bryanbrattlof.com/cgit-nginx-gitolite-a-personal-git-server/
- https://matejamaric.com/blog/git-server/