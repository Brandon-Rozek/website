---
title: "Starbound Server using LXC"
date: 2023-12-03T11:17:10-05:00
draft: false
tags: []
math: false
medium_enabled: false
---

I recently had a gaming session with old friends and we played the game Starbound. In hopes of continuing our session in the near future, I set up a Starbound server for us all to connect to.

However, since I've recently learned how to setup LXC containers, my host OS is Fedora, and the [steamcmd](https://developer.valvesoftware.com/wiki/SteamCMD#Ubuntu) provides instructions for Debian, Ubuntu, and Arch.  I've decided to set up a system container using LXC.

Also who knows how secure these game servers are. It's likely a good idea to virtualize them when possible...

This guide assumes you have a Ubuntu Jammy (22.04) amd64 system container configured and that you're within the root shell of that container. For help with that, check out [my post](/blog/lxc-fedora-38/).

## Installing Starbound

Since we start off with a root account, let's create another user which we'll call `steam`.

```bash
adduser steam
```

We'll give `sudo` privileges to our `steam` user. You can always remove this privilege after setting it up.

```bash 
usermod -aG sudo steam
```

Now let's go into our steam user

```bash
su steam
```

Before using `apt`, it's always a good idea to make sure our system is up to date.

```bash
sudo apt update && sudo apt upgrade
```

Steam requires 32-bit libraries to work properly, so we'll need to setup the multiverse repository and add i386 support.

```bash
sudo apt install software-properties-common
sudo add-apt-repository multiverse
sudo dpkg --add-architecture i386
```

Finally, we can update our local cache and install `steamcmd`.

```bash
sudo apt update
sudo apt install steamcmd
```

Now let's open our steam shell.

```bash
steamcmd
```

We should now see a `steam>` at the beginning of our prompt. We'll tell steam to install Starbound under the Starbound folder of our `$HOME` directory.

```bash
force_install_dir /home/steam/starbound
```

I'm unsure if we need to login or do this anonymously. When I set this up, I've logged into my steam account. Write to me if you were able to get this to work anonymously.

```bash
login <username> <password>
```

After logging in (it might ask for a 2FA code), we can install Starbound using the following command.

```bash
app_update 211820
```

We can then leave the steam shell.

```bash
quit
```

At this point, we should check to see if the server binary runs as expected.

```bash
/home/steam/starbound/linux/starbound_server
```

If this works, great! I didn't face any issues at this step, but feel free to write in if you did.

## Configuring Networking

We now have a Starbound server running from within our LXC container. Since we want players outside of the host system to access the Starbound server, we'll need to setup some firewall rules and TCP forwarding.

First we'll need to allow traffic to go into our container network.

```bash
sudo ufw allow in on lxdbr0
sudo ufw route allow in on lxdbr0
```

On the host, we need to open up the Starbound port

```bash
sudo ufw allow 21025
```

Then we need to route TCP traffic back and forth. For this I used `nginx`.

```bash
sudo dnf install nginx
```

We need to get the container IP.

```bash
lxc-ls --fancy
```

Add the following to the end of `/etc/nginx/nginx.conf`

```
stream {
    upstream starbound {
        server CONTAINERIP:21025;
    }

    server {
        listen 21025;
        proxy_pass starbound;
    }
}
```

Start and enable the nginx service

```bash
sudo systemctl enable --now nginx
```

If you face an error here, it might be because of `selinux`. Either disable that or configure it to allow for binding of `21025`.

At this point, you can try to connect to the Starbound server using the game! I didn't face any unexpected issues at this part, but feel free to write in if you did.

## Locking down Starbound (Optional)

This part is optional, but if you don't want any arbitrary person to connect to your Starbound server, you'll need to lock it down.

Inside your container exit the `/home/steam/starbound/storage/starbound_server.config`

Disallow anonymous connections

```json
"allowAnonymousConnections": false
```

Add users with usernames and passwords

```bash
"serverUsers" : {
  "user1" : {
    "admin" : false,
    "password" : "somethinghere"
  },
  "user2" : {
    "admin" : false,
    "password" : "somethinghere2"
  }
}
```

Keep in mind that we didn't set up TLS so I wouldn't put a password here that gets used anywhere else.

## Automatically Starting up the Starbound server

First make sure [the container autostarts on boot](/blog/lxc-fedora-38/). 

Then within the container, we can set up a systemd service to start the starbound server.

Edit `/etc/systemd/system/starbound.service`

```ini
[Unit]
Description=StarboundServer
After=network.target

[Service]
WorkingDirectory=/home/steam/starbound/linux
User=steam
Group=steam
Type=simple
ExecStart=/home/steam/starbound/linux/starbound_server
RestartSec=15
Restart=always
KillSignal=SIGINT

[Install]
WantedBy=multi-user.target
```

Then start and enable the service

```bash
sudo systemctl enable --now starbound
```
