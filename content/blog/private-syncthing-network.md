---
title: "How to set up a private Syncthing network"
date: 2023-09-19T22:54:50-04:00
draft: false
tags: []
math: false
medium_enabled: false
---

[Syncthing](https://syncthing.net/) is a peer to peer file synchronization program that I've been using for many years. I've never had any issues with it and I consider it rock solid in stability.

Each device is given a unique identifier, which it can then query a discovery server for its IP address. The Syncthing foundation runs a public discovery server to facilitate this.

Once the IPs are known, if a direct connection can't be established, then Syncthing will make use of a relay. A relay only forwards encrypted packets like a router and is unable to inspect its contents.

The community runs a pool of public relay servers that are configured by default as well.

For privacy reasons, one might not want to make use of these public discovery and relay servers. Also, it may be more performant to run your own relay servers. We'll show how you can configure Syncthing to work without relying on these community services.

We'll go over:

- How to setup a private relay server
- How to configure the clients to disable discovery and use the private relay server.

### Setting up the private relay server

First we'll need to have `strelaysrv` installed. On Fedora, this is under the `syncthing-tools` package.

```bash
sudo dnf install syncthing-tools
```

Then we need to make sure that port 22067 is open to TCP traffic on our firewall. Optionally, strelaysrv can expose a `/status` HTTP endpoint on port 22070, but I didn't enable it myself.

```bash
sudo ufw allow 22067/tcp
```

If applicable, make sure that these are enabled in your cloud firewall.

When `strelaysrv` runs for the first time, it's going to create a set of public/private keys. We'll store this in `/etc/strelaysrv`.

```bash
sudo mkdir /etc/strelaysrv
```

To run as a daemon on startup, we'll write a systemd service to `/etc/systemd/system/strelaysrv.service`.

```ini
[Unit]
Description=Syncthing Relay Server
After=network.target
Documentation=man:strelaysrv(1)

[Service]
ExecStart=/usr/bin/strelaysrv -keys=/etc/strelaysrv -status-srv="" -token=INSERT_TOKEN_HERE

# Hardening
User=brandonrozek
Group=brandonrozek
ProtectSystem=strict
ReadWritePaths=/etc/strelaysrv
NoNewPrivileges=true
PrivateTmp=true
PrivateDevices=true
ProtectHome=true
SystemCallArchitectures=native
MemoryDenyWriteExecute=true

[Install]
WantedBy=multi-user.target
```

Let's discuss the flags given in `ExecStart`:

- `-keys` indicate the location that the public/private keys will be written to or read from
- `-status-srv=""` disables the status endpoint on port 22070. You can remove that flag if you want that feature.
- `-token="INSERT_TOKEN_HERE"` first prevents the server from joining the public pool and requires clients to specify the token in order to use the relay.
  - NOTE:  Replace the token with a random output, such as `uuidgen`.

The hardening section is better left to a future blog post. In the meantime, read the [Freedesktop documentation](https://www.freedesktop.org/software/systemd/man/systemd.exec.html) for more information.

Now we can enable the service on boot and start the Syncthing relay service.

```bash
sudo systemctl enable --now strelaysrv.service
```

You'll need to note the `relay://` URL shown at `sudo systemctl status strelaysrv` for the next section.

### Client Configuration

On the client side, we have to prevent the Syncthing service from listening to traffic from public relays and not rely on the public servers for discovery. These instructions are for the GUI interface on `localhost:8384`.

Lets say we have a relay at `relay:examplerelay.com?id=SOME-ID&token=SOME-TOKEN`

Change Settings->Connections->Sync Protocol Listen from `default` to:

```
relay:examplerelay.com:22067?id=SOME-ID&token=SOME-TOKEN
```

If we want to allow for direct connections, then we'll need to have port `22000`/UDP open on the client side.

```bash
sudo ufw allow 22000/udp
```

Then edit Settings->Connections->Sync Protocol Listen to:

```
quic://0.0.0.0:22000, relay://examplerelay.com:22067/?id=SOME-ID&token=SOME-TOKEN
```

Uncheck 'Global Discovery' within that menu. Optionally,  uncheck "Local Discovery" as well.

Local discovery only sends packets within the local network so it's safe to leave it enabled if desired. If you're worried about information leakage in a public WiFi network, then leave it disabled.

Since we disabled the discovery server, how do we find a connection to the different devices? Here, we can make use of the relay, and/or hard code static ip addresses that some devices may have.

For example, say that I have a home-server on the following IP addresses:

- `192.168.1.58` within my home network
- `10.10.2.7` within my Wireguard network.

Then under home-server->Settings->Advanced->Addresses, I can set it to:

```
quic://192.168.1.58, quic:10.10.2.7, relay://examplerelay.com:22067
```

This will try to establish a direct connection using the local and wireguard IP addresses and fallback to the relay if not possible.

### Conclusion

With these configuration changes, Syncthing no longer relies on public discovery and relay servers and instead makes use of your own relay server.

This helps improve privacy and perhaps even efficiency as well! If you run into any troubles during this configuration let me know and I can expand upon this post.

