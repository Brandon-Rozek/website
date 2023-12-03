---
title: "Setting up unprivileged containers with LXC on Fedora 38"
date: 2023-12-03T10:21:41-05:00
draft: false
tags: []
math: false
medium_enabled: false
---

LXC is a containerization technology that allows us to create *system containers*. We can set it up so that we can SSH into a container and perform many of the same tasks we would on a regular Linux box. I currently have two uses cases for this.

First, these system containers allows me to follow instruction documentation for projects that do not treat docker/podman as a first class distribution method. Maybe the project relies on being able to access `systemd`, or perhaps I don't want the additional burden of ensuring the upgrade path of a custom docker-based method.

Second, it allows me to provide a lightweight virtualized environment for my friends and family. With this approach, we don't have to set caps on the amount of CPU and memory usage from the start (as opposed to a VM), and instead impose them later if others are violating fair use.

In this guide, we'll focus on setting up unprivileged containers. These are containers that are started up and maintained by a user other than `root`.

This technology is moving fast. It's likely that this guide will be out of date by the time you're reading this. I do hope, however, that this can serve a as a good jumping off point for other queries.

## Setup

First, let's install `lxc`

```bash
sudo dnf install lxc lxc-templates
```

To setup networking for our containers, we'll also need to install `dnsmasq`.

```bash
sudo dnf install dnsmasq
```

We now need to tell LXC that our user is allowed to create a certain number of network devices on our `lxcbr0` bridge that LXC configures for us.

```bash
echo $(id -un) veth lxcbr0 50 | sudo tee -a /etc/lxc/lxc-usernet
```

I can't imagine myself creating more than 50 system containers, but do adjust that number as you see fit.

The last command we'll need to run as root on the host system is to enable and start the `lxc-net` service.

```bash
sudo systemctl enable --now lxc-net
```

For our user on the host, we need to setup the LXC configuration file. Here, we're going to map the user UID/GIDs into our container.

This set of commands were taken from [LXC getting started](https://linuxcontainers.org/lxc/getting-started/).

```bash
mkdir -p ~/.config/lxc
cp /etc/lxc/default.conf ~/.config/lxc/default.conf
MS_UID="$(grep "$(id -un)" /etc/subuid  | cut -d : -f 2)"
ME_UID="$(grep "$(id -un)" /etc/subuid  | cut -d : -f 3)"
MS_GID="$(grep "$(id -un)" /etc/subgid  | cut -d : -f 2)"
ME_GID="$(grep "$(id -un)" /etc/subgid  | cut -d : -f 3)"
echo "lxc.idmap = u 0 $MS_UID $ME_UID" >> ~/.config/lxc/default.conf
echo "lxc.idmap = g 0 $MS_GID $ME_GID" >> ~/.config/lxc/default.conf
```

Now we can download and create our container.

```bash
systemd-run --unit=my-unit --user --scope -p "Delegate=yes" -- lxc-create -t download -n test
```

At the time of writing, we unfortunately have to wrap the `lxc-create` command within a `systemd-run` because of a semi-recent change in how `cgroups` work.

After running that command, you should see a large table of distributions and questions about which one to choose. Of course this is personal preference, but I selected `ubuntu jammy amd64`. 

Once downloaded, we can then start our container.

```bash
systemd-run --unit=my-unit --user --scope -p "Delegate=yes" -- lxc-start test
```

If we see an error message here, then we can add a log file to check for details.

```bash
systemd-run --unit=my-unit --user --scope -p "Delegate=yes" -- lxc-start test --logfile=~/lxc.log
```

The error I commonly saw when setting this up was:

```
lxc-start test 20231130034412.168 ERROR    start - start.c:print_top_failing_dir:99 - Permission denied - Could not access /home/brandon. Please grant it x access, or add an ACL for the container root
```

This means we need to give `$MS_UID` access to open the `/home/brandon` folder. Though what it's really trying to do is access `/home/brandon/.local/share/lxc` for it's `rootfs` and `config`.

```bash
setfacl -m u:$MS_UID:x /home/rozek
```

Then try running the `lxc-start` command from before again. Sometimes when setting this up it worked from here, other times it wanted me to add the `+x` permission to other folders.

If you run it and don't see a bunch of errors, then it's hopefully a success! Check that it's running:

```bash
[brandon@host ~]$ lxc-ls --fancy
NAME      STATE   AUTOSTART GROUPS IPV4       IPV6 UNPRIVILEGED 
test      RUNNING 0         -      10.0.3.43  -    true   
```

We can then attach to our container to get a shell within it.

```bash
lxc-attach test
```

If the above command doesn't work, you might need to wrap it in a `systemd-run`

```bash
systemd-run --unit=my-unit2 --user --scope -p "Delegate=yes" -- lxc-attach test
```

## Auto-starting LXC containers at boot

When we start a container with the `systemd-run` command, it's tied to that particular terminal session. If we want to start these containers when the machine boots up, we can rely on `systemd`.

First let's create a service file under `~/.config/systemd/user/lxc@.service`

```ini
[Unit]
Description=Start LXC container
After=lxc-net.service
Wants=lxc-net.service

[Service]
Type=oneshot
Delegate=yes
RemainAfterExit=yes
ExecStart=/usr/bin/lxc-start %i
ExecStop=/usr/bin/lxc-stop %i
TimeoutStartSec=0

[Install]
WantedBy=default.target
```

Then we can start our test container

```bash
systemctl --user start lxc@test
```

Enable it on bootup

```bash
systemctl --user enable lxc@test
```

Since this is a user service, we need to make sure linger is on for it to respect
the enable on boot setting.

```bash
sudo loginctl enable-linger rozek
```

## Other Resources

https://linuxcontainers.org/lxc/getting-started/

https://www.redhat.com/sysadmin/exploring-containers-lxc

https://wiki.archlinux.org/title/Linux_Containers
