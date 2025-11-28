---
title: "Fedora CoreOS: First Impressions"
date: 2025-11-28T10:47:11-05:00
draft: false
tags: []
math: false
medium_enabled: false
---

I have a VPS whose contract ends in December. Instead of renewing, I decided to switch providers of that VPS to OVHCloud. The latter's commitment to [sustainability](https://corporate.ovhcloud.com/en/sustainability/environment/) through renewables and component reuse is super cool. Now, I could've kept the migration simple and keep the configuration the same. I don't write about it much here, but I have [Ansible](https://www.redhat.com/en/ansible-collaborative) playbooks for all my servers. However, [immutable Linux distributions](https://www.zdnet.com/article/what-is-immutable-linux-heres-why-youd-run-an-immutable-linux-distro/) have been receiving a lot of attention over the past few years and tragically I knew little about them.

**What is an immutable Linux distribution?** It is a Linux distribution with a read-only core. This prevents accidental modifications which overtime lead to an unstable system. 

There are [many](https://nixos.org/) [different](https://ubuntu.com/core) [options](https://microos.opensuse.org/) for these immutable distributions, but as you can see from the title of this post, I went with [Fedora CoreOS](https://www.fedoraproject.org/coreos/). The reason is simple. All my other servers run Fedora Server, so hopefully the changes I need to make to my playbooks are minimal.

At the time of writing, Fedore CoreOS uses [OSTree](https://ostreedev.github.io/ostree/introduction/) to perform upgrades over the entire filesystem. These upgrades are *atomic* which suggests that we are not updating individual packages but the entire Linux distribution as a whole. Apart from the read-only core, there are two writable directories `/etc` and `/var`. In fact, your home directory lives in `/var/home`.

## Initial Installation

OVHCloud does not have a way to upload an ISO and boot directly from there. Instead, we'll have to use their rescue mode feature. Luckily, Timothée wrote up a [great guide](https://tim.siosm.fr/blog/2025/09/14/fedora-coreos-ovhcloud-vps/) on how to get started. If this doesn't exactly match your situation, the [official documentation](https://docs.fedoraproject.org/en-US/fedora-coreos/getting-started/) has over 20 different provisioning guides.

When I was following the documentation, one of the parts I got tripped up on was how much configuration to put in my Butane file. As noted above, I already have Ansible setup to copy over various files I need. Then I saw that *ignition runs only once during the first boot of the system*. Hence, if we wanted to customize our storage partitions or lay out networking, then this is a good place to do this. Otherwise, if we want to setup `systemd` services and the like, we can always add those via Ansible later.

In other words, if you're fine with the defaults and there's a DHCP server running on your network, then the  *base Butane config outlined in the documentation is sufficient*.

From the official documentation:

```yaml
variant: fcos
version: 1.6.0
passwd:
  users:
    - name: core
      ssh_authorized_keys:
        - ssh-rsa AAAA...
```

Where you replace the `ssh-rsa` line with your own SSH public key file.

## Running Software

For the most part, using OSTree to install additional packages is [highly discouraged](https://docs.fedoraproject.org/en-US/fedora-coreos/faq/#_how_do_i_run_custom_applications_on_fedora_coreos). Instead, it's suggested to install and run things through [containers](https://docs.fedoraproject.org/en-US/fedora-coreos/running-containers/). The official documentation shows how to set up containers via the Butane configuration above, however, I kept my file as simple as shown above.  Instead since `/etc/containers/systemd` is writable, I wrote [Podman Quadlet files](https://brandonrozek.com/blog/migrating-docker-compose-podman-quadlets/) directly ([Official Quadlet Documentation](https://docs.podman.io/en/latest/markdown/podman-systemd.unit.5.html)). 

For example, here is my Wireguard Quadlet file

```ini
[Unit]
Description=WireGuard VPN Container
After=network-online.target
Wants=network-online.target

[Container]
Image=docker.io/linuxserver/wireguard:latest
ContainerName=wireguard

# Give the container the ability to add network interfaces
AddCapability=NET_ADMIN

# Have the wireguard network accessible on the host
Network=host

# Mount the WireGuard configuration directory
Volume=/etc/wireguard:/config/wg_confs:Z

[Service]
Restart=always
TimeoutStartSec=900

[Install]
WantedBy=multi-user.target default.target
```

The following are my Ansible tasks which copy that file over to the machine.

```yaml
- name: Create /etc/wireguard directory
  become: true
  ansible.builtin.file:
    path: /etc/wireguard
    state: directory
    mode: '0700'
    owner: root
    group: root

- name: Copy Quadlet container file
  become: true
  ansible.builtin.copy:
    src: etc/containers/systemd/wireguard.container
    dest: /etc/containers/systemd/wireguard.container
    mode: '0644'
    owner: root
    group: root
  register: wireguardcontainer

- name: Reload systemd daemon to pick up Quadlet
  become: true
  ansible.builtin.systemd:
    daemon_reload: yes
  when: wireguardcontainer.changed
```

Now not everything deserves a spot in `/etc/containers/systemd`. Take `fastfetch` for example.

```txt
             .',;::::;,'.                 core@toolbx
         .';:cccccccccccc:;,.             ------------
      .;cccccccccccccccccccccc;.          OS: Fedora Linux 43 (Toolbx Container Image) x86_64
    .:cccccccccccccccccccccccccc:.        Host: OpenStack Nova (19.3.2)
  .;ccccccccccccc;.:dddl:.;ccccccc;.      Kernel: Linux 6.17.1-300.fc43.x86_64
 .:ccccccccccccc;OWMKOOXMWd;ccccccc:.     Uptime: 22 hours, 16 mins
.:ccccccccccccc;KMMc;cc;xMMc;ccccccc:.    Packages: 366 (rpm)
,cccccccccccccc;MMM.;cc;;WW:;cccccccc,    Shell: bash 5.3.0
:cccccccccccccc;MMM.;cccccccccccccccc:    Terminal: conmon
:ccccccc;oxOOOo;MMM000k.;cccccccccccc:    CPU: 6 x Intel Core (Haswell, no TSX) (6) @ 2.99 GHz
cccccc;0MMKxdd:;MMMkddc.;cccccccccccc;    GPU: Cirrus Logic GD 5446
ccccc;XMO';cccc;MMM.;cccccccccccccccc'    Memory: 920.56 MiB / 11.39 GiB (8%)
ccccc;MMo;ccccc;MMW.;ccccccccccccccc;     Swap: Disabled
ccccc;0MNc.ccc.xMMd;ccccccccccccccc;      Disk (/): 11.53 GiB / 99.44 GiB (12%) - overlay
cccccc;dNMWXXXWM0:;cccccccccccccc:,       Disk (/run/host/boot): 277.41 MiB / 349.87 MiB (79%) - ext4 [Read-only]
cccccccc;.:odl:.;cccccccccccccc:,.        Disk (/run/host/etc): 11.53 GiB / 99.44 GiB (12%) - xfs
ccccccccccccccccccccccccccccc:'.          
:ccccccccccccccccccccccc:;,..             
 ':cccccccccccccccc::;,.

```

All it does it displays system information. Now this is a very important task when showing off your system on Reddit, but it's more of a *system administration* tool than a software service that your server provides. For these types of tools, we can use `toolbox`.

```bash
toolbox create # Run this once
toolbox enter
```

This will give us a new prompt:

```
⬢ [core@toolbx ~]$
```

From here, we can use `dnf` and treat it similarly as a mutable Fedora server machine.

```bash
sudo dnf install fastfetch
```

Now you'll notice that by default it mounts your home directory but the `/etc` and `/var` directories are those of the container. We can find all the files in the host system by accessing `/run/host`.

I use this when trying to view my Nginx logs:

```bash
goaccess /run/host/var/log/nginx/access.log
```

## System Security

A huge benefit to running all your services via Quadlets is that Podman is able to automatically set the SELinux contexts and configure your firewall rules for you. This means that we don't have to manually change the SELinux context of every file with `chcon`. If you're lazy, this means hopefully we don't have to disable SELinux!

**SELinux:** Notice in my Wireguard Quadlet file I had the following

```ini
Volume=/etc/wireguard:/config/wg_confs:Z
```

The part after `wg_confs:` is an optional comma-separated list of options. Here are some that I found to be particularly relevant:

| Option | Description                                                  |
| ------ | ------------------------------------------------------------ |
| `Z`    | Label the content with a private unshared SELinux label.     |
| `z`    | Label the content with a shared SELinux content label so that two or more containers can access it. |
| `U`    | Recursively change the owner and group of the source volume based on the UID and GID of the container |
| `ro`   | The container can only read, not write to the volume         |

**NFTables:** My other Fedora server systems use `firewalld` as the primary way I interface with the firewall. Instead of using a CLI tool, the idea is that we edit `/etc/sysconfig/nftables.conf` with the rules we want. I'm still getting used writing my firewall config this way, but I do like how it's all easily viewable in one place.

Here's a version of what I have:

```nftables
#!/usr/sbin/nft -f

# Define the main table
table inet filter {
    
    # Data structure we'll use to keep track of rate-limiting
    set ssh_ratelimit {
        type ipv4_addr
        size 65536
        flags dynamic,timeout
        timeout 30s
    }

    chain input {
        type filter hook input priority filter; policy drop;

        # Allow loopback
        iif lo accept

        # Allow established/related connections
        ct state established,related accept

        # Allow ICMP (ping, etc)
        ip protocol icmp accept
        ip6 nexthdr icmpv6 accept

        # SSH with rate limiting
        tcp dport 22 ct state new limit rate over 12/minute burst 6 packets drop
        tcp dport 22 accept

        # Allow HTTP and HTTPS
        tcp dport { 80, 443 } accept

        # Drop everything else
        drop
    }

    chain forward {
        type filter hook forward priority filter; policy drop;
        
        # Allow established/related connections
        ct state established,related accept
    }

    chain output {
    	# Allow outgoing connections
        type filter hook output priority filter; policy accept;
    }
}
```

I won't go into detail how NFTables works here. Notice though how we don't specify anything about the Podman network. As I said before, Podman will automatically handle that for us.

However, what Podman won't automatically handle is if we try to change our NFTables configuration without a reboot. This is because reloading NFTables will *wipe the existing configuration*. As such, we need to manually invoke Podman to regenerate the rules.

Luckily, we can override the NFTables systemd service so that it happens automatically. Create the file `/etc/systemd/system/nftables.service.d/override.conf` with the following:

```ini
[Service]
ExecStartPost=podman network reload --all
ExecReload=podman network reload --all
```

## Conclusion

That wraps up the bits and pieces I had to learn while I was setting my machine up. From there, I've been running my CoreOS machine for a month and have not yet had any issues. It's too early for me to make any grand claims, but it *feels* incredibly reliable.

By default, updates are automatic. Since these are atomic, it means that the machine reboots regularly to apply these updates. This encourages us to setup everything to survive reboots and not require any manual intervention. Also, boot times are quick with it clocking under 12 seconds for my VPS.

Running everything in containers provides isolation between these services and the host. This is useful of course for security, but also allows everything to update on their own cadence and not conflict.

Overall, using an immutable distribution is different than traditional Linux server management. However hopefully with this setup, it incentivizes us to create less fragile systems. A community of maintainers will keep the stable read-only core in a great state, and if things go wrong, we can copy our container volumes to another machine.

So if you haven't already, I recommend giving Fedora CoreOS a shot. Next, I have to take a look at how it's like using an immutable distribution on a desktop.
