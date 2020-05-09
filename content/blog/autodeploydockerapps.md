---
title: "Auto-Deploy Docker Applications"
date: 2020-05-09T10:20:34-04:00
draft: false
tags: []
---

This post will combine that last three posts on [Packer](https://brandonrozek.com/blog/snapshotswithpacker/), [Terraform](https://brandonrozek.com/blog/autodeployterraform/), and their [configuration](https://brandonrozek.com/blog/sharedpackerterraformconfig/) to show an entire example of how to deploy a docker-compose application. We will specifically look at deploying a game called [`minetest`](https://www.minetest.net/) on DigitalOcean, but these principles can be adjusted to deploy your application as well. The entire setup is [documented on Github](https://github.com/Brandon-Rozek/minetest-deploy).

## Shared Config

We're going to use a shared configuration between Packer and Terraform. The template goes like this:

```
base_system_image = "ubuntu-20-04-x64"
region = "nyc3"
size = "512mb"
domain = "brandonrozek.com" # Replace
subdomain = "minetest"

# Secrets
do_token = "DO-TOKEN-HERE" # Replace
key_name = "SSH-NAME-ON-DO-HERE" # Replace
```

We'll also need to define the types of these variables in `variables.hcl`

```
variable "do_token" {
  type = string
}

variable "base_system_image" {
  type = string
}

variable "domain" {
  type = string
}

variable "key_name" {
  type = string
}

variable "subdomain" {
  type = string
}

variable "region" {
  type = string
}

variable "size" {
  type = string
}
```

## Packer

Create a packer directory and setup some symbolic links to the share configuration

```bash
mkdir packer && cd packer
ln -s ../config variables.auto.pkrvars.hcl
ln -s ../variables.hcl variables.pkr.hcl
```

Now let's create a script named `setup.sh` that will run on top of our base image. This will install Docker and setup the firewall to allow SSH and Minetest traffic through.

```bash
#!/bin/bash
apt update
apt upgrade -y

apt install -y docker.io docker-compose
systemctl enable docker-compose
systemctl start docker-compose

ufw allow OpenSSH
# Add any firewall rules you need
# for your application here
ufw allow 30000/udp
ufw --force enable
```

The image that we'll use for Minetest comes from [linuxserverio](https://fleet.linuxserver.io/image?name=linuxserver/minetest). To configure docker-compose we'll need a file named `docker-compose.yml`. Its contents will be highly similar to what is listed on their [Github](https://github.com/linuxserver/docker-minetest/blob/466cde1f2fd38278fe69d33ea3b2f42df50e6b16/README.md).

```yml
version: "2.1"
services:
  minetest:
    image: linuxserver/minetest
    container_name: minetest
    environment:
      - PUID=1000
      - PGID=1000
      - TZ=US/Eastern
    volumes:
      - /volumes/minetest/config/.minetest:/config/.minetest
    ports:
      - 30000:30000/udp
    restart: unless-stopped
```

We'll need to create a `systemd` script called `docker-compose.service` for systemd to [enable docker-compose on startup](https://brandonrozek.com/blog/composesystemd/).

```ini
[Unit]
Description=Docker Compose Application Service
Requires=docker.service
After=docker.service

[Service]
Type=oneshot
RemainAfterExit=yes
WorkingDirectory=/root
ExecStart=/usr/bin/docker-compose up -d
ExecStop=/usr/bin/docker-compose down
TimeoutStartSec=0

[Install]
WantedBy=multi-user.target
```

Finally we'll need to write a packer configuration file `do.pkr.hcl` to create our snapshot.

```
source "digitalocean" "web" {
  api_token = var.do_token
  image = var.base_system_image
  region = var.region
  size = var.size
  ssh_username = "root"
  snapshot_name = "packer-docker"
}


build {
  sources = [
    "source.digitalocean.web",
  ]

  provisioner "file" {
    source = "docker-compose.yml"
    destination = "/root/docker-compose.yml"
  }
  
  provisioner "file" {
    source = "docker-compose.service"
    destination = "/etc/systemd/system/docker-compose.service"
  }
  
  provisioner "shell" {
    scripts = [ "setup.sh" ]
  }
}
```

To build our image we need to run `packer build .` in the directory with all these files.

## Terraform

Like before, we need to tell terraform where to look for its configuration

```bash
mkdir terraform && cd terraform
ln -s ../config terraform.tfvars
ln -s ../variables.hcl variables.tf
```

To deploy, we only need to create one additional file that will tell digital ocean to create a droplet and assign a subdomain to that droplet.

```
provider "digitalocean" {
    token = var.do_token
}

data "digitalocean_ssh_key" laptop {
    name = var.key_name
}

data "digitalocean_droplet_snapshot" "packer_snapshot" {
    name = "packer-docker"
    most_recent = true
}

# Create a droplet
resource "digitalocean_droplet" "web" {
    name = "tf-1"
    image = data.digitalocean_droplet_snapshot.packer_snapshot.id
    region = var.region
    size = var.size
    ssh_keys = [data.digitalocean_ssh_key.laptop.id]
    backups = false
}

# Attach a subdomain
resource "digitalocean_record" "www" {
  domain = var.domain
  type   = "A"
  name   = var.subdomain
  value  = digitalocean_droplet.web.ipv4_address
}

output "ip" {
    value = digitalocean_droplet.web.ipv4_address
}

output "domain" {
    value = "${digitalocean_record.www.name}.${digitalocean_record.www.domain}"
}
```

To deploy run

```bash
terraform apply
```

To later take down the minetest server, run

```bash
terraform destroy
```

## Conclusion

This method can be easily configured to run whichever docker services you'd like. All you have to do is edit the `packer/docker.compose.yml` file and `packer/setup.sh` to setup the firewall rules.
