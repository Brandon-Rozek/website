---
title: "Snapshot Creation with Packer"
date: 2020-05-08T22:31:40-04:00
draft: false
tags: []
medium_enabled: true
---

[Packer](https://www.packer.io/) is a tool to create automated machine images in both local virtual machine / container environments, as well as a variety of cloud platforms. My current cloud platform of choice is [Digital Ocean](https://www.digitalocean.com/), so this post will explain how to set up Packer with it. Though you can likely find your platform of choice on their [docs](https://www.packer.io/docs/builders/) page

In this post I am going to use the beta configuration language of HCL2. This requires a Packer version of at least 1.5.

## Variables

First let us set up a variables file which we will later reference. This makes it easy to keep your main Packer configuration files in Git, while not committing your API key.

Create a file called `variables.auto.pkrvars.hcl`. Here is some example variables and values that I put in mine.

```
base_system_image = "ubuntu-20-04-x64"
region = "nyc3"
size = "512mb"
do_token = "DOTOKENHERE" # Secret
```

Then we need to create `variables.pkr.hcl` that define the types of each of these variables

```
variable "do_token" {
  type = string
}

variable "base_system_image" {
  type = string
}

variable "region" {
  type = string
}

variable "size" {
  type = string
}
```

## Provisioning

Once the system is up and running we can use a [variety of tools](https://www.packer.io/docs/provisioners/) that setup the image.

- Ansible
- Chef
- Powershell
- etc.

I'll use a simple bash script as an example

```bash
#!/bin/bash
apt update
apt upgrade -y
```

## Piecing it together

Finally let us create a `do.pkr.hcl` file that contains the following information

```
source "digitalocean" "web" {
  api_token = var.do_token
  image = var.base_system_image
  region = var.region
  size = var.size
  ssh_username = "root"
  snapshot_name = "packer-example"
}


build {
  sources = [
    "source.digitalocean.web",
  ]

  provisioner "shell" {
    scripts = [ "setup.sh" ]
  }
}
```

Assuming all the files we've just created are in the same directory, Packer will automatically recognize where the value for `var.do_token` lives. We can then run packer to build the image

```bash
packer build .
```

This sets up a snapshot called `packer-example` which we can later spin up and use! Keep in mind that it does a small amount of money to store images on DigitalOcean. 

