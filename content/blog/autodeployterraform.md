---
title: "Automatic Deployments with Terraform"
date: 2020-05-08T22:45:18-04:00
draft: false
tags: ["Deployment"]
medium_enabled: true
---

I have recently written about [Packer](/blog/snapshotswithpacker/) to create system images or snapshots. This post will go over another [HashiCorp](https://www.hashicorp.com/) project named [Terraform](https://www.terraform.io/) that we can use to deploy that image to a VPS. Like before, I am going to go over how to setup this up in DigitalOcean. Check out [this list](https://www.terraform.io/docs/providers/index.html) for documentation on your favorite cloud provider.

## Variables

To protect against committing secrets like API keys, we're going to create a file that only stores variables. For it to be loaded automatically, it needs to be named `terraform.tfvars`. Here is an example configuration:

```
region = "nyc3"
size = "512mb"
domain = "example.com"
subdomain = "temp"

# Secrets
do_token = "DO-TOKEN-HERE"
key_name = "SSH-KEY-NAME-ON-DO"
```

Now to define the variables in HCL, we need to create a separate `variables.tf` file defining their types

```
variable "do_token" {
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

## Configuration

Now let's create a file called `do.tf`.  We need to start off by stating which provider we are using

```
provider "digitalocean" {
    token = var.do_token
}
```

If you want to hook up your SSH key, then we need to query the Digital Ocean API for its ID.

```
data "digitalocean_ssh_key" laptop {
    name = var.key_name
}
```

We need to also query the API for the packer snapshot we created. Replace this with any standard image like `"ubuntu-20-04-x64"` if you don't want to use a snapshot.

```
data "digitalocean_droplet_snapshot" "packer_snapshot" {
    name = "packer-example"
    most_recent = true
}
```

Now we can create the droplet

```
resource "digitalocean_droplet" "web" {
    name = "tf-1"
    image = data.digitalocean_droplet_snapshot.packer_snapshot.id
    region = var.region
    size = var.size
    ssh_keys = [data.digitalocean_ssh_key.laptop.id]
    backups = false
}
```

Attach a domain to the droplet

```
resource "digitalocean_record" "www" {
  domain = var.domain
  type   = "A"
  name   = var.subdomain
  value  = digitalocean_droplet.web.ipv4_address
}
```

Output useful pieces of information like the new system's IP address and the domain

```
output "ip" {
    value = digitalocean_droplet.web.ipv4_address
}

output "domain" {
    value = "${digitalocean_record.www.name}.${digitalocean_record.www.domain}"
}
```

The whole configuration file for your convenience:

```
provider "digitalocean" {
    token = var.do_token
}

data "digitalocean_ssh_key" laptop {
    name = var.key_name
}

data "digitalocean_droplet_snapshot" "packer_snapshot" {
    name = "packer-example"
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

# Deploy

Check if your configuration is valid

```bash
terraform plan
```

Deploy!

```bash
terraform apply
```

Take down when done

```bash
terraform destroy
```

