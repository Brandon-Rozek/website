---
title: "Shared Packer & Terraform Config"
date: 2020-05-08T22:59:30-04:00
draft: false
tags: ["Deployment"]
medium_enabled: true
---

You might have noticed from my last two posts on [Packer](/blog/snapshotswithpacker/) and [Terraform](/blog/autodeployterraform/) that the configuration files are highly similar. In fact, we can trick them into sharing a configuration file!

## Shared Configuration

First let's create a file we'll call `config` that contains all our assignments. Here is an example configuration:

```
base_system_image = "ubuntu-20-04-x64"
region = "nyc3"
size = "512mb"
domain = "example.com"
subdomain = "temp"

# Secrets
do_token = "DO-TOKEN-HERE"
key_name = "KEY-NAME-ON-DO"
```

Then we'll create a file named `variables.hcl` that contains the type definitions

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

Now to trick Packer into reading the configuration files we need to:

- map `variables.auto.pkrvars.hcl` to `config`
- map `variables.pkr.hcl` to `variables.hcl`

We can do this with symbolic links

```bash
ln -s config variables.auto.pkrvars.hcl
ln -s variables.hcl variables.pkr.hcl
```

## Terraform

To trick Terraform into reading the configuration files we need to:

- map `terraform.tfvars ` to `config`
- map `variables.tf` to `variables.hcl`

As before, we can do this with symbolic links

```bash
ln -s config terraform.tfvars
ln -s variables.hcl variables.tf
```

