---
title: "Use block storage for your application data"
date: 2023-10-02T23:40:07-04:00
draft: false
tags: []
math: false
medium_enabled: false
---

One day I was upgrading my server from Fedora 37 to 38 and the thought came to my head.

> What if this installation fails and I need to recreate the server?

Luckily that didn't come to pass, but the thought was enough to scare me into learning [Ansible](https://www.ansible.com/).

Honestly, I've been skeptical of it for a while. I thought that having bash automation scripts was good enough and that Ansible will come and go.

Except, that it's been around for the last 11 years...

Consider me converted! My favorite module is [`lineinfile`](https://docs.ansible.com/ansible/latest/collections/ansible/builtin/lineinfile_module.html). It's all too common in Linux for setup instructions to contain "edit x line in y file."

Now, I have Playbooks written for configuring my server, but what about the data?

I was chatting with my good friend Stefano Coronado and he suggested using block volumes. Most VPS providers offer this feature and its persistent data storage that can be attached to one or more servers within the same data center.

This of course does not substitute having good backups, but having separation between configuration and data is a great idea. 

Lets say that I have block storage mounted on `/mnt/storage`.

It's easy to point directly to it within docker-compose:

```yml
database:
  image: docker.io/mongo:5.0
  volumes:
    - /mnt/storage/database/data/db:/data/db
```

If you're using an application outside of docker and is not easily configurable, we can make use of symlinks.

For example, if an application is expecting configuration to be at `/etc/special` then:

```bash
sudo ln -s /mnt/storage/special /etc/special
```

sets up a symlink at `/etc/special` to point at `/mnt/storage/special`.

Learn more on how to specifically setup and mount a block volume depending on your hosting provider:

- [Linode](https://www.linode.com/docs/products/storage/block-storage/)
- [DigitalOcean](https://docs.digitalocean.com/products/volumes/)
- [Vultr](https://www.vultr.com/docs/block-storage)
- [AWS](https://aws.amazon.com/ebs/)
