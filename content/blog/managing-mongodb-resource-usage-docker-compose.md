---
title: "Limiting MongoDB Resource Usage within Docker Compose"
date: 2023-09-19T16:08:41-04:00
draft: false
tags:
  - Containers
math: false
medium_enabled: false
---

*Warning: This technique does not work for the older Docker Compose v3*

One of my web services utilizes MongoDB as the database backend. It lives on one of the smaller sized virtual private servers with only 1GB of RAM and 1 CPU. Every so often I encounter a scenario where MongoDB is taking all of the sytem resources, so I started looking into how to limit it.

First, we can set some limits to container in general within docker-compose.

Example:

```yml
mongo:
  image: docker.io/mongo:5.0
  mem_limit: 256m
  cpus: 0.25
```

This says that the mongo container can only use a maximum of 256MB of memory and can only use up to 25% of one CPU. 

To see a detailed list of possible options, check out the [docker documentation](https://docs.docker.com/config/containers/resource_constraints/).

Keep in mind that your memory and CPUs are not virtualized, therefore the container can see all the resources available, it just cannot request them.

This may lead to some problems depending on the codebase. For example, in [MongoDB](https://www.mongodb.com/docs/manual/reference/configuration-options/#mongodb-setting-storage.wiredTiger.engineConfig.cacheSizeGB) the WiredTiger internal cache is by default set to 50% of the total amount of RAM minus 1GB.

Luckily we can change this default, by adding a flag within the docker-compose file.

```yml
mongo:
  image: docker.io/mongo:5.0
  mem_limit: 256m
  cpus: 0.25
  command: --wiredTigerCacheSizeGB 0.25
```

The `wiredTigerCacheSizeGB` takes values between `0.25` GB and `10000` GB.

