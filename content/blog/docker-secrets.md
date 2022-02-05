---
title: "Docker Secrets"
date: 2022-02-04T23:59:13-05:00
draft: false
tags: []
math: false
---

I try to keep secrets such as passwords and keys out in their own separate files so that I can `.gitignore` them and commit the rest of my configuration. With `docker-compose` we can do that with the `env_file` field. Here is an example with a postgres configuration:

```yaml
database:
  image: postgres:13.4
  container_name: database
  hostname: database
  env_file:
    - Volumes/database/docker.env
  volumes:
    - Volumes/database/var/lib/postgresql/data:/var/lib/postgresql/data
```

Then in `Volumes/database/docker.env` I can have a file with the secrets as key-value pairs:

```yaml
POSTGRES_USER=user
POSTGRES_PASSWORD=389ed93045c84cc0828c4310e6ef76ce
POSTGRES_DB=database
```

