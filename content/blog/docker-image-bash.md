---
title: "Advanced Docker Image Construction with Bash"
date: 2019-12-26T21:01:37-05:00
draft: false
tags: [ "linux", "containers", "bash" ]
---

On current versions of Docker, you can't mount volumes during image construction. This poses an issue for me as I don't want to replicate gigabytes of data already existing on my disk when it won't appear on the final build. Therefore, instead of building an image with a traditional Dockerfile, we're going to use a bash script on a running base image container and export the filesystem to create the image from.

So first run the base image with the mounts that you want

```bash
docker run -v /mnt:/mnt -td --name containername baseimage /bin/bash
```

Then copy whatever `setup` script you have and execute it on the running container

```bash
docker cp setup containername:/setup
docker exec -it containername /setup
```

Once the setup script finalizes, we can export the container filesystem into a file called `image.tar`

```bash
docker export --output="image.tar" containername
```

Once we've exported the filesystem, we can get rid of the existing container

```bash
docker stop containername && docker rm containername
```

Now create a `Dockerfile` with the following:

```dockerfile
FROM scratch
ADD image.tar /
CMD ["bin/bash"]
```

Now you can create the image by building the Dockerfile

```bash
docker build -t finalimagename .
```

