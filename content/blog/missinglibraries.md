---
title: "Missing Libraries"
date: 2020-02-08T20:42:50-05:00
draft: false
images: []
---

The piwheels blog outlined a great [post](https://blog.piwheels.org/how-to-work-out-the-missing-dependencies-for-a-python-package/) on what to do when you are missing shared libraries in Python packages. Though the short of this tip is helpful on its own as well. If you are running any piece of software and its missing a library, try to find the `.so` file related to that package.

Then run `ldd` on that file passing it to grep to filter for not found packages:

```bash
ldd file.so | grep "not found"
```

And if you're on Ubuntu, then you can use `apt-file` to find the related packages.

