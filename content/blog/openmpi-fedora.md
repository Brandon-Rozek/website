---
date: 2022-05-03 00:52:38-04:00
draft: false
math: false
medium_enabled: true
medium_post_id: 1c0c98b99e8a
tags:
- Fedora
title: OpenMPI on Fedora
---

To use use the OpenMPI compilers (mpicc, mpic++, etc.) and mpirun
on Fedora, you'll need to install the openmpi package as well
as set up the envionrment paths correctly.

To install:
```bash
sudo dnf install openmpi openmpi-devel
```

Then to set up the environmental variables correctly
so that PATH is set. You'll need to use the
[environment modules](https://modules.readthedocs.io/en/latest/)
program installed by default on Fedora. First, you'll
need to source it:
```bash
source /etc/profile.d/modules.sh
```

Now you can load in the OpenMPI module
```bash
module load mpi/openmpi-x86_64
```

Finally, with these changes you can use the compiler
tools and runner. Do note that you'll have to source
and load the OpenMPI module for every shell you open
unless you add it within `$HOME/.bashrc`.