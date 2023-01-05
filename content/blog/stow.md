---
title: "Stow Version Manager"
date: 2021-02-25T10:31:34-05:00
draft: false
tags: []
medium_enabled: true
---

Suppose you need a newer or specific version of a package that isn't included in your standard linux repo. The standard procedure is to do something like the following...
```bash
git clone https://github.com/brandon-rozek/project.git
cd project
./configure
make
sudo make install
```

Depending on how the package is configured, it will put the executable, configurations, and libraries in `/usr/local/` or other places in your system.

The difficulty comes, when it is time to change versions of the software. Some people include a nice `make uninstall` target which can help you track down which files were installed. Other software packages aren't so convinient. This is where stow comes in. It allows you to easily change between software versions.

How does this work? First let's create a stow directory in `/usr/local`
```bash
sudo mkdir /usr/local/stow
```

Then let's go to the project we want to install and add a flag to configure to tell it where to install
```bash
git clone https://github.com/brandon-rozek/project.git
cd project
./configure --prefix=/usr/local/stow/project-v1
make
sudo make install
```

For cmake based projects...
```bash
git clone https://github.com/brandon-rozek/cmake-project.git
cd cmake-project
mkdir build
cd build
cmake3 -DCMAKE_INSTALL_PREFIX=/usr/local/stow/cmake-project-v1  ..
make
sudo make install
```

Now let's check out the installation directroy
```bash
cd /usr/local/stow/project-v1
ls
```

```
etc
lib
bin
```
You'll notice here that we'll have the same setup as `/usr/local/etc/`, `/usr/local/lib/` and `/usr/local/bin`. That's because when we run `stow` it'll go through and create the appropriate symlinks to the files.

```bash
cd /usr/local/stow
sudo stow project-v1
```

## Stow Flags

Stow will go into the folder and then create the appropriate symlinks relative to the parent directory of stow, which in this case is `/usr/local`. If you don't want it to create the symlinks in the parent directory then you can set the target somewhere else with `--target` or `-t`.

```bash
cd /home/brandon/stow
sudo stow --target /usr/local project-v1
```

If you don't want to `cd` into your stow directory, you can set `--dir` or `-d` to indicate where that is.
```bash
sudo stow --dir /home/brandon/stow --target /usr/local project-v1
```

Summary of Flags (From the Man page)

| Flag           | Description                                                  |
| -------------- | ------------------------------------------------------------ |
| `--no`         | Do not perform any operations that modify the filesystem; merely show what would happen. |
| `--dir=DIR`    | Set the stow directory to "DIR" instead of the current directory.  This  also has the effect of making the default target directory be the parent of "DIR". |
| `--target=DIR` | Set the target directory to "DIR" instead of the parent of the stow  directory. |
| `--stow`       | Stow the packages that follow this option into the target directory. This is the default action and so can be omitted if you are only stowing packages rather than performing a mixture of stow/delete/restow actions. |
| `--delete`     | Unstow the packages that follow this option from the target directory  rather than installing them. |
| `--restow`     | Restow packages (first unstow, then stow again).             |
| `--no-folding` | Disable folding of newly stowed directories when stowing, and refolding  of newly foldable directories when unstowing. |




## Applications


### Switching between versions
This makes changing versions of software really easy.

```bash
cd /usr/local/stow
sudo stow -D project-v1
sudo stow project-v2
```

And like that you've switched versions from 1 to 2!

### Managing dot files

This is also a great way to store dot files for your user directory. Here is an example of what I do:

```
/home/brandon/stow
├── bash
│   └── .bashrc
├── git
│   └── .gitconfig
└── tmux
    └── .tmux.conf
```

## Troubleshooting

If you get a command not found for an executable you know lives in `/usr/local/bin` then it might be because your `PATH` isn't setup to look there.

Inside your `~/.bash_rc`
```bash
export PATH=$PATH:/usr/local/bin
```
