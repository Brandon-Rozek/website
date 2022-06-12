---
title: "Deploying Binaries to other Linux Distros using Appimage"
date: 2020-10-19T21:53:52-04:00
draft: false
tags: ["Packaging"]
---

One way to distribute to different Linux distributions is to compile the source under each of them and distribute it separately.  This can be a pain to manage if you target multiple distributions and multiple versions of those distributions. Instead, let's take a look at AppImage. This allows us to package up our binaries and shared libraries under one file which we can distribute.

![AppImage Architecture Diagram](/files/images/blog/appimage-architecture-overview.svg)

Source: https://docs.appimage.org/reference/architecture.html

It works by packaging up the application in a SquashFS which is then mounted during runtime using FUSE. The project recommends that the AppImage is packaged on an older system, like an Ubuntu LTS or CentOS. Newer systems are often backwards compatible but not the other way around. Let's get started!

## Setting up the AppImage

Let's create an AppImage based on the application Gqrx. The following structure will be common for all binary distribution packages:

```
gqrx.AppDir/
  AppRun
  icon.png
  gqrx.desktop
  usr/
    bin/
      gqrx
    etc/
      # Config files
    lib/
      # Shared libraries
```

The `AppRun` executable comes from the [AppImage Releases Page](https://github.com/AppImage/AppImageKit/releases). While you're there, you should also download `appimagetool` as we'll be using that soon.

The `.desktop` file needs to be a valid [Linux Desktop Icon](https://brandonrozek.com/blog/linuxdesktopicons/). Some things to take note about the desktop file:

- The icon is assumed to be a `.png`
- The executable is assumed to be located in `/usr/bin/`
- Make sure to define the [`Categories`](https://specifications.freedesktop.org/menu-spec/latest/apa.html) field, the `appimagetool` complained when I didn't.

Here is an example desktop file.

```
[Desktop Entry]
Type=Application
Name=Gqrx
Icon=icon
Exec=gqrx
Categories=Development;
```

Copy over `gqrx` executable over to the AppDir:

```bash
export gqrx_loc=$(which gqrx)
cp $gqrx_loc gqrx.AppDir/usr/bin/
```

### Finding Needed Shared Libraries

This part is the most time consuming of this whole process. Most of the shared libraries that the application depends on needs to be added to the `usr/lib` folder. Except for the lowest level libraries. 

Let's first take a look at all the libraries we need:

```bash
export all_libraries=$(ldd $gqrx_loc | awk '{ print $1 }')
echo $all_libraries
```

Then let's grab the [`excludelist` from AppImage](https://raw.githubusercontent.com/AppImage/pkg2appimage/master/excludelist):

```bash
wget https://raw.githubusercontent.com/AppImage/pkg2appimage/master/excludelist
```

Now let's filter our library output to take away the lowest level libraries:

```bash
export filtered_libraries=$(echo $all_libraries | grep -vwf excludelist)
echo $filtered_libraries
```

If this filter doesn't work, then you might need to make sure each library is listed on its own line.

Finally, let's save the locations of these libraries to `library_locations.txt`

```bash
ldd $gqrx_loc | grep $filtered_libraries | awk '{ print $3 }' > library_locations.txt
cat library_locations.txt
```

Copy over all the libraries

```bash
xargs -a library_locations.txt -L 1 -I @ cp @ gqrx.AppDir/usr/lib/
```

If there are any libraries that you need get dynamically injected during runtime, you will have to copy those over as well.

For those using Qt plugins, those live within the `/usr/bin` directory. For example `libqxcb.so` lives in `/usr/bin/platforms/libqxcb.so`.

### Creating the AppImage

Finally we can use the `appimagetool` command to create the AppImage:

```bash
./appimagetool-x86_64.AppImage gqrx.AppDir/
```

Which will generate a `gqrx-appimage-x86_64.AppImage` file.

Now for the moment of true, copy that file over to another Linux distribution and see if it executes appropriately.  If it complains about shared libraries missing, then you should go back to the previous system and add that library in.

If it complains about Illegal instructions, then there is probably either a low level library that needs to be removed, or the CPU instruction set between the two computers differ.