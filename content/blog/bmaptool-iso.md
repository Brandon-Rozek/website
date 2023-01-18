---
title: "Bmaptool: A simpler way to copy ISOs"
date: 2023-01-18T11:08:20-05:00
draft: false
tags: []
math: false
---

Bmaptool is a project created by Intel for creating and copying data using block maps. It's meant to be a simpler, faster, and more reliable tool than `dd`.

From their [GitHub page](https://github.com/intel/bmap-tools):

> - Faster. Depending on various factors, like write speed, image size, how full is the image, and so on, `bmaptool` was 5-7 times faster than `dd` in the Tizen IVI project.
> - Integrity. `bmaptool` verifies data integrity while flashing, which means that possible data corruptions will be noticed immediately.
> - Usability. `bmaptool` can read images directly from the remote server, so users do not have to download images and save them locally.
> - Protects user's data. Unlike `dd`, if you make a mistake and specify a wrong block device name, `bmaptool` will less likely destroy your data because it has protection mechanisms which, for example, prevent `bmaptool` from writing to a mounted block device.

It comes with two commands **create** and **copy**. Create generates the block maps which isn't required to use the application. However, having a bmap will speed up the copying process. The syntax of the copy command is the following

```bash
sudo bmaptool copy SRC DST
```

Let's say that I want to flash the latest Ubuntu ISO to a USB stick located at `/dev/sdX`. As the third bullet point claims, I can easily use the URL as SRC and since we don't have a bmap, we'll have to specify that with the flag `--nobmap`.

```bash
sudo bmaptool copy --nobmap https://releases.ubuntu.com/22.04.1/ubuntu-22.04.1-desktop-amd64.iso /dev/sdX
```

Example run on my desktop:

 ```
 bmaptool: info: no bmap given, copy entire image to '/dev/sdX'
 /
 bmaptool: info: synchronizing '/dev/sdX'
 bmaptool: info: copying time: 3m 7.3s, copying speed 19.5 MiB/sec
 ```

Now if we have the ISO downloaded on our computer, we can take the time to create a bmap for it.

```bash
sudo bmaptool create ubuntu-22.04.1-desktop-amd64.iso > ubuntu-22.04.1-desktop-amd64.bmap
```

A bmap file is a human readable XML file that shows the block map and the checksums for each block.

```xml
<?xml version="1.0" ?>
<!-- This file contains the block map for an image file, which is basically
     a list of useful (mapped) block numbers in the image file. In other words,
     it lists only those blocks which contain data (boot sector, partition
     table, file-system metadata, files, directories, extents, etc). These
     blocks have to be copied to the target device. The other blocks do not
     contain any useful data and do not have to be copied to the target
     device.

     The block map an optimization which allows to copy or flash the image to
     the image quicker than copying of flashing the entire image. This is
     because with bmap less data is copied: <MappedBlocksCount> blocks instead
     of <BlocksCount> blocks.

     Besides the machine-readable data, this file contains useful commentaries
     which contain human-readable information like image size, percentage of
     mapped data, etc.

     The 'version' attribute is the block map file format version in the
     'major.minor' format. The version major number is increased whenever an
     incompatible block map format change is made. The minor number changes
     in case of minor backward-compatible changes. -->

<bmap version="2.0">
    <!-- Image size in bytes: 3.6 GiB -->
    <ImageSize> 3826831360 </ImageSize>

    <!-- Size of a block in bytes -->
    <BlockSize> 4096 </BlockSize>

    <!-- Count of blocks in the image file -->
    <BlocksCount> 934285 </BlocksCount>

    <!-- Count of mapped blocks: 3.6 GiB or 100.0%   -->
    <MappedBlocksCount> 934285 </MappedBlocksCount>

    <!-- Type of checksum used in this file -->
    <ChecksumType> sha256 </ChecksumType>

    <!-- The checksum of this bmap file. When it is calculated, the value of
         the checksum has be zero (all ASCII "0" symbols).  -->
    <BmapFileChecksum> e69f56b4cf11a26fba8700bc66a443a20f667d0d0fe1c2d8028715ac060c402d </BmapFileChecksum>

    <!-- The block map which consists of elements which may either be a
         range of blocks or a single block. The 'chksum' attribute
         (if present) is the checksum of this blocks range. -->
    <BlockMap>
        <Range chksum="c396e956a9f52c418397867d1ea5c0cf1a99a49dcf648b086d2fb762330cc88d"> 0-934284 </Range>
    </BlockMap>
</bmap>
```

Once we have generated the bmap, we can copy the ISO to the device.

```bash
sudo bmaptool copy ubuntu-22.04.1-desktop-amd64.iso /dev/sdX
```

Example run on my desktop:

```
bmaptool: info: discovered bmap file 'ubuntu-22.04.1-desktop-amd64.bmap'
bmaptool: info: block map format version 2.0
bmaptool: info: 934285 blocks of size 4096 (3.6 GiB), mapped 934285 blocks (3.6 GiB or 100.0%)
bmaptool: info: copying image 'ubuntu-22.04.1-desktop-amd64.iso' to block device '/dev/sdX' using bmap file 'ubuntu-22.04.1-desktop-amd64.bmap'
bmaptool: info: 100% copied
bmaptool: info: synchronizing '/dev/sdX'
bmaptool: info: copying time: 2m 49.2s, copying speed 21.6 MiB/sec
```

Recall that the `bmap` generation isn't necessary, as you can pass in the `--nobmap` flag.
