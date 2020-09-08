---
title: "Splitting Files to Circumvent Size Limits"
date: 2020-09-07T20:41:25-04:00
draft: false
tags: []
---

Let's say you want to transfer file(s) over to someone and there is a limit the size you can transfer over. Maybe because of the physical medium or the online service you're using. You can make use of the terminal tool `split` in order to get the chunks over there and then use `cat ` to combine it back to one file.

## Create a Single File

Skip to the next section if you only want to transfer a single file.

Otherwise, let's say you have a folder of files named `Documents`. First, let's create a gzipped compressed archive that contains everything.

```bash
tar -czf documents.tar.gz Documents
```

## Splitting the File

Next let's split the file into 1 GB parts. 

```bash
split -b 1GB -d documents.tar.gz PART
```

Then transfer the files labeled PARTX where X is the part number over....

## Re-combining

Once the files are transfered, we use `cat` to bring the files back together.

```bash
cat PART* > documents.tar.gz
```

