---
date: 2022-02-07 17:07:08-05:00
draft: false
math: false
medium_enabled: true
medium_post_id: 95d4bd60af72
tags:
- Git
title: Git Partial Clones
---

I recently was introduced to [Sparse Directories in SVN](https://svnbook.red-bean.com/en/1.8/svn.advanced.sparsedirs.html). In SVN, you can initially clone a repository and have it be empty until you checkout the specific files needed. I wondered if I can do the same with `git`. For the *tl;dr* skip to the conclusion section.

As a benchmark, we're going to reference the size of a cryptographic library I helped author. As a baseline, let's see how big the repository is before adding any flags.

```bash
git clone https://github.com/symcollab/cryptosolve
du -sh cryptosolve
```

```
90M cryptosolve
```

##  Using the `--filter` flag

With the `filter` flag, blobs that fall under a specified criteria do not get automatically downloaded during a clone. The blobs do, however, get downloaded whenever its associated files get checked out. By setting the flag to `blob:none`, we are telling git to not download any files initially. Though since the main branch gets checked out by default during a clone, git will still download the blobs associated with the main branch.

```bash
git clone --filter=blob:none https://github.com/symcollab/cryptosolve
du -sh cryptosolve
```

```
2.1M cryptosolve
```

## Using the `--no-checkout` flag

We can then improve the last command by adding the `no-checkout` flag. This flag will not construct any of the files in the current branch. If you don't include include the filter flag from before, then there really isn't much of a space savings since all the information is stored in the git database.

```bash
git clone --no-checkout https://github.com/symcollab/cryptosolve
du -sh cryptosolve
```

```
89M cryptosolve
```

You can see that there are no files checked out with a `ls -a`.

```
.  ..  .git
```

Though with the filter flag, we can see the space savings!

```bash
git clone \
	--no-checkout \
	--filter=blob:none \
	https://github.com/symcollab/cryptosolve
du -sh cryptosolve
```

```
508K cryptosolve
```

## Using the `--sparse` flag

The sparse flag makes it so that when we checkout a reference, only the immediate files in the root directory are constructed. Additional commands then need to be issued in order to checkout other directories. With the sparse flag by itself, there isn't much savings since all the information is still downloaded and stored in the git database.

```bash
git clone --sparse https://github.com/symcollab/cryptosolve
du -sh cryptosolve
```

```
89M cryptosolve
```

## Conclusion

The power comes from when we combine all these flags together.

```bash
git clone \
	--filter=blob:none \
	--sparse \
	--no-checkout \
	https://github.com/symcollab/cryptosolve
du -sh cryptosolve
```

```
516K cryptosolve
```

It's not different from the `--filter=blob:none --no-checkout` command initially, but when we checkout a branch we can see that not all the blobs get downloaded.

```bash
cd cryptosolve
git checkout main
cd ..
du -sh cryptosolve
```

```
644K cryptosolve
```

You can fetch folders as you please with the following command:

```bash
git sparse-checkout add FOLDERNAME
```

You can even set it so that a specific folder is shown at the root of your directory.

```bash
git sparse-checkout set FOLDERNAME
```