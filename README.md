# BrandonRozek.com
Github Repo of Personal Website

## Instructions

In order to build the site you need to have `hugo` and `git` installed.

Clone the repository
```bash
git clone --recurse-submodules https://github.com/Brandon-Rozek/website
```
If you don't include `--recurse-submodules` then the theme won't load rendering the site unusable.

This repository uses Git-LFS to store some of the static assets. 
```bash
git lfs fetch
git lfs checkout
```

Then you need to build the site
```bash
cd website
hugo
```
All of the HTML files generated will appear in the folder `Public`. You can then copy this folder over to a webserver.

If you want to run the website locally, then run
```bash
hugo serve
```
This will start a webserver that hosts the site using a port (usually 1313) on your localhost.
