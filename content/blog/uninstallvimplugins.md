---
title: "Uninstall Vim Plugins"
date: 2020-03-23T23:00:00-04:00
draft: false
tags: []
---

Assuming you're using `vim-plug` you might come to the point where you want to uninstall a plugin. Googling around will land you at [a GitHub issue](https://github.com/junegunn/vim-plug/issues/121) where a contributor named Andrea Cedraro states a workaround instead.

- Delete Plug line from `.vimrc` or `~/.config/nvim/init.vim`
- Source the file. e.g `:so .vimrc`
- Call `:PlugClean`

