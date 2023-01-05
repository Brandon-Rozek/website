---
title: "Neovim Plugins"
date: 2020-03-23T22:52:19-04:00
draft: false
tags: []
medium_enabled: true
---

I decided to switch to [`neovim`](https://neovim.io/) recently and that resulted in having to redo my setup. This post will describe how to setup plugins with `vim-plug`.

First install neovim

```bash
sudo apt install neovim
```

Next, setup the `vim-plug` manager

```bash
curl \
  -fLo ~/.local/share/nvim/site/autoload/plug.vim \
  --create-dirs https://raw.githubusercontent.com/junegunn/vim-plug/master/plug.vim
```

Then, you can load your favorite plugins inside of `~/.config/nvim/init.vim`

```vim
"" Plugins Section
call plug#begin()
Plug 'airblade/vim-gitgutter' " Git Integration
Plug 'junegunn/fzf' " Fuzzy Finder
Plug 'vim-airline/vim-airline' " Status Line
Plug 'dense-analysis/ale' " Async Lint
Plug 'scrooloose/nerdtree' " Directory Tree
call plug#end()

map <C-o> :NERDTreeToggle<CR>
```

Finally, enter `vim` and type `:PlugInstall` to install all the plugins listed.
