#!/usr/bin/env sh
hugo
rsync -Paz --delete public/ brandonrozek.com:brandonrozek
