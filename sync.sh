#!/usr/bin/env sh
hugo
rsync -Pazc --exclude=*.bak --delete public/ brandonrozek.com:brandonrozek/

