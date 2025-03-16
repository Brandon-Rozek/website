#!/usr/bin/env sh
rsync -Pazc --exclude=*.bak --delete public/ build@Rozek-Fog:brandonrozek/

