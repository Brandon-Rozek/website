#!/usr/bin/env sh
rsync -Pazc --exclude=*.bak --delete public/ build@Rozek-Cloud:brandonrozek/
rsync -Pazc --exclude=*.bak --delete public/ build@Rozek-Stratus:brandonrozek/
