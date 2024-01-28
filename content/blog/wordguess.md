---
title: "Wordguess: A game for the Tildeverse"
date: 2024-01-28T18:40:00-05:00
draft: false
tags: []
math: false
medium_enabled: false
---

The [Tildeverse](/blog/tildeverse/) is a collection of online communities that allows people to create user accounts on public unix machines (pubnixes). Often this is to create websites, however, one component that I think deserves additional attention is the creation of games for these communities.

Three games that are featured in the message-of-the-day in Tilde.club are:

- [Botany](https://tildegit.org/team/botany): Plant raising game where players can help water each other's plants
- [Asciifarm](https://github.com/jmdejong/asciifarm): Multiplayer farming/fighting game
- [Dungeon Crawl Stone Soup](http://crawl.develz.org/): Rouge-like dungeon adventure

These games are designed to be multiplayer, but it doesn't need to in order to be a social game. A large example of this recently, is the game Wordle.

Wordle is designed to be played by oneself. A challenge is issued once a day, and the player gets a score based on their performance. The players can then compare the scores with each other and strive to beat each other on future days.

WordGuess is a Wordle inspired game I made designed to run on a pubnix. It relies on the Linux permission system to authenticate players and keeps a leaderboard showing players scores for each of the days.

Below is how it looks like for a player to SSH into the pubnix and play the game:

![Gameplay of WordGuess](/files/images/blog/wordguess.svg)

For those on the [Tilde.club](https://tilde.club/) server, it's already setup and ready to play. Run the following command to start:

```bash
python /home/brozek/WordGuess/client.py
```

After playing the game you're welcome to see the scores of others that day:

```bash
python /home/brozek/WordGuess/leaderboard.py
```

If you're not on Tilde.club. You're welcome to set it up yourself on any Linux server or pubnix. The instructions are listed on the [Github](https://github.com/brandon-rozek/wordguess).



