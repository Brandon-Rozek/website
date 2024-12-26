---
title: "Curl Card"
date: 2024-12-26T09:12:58-05:00
draft: false
tags: []
math: false
medium_enabled: false
---

Browsing around on the Interwebs, I found that [Rahul](https://codingotaku.com/) has a curl card.

```bash
curl https://codingotaku.com/cc
```

```
╔═══════════════════════════════════════════════════════════╗
║                                     )                     ║
║   (        (                     ( /(     )        )      ║
║   )\       )\ ) (        (  (    )\()) ( /(   ) ( /(   (  ║
║ (((_)  (  (()/( )\  (    )\))(  ((_)\  )\()( /( )\()) ))\ ║
║ )\___  )\  ((_)((_) )\ )((_))\    ((_)(_))/)(_)((_)\ /((_)║
║((/ __|((_) _| | (_)_(_/( (()(_)  / _ \| |_((_)_| |(_(_))( ║
║ | (__/ _ / _` | | | ' \)/ _` |  | (_) |  _/ _` | / /| || |║
║  \___\___\__,_| |_|_||_|\__, |   \___/ \__\__,_|_\_\ \_,_|║
║                         |___/                             ║
║                                                           ║
║         -~= free-software = web = anime =~-               ║
║                                                           ║
╠═══════════════════════════════════════════════════════════╣
║                                                           ║
║        ■ Web developer who adore Minimalism ■             ║
║                                                           ║
║     Email:  contact<at>codingotaku<dot>com                ║
║                                                           ║
║       Web:  https://codingotaku.com/                      ║
║                                                           ║
║  Peertube:  https://videos.codingotaku.com/c/codingotaku  ║
║  Mastodon:  https://fosstodon.org/@codingotaku            ║
║  Codeberg:  https://codeberg.org/codingotaku              ║
║                                                           ║
║      Card:  curl -sL https://codingotaku.com/cc           ║
║                                                           ║
╚═══════════════════════════════════════════════════════════╝

```

The black and white rendition here really does not give it justice. Run the command yourself so you can see the wicked colors they use.

Now if you ask me, this is really awesome and I need to have this for myself. Searching around, I found an old [GitHub repo](https://github.com/tallguyjenks/BusinessCard) by Bryan Jenks containing the bash script they use to generate their curl card.

```bash
curl https://raw.githubusercontent.com/tallguyjenks/BusinessCard/refs/heads/master/business_card
```

```
╭───────────────────────────────────────────────────────╮
│                                                       │
│           Bryan Jenks / TallGuyJenks                  │
│                                                       │
│     Email:  bryanjenks@protonmail.com                 │
│       Web:  https://www.bryanjenks.dev                │
│                                                       │
│   Twitter:  https://twitter.com/tallguyjenks          │
│    GitHub:  https://github.com/tallguyjenks           │
│  LinkedIn:  https://linkedin.com/in/bryanjenks        │
│   YouTube:  https://www.youtube.com/c/BryanJenksTech  │
│     OrcID:  https://orcid.org/0000-0002-9604-3069     │
│   Patreon:  https://www.patreon.com/bryanjenks        │
│                                                       │
│      Card:  curl -sL bit.ly/2AtVaXR                   │
│                                                       │
╰───────────────────────────────────────────────────────╯

```

Their bash script makes uses of `tput` from the `ncurses` library to set the terminal colors. Adapting their script to include my information, and I now have a curl card of my own!

```bash
curl https://brandonrozek.com/cc
```

```
╭──────────────────────────────────────────────────╮
│                                                  │
│                  Brandon Rozek                   │
│                                                  │
│     Email:  brozek@brandonrozek.com              │
│       Web:  https://brandonrozek.com             │
│                                                  │
│  Mastodon:  https://fossotdon.org/@brozek        │
│    GitHub:  https://github.com/Brandon-Rozek     │
│                                                  │
│      Card:  curl -sL brandonrozek.com/cc         │
│                                                  │
╰──────────────────────────────────────────────────╯

```



