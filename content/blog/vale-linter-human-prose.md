---
title: "Linting my blog posts with Vale"
date: 2024-11-27T16:29:30-05:00
draft: false
tags: []
math: false
medium_enabled: false
---

How do you write *good*?

For some, the answer is Grammarly. This, however, falls short to me for the following reasons:

- Needing to rely on some third party service. Seriously, what if I want to draft my blog posts without Internet?
- Not configurable. Leave me alone, sometimes I like writing **my way**.
- Where's my beautiful terminal application?

I use [Vale](https://vale.sh/) ([GitHub](https://github.com/errata-ai/vale)) a linter for human prose. It runs locally on my computer ✔, is configurable by defining a rule set ✔, and offers not only a beautiful CLI application ✔, but even offers integrations to editors like VSCode.

To provide useful feedback, we'll need a strong collection of rules. Like a crazy person, I went onto the [Vale package hub](https://vale.sh/hub/) and looked at the rules of many different packages and compiled the ones I liked into [my own package](https://github.com/brandon-rozek/vale) for us to use.

All we need to do is specify the package in our Vale config. To see where this lives, you can run `vale ls-dirs`. For example, on my computer it is at `~/.config/vale/.vale.ini`

```ini
StylesPath = /home/rozek/.local/share/vale/styles

Vocab = brozek

MinAlertLevel = suggestion

Packages = https://github.com/Brandon-Rozek/vale/releases/download/0.1.0/brozek.zip

[*]
BasedOnStyles = Vale, brozek
```

By default, Vale includes a spell-checker. As a technical writer, I often talk about products which Vale claims are typos. We can force Vale to not complain by creating a [Vocabulary](https://vale.sh/docs/topics/vocab/) (fancy word for dictionary).

`<StylesPath>/config/vocabularies/brozek/accept.txt`

```
BTRFS
[Bb]oolean
systemd
Zulip
```

These vocabularies are case-sensitive, which while may seen like a weird choice, I find useful in keeping capitalization consistent. To specify that something is not case sensitive you'll need to put square brackets around the upper and lower-case letter. For example, case-insensitive b is `[Bb]`.

With all this configured, we can then sync the configuration rules to our machine.

```bash
vale sync
```

Then, lint a blog post!

```bash
vale vale-linter-human-prose.md
```

```
 vale-linter-human-prose.md
 14:48  warning     Remove 'Seriously' if it's not  brozek.Adverbs
                    important to the meaning of
                    the statement.
 20:70  suggestion  Try to keep sentences short (<  brozek.SentenceLength
                    30 words).
 48:91  warning     Remove 'really' if it's not     brozek.Adverbs
                    important to the meaning of
                    the statement.
```

From there you can choose which suggestions to keep and which to ignore ;)

