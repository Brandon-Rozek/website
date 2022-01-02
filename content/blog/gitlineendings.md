---
title: "Git Line Endings"
date: 2020-05-09T11:01:21-04:00
draft: false
tags: ["Git"]
---

if you have worked with a team that has a mix of Windows and Linux developers, you might have noticed pull requests where Git reports changes in a file that is not visible. One explanation is that the line endings might have changed. 

Due to historical reasons Windows uses a line ending called CRLF which stands for carriage return + line feed. This dates back to type writers where once you hit the line feed button to push the paper up, you need to press the carriage return button to move back to the left side of the paper. [Wikipedia](https://en.wikipedia.org/wiki/Carriage_return) has more of a history if you want to learn more.

Meanwhile, Linux only uses LF or line feed for its ending.  We can configure a repository with a `.gitattributes` file to automatically convert CRLF to LF line endings in order not to see these frivolous changes in our repository. 

The `.gitattributes` file looks like this

```
# Automatically convert CRLF->LF on files git thinks are text
* text=auto

# Explicitly declare what are text files
*.py text
*.js text

# Denote files that are binary and should not be modified.
*.png binary
*.jpg binary
```

Make sure that you don't have any working changes that need to be committed as the following commands will convert all the line endings for text files in your repository to LF.

First let us commit the git attributes file

```bash
git add .gitattributes
git commit -m "Added gitattributes file"
```

Then let us convert all the line endings to LF

```bash
git add --renormalize .
git commit -m "Convert line endings to LF"
```

Then tell your coworkers to expect a large commit which only line ending changes....