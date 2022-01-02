---
title: "YubiKey"
date: 2019-07-07T14:31:47-04:00
draft: false
tags: ["Security"]
---

The YubiKey is a hardware authentication device manufactured by Yubico. It is a write only device that is meant to hold various authentication keys. The fact that it is write only means that people can't duplicate these keys. [Noah Chelliah](https://twitter.com/kernellinux) from Altispeed says that he uses YubiKeys at his company so that when employees moves on from his company he only needs to take their YubiKey.

Now I don't manage any infrastructure larger than a couple computers, so why are these things interesting from a home use perspective? Well it allows you to have two-factor authentication separate from your smart phone. I was never a large fan of using my cell phone for two factor since you usually change cell phones every couple years.

What I wanted to highlight is how easy it is to integrate it with Linux. The Pluggable Authentication Module (PAM) is responsible for authentication and other various utilities in Linux. By adding a couple of lines to a couple of text files, you can add two-factor authentication to your laptop!

Instead of rewriting a bunch of instructions I got from somewhere else, I'll direct you to Yubico's own [documentation entry](https://developers.yubico.com/yubico-pam/Authentication_Using_Challenge-Response.html). Happy hacking!

