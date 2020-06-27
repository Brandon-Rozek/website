---
title: "Firefox Privacy Configuration"
date: 2020-06-26T22:35:05-04:00
draft: false
tags: []
---

Firefox has a great number of configurable options when it comes to privacy. I first discovered this as I was browsing [privacytools.io](https://www.privacytools.io/browsers/) recommendations. Mozilla also has a [privacy task force](https://wiki.mozilla.org/Privacy/Privacy_Task_Force/firefox_about_config_privacy_tweeks) documenting some these options. I later learned that there is a website called [Firefox Profilemaker](https://ffprofile.com/) that takes the user step by step creating a privacy preserving profile.

Here are the list of settings in `about:config` that I found most interesting,

| Flag                         | Description                                                  |
| ---------------------------- | ------------------------------------------------------------ |
| privacy.resistFingerprinting | Attempts to [resist fingerprinting](https://wiki.mozilla.org/Security/Fingerprinting). |
| privacy.firstparty.isolate   | Isolates cookies to the first party domain to prevent tracking across domains. |
| network.IDN_show_punycode    | Render internationalized domain name (IDN) as Punycode equivalent to help against [phishing attacks](https://en.wikipedia.org/wiki/IDN_homograph_attack). |

[Hold Integrity released a tool](https://holdintegrity.com/checker) to check IDNs and see if there are any look alikes domains registered on the Internet. 