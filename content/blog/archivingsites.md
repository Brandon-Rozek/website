---
title: "Archiving Sites"
date: 2019-08-02T22:42:16-04:00
draft: false
---

I have several old Wordpress sites that are now only alive for archival purposes. I've been trying to migrate off of Wordpress since I don't like having yet another system to manage. Luckily for archival type sites, I don't need the whole backend of Wordpress since I don't actually need any CRUD functionality. (Well I need the R part)

Solution... wget comes to the [rescue](https://stackoverflow.com/questions/538865/how-do-you-archive-an-entire-website-for-offline-viewing#538878)

User [chuckg](https://stackoverflow.com/users/63193/chuckg) initially suggested to run `wget -m -k -K -E https://url/of/web/site` to get a full offline copy of a website.

[Joel Gillman](https://stackoverflow.com/users/916604/jgillman) and [Firsh](https://letswp.io/download-an-entire-website-wget-windows/) wrote about their commands and now our command has expanded to: 
```bash
wget --mirror \
     --convert-links \
     --adjust-extension \
     --no-clobber \
     --page-requisites \
     https://url/of/web/site
```

There are other solutions in that stack overflow post, but something about the simplicity of `wget` appealed to me.

[Check out this now Wordpress free site of mine!](https://sentenceworthy.com)
