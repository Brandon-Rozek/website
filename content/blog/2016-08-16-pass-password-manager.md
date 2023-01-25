---
id: 919
title: Pass the password manager
date: 2016-08-16T23:37:09+00:00
author: Brandon Rozek
aliases:
    - /2016/08/pass-password-manager/
permalink: /2016/08/pass-password-manager/
medium_post:
  - 'O:11:"Medium_Post":11:{s:16:"author_image_url";N;s:10:"author_url";N;s:11:"byline_name";N;s:12:"byline_email";N;s:10:"cross_link";s:2:"no";s:2:"id";N;s:21:"follower_notification";s:3:"yes";s:7:"license";s:19:"all-rights-reserved";s:14:"publication_id";s:2:"-1";s:6:"status";s:4:"none";s:3:"url";N;}'
mf2_cite:
  - 'a:4:{s:9:"published";s:25:"0000-01-01T00:00:00+00:00";s:7:"updated";s:25:"0000-01-01T00:00:00+00:00";s:8:"category";a:1:{i:0;s:0:"";}s:6:"author";a:0:{}}'
bridgy_syndication:
  - https://twitter.com/B_RozekJournal/status/790336614866100224
mf2_syndicate-to:
  - 'a:1:{i:0;s:4:"none";}'
tags: ["Security"]
---
Looking over the list of programs installed on my computer, one of my all time favorites is a program called [Pass](https://www.passwordstore.org/). It&#8217;s a program available under most Linux distributions, Mac OS X (through [Brew](http://brew.sh/)), [Windows](https://github.com/mbos/Pass4Win), [Android](https://play.google.com/store/apps/details?id=com.zeapo.pwdstore), and [iOS](https://github.com/davidjb/pass-ios#readme). It stores all of the passwords using gpg encryption and stores them as actual files on the hard disk. Meaning if you wanted, you can sync them to all your devices!

This program assumes a light familiarity with the terminal

<!--more-->

## Setup {#setup}

First if you do not already have a gpg key, [create one](http://wooledge.org/~greg/crypto/node41.html).

Then in the terminal type in

    pass init youremail@address

Substituting youremail@address with the email associated with your gpg key.

This will autmatically create an empty repository under your home folder in a folder labeled `.pass`

If you are switching from an existing password manager, check to see if on the [Pass homepage](https://www.passwordstore.org/), there doesn&#8217;t exist a script to help you out

## Basic Tasks {#basic-tasks}

To insert a password into pass

    pass insert password-name

It will then prompt you to enter the password

To show passwords you have already inserted

    pass

To show an individual password

    pass password-name

But generally I find it handy to have it automatically in my clipboard. You can do that with the -c option

    pass -c password-name

You can generate new secure passwords using pass. (-c copies the result into your clipboard)

    pass generate -c password-name password-length

If you don&#8217;t want it to output symbols, use the -n option to restrict it to alphanumericals

    pass generate -n -c password-name password-length

Another command i find handy is the `find` command. Mainly because I have over a 100 passwords in this system and i tend to forget what I named some of them

    pass find search-string

There are too many commands to list them all, but if you ever want to find out more, check out the manual entry page for `pass`

    man pass

## Extra: Syncing {#sync}

I use a nextCloud instance on my server to sync my passwords, but I don&#8217;t see a reason why this wouldn&#8217;t work with other projects like dropbox, syncthing, or any other sync solution

Some sync solutions don&#8217;t like to sync folders that begin with a &#8216;.&#8217;, my solution around this is to create a symbolic link between that and a folder you wish to link it to

    ln -s /path/to/home/folder/.password-store /path/to/sync/folder/password-store

Then you just need to make sure to make the same link to all your other computers

## Conclusion {#conclusion}

I like Pass for it&#8217;s ease of use and for the fact that I&#8217;m not tied into any one company for managing my passwords. It&#8217;s based on open source tools and the fact I didn&#8217;t have to configure a database is a huge plus for me

If you&#8217;re in a need of a password manager (I hope you have more than one password), then give pass a shot. It served me and my many passwords well.