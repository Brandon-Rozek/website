---
title: "Ascii Towns in the Tildeverse with Cadastre"
date: 2024-01-17T18:14:32-05:00
draft: false
tags: []
math: false
medium_enabled: false
---

[Cadastre](https://github.com/jmdejong/cadastre) stitches together plots of "land" that users on a tilde server control. Ultimately creating one giant ascii town.

For example,  consider one user has the following in `~/.cadastre/home.txt`:

```
0 0
####################
#  ________        #
# /~\__\___\       #
# | |  |   | ,,,,  #
#           ,,,,,  #
#    ~~~~~  ,,,,,  #
#    ~~~~~     _   #
#    ~~~~~    (*)  #
# ~deepend     |   #
#                  #
####################
```

While another user has:

```
0 1
~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~
~~        ~~~~~~~~~~~~~
~    ~~~      ~~~~~~~~~~
~~~~~~~~~      ~~~    ~
~~~~~~~~~~~         ~~~
~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~
```

Then the stitched together town will be:

```
#################### ~~~~~~~~~~~~~~~~~~~~~~~~
#  ________        # ~~~~~~~~~~~~~~~~~~~~~~~
# /~\__\___\       # ~~~~~~~~~~~~~~~~~~~~~~~
# | |  |   | ,,,,  # ~~~~~~~~~~~~~~~~~~~~~~~
#           ,,,,,  # ~~        ~~~~~~~~~~~~~
#    ~~~~~  ,,,,,  # ~    ~~~      ~~~~~~~~~~
#    ~~~~~     _   # ~~~~~~~~~      ~~~    ~
#    ~~~~~    (*)  # ~~~~~~~~~~~         ~~~
# ~deepend     |   # ~~~~~~~~~~~~~~~~~~~~~~~
#                  # ~~~~~~~~~~~~~~~~~~~~~~~
#################### ~~~~~~~~~~~~~~~~~~~~~~~
```

Ascii art is something that always interested me, but I never took the time to make. Cadastre limits us to 24x12 characters which serves as a good starting canvas for myself.

You might be able to tell, but I'm a big fan of mountains.

```
+=======================+
.    /\                 .
.   /  \  /\            .
.  /    \/  \/\         .
. /      \ _ \ \        .
.     ____//            .
. ___/____/      @@@    .
. ___/         @@@@@@@  .
.             @@@@@@@@@ .
.              @@@@@@@  .
. ~brozek        | |    .
.........................
```

Check out my plot among the village over at [tilde.club](https://tilde.club/~troido/cadastre/town.html). For a more lively instance check out [tilde.town](http://tilde.town/~troido/cadastre/town.html).

*Thanks to [~troido](http://tilde.town/~troido/) for creating this cool piece of software!*
