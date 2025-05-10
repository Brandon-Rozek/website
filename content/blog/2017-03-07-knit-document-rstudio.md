---
id: 2090
title: Knit a Document in RStudio
date: 2017-03-07T04:29:50+00:00
author: Brandon Rozek
aliases:
    - /2017/03/knit-document-rstudio/
permalink: /2017/03/knit-document-rstudio/
medium_post:
  - 'O:11:"Medium_Post":11:{s:16:"author_image_url";N;s:10:"author_url";N;s:11:"byline_name";N;s:12:"byline_email";N;s:10:"cross_link";N;s:2:"id";N;s:21:"follower_notification";N;s:7:"license";N;s:14:"publication_id";N;s:6:"status";N;s:3:"url";N;}'
mf2_syndicate-to:
  - 'a:1:{i:0;s:4:"none";}'
mf2_cite:
  - 'a:4:{s:9:"published";s:25:"0000-01-01T00:00:00+00:00";s:7:"updated";s:25:"0000-01-01T00:00:00+00:00";s:8:"category";a:1:{i:0;s:0:"";}s:6:"author";a:0:{}}'
format: aside
tags: ["R"]
---
In case you were wondering how I got all the R code and output for the [&#8220;Do females live longer than males?&#8221;](https://brandonrozek.com/portfolio/male-vs-female-life-expectancy/) page. There is actually a function in RStudio that allows one to compile a report based on code and it&#8217;s output.

<!--more-->

First go to File->Knit Document. If this is your first time, then it will install RMarkdown, a dependency this tool needs to compile the report.

Once that is downloaded, it will let you choose between three different file formats (HTML, PDF, MS Word). For the purposes of blog posts, I like to output it in HTML so I can copy and paste the code. But for personal use, I like using PDFs

After you select the file format, hit compile, and voila! A nice neat compiled report is created for you. Here is a [pdf](/files/reports/LifeExpectancy.pdf) example of the report I made.
