---
date: 2022-12-18 12:55:32-05:00
draft: false
math: false
medium_enabled: true
medium_post_id: 9801b2556737
tags: []
title: Capturing Quoted Strings in Sed
---

*Disclaimer: This posts assumes some knowledge about regular expressions.*

Recently I was trying to capture an HTML attribute in `sed`. For example, let's say I want to extract the `href` attribute in the following example:

```
<a href="https://brandonrozek.com" rel="me"></a>
```

Advice you commonly see on the Internet is to use a capture group for anything between the quotes of the href.

In regular expression land, we can represent anything as `.*` and define a capture group of some regular expression `X` as `\(X\)`.

```bash
sed "s/.*href=\"\(.*\)\".*/\1/g"
```

What does this look like for our input?

```bash
echo \<a href=\"https://brandonrozek.com\" rel=\"me\"\>\</a\> |\
sed "s/.*href=\"\(.*\)\".*/\1/g"
```

```
https://brandonrozek.com" rel="me
```

It matches all the way until the second `"`! What we want, is to not match *any* character within the quotations, but match any character that is not the quotation itself `[^\"]*`

```bash
sed "s/.*href=\"\([^\"]*\)\".*/\1/g"
```

This then works for our example:

```bash
echo \<a href=\"https://brandonrozek.com\" rel=\"me\"\>\</a\> |\
sed "s/.*href=\"\([^\"]*\)\".*/\1/g"
```

```
https://brandonrozek.com
```

Within a bash script, we can make this a little more readable by using multiple variables.

```bash
QUOTED_STR="\"\([^\"]*\)\""
BEFORE_TEXT=".*href=$QUOTED_STR.*"
AFTER_TEXT="\1"
REPLACE_EXPR="s/$BEFORE_TEXT/$AFTER_TEXT/g"

INPUT="\<a href=\"https://brandonrozek.com\" rel=\"me\"\>\</a\>"

echo "$INPUT" | sed "$REPLACE_EXPR"
```