---
title: "Process JSON in the terminal with jq"
date: 2024-10-05T15:59:10-07:00
draft: false
tags: []
math: false
medium_enabled: false
---

The `jq` command is great for quickly viewing and manipulating JSON data. By default, the output is formatted is a human-readable way, and they provide an easy way to "filter" or access elements within the JSON data.

For example

```bash
echo "{\"firstName\": \"Brandon\", \"lastName\": \"Rozek\"}"  | jq
```

Outputs

```json
{
  "firstName": "Brandon",
  "lastName": "Rozek"
}
```

To see what's in the field `firstName`

```bash
echo "{\"firstName\": \"Brandon\", \"lastName\": \"Rozek\"}"  | jq .firstName
```

Other than quickly viewing JSON objects in the terminal. I have two other use cases for it.

**1: Sanitizing Strings**

```bash
echo $OUTPUT | jq -Rsa .
```

| Flag | Description                                                  |
| ---- | ------------------------------------------------------------ |
| `-R` | Don´t parse the input as JSON. Instead, each line of text is passed to the filter as a string. |
| `-s` | Pass the entire input to the filter as a single long string  |
| `-a` | Produce  pure  ASCII  output  with every  non-ASCII  character replaced with the equivalent escape sequence. |

**2: Stringifying JSON**

```bash
jq ".|tojson"
```

From the man pages

> The `tojson` and `fromjson` builtins dump values as JSON texts or parse JSON texts into values, respectively. 

