---
title: "Type Checking Javascript Files Using Typescript"
date: 2023-09-19T15:30:02-04:00
draft: false
tags: []
math: false
medium_enabled: false
---

There's a nice and easy way to type check Javascript files without having to set up an entire project or adjust the code. It only takes understanding some of the flags within the Typescript compiler.

To install:

```bash
npm install -g typescript
```

Typecheck a file:

```bash
tsc --checkJs --allowJs example.js --noEmit
```

| Flag        | Description                                             |
| ----------- | ------------------------------------------------------- |
| `--checkJs` | Allow JavaScript files to be a part of your program.    |
| `--allowJs` | Enable error reporting in type-checked JavaScript files |
| `--noEmit`  | Disable emitting files from a compilation.              |

Since `tsc` is primarily a compile, it by default produces code output.
We're only concerned with seeing any type errors, so we throw away
the compiled code with the flag `--noEmit`.[^1]

[^1]: In an earlier version of this post, I had `--outfile /dev/null` instead of `--noEmit`.
[Veyndan](https://veyndan.com/) kindly reached out and showed how the `--noEmit` flag is
more flexible in allowing for exported classes. 

Now it's likely that we're using features of the standard library or the DOM in our Javascript code. We need to include a couple flags for Typescript to understand them.

| Flag       | Description                                                  |
| ---------- | ------------------------------------------------------------ |
| `--target` | Set the JavaScript language version for emitted JavaScript and include compatible library declarations. |
| `--lib`    | Specify a set of bundled library declaration files that describe the target runtime environment. |

You can see `tsc --help`for the long list of options. Here's an example for targetting `ES2022` with the DOM library.

```bash
tsc --checkJs --allowJs --target es2022 --lib es2022,dom example.js --noEmit
```

