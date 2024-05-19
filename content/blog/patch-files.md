---
title: "Creating Patch Files"
date: 2024-05-18T20:10:21-04:00
draft: false 
tags: []
math: false
medium_enabled: false
---

Distributing software can be difficult. Is the shared library called `x` on this distribution or is it called `y`? This may lead to a lot of distribution specific code.

It might not make sense to commit these changes to the main software repository. An alternative is to create *patch files*. These are files that capture exactly how you want to update a given file.

Let's take the following C code as an example:

```c
#include <stdio.h>

int main(void)
{
  printf("Goodbye World\n");
  return 0;
}
```

Instead, we want for it to print out the classic "Hello World". To do this, first let us save the original file.

```bash
cp hello-world.c hello-world.c.orig
```

Then let's edit `hello-world.c` to produce the desired result

```c
#include <stdio.h>

int main(void)
{
  printf("Hello World\n");
  return 0;
}
```

Now we can create the patch file.

```bash
diff -Naur hello-world.c.orig hello-world.c > hello.patch
```

The options of `diff` are the following:

| Flag | Description                                  |
| ---- | -------------------------------------------- |
| `-N` | Treat absent files as empty                  |
| `-a` | Treat all files as text                      |
| `-u` | Output 3 lines of unified context            |
| `-r` | Recursively compare any subdirectories found |

This will output the following patch file

```diff
--- hello-world.c.orig  2024-05-12 20:41:27.708297085 -0400
+++ hello-world.c       2024-05-12 20:41:36.742348955 -0400
@@ -2,7 +2,7 @@
 
 int main(void)
 {
-  printf("Goodbye World\n");
+  printf("Hello World\n");
   return 0;
 }
```

In order to test out the patch, let us revert the hello-world.c file to it's original state.

```bash
cp hello-world.c.orig hello-world.c
```

Now apply the patch

```bash
patch < hello.patch
```

To undo the patch

```bash
patch -R hello-world.c < hello.patch
```

