---
title: "Memory Errors in Go"
date: 2019-08-02T22:35:53-04:00
draft: false
---

I enjoy playing with Valgrind. Sometimes I view it as a game to get rid of memory errors. When I wrote a go script, I noticed that I received a lot of memory errors. I decided to double check by writing a simple hello world program in Go.

```go
package main
import "fmt"
func main() {
  fmt.Println("Hello World")
}
```
Running this then gives me a bunch of memory errors of the form `Invalid read of size 4`.

Now this doesn't mean that the program is leaky. Valgrind does confirm that no leaks are possible. It then begs the question, does this type of memory error even matter?

To avoid thinking about that I decided to play with [Rust](https://rust-lang.org) instead.