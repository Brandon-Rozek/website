---
id: 2241
title: Obtaining Command Line Input in Java
date: 2017-08-28T17:37:59+00:00
author: Brandon Rozek
aliases:
    - /2017/08/obtaining-command-line-input-java/
permalink: /2017/08/obtaining-command-line-input-java/
medium_post:
  - 'O:11:"Medium_Post":11:{s:16:"author_image_url";N;s:10:"author_url";N;s:11:"byline_name";N;s:12:"byline_email";N;s:10:"cross_link";N;s:2:"id";N;s:21:"follower_notification";N;s:7:"license";N;s:14:"publication_id";N;s:6:"status";N;s:3:"url";N;}'
mf2_syndicate-to:
  - 'a:1:{i:0;s:4:"none";}'
mf2_cite:
  - 'a:4:{s:9:"published";s:25:"0000-01-01T00:00:00+00:00";s:7:"updated";s:25:"0000-01-01T00:00:00+00:00";s:8:"category";a:1:{i:0;s:0:"";}s:6:"author";a:0:{}}'
mf2_mp-syndicate-to:
  - 'a:1:{i:0;s:4:"none";}'
tags: ["Java"]
---
To obtain console input for your program you can use the `Scanner` class

First import the relevant library

```java
import java.util.Scanner;
```

Then create a variable to hold the `Scanner` object

```java
Scanner input;
input = new Scanner(System.in);
```

Inside the parenthesis, the `Scanner` binds to the System input which is by default the console

The new varible `input` now has the ability to obtain input from the console. To do so, use any of the following methods:

| Method         | What it Returns                                            |
| -------------- | ---------------------------------------------------------- |
| `next()`       | The next space separated string from the console           |
| `nextInt()`    | An integer if it exists from the console                   |
| `nextDouble()` | A double if it exists from the console                     |
| `nextFloat()`  | A float if it exists from the console                      |
| `nextLine()`   | A string up to the next newline character from the console |
| `hasNext()`    | Returns true if there is another token                     |
| `close()`      | Unbinds the Scanner from the console                       |



Here is an example program where we get the user&#8217;s first name

```java
import java.util.Scanner;

public class GetName {
  public static void main(String[] args) {
    Scanner input = new Scanner(System.in);
    System.out.print("Please enter your name: ");
    String firstName = input.next();
    System.out.println("Your first name is " + firstName); 
  }
}
```
