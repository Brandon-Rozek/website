---
id: 350
title: Functions in Javascript
date: 2015-10-25T13:48:41+00:00
author: Brandon Rozek
layout: post
guid: https://brandonrozek.com/?p=350
aliases:
    - /2015/10/functions/
permalink: /2015/10/functions/
medium_post:
  - 'O:11:"Medium_Post":11:{s:16:"author_image_url";N;s:10:"author_url";N;s:11:"byline_name";N;s:12:"byline_email";N;s:10:"cross_link";N;s:2:"id";N;s:21:"follower_notification";N;s:7:"license";N;s:14:"publication_id";N;s:6:"status";N;s:3:"url";N;}'
  - 'O:11:"Medium_Post":11:{s:16:"author_image_url";s:74:"https://cdn-images-1.medium.com/fit/c/200/200/1*dmbNkD5D-u45r44go_cf0g.png";s:10:"author_url";s:32:"https://medium.com/@brandonrozek";s:11:"byline_name";N;s:12:"byline_email";N;s:10:"cross_link";s:2:"no";s:2:"id";s:12:"44583f68d3fa";s:21:"follower_notification";s:2:"no";s:7:"license";s:19:"all-rights-reserved";s:14:"publication_id";s:2:"-1";s:6:"status";s:6:"public";s:3:"url";s:55:"https://medium.com/@brandonrozek/functions-44583f68d3fa";}'
  - 'O:11:"Medium_Post":11:{s:16:"author_image_url";s:74:"https://cdn-images-1.medium.com/fit/c/200/200/1*dmbNkD5D-u45r44go_cf0g.png";s:10:"author_url";s:32:"https://medium.com/@brandonrozek";s:11:"byline_name";N;s:12:"byline_email";N;s:10:"cross_link";s:2:"no";s:2:"id";s:12:"44583f68d3fa";s:21:"follower_notification";s:2:"no";s:7:"license";s:19:"all-rights-reserved";s:14:"publication_id";s:2:"-1";s:6:"status";s:6:"public";s:3:"url";s:55:"https://medium.com/@brandonrozek/functions-44583f68d3fa";}'
mf2_cite:
  - 'a:1:{s:6:"author";a:0:{}}'
  - 'a:1:{s:6:"author";a:0:{}}'
tumblr_post_id:
  - "135657661534"
  - "135657661534"
kind:
  - article
tags: ["Web", "JS"]
---
Ever had a snippet of code that appears multiple times in different places in your program? Whenever you had to change that snippet, you end up playing this game of search and replace. Functions can help. They exist to abstract your code, making it not only easier to change that little snippet, but to read and debug your code as well.

<!--more-->

### <a href="#how-to-create/execute-a-function" name="how-to-create/execute-a-function"></a>How to create/execute a function {#how-to-create/execute-a-function}

To make a function

```javascript
    var doSomething = function() {
        doStuff;
    }
```

To call the above function to execute

```javascript
    doSomething();
```

### <a href="#arguments" name="arguments"></a>Arguments {#arguments}

You can also add in arguments (parameters that go inside the paraenthesis next to the word function) for the functions to use.

```javascript
    var add = function(number1, number2) {
        return number1 + number2;
    }
```

And when you use the `return` keyword, like the function above. You can store the value in a variable for future use.

```javascript
    var total = add(1, 3);
```

<code class="language-javascript">total</code> here will equal `4`

### <a href="#scope" name="scope"></a>Scope {#scope}

Functions create their own scope, which means that variables created inside the function will only be able available within that function.

The snippet below will output an error like <code class="language-javascript">total is not defined</code>

```javascript
    var add = function(number1, number2) {
        var total = number1 + number2;
    }
    console.log(total);
```

Below is a correct example of the concept

```javascript
    //Function below converts km/hr to m/s
    var convert = function(speed) {
        var metersPerHour = speed * 1000;
        var metersPerSecound = metersPerHour / 3600;
        return metersPerSecond;
    }
    var currentSpeed = convert(5);
```

It’s also important to note that functions can use variables outside of it; granted it resides in the same scope.

Here is an example of a variable that doesn&#8217;t reside in the same scope as the function. (The below code will fail)

```javascript
    var something = function() {
        var x = 5;
        var y = 2;
    }
    something();
    var addXandY = function() {
        console.log(x + y);
    }
    addXandY();
```

Below, is an example of where the variable does reside in the same scope as the function. Which allows this snippet to execute properly.

```javascript
    var x = 5;
    var addX = function(a) {
        return a + x;
    }
    var sum = addX(6);
```

<code class="language-javascript">sum</code> here will equal <code class="language-javascript">11</code>

### <a href="#conclusion" name="conclusion"></a>Conclusion {#conclusion}

As long as you name them appropriately, functions are useful for abstracting your code, making them easier to understand. This concludes another lecture made for the members over at Math I/O. Until next week 🙂