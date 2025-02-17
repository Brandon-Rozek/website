---
id: 238
title: Javascript Data Types
date: 2015-10-10T20:01:20+00:00
author: Brandon Rozek
aliases:
    - /2015/10/javascript-data-types/
permalink: /2015/10/javascript-data-types/
medium_post:
  - 'O:11:"Medium_Post":11:{s:16:"author_image_url";N;s:10:"author_url";N;s:11:"byline_name";N;s:12:"byline_email";N;s:10:"cross_link";N;s:2:"id";N;s:21:"follower_notification";N;s:7:"license";N;s:14:"publication_id";N;s:6:"status";N;s:3:"url";N;}'
  - 'O:11:"Medium_Post":11:{s:16:"author_image_url";s:74:"https://cdn-images-1.medium.com/fit/c/200/200/1*dmbNkD5D-u45r44go_cf0g.png";s:10:"author_url";s:32:"https://medium.com/@brandonrozek";s:11:"byline_name";N;s:12:"byline_email";N;s:10:"cross_link";s:2:"no";s:2:"id";s:12:"edcd4e2dcf42";s:21:"follower_notification";s:2:"no";s:7:"license";s:19:"all-rights-reserved";s:14:"publication_id";s:2:"-1";s:6:"status";s:6:"public";s:3:"url";s:67:"https://medium.com/@brandonrozek/javascript-data-types-edcd4e2dcf42";}'
  - 'O:11:"Medium_Post":11:{s:16:"author_image_url";s:74:"https://cdn-images-1.medium.com/fit/c/200/200/1*dmbNkD5D-u45r44go_cf0g.png";s:10:"author_url";s:32:"https://medium.com/@brandonrozek";s:11:"byline_name";N;s:12:"byline_email";N;s:10:"cross_link";s:2:"no";s:2:"id";s:12:"edcd4e2dcf42";s:21:"follower_notification";s:2:"no";s:7:"license";s:19:"all-rights-reserved";s:14:"publication_id";s:2:"-1";s:6:"status";s:6:"public";s:3:"url";s:67:"https://medium.com/@brandonrozek/javascript-data-types-edcd4e2dcf42";}'
dsq_thread_id:
  - "4215821079"
  - "4215821079"
mf2_cite:
  - 'a:1:{s:6:"author";a:0:{}}'
  - 'a:1:{s:6:"author";a:0:{}}'
tags: ["Web", "JS"]
---
Javascript has multiple ways you can store your data. Each of these different ways is called a data type, and they each carry different “methods” which are helpful commands. Today, I’ll show you the different data types and methods that I use and how they’re useful.

This post is by far not a comprehenive list of all the Data types and their methods. If you want one of those, please check out [MDN](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects) and/or [WebPlatform](http://docs.webplatform.org/wiki/javascript/objects){.broken_link}. This is the second lecture of the web development class I’m teaching for the newer folks over at [Math I/O](http://math-io.com). Due to the nature of Math I/O (making math games and all), the next few posts will be Javascript centric. We’re getting ready to build a new game, so I want to prepare them as much as possible. \*Excited\* ^_^ Ilya Kantor does a good job of descibing Javascript data types and their many methods in [Mastering Data Types](http://javascript.info/tutorial/mastering-data-types) which I made the recommended reading for this lecture.

### String

A string is one or more characters.

```javascript
var name = "Brandon";
```

You can access a character inside of a string by using [] notation. Inside the [] you put the index of the character you want. An index is the numeral location of the character starting from the left. It is important to note that Javascript starts counting from 0.

| B    | r    | a    | n    | d    | o    | n    |
| ---- | ---- | ---- | ---- | ---- | ---- | ---- | 
| 0    | 1    | 2    | 3    | 4    | 5    | 6    |


```javascript
var firstInitial = "Brandon"[0];
```
Now the value of firstInitial is the letter `"B"`.

#### Some useful methods for strings

##### `String.prototype.indexOf`

This can be used to find the index of any character(s) in a string. I primarily use it for when I need to check if something exists in a string. Do I have a ‘z’ in my name?

```javascript
"Brandon".indexOf('z');
```

Nope, so Javascript will return a `-1`. How about a ‘d’?

```javascript
"Brandon".indexOf('d');
```

Yes, Javascript will return `5` which is the index of the letter `‘d’`.

##### `String.prototype.replace`

The replace method can replace any character(s) with other character(s). For more complex replacing, look into [Regular Expression](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Guide/Regular_Expressions) and how you can use them in `.replace()`. Replace the first `‘n’` in my name with an `‘m’`.

```javascript
var modifiedName = "Brandon".replace('n', 'm');
console.log(modifiedName);
```

Logs `"Bramdon"`.

##### `String.prototype.toUpperCase`

This method returns the string with all the lowercase characters converted to uppercase and can be useful for when you’re checking user input and you don’t want to worry about different cases.

```javascript
"Brandon".toUpperCase();
```

Returns `"BRANDON"`.

##### `String.prototype.toLowerCase()`

Same as above but instead of converting lowercase to uppercase, it converts uppercase to lowercase.

```javascript
"Brandon".toLowerCase();
```

Returns `"brandon"`.

#### A couple useful escape secquences

  * `\n` for newline.
  * `\t` for tab character.

You can also use escape sequnces if you want to add `“”` or `‘’` to your strings.

```javascript
var greeting = "Hello \"Brandon\"";
console.log(greeting);
```

Returns `"Hello "Brandon""`.

### Number

Any number between -(2^53 – 1) and (2^53 – 1).

#### Number Methods

Number methods are useful when trying to represent complex numbers.

##### `Number.prototype.toExponential()`

Returns a string representing a number in exponential notation.

```javascript
77.1234.toExponential(2);
```

Returns `"7.71e+1"`.

##### `Number.prototype.toFixed()`

Returns a string representing a number fixed to x amount of decimal places.

```javascript
12345.6789.toFixed(1);
```

Returns `"12345.7"`.

##### `Number.prototype.toPrecision();`

Returns a string representing a number using x amount of significant figures.

```javascript
5.123456.toPrecision(2);
```

Returns `"5.1"`.

#### Math properties/methods

In Javascript there is a Math object which contains many properties and methods which are useful for mathmatical calculations.

##### Return Euler’s constant

`Math.E` which returns ~2.718.

##### Return the natural log of x

```javascript
Math.log(x)
```

##### Rise x to the y power

```javascript
Math.pow(x,y)
```

##### Return a psuedo random number \[0,1\) 

```javascript
Math.random()
```

##### Round x to the nearest integer

```javascript
Math.round(x)
```

### Boolean

Booleans are either `true` or `false` and are typically used in conditional statements. You can either create them explicitly

```javascript
var alive = true;
```
or by evaluating a [comparison](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Operators/Comparison_Operators).

```javascript
var dead = false;
var isAlive = !dead;
```

isAlive equals `true`.

### Array

An array is a list of items. In Javascript these items can be any data type, even arrays themselves.

```javascript
var mixedBag = ['sword', 24, true, [Math.PI, Math.E], 'shield'];
```

To access an item in an array use [] notation with an index as mentioned over at strings.

```javascript
['sword', 'shield', 'helmet'][1];
```

Returns `'shield'`. In order to figure out how many items are in the array:

```javascript
var inventory = ['boots', 'gloves', 'pants', 'shirt'];
var inventoryAmt = inventory.length;
```

inventoryAmt is `4` since there are 4 items in inventory.

#### Array Methods

##### `Array.prototype.push()`

Adds whatever is inside the parenthesis to the end of the array. Great for adding items to a list. For example, test scores.

```javascript
[100,92,95].push(80);
```

Returns `[100,92,95,80]`.

##### `Array.prototype.reverse()`

Reverses the order of all the items in the array.

```javascript
[1,2,3].reverse();
```

Returns `[3,2,1]`.

##### `Array.prototype.concat()`

Combines two arrays, putting the items from the array in the parenthesis to the end of the main array. This method is a lot faster than grabbing each item by their index and adding them using the `.push()` method.

```javascript
['a','b','c'].concat([1,2,3]);
```

Returns `['a','b','c',1,2,3]`.

##### `Array.prototype.join()`

Converts the array into a string, with each item seperated by whatever is in the parenthesis. Useful for telling the user the items in their inventory, for example.

```javascript
var inventory = ['books','apples','pencils'];
console.log("You have " + inventory.join(", ") + " in your inventory.");
```

Logs `"You have books, apples, pencils in your inventory."`

##### `Array.prototype.indexOf()`

Similar to String.prototype.indexOf(), it returns the index of the item inside the parenthesis.

```javascript
['chicken','pizza','tacos'].indexOf('tacos');
```

Returns `2`.

### Objects

Objects are like arrays, however they’re easier for establishing the relationship between properties and their values. You can store any data type as a property of an object.

```javascript
var player = {};
player.name = "Brandon";
player.health = Number.POSITIVE_INFINITY;
console.log(player.name + " has " + player.health + " health.");
```

Logs `"Brandon has Infinity health"`. Yup that sounds about right.

### Conclusion

All of the different data types in Javascript are tools for you to get the job done. When assigning a variable, think to yourself which tool you should use. I had fun doing this lecture. We finished earlier than expected, due to my extra preparations. (Still shuddering over my unpreparedness from last week). We had finished so early in fact, that I went ahead and started teaching next week's material. Do not worry though, my lovely readers only get the most structured of lesson materials. So you'll have to wait until next week to hear more. 🙂