---
id: 238
title: Javascript Data Types
date: 2015-10-10T20:01:20+00:00
author: Brandon Rozek
layout: post
guid: https://brandonrozek.com/?p=238
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
tumblr_post_id:
  - "135657462089"
  - "135657462089"
kind:
  - article
tags: ["Web", "JS"]
---
Javascript has multiple ways you can store your data. Each of these different ways is called a data type, and they each carry different “methods” which are helpful commands. Today, I’ll show you the different data types and methods that I use and how they’re useful.

<!--more-->

This post is by far not a comprehenive list of all the Data types and their methods. If you want one of those, please check out [MDN](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects) and/or [WebPlatform](http://docs.webplatform.org/wiki/javascript/objects){.broken_link}. This is the second lecture of the web development class I’m teaching for the newer folks over at [Math I/O](http://math-io.com). Due to the nature of Math I/O (making math games and all), the next few posts will be Javascript centric. We’re getting ready to build a new game, so I want to prepare them as much as possible. \*Excited\* ^_^ Ilya Kantor does a good job of descibing Javascript data types and their many methods in [Mastering Data Types](http://javascript.info/tutorial/mastering-data-types) which I made the recommended reading for this lecture.

### <a href="#string" name="string"></a>String {#string}

A string is one or more characters.

<pre><code class="language-javascript">var name = "Brandon";</code></pre>

You can access a character inside of a string by using [] notation. Inside the [] you put the index of the character you want. An index is the numeral location of the character starting from the left. It is important to note that Javascript starts counting from 0.

<table border="1">
  <tr>
    <td>
      B
    </td>

    <td>
      r
    </td>
    
    <td>
      a
    </td>
    
    <td>
      n
    </td>
    
    <td>
      d
    </td>
    
    <td>
      o
    </td>
    
    <td>
      n
    </td>
  </tr>

  <tr>
    <td>
    </td>
    
    <td>
      1
    </td>
    
    <td>
      2
    </td>
    
    <td>
      3
    </td>
    
    <td>
      4
    </td>
    
    <td>
      5
    </td>
    
    <td>
      6
    </td>
  </tr>
</table>

<pre><code class="language-javascript">var firstInitial = "Brandon"[0];</code></pre>

Now the value of firstInitial is the letter <code class="language-javascript">"B"</code>.

#### <a href="#some-useful-methods-for-strings" name="some-useful-methods-for-strings"></a>Some useful methods for strings {#some-useful-methods-for-strings}

##### <a href="#string.prototype.indexof();" name="string.prototype.indexof();"></a>String.prototype.indexOf(); {#string.prototype.indexof();}

This can be used to find the index of any character(s) in a string. I primarily use it for when I need to check if something exists in a string. Do I have a ‘z’ in my name?

<pre><code class="language-javascript">"Brandon".indexOf('z');</code></pre>

Nope, so Javascript will return a <code class="language-javascript">-1</code>. How about a ‘d’?

<pre><code class="language-javascript">"Brandon".indexOf('d');</code></pre>

Yes, Javascript will return <code class="language-javascript">5</code> which is the index of the letter ‘d’.

##### <a href="#string.prototype.replace();" name="string.prototype.replace();"></a>String.prototype.replace(); {#string.prototype.replace();}

The replace method can replace any character(s) with other character(s). For more complex replacing, look into [Regular Expression](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Guide/Regular_Expressions) and how you can use them in .replace(). Replace the first ‘n’ in my name with an ‘m’.

<pre><code class="language-javascript">
var modifiedName = "Brandon".replace('n', 'm');

console.log(modifiedName);
</code></pre>

Logs <code class="language-javascript">"Bramdon"</code>.

##### <a href="#string.prototype.touppercase();" name="string.prototype.touppercase();"></a>String.prototype.toUpperCase(); {#string.prototype.touppercase();}

This method returns the string with all the lowercase characters converted to uppercase and can be useful for when you’re checking user input and you don’t want to worry about different cases.

<pre><code class="language-javascript">"Brandon".toUpperCase();</code></pre>

Returns <code class="language-javascript">"BRANDON"</code>.

##### <a href="#string.prototype.tolowercase();" name="string.prototype.tolowercase();"></a>String.prototype.toLowerCase(); {#string.prototype.tolowercase();}

Same as above but instead of converting lowercase to uppercase, it converts uppercase to lowercase.

<pre><code class="language-javascript">"Brandon".toLowerCase();</code></pre>

Returns <code class="language-javascript">"brandon"</code>.

#### <a href="#a-couple-useful-escape-secquences" name="a-couple-useful-escape-secquences"></a>A couple useful escape secquences {#a-couple-useful-escape-secquences}

  * <code class="language-javascript">n</code> for newline.
  * <code class="language-javascript">t</code> for tab character.

You can also use escape sequnces if you want to add “” or ‘’ to your strings.

<pre><code class="language-javascript">
var greeting = "Hello "Brandon"";

console.log(greeting);
</code></pre>

Returns <code class="language-javascript">"Hello "Brandon""</code>.

### <a href="#number" name="number"></a>Number {#number}

Any number between -(2<sup>53</sup> – 1) and (2<sup>53</sup> – 1).

#### <a href="#number-methods" name="number-methods"></a>Number Methods {#number-methods}

Number methods are useful when trying to represent complex numbers.

##### <a href="#number.prototype.toexponential();" name="number.prototype.toexponential();"></a>Number.prototype.toExponential(); {#number.prototype.toexponential();}

Returns a string representing a number in exponential notation.

<pre><code class="language-javascript">77.1234.toExponential(2);</code></pre>

Returns <code class="language-javascript">"7.71e+1"</code>.

##### <a href="#number.prototype.tofixed();" name="number.prototype.tofixed();"></a>Number.prototype.toFixed(); {#number.prototype.tofixed();}

Returns a string representing a number fixed to x amount of decimal places.

<pre><code class="language-javascript">12345.6789.toFixed(1);</code></pre>

Returns <code class="language-javascript">"12345.7"</code>.

##### <a href="#number.prototype.toprecision();" name="number.prototype.toprecision();"></a>Number.prototype.toPrecision(); {#number.prototype.toprecision();}

Returns a string representing a number using x amount of significant figures.

<pre><code class="language-javascript">5.123456.toPrecision(2);</code></pre>

Returns <code class="language-javascript">"5.1"</code>.

#### <a href="#math-properties/methods" name="math-properties/methods"></a>Math properties/methods {#math-properties/methods}

In Javascript there is a Math object which contains many properties and methods which are useful for mathmatical calculations.

##### <a href="#return-euler's-constant" name="return-euler's-constant"></a>Return Euler’s constant {#return-euler's-constant}

<code class="language-javascript">Math.E</code> which returns ~2.718.

##### <a href="#return-the-natural-log-of-x" name="return-the-natural-log-of-x"></a>Return the natural log of x {#return-the-natural-log-of-x}

<code class="language-javascript">Math.log(x)</code>

##### <a href="#rise-x-to-the-y-power" name="rise-x-to-the-y-power"></a>Rise x to the y power {#rise-x-to-the-y-power}

<code class="language-javascript">Math.pow(x,y)</code>

##### <a href="#return-a-psuedo-random-number-[0,1)" name="return-a-psuedo-random-number-[0,1)"></a>Return a psuedo random number [0,1) {#return-a-psuedo-random-number-[0,1)}

<code class="language-javascript">Math.random()</code>

##### <a href="#round-x-to-the-nearest-integer" name="round-x-to-the-nearest-integer"></a>Round x to the nearest integer {#round-x-to-the-nearest-integer}

<code class="language-javascript">Math.round(x)</code>

### <a href="#boolean" name="boolean"></a>Boolean {#boolean}

Booleans are either <code class="language-javascript">true</code> or <code class="language-javascript">false and</code> are typically used in conditional statements. You can either create them explicitly

<pre><code class="language-javascript">var alive = true;</code></pre>

or by evaluating a [comparison](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Operators/Comparison_Operators).

<pre><code class="language-javascript">
var dead = false;
var isAlive = !dead;
</code></pre>

isAlive equals <code class="language-javascript">true</code>.

### <a href="#array" name="array"></a>Array {#array}

An array is a list of items. In Javascript these items can be any data type, even arrays themselves.

<pre><code class="language-javascript">var mixedBag = ['sword', 24, true, [Math.PI, Math.E], 'shield'];</code></pre>

To access an item in an array use [] notation with an index as mentioned over at strings.

<pre><code class="language-javascript">['sword', 'shield', 'helmet'][1];</code></pre>

Returns <code class="language-javascript">'shield'</code>. to figure out how many items are in the array.

<pre><code class="language-javascript">
var inventory = ['boots', 'gloves', 'pants', 'shirt'];
var inventoryAmt = inventory.length;
</code></pre>

inventoryAmt is <code class="language-javascript">4</code> since there are 4 items in inventory.

#### <a href="#array-methods" name="array-methods"></a>Array Methods {#array-methods}

##### <a href="#array.prototype.push();" name="array.prototype.push();"></a>Array.prototype.push(); {#array.prototype.push();}

Adds whatever is inside the parenthesis to the end of the array. Great for adding items to a list. For example, test scores.

<pre><code class="language-javascript">[100,92,95].push(80);</code></pre>

Returns <code class="language-javascript">[100,92,95,80]</code>.

##### <a href="#array.prototype.reverse();" name="array.prototype.reverse();"></a>Array.prototype.reverse(); {#array.prototype.reverse();}

Reverses the order of all the items in the array.

<pre><code class="language-javascript">[1,2,3].reverse();</code></pre>

Returns <code class="language-javascript">[3,2,1]</code>.

##### <a href="#array.prototype.concat();" name="array.prototype.concat();"></a>Array.prototype.concat(); {#array.prototype.concat();}

Combines two arrays, putting the items from the array in the parenthesis to the end of the main array. This method is a lot faster than grabbing each item by their index and adding them using the .push() method.

<pre><code class="language-javascript">['a','b','c'].concat([1,2,3]);</code></pre>

Returns <code class="language-javascript">['a','b','c',1,2,3]</code>.

##### <a href="#array.prototype.join();" name="array.prototype.join();"></a>Array.prototype.join(); {#array.prototype.join();}

Converts the array into a string, with each item seperated by whatever is in the parenthesis. Useful for telling the user the items in their inventory, for example.

<pre><code class="language-javascript">
var inventory = ['books','apples','pencils'];
console.log("You have " + inventory.join(", ") + " in your inventory.");
</code></pre>

Logs <code class="language-javascript">"You have books, apples, pencils in your inventory."</code>

##### <a href="#array.prototype.indexof();" name="array.prototype.indexof();"></a>Array.prototype.indexOf(); {#array.prototype.indexof();}

Similar to String.prototype.indexOf(), it returns the index of the item inside the parenthesis.

<pre><code class="language-javascript">['chicken','pizza','tacos'].indexOf('tacos');</code></pre>

Returns <code class="language-javascript">2</code>.

### <a href="#objects" name="objects"></a>Objects {#objects}

Objects are like arrays, however they’re easier for establishing the relationship between properties and their values. You can store any data type as a property of an object.

<pre><code class="language-javascript">
var player = {};
player.name = "Brandon";
player.health = Number.POSITIVE_INFINITY;
console.log(player.name + " has " + player.health + " health.");
</code></pre>

Logs <code class="language-javascript">"Brandon has Infinity health"</code> Yup that sounds about right.

### <a href="#conclusion" name="conclusion"></a>Conclusion {#conclusion}

All of the different data types in Javascript are tools for you to get the job done. When assigning a variable, think to yourself which tool you should use. I had fun doing this lecture. We finished earlier than expected, due to my extra preparations. (Still shuddering over my unpreparedness from last week). We had finished so early in fact, that I went ahead and started teaching next week&#8217;s material. Do not worry though, my lovely reader&#8217;s only get the most structured of lesson materials. So you&#8217;ll have to wait until next week to hear more. 🙂