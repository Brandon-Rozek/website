---
title: "Cursed Knowledge: Javascript Arrays Are Objects"
date: 2025-09-01T09:47:01-04:00
draft: false
tags: []
math: true
medium_enabled: false
---

My friend Ethan recently wrote a blog post on [cursed commands](https://emar10.dev/posts/cursed-commands-part-1/). Chris shared with me that Immich has a page on their site called [cursed knowledge](https://immich.app/cursed-knowledge/), and it looks like this has started a trend. I've seen my fair share of the dark arts in programming, so I'll hop on and share what I know about JavaScript arrays.

JavaScript arrays are [*exotic objects*](https://262.ecma-international.org/#sec-array-exotic-objects) according to the ECMAScript specification. Therefore, they may lead to unintuitive behavior if we think of these arrays as C-like.

Let's play around.

### Concept 1: JavaScript arrays are not continguous

First, consider the following array:

```javascript
let x = [0, 1, 2];
```

As one might expect, `x.length` is equal to `3`. To tell whether or not an index is in an array, we can use the `in` operator.

```javascript
3 in x // Evaluates to false
```

If we try to access the 3rd index, the result will evaluate to `undefined`.

```javascript
x[3] // Evaluates to undefined
```

Now let's assign an element to the 4th index. Keep in mind that we're skipping over the 3rd one.

```javascript
x[4] = 4;
```

Now when we check our `length` property, it'll say that our array is now of size `5`.

```javascript
x.length // Evaluates to 5
```

However, the 3rd index still does not exist

```javascript
3 in x // Evaluates to false
```

### Concept 2: Explicit vs Implicit `undefined`

Recall that `x[3]` evaluates to `undefined`. What happens when we set the value explicitly?

```javascript
x[3] = undefined;
3 in x // Evaluates to true
```

So there is a difference on whether we have explicitly set an index to `undefined`! This distinction is not always used. For example, our trusty for-of loop does not care.

```javascript
x = [0, 1, 2];
x[4] = 4;
for (a of x) {
    console.log(a)
}
```

Will print out

```
0
1
2
undefined
4
```

### Concept 3: Indices are actually strings

Given that we have a length property and that we've been indexing with numeric keys, it must mean that arrays have numeric indices. Right?

```
"0" in ["a", "b"] // Evaluates to true
```

Okay, it looks like there's some conversion magic that's happening behind the scenes here. The ECMAScript specification says that an array index must be strictly less than $2^{32}$. So what happens if it is not?

```javascript
let x = [0];
x[4294967296] = true
x // Evaluates to [ 0, '4294967296': true ]
```

It looks like it no longer gets treated as an array item, but instead treats it as an arbitrary key-value pair. Why stop there, this must mean that we can store any sort of arbitrary data in our array.

```javascript
x.name = "Brandon"
x // Evaluates to [ 0, '4294967296': true, name: 'Brandon' ]
```

### Viewing arrays as objects

Now everything starts to make more sense when we think of these arrays as objects.

```javscript
let x = [0, 1, 2];
x[4] = 4;
```

Internally, this corresponds to the object:

```javascript
{
    "0": 0,
    "1": 1,
    "2": 2,
    "4": 4
}
```

From this object, we can see that the keys are strings and that the 3rd key is not in the object. Now let's see what happens when we explicitly set `x[5] = undefined`.

```javascript
{
  "0": 0,
  "1": 1,
  "2": 2,
  "4": 4,
  "5": undefined
}
```

The 5th key is now in our object and it's set to an undefined value. We also get an undefined value when we try to retrieve a value of a key that is not in our object.

The length of our array is the highest "numeric" key within our object (subject to the size limit). When we iterate over our array using `for-of`, we're iterating from `"0"` to our length.

```javascript
for (a of x) {
    console.log(a);
}
```

Is the same as:

```javascript
console.log(x[0]);
console.log(x[1]);
console.log(x[2]);
console.log(x[3]);
console.log(x[4]);
console.log(x[5]);
```

That's an exotic object for you.

