---
title: "Progressive Enhancement of Page Transitions in Hugo with htmx"
date: 2023-07-21T19:31:43-04:00
draft: false
tags: []
math: false
medium_enabled: false
---

Progressive Enhancement is a philosophy that places emphasis on making sure that a website's content is available to everyone. Additional functionality, such as JavaScript interactivity, are viewed as a nicety. This idea became popular around the time period when many news websites would show a blank screen if JavaScript was disabled.

However without JavaScript, transitioning between pages can flash a white screen in between. This can be jarring for websites using a non-white background. Single page applications attempt to resolve this by requesting webpages via JavaScript and dynamically reshuffling the page.

Pjax is a technique designed to marry these two ideas. [The name Pjax stands for `pushState` + `Ajax`](https://gander.wustl.edu/~wilson/store/yui/docs/pjax/index.html). The idea is that when a person clicks a link, instead of the browser loading an entirely new page, the local  JavaScript would issue an Ajax request. Once the request is fulfilled it would replace hte current screen contents with the request and update the browser's history via a `pushState`. Browsers that don't support this feature will result in a normal full page load when the link is clicked.

Over the years several JavaScript libraries have popped up to fill this need. There was the classic [`pjax`](https://clarle.github.io/yui3/yui/docs/pjax/) library which handled this. Then [`intercooler.js`](https://intercoolerjs.org/) came around to allow you to specify Ajax requests via HTML attributes. Finally, [`htmx`](https://htmx.org/) extends these HTML attributes beyond Ajax and into CSS transitions and WebSockets.

This post will show how you can use `htmx` to easily create page transitions in a progressively enhanced way.  The quickest way to achieve this is with an attribute called `hx-boost`. This can be used by `<a>` tags in HTML for links and `<form>` tag for form submissions. By default, these two HTML elements will issue a full page load to a new URL once they are clicked. However with `hx-boost`, it will replace the full page load with a `ajax` request and replace the `innerHTML` of the HTML node's contents with the response.

Another nice feature of `htmx` is that we don't need to add `hx-boost` for every HTML node. Instead, this attribute can be *inherited*. This allows us to put `hx-boost="true"` on the body of the document and every form and link will be boosted. If we want to simulate a page transition, instead of replacing the inner HTML of the link or form, we can replace the entire inner HTML of the body of the document using `hx-indicator`.

```html
<body hx-boost="true" hx-indicator="body">
   
</body>
```

Though we have to do a little more work if we want a smooth page transition. HTMX uses classes to denote the [lifecycle of the request](https://htmx.org/docs/#request-operations). When an element sends off a request is, the `htmx-request` class is added to whichever node is spcified in `hx-indicator` (itself by default).  We can use this to have a simple fade out transition in the beginning of the request.

```css
.htmx-request {
  opacity: 0;
  transition: opacity 200ms ease-in;
}
```

Once the AJAX request is satisfied, the `htmx-request` class is replaced with `htmx-swapping` to indicate that the content is about to be replaced. 

```css
.htmx-swapping {
  opacity: 0;
}
```

[Unless a swap delay is specified](https://htmx.org/attributes/hx-swap/), the content is then quickly replaced which then puts the node in a settled state. This is when we should fade in to see the new content

```css
.htmx-settling {
  opacity: 1;
  transition: opacity 200ms ease-in;
}
```

Using the htmx library, we can have nice page transitions with one line of HTML code, an optional 11 lines of CSS, and zero lines of custom JavaScrpt code. The small transitions are especially nice in low-bandwidth scenarios when a response to an ajax request isn't immediately received. It gives some visual indication that clicking the link still did something.

