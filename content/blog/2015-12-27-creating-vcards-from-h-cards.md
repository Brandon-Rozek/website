---
id: 599
title: Creating vCards from h-cards
date: 2015-12-27T15:17:12+00:00
author: Brandon Rozek
layout: post
guid: https://brandonrozek.com/?p=599
aliases:
    - /2015/12/creating-vcards-from-h-cards/
permalink: /2015/12/creating-vcards-from-h-cards/
medium_post:
  - 'O:11:"Medium_Post":11:{s:16:"author_image_url";N;s:10:"author_url";N;s:11:"byline_name";N;s:12:"byline_email";N;s:10:"cross_link";N;s:2:"id";N;s:21:"follower_notification";N;s:7:"license";N;s:14:"publication_id";N;s:6:"status";N;s:3:"url";N;}'
  - 'O:11:"Medium_Post":11:{s:16:"author_image_url";s:74:"https://cdn-images-1.medium.com/fit/c/200/200/1*dmbNkD5D-u45r44go_cf0g.png";s:10:"author_url";s:32:"https://medium.com/@brandonrozek";s:11:"byline_name";N;s:12:"byline_email";N;s:10:"cross_link";s:2:"no";s:2:"id";s:12:"9eab6bd8e0e4";s:21:"follower_notification";s:3:"yes";s:7:"license";s:19:"all-rights-reserved";s:14:"publication_id";s:2:"-1";s:6:"status";s:6:"public";s:3:"url";s:74:"https://medium.com/@brandonrozek/creating-vcards-from-h-cards-9eab6bd8e0e4";}'
mf2_cite:
  - 'a:1:{s:6:"author";a:0:{}}'
tumblr_post_id:
  - "136059699334"
kind:
  - article
---
Microformats is semantic HTML used to convey metadata. Using an userscript, I can generate a vCard from the representative h-card of the page. The code for this is on this gist [here.](https://gist.github.com/brandonrozek/e0153b2733e947fa9c87)

<!--more-->

### Terminology

[Microformats](http://microformats.org/wiki/Main_Page) allows search engines, browsers, websites, or people like me to consume content on a site.

[H-card](http://microformats.org/wiki/h-card) is a type of microformat that serves as a contact card for people and organizations.

[vCard](https://en.wikipedia.org/wiki/VCard) is the standard for electronic business cards. They&#8217;re most likely used in your phone to store contacts.

Userscript is essentially JavaScript that runs in the [Greasemonkey](http://www.greasespot.net/) extension.

### What I&#8217;ll need

  * Microformat parser
  * Way to find the representative h-card
  * Way to generate a vCard from an h-card
  * The userscript itself

### Implementation

To keep everything in small [reusable components](https://en.wikipedia.org/wiki/Modular_programming), I created four different sections. Thankfully, [Glenn Jones](http://glennjones.net/) already wrote a JavaScript microformats parser called [microformat-shiv.](https://github.com/glennjones/microformat-shiv) It&#8217;s licensed with [MIT](https://tldrlegal.com/license/mit-license), so we can use it, yay!

Next, I need to find the representative h-card of the page. Following the [instructions](http://microformats.org/wiki/representative-h-card-parsing) on the microformats wiki, I wrote the following code.

<pre><code class="language-javascript">
/*
   representative-h-card - v0.1.0
   Copyright (c) 2015 Brandon Rozek
   Licensed MIT 
*/

/**
	Finds the representative h-card of the page
	[http://microformats.org/wiki/representative-h-card-parsing]
	@returns representative h-card if found, null otherwise
**/
var representativeHCard = function(hCards, url) {
	if (hCards.items.length == 0) {
		return null;
	} else if (hCards.items.length == 1 && urlsMatchURL(hCards.items[0], url)) {
		hCard = hCards;
		hCard.items = [hCards.items[0]];
		return hCard
	} else {
		for (var i = 0; i &lt; hCards.items.length; i++) {
			if (urlsMatchURL(hCards.items[i], url) && (uidsMatchURL(hCards.items[i], url) || relMeMatchURL(hCards, url))) {
				hCard = hCards;
				hCard.items = [hCards.items[i]];
				return hCard
			}

		}
	}
	return null;
}

var urlsMatchURL = function(hCard, url) {
	var urls = hCard.properties.url;
	if (typeof(urls) == "object") {
		for (var i = 0; i &lt; urls.length; i++) {
			if (new URL(urls[i]).toString() == new URL(url).toString()) {
				return true;
			}
		}
	}
	return false;
}
var uidsMatchURL = function(hCard, url) {
	var uids = hCard.properties.uid;
	if (typeof(uids) == "object") {
		for (var i = 0; i &lt; uids.length; i++) {
			if (new URL(uids[i]).toString() == new URL(url).toString()) {
				return true;
			}
		}
	}
	return false;
};
var relMeMatchURL = function(microformats, url) {
	var me = microformats.rels.me;
	if (typeof(me) == "object") {
		for (var i = 0; i &lt; me.length; i++) {
			if (new URL(me[i]).toString() == new URL(url).toString()) {
				return true;
			}
		}
	}
	return false;
}
</code></pre>

Next up, is making the vCard. For this, I had to look at the [vCard 4.0 specification](https://tools.ietf.org/html/rfc6350) to figure out what the property names and values are. Then I browsed around different <a href="http://indieweb.thatmustbe.us/" rel="nofollow">sites</a> (takes you to a random [Indieweb](https://indiewebcamp.com/) site)  to figure out which properties are the most common.

The properties I ended up adding to the vCard.

  * name
  * photo
  * telephone numbers
  * URLs
  * [IMPPs](https://en.wikipedia.org/wiki/Instant_Messaging_and_Presence_Protocol) (Instant Messaging and Presence Protocol)
  * emails
  * roles
  * categories
  * notes

 As I was browsing around, I noticed that a few people would have empty values for certain properties on their h-card. To avoid having this show up on the vCard, I added a filter that takes out empty strings.

<pre><code class="language-javascript">
/*
   vCard-from-h-card - v0.1.0
   Copyright (c) 2015 Brandon Rozek
   Licensed MIT 
*/
var makeVCard = function(hCard) {
	var vCard = "BEGIN:VCARDnVERSION:4.0n";

	//Add full name
	var name = hCard.items[0].properties.name;
	if (typeof(name) == "object") {
		name.removeEmptyStrings();
		for (var i = 0; i &lt; name.length; i++) {
			vCard += "FN: " + name[i] + "n";
		}
	}
	
	//Add photo
	var photo = hCard.items[0].properties.photo;
	if (typeof(photo) == "object") {
		photo.removeEmptyStrings();
		for (var i = 0; i &lt; photo.length; i++) {
			vCard += "PHOTO: " + photo[i] + "n";
		}
	}
	
	//Add phone number
	var tel = hCard.items[0].properties.tel;
	if (typeof(tel) == "object") {
		tel.removeEmptyStrings();
		for (var i = 0; i &lt; tel.length; i++) {
			try {
				if (new URL(tel[i]).schema == "sms:") {
					vCard += "TEL;TYPE=text;VALUE=text: " + new URL(tel[i]).pathname + "n";
				} else {
					vCard += "TEL;TYPE=voice;VALUE=text: " + new URL(tel[i]).pathname + "n";
				}
			} catch(e) {
				vCard += "TEL;TYPE=voice;VALUE=text: " + tel[i] + "n";
			}
		}
	}
	
	//Add URLs
	var url = hCard.items[0].properties.url;
	if (typeof(url) == "object") {
		url.removeEmptyStrings();
		for (var i = 0; i &lt; url.length; i++) {
			vCard += "URL: " + url[i] + "n";
		}
	}
	
	var impp = hCard.items[0].properties.impp;
	//Add IMPP (Instant Messaging and Presence Protocol)
	if (typeof(impp) == "object") {
		impp.removeEmptyStrings();
		for (var i = 0; i &lt; impp.length; i++) {
			vCard += "IMPP;PREF=" + (i + 1) + ": " + impp[i] + "n";
		}
	}
	
	//Add emails
	var email = hCard.items[0].properties.email;
	if (typeof(email) == "object") {
		email.removeEmptyStrings();
		for (var i = 0; i &lt; email.length; i++) {
			try {
				vCard += "EMAIL: " + new URL(email[i]).pathname + "n";
			} catch (e) { 
				vCard += "EMAIL: " + email[i] + "n" 
			}		
		}
	}
	
	//Add roles
	var role = hCard.items[0].properties.role;
	if (typeof(role) == "object") {
		role.removeEmptyStrings();
		for (var i = 0; i &lt; role.length; i++) {
			vCard += "ROLE: " + role[i] + "n";
		}
	}
	
	//Add Organizations
	var org = hCard.items[0].properties.org;
	if (typeof(org) == "object") {
		org.removeEmptyStrings();
		for (var i = 0; i &lt; org.length; i++) {
			vCard += "ORG: " + org[i] + "n";
		}
	}
	
	//Add Categories
	var category = hCard.items[0].properties.category; 
	if (typeof(category) == "object") {
		vCard += "CATEGORIES: " + category.removeEmptyStrings().join(",") + "n";
	}
	
	//Add notes
	var note = hCard.items[0].properties.note;
	if (typeof(note) == "object") {
		note.removeEmptyStrings();
		for (var i = 0; i &lt; note.length; i++) {
			vCard += "NOTE: " + note[i] + "n";
		}
	}
	
	return vCard + "END:VCARD";

}

Array.prototype.removeEmptyStrings = function() {
	return this.filter(function(i) { return i !== "" })
}

</code></pre>

Now for the final part, making the userscript. Inspired by [Ryan Barret](https://snarfed.org/) and his userscript [Let&#8217;s Talk,](https://github.com/snarfed/misc/blob/master/userscripts/lets_talk.user.js) this userscript brings all of the above modules together. First it grabs the microformats from the page using microformat-shiv.

For some reason, when I tried filtering it by &#8216;h-card&#8217; it froze my computer. So I wrote my own little filter instead.

After I grab the representative h-card from the page using the little module I wrote, I generated a vCard. With the vCard generated, I set up a little HTML and CSS to display the link in the top left corner of the screen.

The link is actually a [data uri](https://developer.mozilla.org/en-US/docs/Web/HTTP/data_URIs) that has all of the information of the vCard encoded in it. Depending on your browser, once you click the link you might have to hit CTRL-S to save.

<pre><code class="language-javascript">
/*
   show-vCard - v0.1.0
   Copyright (c) 2015 Brandon Rozek
   Licensed MIT 
*/
var filterMicroformats = function(items, filter) {
	var newItems = [];
	for (var i = 0; i &lt; items.items.length; i++) {
		for (var k = 0; k &lt; items.items[i].type.length; k++) {
			if (filter.indexOf(items.items[i].type[k]) != -1) {
				newItems.push(items.items[i]);
			}
		}
	}
	items.items = newItems;
	return items;
}
var render = function() {
	var hCards = filterMicroformats(Microformats.get(), ['h-card']);
	var person = representativeHCard(hCards, location.origin);
	if (person == null) {
		return;
	}

	var node = document.createElement("div");
	node.setAttribute("class", "lt");
	
	var link = "&lt;a href="text/vcf;base64," + btoa(makeVCard(person))+ "" target="_blank">vCard&lt;/a>";
	var style = " 
			.lt { 
				position: absolute; 
				left: 24px; 
				top: 0; 
				color: #DDD; 
				background-color: #FFD700; 
				z-index: 9999; 
				border-width: medium 1px 1px; 
				border-style: none solid solid; 
				border-color: #DDD #C7A900 #9E8600; 
				box-shadow: 0px 1px rgba(0, 0, 0, 0.1), 0px 1px 2px rgba(0, 0, 0, 0.1), 0px 1px rgba(255, 255, 255, 0.34) inset; 
				border-radius: 0px 0px 4px 4px; 
		        } 
			.lt a { 
				padding: .5rem; 
			 	color: #8f6900; 
			 	text-shadow: 0px 1px #FFE770; 
				border: medium none; 
			} 
		     ";
	
	node.innerHTML = link + style;
	document.body.appendChild(node);	
}
document.addEventListener("DOMContentLoaded", function() {
	render();
});
</code></pre>

Sadly, I have no way of controlling the file name when you save it so you&#8217;ll have to manually rename it to something more meaningful than a random string of characters. Also remember to add the extension &#8216;.vcf&#8217; for it to be recognized by some devices.

### Conclusion

Fire up your favorite userscript handling tool and add the [script](https://gist.github.com/brandonrozek/e0153b2733e947fa9c87) in! Of course, since it&#8217;s pure JavaScript, you can also add it to your own site to serve the same purpose.

I ran into a small problem loading a contact onto my Android 5.0.2 phone. Apparently, they don&#8217;t support vCard 4.0 yet so I had to go into the file and change the line that says &#8220;VERSION 4.0&#8221; to &#8220;VERSION 3.0&#8221; which then allowed me to import the file into my contacts.

As with all the code I write, feel free to comment/criticize. I love hearing feedback so if you spot anything, [contact me](mailto:hello@brandonrozek.com) 🙂

Also posted on [IndieNews](http://news.indiewebcamp.com/en){.u-syndication}