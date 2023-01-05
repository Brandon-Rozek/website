---
title: "Displaying Hikes with gpx.studio"
date: 2022-05-23T16:35:01-04:00
draft: false
tags: ["Hugo", "GPS"]
math: false
medium_enabled: true
---

As the weather gets warmer, I am starting to go on more hikes. Several people on their websites share a Strava embed which highlights a path taken during their workout. I believe as a community this has great potential for sharing our favorite hiking paths. I don't, however, want to rely on Strava to host my GPS data. Instead, we will showcase how to accomplish the same effect but with open technologies.

At the end of this post, we will achieve in creating an embed like the following:

{{< displayGPX "2022-05-18-Burden-Pond-Preserve.gpx" >}}

To get there, we will talk about:

- [Recording the Walk](#recording-the-walk)
- [Grabbing an embed](#grabbing-an-embed)
- [Shortcodes for website](#shortcodes-for-website)
- [Conclusion](#conclusion)

## Recording the Walk

My first requirement is that the route is recorded in an open source format. For this I chose GPX otherwise known as the GPS Exchange format. There are three types of messages that a GPX file can contain:

- **Waypoint**: A point of interested denoted by a latitude/longitude/altitude (LLA) and a time with a small note describing it.
- **Route**: An ordered list of LLA and time points used to denote a navigation from a start to end location.
- **Track**: An ordered list of frequent LLA and time points denoting a GPS feed.

Popular applications such as AllTrails and Strava allow you to export your activities as GPX files. These will generally contain the track information. A cool open source alternative application called [OSMTracker](https://wiki.openstreetmap.org/wiki/OSMTracker_(Android)) records track information as well as enabling an easy way to create waypoints.

## Grabbing an embed

To create the embed we will use a project called [gpx.studio](https://gpx.studio). It's a great [open source](https://github.com/gpxstudio/gpxstudio.github.io) project created by vcoppe on GitHub and built on top of [Mapbox](https://www.mapbox.com/) and [OpenStreetMap](https://www.openstreetmap.org/). If you end up using this application, consider providing a [donation](https://ko-fi.com/gpxstudio) to their developer to cover for some of the hosting and API costs.
Our next step is to upload the GPX file we recorded from our exercise onto our website and configure our webserver so that gpx.studio can access the file. I store my hikes in `data/tracks` and created the following Nginx rule:

```nginx
# Allow any application access
location /data/tracks {
  add_header Access-Control-Allow-Origin "*";
}
```

Next, go to the [gpx.studio about page](https://gpx.studio/about.html#embed) to enter in the URL in the embed section. It will then output the following HTML code to add to your website

```html
<iframe 
  src="https://gpx.studio/?state=%7B%22urls%22:%5B%22https%3A%2F%2Fbrandonrozek.com%2Fdata%2Ftracks%2F2022-05-18-Burden-Pond-Preserve.gpx%22%5D%7D&embed&distance"
  width="100%"
  height="500"
  frameborder="0"
  allowfullscreen>
   	<p><a href="https://gpx.studio/?state=%7B%22urls%22:%5B%22https%3A%2F%2Fbrandonrozek.com%2Fdata%2Ftracks%2F2022-05-18-Burden-Pond-Preserve.gpx%22%5D%7D"></a></p>
</iframe>
```

## Shortcodes for website

Notice that the URL structure follows a prescribed format. This means we can create a Hugo shortcode to  generate these iFrames for us! The embed shown earlier on this page was created using the following shortcode command:

&lbrace;&lbrace;< displayGPX "2022-05-18-Burden-Pond-Preserve.gpx" >&rbrace;&rbrace;	 

So what's the structure of the URLs? If we perform an URL decode on the IFrame URL we get the following: 

```
https://gpx.studio/?
	state={"urls":["https://brandonrozek.com/data/tracks/2022-05-18-Burden-Pond-Preserve.gpx"]}
	&embed&distance
```

We can then replace the URL in the array with the one that you'll use for your website. Since I'm sticking all my GPX files under https://brandonrozek.com/data/tracks, I only have to pass the filename into the shortcode which is stored under `layouts/shortcodes/displayGPX.html`.

```html
<!-- Grab the filename and append it to the base url -->
{{ $url := printf "%sdata/tracks/%s" .Site.BaseURL (.Get 0) }}
<!-- Make the state={...} URL friendly -->
{{ $url_state := querify "state" (printf "{\"urls\":[\"%s\"]}" $url) }}
<!-- Create the Iframe and A tag URLs -->
{{ $iframe_url := printf "https://gpx.studio/?%s&embed&distance" $url_state }}
{{ $a_url := printf "https://gpx.studio/?%s" $url_state }}
<!-- Output the IFrame -->
<iframe {{ printf "src=%q" $iframe_url | safeHTMLAttr }}
        width="100%"
        height="500"
        frameborder="0"
        allowfullscreen>
            <p><a {{ printf "href=%q" $a_url | safeHTMLAttr }}></a></p>
</iframe>
```

## Conclusion

With this we created a cool visual representation of GPX data on our own website built on top of open technologies. Since our routes are stored in GPX files, if gpx.studio was to go down, then we can likely find an alternative to plot the file for us. Gpx.studio is also built on top of OpenStreetMap, a great  long-standing community driven mapping project. 
