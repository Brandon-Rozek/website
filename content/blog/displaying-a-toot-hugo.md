---
title: "Displaying a Toot in Hugo"
date: 2022-05-20T16:57:11-04:00
draft: false
tags: ["Hugo"]
math: false
---

Mastodon for me is a nice friendly place and I enjoy participating in that community. With that, I want to be able to share the great toots out there in my own website as well as keep an archive of all the toots I made. This post will go over the code I wrote in Hugo to display a single toot into a blog post.

Example toot:

{{< displayToot fosstodon-org-108334900197768307 >}}

In this post, we will go over the following:

- [Mastodon API](#mastodon-api)
- [Displaying Toot](#displaying-toot)
- [Hugo Shortcode](#hugo-shortcode)
- [Archiving Toots](#archiving-toots)
- [Conclusion](#conclusion)

## Mastodon API

Before jumping into the code right away, it is good to understand how to query data from Mastodon. The Mastodon API is so friendly that for public toots, you don't even need an API key. The first thing we need to know is the toot id of the toot you are interested in. In my example above, the toot id is `108334900197768307`, you can get that by looking at the last string of numbers at the end of the toot URL. You can get the toot URL by clicking on "Copy link to post" in the three dot menu of the toot. Otherwise you can get it from the URL of the favorite and reblog button. Let's say the URL of the toot is the following:

```
https://fosstodon.org/@brozek/108334900197768307
```

Then the API endpoint to get the JSON representation is at:

```
https://fosstodon.org/api/v1/statuses/108334900197768307
```

In its most general form you'll need to know the server the toot came from and its id:

```
https://SERVER/api/v1/statuses/TOOTID
```

If you check out the example link, you'll see that the JSON returned is of the form:

{{< details "Expand JSON:">}}

```json
{
  "id": "108334900197768307",
  "created_at": "2022-05-20T15:09:50.226Z",
  "in_reply_to_id": "108331903834519586",
  "in_reply_to_account_id": "108219415927856966",
  "sensitive": false,
  "spoiler_text": "",
  "visibility": "unlisted",
  "language": "en",
  "uri": "https://fosstodon.org/users/brozek/statuses/108334900197768307",
  "url": "https://fosstodon.org/@brozek/108334900197768307",
  "replies_count": 0,
  "reblogs_count": 0,
  "favourites_count": 0,
  "edited_at": null,
  "content": "[Shortened for display purposes]",
  "reblog": null,
  "application": null,
  "account": {
    "id": "108219415927856966",
    "username": "brozek",
    "acct": "brozek",
    "display_name": "Brandon Rozek",
    "created_at": "2022-04-30T00:00:00.000Z",
    "note": "[Shortened for display purposes]",
    "url": "https://fosstodon.org/@brozek",
    "avatar": "https://cdn.fosstodon.org/accounts/avatars/.../c007afd0c6749859.png",
    "header": "https://fosstodon.org/headers/original/missing.png",
    "followers_count": 114,
    "following_count": 271,
    "statuses_count": 57,
    "last_status_at": "2022-05-20",
    "emojis": [ ],
    "fields": [ ]
  },
  "media_attachments": [],
  "mentions": [
    {
      "id": "106627708559095741",
      "username": "ashshuota",
      "url": "https://fosstodon.org/@ashshuota",
      "acct": "ashshuota"
    },
    {
      "id": "107584265842142303",
      "username": "technicalissues",
      "url": "https://fosstodon.org/@technicalissues",
      "acct": "technicalissues"
    }
  ],
  "tags": [],
  "emojis": [],
  "card": null,
  "poll": null
}
```

{{< /details >}}

Wow that's a lot of information that comes with a single toot! For the purposes of my simple toot displayer I will only focus on a few of the fields:

- `account.avatar`: Avatar image of tooter
- `created_at`:  Date toot was posted
- `media_attachments`: Images within the toot (if any)
- `url`: URL of toot
- `content`: Contents of toot

For sake of simplicity, let's ignore content warnings and boosts and revisit those in a future post.

## Displaying Toot

The following is the high level overview of our toots, complete with microformats2 metadata. 

```html
<article class="toot h-entry">
  <div rel="author" class="h-card p-author toot-avatar">
    <img class="u-photo" width=50 src="{{ .account.avatar }}"/>
    <span style="display: none;">{{ .account.display_name }}</span>
  </div>
  <p class="date">Tooted on
    <time class="dt-published" datetime='{{ .created_at }}'>
      {{ dateFormat "January 2, 2006 15:04" (time .created_at) }}
    </time>
  </p>
  <div class="e-content p-name">
    {{ .content | safeHTML }}
    <div class="toot-photos space-evenly">
      <!-- TODO -->
    </div>
  </div>
  <div class="toot-social">
    <!-- TODO -->
  </div>
</article>
```

We wrap the entire toot in an `h-entry` class. Then we begin by creating a div that contains the authors details such as their avatar. Afterwards, we display the date/time that the toot was made. Then we display the content of the toot and its images. Lastly, we display social interaction icons such as reply, favorite, and reblog.

To display the images we range over the media_attachments array and grab any image URLs and their descriptions:

```html
<div class="toot-photos space-evenly">
{{ range .media_attachments}}
{{ if eq .type "image" }}
  <img src="{{ .preview_url }}" alt="{{ .description }}"/>
{{ end }}
{{ end }}
</div>
```

For the interaction URLs notice the following pattern:

- Reply URL -> `https://SERVER/interact/TOOTID?type=reply`
- Favorite URL -> `https://SERVER/interact/TOOTID?type=favourite`
- Boost URL -> `https://SERVER/interact/TOOTID?type=reblog`

```html
<div class="toot-social">
  {{ $post_url := urls.Parse .url }}
  {{ $status_id := index (last 1 (split $post_url.Path "/")) 0 }}
  {{ $social_url := printf "%s://%s/interact/%s" $post_url.Scheme $post_url.Host $status_id }}
  {{ $reply_url := printf "%s?type=reply" $social_url }}
  {{ $favorite_url := printf "%s?type=favourite" $social_url }}
  {{ $boost_url := printf "%s?type=reblog" $social_url }}
  <span>
    <a class='fas fa-share' href="{{ $reply_url }}"></a>
      {{ .replies_count }}
  </span>
  <span>
    <a class='fas fa-retweet' href="{{ $boost_url }}"></a>
      {{ .reblogs_count }}
  </span>
  <span>
    <a class='fas fa-star' href="{{ $favorite_url }}"></a>
      {{ .favourites_count }}
  </span>
  <span>| Source: <a class="u-syndication" href="{{ .url }}">{{ .url }}</a></span>
</div>
```

## Hugo Shortcode

We can then stick this all into a shortcode so that I can easily embed a toot into a blog post!

Let's go with the format `{{ displayOnlineToot "https://fosstodon.org/@brozek/108334900197768307"}}`

We'll have to add the following contents to `theme/layouts/shortcodes/displayOnlineToot.html`:

{{< details "Show code:" >}}

```html
{{ $url := urls.Parse (.Get 0) }}
{{ $status_id := index (last 1 (split $url.Path "/")) 0 }}
{{ $api_url := printf "%s://%s/api/v1/statuses/%s" $url.Scheme $url.Host $status_id }}
{{ $dataJ := getJSON $api_url }}

{{ with $dataJ }}
{{ if ne .content "" }}
<article class="toot h-entry">
    <div rel="author" class="h-card p-author toot-avatar">
      <img class="u-photo" width=50 src="{{ .account.avatar }}"/>
      <span style="display: none;">{{ .account.display_name }}</span>
    </div>
    <p class="date">Tooted on <time class="dt-published" datetime='{{ .created_at }}'>{{ dateFormat "January 2, 2006 15:04" (time .created_at) }}</time></p>
    <div class="e-content p-name">
      {{ .content | safeHTML }}
      {{ if gt (len .media_attachments) 0 }}
      <div class="toot-photos space-evenly">
      {{ range .media_attachments}}
        {{ if eq .type "image" }}
        <img src="{{ .preview_url }}" alt="{{ .description }}"/>
        {{ end }}
      {{ end }}
      </div>
      {{ end }}
    </div>
    <a class="u-url" style="display: none">{{ .Permalink }}</a>
    {{ range .tags }}
    <a class="p-category" href="{{ .url }}" style="display: none;">{{ .name }}</a>
    {{ end }}
    <div class="toot-social">
        {{ $post_url := urls.Parse .url }}
        {{ $status_id := index (last 1 (split $post_url.Path "/")) 0 }}
        {{ $social_url := printf "%s://%s/interact/%s" $post_url.Scheme $post_url.Host $status_id }}
        {{ $reply_url := printf "%s?type=reply" $social_url }}
        {{ $favorite_url := printf "%s?type=favourite" $social_url }}
        {{ $boost_url := printf "%s?type=reblog" $social_url }}
        <span>
          <a class='fas fa-share' href="{{ $reply_url }}"></a>
          {{ .replies_count }}
        </span>
        <span>
          <a class='fas fa-retweet' href="{{ $boost_url }}"></a>
          {{ .reblogs_count }}
        </span>
        <span>
          <a class='fas fa-star' href="{{ $favorite_url }}"></a>
          {{ .favourites_count }}
        </span>
        <span>| Source: <a class="u-syndication" href="{{ .url }}">{{ .url }}</a></span>
    </div>
  </article>
{{ end }}
{{ end }}
```

{{< /details >}}

The beginning part of the shortcode converts the URL to the JSON endpoint of the toot. It then requests the resource and parses the JSON to display the toot like in the last section. With this, you can include the shortcode `displayOnlineToot` to any Hugo markdown post.

## Archiving Toots

With the setup above the Mastodon server will be queried and the toots created at build time. For a multitude of reasons, I prefer to archive the toot onto my own website and reference that during build time.

I wrote [a python script](https://github.com/Brandon-Rozek/website/blob/9947478c6c4e3f9f9f99c742c2c2287e51a98a29/archive_toot.py) that saves the JSON representation of the toot locally and returns `SERVER-TOOTID` which I can then use in another [shortcode that I called `displayToot`](https://github.com/Brandon-Rozek/pulp/blob/69eb3014056f0594a16a0417d8cd6b3b4cfc3750/layouts/shortcodes/displayToot.html).

## Conclusion

I'm happy to see that Mastodon doesn't make it difficult to query and parse data from their platform. Within one toot there are a lot of possibilities for its type. For example, it can be a reply, a boost, or include a content warning label. To quickly get the basics (which includes replies), I ignored many of the fields. I would like to come back to this in the future and explore how to design for the other cases as well.
