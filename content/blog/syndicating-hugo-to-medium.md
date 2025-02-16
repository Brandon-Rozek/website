---
title: "Syndicating Hugo Posts to Medium"
date: 2023-05-17T21:28:55-04:00
draft: false 
tags: ["Hugo"]
math: false
medium_enabled: false
---

*Warning: This work was done prior to the deprecation of the Medium API. I'm unsure how much longer the contents of this post will be relevant. Regardless, the ideas in this post can be adapted to other syndication systems of Hugo content.*

I wrote a script that can selectively upload blog posts generated from a Hugo website onto Medium. This post will go into further detail each of the following steps that make it happen:

- Creating labels on the YAML frontmatter
- Outputting a JSON feed to make it easier to create scripts
- Writing a python script to ingest the JSON feed and upload new specified posts onto Medium
- Updating the YAML frontmatter with information from Medium

**Step 1 Define Labels:** This advice not only goes for Medium but any other site you want to syndicate to. Within each of the content files within Hugo, there's generally a frontmatter section that holds the metadata such as title, date, and tags. Within the YAML frontmatter, I created two new fields:

- medium_enabled: Whether or not I want this post to be uploaded to Medium
- medium_post_id: The post identifier used within Medium, empty if non-existent.

We don't need to include these two new fields in every new post we create. Instead in Step 2, we'll consider some sane defaults. Though it could be useful to include some default values within the [archetype](https://gohugo.io/content-management/archetypes/) file so that you don't forget they exist.

For example:`themes/themeName/archetypes/default.md`

```yaml
---
title: "{{ replace .TranslationBaseName "-" " " | title }}"
date: {{ dateFormat "2006-01-02T15:04:05Z07:00" .Date }}
draft: true
tags: []
medium_enabled: false
---
```

**Step 2 Setup JSON Feed:** Following the [Hugo template system](https://gohugo.io/templates/), I created a `item.json.json`, `list.json.json`, and `single.json.json`. For this post, the first two are important.

`list.json.json`

```json
{
    "version": "https://jsonfeed.org/version/1.1",
    "title": "{{ if eq  .Title  .Site.Title }}{{ .Site.Title }}{{ else }}{{ with .Title }}{{.}} | {{ end }}{{ .Site.Title }}{{ end }}",
    "home_page_url": "{{ .Site.BaseURL }}",
    "feed_url": "{{ .Permalink }}",
    "description": "{{ .Description }}",
    "icon": "{{ .Site.BaseURL }}img/{{ .Site.Params.avatar }}",
    "language": "en-US",
    "authors": [
        {{with $.Site.Params.name }}
            { "name": "{{ . }}" }
        {{ end }}
    ],
    "items": [
        {{ range $index, $page := .Pages }}{{ if ne $index 0 }},{{ end }}
            {{ .Render "item"}}
        {{ end }}
    ]
}
```

My `list.json.json` follows the [JSON Feed](https://jsonfeed.org/) specification. The idea here is that this file will contain a list of blog posts within the `items` attribute. For each item, we have the next template file that defines how it's structured.

`item.json.json`

```json
{
    "id": "{{ .Permalink }}",
    "url": "{{ .Permalink }}",
    "title": {{ .Title | jsonify }},
    "authors": [
        {{with $.Site.Params.Author }}
            { "name": "{{ . }}" }
        {{ end }}
    ],
    "content_html": {{ .Content | jsonify }},
    "date_published": "{{ .Date.Format "2006.01.02" }}",
    "tags": {{ .Params.tags | jsonify }},
    "_syndication": {
        "medium": {
            "enabled": {{ .Params.medium_enabled | default "false" }},
            "post_id": {{ .Params.medium_post_id | jsonify }}
        }
    }
}
```

Notice the `_syndication` attribute. Attributes beginning with an underscore are ignored by JSON feed readers. Within this attribute, we can store our `enabled` and `post_id` attributes. If the post does not specify the relevant attributes in the frontmatter YAML, we'll assume `false` for `enabled` and `null` to for `post_id`.

Finally for this step we need to tell Hugo to generate this JSON feed. Within your website's `config.toml`:

```toml
# ...

[outputFormats.json]
  name = "json"
  mediaType = "application/feed+json"
  baseName = "index"
  isPlainText = false
  rel = "alternate"
  isHTML = false
  noUgly = true
  permalinkable = false

[outputs]
    section = ["json", "html", "rss"]
	# ...
```

**Step 3 Ingest Feed and Syndicate via External Script:** Now that we can store the metadata on whether or not we want to syndicate a particular post and its relevant medium id if it has already been, we can create an external script that ingests this data and uploads if necessary.

We'll use Python for this task. The core loop of the file will look like the following:

```python
# Generate the necessary feed files
subprocess.run(['hugo'], check=True)

# Grab blog's feed
data = ""
with open("public/blog/index.json", "r", encoding="UTF-8") as feed_file:
    data = feed_file.read()
feed_data = json.loads(data)

# Go through each post and check syndication status
for post in feed_data['items']:
    medium_enabled = post['_syndication']['medium']['enabled']
    medium_post_id = post['_syndication']['medium']['post_id']
    if medium_enabled and medium_post_id is None:
        # Syndicate.....
        medium_result = syndicate_post(post)
        update_front_matter(post, medium_result)
        time.sleep(60) # Throttle to not hit rate limit
```

The last couple steps were necessary for Hugo to produce the JSON feed needed which contains the appropriate syndication fields. Now the magic is within the `syndicate_post` method.

For the magic we need to make use of the [Medium API](https://github.com/Medium/medium-api-docs). You'll need to know both your `access token` and your `authorId`. Your author id can be displayed publically, for example mine is `18bad95d2020608a45ef502ef0db83d2cad2e28886d8d3eeef71a6bd089fc2a4e`. However, your access token must be kept private. Otherwise, others can impersonate you. For my script, I put my access token within a secret file that I don't commit to the repository.

```python
# Grab secret
medium_secret = ""
with open("secrets/medium.secret", "r") as secret_file:
    medium_secret = secret_file.read().strip()
```

The secret is used within the request headers

```python
request_headers = {
        "Host": "api.medium.com",
        "Authorization": f"Bearer {medium_secret}",
        "Content-Type": "application/json",
        "Accept": "application/json",
        "Accept-Charset": "utf-8",
}
```

Following the API documentation we then create a JSON object that represents our new blog post with its corresponding metadata.

```python
# Structure API Request
blog_post = dict(
    title=post['title'],
    contentFormat="html",
    content=post['content_html'],
    tags=post['tags'],
    canonicalUrl=post['url'],
    publishStatus="public",
    license="all-rights-reserved",
    notifyFollowers=False
)
```

You're welcome to change the publish status, license, and follower notification as you see fit. Afterwards, following the API documentation we send a `POST` request to the Medium API

```python
# Send Request
conn = HTTPSConnection("api.medium.com")
conn.request(
    "POST",
    f"/v1/users/{AUTHOR_ID}/posts",
    json.dumps(blog_post).encode("utf-8"),
    request_headers
)
```

We'll need to hold onto the response from the website as that'll contain our post id.

```python
# Check and parse response
response = conn.getresponse()
if response.status != 201:
    raise Exception(f"Medium API rejected the request with response code {response.status}")
medium_response = json.loads(response.read().decode('utf-8'))
conn.close()
```

**Step 4 Update Frontmatter:** Now that we have the post id within the Medium response, we can look towards the original markdown file that contains our content and modify the frontmatter so that the `medium_post_id` field is populated.

First we need to get the appopriate markdown file

```python
# Figure out the file path of the post
ORIG_URL = urlparse(post['id'])
file_path = "content" + ORIG_URL.path[:-1] + ".md"
```

Using the [Frontmatter](https://pypi.org/project/frontmatter/) Python library, we can read the existing YAML frontmatter and edit the post id with what we received from Medium

```python
# Read existing frontmatter and edit the post id
item = {}
with open(file_path, "r", encoding="UTF-8") as content_file:
    item = frontmatter.load(content_file)
    item['medium_post_id'] = medium_data['data']['id']
```

The library also helps us edit the file with updated fronmatter

```python
# Write out new frontmatter
with open(file_path, "w", encoding="UTF-8") as content_file:
    content_file.write(frontmatter.dumps(item))
```

**Conclusion:** This constitutes my somewhat generic framework for how you can selectively syndicate content within a Hugo website. To summarize, we do this by keeping track of the syndication through frontmatter additions and a JSON feed. We then created an external script that ingests this feed and syndicates if necessary, finally updating the original frontmatter with the server response.

Downsides to this approach is that the external script occurs outside of the `hugo` call. This adds an extra layer of complication when managing your website. However, keeping it all within Hugo is not only difficult but inflexible. The way I envision this is that Hugo is a database of sorts that keeps track of the syndication status and external scripts operates over this database.

How do you go about syndicating content to other websites? Is your approach different from mine? Please get in touch and share :)

Relevant files from my website repository:

- https://github.com/Brandon-Rozek/website/blob/52b47f1311e7bf98b97c69bd0e838d8e3cdf8392/scripts/syndicate_medium.py
- https://github.com/Brandon-Rozek/website/blob/52b47f1311e7bf98b97c69bd0e838d8e3cdf8392/config.toml
- https://github.com/Brandon-Rozek/website-theme/blob/fb42d6b950b1d7752e199dc16fd0d39292a16c93/layouts/_default/item.json.json
- https://github.com/Brandon-Rozek/website-theme/blob/fb42d6b950b1d7752e199dc16fd0d39292a16c93/layouts/_default/list.json.json
