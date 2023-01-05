---
title: "Archiving Toots"
date: 2022-05-20T22:47:48-04:00
draft: false
tags: ["Hugo", "Mastodon", "Archive"]
math: false
medium_enabled: true
---
In the spirit of [syndicating Mastodon toots](/blog/why-i-pesos-from-mastodon/)
to my own site, I wrote a Python script that turns toots into Hugo markdown
files.

In this post we'll go over:
- [Mastodon API](#mastodon-api)
- [Reformatting Toot](#reformatting-toot)
- [Creating the Markdown files](#creating-the-markdown-files)
- [Conclusion](#conclusion)

## Mastodon API
Before we can retrieve our toots, we need to know what user id of our account.
James Cahill wrote a very clean [web tool](https://prouser123.me/mastodon-userid-lookup/)
to grab your user id. For the sake of example, we'll use mine which
is 108219415927856966.

To grab the statuses, we then need to access the following URL:
```
https://SERVER/api/v1/accounts/USERID
```
For my specific user:
```
https://fosstodon.org/api/v1/accounts/108219415927856966
```

By default, this will return 20 statuses in an array.
To see how to parse each individual status, check out my
post on [displaying a single toot](/blog/displaying-a-toot-hugo/).

You can use the limit parameter to set how many statuses you wish to see.
The maximum number you can set it to is 40.

In order to see more than the last 40 toots, there is another
parameter that we can use called `max_id` which will specify the maximum
toot id to respond with.
You can then use this parameter to grab all your toots, by
following the following algorithm:
- Make an initial query to the API
- Find the smallest toot id in the response
- While the response is not empty
  - Send a query with the `max_id` set to the smallest toot id known
  - Update the smallest toot id known


Together with `limit` and `max_id` we can grab any specified number of toots.
Here's the psuedocode for that:
```python
for _ in range(math.ceil(RETRIEVE_NUM_TOOTS // MAX_TOOTS_PER_QUERY)):
    url = f"{SERVER}/api/v1/accounts/{UID}/statuses"
    url += "?limit=40" if limit_param > 40 else f"?limit={limit_param}"
    url += "&max_id={max_id}" if max_id is not None else ""
    response = query(url)
    if len(resposne) == 0:
        break
    # Process response...
```
## Reformatting Toot
Rather than storing the JSON of the toot verbatim, I do make some changes
to it for the following reasons:
- By default every toot has a lot of account information, this is an issue because
if my number of followers update, then I need to update all my toots.
- Hugo expects certain field names to exist. For example: date.

I delete the following account information from my toot archive:
- Lock status
- Bot
- Discoverable
- Group
- Created_at
- Note
- Follower count
- Following count
- Status count
- Last status at

I create a date field based on `created_at`.
The URL field in mastodon conflicts with Hugo,
so I rename it to `syndication`.


## Creating the Markdown files
From here I can construct the following
markdown file based on this template:
```
---
{Toot JSON}
---
JSON.content
```

I save each toot in an individual markdown file under `content/toots`.

## Conclusion

My full [script](https://github.com/Brandon-Rozek/website-toots/blob/main/.scripts/refreshtoots.py)
is on GitHub.
The script will let you know of any toot IDs that are created
and/or updated. I then add these toots to Git for version control
just like my posts.
