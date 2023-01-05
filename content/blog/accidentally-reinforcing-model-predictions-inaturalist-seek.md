---
title: "Accidentally Reinforcing Model Predictions in iNaturalist with Seek"
date: 2022-10-04T11:38:03-04:00
draft: false 
tags: []
math: false
medium_enabled: true
---

I [previously wrote](/blog/identifying-plants-with-inaturalist/) about using Seek to identify organisms and then uploading them separately to iNaturalist. Though after some thought I believe that by only uploading photos that Seek has blessed as knowing,  I may be reinforcing peculiar features of the dataset and hence the model.

For example, let's say that I'm using the iNaturalist app and I'm having difficulties getting the species classification. After shifting the angles of my shots, I finally get to one where it classifies the species. So, I snap a picture. What about all the other angles? Are those invalid for identifying the organism?

Now it's possible that many of the other angles don't capture enough information to separate the specific species from the rest in its genus. For example to my untrained eye, many species of the [Goldenrod genus](https://www.inaturalist.org/taxa/48678-Solidago/browse_photos) look the same. It could be that by zooming in with enough detail, there is enough information about the shape of the flower to make the classification. Or maybe you need a zoomed out view to see the shape of the leaves and stalk in comparison.

Does this mean that uploading photos classified by Seek is redundant? No! Because there are a couple extra features outside the image itself.

**Time:** It's useful to know the lifecycle of the organism. Is it currently flowering? Is it dormant for the winter? 

**Location:** Is the plant native to the area? Is it an invasive species or introduced? Location data can help identify clusters of organisms within an area.

For the image itself, one recommendation I have is the following. Take the image that Seek recommends for the classification, and then take one or two different angles of the same organism. Within iNaturalist, you can upload multiple photos for a single organism.

Now go and take some pictures :)

 
