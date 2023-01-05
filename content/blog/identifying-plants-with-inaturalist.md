---
title: "Identifying Plants With iNaturalist"
date: 2022-09-29T20:08:30-04:00
draft: false 
tags: []
math: false
medium_enabled: true
---

Seek by iNaturalist ([android](https://play.google.com/store/apps/details?id=org.inaturalist.seek)) ([apple](https://apps.apple.com/us/app/seek-by-inaturalist/id1353224144)) is a great app for identifying plants and animals. It uses a computer vision model to provide the hierarchical classifications. In fact they run yearly challenges with their dataset on [Kaggle](https://www.kaggle.com/c/inaturalist-2021/overview) as well as publicly host their dataset on AWS ([instructions](https://github.com/inaturalist/inaturalist-open-data)).

What makes the experience so interesting, is the identification process is somewhat interactive. For example, look at the following screenshots of when I was trying to identify a plant near my workplace. 

First we start off with the dicot class. This is roughly equivalent to it saying that it has identified a flower. 

![Screenshot showing Dicot Class for the Flower](/files/images/blog/20220929194646.jpg)

To get a better classification, we need to get closer to the plant and try different angles, notice how the classification updates the get closer and closer to the species of the plant. That is, white snakeroot. 

![Screenshot showing Family designation for the Flower](/files/images/blog/20220929194647.jpg)![Screenshot showing Genus designation for the Flower](/files/images/blog/20220929194648.jpg)![Screenshot showing Species designation for the Flower](/files/images/blog/20220929194649.jpg)

Fun fact, white snakeroot is the most common flower in New York.

Once you get to the species level, you can take a picture and the observation is saved within the Seek app. This by default is only saved locally and not shared with the community. If you're up for some citizen science, we can upload it separately! If you like to use your phone for that you can use the iNaturalist app ([Android](https://play.google.com/store/apps/details?id=org.inaturalist.android)) ([Apple](https://apps.apple.com/us/app/inaturalist/id421397028)).

Within the app, create a new observation and select "choose image". Then navigate to your Seek folder and select the image you want to upload.

You should then see a screen similar to this one:

![Screenshot showing new observation page where the user can fill out the species information and other notes.](/files/images/blog/20220929201902.jpg)

If your image contains geotagged information then it will use that to populate the location field. You can also change the location visibility to obscured or private instead of public if you'd like. If you're not in a park or preserve, but instead at a garden or other areas with hand-placed plants you should mark it as cultivated. Though if you need more detail, the [iNaturalist FAQ](https://www.inaturalist.org/pages/help-inaturalist-canada-en#captive) explains it in depth. 

When you click on "What did you see?", you'll see a new screen with the level of depth they were able to identify it at and nearby organisms that are visually similar.

![Screenshot showing most specific classification made and visually similar and nearby species.](/files/images/blog/20220929201903.jpg)

Once you select the species you're ready to publish the observation! This will generate a unique URL for the observation. For example, my [white snakeroot observation](https://www.inaturalist.org/observations/135665018).  If another community member agrees with your classification and the observation has enough supporting metadata, then it could become research grade!

Research grade observations gets used by scientists for research which may also help improve the image classification algorithm for all. Happy identifying!
