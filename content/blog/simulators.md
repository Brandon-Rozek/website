---
title: "Simulators"
date: 2019-07-01T22:22:29-04:00
draft: false 
medium_enabled: true
---

Part of my job involves integrating multiple different sensors together to make a cohesive product. One thing that I appreciate about my current team, is the rich set of tooling built around the project. I am definitely learning a lot from this project. One thing I wanted to share was the use of *simulators*. 

Now since we're working with sensor data, it doesn't always make sense to need to be connected to a whole system. There's also the additional hassle of dealing with safety and working outside. So in order to do some programming and still be at ease that we didn't break anything, we make heavy use of simulators.

**Example**: Have a GPS hooked up to your system? Well with a tool you can make waypoints and generate a file which you then feed in as a fake GPS device!

Now when I say fake device, I don't mean I'm actually emulating the device on the machine. It's easier to have your device interfacers publish to the local network and have your other parts of the application subscribe to it. So in this case, you will just need to produce those messages directly.

So in conclusion, I think this pattern will work well for my personal projects. It helps keep your code modular and easily testable!
