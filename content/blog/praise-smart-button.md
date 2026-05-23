---
title: "Praise the Smart Button"
date: 2026-05-22T20:07:42-04:00
draft: false 
tags: []
math: false
medium_enabled: false
---

{{< unsafe >}}
<img alt="Lamp which has a giraffe as it's base" height="500px" src="/files/images/blog/202605222012.jpg" />
<br/>
{{< /unsafe >}}

Meet Giraffe. Equipped with an [Innr AE 270 T](https://www.zigbee2mqtt.io/devices/AE_270_T.html) smart bulb, it allows me to turn the light on and off from our phones using [Home Assistant](https://www.home-assistant.io/). The main issue? I need my phone to turn it on and off.

Now don't get me wrong, I can still walk up to the lamp and flip the switch. But, then I need to walk back up to it in order to turn it back on. Turns out, the smart bulb needs some power to receive control messages via the network.

If that wasn't annoying enough, flipping the switch off would mess with my cool automations. At sunrise, it's supposed to turn on to help wake me up and then automatically turn itself off after noon.

So I lived with that reality for a few years. Whenever I want to turn on or off the lamp, I would pull out my phone. Forgot to turn off the lights when I left the house? No worries, I can still control it remotely.

But that all changed this Christmas when my wife gifted me the following...

{{< unsafe >}}
<img alt="Lamp which has a giraffe as it's base" height="500px" src="/files/images/blog/202605222013.jpg" />
<br/>
{{< /unsafe >}}

That's right. It's a [Third Reality 3RSB22BZ](https://www.zigbee2mqtt.io/devices/3RSB22BZ.html) smart button. Setting this up was relatively straightforward. On Home Assistant, I clicked on "Add Device" and then specified that I wanted to add a Zigbee device. This requires a Zigbee hub, and for that I use the [Home Assistant Connect ZBT-2](https://www.home-assistant.io/connect/zbt-2/). After that, I went through a short pairing process and tada the device is added!

By itself, the button doesn't actually do anything. To change that, we need to set up automations. At the time of writing, Home Assistant specifies automations through triggers, conditions, and actions. I set my trigger to `remote_button_short_press`. I didn't add any extra conditions, and my action is to toggle my Giraffe lamp.

With that, I don't need to pull out my phone anymore to control the light! 

---

I've been meaning to write more about my Home Assistant setup, but I'm not sure what would be useful to share. For now I'll write what's on my mind, but feel free to get in touch if you want me to share more.

I started off my Home Assistant journey by purchasing smart bulbs and smart switches flashed with the [Tasmota firmware](https://tasmota.github.io/docs/). The devices specifically connected to my local WiFi network and sent messages to my MQTT server.

However, I wasn't the happiest with the quality of my smart bulbs. I came across itchaboyagin's post on the [Home Assistant forum](https://community.home-assistant.io/t/i-just-finished-testing-over-150-of-the-best-smart-lights-here-s-all-the-data/764760) where they shared a [database](https://optimizeyourbiology.com/smart-light-database/) of 120 different smart bulbs full of metrics. What I was looking for at the time escaped by head, but I believe I focused on bulbs with no flicker risk and great [color quality](https://en.wikipedia.org/wiki/Color_rendering_index).

That's when I came across the Innr bulb and noticed that it relied on Zigbee for connectivity. 
This means that instead of connecting to my WiFI, it creates it's own mesh network and requires a hub to work. So... I needed to purchase an extra device. Luckily, many companies support the Zigbee standard, so I told myself that this would open up oppurtunities for future devices.

Overall, I've been rocking this new setup for the last 6 months and I'm happy.
