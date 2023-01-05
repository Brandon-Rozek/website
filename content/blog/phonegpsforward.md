---
title: "Forwarding Phone's GPS"
date: 2020-11-08T00:58:11-05:00
draft: false
tags: ["GPS"]
medium_enabled: true
---

Sometimes I wish to open up [Marble](https://marble.kde.org/) which an a mapping application and see my current location on the globe. My laptop, however, doesn't have a GPS module in it. Though I realized that I carry around a device that does... My phone.

Tiago Shibata wrote a great Android application called [GPSd Forwarder](https://www.f-droid.org/en/packages/io.github.tiagoshibata.gpsdclient/) which allows you to forward the NMEA data from your phone's GPS to another device over UDP. The user interface of the app is really simple and only requires you to put an ip address and a port of the device you want to stream the GPS data to.

For sake of example, let's say we're sending UDP packets to the ip address of 192.168.0.86 and a port of 29998.

As a good sanity check, let's make sure that the computer is receiving those UDP packets.

```bash
nc -lu 29998
```

You should see a constant stream of output that looks similar to:

```
$GNGSA,A,2,324,,,,,,,,,,,,1.2,0.9,0.8,3*05
```

Then we need a piece of software that knows how to process this NMEA message. For that we use `gpsd`.

To install,

```bash
sudo apt install gpsd gpsd-clients
```

For the purposes of this demo, we'll disable the automatic socket daemon and tell gpsd to listen on the udp port 29998.

```bash
sudo systemctl stop gpsd.socket
sudo gpsd -N udp://*:29998
```

To sanity check that gpsd is processing the data, you can make sure there's output in `gpsmon`.

Finally to hook this into Marble, go to Settings -> Panel -> Location. Then in the location pane change the Position Tracking option to "gpsd".