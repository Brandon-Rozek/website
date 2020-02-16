---
title: "Getting started with Digital Modes in Linux"
date: 2019-09-04T09:52:21-04:00
draft: false
tags: [ "amateur radio" ]
---

This blog post is going to describe what steps I took to be able to decode signals using digital modes. Hardware wise, you will either need a RTL-SDR receiver or a transceiver radio with a cable plugging into the computer's soundcard.

## Software Required

- Gqrx (depends on GNU Radio)

  - This is if you are trying to work with RTL-SDR
  - It acts as a AM/FM/CW/etc demodulator for the data sent by the equipment

- Fldigi

  - This is what decodes the protocol used to package the data
  - It acts as a modem and provides capability to transmit data using a transceiver 

- Pavucontrol

  - This connects both Gqrx and Fldigi if using RTL-SDR

As you can see, if you are only using a transceiver then you can skip the parts mentioning Gqrx and Pavucontrol

## Process

### Gqrx

When you first open up Gqrx, it'll ask you to configure the device. I have the RTL2832U, so if you have the same tool...

Select the profile partially labeled RTL2832U. If you want to look at frequencies between 0 and 28MHz then add to the device string "direct_samp=3". Otherwise don't add that string. 

You can keep the rest of the settings the same.

### Fldigi

When you first open up Fldigi, it'll ask you for our operator info.

| Field             | description                               |
| ----------------- | ----------------------------------------- |
| Station Callsign  | Your callsign                             |
| Station QTH       | City, State                               |
| Station Locator   | Your grid code. (Can look this up on QRZ) |
| Operator Callsign | Your callsign                             |
| Operator Name     | Your name                                 |
| Antenna           | Your antenna type                         |

In Audio->Devices, make sure you select the physical device if you're using a transceiver, otherwise select PulseAudio.

You can keep the rest of the settings as the default.

### Pavucontrol

Finally to link the two, run the following lines in bash to create a sink in order to push the audio from Gqrx to Fldigi.

```bash
pacmd load-module module-null-sink sink_name=MyLoopback
pacmd update-sink-proplist MyLoopback device.description=MyLoopback
pacmd load-module module-loopback sink=MyLoopback
```

Now open up `pavucontrol`. On the Playback tab, change the output device of GQRX to be "MyLoopback"

On the Recording tab, change the input of fldigi to "Monitor of Null Output"

## Conclusion

Now the software is sufficiently setup to be able to receive and decode signals. Best of luck finding things out there!

## Beginner Pitfalls

Since I'm also a beginner, I will share what I got stuck on and how you can avoid it.

Make sure that you know the appropriate mode to demodulate the signal. I've had luck getting information from https://www.sigidwiki.com/wiki/Signal_Identification_Guide

-> This needs to be configured on both Gqrx and Fldigi
