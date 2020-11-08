---
title: "Getting Started with FM Digital Modes"
date: 2020-11-07T21:31:52-05:00
draft: false
tags: ["amateur radio"]
---

In this post, I will describe a low cost way to get started with digital modes using FM. We will extend off my [previous post](/blog/digitalmodes). Even though some of these instructions are hardware specific, I hope that the general principles will apply to whatever hardware you're working with.

In order to transmit, you will need an amateur radio license. We are going to be transmitting within 145.50-145.80 Mhz which according to the [ARRL Band Plan](http://www.arrl.org/band-plan) is marked as the miscellaneous and experimental section. In terms of our encoding scheme, let's play around with [8PSK](https://www.sigidwiki.com/wiki/8PSK). 

## Equipment

| Item                                                         | Purpose                                               |
| ------------------------------------------------------------ | ----------------------------------------------------- |
| [BaoFeng BF-F8HP](https://www.amazon.com/BaoFeng-BF-F8HP-Two-Way-136-174Mhz-400-520Mhz/dp/B00MAULSOK/) | Transmitter                                           |
| [Audio Interface Cable](https://www.amazon.com/BTECH-APRS-K1-Interface-APRSDroid-Compatible/dp/B01LMIBAZW/) | Cable that plugs from the transmitter to the computer |
| [USB Audio Adapter](https://www.amazon.com/LZYCO-External-Adapter-Headphone-Microphone/dp/B072J7WLQ5/) (Optional) | If your computer doesn't have a 3.5mm audio jack      |
| Transmitter Computer                                         | Modulates with Fldigi                                 |
| [Software Defined Radio](https://www.amazon.com/RTL-SDR-Blog-RTL2832U-Software-Defined/dp/B011HVUEME/) | Receiver                                              |
| Receiver Computer                                            | Demodulates with Gqrx and decodes with Fldigi         |

## Transmitter End

Plug in the audio interface cable from the Baofeng to the transmitter computer. Then open up Fldigi and configure it to directly access the radio from the audio port. Refer to my previous post for some of the setup instructions.

For our computer to handle transmitting, we need to disable push to talk on our Baofeng. To do that, we need to set VOX in the menu to 10.

In Fldigi, go to Op mode and set it to 8PSK-125.

## Receiver End

Now let's plug in our software defined radio into our receiver computer and open up `gqrx`.

When you first open the application, you need to configure the IO devices. Here are the settings I use:

| Parameter     | Value                  |
| ------------- | ---------------------- |
| Device        | Realtek RTL2838UHID... |
| Device String | rtl=0                  |
| Input Rate    | 2500000                |
| Bandwidth     | 0 MHz (Auto)           |
| LNA LO        | 0 MHz (Auto)           |
| Device        | Default                |
| Sample Rate   | 48 KHz                 |

After hitting `Ok`, look for the play button on the top left of the application to start DSP.

Since we're working in the 2 m band, we can set the LNA to 0 dB in the Input Controls. In the receiver options set the mode to Narrow FM and click R by the squelch to disable the squelch.

Next, we need to pipe the audio output to FLDIGI. For convenience, here is part of the instructions I had in the previous blog post.

```bash
pacmd load-module module-null-sink sink_name=MyLoopback
pacmd update-sink-proplist MyLoopback device.description=MyLoopback
pacmd load-module module-loopback sink=MyLoopback
```

Now open up `pavucontrol`. On the Playback tab, change the output device of GQRX to be “MyLoopback”. On the Recording tab, change the input of fldigi to “Monitor of Null Output”.

In Fldigi, we will need to set the Op Mode to 8PSK-125 to match the transmitter end.

## Conclusion

Finally, we can test our setup by typing a message in the blue box in FLDIGI on the transmitter machine. Hit the blue Tx button on the bottom right of the screen, and hope to see the message decoded on the receiver computer's FLDIGI application.

One of the biggest troubleshooting pieces for me is the fact that my laptop wants to mute new audio devices automatically. Make sure that MyLoopback is not muted.

Also if you are having trouble with 8PSK, CW is easier to work with.