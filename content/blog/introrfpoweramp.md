---
title: "Introduction to RF Power Amplifiers"
date: 2021-04-10T13:01:00-04:00
draft: false
tags: ["amateur-radio"]
math: true
---

For field day I've been toying with the idea of buying a power amplifier for my HackRF. What I've come to realize is that there are a lot more to power amplifiers than just how much it amplifies by. This post outlines my current understanding (I'm by no means an expert) on the subject of RF power amplifiers.

I opened up mini-circuits and was greeted with the following table. (Shorted for sake of demonstration)

| Model Number | F Low (MHz) | F High (MHz) | Gain (dB) | NF (dB) | P1dB | OIP3 (dBm) | Input VSWR | Output VSWR | Voltage (V) | Current (mA) |
| ------------ | ----------- | ------------ | --------- | ------- | ---- | ---------- | ---------- | ----------- | ----------- | ------------ |
| LZV-22+      | 0.1         | 200          | 43        | 8.9     | 42   | 52         | 1.4        | 4           | 24          | 6000         |
| ZHL-1W-63-S+ | 600         | 6000         | 35        | 12      | 30   | 35         | 2.5        | 3.5         | 15          | 1000         |

<u>Definitions</u>

F Low: Lowest frequency supported by the power amplifier

F High: Highest frequency supported by the power amplifier

Gain (dB): The difference between the output power and  the input power

Noise Figure (NF): The amount of additional noise that gets added to the system by using the power amplifier

P1dB:  This is the point in where the output power is 1dB less than the linear projected power. This is expressed as the value of the output power. This is commonly used to describe the point in which the power amplifier turns non-linear or approaches saturation.

Saturation: The point in where adding more input power does not increase the output power.  

Third order intercept point (OIP3): Currently unclear as to what this is.

Voltage Standing Wave Radio (VSWR): It's a function of return loss and describes how well impedance is matched. We want this to be as close to 1 as possible. More information: https://antenna-theory.com/m/definitions/vswr.php



From P1dB you can derive a notion of maximum input power. Take your P1dB point and subtract out the gain.
$$
Input_{max} = P1dB - Gain
$$
For the LZV-22+, the maximum input power before P1dB is reached is -1dBm. This measure is separate than a "Maximum Input Power" given by a datasheet. Those are usually the maximum power allowed before the amplifier gets damaged.

To calculate the power required to drive an amplifier, multiply the value listed in voltage by the current. From this you can then derive the efficiency of a power amplifier at any given input power. For example, let us look at LZV-22+ at it's P1dB point.

Power required to drive = 24V * 6000mA / 1000mA = 144W

Output power at P1dB = 42dBm = ~16W

Efficiency = 16 / 144 * 100 = ~11%  

With that background, let's think about my field day setup. For a technician level's amateur radio license, you likely only need an amplifier that supports 28MHz-1GHz. The HackRF outputs 1mW at most frequencies. As a starting point, it would be good to get that to 1W. Most specifications are listed in logithmic scale. 
$$
P_{dBm} = 10\log_{10}{(P_W)} + 30
$$
Hence, 1mW is 0dBm and 1W is 30dBm.

Considerations:

- Need a gain of 30dB
- Lower noise figure is always better but a link budget analysis would get you a specific number.
- Want VSWR as close to 1 as possible. 


