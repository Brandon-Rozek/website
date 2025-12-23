---
title: "Disabling Nat Source Port Randomization on OPNsense for Gaming"
date: 2025-12-23T11:16:02-05:00
draft: false
tags:
  - Networking
math: false
medium_enabled: false
---

> Let's play Mario Party tonight!

After many years of friendship, I've learned that playing online multiplayer games is almost never as simple as it seems. This night was no different.  In this post, I'll go over what I learned setting up my Nintendo Switch for online play. Luckily, this same concept applies to the PlayStation 5 as well[^1]. 

But first, I'll take a detour into how peer-to-peer (P2P) gaming typically works. So, feel free to [skip](#the-solution) down to the solution.

## Peer-to-Peer Gaming

Mario Party is a board game where you move characters around in hopes of collecting the most stars. You play as a character from the Mario franchise, and between each turn on the board is a minigame. These minigames provide the illusion that this is a skill-based game. But trust me, you can win by just tapping A.

Sony and Nintendo both aren't forthcoming with information about how their games and systems work. Therefore, I'll be making a number of assumptions here. 

Nintendo owns Mario Party, and from there we can presume that they use the standard Nintendo libraries when building the game. The homebrew community over the years reverse-engineered many of these libraries and due to this we can look at the protocols they use. The Nintendo networking library, called [Pia](https://github.com/kinnay/NintendoClients/wiki/Pia-Overview), uses a service called NEX to match players in games. This match-making protocol includes a [network-address-translation (nat) traversal protocol](https://en.wikipedia.org/wiki/UDP_hole_punching).

For sake of simplicity, I won't describe the protocol in full-depth. What's important to know is that when both players message the server, the server knows each player's IP address and the source port that they used to communicate. The server will then share the other console's information to facilitate that direct peer-to-peer connection

Unfortunately, I was not able to find either official or unofficial documentation on how P2P gaming works on the PlayStation 5. From browsing around, I have the impression that this is less standardized and developers are either relying on external SDKs or developing their own libraries.

## The Problem

Opnsense, in all their great wisdom, wants to protect me from [TCP hijacking](https://en.wikipedia.org/wiki/TCP_sequence_prediction_attack) and spoofing attacks. Therefore, by default during nat my source port is randomized.

Now the game consoles will not tell us directly that this is the issue. Instead it will provide a "score" which is supposed to establish a rough sense of how easy it will be to establish a P2P connection.

Nintendo Switch: Settings -> Internet -> Test Connection

PS5: Settings -> Network -> Test Internet Connection

Before applying any changes, on the switch I had a "D" score on on the PS5 it was "Type 3". I wish I can tell you what these scores mean, but the documentation is lacking to say the least...

However, I was finally able to determine that nat source port randomization was the problem after stumbling upon this [Reddit thread](https://www.reddit.com/r/OPNsenseFirewall/comments/g3sx2l/tip_opnsense_and_nintendo_switch_nat_rules/) -- which now takes us to the solution:



## The Solution

We need to tell our router that our gaming devices are special, and therefore does not need the additional security measure of randomizing the source port during nat. That way when the game is establishing a P2P connection, the ports aren't randomized and the connection can proceed smoothly.

On Opnsense, we can change this setting by navigating to Firewall -> NAT -> Outbound.

Now I do want this security measure to be applied to the rest of my devices. Therefore, we'll be setting the mode to "Hybrid outbound NAT rule generation"  which allows us to specify the custom rules.

From there, we can add a manual rule for each game console with the following:
- Interface: WAN
- TCP/IP Version: IPv4
- Protocol: UDP
- Source Address: Single host or network
	- Insert Switch/PS5 address
	- Replace netmask with 32
- Source Port: any
- Destination Address: any
- Destination Port: Any
- Static Port: **Checked**

The last option is what tells Opnsense to not randomize the source port. 

From there, we can save, apply our settings, and rerun our connection tests. With this change, my Switch reports a NAT type of B and PS5 reports Type 2. Good enough for online gaming :)

[^1]: Sorry Xbox folks, I do not own one so I cannot tell you if this technique works for that platform as well.
