---
title: "Common Network Debugging Commands"
date: 2022-01-02T15:17:02-05:00
draft: false
tags: ["Networking"]
math: false
---

Below are list of commands that I use to debug common issues in a network. There is a wonderful tool called Wireshark which you can use to sniff packets in a network and filter by a wide range of options, but we'll mainly focus on simple tools that you can use in the terminal.

## `ping`

The most commonly used networking command is `ping`. This allows you to see the time it takes to send and receive an ICMP packet from/to a specified address. Most people use Google's DNS server `8.8.8.8` as a quick test to see if they have access to the Internet.

```bash
ping 8.8.8.8
```

```
PING 8.8.8.8 (8.8.8.8) 56(84) bytes of data.
64 bytes from 8.8.8.8: icmp_seq=1 ttl=117 time=267 ms
64 bytes from 8.8.8.8: icmp_seq=2 ttl=117 time=74.9 ms
64 bytes from 8.8.8.8: icmp_seq=3 ttl=117 time=34.7 ms
64 bytes from 8.8.8.8: icmp_seq=4 ttl=117 time=298 ms
```

Press CTRL-C when you are done looking at the output. Here is a list of common flags used in the ping command.

| Flag         | Description                                                  |
| ------------ | ------------------------------------------------------------ |
| `-c NUM`     | Only send/receive an ICMP packet `NUM` number of times       |
| `-D`         | Print the timestamp along with the roundtrip time            |
| `-W timeout` | Waits a `timeout` amount of seconds for the response before moving on to the next ICMP roundtrip |

Example:

```bash
ping -c3 -D -W1 1.1.1.1
```

```
PING 1.1.1.1 (1.1.1.1) 56(84) bytes of data.
[1641156381.342990] 64 bytes from 1.1.1.1: icmp_seq=1 ttl=57 time=52.6 ms
[1641156382.555358] 64 bytes from 1.1.1.1: icmp_seq=2 ttl=57 time=263 ms
[1641156383.327286] 64 bytes from 1.1.1.1: icmp_seq=3 ttl=57 time=34.3 ms

--- 1.1.1.1 ping statistics ---
3 packets transmitted, 3 received, 0% packet loss, time 2003ms
rtt min/avg/max/mdev = 34.275/116.670/263.116/103.823 ms

```

## `ip route`

Without any extra flags or subcommands this will give you a view of your routing table. A routing table specifies for a given address range, which device to send the network traffic over. Normally you see a large routing table inside businesses (or if you access a lot of VPNs at once). Here is an example of a typical one in a household.

```bash
ip route
```

```bash
default via 192.168.0.1 dev wlan0 proto dhcp metric 600 
192.168.0.0/24 dev wlan0 proto kernel scope link src 192.168.0.2 metric 600 
```

This says that any address between 192.168.0.1-254 goes over the `wlan0` device which on some computers  denote WiFi. The first line shows what the default entry/gateway is, that is if the ip address you're trying to access is not listed in the table it will go through the IP listed in that row first.

You can manually add and remove entries in the routing table as well.

Example:

```bash
sudo ip route add 192.168.1.0/24 dev wlan0
```

```bash
sudo ip route del 192.168.1.0/24 dev wlan0
```

## `traceroute`

This command is more useful if you have multiple segmented networks and you're trying to figure out at which layer the connection failed. Recently I used this to debug some directional WiFi extenders.

```bash
traceroute 8.8.8.8
```

```bash
traceroute to 8.8.8.8 (8.8.8.8), 64 hops max
  1   192.168.0.1  2.051ms  2.003ms  1.278ms 
  2   192.168.2.1  5.743ms  5.647ms  3.592ms 
  3   192.168.5.1  5.754ms  63.285ms  7.187ms 
  4   72.126.142.1  96.056ms  101.861ms  14.547ms 
  5   103.51.11.206  87.273ms  16.617ms  72.810ms 
  6   170.222.220.217  13.745ms  101.122ms  16.402ms 
  7   201.149.23.6  85.738ms  102.977ms  100.974ms 
  8   107.150.228.33  15.111ms  87.467ms  103.076ms 
  9   12.21.20.233  100.755ms  102.000ms  102.352ms 
 10   8.8.8.8  102.505ms  102.085ms  101.762ms 

```

## `dig`

We've been talking about IP addresses with the last few commands, but there can be problems in the domain name resolution as well. A domain name is what you commonly type in the browser such as `duckduckgo.com`. Your computer will then ask the DNS server it knows about what the IP of that address is.

```bash
dig duckduckgo.com
```

```

; <<>> DiG <<>> duckduckgo.com
;; global options: +cmd
;; Got answer:
;; ->>HEADER<<- opcode: QUERY, status: NOERROR, id: 36469
;; flags: qr rd ra; QUERY: 1, ANSWER: 1, AUTHORITY: 0, ADDITIONAL: 1

;; OPT PSEUDOSECTION:
; EDNS: version: 0, flags:; udp: 65494
;; QUESTION SECTION:
;duckduckgo.com.                        IN      A

;; ANSWER SECTION:
duckduckgo.com.         149     IN      A       52.149.246.39

;; Query time: 88 msec
;; SERVER: 127.0.0.53#53(127.0.0.53)
;; WHEN: Sun Jan 02 16:06:23 EST 2022
;; MSG SIZE  rcvd: 59

```

Most linux systems have a DNS cache server setup which makes it difficult to figure out what the upstream DNS server that it's querying is. Mainly because it can be configured a myriad of ways. If you are using NetworkManager you can use the following command:

```bash
nmcli dev show | grep DNS
```

In some other cases it would be in `/etc/resolv.conf`

```bash
cat /etc/resolv.conf
```

## `arp`

Lastly at the lowest level, arp will tell you the MAC addresses of IP addresses you have communicated with before.

```bash
arp
```

```
Address                  HWtype  HWaddress           Flags Mask            Iface
192.168.0.1              ether   10:1d:b1:1d:1f:91   C                     wlan0
192.168.0.11             ether   72:25:22:2c:72:72   C                     wlan0
192.168.0.111            ether   03:33:34:3b:23:39   C                     wlan0
```

