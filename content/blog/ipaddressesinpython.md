---
title: "How to get list of IP Addresses in Python"
date: 2020-09-07T20:03:24-04:00
draft: false
tags: ["python", "networking"]
---

[Elemag](https://stackoverflow.com/users/2436840/elemag) on gave a quick solution on StackOverflow on [how to determine IP addresses with multiple NICS](https://stackoverflow.com/questions/270745/how-do-i-determine-all-of-my-ip-addresses-when-i-have-multiple-nics).  

His one-line solution:

```python
import netifaces
ip_addresses = [netifaces.ifaddresses(iface)[netifaces.AF_INET][0]['addr'] for iface in netifaces.interfaces() if netifaces.AF_INET in netifaces.ifaddresses(iface)]
```

Expanded out to see what is happening

```python
import netifaces
interface_list = netifaces.interfaces()
# Get addresses, netmask, etc. information 
address_entries = (netifaces.ifaddresses(iface) for iface in interface_list)
# Only pay attention to ipv4 address types
ipv4_address_entries = (address[netifaces.AF_INET] for address in address_entries if netifaces.AF_INET in address)
# Since multiple addresses can be associated, only look at the first ip address
ipv4_addresses = [address[0]['addr'] for address in ipv4_address_entries]
```

We can easily adjust this to ask for IPv6 addresses by using `netifaces.AF_INET6` instead.

```python
import netifaces
interface_list = netifaces.interfaces()
# Get addresses, netmask, etc. information 
address_entries = (netifaces.ifaddresses(iface) for iface in interface_list)
# Only pay attention to ipv6 address types
ipv6_address_entries = (address[netifaces.AF_INET6] for address in address_entries if netifaces.AF_INET6 in address)
# Since multiple addresses can be associated, only look at the first ip address
ipv6_addresses = [address[0]['addr'] for address in ipv6_address_entries]
```

