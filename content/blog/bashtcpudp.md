---
title: "TCP/UDP with Bash"
date: 2020-05-25T23:10:15-04:00
draft: false
tags: ["Bash", "Networking"]
medium_enabled: true
---

The bash shell contains pseudo-devices to send packets with TCP/UDP. The pseudo files are formatted like the following:

```
dev/tcp/HOST/PORT
/dev/udp/HOST/PORT
```

To send a UDP packet to `localhost:6300` containing the payload "Hello, World.", we would run the following command:

```bash
echo "Hello, World." > /dev/udp/127.0.0.1/6300
```