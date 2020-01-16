---
title: "Systemd with Python environments"
date: 2019-08-25T20:04:20-04:00
draft: false
---

It took me some time to realize why I couldn't start a project during startup. I then realized that it was because I was using a python virtual environment and didn't tell systemd about it. 

Here's how you can do so...

```yaml
[Unit]
Description=Start Service
# After=network.target # If you want a python webserver...

[Service]
Type=Simple
User=brandon
WorkingDirectory=/home/brandon/Development
ExecStart=/bin/sh -c ". /home/brandon/Development/pythonenv/bin/activate; /home/brandon/Development/start"

[Install]
WantedBy=multi-user.target
```





