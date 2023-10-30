---
title: "Quickly configuring and testing the Mosquitto MQTT broker"
date: 2023-10-30T01:01:57-04:00
draft: false
tags: []
math: false
medium_enabled: false
---

I've been playing with Tasmota smart devices recently; and to hook them up with home assistant, they both need to be configured to utilize MQTT. In this post, we'll only focus on the MQTT part. From quickly installing it to making sure publish/subscribe messages work on another machine. 

## Installing MQTT Broker

On the server you want to install MQTT on:

```bash
sudo dnf install mosquitto
```

We won't go over how to setup TLS or authenticated users. Instead for a quick test, we'll configure it to allow for anonymous connections over any interface.

Add the following lines to `/etc/mosquitto/mosquitto.conf`

```
listener 1883
allow_anonymous true
```

Then enable the systemd service to start mosquitto

```bash
sudo systemctl enable --now mosquitto
```

Make sure it's running:

```bash
sudo systemctl status mosquitto
```

## Testing the Broker

Most tutorials have you test the publish/subscribe on the local machine. Though given we're working with smart devices, we need to make sure it works on another machine first.

**Approach 1:** Install the mosquitto tools on that machine. Then you'll need to open two terminals.

- On terminal 1, subscribe to all messages `mosquitto_sub -h [MQTT_BROKER_ADDR] -t "#" `
- On terminal 2, publish a message: `mosquitto_pub -h [MQTT_BROKER_ADDR] -t "test"  -m "Hello, World"`

On the first terminal, you should see the string `Hello, World`.

**Approach 2:** Use curl.

- On terminal 1, subscribe to all messages with `curl mqtt://[MQTT_BROKER_ADDR]/%23 --OUTPUT - --trace -`
- On terminal 2, publish a message `curl -d 'Hello, World'  mqtt://[MQTT_BROKER_ADDR]/test/`

Similarly, you should see the string `Hello, World` along with a bunch of debugging information.
