---
title: "Monitoring my Hard Drives with SMART Attributes"
date: 2024-10-17T13:05:59-04:00
draft: false
tags: []
math: false
medium_enabled: false
---

After having a hard drive fail on me once, I've been slowly upgrading my homelab to be more resilient. Currently I take daily backups using [Restic](https://restic.net/), push it offsite to two different services, and have 4 hard drives [set up in a RAID 10 configuration](https://brandonrozek.com/blog/switching-raid-10/). 

The RAID 10 configuration means that I can safely lose one hard drive without needing to access my backups. Though you know the saying, "when it rains it pours". This means I can't ignore the possibility that multiple hard drives die at once.

Luckily, in many cases, we can detect early signs of drive failures. This is where SMART attributes come in. The **S**elf-**M**onitoring, **A**nalysis, and **R**eporting **T**echnology (SMART) system reports many different indicators on drive reliability. Unfortunately, which indicators the hard drive reports, and sometimes even the way the value is formatted is vendor-dependent. 

In order to list the value of all the SMART attributes of a given drive (e.g `/dev/sda`),

```bash
sudo smartctl -A /dev/sda
```

Wikipedia maintains a list of [common SMART attributes](https://en.wikipedia.org/wiki/Self-Monitoring%2C_Analysis_and_Reporting_Technology#Known_ATA_S.M.A.R.T._attributes). In my server, I have a mix of Western Digital and Seagate drives.  I looked at the SMART attributes that were in common between these drives, and additionally filtered by the ones where the values are vendor-agnostic. This gives me the following table:

| Attribute              | Description                                                  |
| ---------------------- | ------------------------------------------------------------ |
| Reallocated_Sector_Ct  | The number of bad sectors that have been found and reallocated. |
| Current_Pending_Sector | The number of sectors waiting to be remapped due to unrecoverable read errors. |
| Offline_Uncorrectable  | The total number of uncorrectable errors when reading/writing a sector. |

In order to grab the value of a specific SMART attribute, we need to filter the `smartctl` output with `grep` and `awk`,

```bash
sudo smartctl -A /dev/sda | grep Reallocated_Sector_Ct | awk '{print $NF}'
```

Hopefully, the last command printed `0` for you...

Now that we know which attributes to make sure stay zero and we have a way to [get notified from our server](https://brandonrozek.com/blog/webhook-notifications-on-systemd-service-failure/), we can create a script that runs daily and notifies us only when a bad sector appears.

```bash
# Sends a webhook based on the argument given
# feel free to replace this with your own
# solution
sendMsg() {
    local MSG=$1
    local CLEAN_MSG
    CLEAN_MSG=$(echo "$MSG" | jq -Rsa .)
    curl -X POST --data-urlencode "payload={\"text\": $CLEAN_MSG}" "$WEBHOOK_URL"
}
```

Different failure modes:

1) Drive that we expect exists doesn't. It's likely too late for the drive at this point...

```bash
sendMissingDevice() {
    local DEVICE=$1

    local MSG="ALERT: '$DEVICE' not found"
    sendMsg "$MSG"
}
```

2. The hard drive does not report one of the three smart attributes we're checking. In this case, you'll either have to skip the attribute check for this drive or find another common set of attributes to check for.

```bash
sendMissingAttribute() {
    local DEVICE=$1
    local ATTRIBUTE=$2

    local MSG="ALERT: '$DEVICE' is missing attribute '$ATTRIBUTE'"
    sendMsg "$MSG"
}
```

3. The indicator reports a non-zero value. For the attributes we're monitoring, this means that we have a bad sector in our hard drive.

```bash
sendAlert() {
    local DEVICE=$1
    local ATTRIBUTE=$2
    local RAW_VALUE=$3

    local MSG="WARNING: '$DEVICE' has a non-zero raw value for attribute '$ATTRIBUTE'.\n$DEVICE $ATTRIBUTE $RAW_VALUE"
    sendMsg "$MSG"
}
```

Our main loop then iterates over all our devices and attributes we want to check for.

```bash
for DEVICE in "${DEVICES[@]}"; do
    echo "Checking $DEVICE..."

    # Check if the device exists
    if [ ! -e "$DEVICE" ]; then
        echo "Device $DEVICE not found."
        sendMissingDevice "$DEVICE"
        continue
    fi

    SMART_OUTPUT=$(smartctl -A "$DEVICE")

    for ATTRIBUTE in "${ATTRIBUTES[@]}"; do

        # Check if the attribute exists in the output
        if ! echo "$SMART_OUTPUT" | grep -q "$ATTRIBUTE"; then
            echo "Attribute '$ATTRIBUTE' not found"
            sendMissingAttribute "$DEVICE" "$ATTRIBUTE"
            continue
        fi

        RAW_VALUE=$(echo "$SMART_OUTPUT" | grep "$ATTRIBUTE" | awk '{print $NF}')

        if [ "$RAW_VALUE" -gt 0 ]; then
            echo "Attribute '$ATTRIBUTE' has raw value of '$RAW_VALUE'"
            sendAlert "$DEVICE" "$ATTRIBUTE" "$RAW_VALUE"
        fi
    done
done
```

Put this all in a script located at `/usr/local/bin/monitor-disks.sh`. In order to have this script run daily, we'll need to first create a systemd service at `/etc/systemd/system/monitor-disks.service`.

```ini
[Unit]
Description=Monitors disks for bad sectors
Requires=
Wants=
# You'll want to run this script after all the
# hard drives come online
After=dev-sda1.device dev-sdb1.device dev-sdc1.device dev-sdd1.device
# See: https://brandonrozek.com/blog/webhook-notifications-on-systemd-service-failure/	
OnFailure=webhook-notify@%i.service

[Service]
Type=oneshot
ExecStart=/usr/local/bin/monitor-disks.bash

[Install]
WantedBy=multi-user.target

```

Finally, we create a systemd timer at `/etc/systemd/system/monitor-disks.timer`.

```ini
[Unit]
Description=Check for bad sectors daily
[Timer]
OnCalendar=daily
Persistent=true
[Install]
WantedBy=timers.target
```

For your convenience, the `monitor-disks.sh` file in its entirety:

```bash
#!/bin/bash

DEVICES=("/dev/sda" "/dev/sdb" "/dev/sdc" "/dev/sdd")
ATTRIBUTES=("Reallocated_Sector_Ct" "Current_Pending_Sector" "Offline_Uncorrectable")
WEBHOOK_URL="INSERT_WEBHOOK_URL_HERE"

if [ "$EUID" -ne 0 ]
  then echo "Please run as root"
  exit
fi

if ! command -v smartctl &> /dev/null; then
    echo "smartctl is not installed"
    exit 1
fi

if ! command -v jq &> /dev/null; then
    echo "jq is not installed"
    exit 1
fi

sendMsg() {
    local MSG=$1
    local CLEAN_MSG
    CLEAN_MSG=$(echo "$MSG" | jq -Rsa .)
    curl -X POST --data-urlencode "payload={\"text\": $CLEAN_MSG}" "$WEBHOOK_URL"
}

sendMissingDevice() {
    local DEVICE=$1

    local MSG="ALERT: '$DEVICE' not found"
    sendMsg "$MSG"
}

sendMissingAttribute() {
    local DEVICE=$1
    local ATTRIBUTE=$2

    local MSG="ALERT: '$DEVICE' is missing attribute '$ATTRIBUTE'"
    sendMsg "$MSG"
}

sendAlert() {
    local DEVICE=$1
    local ATTRIBUTE=$2
    local RAW_VALUE=$3

    local MSG="WARNING: '$DEVICE' has a non-zero raw value for attribute '$ATTRIBUTE'.\n$DEVICE $ATTRIBUTE $RAW_VALUE"
    sendMsg "$MSG"
}

for DEVICE in "${DEVICES[@]}"; do
    echo "Checking $DEVICE..."

    # Check if the device exists
    if [ ! -e "$DEVICE" ]; then
        echo "Device $DEVICE not found."
        sendMissingDevice "$DEVICE"
        continue
    fi

    SMART_OUTPUT=$(smartctl -A "$DEVICE")

    for ATTRIBUTE in "${ATTRIBUTES[@]}"; do

        # Check if the attribute exists in the output
        if ! echo "$SMART_OUTPUT" | grep -q "$ATTRIBUTE"; then
            echo "Attribute '$ATTRIBUTE' not found"
            sendMissingAttribute "$DEVICE" "$ATTRIBUTE"
            continue
        fi

        RAW_VALUE=$(echo "$SMART_OUTPUT" | grep "$ATTRIBUTE" | awk '{print $NF}')

        if [ "$RAW_VALUE" -gt 0 ]; then
            echo "Attribute '$ATTRIBUTE' has raw value of '$RAW_VALUE'"
            sendAlert "$DEVICE" "$ATTRIBUTE" "$RAW_VALUE"
        fi
    done
done

```

