---
title: "Backing up my data with Restic, Btrfs, and MinIO"
date: 2025-12-30T11:51:07-05:00
draft: false
tags: []
math: true
medium_enabled: false
---

For the past year, I settled on a backup strategy that serves my needs. In this post, I'll share the properties I look for in a backup solution and how my current solution addresses them. As always, if you have any suggestions or improvements, feel free to get in touch.

The first step before talking technology is to identify exactly what data we want to backup. In my homelab, I rely on [Immich](https://immich.app/) for photo storage, [Navidrome](https://www.navidrome.org/) for music streaming, databases for my website, and other personal documents. This amounts to a little over 250 GB of data that would be very difficult for me to replace if it was lost.

Not all my data lives on that one server though. I also have a storage VPS which runs [Nextcloud](https://nextcloud.com/) and [Hedgedoc](https://hedgedoc.org/). Both of those services combined have less than 100 GB of data, but just like the homelab, that data is precious. The storage VPS has a total capacity of 1.5 TB.

The [3-2-1 backup strategy](https://www.backblaze.com/blog/the-3-2-1-backup-strategy/) coined by Peter Krogh suggests that we should have three copies of our data, stored on two different media, and with one being off-site.

Both of my servers have enough storage capacity to hold a copy of all of my data. For my third copy, I decided to rely on [Backblaze b2](https://www.backblaze.com/cloud-storage). This is a S3 object storage service that charges low rates for what I store and the number of transactions I make.

My homelab sits in my house, the storage VPS sits in Montreal, and Backblaze stores my data in Phoenix. Therefore, I have **3** copies of my data and it's stored in more than **1** location.

In order to address having at least **2** different storage media, I backup my data using two different approaches: Restic and Btrfs Snapshots. I don't currently have enough data such that hot online storage is cost-prohibitive.

### Restic 
[Restic](https://restic.net/) is a modern and open-source backup software that both deduplicates and encrypts file contents at the blob level. In combination with a metadata local cache, this makes this Restic snappy and efficient to use.

It supports a variety of backup targets:
- Local filesystem
- SFTP
- REST server
- S3
- and [several others](https://restic.readthedocs.io/en/latest/030_preparing_a_new_repo.html#), including those implemented by [Rclone](https://rclone.org/)!

While I could use the variety of backup targets to increase the number of approaches my data is backed up, to me, this does not feel sufficiently different enough to warrent the additional complexity. Therefore, I'll use one backup target for all three locations.

Since Backblaze b2 only supports the S3 protocol, this means then that my choice has been made for me. However even if it wasn't forced upon me, I would still pick that option. Designed by Amazon for their storage service, the S3 protocol is built with scale in mind and supports concurrent multipart file uploads. Additionally unlike SFTP, S3 separates its accounts from that of the server. There are ways to restrict SSH clients, however, it is not the default behavior. In S3, by default a user cannot do anything.

Thus, after choosing S3, I need to set up a S3 server on both my storage VPS and my homelab. I landed on MinIO for its ease of setup and longevity, however, any of the other solutions would work as well. 

Since, we're storing copies of the data on all the servers, one idea is to set it up in a cluster configuration. However, since I'm not managing the S3 server hosted by Backblaze, I wouldn't be able to include that in the cluster. Generally, it is not recommended to run a cluster with only two nodes. If we do, it can lead to what's called a [*split brain problem*](https://en.wikipedia.org/wiki/Split-brain_(computing)) where both nodes are unable to communicate with each other and think that they are the leader node.

To avoid this, we can run both MinIO instances inpendently and have Restic separately send the data to all servers.

#### MinIO Setup

If you already have a bucket setup and configured with the appropriate permissions, then feel free to skip this section.

The following code examples assume that [MinIO is installed](https://min.io/docs/minio/container/index.html) and the `mc` client is available with the root credentials to each server (alias) set. These general steps can also be achieved using the management UI. For simplicity, I'll show how to do this with respect to one server `homelab`. However, we'll need to do this for every MinIO instance.

First, [create a bucket](https://min.io/docs/minio/linux/reference/minio-mc/mc-mb.html) which will hold our backup data.

```bash
# alias_of_server/bucket_name
mc mb homelab/backups
```

Afterwards, create a [backup user](https://min.io/docs/minio/linux/administration/identity-access-management/minio-user-management.html). We'll need to specify the `ACCESS_KEY` and `SECRET_KEY` which corresponds to the username and password respectively. Store these as we'll later need to use them.
```bash
export ACCESS_KEY="my_awesome_homelab_user"
export SECRET_KEY="SUPER_SECURE_SECRET_KEY"
mc admin user add homelab $ACCESSKEY $SECRETKEY
```

*Note:* For a bit more security, I like to create a different access key and secret key for the other servers.

By default, our user cannot cannot do anything. Let's make it so that they have access to our `backups` bucket we created earlier. To do that, we'll need to create a [policy](https://min.io/docs/minio/linux/administration/identity-access-management/policy-based-access-control.html) which allows the user to perform operations on that bucket.

We'll have to create a JSON file and follow the AWS IAM format. 
```iam
{
 "Version": "2012-10-17",
 "Statement": [
  {
   "Effect": "Allow",
   "Action": [
    "s3:ListBucket",
    "s3:PutObject",
    "s3:DeleteObject",
    "s3:GetObject"
   ],
   "Resource": [
    "arn:aws:s3:::backups/*",
    "arn:aws:s3:::backups"
   ]
  }
 ]
}
```

Assume that we saved the prior JSON at a location specified by the environmental variable `$POLICY_PATH`, then we can create the policy through the following:

```bash
export POLICY_NAME="backup-policy"
mc admin policy create homelab $POLICY_NAME $POLICY_PATH
```

After creating the policy, we need to assign it to our backup user.

```bash
mc admin policy attach homelab $POLICY_NAME --user $ACCESS_KEY
```

#### Nginx and Initializing Restic
With our bucket and user configured, now let's discuss how we'll perform our backups. Our bucket will have the following directory structure:
```
backups/
  homelab/
  vps/
```

Each folder will contain a restic repository. We separate them out instead of having one giant restic repository, so that we don't have to worry about multiple servers competing for a lock.

Instead of communicating over HTTP, we want a secure way to access our buckets from outside the server. For this, I use [nginx to proxy the traffic over to MinIO](https://min.io/docs/minio/linux/integrations/setup-nginx-proxy-with-minio.html). I configure [Certbot with LetsEncrypt](https://letsencrypt.org/getting-started/) so that the connection can be secureted with HTTPS/TLS. In addition to the instructions listed on the MinIO page, I also restrict the IPs which are allowed to connect. For example, to only allow traffic from within your Wireguard network (ex subnet: `10.10.10.1/24`) then you can put the following within the `location` block of the nginx config.
```nginx
allow 10.10.10.1/24;
deny all; // Denies all other traffic
```

After securing the entryway to our S3 server, we're ready to use Restic. Before jumping in, you might want to [create a dedicated account](https://restic.readthedocs.io/en/stable/080_examples.html#full-backup-without-root) so that we don't have to use the `root`  user.

Let's initialize each server's respective repository. Since our backups will be encrypted, we need to come up with another password and put it within the `RESTIC_PASSWORD` environmental variable. Save this password in a safe place, since we will not be able to decrypt the backup without it.

```
export RESTIC_REPOSITORY=s3:https://<domain-of-s3-server>/backups/homelab
export AWS_ACCESS_KEY_ID=$ACCESS_KEY
export AWS_SECRET_ACCESS_KEY=$SECRET_ACCESS_KEY
export RESTIC_PASSWORD="RESTIC_SUPER_SECURE_PASSWORD"

restic init
````

From here, create a backup script at `/usr/local/bin/backup.sh`. This is where we specify which folders to backup.

Example:
```bash
#!/bin/sh

set -o errexit
set -o nounset

if [ "$EUID" -ne "$(id -u restic)" ]
  then echo "Please run as restic"
  exit
fi

# Usage: rbackup [message] [restic-tag] [backup-dir]
rbackup () {
  echo "$1"
  restic backup \
    --tag "$2" \
    "$3"
}


## BACKUP TO CLOUD
export RESTIC_REPOSITORY=s3:https://<domain-of-cloud-server>/backups/homelab
export AWS_ACCESS_KEY_ID="CLOUD_ACCESS_KEY"
export AWS_SECRET_ACCESS_KEY="CLOUD_SECRET_ACCESS_KEY"
export RESTIC_PASSWORD="RESTIC_SUPER_SECURE_PASSWORD"

rbackup "Backing up documents" \
  Documents \
  /home/user/Documents

# Backup other great directories...

## BACKUP TO BACKBLAZE
export RESTIC_REPOSITORY=s3:https://<domain-of-backblaze-server>/backups/homelab
export AWS_ACCESS_KEY_ID="BACKBLAZE_ACCESS_KEY"
export AWS_SECRET_ACCESS_KEY="BACKBLAZE_SECRET_ACCESS_KEY"
export RESTIC_PASSWORD="RESTIC_SUPER_SECURE_PASSWORD"

rbackup "Backing up documents" \
  Documents \
  /home/user/Documents

# Backup other great directories...
```

Unless you have unlimited storage, you probably want to prune old backups according to some schedule. In the same script I have the following function:
```bash
prune () {
  echo "Pruning old snapshots"
  restic unlock
  restic forget \
    --group-by "tags" \
    --keep-daily N_DAYS \
    --keep-weekly N_WEEKS \
    --keep-monthly N_MONTHS \
    --prune
}
```

Replace `N_*` to your liking. Restic will then ensure that it keeps enough snapshots such that those time-based rules are satisfied.

With the script written, we can then setup a systemd service and timer so that it runs daily. Write the following to `/etc/systemd/system/restic-backup.service`.

```ini
[Unit]
Description=Executes backup script
Requires=network-online.target
Wants=

[Service]
User=restic
Group=restic
Type=oneshot
ExecStart=/usr/local/bin/backup.sh
Environment="HOME=/home/restic"

[Install]
WantedBy=multi-user.target

```

Write the timer to `/etc/systemd/system/restic-backup.timer`
```ini
[Timer]
OnCalendar=daily
Persistent=true
[Install]
WantedBy=timers.target
```

### Btrfs snapshots

Both my servers run Btrfs as the underlying filesystem. One cool feature is that Btrfs can create *snapshots*. These are immutable point-in-time views of a given subvolume. As such, we'll need to create a subvolume that will contain the directories we want.

If we're not starting from scratch, and instead want to create a subvolume from an existing folder, then I recommend performing the following steps from [this reddit thread](https://www.reddit.com/r/btrfs/comments/198hbod/converting_directory_into_subvolume/):

```
mv folder folder_backup
btrfs subvolume create folder
cp --archive --one-file-system --reflink=always folder_backup/. folder
```

From here, we can create our snapshots. Like with our Restic setup, I like having some daily, weekly, and monthly backups available. I'll store these snapshots in `/snapshots`, but you're free to change the location. Here's what it looks like on my machine:
```
/snapshots/
  daily
    20251201
      /home/user/Documents
      ...
      /home/user/Music
    ...
    20251227
  monthly
    ...
  weekly
    ...
```

Since these are backup snapshots, we want it to be *readonly*. Here is what it looks like to create a daily snapshot for our documents subvolume:

```bash
SNAPSHOT_PATH="/snapshots/daily/$(date +'%Y%m%d')/home/user/Documents"
mkdir -p "$(dirname $SNAPSHOT_PATH)"
btrfs subvolume snapshot -r /home/user/Documents "${SNAPSHOT_PATH}"
```

We used the date in the folder name so that we can easily detect the oldest snapshots for deletion.
```bash
OLDEST_SNAPSHOT=$(ls "${SNAPSHOT_DIR}" | sort | head -n 1)
for SUBVOLUME_PATH in "${SUBVOLUMES[@]}"
do
    SNAPSHOT_PATH="${SNAPSHOT_DIR}/${OLDEST_SNAPSHOT}${SUBVOLUME_PATH}"
    btrfs subvolume delete -c "${SNAPSHOT_PATH}"    
done
rm -rf "${SNAPSHOT_DIR}/${OLDEST_SNAPSHOT}"
```

I put together a script which takes as input the environment variable `SNAPSHOT_DIR` and handles creating and pruning snapshots. To get these snapshots at different time intervals, we use different systemd timers and change that input variable. Unlike with our restic setup, this will keep the same $N$ number of snapshots for each of our time intervals.  We copy this script to `/usr/local/bin/localbtrbak.sh`.

```bash
#!/bin/bash

set -o nounset

show_usage() {
    echo "Usage: localbtrback"
    exit 1
}

# Check argument count
if [ "$#" -ne 0 ]; then
    show_usage
fi

if [ "$EUID" -ne 0 ]
    then echo "Please run as root"
    exit
fi

if [ -z "$SNAPSHOT_DIR" ]
    then echo "SNAPSHOT_DIR not defined"
    exit
fi

# EDIT TO POINT TO YOUR SUBVOLUMES
SUBVOLUMES=("/home/user/Documents"  "/home/user/Music")

for SUBVOLUME_PATH in "${SUBVOLUMES[@]}"
do
    SNAPSHOT_PATH="${SNAPSHOT_DIR}/$(date +'%Y%m%d')${SUBVOLUME_PATH}"

    # Create folder if not already exists
    mkdir -p "$(dirname $SNAPSHOT_PATH)"

    # Create the readonly snapshot
    btrfs subvolume snapshot -r "${SUBVOLUME_PATH}" "${SNAPSHOT_PATH}"
done

# Calculate the number of snapshots
COUNT=$(ls "${SNAPSHOT_DIR}" | wc -l)

if [ "${COUNT}" -gt 3 ]; then
    OLDEST_SNAPSHOT=$(ls "${SNAPSHOT_DIR}" | sort | head -n 1)
    for SUBVOLUME_PATH in "${SUBVOLUMES[@]}"
    do
        SNAPSHOT_PATH="${SNAPSHOT_DIR}/${OLDEST_SNAPSHOT}${SUBVOLUME_PATH}"
        btrfs subvolume delete -c "${SNAPSHOT_PATH}"    
    done
    rm -rf "${SNAPSHOT_DIR}/${OLDEST_SNAPSHOT}"
fi
```

For our systemd service in `/etc/systemd/system/btrlocalback@.service`
```ini
[Unit]
Description=Create a local BTRFS snapshot

[Service]
Type=oneshot
Environment=SNAPSHOT_DIR="/snapshots/%i"
ExecStart=/usr/local/bin/localbtrbak.sh

[Install]
WantedBy=multi-user.target
```

An example daily timer stored in `/etc/systemd/system/btrlocalbak@daily.timer`
```ini
[Unit]
Description=Create a daily local BTRFS snapshot
[Timer]
OnCalendar=daily
Persistent=true
[Install]
WantedBy=timers.target
```

### Conclusion

Here is a visualization of the three servers and where the data gets backed up to:

![Diagram of the backup setup I described](/files/images/blog/BackupSetup2025.svg)

The bucket image in the diagram denotes the S3 storage, while the cylinder database icon denotes the Btrfs snapshots. Pictorially, this also shows us how the 3-2-1 rule is satisfied.

- Three outgoing arrows on the two servers means that we have three copies of the data
- The two icons on each of the servers show that we're backing it up in two different ways
- I have more than one off-site backup since all three boxes are in different locations.

If I accidentally delete a file, the Btrfs setup is useful since I can quickly access the old version at `/snapshots/daily/<yesterday>/path`. However, if my entire server goes down, then I can use one of the restic backups in either server to restore.



