---
date: 2022-04-10 22:05:46-04:00
draft: false
math: false
medium_enabled: true
medium_post_id: ee4c7c4d2966
tags:
- Backup
title: 'Rclone: The Swiss Army Knife of Cloud Storage'
---

[Rclone](https://rclone.org/) is a terminal application that manages remote storage. It supports the standard remote filesystem protocols such as S3, (S)FTP, WebDAV as well as easy to use integration with cloud providers such as Amazon S2, Backblaze B2, Google Drive, and others. We can even perform regular backups using [Restic](https://restic.net/) with Rclone underneath. With all these features, it's easy to configure all remote storage within Rclone and then synchronize the configuration file across machines.

Outline:

- [Setting up a remote](#setting-up-a-remote)
- [Mounting a remote](#mounting-a-remote)
- [Serving a remote](#serving-a-remote)
- [Conclusion](#conclusion)



## Setting up a remote

Below is an example of setting up a WebDAV remote.

```bash
rclone config
```

```
No remotes found - make a new one
n) New remote
s) Set configuration password
q) Quit config
n/s/q> n
name> WebDav-Test
Type of storage to configure.
Enter a string value. Press Enter for the default ("").
Choose a number from below, or type in your own value
 1 / 1Fichier
   \ "fichier"
	...
31 / Webdav
   \ "webdav"
	...
35 / seafile
   \ "seafile"
Storage> 31
** See help for webdav backend at: https://rclone.org/webdav/ **

URL of http host to connect to
Enter a string value. Press Enter for the default ("").
Choose a number from below, or type in your own value
 1 / Connect to example.com
   \ "https://example.com"
url> https://webdav.example.com
Name of the Webdav site/service/software you are using
Enter a string value. Press Enter for the default ("").
Choose a number from below, or type in your own value
 1 / Nextcloud
   \ "nextcloud"
	...
 4 / Other site/service or software
   \ "other"
vendor> 4
User name
Enter a string value. Press Enter for the default ("").
user> brandon
Password.
y) Yes type in my own password
g) Generate random password
n) No leave this optional password blank (default)
y/g/n> y
Enter the password:
password:
Confirm the password:
password:
Bearer token instead of user/pass (eg a Macaroon)
Enter a string value. Press Enter for the default ("").
bearer_token>
Edit advanced config? (y/n)
y) Yes
n) No (default)
y/n> n
Remote config
--------------------
[WebDav-Test]
url = https://webdav.example.com
vendor = other
user = brandon
pass = *** ENCRYPTED ***
--------------------
y) Yes this is OK (default)
e) Edit this remote
d) Delete this remote
y/e/d> y
Current remotes:

Name                 Type
====                 ====
WebDav-Test          webdav

e) Edit existing remote
n) New remote
d) Delete remote
r) Rename remote
c) Copy remote
s) Set configuration password
q) Quit config
e/n/d/r/c/s/q>
```

## Mounting a remote

Now that we have a remote, it would be great to mount it in order to explore the filesystem.

The simplest way is through the following command. Where the mountpoint is an empty directory.

```bash
rclone mount remote_name:remote_path /path/to/mountpoint
```

To unmount use the `fusermount` command.

```bash
fusermount -u /path/to/mountpoint
```

If you forget the exact mountpoint, we can list all mountpoints with the following command.

```bash
mount
```

You can then try to narrow it down such as "show me mounts under the /home directory"

```bash
mount | grep /home
```

[Amy Nagle wrote the following gist](https://gist.github.com/kabili207/2cd2d637e5c7617411a666d8d7e97101) in order to get this to work with `systemd`. First make sure `user_allow_other` is in `/etc/fuse.conf`.  Then create the following user systemd service in `~/.config/systemd/user/rclone@.service`.

```ini
[Unit]
Description=rclone: Remote FUSE filesystem for cloud storage config %i
Documentation=man:rclone(1)
After=network-online.target
Wants=network-online.target
AssertPathIsDirectory=%h/remote/%i

[Service]
Type=notify
ExecStart= \
  /usr/bin/rclone mount \
    --config=%h/.config/rclone/rclone.conf \
    --vfs-cache-mode writes \
    --vfs-cache-max-size 100M \
    --log-level INFO \
    --log-file /tmp/rclone-%i.log \
    --umask 022 \
    --allow-other \
    %i: %h/remote/%i
ExecStop=/bin/fusermount -u %h/remote/%i

[Install]
WantedBy=default.target
```

Then you can enable it on user login with the following command.

```bash
systemctl --user enable rclone@REMOTE_NAME
```

You can start it now by

```bash
systemctl --user start rclone@REMOTE_NAME
```



## Serving a remote

This option is especially useful when you want a computer to access a cloud service without having `rclone` or the cloud specific tool installed. A computer can act as a hub for all the cloud services and present it to other computers in a network with a standard protocol such as SFTP and WebDAV.

To serve via SFTP:
```bash
rclone serve \
	--addr 0.0.0.0:9191 \
	--user brandon \
	--pass SuperSecurePasswordHere \
	sftp \
	REMOTE_NAME:
```

We can adapt Amy Nagle's systemd script above to serve SFTP instead:

```ini
[Unit]
Description=rclone: Remote FUSE filesystem for cloud storage config %i
Documentation=man:rclone(1)
After=network-online.target
Wants=network-online.target

[Service]
Type=simple
ExecStart= \
  /usr/bin/rclone serve \
    --config=%h/.config/rclone/rclone.conf \
    --log-level INFO \
    --log-file /tmp/rclone-Icedrive-Secure.log \
    --addr 0.0.0.0:9191 \
    --user brandon \
    --pass SUPER_SECURE_PASS_HERE \
    sftp REMOTE_NAME:

[Install]
WantedBy=default.target

```

## Conclusion

This is just the tip of the iceburg when it comes to Rclone! Another popular feature is automatically [encrypting](https://rclone.org/crypt/) files uploaded to cloud storage. Once you have everything configured to your liking, you can synchronize the file under `~/.config/rclone/rclone.conf` across all your machines.