---
title: "Using the DNS-01 Challenge to obtain a wildcard certificate on Letsecnrypt"
date: 2023-09-18T17:42:10-04:00
draft: false
tags: []
math: false
medium_enabled: false
---

Letsencrypt lets anyone get a free SSL certificate in an easily automated way. It verifies that the user is allowed to issue a certificate for that domain by issuing a *challenge*. Lets say that I want a certificate for `exampledomain.com`. The defaults for most clients is to use the `HTTP-01` challenge. This requires that we have a webserver installed on that domain running on port 80. As part of the challenge, the Letsencrypt client will drop a file within the appropriate webserver folder so that it gets served at `http://exampledomain.com/.well-known/acme-challenge/<token>`. For example on `nginx` this could be at `/var/www/exampledomain.com/.well-known/acme-challenge/<token>`.  The Letsencrypt server will then verify that the file exists before issuing the certificate.

This easily works for one domain, but what if we have many sub-domains we want added to the certificate? With the `HTTP-01` challenge, we need to test each sub-domain individually. Alternatively, we can use the `DNS-01` challenge to get issued a wildcard certificate. With one wildcard certificate (e.g `*.exampledomain.com`) we can secure `a.exampledomain.com`, `b.exampledomain.com` and many more!

Letsecnrypt verifies that the user is allowed to claim all these subdomains, by seeing if the user has access to the DNS zone file for that domain. The idea is that if the user is able to change the DNS anyways, then the user could've gone through the process of installing a webserver at that IP. With access to the DNS zone file, the user would have to create a `TXT` record. 

Now this process could be done manually on Certbot by using the `--manual` flag. However, in the spirit of automation, there are many plugins existent to help streamline the process. This list of [DNS providers](https://community.letsencrypt.org/t/dns-providers-who-easily-integrate-with-lets-encrypt-dns-validation/86438) shows which provider supports this feature and in what clients.

If your provider isn't supported on this list, not all hope is lost. Under the manual plugin one can use the  [hooks](https://certbot.eff.org/docs/using.html#hooks) `--manual-auth-hook` and `--manual-cleanup-hook` to execute external scripts to access the DNS provider's API.

This wiki page for [Certbot](https://eff-certbot.readthedocs.io/en/stable/using.html#dns-plugins) shows the list of supported providers and how to structure the command line arguments. For example, I use `Nginx` as my webserver and Linode as my DNS nameserver.

```bash
certbot certonly \
  --dns-linode \
  --dns-linode-credentials ~/.secrets/certbot/linode.ini \
  -d *.exampledomain.com
```

