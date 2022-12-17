---
title: "Quick CA for internal LAN"
date: 2020-04-18T16:26:53-04:00
draft: false
tags: ["Networking", "Security"]
---

Setting up trusted HTTPs inside a network without exposure to the Internet requires creating a Certificate Authority. The audience for this post is oriented for people setting up services in a small low threat model environment. Additional cautions should be applied when setting this up for a business, for example working off an intermediate CA. 

We're going to be using [CFSSL](https://blog.cloudflare.com/introducing-cfssl/), this is Cloudflare's PKI toolkit to accomplish this. To install on Ubuntu,

```bash
sudo apt install golang-cfssl
```

## Creating the CA

This tool makes heavy use of JSON for its configuration. To setup a CA, first let's create `csr_ca.json` that contains the following information

```json
{
  "CN": "Common Name",
  "key": {
    "algo": "rsa",
    "size": 2048 
  },
    "names": [
       {
         "C": "US",
         "O": "Orgnaization",
         "OU": "Organizational Unit",
         "ST": "Washington",
         "L": "Locality"
       }
    ]
}
```

Where `C` is the two-letter country code and `ST` is the full state name.

Then to create the certificate authority

```bash
cfssl gencert -initca csr_ca.json | cfssljson -bare ca
```

This will create the following files

| Filename   | Purpose                     |
| ---------- | --------------------------- |
| ca.pem     | Public Certificate          |
| ca-key.pem | Private Key                 |
| ca.csr     | Certificate Signing Request |

## Creating Certficates

Now we can create SSL certificates for whatever websites we wish by specifying in a file we'll call `csr_client.json`

```json
{
  "hosts": [
    "example.com",
    "*.example.com"
  ],
  "key": {
    "algo": "rsa",
    "size": 2048
  },
  "names": [
     {
       "C": "US",
       "O": "Orgnaization",
       "OU": "Organizational Unit",
       "ST": "Washington",
       "L": "Locality"
     }
  ]
}
```

Then to create the certs,

```bash
cfssl gencert -ca=ca.pem -ca-key=ca-key.pem csr_client.json | cfssljson -bare cert
```

It will create the private key, public certificate, and CSR just like the previous command. By default the certificate will last for one year and has the following usages:

- Signing
- Key Encipherment
- Server Authentication
- Client Authentication

To have more full grained control over the certificate usages and expiry time, I will defer you to the documentation. It involves creating another JSON file to pass as a flag into `cfssl gencert`.

## Trusting the CA

On Linux, I know of two different ways to trust the CA depending on your distrubtion.

### Ubuntu Derivative

First you need to copy  the `ca.pem` file over to `/usr/local/share/ca-certificates/`.

```bash
sudo mv ca.pem /usr/local/share/ca-certificates
```

Then you need to execute

```bash
sudo update-ca-certificates
```

### Fedora Derivative

Copy `ca.pem` over to `/etc/pki/ca-trust/source/anchors`.

```bash
sudo mv ca.pem /usr/pki/ca-trust/source/anchors
```

Then execute

```bash
sudo update-ca-trust
```

### Special Instructions for Firefox

Firefox has its own certificate store that you can add `ca.pem` to by accessing Preferences->Privacy & Security->Security->Certificates->View Certificates->Authorities->Import. The exact trail might have changed by the time you read this.

