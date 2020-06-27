---
title: "PDF To Kindle"
date: 2020-06-14T21:54:21-04:00
draft: false
tags: []
---

This post will outline a process I take in order to get content from a website onto my Kindle.

## Suggested Software

- To save a webpage as a PDF, we will use [WeasyPrint](https://weasyprint.org/).
- To convert the PDF into a more Kindle readable format, including converting math type properly, we're going to use [k2pdfopt](https://www.willus.com/k2pdfopt/).
- Finally we're going to use [Calibre](https://calibre-ebook.com/) to copy metadata and convert to an ebook format.

```bash
sudo apt install weasyprint k2pdfopt calibre
```

## Process

Now I'll show how we can take the [Noise Protocol specification](http://noiseprotocol.org/noise.html) and send it to the Kindle.

First let's download the page as a PDF

```bash
weasyprint https://noiseprotocol.org/noise.html noise.pdf
```

Then let's use `k2pdfopt` to convert the PDF to a more Kindle friendly format,

```bash
k2pdfopt noise.pdf -ui- -x
```

This will produce the file `noise_k2opt.pdf`, but sadly without the metadata. We can copy that over,

```bash
ebook-meta noise.pdf --to-opf temp.opf && \
ebook-meta noise_k2opt.pdf --from-opf temp.opf && \
rm temp.opf
```

Finally we can convert it to a Kindle friendly file format.

```bash
ebook-convert noise_k2opt.pdf noise.azw3
```

This will give us `noise.azw3` which we can then transfer over to the Kindle.