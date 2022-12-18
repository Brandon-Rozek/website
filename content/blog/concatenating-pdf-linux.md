---
title: "Concatenating PDF files in Linux"
date: 2022-12-18T18:38:44-05:00
draft: false
tags: []
math: false
---

Every so often I need to combine several images into a single PDF. First, to convert an image to a PDF we can use `imagemagick`.

```bash
convert -quality 100 Image.png Scanned.pdf
```

To combine or concatenate multiple PDF files, we can use `ghostscript`.

```bash
gs -sDEVICE=pdfwrite \
   -sOUTPUTFILE=output.pdf \
   -dNOPAUSE \
   -dBATCH \
   input0.pdf input1.pdf input2.pdf
```

| Flag           | Description                                                  |
| -------------- | ------------------------------------------------------------ |
| `-sDEVICE`     | Device used for processing the output file type. Use `pdfwrite` to write to a PDF file. |
| `-sOUTPUTFILE` | Path to save the resulting file output.                      |
| `-dNOPAUSE`    | Disables the prompting and pausing at the end of each page.  |
| `-dBATCH`      | Finishes interpreting after processing the inputted files    |

Alternatively you can use `pdftk`

```bash
pdftk input0.pdf input1.pdf input2.pdf \
	cat output output.pdf
```

Lastly, you can also use `imagemagick`. Do note, however, that this program often leads to larger file sizes.

```bash
convert input0.pdf input1.pdf input2.pdf output.pdf
```

## Aside: Pixel Densities

One issue I came across is that the pages were of different sizes. This is often because the pages can be of different pixel densities.

To check run `pdfimages` and look at the 3rd to last and 2nd to last columns:

```bash
pdfimages -list filename.pdf 
```

```
page   num  type   width height color comp bpc  enc interp  object ID x-ppi y-ppi size ratio
--------------------------------------------------------------------------------------------
   1     0 image     613    77  rgb     3   8  jpeg   no         8  0  1071  1076 9456B 6.7%
   1     1 image    2692  3496  rgb     3   8  jpeg   no         9  0   329   329  418K 1.5%
   2     2 image     613    77  rgb     3   8  jpeg   no         8  0   915   919 9456B 6.7%
   2     3 image    2300  3016  rgb     3   8  jpeg   no        15  0   282   282  322K 1.6%
   3     4 image     613    77  rgb     3   8  jpeg   no         8  0   937   942 9456B 6.7%
   3     5 image    2356  3024  rgb     3   8  jpeg   no        21  0   288   288  150K 0.7%
   4     6 image    1686  2200  rgb     3   8  jpeg   no        27  0   204   204  622K 5.7%
   5     7 image    5100  7016  rgb     3   8  jpeg   no        33  0   600   600 1193K 1.1%
   6     8 image     613    77  rgb     3   8  jpeg   no         8  0  1104  1110 9456B 6.7%
   6     9 image    2776  3720  rgb     3   8  jpeg   no        38  0   339   339  231K 0.8%
   7    10 image     613    77  rgb     3   8  jpeg   no         8  0   939   943 9456B 6.7%
   7    11 image    2360  3072  rgb     3   8  jpeg   no        44  0   289   289  151K 0.7%
```

We can then use `imagemagick` to enforce a certain pixel density. The tradeoff being that the file size might increase.

```bash
convert -density 300 input.pdf output.pdf
```

If you happen to know a different way to enforce a pixel density that doesn't have a file size increase tradeoff. Please get in touch.
