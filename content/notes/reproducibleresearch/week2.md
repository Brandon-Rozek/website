## Coding Standards for R

1. Always use text files/text editor
2. Indent your code
3. Limit the width of your code (80 columns?)
4. Author suggests indentation of 4 spaces at minimum
5. Limit the length of individual functions

## What is Markdown?

Markdown is a text-to-HTML conversion tool for web writers. Markdown allows you to write using an easy-to-read, easy-to-write plain text format, then convert it structurally to valid XHTML/HTML

## Markdown Syntax

`*This text will appear italicized!*`

*This text will appear italicized!*

`**This text will appear bold!**`

**This text will appear bold**

`## This is a secondary heading`

`###This is a tertiary heading `

## This is a secondary heading

### This is a tertiary heading

Unordered Lists

`- first item in list`

`- second item in list`

- first item in list
- second item in list

Ordered lists

`1. first item in list`

`2. second item in list`

`3. third item in list`

1. first item in list
2. second item in list
3. third item in list

Create links

`[Download R](http://www.r-project.org/)`

[Download R](http://www.r-project.org/)

Advanced linking

`I spent so much time reading [R bloggers][1] and [Simply Statistics][2]!`

`[1]: http://www.r-bloggers.com/	"R bloggers"`

`[2]: http://simplystatistics.org/	"Simply Statistics"`

I spent so much time reading [R bloggers][1] and [Simply Statistics][2]!

[1]: http://www.r-bloggers.com/	"R bloggers"

[2]: http://simplystatistics.org/	"Simply Statistics"

Newlines require a double space after the end of a line

## What is Markdown?

Created by John Gruber and Aaron Swartz. It is a simplified version of "markup" languages. It allows one to focus on writing as opposed to formatting. Markdown provides a simple, minimal, and intuitive way of formatting elements. 

You can easily convert Markdown to valid HTML (and other formats) using existing tools.

## What is R Markdown?

R Markdown is the integration of R code with markdown. It allows one to create documents containing "live" R code. R code is evaluated as part of the processing of the markdown and its results are inserted into the Markdown document. R Markdown is a core tool in **literate statistical programming**

R Markdown can be converted to standard markdown using `knitr` package in R. Markdown can then be converted to HTML using the `markdown` package in R. This workflow can be easily managed using R Studio. One can create powerpoint like slides using the `slidify` package.

## Problems, Problems

- Authors must undertake considerable effort to put data/results on the web
- Readers must download data/results individually and piece together which data go with which code sections, etc.
- Authors/readers must manually interact with websites
- There is no single documents to integrate data analysis with textual representations; i.e data, code, and text are not linked

One of the ways to resolve this is to simply put the data and code together in the same document so that people can execute the code in the right order, and the data are read at the right times. You can have a single document that integrates the data analysis with all the textual representations.

## Literate Statistical Programming

- Original idea comes from Don Knuth
- An article is a stream of **text** and **code**
- Analysis code is divded into text and code "chunks"
- Presentation code formats results (tables, figures, etc.)
- Article text explains what is going on
- Literate programs are weaved to produce human-readable documents and tangled to produce machine-readable documents.

## Literate Statistical Programming

- Literate programming is a general concept. We need
  - A documentation language
  - A programming language
- `knitr` supports a variety of documentation languages

## How Do I Make My Work Reproducible?

- Decide to do it (ideally from the start)
- Keep track of everything, hopefully through a version control system
- Use software in which operations can be coded
- Don't save output
- Save data in non-proprietary formats

## Literate Programming: Pros

- Text and code all in one place, logical order
- Data, results automatically updated to reflect external changes
- Code is live -- automatic "regression test" when building a document

## Literate Programming: Cons

- Text and code are all in one place; can make documents difficult to read, especially if there is a lot of code
- Can substantially slow down processing of documents (although there are tools to help)

## What is Knitr Good For?

- Manuals
- Short/Medium-Length technical documents
- Tutorials
- Reports (Especially if generated periodically)
- Data Preprocessing documents/summaries

## What is knitr NOT good for?

- Very long research articles
- Complex time-consuming computations
- Documents that require precise formatting

## Non-GUI Way of Creating R Markdown documents

```R
library(knitr)
setwd(<working directory>)
knit2html('document.Rmd')
browseURL('document.html')
```

## A few notes about knitr

- knitr will fill a new document with filler text; delete it

- Code chunks begin with ` ```{r}` and ends with ` ``` ` 

- All R code goes in between these markers

- Code chunks can have names, which is useful when we start making graphics

  ` ```{r firstchunk}`

  `## R code goes here`

  ` ``` `

- By default, code in a code chunk is echoed, as will the results of the computation (if there are results to print)

## Processing of knitr documents

- You write RMarkdown document (.Rmd)
- knitr produces a Markdown document (.md)
- knitr converts the Markdown document into HTML (by default)
- .Rmd -> .md -> .html
- You should NOT edit (or save) the .md or .html documents until you are finished

## Inline Text Computations

You can reference variable in RMarkdown through the following

```
`The current time is `r time`. My favorite random number is `r rand`
```

## Setting Global Options

- Sometimes we want to set options for every code chunk that are different from the defaults
- For example, we may want to suppress all code echoing and results output
- We have to write some code to set these global options

Example for suppressing all code chunks

```R
​```{r setoptions, echo=FALSE}
opts_chunk$set(echo=False, results = "hide")
​```
```

## Some Common Options

- Output
  - Results: "axis", "hide"
  - echo: TRUE, FALSE
- Figures
  - fig.height: numeric
  - fig.width: numeric

## Caching Computations

- What if one chunk takes a long time to run?
- All chunks have to be re-computed every time you re-knit the file
- The `cache=TRUE` option can be set on a chunk-by-chunk basis to store results of computation
- After the first run, results are loaded from cache

## Caching Caveats

- If the data or code (or anything external) changes, you need to re-run the cache code chunks
- Dependencies are not checked explicitly!!!!
- Chunks with significant *side effects* may not be cacheable

## Summary of knitr

- Literate statistical programming can be a useful way to put text, code, data, output all in one document
- knitr is a powerful tool for iterating code and text in a simple document format

