---
title: Week 4
showthedate: false
---

## The `cacher` Package for R

- Add-on package for R
- Evaluates code written in files and stores immediate results in a key-value database
- R expressions are given SHA-1 hash values so that changes can be tracked and code reevaluated if necessary
- "Chacher packages" can be built for distribution
- Others can "clone" an analysis and evaluate subsets of code or inspect data objects

The value of this is so other people can get the analysis or clone the analysis and look at subsets of the code. Or maybe more specifically data objects. People who want to run your code may not necessarily have the resources that you have. Because of that, they may not want to run the entire Markov chain Monte Carlo simulation that you did to get the posterior distribution or the histogram that you got at the end. 

But the idea is that you peel the onion a little bit rather than just go straight to the core. 

## Using `cacher` as an Author

1. Parse the R source file; Create the necessary cache directiories and subdirectories
2. Cycle through each expression in the source file
   - If an expression has never been evaluated, evaluate it and store any resulting R objects in the cache database
   - If any cached results exists, lazy-load the results from the cache database and move to the next expression
   - If an expression does not create any R objects (i.e, there is nothing to cache), add the expression to the list of expressions where evaluation needs to be forced
   - Write out metadata for this expression to the metadata file

- The `cachepackage` function creates a `cacher` package storing
  - Source File
  - Cached data objects
  - Metadata
- Package file is zipped and can be distributed
- Readers can unzip the file and immediately investigate its contents via `cacher` package

## Using `cacher` as a Reader

A journal article says

​	"... the code and data for this analysis can be found in the cacher package 092dcc7dda4b93e42f23e038a60e1d44dbec7b3f"

```R
library(cacher)
clonecache(id = "092dcc7dda4b93e42f23e038a60e1d44dbec7b3f")
clonecache(id = "092d") ## Same as above
# Created cache directory `.cache`
showfiles()
# [1] "top20.R"
sourcefile("top20.R")
```

## Cloning an Analysis

- Local directories are created
- Source code files and metadata are downloaded
- Data objects are *not* downloaded by default (may be really large)
- References to data objects are loaded and corresponding data can be lazy-loaded on demand

`graphcode()` gives a node graph representing the code

## Running Code

- The `runcode` function executes code in the source file
- By default, expressions that results in an object being created are not run and the resulting objects is lazy-loaded into the workspace
- Expressions not resulting in objects are evaluated

## Checking Code and Objects

- The `checkcode` function evaluates all expressions from scratch (no lazy-loading)
- Results of evaluation are checked against stored results to see if the results are the same as what the author calculated
  - Setting RNG seeds is critical for this to work
- The integrity of data objects can be verified with the `checkobjects` function to check for possible corruption of data perhaps during transit.

You can inspect data objects with `loadcache`. This loads in pointers to each of the data objects into the workspace. Once you access the object, it will transfer it from the cache.

## `cacher` Summary

- The `cacher` package can be used by authors to create cache packages from data analyses for distribution
- Readers can use the `cacher` package to inspect others' data analyses by examing cached computations
- `cacher` is mindful of readers' resources and efficiently loads only those data objects that are needed.

# Case Study: Air Pollution

Particulate Matter -- PM

When doing air pollution studies you're looking at particulate matter pollution. The dust is not just one monolithic piece of dirt or soot but it's actually composed of many different chemical constituents. 

Metals inert things like salts and other kinds of components so there's a possibility that a subset of those constituents are really harmful elements.

PM is composed of many different chemical constituents and it's important to understand that the Environmental Protection Agency (EPA) monitors the chemical  constituents of particulate matter and has been doing so since 1999 or 2000 on a national basis.

## What causes PM to be Toxic?

- PM is composed of many different chemical elements
- Some components of PM may be more harmful than others
- Some sources of PM may be more dangerous than others
- Identifying harmful chemical constituents may lead us to strategies for controlling sources of PM

## NMMAPS

- The National Morbidity, Mortality, and Air Pollution Study (NMMAPS) was a national study of the short-term health effects of ambient air pollution

- Focused primarily on particulate matter ($PM_{10}$) and Ozone ($O_3$) 

- Health outcomes include mortality from all causes and hospitalizations for cardiovascular and respiratory diseases

- Key publications

  - http://www.ncbi.nlm.nih.gov/pubmed/11098531
  - http://www.ncbi.nlm.nih.gov/pubmed/11354823

- Funded by the Heath Effects Institute

  - Roger Peng currently serves on the Health Effects Institute Health Review Committee

  ​

## NMMAPS and Reproducibility

- Data made available at the Internet-based Health and Air Pollution Surveillance System (http://www.ihapss.jhsph.edu)
- Research and software also available at iHAPSS
- Many studies (over 67 published) have been conducted based on the public data http://www.ncbi.nlm.nih.gov/pubmed/22475833
- Has served as an important test bed for methodological development

## What Causes Particulate Matter to be Toxic?

http://www.ncbi.nlm.nih.gov/pmc/articles/PMC1665439

- Lippmann et al. found strong evidence that NI modified the short-term effect of $PM_{10}$ across 60 US communities
- No other PM chemical constituent seemed to have the same modifying effect
- To simple to be true?

## A Reanalysis of the Lippmann et al. Study

http://www.ncbi.nlm.nih.gov/pmc/articles/PMC2137127

- Rexamine the data from NMMAPS and link with PM chemical constituent data
- Are the findings sensitive for levels of Nickel in New York City?

## Does Nickel Make PM Toxic?

- Long-term average nickel concentrations appear correlated with PM risk
- There appear to be some outliers on the right-hand side (New York City)

## Does Nickel Make PM Toxic?

One of the most important things about those three points to the right is those are called high leverage points. So the regression line can be very senstive to high leverage points. Removing those three points from the dataset brings the regression line's slope down a little bit. Which then produces a line that is no longer statistical significant (p-value about 0.31)

## What Have We Learned?

- New York does have very high levels of nickel and vanadium, much higher than any other US community
- There is evidence of a positive relationship between NI concentrations and $PM_{10}$ risk
- The strength of this relationship is highly sensitive to the observations from New York City
- Most of the information in the data is derived from just 3 observations

## Lessons Learned

- Reproducibility of NMMAPS allowed for a secondary analysis (and linking with PM chemical constituent data) investigating a novel hypothesis (Lippmann et al.)
- Reproducibility also allowed for a critique of that new analysis and some additional new analysis (Dominici et al.)
- Original hypothesis not necessarily invalidated, but evidence not as strong as originally suggested (more work should be done)
- Reproducibility allows for the scientific discussion to occur in a timely and informed manner
- This is how science works.



