---
title: Week 1
showthedate: false
---

## Replication

The ultimate standard for strengthening scientific evidence is replication of finding and conducting studies with independent

- Investigators
- Data
- Analytical Methods
- Laboratories
- Instruments

Replication is particularly important in studies that can impact broad policy or regulatory decisions



### What's wrong with replication?

Some studies cannot be replicated

- No time, opportunistic
- No money
- Unique

*Reproducible Research:* Make analytic data and code available so that others may reproduce findings



Reproducibility bridges the gap between replication which is awesome and doing nothing.



## Why do we need reproducible research?

New technologies increasing data collection throughput; data are more complex and extremely high dimensional

Existing databases can be merged into new "megadatabases"

Computing power is greatly increased, allowing more sophisticated analyses

For every field "X" there is a field "Computational X"



## Research Pipeline

Measured Data -> Analytic Data -> Computational Results -> Figures/Tables/Numeric Summaries -> Articles -> Text

Data/Metadata used to develop test should be made publically available

The computer code and fully specified computational procedures used for development of the candidate omics-based test should be made sustainably available

"Ideally, the computer code that is released will encompass all of the steps of computational analysis, including all data preprocessing steps. All aspects of the analysis needs to be transparently reported" -- IOM Report



### What do we need for reproducible research?

- Analytic data are available
- Analytic code are available
- Documentation of code and data
- Standard means of distribution



### Who is the audience for reproducible research?

Authors:

- Want to make their research reproducible
- Want tools for reproducible research to make their lives easier (or at least not much harder)

Readers:

- Want to reproduce (and perhaps expand upon) interesting findings
- Want tools for reproducible research to make their lives easier.

### Challenges for reproducible research

- Authors must undertake considerable effort to put data/results on the web (may not have resources like a web server)
- Readers must download data/results individually and piece together which data go with which code sections, etc.
- Readers may not have the same resources as authors
- Few tools to help authors/readers

### What happens in reality

Authors:

- Just put stuff on the web
- (Infamous for disorganization) Journal supplementary materials
- There are some central databases for various fields (e.g biology, ICPSR)

Readers:

- Just download the data and (try to) figure it out
- Piece together the software and run it

## Literate (Statistical) Programming

An article is a stream of text and code

Analysis code is divided into text and code "chunks"

Each code chunk loads data and computes results

Presentation code formats results (tables, figures, etc.)

Article text explains what is going on

Literate programs can be weaved to produce human-readable documents and tagled to produce machine-readable documents

Literate programming is a general concept that requires

1. A documentation language (human readable)
2. A programming language (machine readable)

Knitr is an R package that brings a variety of documentation languages such as Latex, Markdown, and HTML

### Quick summary so far

Reproducible research is important as a minimum standard, particularly for studies that are difficult to replicate

Infrastructure is needed for creating and distributing reproducible document, beyond what is currently available

There is a growing number of tools for creating reproducible documents



**Golden Rule of Reproducibility: Script Everything**

## Steps in a Data Analysis

1. Define the question
2. Define the ideal data set
3. Determine what data you can access
4. Obtain the data
5. Clean the data
6. Exploratory data analysis
7. Statistical prediction/modeling
8. Interpret results
9. Challenge results
10. Synthesize/write up results
11. Create reproducible code

"Ask yourselves, what problem have you solved, ever, that was worth solving, where you knew all of the given information in advance? Where you didn't have a surplus of information and have to filter it out, or you had insufficient information and have to go find some?" -- Dan Myer

Defining a question is the kind of most powerful dimension reduction tool you can ever employ.

### An Example for #1

**Start with a general question**

Can I automatically detect emails that are SPAM or not?

**Make it concrete**

Can I use quantitative characteristics of emails to classify them as SPAM?

### Define the ideal data set

The data set may depend on your goal

- Descriptive goal -- a whole population
- Exploratory goal -- a random sample with many variables measured
- Inferential goal -- The right population, randomly sampled
- Predictive goal -- a training and test data set from the same population
- Causal goal -- data from a randomized study
- Mechanistic goal -- data about all components of the system

### Determine what data you can access

Sometimes you can find data free on the web

Other times you may need to buy the data

Be sure to respect the terms of use

If the data don't exist, you may need to generate it yourself.

### Obtain the data

Try to obtain the raw data

Be sure to reference the source

Polite emails go a long way

If you load the data from an Internet source, record the URL and time accessed

### Clean the data

Raw data often needs to be processed

If it is pre-processed, make sure you understand how

Understand the source of the data (census, sample, convenience sample, etc)

May need reformatting, subsampling -- record these steps

**Determine if the data are good enough** -- If not, quit or change data

### Exploratory Data Analysis

Look at summaries of the data

Check for missing data

-> Why is there missing data?

Look for outliers

Create exploratory plots

Perform exploratory analyses such as clustering

If it's hard to see your plots since it's all bunched up, consider taking the log base 10 of an axis

`plot(log10(trainSpan$capitalAve + 1) ~ trainSpam$type)`

### Statistical prediction/modeling

Should be informed by the results of your exploratory analysis

Exact methods depend on the question of interest

Transformations/processing should be accounted for when necessary

Measures of uncertainty should be reported.

### Interpret Results

Use the appropriate language

- Describes
- Correlates with/associated with
- Leads to/Causes
- Predicts

Gives an explanation

Interpret Coefficients

Interpret measures of uncertainty

### Challenge Results

Challenge all steps:

- Question
- Data Source
- Processing
- Analysis
- Conclusions

Challenge measures of uncertainty

Challenge choices of terms to include in models

Think of potential alternative analyses

### Synthesize/Write-up Results

Lead with the question

Summarize the analyses into the story

Don't include every analysis, include it

- If it is needed for the story
- If it is needed to address a challenge
- Order analyses according to the story, rather than chronologically
- Include "pretty" figures that contribute to the story

### In the lecture example...

Lead with the question

​	Can I use quantitative characteristics of the emails to classify them as SPAM?

Describe the approach

​	Collected data from UCI -> created training/test sets

​	Explored Relationships

​	Choose logistic model on training set by cross validation

​	Applied to test, 78% test set accuracy

Interpret results

​	Number of dollar signs seem reasonable, e.g. "Make more money with Viagra $ $ $ $"

Challenge Results

​	78% isn't that great

​	Could use more variables

​	Why use logistic regression?



## Data Analysis Files

Data

- Raw Data
- Processed Data

Figures

- Exploratory Figures
- Final Figures

R Code

- Raw/Unused Scripts
- Final Scripts
- R Markdown Files

Text

- README files
- Text of Analysis/Report

### Raw Data

Should be stored in the analysis folder

If accessed from the web, include URL, description, and date accessed in README

### Processed Data

Processed data should be named so it is easy to see which script generated the data

The processing script -- processed data mapping should occur in the README

Processed data should be tidy

### Exploratory Figures

Figures made during the course of your analysis, not necessarily part of your final report

They do not need to be "pretty"

### Final Figures

Usually a small subset of the original figures

Axes/Colors set to make the figure clear

Possibly multiple panels

### Raw Scripts

May be less commented (but comments help you!)

May be multiple versions

May include analyses that are later discarded

### Final Scripts

Clearly commented

- Small comments liberally - what, when, why, how

- Bigger commented blocks for whole sections

Include processing details

Only analyses that appear in the final write-up

### R Markdown Files

R Markdown files can be used to generate reproducible reports

Text and R code are integrated

Very easy to create in RStudio

### Readme Files

Not necessary if you use R Markdown

Should contain step-by-step instructions for analysis

### Text of the document

It should contain a title, introduction (motivation), methods (statistics you used), results (including measures of uncertainty), and conclusions (including potential problems)

It should tell a story

It should not include every analysis you performed

References should be included for statistical methods
