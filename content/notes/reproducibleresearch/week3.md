## tl;dr

People are busy, especially managers and leaders. Results of data analyses are sometimes presented in oral form, but often the first cut is presented via email.

It is often useful therefore, to breakdown the results of an analysis into different levels of granularity/detail

## Hierarchy of Information: Research Paper

- Title / Author List
  - Speaks about what the paper is about
  - Hopefully interesting
  - No detail
- Abstract
  - Motivation of the problem
  - Bottom Line Results
- Body / Results
  - Methods
  - More detailed results
  - Sensitivity Analysis
  - Implication of Results
- Supplementary Materials / Gory Details
  - Details on what was done
- Code / Data / Really Gory Details
  - For reproducibility



## Hierarchy of Information: Email Presentation

- Subject Line / Subject Info
  - At a minimum: include one
  - Can you summarize findings in one sentence?
- Email Body
  - A brief description of the problem / context: recall what was proposed and executed; summarize findings / results. (Total of 1-2 paragraphs)
  - If action is needed to be taken as a result of this presentation, suggest some options and make them as concrete as possible
  - If questions need to be addressed, try to make them yes / no
- Attachment(s)
  - R Markdown file
  - knitr report
  - Stay Concise: Don't spit out pages of code
- Links to Supplementary Materials
  - Code / Software / Data
  - Github Repository / Project Website



## DO: Start with Good Science

- Remember: Garbage, in, garbage out
- Find a coherent focused question. This helps solve many problems
- Working with good collaborators reinforces good practices
- Something that's interesting to you will hopefully motivate good habits

## DON'T: Do Things By Hand

- Editing spreadsheets of data to "clean it up"
  - Removing outliers
  - QA / QC
  - Validating
- Editing tables or figures (e.g rounding, formatting)
- Downloading data from a website
- Moving data around your computer, splitting, or reformatting files.

Things done by hand need to precisely documented (this is harder than it sounds!)

## DON'T: Point and Click

- Many data processing / statistical analysis packages have graphical user interfaces (GUIs)
- GUIs are convenient / intuitive but the actions you take with a GUI can be difficult for others to reproduce
- Some GUIs produce a log file or script which includes equivalent commands; these can be saved for later examination
- In general, be careful with data analysis software that is highly interactive; ease of use can sometimes lead to non-reproducible analyses.
- Other interactive software, such as text editors, are usually fine.


## DO: Teach a Computer

If something needs to be done as part of your analysis / investigation, try to teach your computer to do it (even if you only need to do it once) 

In order to give your computer instructions, you need to write down exactly what you mean to do and how it should be done. Teaching a computer almost guarantees reproducibility

For example, by, hand you can

       	1. Go to the UCI Machine Learning Repository at http://archive.ics.uci.edu/mil/
        	2. Download the Bike Sharing Dataset

Or you can teach your computer to do it using R

```R
download.file("http://archive.ics.uci.edu/ml/machine-learning-databases/00275/Bike-Sharing-Dataset.zip", "ProjectData/Bike-Sharing-Dataset.zip")
```

Notice here that:

- The full URL to the dataset file is specified
- The name of the file saved to your local computer is specified
- The directory to which the filed was saved is specified ("ProjectData")
- Code can always be executed in R (as long as link is available)

## DO: Use Some Version Control

It helps you slow things down by adding changes into small chunks. (Don't just do one massive commit). It allows one to track / tag snapshots so that one can revert back to older versions of the project. Software like Github / Bitbucket / SourceForge make it easy to publish results.



## DO: Keep Track of Your Software Environment

If you work on a complex project involving many tools / datasets, the software and computing environment can be critical for reproducing your analysis.

**Computer Architecture**: CPU (Intel, AMD, ARM), CPU Architecture, GPUs

**Operating System**: Windows, Mac OS, Linux / Unix

**Software Toolchain**: Compilers, interpreters, command shell, programming language (C, Perl, Python, etc.), database backends, data analysis software

**Supporting software / infrastructure**: Libraries, R packages, dependencies

**External dependencies**: Websites, data repositories, remote databases, software repositories

**Version Numbers:** Ideally, for everything (if available)

This function in R helps report a bunch of information relating to the software environment

```R
sessionInfo()
```

## DON'T: Save Output

Avoid saving data analysis output (tables, figures, summaries, processed data, etc.), except perhaps temporarily for efficiency purposes.

If a stray output file cannot be easily connected with the means by which it was created, then it is not reproducible

Save the data + code that generated the output, rather than the output itself.

Intermediate files  are okay as long as there is clear documentation of how they were created.

## DO: Set Your Seed

Random number generators generate pseudo-random numbers based on an initial seed (usually a number or set of numbers)

​	In R, you can use the `set.seed()` function to set the seed and to specify the random number generator to use

Setting the seed allows for the stream of random numbers to be exactly reproducible

Whenever you generate random numbers for a non-trivial purpose, **always set the seed**.

## DO: Think About the Entire Pipeline

- Data analysis is a lengthy process; it is not just tables / figures/ reports
- Raw data -> processed data -> analysis -> report
- How you got the end is just as important as the end itself
- The more of the data analysis pipeline you can make reproducible, the better for everyone

## Summary: Checklist

- Are we doing good science?
  - Is this interesting or worth doing?
- Was any part of this analysis done by hand?
  - If so, are those parts precisely documented?
  - Does the documentation match reality?
- Have we taught a computer to do as much as possible (i.e. coded)?
- Are we using a version control system?
- Have we documented our software environment?
- Have we saved any output that we cannot reconstruct from original data + code?
- How far back in the analysis pipeline can we go before our results are no longer (automatically reproducible)


##  Replication and Reproducibility

Replication

- Focuses on the validity of the scientific claim
- Is this claim true?
- The ultimate standard for strengtening scientiffic evidence
- New investigators, data, analytical methods, laboratories, instruments, etc.
- Particularly important in studies that can impact broad policy or regulatory decisions.

Reproducibility

- Focuses on the validity of the data analysis
- Can we trust this analysis?
- Arguably a minimum standard for any scientific study
- New investigators, same data, same methods
- Important when replication is impossible

## Background and Underlying Trends

- Some studies cannot be replicated: No time, no money, or just plain unique / opportunistic
- Technology is increasing data collection throughput; data are more complex and high-dimensional
- Existing databases can be merged to become bigger databases (but data are used off-label)
- Computing power allows more sophisticated analyses, even on "small" data
- For every field "X", there is a "Computational X"

## The Result?

- Even basic analyses are difficult to describe
- Heavy computational requirements are thrust upon people without adequate training in statistics and computing
- Errors are more easily introduced into long analysis pipelines
- Knowledge transfer is inhibited
- Results are difficult to replicate or reproduce
- Complicated analyses cannot be trusted

## What Problem Does Reproducibility Solve?

What we get:

- Transparency
- Data Availability
- Software / Methods of Availability
- Improved Transfer of Knowledge

What we do NOT get

- Validity / Correctness of the analysis

An analysis can be reproducible and still be wrong

We want to know 'can we trust this analysis

Does requiring reproducibility deter bad analysis?

## Problems with Reproducibility

The premise of reproducible research is that with data/code available, people can check each other and the whole system is self-correcting

- Addresses the most "downstream" aspect of the research process -- Post-publication
- Assumes everyone plays by the same rules and wants to achieve the same goals (i.e. scientific discovery)

## Who Reproduces Research?

- For reproducibility to be effective as a means to check validity, someone needs to do something
  - Re-run the analysis; check results match
  - Check the code for bugs/errors
  - Try alternate approaches; check sensitivity
- The need for someone to do something is inherited from traditional notion of replication
- Who is "someone" and what are their goals?

## The Story So Far

- Reproducibility brings transparency (wrt code+data) and increased transfer of knowledge
- A lot of discussion about how to get people to share data
- Key question of "can we trust this analysis"? is not addressed by reproducibility
- Reproducibility addresses potential problems long after they've occurred ("downstream")
- Secondary analyses are inevitably colored by the interests/motivations of others.

## Evidence-based Data Analysis

- Most data analyses involve stringing together many different tools and methods
- Some methods may be standard for a given field, but others are often applied ad hoc
- We should apply throughly studied (via statistical research), mutually agreed upon methods to analyze data whenever possible
- There should be evidence to justify the application of a given method

## Evidence-based Data Analysis

- Create analytic pipelines from evidence-based components - standardize it
- A deterministic statistical machine
- Once an evidence-based analytic pipeline is established, we shouldn't mess with it
- Analysis with a "transparent box"
- Reduce the "research degrees of freedom"
- Analogous to a pre-specified clinical trial protocol

## Case Study: Estimating Acute Effects of Ambient Air Pollution Exposure

- Acute / Short-term effects typically estimated via panel studies or time series studies
- Work originated in late 1970s early 1980s
- Key question "Are short-term changes in pollution associated with short-term changes in a population health outcome?"
- Studies are usually conducted at a community level
- Long history of statistical research investigating proper methods of analysis

## Case Study: Estimating Acute Effects of Ambient Air Pollution Exposure

- Can we encode everything that we have found in statistical / epidemiological research into a single package?
- Time series studies do not have a huge range of variation; typically involves similar types of data and similar questions
- We can create a deterministic statistical machine for this area?

## DSM Modules for Time Series Studies of Air Pollution and Health

1. Check for outliers, high leverage, overdispersion
2. Fill in missing data? No!
3. Model selection: Estimate degrees of freedom to adjust for unmeasured confounders
   -  Other aspects of model not as critical
4. Multiple lag analysis
5. Sensitivity analysis wrt
   -  Unmeasured confounder adjustment
   -  Influential points

## Where to Go From Here?

- One DSM is not enough, we need many!
- Different problems warrant different approaches and expertise
- A curated library of machines providing state-of-the-art analysis pipelines
- A CRAN/CPAN/CTAN/... for data analysis
- Or a "Cochrane Collaboration" for data analysis

## A Curated Library of Data Analysis

- Provide packages that encode data analysis pipelines for given problems, technologies, questions
- Curated by experts knowledgeable in the field
- Documentation / References given supporting module in the pipeline
- Changes introduced after passing relevant benchmarks/unit tests

## Summary

- Reproducible research is important, but does not necessarily solve the critical question of whether a data analysis is trustworthy
- Reproducible research focuses on the most "downstream" aspect of research documentation
- Evidence-based data analysis would provide standardized best practices for given scientific areas and questions
- Gives reviewers an important tool without dramatically increases the burden on them
- More effort should be put into improving the quality of "upstream" aspects of scientific research