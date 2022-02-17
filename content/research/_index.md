---
Title: Research
Description: A list of my research Projects
---

**[Quick List of Publications](publications)**

**Broad Research Interests:** Automated Reasoning, Artificial Intelligence, Formal Methods

## Logic-Based AI
Working with [Dr. Selmer Bringsjord](https://homepages.rpi.edu/~brings/) and others in the [RAIR Lab](https://rair.cogsci.rpi.edu/) to
design and implement artificial intelligent agents using computational logic. I'm particularly interested in:
- Explainability through verifiable chains of inference
- Defeasible reasoning under uncertainty
- Reasoning about agents and their cognitive states
- Automated planning under ethical constraints


## Symbolic Methods for Cryptography
Working with [Dr. Andrew Marshall](https://www.marshallandrew.net/) and others in applying term reasoning within computational logic
towards cryptography. This collaboration was previously funded under an ONR grant. We are interested in applying techniques such
as unification and term rewriting to the following areas:
- Block Ciphers
- Secure Multi-party Computation
- Authentication
- Commitment Schemes

Together we built [CryptoSolve](https://github.com/symcollab/CryptoSolve), a symbolic cryptographic analysis tool, and made it publically available on GitHub. I wrote the term algebra and rewrite libraries, and contributed to the mode of operation library and some unification algorithms.
I still help maintain the codebase, as well as contribute to our current work on Garbled Circuits. We previously presented our work
at  [UNIF 2020](https://www3.risc.jku.at/publications/download/risc_6129/proceedings-UNIF2020.pdf#page=58) ([slides](/files/research/UNIF2020-Slides.pdf)), FROCOS 2021, and soon at WRLA 2022.

I've written a few [notes](termreasoning) about term reasoning.

Collaborators:
- NRL: Catherine Meadows
- UMW: [Andrew Marshall]((https://www.marshallandrew.net/)), Veena Ravishankar
- UT Dallas: Serdar Erbatur
- SUNY Albany: [Paliath Narendran](https://www.cs.albany.edu/~dran/), Wei Du 
- Clarkson University: [Christopher Lynch](https://people.clarkson.edu/~clynch/), Hai Lin



## Reinforcement Learning

**Deep Reinforcement Learning:** With [Dr. Ron Zacharski](http://zacharski.org/) I focused on how to make deep reinforcement learning
algorithms more sample efficient. That is, how can we make it so that the RL agent learns more from every observation to make it so that
we achieve our goal faster. With that goal in mind, I built out a Reinforcement Learning library written in PyTorch to help benchmark
my ideas. 


*Links:*

|                                                              |                                                              |                                                              |
| ------------------------------------------------------------ | ------------------------------------------------------------ | ------------------------------------------------------------ |
| [RL Library on Github](https://github.com/brandon-rozek/rltorch) | [Interactive Demonstrations Library](https://github.com/brandon-rozek/gyminteract) | [Undergraduate Honors Thesis](/files/research/honorsthesis.pdf) ([Eagle Scholar Entry](https://scholar.umw.edu/student_research/305/)) |
| [Undergraduate Honors Defense](/files/research/ExpeditedLearningInteractiveDemo.pptx) | [QEP Algorithm Slides](/files/research/QEP.pptx)             | [More...](deepreinforcementlearning)                         |



**Reinforcement Learning:** Studied the fundamentals of reinforcement learning with [Dr. Stephen Davies](http://stephendavies.org/). We went over the fundamentals such as value functions, policy functions, how we can describe our environment as a markov decision processes, etc.

[Notes and Other Goodies](reinforcementlearning) / [Github Code](https://github.com/brandon-rozek/ReinforcementLearning)




## Other

[**Programming Languages:**](proglang) Back in the Fall of 2018, under the guidance of Ian Finlayson, I worked towards creating a programming language similar to SLOTH (Simple Language of Tiny Heft). [SLOTH Code](https://github.com/brandon-rozek/SLOTH)

Before this study, I worked through a great book called ["Build your own Lisp"](https://www.buildyourownlisp.com/).


[**Competitive Programming:**](progcomp) Studying algorithms and data structures necessary for competitive programming. Attended ACM ICPC in November 2018/2019 with a team of two other students.

**Cluster Analysis:** The study of grouping similar observations without any prior knowledge. I studied this topic by deep diving Wikipedia articles under the guidance of Dr. Melody Denhere during Spring 2018. **[Extensive notes](clusteranalysis)**

[**Excitation of Rb87**](rb87): Worked in a Quantum Research lab alongside fellow student Hannah Killian under the guidance of Dr. Hai Nguyen. I provided software tools and assisted in understanding the mathematics behind the phenomena. 

[Modeling Population Dynamics of Incoherent and Coherent Excitation](/files/research/modellingpopulationdynamics.pdf)

[Coherent Control of Atomic Population Using the Genetic Algorithm](/files/research/coherentcontrolofatomicpopulation.pdf)



[**Beowulf Cluster:**](lunac) In order to circumvent the frustrations I had with simulation code taking a while, I applied and received funding to build out a Beowulf cluster for the Physics department. Dr. Maia Magrakvilidze was the advisor for this project. [LUNA-C Poster](/files/research/LUNACposter.pdf)

