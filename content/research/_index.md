---
Title: Research
Description: A list of my research Projects
---

**[Quick List of Publications](/publications/)**

**Broad Research Interests:** Automated Reasoning, Automated Planning, Artificial Intelligence, Formal Methods

Currently, I'm a Computer Science PhD Candidate at Rensselaer Polytechnic Institute. I enjoy using logic-based techniques and designing algorithms to solve problems.

Jump to:
- [Planning under uncertainty](#planning-under-uncertainty)
- [Logic](#logic)
- [Symbolic Methods for Cryptography](#symbolic-methods-for-cryptography)

## Planning under Uncertainty

My dissertation topic is on automatically finding and recognizing plans
when agents are uncertain about the environment but can compare the
uncertainty between events *qualitatively*. For example, it is totally
expected when we stack a block that it stays on the top. However, there is a
smaller likelihood that the block falls off.
How can we best make use of this qualitative uncertainty?
- Agents when operating under uncertainty will seek plans which maximize the likelihood of their goals.
I designed an algorithm for recognizing these plans under qualitative possibility theory. This work is supervised under [Selmer Bringsjord](https://kryten.mm.rpi.edu/selmerbringsjord.html) (Paper to be released soon)
- Additionally with Selmer Bringsjord in the [RAIR Lab](https://rair.cogsci.rpi.edu/), I created a framework that captures
situations where agents are able to bucket the likelihood of facts within their environment. I then provide an effective
techinque for using classical planners to find plans which maximize the agent's likelihood of success. ([Paper](/paper/2406.02))
- In the RAIR Lab, I also further developed [Spectra](https://github.com/rairlab/spectra) --
an automated planner built on automated theorem proving. I showed how a class of problems
under uncertainty can be easily encoded and wrote a question-answer algorithm
for ShadowProver so that Spectra can find plans under epistemic uncertainty. ([Paper](/paper/2405.01/))
- With [Junkyu Lee](https://researcher.ibm.com/researcher/view.php?person=ibm-Junkyu.Lee),
[Michael Katz](https://researcher.watson.ibm.com/researcher/view.php?person=ibm-Michael.Katz1),
[Harsha Kokel](https://harshakokel.com/), and [Shirin Sohrabi](https://researcher.watson.ibm.com/researcher/view.php?person=us-ssohrab) at IBM I developed an algorithm
for guiding hierarchical reinforcement agents under partial observability. Specifically,
I focused on situations where the agent knows what they don't know and compiled that knowledge
so that a fully-observable non-deterministic planner can decompose the overall problem. ([Paper](/paper/2406.01))

## Logic

Underlying my work in artificial intelligence and cryptography
is computational logic. In that regard, I have been able
work on problems from the underlying logic formalisms,
unification algorithms, to building
tools for interactive theorem provers.

- With [Andrew Tedder](https://sites.google.com/view/andrewjtedder/research), I'm currently working
on building a tool that checks if matrix models of given logic satisfies relevance properties.
- With [Andrew Marshall](https://www.marshallandrew.net/) and [Kimberly Cornell](https://www.albany.edu/cehc/faculty/kimberly-cornell), we're currently developing a new syntactic AC algorithm.
- With [Thomas Ferguson](https://faculty.rpi.edu/thomas-ferguson) and [James Oswald](https://jamesoswald.dev) we formalized a model theory for a fragment of the Deontic Cognitive Event Calculus.
- With James Oswald we've built interactive theorem provers and showed validity of large proofs in parallel using a high performance cluster.


Related Notes:

- [Automated Theorem Proving](atp/)
- [Term Reasoning](termreasoning/)
 

## Symbolic Methods for Cryptography
Worked with [Andrew Marshall](https://www.marshallandrew.net/) and others in applying term reasoning within computational logic
towards cryptography. This collaboration was previously funded under an ONR grant. We are interested in applying techniques such
as unification and term rewriting to the following areas:
- Block Ciphers
- Secure Multi-party Computation
- Authentication
- Commitment Schemes

Together we built [CryptoSolve](https://github.com/cryptosolvers/CryptoSolve), a symbolic cryptographic analysis tool, and made it publically available on GitHub. I wrote the term algebra and rewrite libraries, and contributed to the mode of operation library and some unification algorithms.
I still help maintain the codebase. We previously presented our work
at  [UNIF 2020](https://www3.risc.jku.at/publications/download/risc_6129/proceedings-UNIF2020.pdf#page=58) ([slides](/files/research/UNIF2020-Slides.pdf)), [FROCOS 2021](https://link.springer.com/chapter/10.1007/978-3-030-86205-3_14) ([slides](/files/slides/FROCOS2021.pdf)), [WRLA 2022](http://sv.postech.ac.kr/wrla2022/assets/files/pre-proceedings-WRLA2022.pdf#page=12) ([slides](/files/slides/wrla2022-slides.pdf)),
and [GandALF 2022](/paper/2209.01/).


Collaborators:
- NRL: Catherine Meadows
- UMW: [Andrew Marshall](https://www.marshallandrew.net/)
- UT Dallas: Serdar Erbatur
- SUNY Albany: [Paliath Narendran](https://www.cs.albany.edu/~dran/) and [Kimberly Cornell](https://www.albany.edu/cehc/faculty/kimberly-cornell)
- Clarkson University: [Christopher Lynch](https://people.clarkson.edu/~clynch/) and Hai Lin


Group Website: [https://cryptosolvers.github.io](https://cryptosolvers.github.io)

---

**Note:** From this point on, the projects listed happened over 5 years ago.

---

## Reinforcement Learning

During my undergraduate degree, I worked with [Dr. Ron Zacharski](http://zacharski.org/)
on making deep reinforcement learning algorithms more sample efficient with human feedback.

In my experimentation, I built out a Reinforcement Learning library in PyTorch.


*Links:*

|                                                              |                                                              |                                                              |
| ------------------------------------------------------------ | ------------------------------------------------------------ | ------------------------------------------------------------ |
| [RL Library on Github](https://github.com/brandon-rozek/rltorch) | [Interactive Demonstrations Library](https://github.com/brandon-rozek/gyminteract) | [Undergraduate Honors Thesis](/files/research/honorsthesis.pdf) ([Eagle Scholar Entry](https://scholar.umw.edu/student_research/305/)) |
| [Undergraduate Honors Defense](/files/research/ExpeditedLearningInteractiveDemo.pptx) | [QEP Algorithm Slides](/files/research/QEP.pptx)             | [More...](deepreinforcementlearning)                         |



[Dr. Stephen Davies](http://stephendavies.org/) guided my study of the fundamentals of reinforcement learning. We went over value functions, policy functions, how we can describe our environment as a markov decision processes, and other concepts.

[Notes and Other Goodies](reinforcementlearning/) / [Github Code](https://github.com/brandon-rozek/ReinforcementLearning)




## Other Research and Academic Activities

[**Excitation of Rb87**](rb87/): Worked in a Quantum Research lab alongside fellow student Hannah Killian under the guidance of Dr. Hai Nguyen. I provided software tools and assisted in understanding the mathematics behind the phenomena.

[Modeling Population Dynamics of Incoherent and Coherent Excitation](/files/research/modellingpopulationdynamics.pdf)

[Coherent Control of Atomic Population Using the Genetic Algorithm](/files/research/coherentcontrolofatomicpopulation.pdf)


[**Beowulf Cluster:**](lunac) In order to circumvent the frustrations I had with simulation code taking a while, I applied and received funding to build out a Beowulf cluster for the Physics department. Dr. Maia Magrakvilidze was the advisor for this project. [LUNA-C Poster](/files/research/LUNACposter.pdf)

**Cluster Analysis:** The study of grouping similar observations without any prior knowledge. I studied this topic by deep diving Wikipedia articles under the guidance of Dr. Melody Denhere during Spring 2018. **[Extensive notes](clusteranalysis/)**

[**Programming Languages:**](proglang/) Back in the Fall of 2018, under the guidance of Ian Finlayson, I worked towards creating a programming language similar to SLOTH (Simple Language of Tiny Heft). [SLOTH Code](https://github.com/brandon-rozek/SLOTH)

Before this study, I worked through a great book called ["Build your own Lisp"](https://www.buildyourownlisp.com/).

[**Competitive Programming:**](progcomp/) Studying algorithms and data structures necessary for competitive programming. Attended ACM ICPC in November 2018/2019 with a team of two other students.




