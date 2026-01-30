---
Title: Research
Description: A list of my research Projects
---

**[Quick List of Publications](/publications/)**

**Broad Research Interests:** Automated Reasoning, Automated Planning, Artificial Intelligence, Formal Methods

I'm a Computer Science PhD Candidate at Rensselaer Polytechnic Institute. I enjoy using logic-based techniques and designing algorithms to solve problems.

Jump to:
- [Automated Planning under uncertainty](#automated-planning-under-uncertainty)
- [Computational and Formal Logic](#computational-and-formal-logic)
- [Verifying Cryptographic Properties](#verifying-cryptographic-properties)

## Automated Planning under Uncertainty

My dissertation topic is on designing algorithms to automatically find
and recognize plans when agents are uncertain about their environment
but can compare the uncertainty between events *qualitatively*.

For example, it is totally
expected when we stack a block that it stays on the top. However, there is a
smaller likelihood that the block falls off.
How can we best make use of this information?
- When recognizing the goals of agents, one assumption we can make is that the agent is
following a plan that maximizes the likelihood of reaching their goals.
I designed an algorithm for recognizing these plans under qualitative possibility theory. This work is supervised under [Selmer Bringsjord](https://kryten.mm.rpi.edu/selmerbringsjord.html) (Paper to be released soon)
- Additionally with Selmer Bringsjord in the [RAIR Lab](https://rair.cogsci.rpi.edu/), I created a framework for when agents are able to bucket the likelihood of facts within their environment. I then provide an effective
technique for using classical planners to find a plan which maximizes the agent's likelihood of success. ([Paper](/paper/2406.02))
- In the RAIR Lab, I also further developed [Spectra](https://github.com/rairlab/spectra) --
an automated planner built on automated theorem proving. I showed how a class of problems
under uncertainty can be easily encoded, and I implemented a question-answer algorithm
for ShadowProver so that Spectra can find plans under epistemic uncertainty. ([Paper](/paper/2405.01/))
- With [Junkyu Lee](https://researcher.ibm.com/researcher/view.php?person=ibm-Junkyu.Lee),
[Michael Katz](https://researcher.watson.ibm.com/researcher/view.php?person=ibm-Michael.Katz1),
[Harsha Kokel](https://harshakokel.com/), and [Shirin Sohrabi](https://researcher.watson.ibm.com/researcher/view.php?person=us-ssohrab) at IBM I developed an algorithm
for guiding hierarchical reinforcement agents under partial observability. Specifically,
I focused on scenarios where the agent knows what they don't know, and I compiled that knowledge
to use a fully-observable non-deterministic planner to decompose the overall problem. ([Paper](/paper/2406.01))

## Computational and Formal Logic

I have a deep fascination of using logic as a tool to model problems. In that regard, I have been fortunate to work with some excellent collaborators on designing logic formalisms, studying properties of logic systems,
and implementing solvers and verifiers.
- With [Andrew Tedder](https://sites.google.com/view/andrewjtedder/research), we built a tool
which can efficiently determine in polynomial time (for a class of logics) whether a matrix model satisfies
the variable sharing property. This property is frequently studied in the relevance logic literature and is often a starting point for other stronger properties. (Paper to be released soon)
- With [Andrew Wells](https://andrewmw94.github.io/) at Amazon Web Services, I built a tool which takes in a supported
fragment of TypeScript, and uses the Dafny verification language to determine whether two functions are equivalent. I wrote the compiler using the Lean 4 programming language, and included several dataflow analysis passes to capture whether the function may have exited at a certain program point, raised an exception, etc.
- With [Andrew Marshall](https://www.marshallandrew.net/) and [Kimberly Cornell](https://www.albany.edu/cehc/faculty/kimberly-cornell), we dedicated effort to designing a new AC unification algorithm that works directly on formulae instead
of compiling to a diophantine solver. This project is currently on hold.
- With [Thomas Ferguson](https://faculty.rpi.edu/thomas-ferguson) and [James Oswald](https://jamesoswald.dev), we formalized a model theory for a fragment of the Deontic Cognitive Event Calculus. ([Paper](/paper/2405.02))
- With James Oswald, we've built an interactive theorem prover ([Project](https://github.com/RAIRLab/lazyslate)) and showed validity of large proofs in parallel using a high performance cluster. ([Paper](/paper/2311.01/))


Related Notes:

- [Automated Theorem Proving](atp/)
- [Term Reasoning](termreasoning/)


## Verifying Cryptographic Properties
Worked with [Andrew Marshall](https://www.marshallandrew.net/) and others in designing and implementing
unification algorithms for verifying cryptographic properties. Our team looked at block ciphers, multi-party computation,
authentication, and commitment schemes. During my time working with this team, I focused on verifying whether
block ciphers are protected against the indistinguishability under chosen plaintext attack.

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




