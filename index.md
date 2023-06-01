Formulog extends the logic programming language Datalog with mechanisms for constructing and reasoning about SMT formulas, plus some first-order functional programming.
In doing so, it makes it possible to write a range of SMT-based static analyses in a way that is both close to their formal specifications and amenable to high-level optimizations and efficient evaluation.

### Publications

**Formulog: Datalog for SMT-Based Static Analysis** ([link](https://aaronbembenek.github.io/papers/formulog-oopsla2020.pdf))  
Aaron Bembenek, Michael Greenberg, and Stephen Chong  
OOPSLA 2020
- This is the seminal Formulog paper, presenting the language design and providing three extended case studies of using Formulog: refinement type checking, bottom-up pointer analysis, and bounded symbolic execution.

**Formulog: Datalog + SMT + FP** ([link](https://aaronbembenek.github.io/papers/formulog-datalog2022.pdf))
Aaron Bembenek, Michael Greenberg, and Stephen Chong
Datalog 2.0 2022
- This short paper presents Formulog to an audience already well versed in Datalog. 

**Datalog-Based Systems Can Use Incremental SMT Solving** ([link](https://aaronbembenek.github.io/papers/datalog-incr-smt-iclp2020.pdf))  
Aaron Bembenek, Michael Ballantyne, Michael Greenberg, and Nada Amin  
ICLP 2020
- This extended abstract evaluates some encoding tricks Formulog uses to take advantage of incremental SMT solving.