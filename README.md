[![Build Status][build_img]][travis]

# Imprecise Variable Identification for Abstract Domains in 2LS framework

Identification and in source localization of template variables, which 
have imprecise values inside computed invariant for supported abstract
domains in 2LS framework.


## Edited Files
* ssa\_analyzer.h
* ssa\_analyzer.cpp
* domain.h
* heap\_domain.h
* heap\_domain.cpp
* tpolyhedra\_domain.h
* tpolyhedra\_domain.cpp

## Code Examples

### 1. Template Polyhedra domain
```cpp
1  void main()
2  {
3    int x = 0;
4    unsigned y = 0;
5
6    while (x || y < 10)
7    {
8      --x;
9      ++y;
10     x = y - x;
11   }
12 }
```

### $ ./2ls main.c --intervals --inline
```
...
Computing summary

Invariant Imprecision Identification
------------------------------------
Variables:
1: x#lb23
2: y#lb23
------------------------------------
1: Imprecise value of variable "x" at the end of the loop, that starts at line 6
2: Imprecise value of variable "y" at the end of the loop, that starts at line 6

Summary for function _start
...
```

### 2. Heap domain
#### - static variables
```cpp
1  typedef struct elem {
2    struct elem *next;
3  } elem_t;
4 
5  void main()
6  {
7    elem_t *head;
8    elem_t e1, e2, e3;
9    
10   head = &e1;
11   e1.next = &e2;
12   e2.next = &e3;
13   
14   elem_t *p = head;
15   while (p)
16   { 
17     p = p->next;
18   } 
19 }
```

### $ ./2ls main.c --heap --inline
```
...
Computing summary
 
Invariant Imprecision Identification
------------------------------------
Variables:
1: p#lb26
------------------------------------
1: Imprecise value of variable "p" at the end of the loop, that starts at li    ne 15

Summary for function _start
...
```

#### - dynamic variables
```cpp
1  typedef struct elem {
2    struct elem *next;
3  } *elem_t;
4 
5  void main()
6  {
7    elem_t head, elem;
8 
9    for (unsigned i = 0; i < 2; i++)
10   {
11     elem = (elem_t) malloc(sizeof(struct elem));
12     elem->next = head;
13     head = elem; 
14   } 
15   
16   elem = head;
17   while (elem)
18   {
19     elem = elem->next;
20   } 
21 }
```

### $ ./2ls main.c --heap --inline
```
...
Computing summary

Invariant Imprecision Identification
------------------------------------
Variables:
1: dynamic_object$27#2.next#lb50
2: dynamic_object$27#1.next#lb50
3: dynamic_object$27#0.next#lb50
4: elem#lb55
------------------------------------
1: Imprecise value of "next" field of dynamic object "dynamic_object$27#2.next#lb50" allocated at line 11 
2: Imprecise value of "next" field of dynamic object "dynamic_object$27#1.next#lb50" allocated at line 11 
3: Imprecise value of "next" field of dynamic object "dynamic_object$27#0.next#lb50" allocated at line 11 
4: Imprecise value of variable "elem" at the end of the loop, that starts at line 17 

Summary for function _start
...
```

About 2LS
=========

2LS ("tools") is a verification tool for C programs. It is built upon the
CPROVER framework ([cprover.org](http://www.cprover.org)), which
supports C89, C99, most of C11 and most compiler extensions provided
by gcc and Visual Studio. It allows verifying array bounds (buffer
overflows), pointer safety, exceptions, user-specified assertions, and
termination properties.  The analysis is performed by template-based
predicate synthesis and abstraction refinements techniques.


License
=======
4-clause BSD license, see `LICENSE` file.

[build_img]: https://travis-ci.org/diffblue/2ls.svg?branch=master
[travis]: https://travis-ci.org/diffblue/2ls


Overview
========

 2LS reduces program analysis problems expressed in second order logic
 such as invariant or ranking function inference to synthesis problems
 over templates. Hence, it reduces (an existential fragment of) 2nd
 order Logic Solving to quantifier elimination in first order logic.

The current tool has following capabilities:

* function-modular interprocedural analysis of C code based on summaries
* summary and invariant inference using generic templates
* combined k-induction and invariant inference
* incremental bounded model checking
* function-modular termination analysis
* non-termination analysis

Releases
========

Download using `git clone http://github.com/diffblue/2ls; cd 2ls; git checkout 2ls-x.y`

* [2LS 0.7](http://github.com/diffblue/2ls/releases/tag/2ls-0.7) (08/2018)
* [2LS 0.6](http://github.com/diffblue/2ls/releases/tag/2ls-0.6) (12/2017)
* [2LS 0.5](http://github.com/diffblue/2ls/releases/tag/2ls-0.5) (01/2017)
* [2LS 0.4](http://github.com/diffblue/2ls/releases/tag/2ls-0.4) (08/2016)
* [2LS 0.3](http://svn.cprover.org/svn/deltacheck/releases/2ls-0.3) (08/2015)
* [2LS 0.2](http://svn.cprover.org/svn/deltacheck/releases/2ls-0.2) (06/2015)
* [2LS 0.1](http://svn.cprover.org/svn/deltacheck/releases/2ls-0.1) (11/2014)

Software Verification Competition Contributions

* [SV-COMP 2018](http://github.com/diffblue/2ls/releases/tag/2ls-0.6) (12/2017)
* [SV-COMP 2017](http://github.com/diffblue/2ls/releases/tag/2ls-0.5-sv-comp-2017) (01/2017)
* [SV-COMP 2016](http://svn.cprover.org/svn/deltacheck/releases/2ls-0.3-sv-comp-2016) (11/2015) [Follow these instructions](http://www.cprover.org/2LS/2ls-sv-comp-2016.pdf)

Installation
============

`cd 2ls; ./install.sh`

 Run `src/2ls/2ls`

Command line options
====================

The default abstract domain are intervals. If no options are given a context-insensitive interprocedural analysis is performed. For context-sensitivity, add --context-sensitive.

Other analyses include:

* BMC: --inline --havoc --unwind n
* Incremental BMC: --incremental-bmc
* Incremental k-induction: --havoc --k-induction
* Incremental k-induction and k-invariants (kIkI): --k-induction
* Intraprocedural abstract interpretation with property checks: --inline
* Necessary preconditions: --preconditions
* Sufficient preconditions: --preconditions --sufficient

Currently the following abstract domains are available:

* Intervals (default): --intervals
* Zones: --zones
* Octagons --octagons
* Equalities/disequalities: --equalities
* The abstract domain consisting of the Top element: --havoc

Since release 0.6:

* Heap abstract domain: --heap

Since release 0.7:

* Heap abstract domain with intervals or zones: --heap-[intervals|zones]
* Heap abstract domain with intervals or zones and loop paths: --heap-[intervals|zones] --sympath

Interprocedural Termination Analysis
====================================

Is supported by release 0.1 and >=0.3.

* Universal termination: --termination
* Context-sensitive universal termination: --termination --context-sensitive
* Sufficient preconditions for termination --termination --context-sensitive --preconditions

Since release 0.6:

* Nontermination analysis: --non-termination

Features in development
=======================

* ACDL solver (ATVA'17 [Lifting CDCL to Template-Based Abstract Domains for Program Verification](https://doi.org/10.1007/978-3-319-68167-2_2))
* array domain
* disjunctive domains
* custom template specifications
* modular refinement
* template refinement
* thread-modular analysis

Publications
============

* FMCAD'18 Template-Based Verification of Heap-Manipulating Programs
* TACAS'18 [2LS: Memory Safety and Non-Termination](https://link.springer.com/chapter/10.1007%2F978-3-319-89963-3_24)
* TOPLAS 40(1) 2018 [Bit-Precise Procedure-Modular Termination Analysis](https://dl.acm.org/citation.cfm?doid=3121136)
* ATVA'17 [Compositional Refutation Techniques](https://link.springer.com/chapter/10.1007%2F978-3-319-68167-2_12)
* ATVA'17 [Lifting CDCL to Template-Based Abstract Domains for Program Verification](https://doi.org/10.1007/978-3-319-68167-2_2)
* TACAS'16 [2LS for Program Analysis](http://dl.acm.org/citation.cfm?id=2945506)
* SAS'15 [Safety Verification and Refutation by k-Invariants and k-Induction](http://link.springer.com/chapter/10.1007%2F978-3-662-48288-9_9)
* ASE'15 [Synthesising Interprocedural Bit-Precise Termination Proofs](http://dl.acm.org/citation.cfm?id=2916211) [Experimental log](http://www.cs.ox.ac.uk/people/peter.schrammel/2ls/ase15-experimental_results_log.txt) [Additional material](http://www.cs.ox.ac.uk/people/peter.schrammel/2ls/ase15-additional-material.tgz) [Website](http://www.cprover.org/termination/modular)

Contributors
============

* Björn Wachter
* Cristina David
* Daniel Kroening
* Hongyi Chen
* Madhukar Kumar
* Martin Brain
* Martin Hruska
* Peter Schrammel
* Rajdeep Mukherjee
* Samuel Bücheli
* Saurabh Joshi
* Stefan Marticek
* Viktor Malik

Contact
=======

[Peter Schrammel](http://www.schrammel.it)


