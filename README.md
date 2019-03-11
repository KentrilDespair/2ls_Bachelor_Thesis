[![Build Status][build_img]][travis]

CHANGED FILES
=============
* ssa\_analyzer.h
* ssa\_analyzer.cpp
* domain.h
* heap\_domain.h
* heap\_domain.cpp
* tpolyhedra\_domain.h
* tpolyhedra\_domain.cpp

CODE EXAMPLES
=============
## 1. Heap domain
```cpp
typedef struct elem {
 struct elem *next;
 int val;
} elem_t;

int main()
{
 int i[] = {1,2,3,4};
 elem_t *head;

 elem_t e1, e2, e3, e4;
 head = &e1;
 e1.val = i[0];
 e1.next = &e2;

 e2.val = i[1];
 e2.next = &e3;

 e3.val = i[2];
 e3.next = &e4;

 e4.val = i[3];

 elem_t *p = head;

 while (p)
 {
  printf("val %d\n", p->val);
  p = p->next;

  if (p)
   p = p->next;  // line 34
 }
 
 return 0;
}
```
## $ ./2ls main.c --heap --inline
```
...
INVARIANT IMPRECISION
---------------------
Variables:
Variables:
0: p#lb37 VAL: TRUE EXPR.ID: symbol
---------------------
MATCH: p#34
MATCH: p#36

-> Variable "p" in file main2.c line 34 function main
...
```
## 2. Template Polyhedra domain
```cpp
void main()
{
  int x = 0;
  unsigned y = 0;

  while (x || y < 10) 
  {
    --x;
    --y;
    ++x;
    --x;
    --y;         // line 12
    x = -y - x;  // line 13
  }

  assert(x == 10);
}
```
## $ ./2ls main.c --intervals --inline

```
...
INVARIANT IMPRECISION
---------------------
Variables:
0: x#lb26	Type: signedbv
	VAL: 01111111111111111111111111111111
MAX
1: -((signed __CPROVER_bitvector[33])x#lb26)	Type: signedbv
	VAL: 010000000000000000000000000000000
2: y#lb26	Type: unsignedbv
	VAL: 11111111111111111111111111111111
MAX
3: -((signed __CPROVER_bitvector[33])y#lb26)	Type: signedbv
	VAL: 000000000000000000000000000000000

---------------------
MATCH: x#20
MATCH: x#22
MATCH: x#23
MATCH: x#25

-> Variable "x" in file main.c line 13 function main

MATCH: y#21
MATCH: y#24

-> Variable "y" in file main.c line 12 function main
...
```

About
=====

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


