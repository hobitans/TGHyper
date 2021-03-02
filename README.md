# TGHyper
### Tree Generator for checking satisfiability of HyperCTL* formula in ENF.
****

*Branching-time and hyperproperties* can express different specifications for verifying the correctness of systems.
*Branching-time properties* consider the branching structure of execution trees and can refer to the exact points of non-deterministic decisions in a system.
*Hyperpoperties* compare multiple execution traces of a system and are able to express the information flow properties.

The hyperlogic *HyperCTL\** an extension of LTL with quantification over path variables at arbitrary positions
is able to express the combination of *branching-time and hyperpropeties*.
HyperCTL enables us to express security policies that follow precisely the flow of information in non-deterministic systems.

TGHyper is the first decision procedure for HyperCTL* formulas in exists-forall normal form(ENF-HyperCTL*).
For satisfiable formulas, TGHyper can return satisfying trees.

## Applications
TGHyper can detect if an ENF-HyperCTL* formula is a tautology or unsatisfiable. 
This is useful in a preprocessing step of model checking ([MCHyper](https://www.react.uni-saarland.de/tools/mchyper/)) 
and synthesis procedures.  
Furthermore, TGHyper can prove or disprove certain implications between different combinations of hyper- and branching-time properties formalized in ENF-HyperCTL*.
By returning trees that disprove implications, it supports the understanding of the relationship between different specifications even more.
***
TGHyper is part of the Master Thesis ''Algorithms for Deciding HyperCTL*'' submitted by Tobias Hans 2021.
Reactive System Group - Faculty of Mathematics and Computer Science -  Department of Computer Science -  Saarland University

*TGHyper* is based on [MGHyper](https://www.react.uni-saarland.de/publications/mghyper.pdf) a semi-decision procedure for arbitrary HyperLTL formulas. 
*MGHyper* is an extension of [EAHyper](https://www.react.uni-saarland.de/tools/eahyper/) a satisfiability solver for formulas in the decidable fragments of HyperLTL.
TGHyper adapts the input format, mode handling functionality and reuses most flags of *MGHyper/EAHyper*. This enables users and scripts, already familiar with those tools,
easily to adapt to TGHyper.
TGHyper adapted/reuse formula types, parser, and lexer of *MGHyper/EAHyper* for handling quantified path variables at arbitrary positions.
Also, functionality for handling quantified boolean formulas and invoking the respective QBFSAT Solver is adapted to handling boolean formulas and invoking [limboole](http://fmv.jku.at/limboole/).
limboole uses [Lingeling](http://fmv.jku.at/lingeling/) as an underlying Sat-Solver.
The list of adapted files is displayed below.


### Dependencies  
* [OCAMl Version 4.06.1](https://opam.ocaml.org/packages/ocaml/ocaml.4.06.1/)
* [Menhir](http://gallium.inria.fr/~fpottier/menhir/)
* [Ocamlgraph](https://opam.ocaml.org/packages/ocamlgraph/ocamlgraph.1.8.8/)
* [dot - graphviz version 2.44.1](https://graphviz.org)
* [limboole](http://fmv.jku.at/limboole/)

### Build
run ``make`` command

### Example
This HyperCTL*  formula is satisfiable by a comb-like structured tree, where on the path ``p`` in every step ``a`` holds and on the branching paths ``~a``.
> exists p. G ( exists r.( a_p & (X (forall q. G(~a_q)))))

We can check the satisfiability using TGHyper.
> ./main.native -fs "exists p. G ( exists r.( a_r & (X (forall q. G(~a_q)))))"

TGHyper can also construct the satisfying tree by invoking the ``--graph`` flag.
> ./main.native -fs "exists p. G ( exists r.( a_r & (X (forall q. G(~a_q)))))" --graph


### Files
* ``enfFormula.ml``     check and translate ENF-HyperCTL\* formulas to E\*HyperCTL\*
* ``unrolling.ml``      unroll E\*HyperCTLs formulas into propositional formulas, based on the unrolling rules for [bounded LTL model checking](http://fmv.jku.at/papers/BiereCimattiClarkeStrichmanZhu-Advances-58-2003-preprint.pdf).
* ``tvStep.ml``         handles the trace variables step setting functionality.
* ``graphFactory.ml``   builds satisfying trees based on the PVMAP and satisfying assignment.
                    It uses [Ocamlgraph](https://opam.ocaml.org/packages/ocamlgraph/ocamlgraph.1.8.8/) for creating dot files representing satisfying trees
                    and [dot - graphviz version 2.44.1](https://graphviz.org) for creating png image based on the dot files.
* ``README.md``         this file
* ``./files``    contain the following files.
    - ``unr_form.in`` file, string representation of propostional formula used for [limboole](http://fmv.jku.at/limboole/) call
    - ``out.dot`` an example dot file, representing a witness tree
    - ``out.png`` an example png file, representing a witness tree as a picture
* ``./solvers``      directory of SAT solvers, contain only [limboole](http://fmv.jku.at/limboole/) SAT*Solver
                    ``limbooleOSX`` can be replaced by any other SAT-Solver for propositional formulas, not in CNF.
                    Limboole can return CNF formulas (``-d`` flag). By adapting ``invokeSatSolver.ml``, it is possible to use *TGHyper* with other SAT solvers.
* ``randHyperCTL.ml`` assigns path variables randomly to atomic propositions, where the atomic propositions are in the scope of the respective path variable. 
* ``secLTLTest.ml``     models the hide-operator of secLTL as HyperCTL* formulas, can be adapted to construct the formulas in the secLTL benchmark.
* ``./benchmarks/`` contains the HyperCTLs formulas we used to evaluate our tool.

#### Files adapted from MGHyper/EAHyper
The following files contain functionality adapted from MGHyper/EAHyper.                    
* ``main.ml`` is adapted from MGHyper/EAHyper. We adapted the mode handling procedures and reused most of the flags from MGHyper/EAHyper, 
            so that users/scripts familiar with those tools can easily adapt.
            We add inter alia the following functionality/flags:
    - ``-r`` randomly assign path variables ``pv`` to atomic propositions ``ap``, where the pv scopes over ``ap``.
    - ``--graph`` If the formula is satisfiable, a graph representation of the assignment is shown.
    - ``--notfast`` Replace G F operators by U R and do not use the smaller reduction (default false).
    - ``--secLTL`` Print a SecLTL formula from our test set to adapt the formula adapt file ``secLTLTest.ml``.
* ``tg_hyperCTL.ml``    adapted from MGHyper. Contains the function to step-wise unrolling of the formulas for incrementally larger bounds until a satisfiable assignment is found.
                            The actual unrolling is done in ``unrolling.ml`` and ``tvStep.ml``.
* ``formulaHyperCTL.ml``    adapted from MGHyper/EAHyper HyperLTL types and function, for handling path variable quantification at arbitrary positions.
* ``invokeSatSolver.ml``    adapted on MGHyper/EAHyper for handling arbitrary propositional formulas and
                            invoke [limboole](http://fmv.jku.at/limboole/) with the ``-s`` flag for checking the satisfiability of propositional formulas.
* ``lexer.mml``  reused from EAHyper/MGHyper.
* ``Makefile``  based on from MGHyper/EAHyper and added ocamlgraph package to build options
* ``parser.mly`` adapted from MGHyper/EAHyper for handling path variable quantification add arbitrary positions
* ``function.ml``     contains functions used in several modules; some of these functions are based on EAHyper/MGHyper
* ``formulaBool.ml`` adapted from Quantified Boolean Formulas methods in MGHyper




[MGHyper](https://www.react.uni-saarland.de/publications/mghyper.pdf) Copyright ©  2018 
Christopher Hahn <hahn@react.uni-saarland.de>, Tobias Hans <s9tshans@stud.uni-saarland.de> ([Reactive Systems Group](https://www.react.uni-saarland.de/) @ [Saarland University](http://www.uni-saarland.de/nc/en/home.html))
  
[EAHyper](https://www.react.uni-saarland.de/tools/eahyper/) Copyright © 2017, 2018 
Christopher Hahn <hahn@react.uni-saarland.de>, Marvin Stenger <stenger@react.uni-saarland.de> ([Reactive Systems Group](https://www.react.uni-saarland.de/) @ [Saarland University](http://www.uni-saarland.de/nc/en/home.html))
Permission to use, copy, modify, and/or distribute this software for any
purpose with or without fee is hereby granted, provided that the above
copyright notice and this permission notice appear in all copies.

THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.



[Lingeling](http://fmv.jku.at/lingeling/)
Copyright (c) 2010-2020 Armin Biere, Johannes Kepler University Linz, Austria

MIT License
Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

                                                                              
