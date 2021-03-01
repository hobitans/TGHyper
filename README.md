# TGHyper
### Tree Generator for checking satisfiability of HyperCTL* formula in ENF.
****




TGHyper is based on [MGHyper](https://www.react.uni-saarland.de/publications/mghyper.pdf) a semi-decision procedure for arbitrary HyperLTL formulas. 
MGHyper is an extension of [EAHyper](https://www.react.uni-saarland.de/tools/eahyper/) a satisfiability solver for formulas in the decidable fragments of HyperLTL.
TGHyper adapt the mode handling functionality and reuses most of the flags of MGHyper/EAHyper
TGHyper adapted/reuse formula types, parser, and lexer of MGHyper/EAHyper for handling quantified path variables at arbitrary positions.
Also functionality for handling quantfied boolean formulas of MGHyper is adapted to boolean formulas 




TGHyper is part of the Master Thesis ''Algorithms for Deciding HyperCTL*'' submitted by Tobias Hans 2021.
Reactive System Group - Faculty of Mathematics and Computer Science -  Department of Computer Science -  Saarland University

[MGHyper](https://www.react.uni-saarland.de/publications/mghyper.pdf) Copyright ©  2018 \\
Christopher Hahn <hahn@react.uni-saarland.de>, Tobias Hans ([Reactive Systems Group](https://www.react.uni-saarland.de/) @ [Saarland University](http://www.uni-saarland.de/nc/en/home.html))
[EAHyper](https://www.react.uni-saarland.de/tools/eahyper/) Copyright © 2017, 2018 \\
Christopher Hahn <hahn@react.uni-saarland.de>, Marvin Stenger <stenger@react.uni-saarland.de> ([Reactive Systems Group](https://www.react.uni-saarland.de/) @ [Saarland University](http://www.uni-saarland.de/nc/en/home.html))

### Dependencies  
* [OCAMl Version 4.06.1](https://opam.ocaml.org/packages/ocaml/ocaml.4.06.1/)
* [Menhir](http://gallium.inria.fr/~fpottier/menhir/)
* [Ocamlgraph](https://opam.ocaml.org/packages/ocamlgraph/ocamlgraph.1.8.8/)
* [dot - graphviz version 2.44.1](https://graphviz.org)
* [limboole](http://fmv.jku.at/limboole/)

### Build
run ``make`` command

### Example
This HyperCTL*  formula is satisfiable by a comb-like structured tree, where on the path ``p`` in every step ``a`` holds and on the branching paths ``~a``
> exists p. G ( exists r.( a_p & (X (forall q. G(~a_q)))))

We can check the satisfiability using TGHyper
> ./main.native -fs "exists p. G ( exists r.( a_r & (X (forall q. G(~a_q)))))"

TGHyper can also construct the satisfiyng tree by invoking the ``--graph`` flag
> ./main.native -fs "exists p. G ( exists r.( a_r & (X (forall q. G(~a_q)))))" --graph


### Files
* ``enfFormula.ml``     check and translate ENF-HyperCTL\* formulas to E\*HyperCTL\*
* ``unrolling.ml``      unroll E\*HyperCTLs formulas into propositional formulas, based on the unrolling rules for bounded LTL model checking by [Biere et al.](http://fmv.jku.at/papers/BiereCimattiClarkeStrichmanZhu-Advances-58-2003-preprint.pdf)
* ``tvStep.ml``         handles the trace variables step setting functions  
* ``graphFactory.ml``   builds satisfying trees based on the PVMAP and satisfiyng assignment
                    uses [Ocamlgraph](https://opam.ocaml.org/packages/ocamlgraph/ocamlgraph.1.8.8/) for creating dot files representing satisfiyng trees
                    and [dot - graphviz version 2.44.1](https://graphviz.org) for create png image based on the dot files
* ``README.md``         this file
* ``./files``    contain the following files
    - ``unr_form.in`` file, string representation of propostional formula used for [limboole](http://fmv.jku.at/limboole/) call
    - ``out.dot`` an example dot file, representing a witness tree
    - ``out.png`` an example png file, representing a witness tree as a picture
* ``./solvers``      directory of SAT solvers, contain only [limboole](http://fmv.jku.at/limboole/) SAT*Solver
                    ``limboolOSX`` can be replaced by any other SAT*Solver for propositional formulas not in CNF.
                    limboolOSX can return CNF formulas (``-d`` flag). By adapting ``invokeSatSolver.ml`` it is possible to use *TGHyper* with other SAT solvers.
* ``randHyperCTL.ml`` assigns path variables randomly to atomic propositions, where the atomic propositions are in the scope of the respective path variable. 
* ``secLTLTest.ml``     models the hide-operator of secLTL as HyperCTL* formulas, can be adapted to construct the formulas in the secLTL benchmark
* ``./benchmarks/`` contains the HyperCTLs formulas we used to evaluate our tool

#### Files adapted from MGHyper/EAHyper
The following files contains function adapted from MGHyper/EAHyper.                    
* ``main.ml`` is adapted from MGHyper/EAHyper. We adapted the mode handling procedures and reuse most of the flags from MGHyper/EAHyper, 
            so that users/scripts familiar with those tools can easily adapt.
            We add inter alia the following functionality/flags:
    - ``-r`` randomly assign path variables ``pv`` to atomic propositions ``ap``, where the pv scopes over ``ap``
    - ``--graph`` If the formula is satisfiable, a graph representation of the assignment is shown.
    - ``--notfast`` Replace G F operators by U R and do not use the smaller reduction (default false)
    - ``--secLTL`` Print a SecLTL formula from our test set, to adapt the formula adapt file ``secLTLTest.ml``
* ``tg_hyperCTL.ml``    adapted from MGHyper. TGHyper and MGhyper are based on the same idea of unrolling the formulas for incremnetially larger bounds until a satisfiable assignment is found.
* ``formulaHyperCTL.ml``    adapted from MGHyper/EAHyper HyperLTL types and function, for handeling path variable quantfication at arbitrary positions
* ``invokeSatSolver.ml``    adapted on MGHyper/EAHyper for handling arbitrary propositional formulas and
                            invoke limboole(http://fmv.jku.at/limboole/) with ``-s`` flag for checking satisfiability of boolean formula
* ``lexer.mml``  reused from EAHyper/MGHyper.
* ``Makefile``  based on from MGHyper/EAHyper and added ocamlgraph package to build options
* ``parser.mly`` adapted from MGHyper/EAHyper for handling path variable quantification add arbitrary positions
* ``function.ml``     contains functions used in several modules; some of these functions are based on EAHyper/MGHyper
* ``formulaBool.ml`` adapted from Quantfied Boolean Formulas methods in MGHyper






                                                                              
