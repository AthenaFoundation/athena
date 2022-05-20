[![ci_regression_tests](https://github.com/AthenaFoundation/athena/actions/workflows/main.yaml/badge.svg)](https://github.com/AthenaFoundation/athena/actions/workflows/main.yaml)
# Athena Proof Framework

This repo contains the source code for Athena, a system for proof engineering based on polymorphic multi-sorted first-order logic.

Athena supports natural deduction, proof organization and abstraction, theory development, equational reasoning and (conditional) rewriting, structural induction, and more. It is also seamlessly integrated with a number of automated theorem provers, as well as SAT and SMT solvers. 

## A Quick Example

Athena is very close in style to the way humans naturally perform deduction.

Below is a simple example of proving the *asymmetry* of the `<` (less-than) relation, taken verbatim from the [Athena book](#learn-athena):


```
module Asymmetry {
  domain D
  declare <: [D D] -> Boolean

  define [x y z] := [?x:D ?y:D ?z:D]

  assert* irreflexivity := (~ x < x)
  assert* transitivity := (x < y & y < z ==> x < z)

  conclude asymmetry := (forall x y . x < y ==> ~ y < x)
    pick-any a:D b:D
      assume (a < b)
        (!by-contradiction (~ b < a)
          assume (b < a) 
            let {less := (!chain-> [(b < a) 
                                ==> (a < b & b < a)    [augment]
                                ==> (a < a)            [transitivity]]);
                 not-less := (!chain-> [true 
                                    ==> (~ a < a)      [irreflexivity]])}
              (!absurd less not-less))

} 
```
## Codebase Structure
Athena is implemented in SML. At its present state, that implementation comprises 80 files, listed in sources.cm.

There are some resources in the repo that specify the dependencies between the various source files:

* `file_dependencies.yaml` lists all the files that each source file depends on.

* `structure_dependencies.yaml` lists all the (SML) structures defined in the code base, and for each structure S, <br> it lists all structures on which S depends.
	
* `dependency_graph.pdf` is a graph (that can be viewed with any pdf reader, e.g., using a browser), which depicts these dependencies graphically.

Note that `athena.sml` is at the top of the graph (it's essentially the 'main' file of the project), while
`base.sml` is at the bottom.


# Building Athena

For build instructions, please refer to the [Building Athena](https://github.com/AthenaFoundation/athena/wiki/Building-Athena) page in the wiki.


# Regression testing

Run `python3 tests/regression/regressionTest.py`. The function `runAthenaTests` will return 0 if all the tests pass and some positive integer <br>
less than 125 otherwise. Thus, this function can be used with `git bisect`, which is useful in debugging a range of commits. By default, <br>
the script runs with a heap image produced by smlnj as described above, but you can also pass it (as the first argument) the name of an <br>
executable produced by MLton (these executables tend to be faster than the heap images produced by smlnj), <br>e.g., `python3 tests/regression/regressionTest.py './athena'`.


# Learn Athena

The most thorough resource for learning to use Athena is the book, [Fundamental Proof Methods in Computer Science](https://mitpress.mit.edu/books/fundamental-proof-methods-computer-science) or FPMICS, authored by Konstantine Arkoudas and David Musser.

Examples of Athena can also be found in the `tests/regression/` directory, including all of the code examples provided with the book.

Other tutorials and online courses are undergoing active development.
# History of Athena

Athena was developed by Konstantine Arkoudas, roughly between 2000 and 2015. The core of the language had more or less settled by 2004, but there were a number of subsequent changes and extensions, some of them conceived and implemented after 2010, such as modules, a good deal of infix syntax, proof chaining (implemented via the primitive 'chain' procedure, both for equations and for logical implications/equivalences), integration with SMT solvers and tabled Prolog systems such as XSB, and others. 

In early 2022, Tannr Allard - already familiar with Athena from a few years of personal use - began applying Athena to research efforts in collaboration with the Ethereum Foundation, MakerDAO, and other projects.
 
In an effort to improve the verification tooling available for developers, Tannr formed the Athena Foundation, a non-profit organization dedicated to the maintenance and continued development of the Athena language, auxiliary tooling, and educational materials. The Athena Foundation also aims to facilitate R&D efforts related to formal verification across various organizations and industries.
 
Tannr is now the core maintainer of the Athena language and regularly collaborates with Konstantine, who serves as an expert advisor and board member of the Athena Foundation.