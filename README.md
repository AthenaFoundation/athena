# Athena Proof Assistant

This repo contains the source code for Athena, a system for proof engineering based on polymorphic multi-sorted first-order logic.

Athena is implemented in SML. At its present state, that implementation comprises 80 files, listed in sources.cm.

There are some resources in the repo that specify the dependencies between the various source files:

* `file_dependencies.yaml` lists all the files that each source file depends on.

* `structure_dependencies.yaml` lists all the (SML) structures defined in the code base, and for each structure S, <br> it lists all structures on which S depends.
	
* `dependency_graph.pdf` is a graph (that can be viewed with any pdf reader, e.g., using a browser), which depicts these dependencies graphically.

Note that `athena.sml` is at the top of the graph (it's essentially the 'main' file of the project), while
`base.sml` is at the bottom.


# Build Instructions

## Build Pre-requisites
First, ensure that both `ml-yacc` and `ml-ulex` are installed (on unix machines, this can be done with `apt`).

Then, ensure that either `mlton` or `smlnj` are installed as well.


## Using SML/NJ

### Hacking Athena 

Developing Athena is best done with smlnj. Bring up smlnj (after installing it), and then do: 

`- CM.make("sources.cm");`

This will compile the entire project. After compilation is done, type:

`- Athena.run();`

to enter Athena's main REPL (read-eval-print loop). You can then go back and make more code changes, remake the project <br>
(by executing `- CM.make("sources.cm");` again), enter the REPL, and so on. 

### Producing a stand-alone program with smlnj

* Make an Athena heap image by starting smlnj, compiling (with `- CM.make("sources.cm");`), and then doing one of the following, <br> depending on how you prefer to use the stand-alone: <br>
  * `- SMLofNJ.exportFn("athena_image",fn (_,arg1::_) => (Athena.runWithStarterFileAndQuit(SOME(arg1)); OS.Process.success));` <br> if you want the executable to take as input an Athena file, execute that file, and then quit. This will save a file athena_image.x86-linux (the extension is OS-specic).
  * `- SMLofNJ.exportFn("athena_image",fn (_,arg1::_) => (Athena.runWithStarterFile(SOME(arg1)); OS.Process.success));` <br> if you want the executable to take as input an initial Athena file, execute it, and then go into the usual Athena REPL.<br>This will also save a file athena_image.x86-linux locally.

* To start the program with an input file, do the following: `sml @SMLload=athenaImage.x86-linux input_file.ath`

## Using MLton

### Producing a stand-alone binary with MLton

Simply run `./make_mlton_binary`. By default, the output will be a natively compiled executable named `athena`.<br><br>
You can run that executable by itself (without any arguments), or you can pass it as an argument the name of an initial<br>
Athena file to load upon starting. After loading, Athena will enter its REPL. If you want Athena to quit after loading <br>
the initial file, pass 'quit' as the second argument to the executable (e.g., `athena some_file.ath quit`). <br><br>
**Note**: The file `athena.mlb` contains the list of source files used by MLton. If you add/delete source files to/from<br>
Athena, you must update both `sources.cm` and `athena.mlb` as needed.


### Making Athena with C and XSB

To make Athena with C (using MLton's [FFI](mlton.org/ForeignFunctionInterface))  and assuming you have XSB on ~/.xsb, do: <br>

`mlton -default-ann 'allowFFI true' -export-header athena.h -stop tc athena.mlb`

`XSB_arch='ls ~/.xsb/config'`

`gcc -c -I/$XSB_HOME/emu -I/$XSB_HOME/config/$XSB_arch -O3 -fno-strict-aliasing  -Wall -pipe -D_GNU_SOURCE athena_with_xsb.c`

Finally:

```
if [ 'uname -s' == 'Darwin' ]
  then mlton -drop-pass deepFlatten -default-ann 'allowFFI true' -output athena-mac -link-opt -lm -ldl -Wl -lpthread' athena.mlb $XSB_HOME/config/$XSB_arch/saved.o/xsb.o athena_with_xsb.o
   else mlton -drop-pass deepFlatten -default-ann 'allowFFI true' -output athena-linux -link-opt -lm -ldl -Wl -export-dynamic -lpthread' athena.mlb $XSB_HOME/config/$XSB_arch/saved.o/xsb.o athena_with_xsb.o
fi
```

# Regression testing

Run `python3 tests/regression/regressionTest.py`. The function `runAthenaTests` will return 0 if all the tests pass and some positive integer <br>
less than 125 otherwise. Thus, this function can be used with `git bisect`, which is useful in debugging a range of commits. By default, <br>
the script runs with a heap image produced by smlnj as described above, but you can also pass it (as the first argument) the name of an <br>
executable produced by MLton (these executables tend to be faster than the heap images produced by smlnj), <br>e.g., `python3 regressionTest.py './athena'`.


# Learn Athena

The most thorough resource for learning to use Athena is the book, [Fundamental Proof Methods in Computer Science](https://mitpress.mit.edu/books/fundamental-proof-methods-computer-science) or FPMICS, authored by Konstantine Arkoudas and David Musser.

Examples of Athena can also be found in the `tests/regression/` directory, including all of the code examples provided with the book.

Other tutorials and online courses are undergoing active development.
# History of Athena

Athena was developed by Konstantine Arkoudas, roughly between 2000 and 2015. The core of the language had more or less settled.

By 2004, but there were a number of subsequent changes and extensions, some of them conceived and implemented after 2010, such as modules, a good deal of infix syntax, proof chaining (implemented via the primitive 'chain' procedure, both for equations and for logical implications/equivalences), integration with SMT solvers and tabled Prolog systems such as XSB, and others. 

In early 2022, Tannr Allard - already familiar with Athena from a few years of personal use - began applying Athena to research efforts in collaboration with the Ethereum Foundation, MakerDAO, and other projects.
 
In an effort to improve the verification tooling available for developers, Tannr formed the Athena Foundation, a non-profit organization dedicated to the maintenance and continued development of the Athena language, auxiliary tooling, and educational materials. The Athena Foundation also aims to facilitate R&D efforts related to formal verification across various organizations and industries.
 
Tannr is now the core maintainer of the Athena language and regularly collaborates with Konstantine, who serves as an expert advisor and board member of the Athena Foundation.