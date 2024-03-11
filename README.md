# coq-cheri-capabilities

This repository contains an abstract Coq implementation of CHERI capabilities, and a concrete implementation for Arm Morello.

# Building and Installing

1. We recommend using opam (OCaml's package manager) to build the source code. If you don't yet have it installed, you can use your system's package manager (e.g. `sudo apt-get install opam` on Ubuntu 20.04) to install it, or follow the [instructions from the opam website](https://opam.ocaml.org/doc/Install.html). On older versions of Ubuntu, such as 18.04, you will not be able to use opam from the package manager and will need to install it following the instructions on opam's website.

2. With opam installed, if you don't yet have an opam switch then you can create one using (here we're using OCaml 4.14.1)
```
opam switch create coq-cheri-capabilities 4.14.1
```
Make sure to run `eval $(opam env --switch=coq-cheri-capabilities)` (or whichever exact command opam suggests) at the end to update your current shell environment.

3. With an opam switch created, you must add the Coq and the Iris repositories, and pin the coq-sail-stdpp package, as follows: 
```
opam repo add --this-switch coq-released https://coq.inria.fr/opam/released
opam repo add --this-switch iris-dev https://gitlab.mpi-sws.org/iris/opam.git
opam pin -n coq-sail-stdpp https://github.com/rems-project/coq-sail.git
```

4. You may now install the opam package `coq-cheri-capabilities` and its dependencies with
```
opam install ./coq-cheri-capabilities.opam
```

5. And you may build using
```
dune build
```
