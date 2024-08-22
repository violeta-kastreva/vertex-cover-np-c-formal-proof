# Formal Proof of Vertex Cover NP-Completeness

This repository contains the formal proof of the NP-completeness of the Vertex Cover problem. 
The proof and its formalization are based on concepts and methodologies developed in conjunction with Lennard Gäher's Bachelor thesis at the [Programming Systems Lab](https://www.ps.uni-saarland.de/) of [Saarland University](https://www.uni-saarland.de/).



## Basis and Contributions

This project is based on the [library of undecidable problems](https://github.com/uds-psl/coq-library-undecidability). The main files contributed as part of this proof are:

```
L/Complexity/Problems/VertexCover.v 
L/Complexity/Reductions/Clique_to_VertexCover.v
```

## Formalization Report

You can find the report [here](https://github.com/violeta-kastreva/vertex-cover-np-c-formal-proof/blob/master/Formalization%20of%20Clique%20to%20Vertex%20Cover%20Reduction%20in%20Coq..pdf).


## How to build

### Required packages

You need `Coq 8.8.1` or `8.8.2` built on OCAML `> 4.02.3` and the [Equations](https://mattam82.github.io/Coq-Equations/) package for Coq. If you're using opam 2 you can use the following commands to install the dependencies on a new switch:

```
opam switch create coq-library-undecidability 4.07.1+flambda
eval $(opam env)
opam repo add coq-released https://coq.inria.fr/opam/released
opam update
opam install . --deps-only
```

### Build external libraries

The Undecidability libraries depends on several external libraries. Initialise and build them once as follows:

``` sh
git submodule init
git submodule update
make deps
```

### Building the undecidability library

- `make all` builds the library
- `make html` generates clickable coqdoc `.html` in the `website` subdirectory
- `make clean` removes all build files in `theories` and `.html` files in the `website` directory
- `make realclean` also removes all build files in the `external` directory. You have to run `make deps` again after this.

Use `make all -j[#cores * 2]` to speed up compilation if you have enough RAM. For compilation with 8 threads or more, about 8-10GB RAM are needed. Minimum RAM needed is ~5GB.
This should take about 1-2 hours, depending on the speed of your system.



## License

The Coq files listed above are licensed under the [CeCILL license](https://github.com/uds-psl/ba-gaeher/blob/master/CeCILL_LICENSE.txt).



### Contributors of the underlying undecidability library 

- Andrej Dudenhefner
- Yannick Forster
- Edith Heiter
- Dominik Kirst
- Fabian Kunze
- Dominique Larchey-Wendling
- Gert Smolka
- Simon Spies
- Dominik Wehr
- Maximilian Wuttke
