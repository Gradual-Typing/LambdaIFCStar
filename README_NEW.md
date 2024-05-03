

# $\lambda_{\mathtt{IFC}}^\star$, A Gradual Security-Typed Programming Language

$\lambda_{\mathtt{IFC}}^\star$ is an experimental gradual security-typed programming language.
$\lambda_{\mathtt{IFC}}^\star$ is *gradual*, in that it provides the programmer with the freedom
of choice between runtime versus compile-time enforcement. $\lambda_{\mathtt{IFC}}^\star$ is
*secure*, because it enforces information-flow security and satisfies
noninterference.

On the technical side, $\lambda_{\mathtt{IFC}}^\star$ is the only programming language design
that combines gradual typing with information-flow control (IFC) without making any
sacrifices. $\lambda_{\mathtt{IFC}}^\star$ (1) satisfies noninterference (the security
guarantee), (2) satisfies the gradual guarantee, (3) enjoys type-guided
classification, and (4) utilizes NSU checking to enforce implicit flows through
the heap with no static analysis required. The semantics of $\lambda_{\mathtt{IFC}}^\star$ is the
first gradual security-typed language to be specified using *coercion calculi*
(a la Henglein).


# A Tale of Two Gradual Security Languages

This repository contains the [Agda](https://wiki.portal.chalmers.se/agda) mechanization of two gradual security-typed
languages:

1.  $\lambda_{\mathtt{SEC}}^\star$ is a gradual security language that is vigilant (that is, a
    runtime error is triggered if inconsistent type annotations are detected) but
    does not enable type-guided classification (that is, type annotations do not
    affect the security level of runtime values). The development of
    $\lambda_{\mathtt{SEC}}^\star$ is reported in our Arxiv draft
    [Mechanized Noninterference for Gradual Security](https://arxiv.org/abs/2211.15745)
    (**Chen and Siek [2022]**). The semantics of
    $\lambda_{\mathtt{SEC}}^\star$ is given by compiling to the cast calculus $\lambda_{\mathtt{SEC}}^{c}$,
    which utilizes type-based casts as its cast representation.
2.  $\lambda_{\mathtt{IFC}}^\star$ is a gradual security language that enjoys *both* vigilance as
    well as type-guided classification, thus enabling type-based reasoning for
    both explicit and implicit information flows. The development of
    $\lambda_{\mathtt{IFC}}^\star$ is reported in our upcoming [PLDI 2024](https://pldi24.sigplan.org/details/pldi-2024-papers/66/Quest-Complete-The-Holy-Grail-of-Gradual-Security) paper
    [Quest Complete: The Holy Grail of Gradual Security](https://homes.luddy.indiana.edu/chen512/lambdaifcstarv2.pdf)
    (**Chen and Siek [2024]**). The semantics of $\lambda_{\mathtt{IFC}}^\star$ is given by compiling
    to another cast calculus $\lambda_{\mathtt{IFC}}^{c}$, in which we adapt ideas from
    the Coercion Calculus of Henglein [1994] to IFC.

Both cast calculi, $\lambda_{\mathtt{IFC}}^{c}$ and $\lambda_{\mathtt{SEC}}^{c}$, support blame-tracking. Casts are
inserted on-demand, only when there is insufficient information during
compilation to decide whether a security policy is enforced or not.


# Quick Start Guide


## Software prerequisites


### Software dependencies for checking proofs:

-   [Agda](https://wiki.portal.chalmers.se/agda) `2.6.4`
-   [Agda standard library](https://github.com/agda/agda-stdlib) `v1.7.3 (0817da6)`
-   [The Abstract Binding Trees library](https://github.com/jsiek/abstract-binding-trees/)
-   [GNU Make](https://www.gnu.org/software/make/)


### Software dependencies for running demos:

-   [GHC](https://www.haskell.org/ghc/) with [MAlonzo](https://wiki.portal.chalmers.se/agda/Docs/MAlonzo)


### Software dependencies for drawing simulation diagrams:

-   [XeLaTeX](https://tug.org/xetex/) and `latexmk`
-   [GraphViz](https://graphviz.org/) (specifically, `dot`)
-   [Dot2TeX](https://dot2tex.readthedocs.io/en/latest/)
-   [Zsh](https://www.zsh.org/) (for running plotting scripts)


## Building the project

-   To build everything, simply run `make` at the top level of this repository.
    This will build the proofs, the runnable demo, and a simulation explorer.

-   Alternatively, to check the proofs only, run `make proofs`.
    The type-checker of Agda makes sure all the proofs are correct.

-   Alternatively, to build the simulator only, run `make sim`.


## Running the demo programs of $\lambda_{\mathtt{SEC}}^\star$

We include example programs written in $\lambda_{\mathtt{SEC}}^\star$. To get a taste of
$\lambda_{\mathtt{SEC}}^\star$ running in action, please build everything first and then run
`bin/RunDemo`.


# Selected Project Code Structure

All Agda source files are located in the [src](./src) directory and end with `.agda`. A
(fairly) large part of the code-base is shared between $\lambda_{\mathtt{IFC}}^\star$ and
$\lambda_{\mathtt{SEC}}^\star$.

