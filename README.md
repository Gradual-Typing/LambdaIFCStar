# About

$\lambda_{\mathtt{SEC}}^\star$ is an experimental gradual security-typed programming language.
It provides programmers with the freedom of choice between runtime versus compile-time
information-flow (IFC) enforcement.
The Agda development of $\lambda_{\mathtt{SEC}}^\star$ comes with machine-checked proofs of
various meta-theoretical results.

# Building and Testing

We compile $\lambda_{\mathtt{SEC}}^\star$ into an intermediate representation ("cast calculus"),
namely, $\lambda_{\mathtt{SEC}}^\Rightarrow$. We define an operational semantics for
$\lambda_{\mathtt{SEC}}^\star$ that includes blame tracking.

You can check proofs and explore examples by following the steps:

## Prerequisites

### Software dependencies for checking proofs:

- [Agda](https://wiki.portal.chalmers.se/agda) `2.6.3`
- [Standard library](https://github.com/agda/agda-stdlib) `v1.7.2 (b2e6385)`
- [Abstract binding trees](https://github.com/jsiek/abstract-binding-trees/)
- [GNU Make](https://www.gnu.org/software/make/)

### Additional dependencies for running demo:

- GHC with working [MAlonzo](https://wiki.portal.chalmers.se/agda/Docs/MAlonzo)

### [Optional] Additional dependencies for drawing simulation diagrams:

- XeLaTeX and `latexmk`
- [GraphViz](https://graphviz.org/) and specifically, `dot`
- [Dot2TeX](https://dot2tex.readthedocs.io/en/latest/)
- [Zsh](https://www.zsh.org/), for running plotting scripts

## Building

+ To build everything, simply run `make` at the top level of this repository.
    - This will build the proofs, the runnable demo, and a simulation explorer.

+ **[Optional]** To check the proofs only, run `make proofs`.
  The type-checker of Agda makes sure everything is correct.

+ **[Optional]** To build the simulator only, run `make sim`.

## Running Demo

To get a taste of $\lambda_{\mathtt{SEC}}^\star$ running in action,
build everything first and then run `bin/RunDemo`.

# Project Code Structure (selected)

All Agda source files are located in the [`src/`](./src) directory
and end with `.agda`.

There are three top-level modules: one contains all type-check-able proofs;
the other two compiles to executable binaries:

+ [`Proofs`](./src/Proofs.agda): sources the proofs of important meta-theoretical results
  in the following modules:
  - [`CC.TypeSafety`](./src/CC/TypeSafety.agda):
    $\lambda_{\mathtt{SEC}}^\Rightarrow$ is type safe by
    satisfying progress and preservation.
  - [`CC.BigStepPreservation`](./src/CC/BigStepPreservation.agda):
    Big-step evaluation to value is type safe.
  - [`CC.BigStepErasedDeterministic`](./src/CC/BigStepErasedDeterministic.agda):
    Big-step evaluation of erased
    $\lambda_{\mathtt{SEC}}^\Rightarrow$ is deterministic.
  - [`CC.Noninterference`](./src/CC/Noninterference.agda):
    The main security guarantee.
  - [`CC.Compile`](./src/CC/Compile.agda):
    Compilation from $\lambda_{\mathtt{SEC}}^\star$
    to $\lambda_{\mathtt{SEC}}^\Rightarrow$ preserves types.

+ [`RunDemo`](./src/RunDemo.agda): runs the stepper on $\lambda_{\mathtt{SEC}}^\star$
  programs in the following modules and pretty-prints their reduction
  sequences to console:
  - [`ExamplePrograms.Demo.Example1`](./src/ExamplePrograms/Demo/Example1.agda):
    shows that $\lambda_{\mathtt{SEC}}^\star$ indeed facilitates both compile-time
    (static) and runtime (dynamic) information-flow control.
    If a $\lambda_{\mathtt{SEC}}^\star$ program is fully statically-typed,
    our type system alone guarantees security. Transition between
    static and dynamic is controlled by the precision of type annotations
    given by the programmer.
  - [`ExamplePrograms.Demo.Example2`](./src/ExamplePrograms/Demo/Example2.agda):
    establishes the intuition that even if the programmer opts for runtime enforcement,
    $\lambda_{\mathtt{SEC}}^\star$ still guards against any possible
    information leakage.
  - [`ExamplePrograms.Demo.Example3`](./src/ExamplePrograms/Demo/Example3.agda):
    shows that moving type annotations to be less precise (or more dynamic) does not
    change the runtime behavior of a program.

+ [`RunSimulation`](./src/RunSimulation.agda): simulates between
  $\lambda_{\mathtt{SEC}}^\Rightarrow$ terms of different precision.
