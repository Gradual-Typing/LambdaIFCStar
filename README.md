# What?

$\lambda_{\mathtt{SEC}}^\star$ is an experimental gradual security-typed programming language.
It provides programmers with the freedom of choice between runtime versus compile-time
information-flow enforcement.

# Why?

The Agda development of $\lambda_{\mathtt{SEC}}^\star$ in this repository comes with
machine-checked proofs of various meta-theoretical results, thus establishing a rock
solid foundation for gradual security. Furthermore, formalizing $\lambda_{\mathtt{SEC}}^\star$
in Agda helps us experiment with different language design choices.

# How?

We compile $\lambda_{\mathtt{SEC}}^\star$ into an intermediate representation ("cast calculus"),
namely, $\lambda_{\mathtt{SEC}}^\Rightarrow$. We have defined operational semantics for
$\lambda_{\mathtt{SEC}}^\star$, which includes blame tracking.

You can check our proofs and run our examples using Agda:

## Prerequisites

- [Agda](https://wiki.portal.chalmers.se/agda) `2.6.2.2`
- GHC with working [MAlonzo](https://wiki.portal.chalmers.se/agda/Docs/MAlonzo)
- [Standard library](https://github.com/agda/agda-stdlib) `1.7.1`
- [Abstract binding trees](https://github.com/jsiek/abstract-binding-trees/)

## Building

+ To build everything, simply run `make` at the top level of this repository.
    - This will build both the proofs and the runnable demo.

+ To check the proofs only, run `make proofs`. The type-checker of Agda makes sure
  everything is correct.

+ To see $\lambda_{\mathtt{SEC}}^\star$ running in action, build everything first
  and then run `bin/Demo`.

# File Structure

+ `src/Examples.agda`: contains examples programs. It sources the
  following modules:
  - `src/ExamplePrograms/Example1.agda`: shows that
    $\lambda_{\mathtt{SEC}}^\star$ indeed facilitates both compile-time
    (static) and runtime (dynamic) information-flow control.
    If a $\lambda_{\mathtt{SEC}}^\star$ program is fully statically-typed,
    our type system alone guarantees security. Transition between
    static and dynamic is controlled by the precision of type annotations
    given by the programmer.
  - `src/ExamplePrograms/Example2.agda`: establishes the
    intuition that even if the programmer opts for runtime enforcement,
    $\lambda_{\mathtt{SEC}}^\star$ still guards against any possible
    information leakage.
