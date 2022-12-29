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
- [GNU Make](https://www.gnu.org/software/make/)

## Building

+ To build everything, simply run `make` at the top level of this repository.
    - This will build both the proofs and the runnable demo.

+ To check the proofs only, run `make proofs`. The type-checker of Agda makes sure
  everything is correct.

+ To get a taste of $\lambda_{\mathtt{SEC}}^\star$ running in action, build everything
  first and then run `bin/Demo`.

# File Structure

In further detail:

+ `src/Proofs.agda`: sources the proofs of several important
  meta-theoretical results, most noticeably, type safety and noninterference.
  This file depends upon modules in the following sub-directories:
  - `src/Surface/`: contains syntax and type system of
    $\lambda_{\mathtt{SEC}}^\star$. This is the "surface language",
    i.e., the language exposed to the programmers.
  - `src/Memory/`: contains our heap model. The heap has a public, low-security
    region and a secretive, high-security region.
  - `src/CC/`: the formal specification of $\lambda_{\mathtt{SEC}}^\Rightarrow$:
    its syntax, its type system, and its operational semantics (both small-step
    and big-step).
      * `src/CC/Compile.agda`: defines type-preserving compilation
        from $\lambda_{\mathtt{SEC}}^\star$ to $\lambda_{\mathtt{SEC}}^\Rightarrow$.

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
  - `src/ExamplePrograms/Example3.agda`: shows that moving
    type annotations to be less precise (or more dynamic) does not change
    the runtime behaviors of a program.

+ `src/Demo.agda`: interprets the $\lambda_{\mathtt{SEC}}^\Rightarrow$
  terms generated by the above example programs. It pretty-prints
  reduction steps to console output.
