

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

This repository contains the [Agda](https://wiki.portal.chalmers.se/agda) mechanization of $\lambda_{\mathtt{IFC}}^\star$ as well as its
sibling gradual security-typed language, $\lambda_{\mathtt{SEC}}^\star$:

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

All Agda source files are located in the [`src/`](./src) directory and end with dot Agda.
A (fairly) large part of the code-base is shared between $\lambda_{\mathtt{IFC}}^\star$ and
$\lambda_{\mathtt{SEC}}^\star$.


## Meta-theoretical results and demo programs

There are three top-level modules in the [`src/`](./src) directory:

1.  [**`Proofs`**](./src/Proofs.agda): sources the proofs of important **meta-theoretical results**
    in the following modules:
    -   Here are some meta-theoretical results for $\lambda_{\mathtt{SEC}}^\star$ and its cast
        calculus $\lambda_{\mathtt{SEC}}^{c}$:
        -   [`CC.TypeSafety`](./src/CC/TypeSafety.agda): $\lambda_{\mathtt{SEC}}^{c}$ is type safe by satisfying progress and
            preservation.
        -   [`CC.BigStepPreservation`](./src/CC/BigStepPreservation.agda): The big-step semantics of $\lambda_{\mathtt{SEC}}^{c}$ also
            preserves types. The big-step semantics
        -   [`CC.BigStepErasedDeterministic`](./src/CC/BigStepErasedDeterministic.agda): The big-step evaluation of erased
            $\lambda_{\mathtt{SEC}}^{c}$ is deterministic.
        -   [`CC.Noninterference`](./src/CC/Noninterference.agda): $\lambda_{\mathtt{SEC}}^{c}$ satisfies termination-insensitive
            noninterference (TINI).
        -   [`CC.Compile`](./src/CC/Compile.agda): The compilation from $\lambda_{\mathtt{SEC}}^\star$ to $\lambda_{\mathtt{SEC}}^{c}$
            preserves types.
    -   Here are meta-theoretical results for $\lambda_{\mathtt{IFC}}^\star$ and its cast calculus
        $\lambda_{\mathtt{IFC}}^{c}$:
        -   [`CC2.Progress`](./src/CC2/Progress.agda): $\lambda_{\mathtt{IFC}}^{c}$ satisfies progress, so that a well-typed $\lambda_{\mathtt{IFC}}^{c}$
            term is either a value or a blame, which does not reduce, or the term
            takes one reduction step.
        -   [`CC2.Preservation`](./src/CC2/Preservation.agda): The operational semantics of $\lambda_{\mathtt{IFC}}^{c}$ preserves types
            and the well-typedness of heap.
        -   [`Compile.CompilationPresTypes`](./src/Compile/CompilationPresTypes.agda): The compilation from $\lambda_{\mathtt{IFC}}^\star$ to
            $\lambda_{\mathtt{IFC}}^{c}$ preserves types.
        -   [`Surface2.GradualGuarantee`](./src/Surface2/GradualGuarantee.agda): $\lambda_{\mathtt{IFC}}^\star$ satisfies the gradual
            guarantee.
2.  [**`RunDemo`**](./src/RunDemo.agda): The program runs a stepper on the following $\lambda_{\mathtt{SEC}}^\star$
    programs and pretty-prints their reduction sequences to command line using [the
    Console pretty-printer backend](./src/PrettyPrinter/Console/PP.agda):
    -   The stepper that generates reduction sequences for $\lambda_{\mathtt{SEC}}^{c}$ in string
        format is defined in [`CC.Interp`](./src/CC/Interp.agda).
    -   [`ExamplePrograms.Demo.Example1`](./src/ExamplePrograms/Demo/Example1.agda): This example shows that $\lambda_{\mathtt{SEC}}^\star$
        indeed facilitates both compile-time (static) and runtime (dynamic)
        information-flow control. If a $\lambda_{\mathtt{SEC}}^\star$ program is fully
        statically-typed, the type system of $\lambda_{\mathtt{SEC}}^\star$ alone guarantees
        security. If type information is insufficient, the runtime of
        $\lambda_{\mathtt{SEC}}^\star$ performs security checks during program execution. The
        transition between static and dynamic IFC enforcement is controlled by the
        programmer, depending on the precision of type annotations.
    -   [`ExamplePrograms.Demo.Example2`](./src/ExamplePrograms/Demo/Example2.agda): This example establishes the intuition that
        even if the programmer opts for dynamic IFC enforcement, $\lambda_{\mathtt{SEC}}^\star$
        still guards against any possible information leak through the heap.
    -   [`ExamplePrograms.Demo.Example3`](./src/ExamplePrograms/Demo/Example3.agda): This example shows that moving type
        annotations to be less precise (more dynamic) does not change the runtime
        behavior of a $\lambda_{\mathtt{SEC}}^\star$ program.
3.  [**`RunSimulation`**](./src/RunSimulation.agda): The program runs a simulator that simulates between
    $\lambda_{\mathtt{SEC}}^{c}$ terms of different precision. The output defaults to
    [the GraphViz pretty-printer backend](./src/PrettyPrinter/GraphViz), which
    will place `*.dot` files that represent the simulation diagrams in the [`plot/`](./plot)
    directory.
    -   The simulator is defined in [`Simulator.Simulator`](./src/Simulator/Simulator.agda).
    -   The list of example $\lambda_{\mathtt{SEC}}^{c}$ terms to run can be found in
        [`ExamplePrograms.Simulation.Examples`](./src/ExamplePrograms/Simulation/Examples.agda).
    -   Please refer to the `README` file in [`plot/`](./plot) for the instructions of
        generating the simulation diagrams in PDF format.


## Noteworthy technical definitions


### General technical definitions [in directory `Common/`](./src/Common)

-   [`Common.SecurityLabels`](./src/Common/SecurityLabels.agda): Definitions of *security labels* as well as
    predicates, relations and operators on security labels.
-   [`Common.Types`](./src/Common/Types.agda): Definitions of *(security) types* as well as predicates,
    relations and operators on types.
-   [`Common.BlameLabels`](./src/Common/BlameLabels.agda): This module defines *blame labels*, which are
    identifiers of casts. In case a cast fails, it raises a cast error, called
    blame, that contains its blame label. In this way, the programmer knows which
    cast is causing the problem.
-   [`Common.TypeBasedCast`](./src/Common/TypeBasedCast.agda): This module defines *type-based casts* between two
    security types. In particular, $\lambda_{\mathtt{SEC}}^{c}$ uses type-based cast as its
    cast representation.
-   [`Common.Coercions`](./src/Common/Coercions.agda): This modules defines the coercion-based cast
    representation used by $\lambda_{\mathtt{IFC}}^{c}$; in particular, it defines the *security
    coercions on values* of $\lambda_{\mathtt{IFC}}^{c}$.


### The shared heap model [in directory `Memory/`](./src/Memory)

-   [`Memory.Addr`](./src/Memory/Addr.agda): Definition of memory addresses.
-   [`Memory.Heap`](./src/Memory/Heap.agda): Definition and helper methods of the split-heap model, where
    low and high addresses are indexed separately. For example, heap lookup has
    the form $\mu(\ell, n) = V$, where $\ell$ is the security level of the memory
    cell, $n$ is the index of the part of the memory where all cells are
    labeled $\ell$, and $V$ is the value stored at $(\ell, n)$.
-   [`Memory.HeapTyping`](./src/Memory/HeapTyping.agda): Definition of heap well-typedness. It is defined
    point-wise. The typing judgment has the form $\Sigma \vdash \mu$, where
    $\Sigma$ is the heap context and $\mu$ is the (well-typed) heap.


### Technical definitions of the surface language $\lambda_{\mathtt{SEC}}^\star$ [in directory `Surface/`](./src/Surface)

-   [`Surface.SurfaceSyntax`](./src/Surface/SurfaceSyntax.agda): The syntax definition of $\lambda_{\mathtt{SEC}}^\star$. It uses
    [the Abstract Binding Tree (ABT) library](https://github.com/jsiek/abstract-binding-trees). For example, the term of function
    application has the signature `sig (op-app p) = ■ ∷ ■ ∷ []`, because it
    contains two sub-terms and introduces no binder. On the other hand, the term
    for $\lambda$ abstraction has the signature `sig (op-lam pc A ℓ) = (ν ■) ∷
      []`, because there is one free variable in the body of a $\lambda$ (indicated
    by `(ν ■)`).
-   [`Surface.SurfaceTyping`](./src/Surface/SurfaceTyping.agda): The typing rules for $\lambda_{\mathtt{SEC}}^\star$. The typing
    judgment takes the form $\Gamma ; g \vdash M : A$, where $\Gamma$ is the
    typing context, $g$ is the static program counter (PC) label, $M$ is a surface
    language program, and $A$ is the security type that $M$ is typed at.


### Technical definitions of the cast calculus $\lambda_{\mathtt{SEC}}^{c}$ [in directory `CC/`](./src/CC)

-   [`CC.CCSyntax`](./src/CC/CCSyntax.agda): The syntax definition of $\lambda_{\mathtt{SEC}}^{c}$. Again, the module uses
    the ABT library. There are a few terms that arise during runtime, including
    memory addresses, casts, PC casts (`cast-pc`), protection terms (`prot`), and
    runtime errors (`error`). The opaque term (●) is used in the erasure-based
    noninterference proof.
-   [`CC.CCTyping`](./src/CC/CCTyping.agda): The typing judgment is of form $\Gamma ; \Sigma ; g ; \ell
      \vdash M : A$. It contains 6 field: $\Gamma$ is the typing context; $\Sigma$
    is the heap context; $g$ is the static PC, which can be viewed as the
    compile-time approximation of the runtime PC; $\ell$ is the dynamic (runtime)
    PC; $M$ is a $\lambda_{\mathtt{SEC}}^{c}$ term; $A$ is the type of $M$.
-   [`CC.HeapTyping`](./src/CC/HeapTyping.agda): Lemmas about heap well-typedness for $\lambda_{\mathtt{SEC}}^{c}$. These
    lemmas are used in the type safety proof.
-   [`CC.Values`](./src/CC/Values.agda): The definition of values in $\lambda_{\mathtt{SEC}}^{c}$. A value can be (1) a
    constant (2) an address (3) a $\lambda$ abstraction or (4) a value wrapped
    with an irreducible (`Inert`) cast. The opaque term is also a value in the
    semantics of erased $\lambda_{\mathtt{SEC}}^{c}$. There are canonical-form lemmas for
    constants, functions, and memory addresses in this model: for example, a value
    of function type must be either a $\lambda$ or a function proxy (a $\lambda$
    wrapped with at least one inert function cast).
-   [`CC.Reduction`](./src/CC/Reduction.agda): The operational semantics for $\lambda_{\mathtt{SEC}}^{c}$. The relation
    $M \mid \mu \mid \ell \longrightarrow N \mid \mu'$ says that $\lambda_{\mathtt{SEC}}^{c}$
    term $M$ reduces with heap $\mu$ under PC label $\ell$ (by one step) to
    term $N$ and heap $\mu'$.
    -   The rule `cast` turns to the `ApplyCast` relation defined in the following
        module:
        -   [`CC.ApplyCast`](./src/CC/ApplyCast.agda): The cast-application relation has the form
            $\mathtt{ApplyCast}\;V , c \leadsto M$, where $V$ is a value and $c$ is
            the cast to apply; $M$ can be either a value, or a cast error (`blame`) if
            the cast application fails.
    -   The rule `fun-cast`, `assign?-cast`, and `assign-cast` turn to the
        proxy-elimination helpers that are defined in the following module:
        -   [`CC.ProxyElimination`](./src/CC/ProxyElimination.agda): The module defines two helper functions:
            `elim-fun-proxy` works on a function proxy and `elim-ref-proxy` works on a
            reference proxy. The helpers check the well-formedness of the outermost
            inert cast, generate proper casts that preserve types if well-formed and
            signal errors if ill-formed.
-   [`CC.Interp`](./src/CC/Interp.agda): A stepper that replies on the progress proof to generate a
    reduction sequence of $k$ steps for a well-typed $\lambda_{\mathtt{SEC}}^{c}$ term.
-   [`CC.Compile`](./src/CC/Compile.agda): Compilation from $\lambda_{\mathtt{SEC}}^\star$ to $\lambda_{\mathtt{SEC}}^{c}$. The module
    also contains a proof that the compilation preserves types
    (`compilation-preserves-type`).

The noninterference proof of $\lambda_{\mathtt{SEC}}^{c}$ is erasure-based. It uses the
following auxiliary definitions:

-   [`CC.BigStep`](./src/CC/BigStep.agda): The big-step semantics for $\lambda_{\mathtt{SEC}}^{c}$. It is a direct
    mechanical translation from the semantics in [CC.Reduction](./src/CC/Reduction.agda).
-   [`CC.Erasure`](./src/CC/Erasure.agda): Definition of the erasure functions for $\lambda_{\mathtt{SEC}}^{c}$ terms
    (`erase`) and heaps (`erase-μ`). Note that the memory cells of high security
    are completely erased, because the values read from those cells are always
    of high security and thus appear to be opaque for a low observer.
-   [`CC.BigStepErased`](./src/CC/BigStepErased.agda): The big-step semantics for erased $\lambda_{\mathtt{SEC}}^{c}$.


### Technical definitions of the surface language $\lambda_{\mathtt{IFC}}^\star$ [in directory `Surface2/`](./src/Surface2)

-   [`Surface2.Syntax`](./src/Surface2/Syntax.agda): The syntax of $\lambda_{\mathtt{IFC}}^\star$. The most noteworthy difference
    from $\lambda_{\mathtt{SEC}}^\star$ is that in $\lambda_{\mathtt{IFC}}^\star$, the PC annotation on a $\lambda$
    is treated as a type annotation, which means that it can be $\star$.
-   [`Surface2.Typing`](./src/Surface2/Typing.agda): The typing rules for $\lambda_{\mathtt{IFC}}^\star$.
-   [`Surface2.Precision`](./src/Surface2/Precision.agda): The precision rules for $\lambda_{\mathtt{IFC}}^\star$. The precision
    relation is used in the definition and the proof of the gradual guarantee.


### The coercion calculus for security labels [in directory `CoercionExpr`](./src/CoercionExpr)


### Security label expressions [in directory `LabelExpr`](./src/LabelExpr)


### Technical definitions of the cast calculus $\lambda_{\mathtt{IFC}}^{c}$ [in directory `CC2/`](./src/CC2)

-   [`CC2.Syntax`](./src/CC2/Syntax.agda): As usual, the cast calculus $\lambda_{\mathtt{IFC}}^{c}$ is a statically-typed
    language that includes an explicit term for casts. Many of the operators in
    $\lambda_{\mathtt{IFC}}^{c}$ have two variants, a "static" one for when the pertinent security
    label is statically known (such as `ref`) and the "dynamic" one for when the
    security label is statically unknown (such as `ref?`). The operational
    semantics of the "dynamic" variants involve runtime checking.
-   [`CC2.Typing`](./src/CC2/Typing.agda): The typing judgment is of form
    $\Gamma ; \Sigma ; g ; \ell \vdash M \Leftarrow A$. The six fields are of the
    same meanings as those of $\lambda_{\mathtt{SEC}}^{c}$. The main difference is that the typing
    of $\lambda_{\mathtt{IFC}}^{c}$ stays in checking mode, so the type $A$ is considered an input of
    the judgment.
-   [`CC2.HeapTyping`](./src/CC2/HeapTyping.agda): Lemmas about heap
    well-typedness for $\lambda_{\mathtt{IFC}}^{c}$. They are similar to those of $\lambda_{\mathtt{SEC}}^{c}$ because
    $\lambda_{\mathtt{IFC}}^{c}$ shares the same heap model as $\lambda_{\mathtt{SEC}}^{c}$.
-   [`CC2.Values`](./src/CC2/Values.agda): The definition of values in $\lambda_{\mathtt{IFC}}^{c}$.
    A raw value can be (1) a constant (2) an address or (3) a $\lambda$
    abstraction. A value can be either a raw value, or a raw value wrapped with an
    irreducible cast. A cast is irreducible if its top-level security label
    coercion is in normal form and the cast is not identity.
-   [`CC2.Reduction`](./src/CC2/Reduction.agda): The operational semantics for $\lambda_{\mathtt{IFC}}^{c}$. Similar to the one of
    $\lambda_{\mathtt{SEC}}^{c}$, the relation $M \mid \mu \mid \ell \longrightarrow N \mid \mu'$
    says that $\lambda_{\mathtt{IFC}}^{c}$ term $M$ reduces with heap $\mu$ under PC label $\ell$ to
    term $N$ and heap $\mu'$.
-   [`Compile.Compile`](./src/Compile/Compile.agda): The compilation function from $\lambda_{\mathtt{IFC}}^\star$ to $\lambda_{\mathtt{IFC}}^{c}$.

