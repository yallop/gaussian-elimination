This directory contains a staged implementation of Gaussian Elimination, a work in progress adapted from the following code:

&nbsp;&nbsp;&nbsp;[Multi-stage programming with functors and monads: eliminating abstraction overhead from generic code](https://www.cas.mcmaster.ca/~carette/metamonads/)  
&nbsp;&nbsp;&nbsp;Jacques Carette and Oleg Kiselyov  

### Differences

As the title suggests, _Multi-stage programming with functors and monads_ uses two mechanisms to structure the Gaussian Elimination code:

  * **functors** decompose the code into independent composable modules, each capturing some aspect of the algorithm family.

  * **monads** support the use of effects in the code generator.  The particular monad used in the paper provides two effects:  
    - state, for passing around a (carefully-typed) environment
    - continuations -- or, more specifically, `let`-insertion using continuations

The implementation here replaces the use of monads with algebraic effects and handlers, which allows the code to be written in direct style rather than the monadic style of the paper.  (In fact, algebraic effects are only used here to provide `let` insertion; it is possible to implement state using algebraic effects, but in accordance with the new direct-style structure the adapted code here uses the host language `ref` for the environment type.)

Switching from monads to effects provides several advantages: it separates the implementation of the handler from the code, it avoids the need for combinators to combine continuations, and it interacts with the control operators of the host language in a natural way.  With the current implementation of effects there are also some drawbacks.  Most notably, since effects are untyped, some of the precise typing of the original (which captured and constrained control flow) becomes lost.

### Installation

Since the code here uses two features that are not yet merged into the main OCaml distribution --- BER MetaOCaml staging constructs, and algebraic effects --- a modified compiler is needed to build the code.  The steps are as follows:

* Install OPAM, the OCaml package manager ([installation instructions](https://opam.ocaml.org/doc/Install.html))

* Add the `advanced-fp` repository to OPAM, to pick up the description of the modified compiler:
  ```
  opam remote add advanced-fp https://github.com/ocamllabs/advanced-fp-repo.git
  ```

* Install the modified compiler:
  ```
  opam switch 4.03.0+effects-ber
  ```

* Type `make` in the root directory to build this code.  To test the code, run `make test`.
