Lean foundation
===============

...

Lean programming
================

  * advanced: monad transformers, ...

  * Lean programming:
    * Monad combinators?
    * understanding expr / tactic: meta variables, local variables, universes, `mk_mapp`
    * conv?


Lean meta programming
=====================

  * basic Lean interfaces: `expr`, `tactic`, `name`, `level`, etc.
  * basic tactics: `apply`, `induction`, `cases`, ...
  * goal management and what are the differences between local variables, constants & meta variables
    * pp names, unique names, and types: when are they important, when do they change
    * how to analyse and create terms
  * the unifier (`defeq`)
  * the simplifier and how to use it
  * writing interactive tactics: providing a nice interface
  * user attributes (advanced: caching)
  * user commands
  * advanced: monad transformers, conversions, ...
  * how to construct proofs:
    * combine tactics
    * upfront production of terms & proofs
    * mixture

Tutorial ideas:
  * some basic algebraic tactics, like cancellation
  * writing a custom induction tactic
  * implementing John Harrisons `wlog` and invariance tactics.

Lean libraries
==============

Mathlib and the Lean repository

Structure
---------

To show what is available, and a little bit how it is organizied. So people know at what places they
might look to find something.

  * numbers
  * type class hierarchies
  * data: list, multiset, finset, finsupp, equiv, ...
  * big operators (using sum operators to construct elements?)
  * how to handle `decidable` vs `classical`
  * algebra: groups, rings, and linear algebra
  * set theory
  * analysis: filters, topology, etc
  * category theory light: complete lattices, Galois connections, map, bind, etc

Style
-----

  * maybe give a short introduction for the style guide?
  * module nameing convention (`basic.lean`, maybe use `default.lean`)
  * using type induced names (i.e. `x.f`)

Tactics
-------

additional tactics in mathlib

Organizing libraries
====================

Type classes
------------

  * thinking about type class hierarchies
  * structures vs classes
  * Type vs Prop classes
  * playing around with auto, and default params, inheritance
  * when to use Sort, Type and Prop
  * different way to index: HOL / DTT vs mathematics / category theory
  * problems with universe level (esp. when concerning category theory)
    e.g. `list.map` vs `functor.map`

(Data) Types
------------

  * working with subtypes & quotient types
  * sometimes a more general structure makes it simpler (list A vs list_of_ints)
  * map, seq, bind, relator, ...
  * order structures
  * different induction, recursion schemas
  * (equivalence) relations between types

Dependent Types
---------------

  * when to use dependent types, when to encode dependencies in another way (HOL approach)
    * how to handle indexed types, especially rewriting
    * how to avoid parametered types
  * using definitional equality vs. proofs
  * inductive Prop <-> using quantifiers and logical connectives

Theorem statements
------------------

  * How to handle `decidable`, proofs, other subsingletons i.e. depending on the intended application
    assume a corresponding proof, or construct one yourself in the theorem statement

Various other
-------------

  * `noncomputable`
  * classical choice versus explicit data (maybe even `subsingleton`)
  * differences to software verification
  * Term mode vs. Tactic mode?
  * special tactics and how to use them:
    - simplifier
    - (r)cases, generalizing, ...
    - ring?
    - transfer?
    - wlog?

