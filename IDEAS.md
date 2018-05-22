Lean foundation
===============

...

Lean programming
================

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
 * data: list, multiset, finset, equiv, ...
 * how to handle `decidable` vs `classical`
 * algebra: groups, rings, and linear algebra
 * set theory
 * analysis: filters, topology, etc

Style
-----

maybe give a short introduction for the style guide?

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

(Data) Types
------------

 * sometimes a more general structure makes it simpler (list A vs list_of_ints)
 * map, seq, bind, relator, ...
 * order structures
 * different induction, recursion schemas
 * (equivalence) relations between types

Dependent Types
---------------

 * how to handles indexed types especially rewriting
 * how to avoid parametered types
