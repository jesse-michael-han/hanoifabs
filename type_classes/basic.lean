/- Tips and Tricks for the Type Class Hierarchy -/

/-
Type classes are the go to approach to model mathematical abstractions.

  * To work with type classes the elaborator needs a way to find a unique instance.
    Usually this is a type, sometimes its an operator.

    * Use when when things are easy to index (usually by their type)

    * Don't use them when you have multiple instances per index

    * Uniqueness is important (at least by defeq), otherwise the elaborator fails at unexpected
      places

  * If you're lucky your theory has only one spine, i.e. a inheritance chain à la A → B → C → D

  * Syntactic type classes (pure data):
      `class has_add (α : Type*) := (add : α → α → α)`
      * in Type
      * only one syntactic element (e.g. +)
      * no properties attached

  * Property classes (in Prop): (TODO: is this the right name?)
      `class is_commutative (α : Type*) (op : α → α → α) := (comm : ∀a b, op a b = op b a)`
      * in Prop
      * no data elements
      * can depend on other type classes either by inheritance or by parameters

  * Balance between

  * Example: Topological structures in mathlib:

    * `topological_space` → `uniform_space` → `metric_space`

    * confusing for mathematicans: each metric space has a uniform space, has a topological space
      assigned

    * why not have separat type classes with relation instances?
      -> wanted definitional equality & uniqueness

    * another solution: have relational classes
      `ordered_topology (α : Type*) [topological_space α] [preorder α] : Prop`

      annoying to use, needs a long list of parameters for each abstract definition / theorem

-/

/-

TODO: reading the type class inference trace

-/