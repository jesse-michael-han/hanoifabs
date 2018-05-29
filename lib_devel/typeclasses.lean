import analysis.real

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

section
noncomputable theory

variables (α : Type*) (β : Type*)

class topology := (open_sets : set (set α))

def cont [topology α] [topology β] (f : α → β) : Prop :=
∀s∈topology.open_sets β, f ⁻¹' s ∈ topology.open_sets α

class metric := (dist : α → α → ℝ)

def metric.to_topology [metric α] : topology α :=
⟨{s : set α | ∀(x:α), x∈s → ∃ε>0, ∀y, metric.dist x y < ε → y ∈ s}⟩

local attribute [instance] metric.to_topology

instance real_topology : topology ℝ :=
⟨{s : set ℝ | ∀(x:ℝ), x∈s → ∃ε>0, ∀y, abs (x - y) < ε → y ∈ s}⟩

-- now in each metric dist is continuous

private lemma cont_dist [metric α] (a : α) : cont α ℝ (metric.dist a) := sorry

-- we have a product topology
instance prod_topology [topology α] [topology β] : topology (α × β) :=
⟨{s : set (α × β) | ∀a b, (a, b) ∈ s →
  ∃u∈topology.open_sets α, a ∈ u ∧ ∃v∈topology.open_sets β, b ∈ v ∧ set.prod u v ⊆ s}⟩

-- but we also want a product metric:
instance prod_metric [metric α] [metric β] : metric (α × β) :=
⟨λ⟨a₀, b₀⟩ ⟨a₁, b₁⟩, max (metric.dist a₀ a₁) (metric.dist b₀ b₁)⟩

-- now we have a problem:

example [m₁ : metric α] [m₂ : metric β] :
  @metric.to_topology (α × β) (prod_metric α β) =
    @prod_topology α β (metric.to_topology α) (metric.to_topology β) :=
rfl -- uhuh it is not defeq!

-- set_option pp.implicit true
example [m₁ : metric α] [m₂ : metric β] (a : α) (b : β) :
  cont (α × β) ℝ (metric.dist (a, b)) :=
cont_dist (α × β) (a, b)
  -- this doesn't work! the product metric is not defeq  to the product topology!

end

section solution1
variables (α : Type*) (β : Type*)

class metric_induced_topology [metric α] [topology α] : Prop :=
(open_sets_iff :
  ∀s, s ∈ topology.open_sets α ↔ (∀(x:α), x∈s → ∃ε>0, ∀y, metric.dist x y < ε → y ∈ s))

private lemma cont_dist
  [topology α] [metric α] [metric_induced_topology α] (a : α) :
  cont α ℝ (metric.dist a) := sorry

instance prod.metric_induced_topology
  [topology α] [metric α] [metric_induced_topology α]
  [topology β] [metric β] [metric_induced_topology β] :
  metric_induced_topology (α × β) :=
sorry

example
  [topology α] [metric α] [metric_induced_topology α]
  [topology β] [metric β] [metric_induced_topology β]
  (a : α) (b : β) :
  cont (α × β) ℝ (metric.dist (a, b)) :=
cont_dist (α × β) (a, b) -- TADA!!

end solution1

section solution2
variables (α : Type*) (β : Type*)

class metric_v2 extends topology α :=
(dist : α → α → ℝ)
(open_sets_iff :
  ∀s, s ∈ topology.open_sets α ↔ (∀(x:α), x∈s → ∃ε>0, ∀y, dist x y < ε → y ∈ s))

end solution2
