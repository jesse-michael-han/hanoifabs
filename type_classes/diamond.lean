import analysis.real

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
