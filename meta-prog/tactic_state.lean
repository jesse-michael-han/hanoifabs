/- The internal `tactic` state

The `tactic` monad contains a lot of internal state, especially the meta (universe) variables,
and their corresponding typing context.

-/

open tactic

/- The `tactic` monad allows us to construct expressions, and interact with the user, access
Lean's environment. The environment contains all declarations (axioms, constant, inductive
definitions), attribute lists, options, etc... -/

#check tactic
#print prefix tactic
#check declaration
#print prefix declaration


-- we can do very basic stuff in the tactic framework

example {α : Type} : ∀a:α, a = a :=
begin
  intro,
  reflexivity
end

example {α : Type} : ∀a:α, a = a := by do
  intro `a,
  reflexivity






meta def find (t : expr) : list expr → tactic expr
| []        := failed
| (h :: lc) := do
  t_h ← infer_type h,
  ((do unify t t_h, return h)
    <|>
    find lc)

meta def my_assm : tactic unit := do
  lc ← local_context,
  t ← target,
  h ← find t lc,
  exact h

example {p q : Prop} (h : p) (h' : q) : q := by do
  my_assm





/- How does the tactic state work?

`set_goals`, `get_goals`: Set and get the list of goals.
  * A goal is not the statement to proof, but the meta variable to fill in.
  * The goal statement is the **type** of the metavariable.

`infer_type`: Infers the type of a term. This is sometimes important for local variables! Local
  variables appearing in a goal often have the __wrong__ type associated. The type needs to be
  infered using `infer_type`. But be aware: if you construct a term using local variable, you need
  to use the type from the local context.

Meta variables `?m : Γ ⊢ t`:
  * a meta variable (a.k.a schematic variable, existential) is a hole in a term which can be
    instantiated at an arbitrary time point in the elaboration process
  * `?m` name of the meta variable (not a pretty printed name)
  * `Γ` a list of local variables (including binder information for type classes)
  * `t` the type of the meta variable, i.e. the type of the hole
  * managed by the tactic framework, generally not directly manipulated
  * `?m[n := t]` when the meta variable is finally instantiated, replace the local variable `n`
    by the term `t`.

`mk_meta_var t`: creates a meta variable of type `t` in the current type context (i.e. the main
  goal).

  How to create a meta variable when we don't know the type?

  Solution: create a meta-variable representing the type!
  `mk_mvar := do
    l ← mk_meta_univ,
    t ← mk_meta_var (sort l),
    mk_meta_var t`

How to instantiate meta variables: `unify`

Other ways to query and operate on meta variables: set it as the main goal!
-/

section internal_tactics

section intro
/- How `intro` works:

Goal:
  ?g0 : Γ ⊢ Πx:t, s

Introduce a new name `x.0`:

  * New Metavariable
    ?g1 : Γ, (x.0 : t) ⊢ s

  * Instantiate:
    ?g0 := λx:t, ?g1[Γ := Γ, x.0 := x]

-/

end intro











section apply

/- How `apply r` works:

Create a meta variable for all additional parameters, i.e. if the goal is
  ?g : Γ ⊢ ∀x_n … x_0, t
  and you apply `r : ∀x_(n + i) … x_n … x_0, t'` then apply creates `i` meta variables, and
  instantiates the rule `r` with these variables. Ths type of `r ?m_i … ?m_0` is unified with the
  type of `?g`, this instantiates already some meta variables. The remaining ones are added as
  new goals.

-/

end apply











section induction

/- How does `induction` work? Why to be careful with local variables.

I annotated each local variable with an additional **unique** identifier.

?g0 :   Γ, (n.0 : ℕ), (h.1 : 0 < n.0)  ⊢  p n.0

Revert `n.0` and all hypothesis depending on `n.0`:

  * New metavariable:
    ?g1 : Γ  ⊢  ∀(n : ℕ) (h : 0 < n), p n

  * Instantiate
    ?g0 := ?g1[Γ := Γ] n.0 h.1

Apply `nat.rec`:

  * New metavariables:
    ?g2 : Γ  ⊢  ∀(h : 0 < 0), p 0
    ?g3 : Γ  ⊢  ∀(n : ℕ) (ih : ∀0<n, p n) (h : 0 < (n+1)), p (n+1)

  * Instantiate:
    ?g1 := nat.rec ?g2[Γ := Γ] ?g3[Γ := Γ]

Introduce locals again:
  * Create new local names / variables:
    h.2, n.3, ih.4, h.5

  * New metavariables:
    ?g4 : Γ, (h.2 : 0 < 0) ⊢ p 0
    ?g5 : Γ, (n.3 : ℕ), (ih.4 : ∀0<n.3, p n.3), (h.5 : 0 < n.3 + 1) ⊢ p (n.3 + 1)

  * Instantiate:
    ?g2 := λh, ?g4[Γ := Γ, h.2 := h]
    ?g3 := λn ih h, ?g4[Γ := Γ, n := n.3, ih := ih.4, h := h.5]

While some variables stay the same (everything in `Γ`), some variables which look unchanged are
actually changing, i.e. `h` and `n` in the induction step.

-/

end induction

end internal_tactics
