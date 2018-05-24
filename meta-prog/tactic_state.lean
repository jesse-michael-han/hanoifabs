/- The internal `tactic` state

The `tactic` monad contains a lot of internal state, especially the meta (universe) variables,
and their corresponding typing context.

-/

open tactic

/- Variables / Constant -/
section variables

#check (expr.const : name → list level → expr)
#check (expr.local_const : name → name → binder_info → expr → expr)
#check (expr.mvar : name → name → expr → expr)
#check (expr.var : ℕ → expr)

/-
  * `const`: Constant refering to global declarations, and can be looked up in the name space,
    they are also universe parametric.

  * `local_const` (Local variables) can be arbitrarily create, but if used to fill in a goal, only
    local variables from the local context are allowed (including the type!)

  * `mvar` (Meta variables): Holes in our proof / term. Represent the goals we want to solve, or
    holes to fill in when unifying two terms.

  * `var` (Bound variables): are de-Bruijn indexed, i.e. just a natural number refering to the
    corresponding lambda.

    Important: When we write a context `C[var 0]`, this doesn't mean that C is a context of `var 0`
    but `var i` depending on the number of binders it occurs in:
      In a context `C[*] = λa, * a`:  `C[var 0] ≝ λa, (var 1) a`

Using bound variables with de-Bruijn indices and free variables with names is called a
**locally nameless representation**.

Local variables and Meta variables exist also in the level representation. They are only used to
construct a term. In the final declaration local and meta variables do not occur anymore.

Local variables are often used to **walk** into a binder (i.e. a Π or a λ): a new unique name is
used to create a `local_const` expression using the pretty print name, the binder information, and
the type of the bound variable. In the expression itself the bound variable is replaced by the local
variable.

In the interface `expr` is often used to carry all the information of a local constant.
-/

section locally_nameless

/- replace local variables by bound variables

expr.abstract_local C[local_const n _ _ _] n ~> C[var 0]
-/
#check expr.abstract_local
#check expr.abstract_locals
#check expr.abstract

/- instantiate bound variables by terms

expr.instantiate_var C[var 0] t ~> C[t]
-/
#check expr.instantiate_univ_params
#check expr.instantiate_var
#check expr.instantiate_vars

/- instantiate local variables by terms

expr.instantiate_local n t C[local_const n _ _ _] ~> C[t]
-/
#check expr.instantiate_local
#check expr.instantiate_locals

/- create Π and λ from a term and a list of local variables:

expr.pis [l_0 : t_0, …, l_n : t_n] t[l_0, …, l_n] ~> Π(l_0 : t_0) ⋯ (l_n : t_n), t[var n, …, var 0]
expr.lambda [l_0 : t_0, …, l_n : t_n] t[l_0, …, l_n] ~> λ(l_0 : t_0) ⋯ (l_n : t_n), t[var n, …, var 0]

The `t_i` are allowed to contain `l_j` for `j < i`. The binder also follows the binder info and
pretty printing name of the local variable.
-/
#check expr.pis
#check expr.lambdas


/- Create a local variable: -/
#check tactic.mk_local' -- needed to get a unique name

/- Walk into a sequence of Π:

tactic.mk_local_pis (Π(v_0 : t_0)⋯(v_n : t_n), t[var n, …, var 0]) ~>
  ([v_0, …, v_n], t[v_0, …, v_n])
-/
#check tactic.mk_local_pis

end locally_nameless

end variables

section term_construction

/-
Note on term construction
-------------------------

Many operations are not type checked. It is possible to write tactics which produce type
incorrect terms and fail at a later stage.

-/

example : ℕ := by do
  -- we contstruct a type incorrect local variable
  (l : expr) ← return $ expr.local_const `n `n binder_info.default (expr.const `has_add.add []),
  t ← infer_type l, -- this just returns the type
  trace t.to_raw_fmt,
  t ← infer_type (l.app l), -- this produces an error
  trace t.to_raw_fmt,
  skip

example : ℕ := by do
  (l : expr) ← return $ expr.local_const `n `n binder_info.default (expr.const `ℕ []),
  (m : expr) ← mk_mvar,
  t ← infer_type (m.app l), -- infer does not unify meta variables
  trace t.to_raw_fmt,
  skip

end term_construction


/- How does the goal list work?

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
