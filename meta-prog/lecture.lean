/- Meta programming in Lean -/

/-

The central type to represent the logical content is `expr`, together with `name` and `level`.

`expr` are expressions (e.g. terms, types & proofs)
`name` used to reference constants & local hypothesis, etc
  pretty printed names, name spaces names, internal unique names
`level` express universe levels

Only parts of them are used to express type correct final terms. They can also contain local
variables and meta variables.

-/
#print expr
#print name
#print level

namespace lecture

open expr tactic












section expr -- let's construct some terms

-- A very simple definition: Prop, i.e. Sort 0
meta def prop : expr := sort level.zero

run_cmd trace prop
-- outputs: Prop ← this is the object logic Prop













-- Let's represent logic as meta expressions:

meta def or_ (a b : expr) : expr :=
((const `or []).app a).app b

meta def and_ (a b : expr) : expr :=
((const `and []).app a).app b

meta def true_ : expr :=
const `true []

meta def false_ : expr :=
const `false []

meta def imp_ (a b : expr) : expr :=
pi `hyp binder_info.default a b













run_cmd trace (imp_ false_ true_)

run_cmd trace (and_ true_ (and_ false_ false_))













-- Use antiquotations `(e) as easier way to write expressions:

run_cmd trace `(true ∧ false)

meta def and_aq (a b : expr) : expr :=
`(%%a ∧ %%b)













-- Problem: When we use %%a the type must be known by context
--   this will relaxed in tactic mode...
meta def imp_aq (a b : expr) : expr :=
`((%%a : Prop) → (%%b : Prop))

meta def nat_add_aq (a b : expr) : expr :=
`(%%a + %%b : ℕ)














/- Example: project the i-th or in a sequence of
  p₀ ∨ (p₁ ∨ (⋯ ∨ pn))

We can use antiquotation for pattern matching
-/
meta def project_or : expr → ℕ → expr
| `(%%a ∧ %%b) 0       := a
| `(%%a ∧ %%b) (n + 1) := project_or b n
| e            _       := e




#check @and.left
/- Example: proof the i-th disjunct given a sequence
  p₀ ∧ (p₁ ∧ (⋯ ∧ p_n)) → p_i
-/
meta def and_in : expr → ℕ → expr → expr
| `(%%a ∧ %%b) 0       h := `(@and.left %%a %%b %%h)
| `(%%a ∧ %%b) (n + 1) h := and_in b n `(@and.right %%a %%b %%h)
| e            _       h := h






example {p q r : Prop} (h : p ∧ (q ∧ r)) : q :=
by do
  h ← get_local `h,
  t ← infer_type h,
  trace t,
  trace (and_in t 1 h),
  infer_type (and_in t 1 h) >>= trace,
  tactic.exact (and_in t 1 h)

end expr






/- Variables / Constant -/
section vars

/- declared constant:
Constant refering to global declarations, and can be looked up in the name space. They are also
universe parametric, so a list of concrete universe levels needs to be provided. -/
#check (const : name → list level → expr)

/- bound variable:
de-Bruijn indexed, i.e. just a natural number giving the distance to the corresponding lambda / pi.
-/
#check (var : ℕ → expr)

/- local constant:
Are arbitrarily created, but we need a unique name.
-/
#check (local_const : name → name → binder_info → expr → expr)

/- meta variable:
Represent holes in our proof / term. Represent the goals we want to solve, or holes to fill in when
unifying two terms.
-/
#check (mvar : name → name → expr → expr)

/-
Using bound variables with de-Bruijn indices and free variables with names is called a
**locally nameless representation**.

Local variables and Meta variables exist also for universe levels. They are only used to
construct a term. In the final declaration local and meta variables do not occur anymore.

Local variables are often used to **walk** into a binder (i.e. a Π or a λ): a new unique name is
used to create a `local_const` expression using the pretty print name, the binder information, and
the type of the bound variable. In the expression itself the bound variable is replaced by the local
variable.

In the interface `expr` is often used instead of the name of the local constant, as `expr` contains
all necessary information.
-/

section deBruijn
-- Let's play with binders:

meta def id (α : expr) : expr :=
lam `a binder_info.default α (var 0)

meta def flip (α : expr) (f : expr) : expr :=
lam `a binder_info.default α (lam `b binder_info.default α ((f.app (var 0)).app (var 1)))

run_cmd trace (id (const `nat []))

run_cmd trace (flip (const `nat []) `((+) : ℕ → ℕ → ℕ))

meta def forall_prop (e : expr) : expr :=
pi `a binder_info.default (sort level.zero) e

run_cmd trace (forall_prop (var 0))
run_cmd trace (forall_prop (imp_ (var 0) true_))
run_cmd trace (forall_prop (imp_ false_ (var 0))) -- oops
run_cmd trace (forall_prop (imp_ false_ (var 1)))

meta def imp' (a b : expr) : expr :=
pi `hyp binder_info.default a (b.lift_vars 0 1)

run_cmd trace (forall_prop (imp' false_ (var 0)))

-- Lean does it right
run_cmd trace (forall_prop (imp_aq false_ (var 0)))

end deBruijn







section locally_nameless

/- local variables ⇔ bound variables

expr.abstract_local C[local_const n _ _ _] n ~> C[var 0]
expr.instantiate_var C[var 0] t ~> C[t]
-/
#check expr.abstract_local
#check expr.instantiate_var







/- instantiate a local constant with a term

expr.instantiate_local n t C[local_const n _ _ _] ~> C[t]
-/
#check expr.instantiate_local
#check expr.instantiate_locals







/- create Π and λ from a term and a list of local variables:

expr.pis [l_0 : t_0, …, l_n : t_n] t[l_0, …, l_n] ~>
  Π(l_0 : t_0) ⋯ (l_n : t_n), t[var n, …, var 0]
expr.lambda [l_0 : t_0, …, l_n : t_n] t[l_0, …, l_n] ~>
  λ(l_0 : t_0) ⋯ (l_n : t_n), t[var n, …, var 0]

The `t_i` are allowed to contain `l_j` for `j < i`. The binder also follows the binder info and
pretty printing name of the local variable.
-/
#check expr.pis
#check expr.lambdas







/- Create a local variable: -/
#check tactic.mk_local' -- needed to get a unique name







/- Walk into a sequence of Π:

tactic.mk_local_pis (Π(v_0 : t_0)⋯(v_n : t_n),
  t[var n, …, var 0]) ~>
  ([v_0, …, v_n], t[v_0, …, v_n])
-/
#check tactic.mk_local_pis







end locally_nameless

end vars

end lecture