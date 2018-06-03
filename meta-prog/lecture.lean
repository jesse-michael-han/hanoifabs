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

/-

The `tactic` monad allows us to construct expressions, and interact with the user. It also gives us
access to Lean's global data, i.e. all declarations (axioms, constant & inductive definitions,
names), attribute lists, options, etc...

-/

#check tactic
#print prefix tactic
#check declaration
#print prefix declaration

/-

`expr (elaborated : bool) : Type`

`elaborated`: is true if the term is fully elaborated, i.e. constants are fully applied, and
  resolved.

`expr ff` are also called pre-elaborated or `pexpr`. They contain a lot of macros from the parser
for things which need to be decided, found etc. by the elaborator. The idea is to carry this data
around until we are in a context where they can be elaborated.

Example:
-/

example : ∀a:ℕ, a ≤ a ∧ a ≤ a :=
begin
  intro a,
  split; exact le_refl _
end

/-

The interesting part is: at which time is `le_refl _` elaborated, i.e. when does Lean try to figure
out what its implicit parameters, its type class instances, and what to fill in at `_`. If it would
try it already at the parsing time it would fail, `exact` doesn't gice us any information at all.

Even more interesting: `exact` gets executed twice! There is no unique elaborated term which would fit!

The solution: Lean passes pre-elaborated terms to tactics!
 E.g. the `exact` tactic gets `le_refl _` as a pre-elaborated term.
 Then `exact` produces the term: `le_refl _ : a ≤ a` and lets it elaborate.
 In our example this happens two times.

Unfortunately, pre-elaborated terms usually contain a lot of macros and other things which we
can not access through Lean's `expr`/`tactic` interface. What we can do is: bring the term in the
right context and tell the elaborator **how** to elaborate it (generating meta-variables / subgoals).

-/

example : true := by do
  e ← return ``(0 + @has_one.one ℤ int.has_one),
  tactic.trace "e",
  tactic.trace e.to_raw_fmt,
  e' ← tactic.to_expr e,
  tactic.trace "e'",
  tactic.trace e'.to_raw_fmt,
  return ()

open tactic expr

example : true := by do
  t ← mk_meta_var (sort (level.zero.succ)),
  x ← return $ local_const `x `x binder_info.default t,
  mt ← infer_type x,
  trace (to_fmt "mt: " ++ to_fmt mt),
  e ← to_expr ``(%%x  = 0),
  get_assignment mt >>= trace

