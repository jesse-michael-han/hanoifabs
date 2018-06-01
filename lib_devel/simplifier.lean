/- Simplifier -/

#check tactic.simplify
#check tactic.interactive.simp

/-

The simplifier is currently the most powerful tactic in Lean (besides definitional equality). Many
problems can be solved by rewriting. But for this it is important to understand the simplifier and
how to organize its rewrite rules.

Basic idea:

  * the simplifier has an database of simp rules `l = r` (can be extended using `@[simp]`)

  * when invoked it tries to rewrite with as much of these simp rules as possible

  * bottom-up: i.e. when run on `f a` it first tries to rewrite `f = f'` then `a = a'`
    and only `f' a'`, if `f' a'` is rewritten, then the simplifier walks again over this term.

  * uses congruence rules `@[congr]` to avoid some problems with dependent types

  * permutation check allows to add commutativity rules

  * there is also `dsimp` which only unfold definitional equal rules:
    doesn't have type dependence problems

  * β-reduction: (λa, f a) x = f x
  * ζ-reduction: let t = x in C[x] = C[t]
  * ι-reduction: prod.fst (a, b) = a

  * contextual := tt:

      p → q:  uses p when proving the assumptions of a conditional rw rule

      a = b → q: adds a = b as rewrite rule

  * how does the simplifier know which rule to apply?
    - it looks at the head symbol H of the term
    - collects all simp rules with head symbol H
    - matches each simp rule with the current term, i.e.
      here the transperency setting comes into play
    - rewrites using the first matching rule:
      conditional assumptions are proved using the discharger

  * problem: non terminating rewriting:

     a = b = a = b = a = ....

     f(a) = f(f a) = f (f (f a)) = ....

  * problem: head symbol needs to be a constant:

    ∀f, is_group_hom f → f (a + b) = f a + f b

    doesn't work as a simp rule

  * the interface:

    simp [r₁, r₂, …]

    simp * at *

    simp [*, r₁, r₂, …]

    simp [-r], simp only [r₁, r₂, …]

    If you add a constant `c` instead of a rule `r : l = r`, then the defining equations are added

  * rule preprocessing:

    ¬ a   ⟹  a ↔ false
    a ≠ b ⟹  (a = b) ↔ false

Type Dependence Problem:

  `f : Πn:ℕ, vector n ℕ`

  `p (f a)` ~> here `f` and `p` can be rewritten arbitrarily, but if we rewrite `a` we also need
  to change `p` (and its type)!

  (Note: `rw` sometimes works in this case as by default it rewrites *all* occurences of `a`, so
    also the one in `p`).

-/

example {α : Type*} {a b c : α} (f : α → α) (hac : a = c) (hfa : f a = b) :
  f a = b :=
begin
  simp [hac, hfa], -- doesn't work as first `f a = f c` by `hac`
end

/- How to setup simp rules -/

/- Example: (non-commutative) groups

Think about *normalizing* behaviour:

  does the theory have a normal form? For example for groups:

    (-a + -b) + -c

  and remove all zeros:

    0 + a = a
    a + 0 = a

  replace - by plus:
    a - b = a + -b

  normalize under -:
    - 0 = 0
    - (a + b) = -a + -b
    - (a - b) = -a + b
    - (- a) = a

  normalize +:
    a + (b + c) = (a + b) + c

  cancel:
    a + -a = 0
    -a + a = 0
    a + (-a + b) = b
    -a + (a + b) = b

This breaks down for commutative groups, there we need a special tactic to find two inverse terms,
reorders and cancels them.

-/

/- Example: Morphisms

  f (x + y) = f x + f y

  f 0 = 0

-/

/- Normal forms:

The right-hand side is not always shorter, but should be smaller in terms of some relation.

  a * (b + c)  = a * b + c * b

Is a possible rule (`+` < `*` is generally prefered) but results also in an explosion of the term,
should be activated by the user case by case.

-/


/- Logic by rewriting

  true ∧ a       = a

  a ∧ ∃x, f x    =  ∃x, a ∧ f x

  (∃x, f x) → p  =  ∀x, f x → p

-/

/- simp rules:

Write rules generic:

  bad:    x ^ (n + 1) = x ^ n * x

  good:   x ^ 1 = x
          x ^ (n + m) = x ^ n * x ^ m

General rule: `l = r`
  * have as much variables in `l` as possible
  * reduce them in `r`
  * `l` should be already in rewritten form
  * also: all variables in `r`, and in your assumptions need to occur already in `l`
    (with the exception of type class instances)

take care of decidability:

  [decidable p] [decidable (λx, ¬ p x)] -- sometimes necessary




-/
