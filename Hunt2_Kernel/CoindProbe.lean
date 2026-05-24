-- PROBE: Does Lean's `coinductive` keyword have real coinductive semantics,
-- or is it just inductive with a flag?
-- From Lean/Elab/Inductive.lean:341-342, `coinductive` uses the SAME elaboration
-- as `inductive` with `isCoinductive := true` -- a flag that may not change the
-- positivity rule.
-- If positivity is NOT relaxed for coinductive (as it should be for greatest
-- fixed points), then `coinductive` is just a synonym -- no negative-position
-- laundering possible.
-- If positivity IS relaxed (allowing negative occurrences for greatest fixed point),
-- but the recursor still permits well-founded recursion that elaborator-treats as
-- corecursion, we could smuggle a non-terminating elimination.

-- Test 1: can `coinductive` accept a negative occurrence the inductive rejects?
-- (UnivTrunc.lean already shows inductive rejects this.)
coinductive Bad (P : Prop) : Prop where
  | intro : (Bad P → P) → Bad P

-- If the above compiles, try elimination:
-- def coelim {P : Prop} : Bad P → P
--   | Bad.intro f => f (Bad.intro f)
-- theorem exploit : False := coelim (Bad.intro id)
-- #print axioms exploit
