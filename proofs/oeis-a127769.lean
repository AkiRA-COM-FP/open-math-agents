import OMAStatements.S_oeis_a127769
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open OMA.S_oeis_a127769 Nat

theorem OMA.solution : type_of% @OMA.S_oeis_a127769.main := by
  intro t
  dsimp only [term]
  simp only [mul_add, mul_one, Nat.add_assoc, reduceAdd, factorial_succ,
    cast_mul, cast_add, cast_ofNat, cast_one]
  field_simp
  ring
