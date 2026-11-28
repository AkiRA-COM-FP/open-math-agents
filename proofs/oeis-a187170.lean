import OMAStatements.S_oeis_a187170
import Mathlib.Tactic

/-! At widths at least 8, every translate count is a polynomial of degree
at most 3. Its finite difference of order 4 vanishes. The proof applies
this identity to each actual walk shape and checks the initial coefficients. -/

namespace LatticeWalk170
open OMA.S_oeis_a187170

abbrev bounded (w : Profile) := w.2.1 ≤ 8 ∧ w.2.2.1 ≤ 8 ∧ w.2.2.2 ≤ 8

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
lemma shapeBound : ∀ w ∈ shapes, bounded w := by
  have h : shapes.all (fun w => decide (bounded w)) = true := by decide +kernel
  intro w hw
  exact of_decide_eq_true (List.all_eq_true.mp h w hw)

lemma one (k : ℕ) (w : Profile) (ok : bounded w) : placed (k+12) w - 4*placed (k+11) w + 6*placed (k+10) w - 4*placed (k+9) w + placed (k+8) w = 0 := by
  obtain ⟨h0,h1,h2⟩ := ok
  simp (disch := omega) only [placed,Nat.cast_sub,Nat.cast_add,Nat.cast_ofNat]
  ring

lemma linearSum (k : ℕ) (xs : List Profile) (ok : ∀ w ∈ xs, bounded w) :
    (xs.map (placed (k+12))).sum - 4*(xs.map (placed (k+11))).sum + 6*(xs.map (placed (k+10))).sum - 4*(xs.map (placed (k+9))).sum + (xs.map (placed (k+8))).sum = 0 := by
  induction xs with
  | nil => simp
  | cons w xs ih =>
    have hw := one k w (ok w (by simp))
    have hx := ih (fun v hv => ok v (List.mem_cons_of_mem w hv))
    simp only [List.map_cons,List.sum_cons]
    linear_combination hw + hx

lemma recurrence (k : ℕ) : sequence (k+12) - 4*sequence (k+11) + 6*sequence (k+10) - 4*sequence (k+9) + sequence (k+8) = 0 :=
  linearSum k shapes shapeBound

set_option maxRecDepth 26000 in
set_option maxHeartbeats 3000000 in
lemma initial : ∀ n : Fin 12, lag 0 n.val - 4*lag 1 n.val + 6*lag 2 n.val - 4*lag 3 n.val + lag 4 n.val = numerator n.val := by
  decide +kernel

lemma gf (n : ℕ) : lag 0 n - 4*lag 1 n + 6*lag 2 n - 4*lag 3 n + lag 4 n = numerator n := by
  by_cases hn : n < 12
  · exact initial ⟨n,hn⟩
  · obtain ⟨k,rfl⟩ : ∃ k : ℕ, n = k+12 := ⟨n-12,by omega⟩
    change sequence (k+12) - 4*sequence (k+11) + 6*sequence (k+10) - 4*sequence (k+9) + sequence (k+8) = 0
    exact recurrence k

end LatticeWalk170

theorem OMA.solution : type_of% @OMA.S_oeis_a187170.main := by
  refine ⟨LatticeWalk170.gf, ?_⟩
  intro k
  linear_combination LatticeWalk170.recurrence k
