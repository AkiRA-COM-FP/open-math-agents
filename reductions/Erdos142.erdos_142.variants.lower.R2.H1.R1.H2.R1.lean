import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1
import Mathlib

/-!
# Summable extremal densities from the quasipolynomial bound

The target is step H2 of reduction R2.H1.R1 of Erdős 142: for every length k at least four the
normalized extremal numbers r_k(4^j) / 4^j are summable. With the steps already proved this is
the only open leaf on the route R2 to the variant r_k(N) = o(N / log N).

H1 is the published quantitative density theorem, in exactly the shape of
OAI.Erdos3.QuantitativeDensityBound (openai/math, Results/Conclusions.lean, theorem
manuscriptQuantitativeDensityTheorem), with the extremal number written as Erdos142.r and
restricted to lengths at least four. It is the one piece that needs the external proof.

H2 is a self-contained statement of real analysis with no arithmetic progressions in it: the
saving exp(-c (log log N)^(1+η)) is summable along the scales N = 4^j. For large j the term is
at most j^(-2), because log (log (4^j)) is at least log j and (log j)^η grows without bound.

The glue below is a comparison of series: divide the bound of H1 at N = 4^(j+1) by 4^(j+1).
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1

open Erdos142 Filter

/-- The quasipolynomial bound for every progression length at least four. -/
def H1 : Prop :=
  ∀ k : ℕ, 4 ≤ k → ∃ C c η : ℝ, 0 < C ∧ 0 < c ∧ 0 < η ∧
    ∀ N : ℕ, 3 ≤ N →
      (r k N : ℝ) ≤ C * N * Real.exp (-c * (Real.log (Real.log N)) ^ (1 + η))

/-- The saving is summable along the scales 4^j. -/
def H2 : Prop :=
  ∀ c η : ℝ, 0 < c → 0 < η →
    Summable (fun j : ℕ ↦ Real.exp (-c * (Real.log (Real.log ((4 : ℝ) ^ j))) ^ (1 + η)))

theorem main : H1 → H2 → OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1.H2 := by
  intro h1 h2 k hk
  obtain ⟨C, c, η, hC, hc, hη, hb⟩ := h1 k hk
  have hs : Summable (fun j : ℕ ↦
      C * Real.exp (-c * (Real.log (Real.log ((4 : ℝ) ^ j))) ^ (1 + η))) :=
    (h2 c η hc hη).mul_left C
  have hs' : Summable (fun j : ℕ ↦
      C * Real.exp (-c * (Real.log (Real.log ((4 : ℝ) ^ (j + 1)))) ^ (1 + η))) :=
    (summable_nat_add_iff 1).mpr hs
  have key : ∀ j : ℕ, (r k (4 ^ (j + 1)) : ℝ) / (4 : ℝ) ^ (j + 1) ≤
      C * Real.exp (-c * (Real.log (Real.log ((4 : ℝ) ^ (j + 1)))) ^ (1 + η)) := by
    intro j
    have h3 : 3 ≤ 4 ^ (j + 1) :=
      calc 3 ≤ 4 ^ 1 := by norm_num
        _ ≤ 4 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hb' := hb (4 ^ (j + 1)) h3
    push_cast at hb'
    have hpos : (0 : ℝ) < (4 : ℝ) ^ (j + 1) := by positivity
    rw [div_le_iff₀ hpos]
    calc (r k (4 ^ (j + 1)) : ℝ)
        ≤ C * (4 : ℝ) ^ (j + 1) *
            Real.exp (-c * (Real.log (Real.log ((4 : ℝ) ^ (j + 1)))) ^ (1 + η)) := hb'
      _ = C * Real.exp (-c * (Real.log (Real.log ((4 : ℝ) ^ (j + 1)))) ^ (1 + η)) *
            (4 : ℝ) ^ (j + 1) := by ring
  have hshift : Summable (fun j : ℕ ↦ (r k (4 ^ (j + 1)) : ℝ) / (4 : ℝ) ^ (j + 1)) :=
    Summable.of_nonneg_of_le (fun j ↦ by positivity) key hs'
  exact (summable_nat_add_iff 1).mp hshift

end OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1
