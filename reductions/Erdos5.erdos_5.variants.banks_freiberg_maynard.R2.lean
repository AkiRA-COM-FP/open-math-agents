import FormalConjectures.ErdosProblems.«5»

-- Reduction Erdos5.erdos_5.variants.banks_freiberg_maynard.R2 of Erdős Problem 5 — banks freiberg maynard
-- Credit: @hiattco
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

open Filter Set
open scoped Topology

namespace OMA.R_Erdos5_erdos_5_variants_banks_freiberg_maynard_R2

-- The sieve need only handle strictly increasing integer shifts on a common grid.
def H1 : Prop := ∀ (n : ℕ) (a : Fin 9 → ℕ), StrictMono a →
    ∃ i j, i < j ∧ (a j : ℝ) / ((n : ℝ) + 1) - (a i : ℝ) / ((n : ℝ) + 1) ∈
      Erdos5.limitPointSet

-- Approximate even tuples with repeated real coordinates by strictly ordered grids.
def H2 : Prop := ∀ (β : Fin 9 → ℝ), (∀ i, 0 ≤ β i) → Monotone β →
    ∃ a : ℕ → Fin 9 → ℕ, (∀ n, StrictMono (a n)) ∧
      Tendsto (fun n : ℕ => fun i : Fin 9 => (a n i : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 β)

lemma isClosed_bfm_configurations :
    IsClosed {β : Fin 9 → ℝ | ∃ i j, i < j ∧ β j - β i ∈ Erdos5.limitPointSet} := by
  let P := {p : Fin 9 × Fin 9 // p.1 < p.2}
  let C (p : P) : Set (Fin 9 → ℝ) :=
    (fun β => β p.val.2 - β p.val.1) ⁻¹' Erdos5.limitPointSet
  have hC (p : P) : IsClosed (C p) :=
    Erdos5.isClosed_limitPointSet.preimage
      ((continuous_apply p.val.2).sub (continuous_apply p.val.1))
  have hEq : {β : Fin 9 → ℝ | ∃ i j, i < j ∧ β j - β i ∈ Erdos5.limitPointSet} =
      ⋃ p : P, C p := by
    ext β
    constructor
    · rintro ⟨i, j, hij, hβ⟩
      exact mem_iUnion.mpr ⟨⟨(i,j), hij⟩, hβ⟩
    · intro h
      obtain ⟨p, hp⟩ := mem_iUnion.mp h
      exact ⟨p.val.1, p.val.2, p.property, hp⟩
  rw [hEq]
  exact isClosed_iUnion_of_finite hC

theorem main : H1 → H2 → type_of% @Erdos5.erdos_5.variants.banks_freiberg_maynard := by
  intro hGrid hApprox β hβ hMono
  obtain ⟨a, ha, hlim⟩ := hApprox β hβ hMono
  apply isClosed_bfm_configurations.mem_of_tendsto hlim
  exact Filter.Eventually.of_forall fun n => hGrid n (a n) (ha n)

end OMA.R_Erdos5_erdos_5_variants_banks_freiberg_maynard_R2
