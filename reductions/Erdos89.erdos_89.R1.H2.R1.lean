import OMAReductions.R_Erdos89_erdos_89_R1

-- Reduction of Erdos89.erdos_89.R1.H2. Credit: @wispiANt
open Filter EuclideanGeometry

namespace OMA.R_Erdos89_erdos_89_R1_H2_R1

/-- Uniform counting on planar lattices whose Gram matrix is rational up to scale.
The coefficients and the shape of the finite subset may vary with its size. -/
def H1 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ a b c : ℤ, 0 < a → b^2 < 4*a*c →
    ∀ S : Finset (ℤ × ℤ), N ≤ S.card →
      let q := fun z : ℤ × ℤ => a*z.1^2 + b*z.1*z.2 + c*z.2^2
      (S.card : ℝ) ≤ C * Real.sqrt (Real.log S.card) *
        ((S.offDiag.image fun xy => q (xy.1 - xy.2)).card : ℝ)

/-- Extremal comparison. A positive fraction of the points can be matched by
an integer configuration under some positive definite integral form, within the
original budget of distinct distances. Only cardinalities are compared. -/
def H2 : Prop :=
  ∃ K : ℕ, 0 < K ∧ ∃ N₀ : ℕ,
    ∀ P : Finset {p : ℝ² // ∀ i : Fin 2, IsIntegral ℤ (p i)}, N₀ ≤ P.card →
      ∃ a b c : ℤ, 0 < a ∧ b^2 < 4*a*c ∧ ∃ S : Finset (ℤ × ℤ),
        S.card ≤ P.card ∧ P.card ≤ K * S.card ∧
        let q := fun z : ℤ × ℤ => a*z.1^2 + b*z.1*z.2 + c*z.2^2
        (S.offDiag.image fun xy => q (xy.1 - xy.2)).card ≤ distinctDistances P

theorem main : H1 → H2 → OMA.R_Erdos89_erdos_89_R1.H2 := by
  classical
  rintro ⟨C, hC, N, hcount⟩ ⟨K, hK, N₀, hcompare⟩
  let X := {p : ℝ² // ∀ i : Fin 2, IsIntegral ℤ (p i)}
  let f (j : ℕ) : X := ⟨EuclideanSpace.single 0 (j : ℝ), by
    intro i
    fin_cases i <;> simp <;> first | exact isIntegral_natCast .. | exact isIntegral_zero⟩
  have : Infinite X := Infinite.of_injective f (by
    intro i j hij
    simpa [f] using congrArg (fun p : X => p.val 0) hij)
  apply Asymptotics.IsBigO.of_bound ((K : ℝ) * C)
  filter_upwards [eventually_ge_atTop (max N₀ (K * (N + 2) + 2))] with n hn
  obtain ⟨P₀, h₀⟩ := Infinite.exists_subset_card_eq X n
  obtain ⟨P, hP, hD⟩ := Nat.sInf_mem (show
    {d : ℕ | ∃ P : Finset X, P.card = n ∧ distinctDistances P = d}.Nonempty
    from ⟨_, P₀, h₀, rfl⟩)
  change distinctDistances P = minimalDistinctDistances X n at hD
  obtain ⟨a, b, c, ha, hd, S, hs, hsize, hbudget⟩ :=
    hcompare P (hP ▸ (le_max_left _ _).trans hn)
  rw [hP] at hs hsize
  have hlarge := (le_max_right _ _).trans hn
  have hmin : N + 2 ≤ S.card := by
    exact Nat.le_of_mul_le_mul_left (by omega : K * (N+2) ≤ K * S.card) hK
  have harith := hcount a b c ha hd S (by omega)
  dsimp only at harith hbudget
  have hlog : Real.sqrt (Real.log S.card) ≤ Real.sqrt (Real.log n) :=
    Real.sqrt_le_sqrt (Real.log_le_log (by exact_mod_cast (by omega : 0 < S.card))
      (by exact_mod_cast hs))
  have hn' : 1 < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
  have hpos := Real.sqrt_pos.2 (Real.log_pos hn')
  change ‖(n : ℝ) / Real.sqrt (Real.log n)‖ ≤
    (K : ℝ) * C * ‖(minimalDistinctDistances X n : ℝ)‖
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.norm_eq_abs, Nat.abs_cast,
    div_le_iff₀ hpos]
  calc
    (n : ℝ) ≤ (K : ℝ) * S.card := by exact_mod_cast hsize
    _ ≤ (K : ℝ) * (C * Real.sqrt (Real.log S.card) * _) :=
      mul_le_mul_of_nonneg_left harith (by positivity)
    _ ≤ (K : ℝ) * (C * Real.sqrt (Real.log n) * (distinctDistances P : ℝ)) := by
      gcongr
    _ = _ := by rw [hD]; ring

end OMA.R_Erdos89_erdos_89_R1_H2_R1
