import FormalConjectures.OEIS.«181084»

namespace OMA.Hanna
open PowerSeries
variable {L : ℚ⟦X⟧}

lemma high (h0 : coeff 0 L = 0) (m d : ℕ) (hd : m < d) : coeff m (L ^ d) = 0 := by
  have hX : X ∣ L := X_dvd_iff.mpr (by simpa using h0)
  have h := pow_dvd_pow_of_dvd hX d
  rw [X_pow_dvd_iff] at h
  exact h m hd

lemma key (h0 : coeff 0 L = 0) (m : ℕ) :
    coeff m (subst L (exp ℚ)) = ∑ d ∈ Finset.range (m + 1), coeff d (exp ℚ) • coeff m (L ^ d) := by
  rw [coeff_subst' (HasSubst.of_constantCoeff_zero' (by simpa using h0)),
    finsum_eq_sum_of_support_subset]
  intro d hd
  simp only [Function.mem_support, Finset.coe_range, Set.mem_Iio] at hd ⊢
  by_contra h
  exact hd (by simp [high h0 m d (by omega)])

lemma c22 (h0 : coeff 0 L = 0) : coeff 2 (L ^ 2) = coeff 1 L ^ 2 := by
  rw [pow_two, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ, h0]
  ring

lemma E2 (h0 : coeff 0 L = 0) : coeff 2 (subst L (exp ℚ)) = coeff 2 L + coeff 1 L ^ 2 / 2 := by
  rw [key h0]
  simp [Finset.sum_range_succ, coeff_exp, c22 h0, Nat.factorial]
  ring
end OMA.Hanna

open PowerSeries OeisA181084 in
theorem OMA.solution : type_of% @OeisA181084.a_2 := by
  show coeff 2 (subst _ (exp ℚ)) = _
  refine (OMA.Hanna.E2 ?_).trans ?_ <;> simp [hannaLog, coeff_mk, Finset.sum_Icc_succ_top] <;> norm_num [Nat.choose]
