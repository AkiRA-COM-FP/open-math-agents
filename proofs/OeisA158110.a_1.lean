import FormalConjectures.OEIS.«158110»

/-! The first-coefficient formula for powers eliminates every substitution term except the linear one. -/

open OeisA158110 PowerSeries in
theorem OMA.solution : type_of% @OeisA158110.a_1 := by
  change coeff 1 (subst _ (exp ℚ)) = 2
  rw [coeff_subst' (HasSubst.of_constantCoeff_zero' (by simp [logSeries]))]
  rw [finsum_eq_single _ 1]
  · simp [coeff_exp, logSeries, coeff_mk]
  · intro d hd
    cases d with
    | zero => simp
    | succ d =>
      have : d ≠ 0 := by omega
      simp [coeff_one_pow, logSeries, this]
