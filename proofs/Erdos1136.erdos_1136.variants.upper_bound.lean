import FormalConjectures.ErdosProblems.«1136»

open Set Finset
/-! Pair each selected integer with its unselected complement to a power of two. -/

open Filter

theorem OMA.solution : type_of% @Erdos1136.erdos_1136.variants.upper_bound := by
  classical
  intro A hA
  have hpartial (k : ℕ) : A.partialDensity univ (2 ^ k + 1) ≤ 1 / 2 := by
    let U := range (2 ^ k + 1)
    let S := U.filter (· ∈ A)
    have hsub : S ⊆ U := filter_subset _ _
    have hpair : S.card ≤ (U \ S).card := by
      apply card_le_card_of_injOn (fun a => 2 ^ k - a)
      · intro a ha
        obtain ⟨haU, haA⟩ := mem_filter.mp ha
        have haU' := mem_range.mp haU
        exact mem_sdiff.mpr
          ⟨mem_range.mpr (Nat.lt_succ_of_le (Nat.sub_le _ _)),
            fun hb => hA a haA _ (mem_filter.mp hb).2 k (by
              change a + (2 ^ k - a) = 2 ^ k
              omega)⟩
      · intro a ha b hb heq
        have := mem_range.mp (hsub ha)
        have := mem_range.mp (hsub hb)
        change 2 ^ k - a = 2 ^ k - b at heq
        omega
    rw [card_sdiff_of_subset hsub, card_range] at hpair
    have hcoe : (S : Set ℕ) = A ∩ Iio (2 ^ k + 1) := by
      ext a
      simp [S, U, and_comm]
    simp only [partialDensity, inter_univ, univ_inter, ← hcoe,
      ncard_coe_finset, ncard_Iio_nat]
    apply (div_le_iff₀ (by positivity)).mpr
    have hsize : (2 : ℝ) * S.card ≤ ((2 ^ k + 1 : ℕ) : ℝ) := by
      have hpow : (0 : ℕ) < 2 ^ k := by positivity
      exact_mod_cast (show 2 * S.card ≤ 2 ^ k + 1 by omega)
    linarith
  rw [lowerDensity, Filter.liminf_eq]
  apply Real.sSup_le _ (by norm_num)
  intro d hd
  obtain ⟨b, hb⟩ := eventually_atTop.mp hd
  exact (hb _ (b.lt_two_pow_self.le.trans (Nat.le_succ _))).trans (hpartial b)
