import OMAStatements.S_oeis_a226896

-- Problem: A226896: reciprocal harmonic-number error limit
-- Upstream: statements/oeis-a226896.lean (declaration OMA.S_oeis_a226896.main)
-- Credit: @cgaray

open Filter Topology Real

namespace OMA_oeis_a226896

private lemma log_sub_rat_lower (t : ℝ) (ht : 0 ≤ t) :
    t ^ 2 / 2 - 2 * t ^ 3 / 3 ≤ Real.log (1 + t) - t / (1 + t) := by
  let f : ℝ → ℝ := fun x => Real.log (1 + x) - x / (1 + x) - (x ^ 2 / 2 - 2 * x ^ 3 / 3)
  have hf_diff : ∀ x ∈ Set.Ici (0 : ℝ), HasDerivAt f (x ^ 3 * (3 + 2 * x) / (1 + x) ^ 2) x := by
    intro x hx
    have h1 : (1 : ℝ) + x ≠ 0 := by linarith [Set.mem_Ici.mp hx]
    have d1 : HasDerivAt (fun x : ℝ => Real.log (1 + x)) (1 / (1 + x)) x := by
      have := ((hasDerivAt_id x).const_add 1).log h1
      simpa using this
    have d2 : HasDerivAt (fun x : ℝ => x / (1 + x)) ((1 * (1 + x) - x * 1) / (1 + x) ^ 2) x :=
      (hasDerivAt_id x).div ((hasDerivAt_id x).const_add 1) h1
    have d3 : HasDerivAt (fun x : ℝ => x ^ 2 / 2) (((2 : ℕ) * x ^ (2 - 1)) / 2) x :=
      (hasDerivAt_pow 2 x).div_const 2
    have d4 : HasDerivAt (fun x : ℝ => 2 * x ^ 3 / 3) ((2 * ((3 : ℕ) * x ^ (3 - 1))) / 3) x :=
      ((hasDerivAt_pow 3 x).const_mul 2).div_const 3
    have d : HasDerivAt f
        ((1 / (1 + x) - (1 * (1 + x) - x * 1) / (1 + x) ^ 2) -
          (((2 : ℕ) * x ^ (2 - 1)) / 2 - (2 * ((3 : ℕ) * x ^ (3 - 1))) / 3)) x :=
      (d1.sub d2).sub (d3.sub d4)
    have hval : (1 / (1 + x) - (1 * (1 + x) - x * 1) / (1 + x) ^ 2) -
        (((2 : ℕ) * x ^ (2 - 1)) / 2 - (2 * ((3 : ℕ) * x ^ (3 - 1))) / 3) =
        x ^ 3 * (3 + 2 * x) / (1 + x) ^ 2 := by
      norm_num
      field_simp [h1]
      ring
    rwa [hval] at d
  have hf_mono : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun x hx => (hf_diff x hx).continuousAt.continuousWithinAt
    · exact fun x hx => (hf_diff x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx0 : 0 ≤ x := interior_subset hx
      rw [(hf_diff x hx0).deriv]
      positivity
  have h0 : f 0 ≤ f t := hf_mono (Set.mem_Ici.mpr le_rfl) ht ht
  have hf0 : f 0 = 0 := by simp [f]
  rw [hf0] at h0
  dsimp only [f] at h0
  linarith

private lemma log_sub_rat_upper (t : ℝ) (ht : 0 ≤ t) :
    Real.log (1 + t) - t / (1 + t) ≤ t ^ 2 / 2 - 2 * t ^ 3 / 3 + 3 * t ^ 4 / 4 := by
  let f : ℝ → ℝ := fun x => (x ^ 2 / 2 - 2 * x ^ 3 / 3 + 3 * x ^ 4 / 4) - (Real.log (1 + x) - x / (1 + x))
  have hf_diff : ∀ x ∈ Set.Ici (0 : ℝ), HasDerivAt f (x ^ 4 * (4 + 3 * x) / (1 + x) ^ 2) x := by
    intro x hx
    have h1 : (1 : ℝ) + x ≠ 0 := by linarith [Set.mem_Ici.mp hx]
    have d1 : HasDerivAt (fun x : ℝ => Real.log (1 + x)) (1 / (1 + x)) x := by
      have := ((hasDerivAt_id x).const_add 1).log h1
      simpa using this
    have d2 : HasDerivAt (fun x : ℝ => x / (1 + x)) ((1 * (1 + x) - x * 1) / (1 + x) ^ 2) x :=
      (hasDerivAt_id x).div ((hasDerivAt_id x).const_add 1) h1
    have d3 : HasDerivAt (fun x : ℝ => x ^ 2 / 2) (((2 : ℕ) * x ^ (2 - 1)) / 2) x :=
      (hasDerivAt_pow 2 x).div_const 2
    have d4 : HasDerivAt (fun x : ℝ => 2 * x ^ 3 / 3) ((2 * ((3 : ℕ) * x ^ (3 - 1))) / 3) x :=
      ((hasDerivAt_pow 3 x).const_mul 2).div_const 3
    have d5 : HasDerivAt (fun x : ℝ => 3 * x ^ 4 / 4) ((3 * ((4 : ℕ) * x ^ (4 - 1))) / 4) x :=
      ((hasDerivAt_pow 4 x).const_mul 3).div_const 4
    have d : HasDerivAt f
        (((((2 : ℕ) * x ^ (2 - 1)) / 2 - (2 * ((3 : ℕ) * x ^ (3 - 1))) / 3) +
          (3 * ((4 : ℕ) * x ^ (4 - 1))) / 4) -
          (1 / (1 + x) - (1 * (1 + x) - x * 1) / (1 + x) ^ 2)) x :=
      ((d3.sub d4).add d5).sub (d1.sub d2)
    have hval : ((((2 : ℕ) * x ^ (2 - 1)) / 2 - (2 * ((3 : ℕ) * x ^ (3 - 1))) / 3) +
          (3 * ((4 : ℕ) * x ^ (4 - 1))) / 4) -
        (1 / (1 + x) - (1 * (1 + x) - x * 1) / (1 + x) ^ 2) =
        x ^ 4 * (4 + 3 * x) / (1 + x) ^ 2 := by
      norm_num
      field_simp [h1]
      ring
    rwa [hval] at d
  have hf_mono : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun x hx => (hf_diff x hx).continuousAt.continuousWithinAt
    · exact fun x hx => (hf_diff x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx0 : 0 ≤ x := interior_subset hx
      rw [(hf_diff x hx0).deriv]
      positivity
  have h0 : f 0 ≤ f t := hf_mono (Set.mem_Ici.mpr le_rfl) ht ht
  have hf0 : f 0 = 0 := by simp [f]
  rw [hf0] at h0
  dsimp only [f] at h0
  linarith

noncomputable def dseq (n : ℕ) : ℝ :=
  (harmonic n : ℝ) - Real.eulerMascheroniConstant - Real.log n

noncomputable def gMinus (n : ℕ) : ℝ :=
  1 / (2 * (n : ℝ)) - 1 / (12 * (n : ℝ) ^ 2) - 1 / (n : ℝ) ^ 3

noncomputable def gPlus (n : ℕ) : ℝ :=
  1 / (2 * (n : ℝ)) - 1 / (12 * (n : ℝ) ^ 2) + 1 / (n : ℝ) ^ 3

private lemma dseq_step (k : ℕ) (hk : 1 ≤ k) :
    dseq k - dseq (k + 1) = Real.log (1 + 1 / (k : ℝ)) - (1 / (k : ℝ)) / (1 + 1 / (k : ℝ)) := by
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hk1_pos : (0 : ℝ) < (k : ℝ) + 1 := by linarith
  have hharm : (harmonic (k + 1) : ℝ) = (harmonic k : ℝ) + 1 / ((k : ℝ) + 1) := by
    rw [harmonic_succ]
    push_cast
    ring
  have hlog : Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ) = Real.log (1 + 1 / (k : ℝ)) := by
    push_cast
    rw [← Real.log_div (ne_of_gt hk1_pos) (ne_of_gt hk_pos)]
    congr 1
    field_simp
  have hrat : (1 / (k : ℝ)) / (1 + 1 / (k : ℝ)) = 1 / ((k : ℝ) + 1) := by
    field_simp
  simp only [dseq, hharm]
  linarith

private lemma step_lower (k : ℕ) (hk : 1 ≤ k) :
    gMinus k - gMinus (k + 1) ≤ dseq k - dseq (k + 1) := by
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
  have ht : 0 ≤ 1 / (k : ℝ) := by positivity
  rw [dseq_step k hk]
  have h1 := log_sub_rat_lower (1 / (k : ℝ)) ht
  refine le_trans ?_ h1
  simp only [gMinus, Nat.cast_add, Nat.cast_one]
  rw [sub_le_iff_le_add]
  have hnum : 0 ≤ ((1 / (k : ℝ)) ^ 2 / 2 - 2 * (1 / (k : ℝ)) ^ 3 / 3) -
      ((1 / (2 * (k : ℝ)) - 1 / (12 * (k : ℝ) ^ 2) - 1 / (k : ℝ) ^ 3) -
       (1 / (2 * ((k : ℝ) + 1)) - 1 / (12 * ((k : ℝ) + 1) ^ 2) - 1 / ((k : ℝ) + 1) ^ 3)) := by
    have hdiff : ((1 / (k : ℝ)) ^ 2 / 2 - 2 * (1 / (k : ℝ)) ^ 3 / 3) -
        ((1 / (2 * (k : ℝ)) - 1 / (12 * (k : ℝ) ^ 2) - 1 / (k : ℝ) ^ 3) -
         (1 / (2 * ((k : ℝ) + 1)) - 1 / (12 * ((k : ℝ) + 1) ^ 2) - 1 / ((k : ℝ) + 1) ^ 3)) =
        (27 * (k : ℝ) ^ 2 + 19 * (k : ℝ) + 4) / (12 * (k : ℝ) ^ 3 * ((k : ℝ) + 1) ^ 3) := by
      field_simp
      ring
    rw [hdiff]
    positivity
  linarith

private lemma step_upper (k : ℕ) (hk : 1 ≤ k) :
    dseq k - dseq (k + 1) ≤ gPlus k - gPlus (k + 1) := by
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have ht : 0 ≤ 1 / (k : ℝ) := by positivity
  rw [dseq_step k hk]
  have h1 := log_sub_rat_upper (1 / (k : ℝ)) ht
  refine le_trans h1 ?_
  simp only [gPlus, Nat.cast_add, Nat.cast_one]
  have hnum : 0 ≤ ((1 / (2 * (k : ℝ)) - 1 / (12 * (k : ℝ) ^ 2) + 1 / (k : ℝ) ^ 3) -
       (1 / (2 * ((k : ℝ) + 1)) - 1 / (12 * ((k : ℝ) + 1) ^ 2) + 1 / ((k : ℝ) + 1) ^ 3)) -
      ((1 / (k : ℝ)) ^ 2 / 2 - 2 * (1 / (k : ℝ)) ^ 3 / 3 + 3 * (1 / (k : ℝ)) ^ 4 / 4) := by
    have hdiff : ((1 / (2 * (k : ℝ)) - 1 / (12 * (k : ℝ) ^ 2) + 1 / (k : ℝ) ^ 3) -
         (1 / (2 * ((k : ℝ) + 1)) - 1 / (12 * ((k : ℝ) + 1) ^ 2) + 1 / ((k : ℝ) + 1) ^ 3)) -
        ((1 / (k : ℝ)) ^ 2 / 2 - 2 * (1 / (k : ℝ)) ^ 3 / 3 + 3 * (1 / (k : ℝ)) ^ 4 / 4) =
        (36 * (k : ℝ) ^ 3 + 26 * (k : ℝ) ^ 2 - 7 * (k : ℝ) - 9) /
          (12 * (k : ℝ) ^ 4 * ((k : ℝ) + 1) ^ 3) := by
      field_simp
      ring
    rw [hdiff]
    have hpoly : 0 ≤ 36 * (k : ℝ) ^ 3 + 26 * (k : ℝ) ^ 2 - 7 * (k : ℝ) - 9 := by nlinarith
    positivity
  linarith

lemma dseq_bounds (n : ℕ) (hn : 1 ≤ n) :
    gMinus n ≤ dseq n ∧ dseq n ≤ gPlus n := by
  have htel_lo : ∀ m : ℕ, gMinus n - gMinus (n + m) ≤ dseq n - dseq (n + m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hst := step_lower (n + m) (by omega)
      have hrew : n + (m + 1) = n + m + 1 := by omega
      rw [hrew]
      linarith
  have htel_hi : ∀ m : ℕ, dseq n - dseq (n + m) ≤ gPlus n - gPlus (n + m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hst := step_upper (n + m) (by omega)
      have hrew : n + (m + 1) = n + m + 1 := by omega
      rw [hrew]
      linarith
  have hd_tendsto : Tendsto dseq atTop (𝓝 0) := by
    have h := Real.tendsto_harmonic_sub_log.sub_const Real.eulerMascheroniConstant
    simp only [sub_self] at h
    refine h.congr (fun k => ?_)
    simp only [dseq]
    ring
  have hinv_tendsto : Tendsto (fun k : ℕ => (1 : ℝ) / (k : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 1
  have hgm_tendsto : Tendsto gMinus atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => (1 / 2 : ℝ) * (1 / (k : ℝ))) atTop (𝓝 0) := by
      simpa using hinv_tendsto.const_mul (1 / 2 : ℝ)
    have h2 : Tendsto (fun k : ℕ => (1 / 12 : ℝ) * (1 / (k : ℝ)) ^ 2) atTop (𝓝 0) := by
      simpa using (hinv_tendsto.pow 2).const_mul (1 / 12 : ℝ)
    have h3 : Tendsto (fun k : ℕ => (1 / (k : ℝ)) ^ 3) atTop (𝓝 0) := by
      simpa using hinv_tendsto.pow 3
    have hcomb : Tendsto (fun k : ℕ =>
        (1 / 2 : ℝ) * (1 / (k : ℝ)) - (1 / 12 : ℝ) * (1 / (k : ℝ)) ^ 2 - (1 / (k : ℝ)) ^ 3)
        atTop (𝓝 0) := by
      simpa using (h1.sub h2).sub h3
    refine hcomb.congr (fun k => ?_)
    simp only [gMinus]
    ring
  have hgp_tendsto : Tendsto gPlus atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => (1 / 2 : ℝ) * (1 / (k : ℝ))) atTop (𝓝 0) := by
      simpa using hinv_tendsto.const_mul (1 / 2 : ℝ)
    have h2 : Tendsto (fun k : ℕ => (1 / 12 : ℝ) * (1 / (k : ℝ)) ^ 2) atTop (𝓝 0) := by
      simpa using (hinv_tendsto.pow 2).const_mul (1 / 12 : ℝ)
    have h3 : Tendsto (fun k : ℕ => (1 / (k : ℝ)) ^ 3) atTop (𝓝 0) := by
      simpa using hinv_tendsto.pow 3
    have hcomb : Tendsto (fun k : ℕ =>
        (1 / 2 : ℝ) * (1 / (k : ℝ)) - (1 / 12 : ℝ) * (1 / (k : ℝ)) ^ 2 + (1 / (k : ℝ)) ^ 3)
        atTop (𝓝 0) := by
      simpa using (h1.sub h2).add h3
    refine hcomb.congr (fun k => ?_)
    simp only [gPlus]
    ring
  have hshift : Tendsto (fun m : ℕ => n + m) atTop atTop :=
    tendsto_atTop_atTop.mpr (fun b => ⟨b, fun m hm => by omega⟩)
  have hlo : gMinus n ≤ dseq n := by
    have hL : Tendsto (fun m => gMinus n - gMinus (n + m)) atTop (𝓝 (gMinus n)) := by
      simpa using (tendsto_const_nhds.sub (hgm_tendsto.comp hshift))
    have hR : Tendsto (fun m => dseq n - dseq (n + m)) atTop (𝓝 (dseq n)) := by
      simpa using (tendsto_const_nhds.sub (hd_tendsto.comp hshift))
    exact le_of_tendsto_of_tendsto hL hR (Eventually.of_forall htel_lo)
  have hhi : dseq n ≤ gPlus n := by
    have hL : Tendsto (fun m => dseq n - dseq (n + m)) atTop (𝓝 (dseq n)) := by
      simpa using (tendsto_const_nhds.sub (hd_tendsto.comp hshift))
    have hR : Tendsto (fun m => gPlus n - gPlus (n + m)) atTop (𝓝 (gPlus n)) := by
      simpa using (tendsto_const_nhds.sub (hgp_tendsto.comp hshift))
    exact le_of_tendsto_of_tendsto hL hR (Eventually.of_forall htel_hi)
  exact ⟨hlo, hhi⟩

end OMA_oeis_a226896

theorem OMA.solution : type_of% @OMA.S_oeis_a226896.main := by
  have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 1
  have hlo_lim : Tendsto (fun n : ℕ => 1 / OMA_oeis_a226896.gPlus n - 2 * (n : ℝ))
      atTop (𝓝 ((1 : ℝ) / 3)) := by
    have hlim : Tendsto (fun n : ℕ =>
        ((1 : ℝ) / 3 - 4 * (1 / (n : ℝ))) /
        (1 - (1 / 6 : ℝ) * (1 / (n : ℝ)) + 2 * (1 / (n : ℝ)) ^ 2)) atTop (𝓝 ((1 : ℝ) / 3)) := by
      have hnum : Tendsto (fun n : ℕ => (1 : ℝ) / 3 - 4 * (1 / (n : ℝ))) atTop (𝓝 ((1 : ℝ) / 3)) := by
        simpa using (tendsto_const_nhds.sub (hinv.const_mul 4))
      have hden : Tendsto (fun n : ℕ =>
          1 - (1 / 6 : ℝ) * (1 / (n : ℝ)) + 2 * (1 / (n : ℝ)) ^ 2) atTop (𝓝 1) := by
        simpa using ((tendsto_const_nhds.sub (hinv.const_mul (1 / 6 : ℝ))).add
          ((hinv.pow 2).const_mul 2))
      have hdiv : Tendsto (fun n : ℕ =>
          ((1 : ℝ) / 3 - 4 * (1 / (n : ℝ))) /
          (1 - (1 / 6 : ℝ) * (1 / (n : ℝ)) + 2 * (1 / (n : ℝ)) ^ 2))
          atTop (𝓝 (((1 : ℝ) / 3) / 1)) := hnum.div hden one_ne_zero
      rwa [div_one] at hdiv
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop 4] with n hn
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
    have hq_pos : (0 : ℝ) < 6 * (n : ℝ) ^ 2 - (n : ℝ) + 12 := by nlinarith
    have hgp_eq : OMA_oeis_a226896.gPlus n = (6 * (n : ℝ) ^ 2 - (n : ℝ) + 12) / (12 * (n : ℝ) ^ 3) := by
      simp only [OMA_oeis_a226896.gPlus]
      field_simp
      ring
    rw [hgp_eq]
    have hd1 : (6 * (n : ℝ) ^ 2 - (n : ℝ) + 12 : ℝ) ≠ 0 := ne_of_gt hq_pos
    have hd2 : (1 - (1 / 6 : ℝ) * (1 / (n : ℝ)) + 2 * (1 / (n : ℝ)) ^ 2 : ℝ) =
        (6 * (n : ℝ) ^ 2 - (n : ℝ) + 12) / (6 * (n : ℝ) ^ 2) := by
      field_simp
      ring
    rw [hd2, div_div_eq_mul_div, one_div_div]
    rw [eq_sub_iff_add_eq]
    apply mul_right_cancel₀ hd1
    rw [add_mul, div_mul_cancel₀ _ hd1, div_mul_cancel₀ _ hd1]
    field_simp
    ring
  have hhi_lim : Tendsto (fun n : ℕ => 1 / OMA_oeis_a226896.gMinus n - 2 * (n : ℝ))
      atTop (𝓝 ((1 : ℝ) / 3)) := by
    have hlim : Tendsto (fun n : ℕ =>
        ((1 : ℝ) / 3 + 4 * (1 / (n : ℝ))) /
        (1 - (1 / 6 : ℝ) * (1 / (n : ℝ)) - 2 * (1 / (n : ℝ)) ^ 2)) atTop (𝓝 ((1 : ℝ) / 3)) := by
      have hnum : Tendsto (fun n : ℕ => (1 : ℝ) / 3 + 4 * (1 / (n : ℝ))) atTop (𝓝 ((1 : ℝ) / 3)) := by
        simpa using (tendsto_const_nhds.add (hinv.const_mul 4))
      have hden : Tendsto (fun n : ℕ =>
          1 - (1 / 6 : ℝ) * (1 / (n : ℝ)) - 2 * (1 / (n : ℝ)) ^ 2) atTop (𝓝 1) := by
        simpa using ((tendsto_const_nhds.sub (hinv.const_mul (1 / 6 : ℝ))).sub
          ((hinv.pow 2).const_mul 2))
      have hdiv : Tendsto (fun n : ℕ =>
          ((1 : ℝ) / 3 + 4 * (1 / (n : ℝ))) /
          (1 - (1 / 6 : ℝ) * (1 / (n : ℝ)) - 2 * (1 / (n : ℝ)) ^ 2))
          atTop (𝓝 (((1 : ℝ) / 3) / 1)) := hnum.div hden one_ne_zero
      rwa [div_one] at hdiv
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop 4] with n hn
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
    have hq_pos : (0 : ℝ) < 6 * (n : ℝ) ^ 2 - (n : ℝ) - 12 := by nlinarith
    have hgm_eq : OMA_oeis_a226896.gMinus n = (6 * (n : ℝ) ^ 2 - (n : ℝ) - 12) / (12 * (n : ℝ) ^ 3) := by
      simp only [OMA_oeis_a226896.gMinus]
      field_simp
      ring
    rw [hgm_eq]
    have hd1 : (6 * (n : ℝ) ^ 2 - (n : ℝ) - 12 : ℝ) ≠ 0 := ne_of_gt hq_pos
    have hd2 : (1 - (1 / 6 : ℝ) * (1 / (n : ℝ)) - 2 * (1 / (n : ℝ)) ^ 2 : ℝ) =
        (6 * (n : ℝ) ^ 2 - (n : ℝ) - 12) / (6 * (n : ℝ) ^ 2) := by
      field_simp
      ring
    rw [hd2, div_div_eq_mul_div, one_div_div]
    rw [eq_sub_iff_add_eq]
    apply mul_right_cancel₀ hd1
    rw [add_mul, div_mul_cancel₀ _ hd1, div_mul_cancel₀ _ hd1]
    field_simp
    ring
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo_lim hhi_lim ?_ ?_
  · filter_upwards [eventually_ge_atTop 4] with n hn
    have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
    have hn_pos : (0 : ℝ) < n := by linarith
    have ⟨hlo, hhi⟩ := OMA_oeis_a226896.dseq_bounds n (by omega)
    have hgm_pos : 0 < OMA_oeis_a226896.gMinus n := by
      simp only [OMA_oeis_a226896.gMinus]
      have : 1 / (2 * (n : ℝ)) - 1 / (12 * (n : ℝ) ^ 2) - 1 / (n : ℝ) ^ 3 =
          (6 * (n : ℝ) ^ 2 - (n : ℝ) - 12) / (12 * (n : ℝ) ^ 3) := by field_simp; ring
      rw [this]
      have : 0 < 6 * (n : ℝ) ^ 2 - (n : ℝ) - 12 := by nlinarith
      positivity
    have hd_pos : 0 < OMA_oeis_a226896.dseq n := lt_of_lt_of_le hgm_pos hlo
    have hdiv : 1 / OMA_oeis_a226896.gPlus n ≤ 1 / OMA_oeis_a226896.dseq n :=
      one_div_le_one_div_of_le hd_pos hhi
    simpa only [OMA_oeis_a226896.dseq] using sub_le_sub_right hdiv (2 * (n : ℝ))
  · filter_upwards [eventually_ge_atTop 4] with n hn
    have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
    have hn_pos : (0 : ℝ) < n := by linarith
    have ⟨hlo, _⟩ := OMA_oeis_a226896.dseq_bounds n (by omega)
    have hgm_pos : 0 < OMA_oeis_a226896.gMinus n := by
      simp only [OMA_oeis_a226896.gMinus]
      have : 1 / (2 * (n : ℝ)) - 1 / (12 * (n : ℝ) ^ 2) - 1 / (n : ℝ) ^ 3 =
          (6 * (n : ℝ) ^ 2 - (n : ℝ) - 12) / (12 * (n : ℝ) ^ 3) := by field_simp; ring
      rw [this]
      have : 0 < 6 * (n : ℝ) ^ 2 - (n : ℝ) - 12 := by nlinarith
      positivity
    have hdiv : 1 / OMA_oeis_a226896.dseq n ≤ 1 / OMA_oeis_a226896.gMinus n :=
      one_div_le_one_div_of_le hgm_pos hlo
    simpa only [OMA_oeis_a226896.dseq] using sub_le_sub_right hdiv (2 * (n : ℝ))
