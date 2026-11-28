import OMAStatements.S_arxiv_1801_06737

-- Problem: At What Frequency Should the Kelly Bettor Bet? (arXiv:1801.06737), Conjecture 2.
-- Credit: @ricnov (the owner of the agent is credited as the solver)
--
-- Idea. Suppose the sufficient attractiveness inequality fails. Then the one-period problem has an
-- interior optimal fraction Ks, where the marginal growth E[X / (1 + Ks X)] vanishes (Fatou's lemma
-- and the intermediate value theorem). Holding a fraction K for two periods is the same as betting K
-- in the first period and the drifted fraction K (1 + X) / (1 + K X) in the second. A second-order
-- bound for the logarithm turns the distance of these two fractions from Ks into a loss of growth,
-- and the two distances cannot both be small unless the return is constant. So the optimal growth
-- with two periods between bets is strictly below the one-period optimum.

open MeasureTheory ProbabilityTheory

lemma OMA.log_second_order (u w b : ℝ) (hu : 0 < u) (hw : 0 < w) (hub : u ≤ b) (hwb : w ≤ b) :
    Real.log w ≤ Real.log u + (w - u) / u - (w - u) ^ 2 / (4 * b ^ 2) := by
  have hb : 0 < b := lt_of_lt_of_le hu hub
  obtain ⟨p, hp, rfl⟩ : ∃ p : ℝ, 0 < p ∧ p ^ 2 = u :=
    ⟨Real.sqrt u, Real.sqrt_pos.2 hu, Real.sq_sqrt hu.le⟩
  obtain ⟨q, hq, rfl⟩ : ∃ q : ℝ, 0 < q ∧ q ^ 2 = w :=
    ⟨Real.sqrt w, Real.sqrt_pos.2 hw, Real.sq_sqrt hw.le⟩
  have h1 : Real.log (q / p) ≤ q / p - 1 := Real.log_le_sub_one_of_pos (div_pos hq hp)
  rw [Real.log_div hq.ne' hp.ne'] at h1
  rw [Real.log_pow, Real.log_pow]
  have key : (q ^ 2 - p ^ 2) ^ 2 / (4 * b ^ 2) ≤ (q - p) ^ 2 / p ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have e : (q ^ 2 - p ^ 2) ^ 2 * p ^ 2 = (q - p) ^ 2 * (p ^ 2 * (q + p) ^ 2) := by ring
    rw [e]
    have h2 : p ^ 2 * (q + p) ^ 2 ≤ 4 * b ^ 2 := by
      have h3 : (q + p) ^ 2 ≤ 4 * b := by nlinarith [sq_nonneg (q - p)]
      nlinarith [sq_nonneg p, sq_nonneg (q + p)]
    nlinarith [sq_nonneg (q - p)]
  have e2 : (q ^ 2 - p ^ 2) / p ^ 2 - (q - p) ^ 2 / p ^ 2 = 2 * (q / p - 1) := by
    field_simp
    ring
  push_cast
  linarith

/-- For a fraction `0 ≤ K < 1` and a return `-1 ≤ x ≤ b - 1`, the wealth factor `1 + K x` lies in
`[1 - K, b]`. -/
lemma OMA.factor_bounds (K x b : ℝ) (hK0 : 0 ≤ K) (hK1 : K < 1) (hx : -1 ≤ x) (hxb : x ≤ b - 1)
    (hb : 1 ≤ b) : 1 - K ≤ 1 + K * x ∧ 1 + K * x ≤ b := by
  constructor
  · nlinarith [mul_nonneg hK0 (by linarith : (0 : ℝ) ≤ x + 1)]
  · nlinarith [mul_le_mul_of_nonneg_left hxb hK0,
      mul_nonneg (sub_nonneg.2 hK1.le) (sub_nonneg.2 hb)]

lemma OMA.one_period_pointwise (K Ks x b : ℝ) (hK0 : 0 ≤ K) (hK1 : K < 1) (hs0 : 0 ≤ Ks)
    (hs1 : Ks < 1) (hx : -1 ≤ x) (hxb : x ≤ b - 1) (hb : 1 ≤ b) :
    Real.log (1 + K * x) ≤ Real.log (1 + Ks * x) + (K - Ks) * (x / (1 + Ks * x))
      - (K - Ks) ^ 2 * x ^ 2 / (4 * b ^ 2) := by
  obtain ⟨h1, h2⟩ := OMA.factor_bounds K x b hK0 hK1 hx hxb hb
  obtain ⟨h3, h4⟩ := OMA.factor_bounds Ks x b hs0 hs1 hx hxb hb
  have h := OMA.log_second_order (1 + Ks * x) (1 + K * x) b (by linarith) (by linarith) h4 h2
  have e : (1 + K * x) - (1 + Ks * x) = (K - Ks) * x := by ring
  rw [e] at h
  have e2 : (K - Ks) * x / (1 + Ks * x) = (K - Ks) * (x / (1 + Ks * x)) := by ring
  have e3 : ((K - Ks) * x) ^ 2 = (K - Ks) ^ 2 * x ^ 2 := by ring
  rw [e2, e3] at h
  exact h

/-- The fraction of wealth at risk after one period of buy and hold. -/
noncomputable def OMA.kap (K x : ℝ) : ℝ := K * (1 + x) / (1 + K * x)

lemma OMA.kap_bounds (K x : ℝ) (hK0 : 0 ≤ K) (hK1 : K < 1) (hx : -1 ≤ x) :
    0 ≤ OMA.kap K x ∧ OMA.kap K x < 1 := by
  have h : 0 < 1 + K * x := by nlinarith [mul_nonneg hK0 (by linarith : (0 : ℝ) ≤ x + 1)]
  unfold OMA.kap
  constructor
  · exact div_nonneg (mul_nonneg hK0 (by linarith)) h.le
  · rw [div_lt_one h]
    nlinarith

lemma OMA.two_period_factor (K x0 x1 : ℝ) (hK0 : 0 ≤ K) (hK1 : K < 1) (hx0 : -1 ≤ x0) :
    1 + K * ((1 + x0) * (1 + x1) - 1) = (1 + K * x0) * (1 + OMA.kap K x0 * x1) := by
  have h : 0 < 1 + K * x0 := by nlinarith [mul_nonneg hK0 (by linarith : (0 : ℝ) ≤ x0 + 1)]
  unfold OMA.kap
  field_simp
  ring

lemma OMA.two_period_pointwise (K Ks x0 x1 b : ℝ) (hK0 : 0 ≤ K) (hK1 : K < 1) (hs0 : 0 ≤ Ks)
    (hs1 : Ks < 1) (hx0 : -1 ≤ x0) (hx0b : x0 ≤ b - 1) (hx1 : -1 ≤ x1) (hx1b : x1 ≤ b - 1)
    (hb : 1 ≤ b) :
    Real.log (1 + K * ((1 + x0) * (1 + x1) - 1)) ≤
      Real.log (1 + Ks * x0) + Real.log (1 + Ks * x1)
        + (K - Ks) * (x0 / (1 + Ks * x0)) + (OMA.kap K x0 - Ks) * (x1 / (1 + Ks * x1))
        - ((K - Ks) ^ 2 * x0 ^ 2 + (OMA.kap K x0 - Ks) ^ 2 * x1 ^ 2) / (4 * b ^ 2) := by
  obtain ⟨hk0, hk1⟩ := OMA.kap_bounds K x0 hK0 hK1 hx0
  have hA := OMA.one_period_pointwise K Ks x0 b hK0 hK1 hs0 hs1 hx0 hx0b hb
  have hB := OMA.one_period_pointwise (OMA.kap K x0) Ks x1 b hk0 hk1 hs0 hs1 hx1 hx1b hb
  obtain ⟨h1, -⟩ := OMA.factor_bounds K x0 b hK0 hK1 hx0 hx0b hb
  obtain ⟨h2, -⟩ := OMA.factor_bounds (OMA.kap K x0) x1 b hk0 hk1 hx1 hx1b hb
  rw [OMA.two_period_factor K x0 x1 hK0 hK1 hx0,
    Real.log_mul (by linarith) (by linarith)]
  have e : ((K - Ks) ^ 2 * x0 ^ 2 + (OMA.kap K x0 - Ks) ^ 2 * x1 ^ 2) / (4 * b ^ 2)
      = (K - Ks) ^ 2 * x0 ^ 2 / (4 * b ^ 2) + (OMA.kap K x0 - Ks) ^ 2 * x1 ^ 2 / (4 * b ^ 2) := by
    ring
  rw [e]
  linarith

/-- Either the fraction `K` or the drifted fraction is away from `Ks`. -/
lemma OMA.bracket_pointwise (K Ks x b : ℝ) (hK0 : 0 ≤ K) (hK1 : K < 1) (hx : -1 ≤ x)
    (hxb : x ≤ b - 1) (hb : 1 ≤ b) :
    K ^ 2 * (1 - K) ^ 2 * x ^ 2 / (2 * b ^ 2) ≤ (K - Ks) ^ 2 + (OMA.kap K x - Ks) ^ 2 := by
  obtain ⟨h1, h2⟩ := OMA.factor_bounds K x b hK0 hK1 hx hxb hb
  have hpos : 0 < 1 + K * x := by linarith
  have hb0 : 0 < b := by linarith
  have e : OMA.kap K x - K = K * (1 - K) * x / (1 + K * x) := by
    unfold OMA.kap
    field_simp
    ring
  have h3 : (OMA.kap K x - K) ^ 2 ≤ 2 * (K - Ks) ^ 2 + 2 * (OMA.kap K x - Ks) ^ 2 := by
    nlinarith [sq_nonneg (OMA.kap K x + K - 2 * Ks)]
  have h4 : K ^ 2 * (1 - K) ^ 2 * x ^ 2 / b ^ 2 ≤ (OMA.kap K x - K) ^ 2 := by
    rw [e, div_pow]
    have e5 : (K * (1 - K) * x) ^ 2 = K ^ 2 * (1 - K) ^ 2 * x ^ 2 := by ring
    rw [e5]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact pow_le_pow_left₀ hpos.le h2 2
  have e6 : K ^ 2 * (1 - K) ^ 2 * x ^ 2 / (2 * b ^ 2) = K ^ 2 * (1 - K) ^ 2 * x ^ 2 / b ^ 2 / 2 := by
    field_simp
  rw [e6]
  linarith

/-- Bounded measurable functions are integrable for a finite measure. -/
lemma OMA.intble {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P] (f : Ω → ℝ)
    (hf : Measurable f) (C : ℝ) (h : ∀ ω, |f ω| ≤ C) : Integrable f P :=
  Integrable.of_mem_Icc (-C) C hf.aemeasurable (Filter.Eventually.of_forall fun ω => abs_le.1 (h ω))

/-- The marginal growth rate `x / (1 + K x)` is bounded. -/
lemma OMA.ratio_bound (K x b : ℝ) (hK0 : 0 ≤ K) (hK1 : K < 1) (hx : -1 ≤ x) (hxb : x ≤ b - 1)
    (hb : 1 ≤ b) : |x / (1 + K * x)| ≤ b / (1 - K) := by
  obtain ⟨h1, -⟩ := OMA.factor_bounds K x b hK0 hK1 hx hxb hb
  have hpos : 0 < 1 + K * x := by linarith
  rw [abs_div, abs_of_pos hpos]
  exact div_le_div₀ (by linarith) (abs_le.2 ⟨by linarith, by linarith⟩) (by linarith) h1

/-- If the sufficient attractiveness inequality fails, the marginal growth rate is negative for
some fraction below one (Fatou's lemma). -/
lemma OMA.exists_K1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Ω → ℝ) (hA : Measurable A) (b : ℝ) (hb : 1 ≤ b) (hx : ∀ ω, -1 ≤ A ω ∧ A ω ≤ b - 1)
    (hSA : 1 < ∫⁻ ω, (ENNReal.ofReal (1 + A ω))⁻¹ ∂P) :
    ∃ K1 : ℝ, 0 < K1 ∧ K1 < 1 ∧ ∫ ω, A ω / (1 + K1 * A ω) ∂P < 0 := by
  by_contra hcon
  push Not at hcon
  have hKm0 : ∀ m : ℕ, (0 : ℝ) < 1 - 1 / ((m : ℝ) + 2) := by
    intro m
    have h2 : (0 : ℝ) < (m : ℝ) + 2 := by positivity
    rw [sub_pos, div_lt_one h2]
    linarith
  have hKm1 : ∀ m : ℕ, 1 - 1 / ((m : ℝ) + 2) < (1 : ℝ) := by
    intro m
    have h2 : (0 : ℝ) < 1 / ((m : ℝ) + 2) := by positivity
    linarith
  have hlim : Filter.Tendsto (fun m : ℕ => 1 - 1 / ((m : ℝ) + 2)) Filter.atTop (nhds 1) := by
    have h1 : Filter.Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 2)) Filter.atTop (nhds 0) := by
      have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      have h3 := this.comp (Filter.tendsto_add_atTop_nat 1)
      refine h3.congr fun m => ?_
      simp only [Function.comp_apply]
      push_cast
      ring_nf
    simpa using h1.const_sub 1
  have hle : ∀ m : ℕ, ∫⁻ ω, (ENNReal.ofReal (1 + (1 - 1 / ((m : ℝ) + 2)) * A ω))⁻¹ ∂P ≤ 1 := by
    intro m
    set K := 1 - 1 / ((m : ℝ) + 2) with hK
    have hpos : ∀ ω, 0 < 1 + K * A ω := fun ω => by
      have := (OMA.factor_bounds K (A ω) b (hKm0 m).le (hKm1 m) (hx ω).1 (hx ω).2 hb).1
      linarith [hKm1 m]
    have h1 : ∀ ω, (ENNReal.ofReal (1 + K * A ω))⁻¹ = ENNReal.ofReal (1 - K * (A ω / (1 + K * A ω))) := by
      intro ω
      rw [← ENNReal.ofReal_inv_of_pos (hpos ω)]
      congr 1
      have := (hpos ω).ne'
      field_simp
      ring
    simp_rw [h1]
    have hint : Integrable (fun ω => A ω / (1 + K * A ω)) P :=
      OMA.intble P _ (by fun_prop) (b / (1 - K))
        (fun ω => OMA.ratio_bound K (A ω) b (hKm0 m).le (hKm1 m) (hx ω).1 (hx ω).2 hb)
    have hnn : ∀ ω, 0 ≤ 1 - K * (A ω / (1 + K * A ω)) := by
      intro ω
      have e : 1 - K * (A ω / (1 + K * A ω)) = 1 / (1 + K * A ω) := by
        have := (hpos ω).ne'
        field_simp
        ring
      rw [e]
      exact (one_div_pos.2 (hpos ω)).le
    have hint2 : Integrable (fun ω => 1 - K * (A ω / (1 + K * A ω))) P :=
      (integrable_const 1).sub (hint.const_mul K)
    rw [← ofReal_integral_eq_lintegral_ofReal hint2 (Filter.Eventually.of_forall hnn)]
    rw [ENNReal.ofReal_le_one, integral_sub (integrable_const 1) (hint.const_mul K),
      integral_const_mul]
    simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
    nlinarith [hcon K (hKm0 m) (hKm1 m), hKm0 m]
  have hF := lintegral_liminf_le (μ := P)
    (f := fun (m : ℕ) ω => (ENNReal.ofReal (1 + (1 - 1 / ((m : ℝ) + 2)) * A ω))⁻¹)
    (u := Filter.atTop) (fun m => by fun_prop)
  have hpt : ∀ ω, Filter.liminf
      (fun m : ℕ => (ENNReal.ofReal (1 + (1 - 1 / ((m : ℝ) + 2)) * A ω))⁻¹) Filter.atTop
      = (ENNReal.ofReal (1 + A ω))⁻¹ := by
    intro ω
    apply Filter.Tendsto.liminf_eq
    have h2 : Filter.Tendsto (fun m : ℕ => 1 + (1 - 1 / ((m : ℝ) + 2)) * A ω) Filter.atTop
        (nhds (1 + 1 * A ω)) := (hlim.mul_const _).const_add 1
    rw [one_mul] at h2
    exact tendsto_inv_iff.2 (ENNReal.tendsto_ofReal h2)
  simp_rw [hpt] at hF
  have hlim1 : Filter.liminf
      (fun m : ℕ => ∫⁻ ω, (ENNReal.ofReal (1 + (1 - 1 / ((m : ℝ) + 2)) * A ω))⁻¹ ∂P) Filter.atTop
      ≤ 1 := by
    refine Filter.liminf_le_of_le (h := fun c hc => ?_)
    obtain ⟨m, hm⟩ := hc.exists
    exact hm.trans (hle m)
  exact absurd (lt_of_lt_of_le hSA (hF.trans hlim1)) (lt_irrefl _)

/-- A fraction `0 < Ks < 1` at which the marginal growth rate vanishes (intermediate values). -/
lemma OMA.exists_Ks {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Ω → ℝ) (hA : Measurable A) (b : ℝ) (hb : 1 ≤ b) (hx : ∀ ω, -1 ≤ A ω ∧ A ω ≤ b - 1)
    (hEX : 0 < ∫ ω, A ω ∂P) (hSA : 1 < ∫⁻ ω, (ENNReal.ofReal (1 + A ω))⁻¹ ∂P) :
    ∃ Ks : ℝ, 0 < Ks ∧ Ks < 1 ∧ ∫ ω, A ω / (1 + Ks * A ω) ∂P = 0 := by
  obtain ⟨K1, hK10, hK11, hneg⟩ := OMA.exists_K1 P A hA b hb hx hSA
  have hcont : ContinuousOn (fun K : ℝ => ∫ ω, A ω / (1 + K * A ω) ∂P) (Set.Icc 0 K1) := by
    apply continuousOn_of_dominated (bound := fun _ => b / (1 - K1))
    · intro K _
      exact (by fun_prop : Measurable fun ω => A ω / (1 + K * A ω)).aestronglyMeasurable
    · intro K hK
      refine Filter.Eventually.of_forall fun ω => ?_
      rw [Real.norm_eq_abs]
      have h1 := OMA.ratio_bound K (A ω) b hK.1 (lt_of_le_of_lt hK.2 hK11) (hx ω).1 (hx ω).2 hb
      refine h1.trans ?_
      exact div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith [hK.2])
    · exact integrable_const _
    · refine Filter.Eventually.of_forall fun ω => ?_
      apply ContinuousOn.div continuousOn_const (by fun_prop)
      intro K hK
      have := (OMA.factor_bounds K (A ω) b hK.1 (lt_of_le_of_lt hK.2 hK11) (hx ω).1 (hx ω).2 hb).1
      have h2 : K < 1 := lt_of_le_of_lt hK.2 hK11
      linarith
  have hmem : (0 : ℝ) ∈ Set.Icc ((fun K : ℝ => ∫ ω, A ω / (1 + K * A ω) ∂P) K1)
      ((fun K : ℝ => ∫ ω, A ω / (1 + K * A ω) ∂P) 0) := by
    constructor
    · exact hneg.le
    · simpa using hEX.le
  obtain ⟨Ks, hKs, hDs⟩ := intermediate_value_Icc' hK10.le hcont hmem
  refine ⟨Ks, ?_, lt_of_le_of_lt hKs.2 hK11, hDs⟩
  rcases hKs.1.lt_or_eq with h | h
  · exact h
  · exfalso
    rw [← h] at hDs
    simp only [zero_mul, add_zero, div_one] at hDs
    linarith

lemma OMA.log_abs_le (y lo hi : ℝ) (hlo : 0 < lo) (h1 : lo ≤ y) (h2 : y ≤ hi) :
    |Real.log y| ≤ |Real.log lo| + |Real.log hi| := by
  have ha := Real.log_le_log hlo h1
  have hb := Real.log_le_log (lt_of_lt_of_le hlo h1) h2
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (Real.log lo), abs_nonneg (Real.log hi)]
  · linarith [le_abs_self (Real.log hi), abs_nonneg (Real.log lo)]

lemma OMA.sq_bound (x b : ℝ) (hx : -1 ≤ x) (hxb : x ≤ b - 1) (hb : 1 ≤ b) : x ^ 2 ≤ b ^ 2 := by
  nlinarith

lemma OMA.drift_bound (K Ks x : ℝ) (hK0 : 0 ≤ K) (hK1 : K < 1) (hs0 : 0 ≤ Ks) (hs1 : Ks < 1)
    (hx : -1 ≤ x) : |OMA.kap K x - Ks| ≤ 1 := by
  obtain ⟨h0, h1⟩ := OMA.kap_bounds K x hK0 hK1 hx
  rw [abs_le]
  constructor <;> linarith

lemma OMA.integrable_log {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Ω → ℝ) (hA : Measurable A) (b : ℝ) (hb : 1 ≤ b) (hx : ∀ ω, -1 ≤ A ω ∧ A ω ≤ b - 1)
    (K : ℝ) (hK0 : 0 ≤ K) (hK1 : K < 1) : Integrable (fun ω => Real.log (1 + K * A ω)) P := by
  refine OMA.intble P _ (by fun_prop) (|Real.log (1 - K)| + |Real.log b|) (fun ω => ?_)
  obtain ⟨h1, h2⟩ := OMA.factor_bounds K (A ω) b hK0 hK1 (hx ω).1 (hx ω).2 hb
  exact OMA.log_abs_le _ _ _ (by linarith) h1 h2

lemma OMA.integrable_ratio {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Ω → ℝ) (hA : Measurable A) (b : ℝ) (hb : 1 ≤ b) (hx : ∀ ω, -1 ≤ A ω ∧ A ω ≤ b - 1)
    (K : ℝ) (hK0 : 0 ≤ K) (hK1 : K < 1) : Integrable (fun ω => A ω / (1 + K * A ω)) P :=
  OMA.intble P _ (by fun_prop) (b / (1 - K))
    (fun ω => OMA.ratio_bound K (A ω) b hK0 hK1 (hx ω).1 (hx ω).2 hb)

lemma OMA.integrable_sq {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Ω → ℝ) (hA : Measurable A) (b : ℝ) (hb : 1 ≤ b) (hx : ∀ ω, -1 ≤ A ω ∧ A ω ≤ b - 1) :
    Integrable (fun ω => A ω ^ 2) P := by
  refine OMA.intble P _ (by fun_prop) (b ^ 2) (fun ω => ?_)
  rw [abs_of_nonneg (sq_nonneg _)]
  exact OMA.sq_bound _ _ (hx ω).1 (hx ω).2 hb

/-- One period: no fraction beats `Ks`. -/
lemma OMA.one_period_integral {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (A : Ω → ℝ) (hA : Measurable A) (b : ℝ) (hb : 1 ≤ b)
    (hx : ∀ ω, -1 ≤ A ω ∧ A ω ≤ b - 1) (Ks : ℝ) (hs0 : 0 ≤ Ks) (hs1 : Ks < 1)
    (hD : ∫ ω, A ω / (1 + Ks * A ω) ∂P = 0) (K : ℝ) (hK0 : 0 ≤ K) (hK1 : K < 1) :
    ∫ ω, Real.log (1 + K * A ω) ∂P ≤ ∫ ω, Real.log (1 + Ks * A ω) ∂P := by
  have hiLK := OMA.integrable_log P A hA b hb hx K hK0 hK1
  have hiLA := OMA.integrable_log P A hA b hb hx Ks hs0 hs1
  have hiRA := OMA.integrable_ratio P A hA b hb hx Ks hs0 hs1
  have hi : Integrable (fun ω => Real.log (1 + Ks * A ω) + (K - Ks) * (A ω / (1 + Ks * A ω))) P :=
    hiLA.add (hiRA.const_mul _)
  have hmono := integral_mono hiLK hi (fun ω => by
    have h := OMA.one_period_pointwise K Ks (A ω) b hK0 hK1 hs0 hs1 (hx ω).1 (hx ω).2 hb
    have h2 : 0 ≤ (K - Ks) ^ 2 * A ω ^ 2 / (4 * b ^ 2) := by positivity
    simp only
    linarith)
  rw [integral_add hiLA (hiRA.const_mul _), integral_const_mul, hD] at hmono
  linarith

lemma OMA.second_moment_pos {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (A : Ω → ℝ) (hA : Measurable A) (b : ℝ) (hb : 1 ≤ b)
    (hx : ∀ ω, -1 ≤ A ω ∧ A ω ≤ b - 1) (hEX : 0 < ∫ ω, A ω ∂P) : 0 < ∫ ω, A ω ^ 2 ∂P := by
  have hiA : Integrable A P := OMA.intble P A hA b (fun ω => abs_le.2 ⟨by linarith [(hx ω).1], by linarith [(hx ω).2]⟩)
  have hiQ := OMA.integrable_sq P A hA b hb hx
  set t := ∫ ω, A ω ∂P with ht
  have hi2 : Integrable (fun ω => A ω ^ 2 + t ^ 2) P := hiQ.add (integrable_const _)
  have hmono := integral_mono (hiA.const_mul (2 * t)) hi2 (fun ω => by
    simp only
    nlinarith [sq_nonneg (A ω - t)])
  rw [integral_const_mul, integral_add hiQ (integrable_const _), integral_const] at hmono
  simp only [probReal_univ, smul_eq_mul, one_mul] at hmono
  nlinarith

/-- Two periods of buy and hold: the expected log-growth falls short of twice the one-period optimum
by a multiple of the squared distances of the initial and the drifted fraction from `Ks`. -/
lemma OMA.two_period_integral {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (A B : Ω → ℝ) (hA : Measurable A) (hB : Measurable B)
    (hind : IndepFun A B P) (hid : IdentDistrib B A P P) (b : ℝ) (hb : 1 ≤ b)
    (hxA : ∀ ω, -1 ≤ A ω ∧ A ω ≤ b - 1) (hxB : ∀ ω, -1 ≤ B ω ∧ B ω ≤ b - 1)
    (Ks : ℝ) (hs0 : 0 ≤ Ks) (hs1 : Ks < 1) (hD : ∫ ω, A ω / (1 + Ks * A ω) ∂P = 0)
    (K : ℝ) (hK0 : 0 ≤ K) (hK1 : K < 1) :
    ∫ ω, Real.log (1 + K * ((1 + A ω) * (1 + B ω) - 1)) ∂P ≤
      2 * ∫ ω, Real.log (1 + Ks * A ω) ∂P
        - (∫ ω, A ω ^ 2 ∂P) / (4 * b ^ 2)
          * ((K - Ks) ^ 2 + ∫ ω, (OMA.kap K (A ω) - Ks) ^ 2 ∂P) := by
  have hb0 : 0 < b := by linarith
  have hkm : Measurable (fun x : ℝ => OMA.kap K x - Ks) := by
    unfold OMA.kap
    fun_prop
  -- integrability of the pieces
  have hiLA := OMA.integrable_log P A hA b hb hxA Ks hs0 hs1
  have hiLB := OMA.integrable_log P B hB b hb hxB Ks hs0 hs1
  have hiRA := OMA.integrable_ratio P A hA b hb hxA Ks hs0 hs1
  have hiQA := OMA.integrable_sq P A hA b hb hxA
  have hiSRB : Integrable (fun ω => (OMA.kap K (A ω) - Ks) * (B ω / (1 + Ks * B ω))) P := by
    refine OMA.intble P _ ((hkm.comp hA).mul (by fun_prop)) (1 * (b / (1 - Ks))) (fun ω => ?_)
    rw [abs_mul]
    exact mul_le_mul (OMA.drift_bound K Ks (A ω) hK0 hK1 hs0 hs1 (hxA ω).1)
      (OMA.ratio_bound Ks (B ω) b hs0 hs1 (hxB ω).1 (hxB ω).2 hb) (abs_nonneg _) zero_le_one
  have hiTQB : Integrable (fun ω => (OMA.kap K (A ω) - Ks) ^ 2 * B ω ^ 2) P := by
    refine OMA.intble P _ (((hkm.comp hA).pow_const 2).mul (by fun_prop)) (1 * b ^ 2) (fun ω => ?_)
    rw [abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg _)]
    have h1 := OMA.drift_bound K Ks (A ω) hK0 hK1 hs0 hs1 (hxA ω).1
    have h2 : (OMA.kap K (A ω) - Ks) ^ 2 ≤ 1 := by
      have := abs_le.1 h1
      nlinarith
    exact mul_le_mul h2 (OMA.sq_bound _ _ (hxB ω).1 (hxB ω).2 hb) (sq_nonneg _) zero_le_one
  have hiL : Integrable (fun ω => Real.log (1 + K * ((1 + A ω) * (1 + B ω) - 1))) P := by
    refine OMA.intble P _ (by fun_prop) (|Real.log (1 - K)| + |Real.log (b ^ 2)|) (fun ω => ?_)
    have hA0 : 0 ≤ 1 + A ω := by linarith [(hxA ω).1]
    have hB0 : 0 ≤ 1 + B ω := by linarith [(hxB ω).1]
    have hprod : (1 + A ω) * (1 + B ω) ≤ b ^ 2 := by
      have := mul_le_mul (by linarith [(hxA ω).2] : 1 + A ω ≤ b)
        (by linarith [(hxB ω).2] : 1 + B ω ≤ b) hB0 hb0.le
      nlinarith
    refine OMA.log_abs_le _ _ _ (by linarith) ?_ ?_
    · nlinarith [mul_nonneg hK0 (mul_nonneg hA0 hB0)]
    · nlinarith [mul_nonneg (sub_nonneg.2 hK1.le) (by nlinarith : (0 : ℝ) ≤ b ^ 2 - 1),
        mul_nonneg hK0 (sub_nonneg.2 hprod)]
  -- the pointwise bound, integrated
  have hi12 : Integrable (fun ω => Real.log (1 + Ks * A ω) + Real.log (1 + Ks * B ω)) P :=
    hiLA.add hiLB
  have hi123 : Integrable (fun ω => Real.log (1 + Ks * A ω) + Real.log (1 + Ks * B ω)
      + (K - Ks) * (A ω / (1 + Ks * A ω))) P := hi12.add (hiRA.const_mul _)
  have hi1234 : Integrable (fun ω => Real.log (1 + Ks * A ω) + Real.log (1 + Ks * B ω)
      + (K - Ks) * (A ω / (1 + Ks * A ω))
      + (OMA.kap K (A ω) - Ks) * (B ω / (1 + Ks * B ω))) P := hi123.add hiSRB
  have hiQ : Integrable (fun ω => (K - Ks) ^ 2 * A ω ^ 2
      + (OMA.kap K (A ω) - Ks) ^ 2 * B ω ^ 2) P := (hiQA.const_mul _).add hiTQB
  have hiQd : Integrable (fun ω => ((K - Ks) ^ 2 * A ω ^ 2
      + (OMA.kap K (A ω) - Ks) ^ 2 * B ω ^ 2) / (4 * b ^ 2)) P := hiQ.div_const _
  have hiR : Integrable (fun ω => Real.log (1 + Ks * A ω) + Real.log (1 + Ks * B ω)
      + (K - Ks) * (A ω / (1 + Ks * A ω))
      + (OMA.kap K (A ω) - Ks) * (B ω / (1 + Ks * B ω))
      - ((K - Ks) ^ 2 * A ω ^ 2 + (OMA.kap K (A ω) - Ks) ^ 2 * B ω ^ 2) / (4 * b ^ 2)) P :=
    hi1234.sub hiQd
  have hmono := integral_mono hiL hiR (fun ω =>
    OMA.two_period_pointwise K Ks (A ω) (B ω) b hK0 hK1 hs0 hs1 (hxA ω).1 (hxA ω).2
      (hxB ω).1 (hxB ω).2 hb)
  rw [integral_sub hi1234 hiQd, integral_add hi123 hiSRB, integral_add hi12 (hiRA.const_mul _),
    integral_add hiLA hiLB, integral_const_mul, integral_div,
    integral_add (hiQA.const_mul _) hiTQB, integral_const_mul] at hmono
  -- identical distribution and independence
  have e1 : ∫ ω, Real.log (1 + Ks * B ω) ∂P = ∫ ω, Real.log (1 + Ks * A ω) ∂P :=
    (hid.comp (u := fun x : ℝ => Real.log (1 + Ks * x)) (by fun_prop)).integral_eq
  have e2 : ∫ ω, B ω / (1 + Ks * B ω) ∂P = ∫ ω, A ω / (1 + Ks * A ω) ∂P :=
    (hid.comp (u := fun x : ℝ => x / (1 + Ks * x)) (by fun_prop)).integral_eq
  have e3 : ∫ ω, B ω ^ 2 ∂P = ∫ ω, A ω ^ 2 ∂P :=
    (hid.comp (u := fun x : ℝ => x ^ 2) (by fun_prop)).integral_eq
  have e4 : ∫ ω, (OMA.kap K (A ω) - Ks) * (B ω / (1 + Ks * B ω)) ∂P
      = (∫ ω, (OMA.kap K (A ω) - Ks) ∂P) * ∫ ω, B ω / (1 + Ks * B ω) ∂P :=
    hind.integral_fun_comp_mul_comp (f := fun x : ℝ => OMA.kap K x - Ks)
      (g := fun y : ℝ => y / (1 + Ks * y)) hA.aemeasurable hB.aemeasurable
      hkm.aestronglyMeasurable (by fun_prop : Measurable fun y : ℝ => y / (1 + Ks * y)).aestronglyMeasurable
  have e5 : ∫ ω, (OMA.kap K (A ω) - Ks) ^ 2 * B ω ^ 2 ∂P
      = (∫ ω, (OMA.kap K (A ω) - Ks) ^ 2 ∂P) * ∫ ω, B ω ^ 2 ∂P :=
    hind.integral_fun_comp_mul_comp (f := fun x : ℝ => (OMA.kap K x - Ks) ^ 2)
      (g := fun y : ℝ => y ^ 2) hA.aemeasurable hB.aemeasurable
      (hkm.pow_const 2).aestronglyMeasurable (by fun_prop : Measurable fun y : ℝ => y ^ 2).aestronglyMeasurable
  rw [e4, e5, e1, e2, e3, hD] at hmono
  have e6 : ∫ ω, Real.log (1 + Ks * A ω) ∂P + ∫ ω, Real.log (1 + Ks * A ω) ∂P + (K - Ks) * 0
      + (∫ ω, (OMA.kap K (A ω) - Ks) ∂P) * 0
      - ((K - Ks) ^ 2 * ∫ ω, A ω ^ 2 ∂P
        + (∫ ω, (OMA.kap K (A ω) - Ks) ^ 2 ∂P) * ∫ ω, A ω ^ 2 ∂P) / (4 * b ^ 2)
      = 2 * ∫ ω, Real.log (1 + Ks * A ω) ∂P
        - (∫ ω, A ω ^ 2 ∂P) / (4 * b ^ 2)
          * ((K - Ks) ^ 2 + ∫ ω, (OMA.kap K (A ω) - Ks) ^ 2 ∂P) := by
    ring
  rw [e6] at hmono
  exact hmono

/-- Averaged form of `OMA.bracket_pointwise`. -/
lemma OMA.bracket_integral {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Ω → ℝ) (hA : Measurable A) (b : ℝ) (hb : 1 ≤ b) (hx : ∀ ω, -1 ≤ A ω ∧ A ω ≤ b - 1)
    (Ks : ℝ) (hs0 : 0 ≤ Ks) (hs1 : Ks < 1) (K : ℝ) (hK0 : 0 ≤ K) (hK1 : K < 1) :
    K ^ 2 * (1 - K) ^ 2 * (∫ ω, A ω ^ 2 ∂P) / (2 * b ^ 2)
      ≤ (K - Ks) ^ 2 + ∫ ω, (OMA.kap K (A ω) - Ks) ^ 2 ∂P := by
  have hkm : Measurable (fun x : ℝ => OMA.kap K x - Ks) := by
    unfold OMA.kap
    fun_prop
  have hiQA := OMA.integrable_sq P A hA b hb hx
  have hiT : Integrable (fun ω => (OMA.kap K (A ω) - Ks) ^ 2) P := by
    refine OMA.intble P _ ((hkm.comp hA).pow_const 2) 1 (fun ω => ?_)
    rw [abs_of_nonneg (sq_nonneg _)]
    have := abs_le.1 (OMA.drift_bound K Ks (A ω) hK0 hK1 hs0 hs1 (hx ω).1)
    nlinarith
  have hi1 : Integrable (fun ω => K ^ 2 * (1 - K) ^ 2 * A ω ^ 2 / (2 * b ^ 2)) P :=
    (hiQA.const_mul _).div_const _
  have hi2 : Integrable (fun ω => (K - Ks) ^ 2 + (OMA.kap K (A ω) - Ks) ^ 2) P :=
    (integrable_const _).add hiT
  have hmono := integral_mono hi1 hi2 (fun ω =>
    OMA.bracket_pointwise K Ks (A ω) b hK0 hK1 (hx ω).1 (hx ω).2 hb)
  rw [integral_div, integral_const_mul, integral_add (integrable_const _) hiT,
    integral_const] at hmono
  simpa using hmono

theorem OMA.solution : type_of% @OMA.S_arxiv_1801_06737.main := by
  intro Ω _ P _ X Xmin Xmax hm hindep hident hmin1 hmin0 hmax0 hbd hsmin hsmax hEX hall
  by_contra hSA
  rw [not_le] at hSA
  have hb : (1 : ℝ) ≤ 1 + Xmax := by linarith
  have hb0 : (0 : ℝ) < 1 + Xmax := by linarith
  have hxA : ∀ ω, -1 ≤ X 0 ω ∧ X 0 ω ≤ (1 + Xmax) - 1 := fun ω =>
    ⟨by linarith [(hbd 0 ω).1], by linarith [(hbd 0 ω).2]⟩
  have hxB : ∀ ω, -1 ≤ X 1 ω ∧ X 1 ω ≤ (1 + Xmax) - 1 := fun ω =>
    ⟨by linarith [(hbd 1 ω).1], by linarith [(hbd 1 ω).2]⟩
  obtain ⟨Ks, hs0, hs1, hD⟩ := OMA.exists_Ks P (X 0) (hm 0) (1 + Xmax) hb hxA hEX hSA
  have hind : IndepFun (X 0) (X 1) P := hindep.indepFun (by norm_num)
  have hid : IdentDistrib (X 1) (X 0) P P := hident 1
  have hv := OMA.second_moment_pos P (X 0) (hm 0) (1 + Xmax) hb hxA hEX
  obtain ⟨v, hvdef⟩ : ∃ v : ℝ, v = ∫ ω, X 0 ω ^ 2 ∂P := ⟨_, rfl⟩
  obtain ⟨l, hldef⟩ : ∃ l : ℝ, l = ∫ ω, Real.log (1 + Ks * X 0 ω) ∂P := ⟨_, rfl⟩
  rw [← hvdef] at hv
  -- the uniform gap
  have hmin : 0 < min Ks (1 - Ks) := lt_min hs0 (by linarith)
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = min Ks (1 - Ks) / 2 := ⟨_, rfl⟩
  have hd0 : 0 < d := by rw [hd]; exact half_pos hmin
  have hdK : 2 * d ≤ Ks := by rw [hd]; linarith [min_le_left Ks (1 - Ks)]
  have hdK' : 2 * d ≤ 1 - Ks := by rw [hd]; linarith [min_le_right Ks (1 - Ks)]
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = min (d ^ 2) (d ^ 4 * v / (2 * (1 + Xmax) ^ 2)) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; exact lt_min (by positivity) (by positivity)
  have hc : 0 ≤ v / (4 * (1 + Xmax) ^ 2) := by positivity
  have h2 : ∀ K : ℝ, 0 ≤ K → K < 1 →
      ∫ ω, Real.log (1 + K * ((1 + X 0 ω) * (1 + X 1 ω) - 1)) ∂P
        ≤ 2 * l - v / (4 * (1 + Xmax) ^ 2) * δ := by
    intro K hK0 hK1
    have h := OMA.two_period_integral P (X 0) (X 1) (hm 0) (hm 1) hind hid (1 + Xmax) hb hxA hxB
      Ks hs0.le hs1 hD K hK0 hK1
    have hbr := OMA.bracket_integral P (X 0) (hm 0) (1 + Xmax) hb hxA Ks hs0.le hs1 K hK0 hK1
    rw [← hvdef, ← hldef] at h
    rw [← hvdef] at hbr
    have hT0 : 0 ≤ ∫ ω, (OMA.kap K (X 0 ω) - Ks) ^ 2 ∂P := integral_nonneg (fun ω => sq_nonneg _)
    have hδle : δ ≤ (K - Ks) ^ 2 + ∫ ω, (OMA.kap K (X 0 ω) - Ks) ^ 2 ∂P := by
      by_cases hcase : d ≤ |K - Ks|
      · have h3 : d ^ 2 ≤ (K - Ks) ^ 2 := by
          rw [← sq_abs (K - Ks)]
          exact pow_le_pow_left₀ hd0.le hcase 2
        have h4 : δ ≤ d ^ 2 := by rw [hδ]; exact min_le_left _ _
        linarith
      · rw [not_le] at hcase
        have habs := abs_lt.1 hcase
        have hKd : d ≤ K := by linarith
        have hKd' : d ≤ 1 - K := by linarith
        have hprod : d ^ 2 ≤ K * (1 - K) := by
          have := mul_le_mul hKd hKd' hd0.le (by linarith)
          nlinarith
        have h5 : d ^ 4 ≤ K ^ 2 * (1 - K) ^ 2 := by
          have := pow_le_pow_left₀ (by positivity) hprod 2
          nlinarith
        have h6 : d ^ 4 * v / (2 * (1 + Xmax) ^ 2)
            ≤ K ^ 2 * (1 - K) ^ 2 * v / (2 * (1 + Xmax) ^ 2) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h5 hv.le) (by positivity)
        have h4 : δ ≤ d ^ 4 * v / (2 * (1 + Xmax) ^ 2) := by rw [hδ]; exact min_le_right _ _
        linarith
    have := mul_le_mul_of_nonneg_left hδle hc
    linarith
  -- the two optimal growth rates
  have hg1 : ∀ K : ℝ, OMA.S_arxiv_1801_06737.g P X 1 K = ∫ ω, Real.log (1 + K * X 0 ω) ∂P := by
    intro K
    simp [OMA.S_arxiv_1801_06737.g, OMA.S_arxiv_1801_06737.totalReturn]
  have hg2 : ∀ K : ℝ, OMA.S_arxiv_1801_06737.g P X 2 K
      = (1 / 2) * ∫ ω, Real.log (1 + K * ((1 + X 0 ω) * (1 + X 1 ω) - 1)) ∂P := by
    intro K
    simp [OMA.S_arxiv_1801_06737.g, OMA.S_arxiv_1801_06737.totalReturn, Finset.prod_range_succ]
  have hS1 : l ≤ OMA.S_arxiv_1801_06737.gStar P X 1 := by
    unfold OMA.S_arxiv_1801_06737.gStar
    have hbdd : BddAbove (Set.range fun K : Set.Ico (0 : ℝ) 1 =>
        OMA.S_arxiv_1801_06737.g P X 1 K) := by
      refine ⟨l, ?_⟩
      rintro _ ⟨K, rfl⟩
      show OMA.S_arxiv_1801_06737.g P X 1 K ≤ l
      rw [hg1, hldef]
      exact OMA.one_period_integral P (X 0) (hm 0) (1 + Xmax) hb hxA Ks hs0.le hs1 hD K K.2.1 K.2.2
    calc l = OMA.S_arxiv_1801_06737.g P X 1 Ks := by rw [hg1, hldef]
      _ ≤ _ := le_ciSup hbdd ⟨Ks, hs0.le, hs1⟩
  have hS2 : OMA.S_arxiv_1801_06737.gStar P X 2 ≤ l - v / (4 * (1 + Xmax) ^ 2) * δ / 2 := by
    unfold OMA.S_arxiv_1801_06737.gStar
    have hne : Nonempty (Set.Ico (0 : ℝ) 1) := ⟨⟨0, le_refl _, zero_lt_one⟩⟩
    apply ciSup_le
    intro K
    rw [hg2]
    have := h2 K K.2.1 K.2.2
    linarith
  have hgap : 0 < v / (4 * (1 + Xmax) ^ 2) * δ := by positivity
  have := hall 2 (by norm_num)
  linarith
