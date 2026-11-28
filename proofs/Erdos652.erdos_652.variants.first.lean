import FormalConjectures.ErdosProblems.«652»

open Real Finset
/-! Put one point at the origin and all the remaining points on the unit circle. -/

open scoped EuclideanGeometry

theorem OMA.solution : type_of% @Erdos652.erdos_652.variants.first := by
  classical
  let : DecidableEq ℝ² := Classical.decEq _
  let : DecidableEq ℝ := Classical.decEq _
  intro n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let t (i : Fin (n - 1)) : ℝ := (i.val : ℝ) / n
  let point (i : Fin (n - 1)) : ℝ² := WithLp.toLp 2 ![t i, sqrt (1 - (t i) ^ 2)]
  have hinj : Function.Injective point := by
    intro i j hij
    apply Fin.ext
    exact_mod_cast (div_left_inj' hnR.ne').mp (congrArg (fun p : ℝ² => p 0) hij)
  have hdist (i : Fin (n - 1)) : dist (point i) (0 : ℝ²) = 1 := by
    have ht0 : 0 ≤ t i := div_nonneg (Nat.cast_nonneg _) hnR.le
    have ht1 : t i ≤ 1 := by
      apply (div_le_iff₀ hnR).mpr
      rw [one_mul]
      exact_mod_cast (show i.val ≤ n by have := i.isLt; omega)
    have hsq : 0 ≤ 1 - (t i) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr ht1) (add_nonneg zero_le_one ht0)]
    rw [dist_zero_right, EuclideanSpace.norm_eq, Fin.sum_univ_two]
    change sqrt (‖t i‖ ^ 2 + ‖sqrt (1 - (t i) ^ 2)‖ ^ 2) = 1
    rw [norm_eq_abs, norm_eq_abs, sq_abs, sq_abs, sq_sqrt hsq, add_sub_cancel,
      sqrt_one]
  let shell : Finset ℝ² := univ.map ⟨point, hinj⟩
  have hcard : shell.card = n - 1 := by simp [shell]
  have hd (p : ℝ²) (hp : p ∈ shell) : dist p 0 = 1 := by
    obtain ⟨i, _, rfl⟩ := mem_map.mp hp
    exact hdist i
  have hzero : (0 : ℝ²) ∉ shell := fun h => by simpa using hd 0 h
  refine ⟨insert 0 shell, ?_, 0, mem_insert_self _ _, ?_⟩
  · rw [card_insert_of_notMem hzero, hcard]
    omega
  · unfold distinctDistancesFrom
    rw [erase_insert hzero, image_congr (fun p hp => hd p hp),
      image_const (card_pos.mp (by omega)), card_singleton]
