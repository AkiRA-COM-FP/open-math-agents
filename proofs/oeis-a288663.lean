import OMAStatements.S_oeis_a288663

-- Problem: A288663: Decimal representation of the diagonal from the corner to the origin of the n-th stage of growth of the two-dimensional cellular automaton defined by Rule 493
-- Credit: @Qwer2077 (the owner of the agent is credited as the solver)

open OMA.S_oeis_a288663 PowerSeries

namespace OMA.Proof_oeis_a288663

private abbrev c (t : ℕ) (x y : ℤ) : Bool := cell 493 t x y

private lemma cell_succ (t : ℕ) (x y : ℤ) :
    c (t + 1) x y =
      (493 : ℕ).testBit ((c t x y).toNat + 2 * ((c t (x + 1) y).toNat +
        (c t (x - 1) y).toNat + (c t x (y + 1)).toNat + (c t x (y - 1)).toNat)) :=
  rfl

private lemma cell_neg_x (t : ℕ) (x y : ℤ) : c t (-x) y = c t x y := by
  induction t generalizing x y with
  | zero => simp [c, cell]
  | succ t ih =>
    rw [cell_succ, cell_succ]
    have h1 : -x + 1 = -(x - 1) := by ring
    have h2 : -x - 1 = -(x + 1) := by ring
    rw [h1, h2, ih x y, ih (x - 1) y, ih (x + 1) y, ih x (y + 1), ih x (y - 1)]
    congr 2; omega

private lemma cell_neg_y (t : ℕ) (x y : ℤ) : c t x (-y) = c t x y := by
  induction t generalizing x y with
  | zero => simp [c, cell]
  | succ t ih =>
    rw [cell_succ, cell_succ]
    have h1 : -y + 1 = -(y - 1) := by ring
    have h2 : -y - 1 = -(y + 1) := by ring
    rw [h1, h2, ih x y, ih (x + 1) y, ih (x - 1) y, ih x (y - 1), ih x (y + 1)]
    congr 2; omega

private lemma cell_swap (t : ℕ) (x y : ℤ) : c t y x = c t x y := by
  induction t generalizing x y with
  | zero => simp [c, cell, and_comm]
  | succ t ih =>
    rw [cell_succ, cell_succ]
    rw [ih x y, ih x (y + 1), ih x (y - 1), ih (x + 1) y, ih (x - 1) y]
    congr 2; omega

private lemma cell_abs (t : ℕ) (x y : ℤ) : c t |x| |y| = c t x y := by
  rcases le_or_gt 0 x with hx | hx <;> rcases le_or_gt 0 y with hy | hy
  · rw [abs_of_nonneg hx, abs_of_nonneg hy]
  · rw [abs_of_nonneg hx, abs_of_neg hy, cell_neg_y]
  · rw [abs_of_neg hx, abs_of_nonneg hy, cell_neg_x]
  · rw [abs_of_neg hx, abs_of_neg hy, cell_neg_x, cell_neg_y]

private lemma abs_sub_abs_eq_two {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a - b = 2) :
    |(|a| - |b|)| = 2 := by
  rw [abs_of_nonneg ha, abs_of_nonneg hb, h]; norm_num

private lemma rule493_s4 (b : Bool) : (493 : ℕ).testBit (b.toNat + 2 * 4) = !b := by
  cases b <;> decide

private lemma rule493_true_step2 (e w n s : Bool) :
    (493 : ℕ).testBit
      (((493 : ℕ).testBit (1 + 2 * (e.toNat + w.toNat + n.toNat + s.toNat))).toNat +
        2 * ((!e).toNat + (!w).toNat + (!n).toNat + (!s).toNat)) = true := by
  cases e <;> cases w <;> cases n <;> cases s <;> decide

private lemma rule493_true_of_1_3 (k : ℕ) (h1 : 1 ≤ k) (h2 : k ≤ 3) :
    (493 : ℕ).testBit (1 + 2 * k) = true := by
  interval_cases k <;> decide

private lemma rule493_false_of_le1 (k : ℕ) (h : k ≤ 1) :
    (493 : ℕ).testBit (0 + 2 * k) = true := by
  interval_cases k <;> decide

private lemma rule493_false_of_ge3 (k : ℕ) (h1 : 3 ≤ k) (h2 : k ≤ 4) :
    (493 : ℕ).testBit (0 + 2 * k) = true := by
  interval_cases k <;> decide

private def Inv493 (m : ℕ) : Prop :=
  (∀ x y : ℤ, Odd (x + y) → c (2 * m + 1) x y = true) ∧
  (∀ x y : ℤ, (m : ℤ) < max |x| |y| → c (2 * m + 1) x y = true) ∧
  (∀ x y : ℤ, |x| = |y| → |x| ≤ (m : ℤ) → c (2 * m + 1) x y = false) ∧
  (∀ x y : ℤ, Even x → Even y → |(|x| - |y|)| = 2 → c (2 * m + 1) x y = true) ∧
  (∀ x y : ℤ, Odd x → Odd y → |(|x| - |y|)| = 2 → max |x| |y| ≤ (m : ℤ) → c (2 * m + 1) x y = false)

private lemma cell_one (x y : ℤ) : c 1 x y = decide (¬ (x = 0 ∧ y = 0)) := by
  rw [cell_succ]
  by_cases h0 : x = 0 ∧ y = 0
  · rcases h0 with ⟨rfl, rfl⟩; decide
  · have h0' : c 0 x y = false := by simp [c, cell, h0]
    have hcases : (x = 1 ∧ y = 0) ∨ (x = -1 ∧ y = 0) ∨ (x = 0 ∧ y = 1) ∨ (x = 0 ∧ y = -1) ∨
        ((x + 1 ≠ 0 ∨ y ≠ 0) ∧ (x - 1 ≠ 0 ∨ y ≠ 0) ∧ (x ≠ 0 ∨ y + 1 ≠ 0) ∧ (x ≠ 0 ∨ y - 1 ≠ 0)) := by
      omega
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨h1, h2, h3, h4⟩
    · decide
    · decide
    · decide
    · decide
    · have c1 : c 0 (x + 1) y = false := by simp [c, cell]; omega
      have c2 : c 0 (x - 1) y = false := by simp [c, cell]; omega
      have c3 : c 0 x (y + 1) = false := by simp [c, cell]; omega
      have c4 : c 0 x (y - 1) = false := by simp [c, cell]; omega
      rw [h0', c1, c2, c3, c4]
      simp [h0]

private lemma inv493_zero : Inv493 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x y hodd
    rw [show 2 * 0 + 1 = 1 from rfl, cell_one]
    simp only [decide_eq_true_eq]
    intro ⟨hx, hy⟩; subst hx; subst hy
    rcases hodd with ⟨k, hk⟩; omega
  · intro x y hgt
    rw [show 2 * 0 + 1 = 1 from rfl, cell_one]
    simp only [decide_eq_true_eq]
    intro ⟨hx, hy⟩; subst hx; subst hy
    simp at hgt
  · intro x y heq hle
    rw [show 2 * 0 + 1 = 1 from rfl, cell_one]
    have hx0 : x = 0 := abs_eq_zero.mp (le_antisymm (by simpa using hle) (abs_nonneg x))
    have hy0 : y = 0 := abs_eq_zero.mp (by rw [← heq, hx0]; simp)
    simp [hx0, hy0]
  · intro x y _ _ hdiff
    rw [show 2 * 0 + 1 = 1 from rfl, cell_one]
    simp only [decide_eq_true_eq]
    intro ⟨hx, hy⟩; subst hx; subst hy
    simp at hdiff
  · intro x y hx _ _ hle
    exfalso
    rcases hx with ⟨k, rfl⟩
    have : 1 ≤ |2 * k + 1| := by
      rcases le_or_gt 0 (2 * k + 1) with h | h
      · rw [abs_of_nonneg h]; omega
      · rw [abs_of_neg h]; omega
    have := le_max_left |2 * k + 1| |y|
    simp at hle
    omega

private lemma cell_even_of_mix {t : ℕ} {x y : ℤ}
    (hc : c t x y = true)
    (htrue : c t (x + 1) y = true ∨ c t (x - 1) y = true ∨ c t x (y + 1) = true ∨ c t x (y - 1) = true)
    (hfalse : c t (x + 1) y = false ∨ c t (x - 1) y = false ∨ c t x (y + 1) = false ∨ c t x (y - 1) = false) :
    c (t + 1) x y = true := by
  rw [cell_succ, hc, Bool.toNat_true]
  set e := c t (x + 1) y
  set w := c t (x - 1) y
  set n := c t x (y + 1)
  set s := c t x (y - 1)
  have h1 : 1 ≤ e.toNat + w.toNat + n.toNat + s.toNat := by
    rcases htrue with h | h | h | h <;> simp [h] <;> omega
  have h2 : e.toNat + w.toNat + n.toNat + s.toNat ≤ 3 := by
    have := Bool.toNat_le e; have := Bool.toNat_le w; have := Bool.toNat_le n; have := Bool.toNat_le s
    rcases hfalse with h | h | h | h <;> simp [h] at * <;> omega
  exact rule493_true_of_1_3 _ h1 h2

private lemma inv493_even_flip {m : ℕ} (hinv : Inv493 m) (x y : ℤ) (hev : Even (x + y)) :
    c (2 * m + 2) x y = !(c (2 * m + 1) x y) := by
  have hP1 := hinv.1
  have ho1 : Odd ((x + 1) + y) := by rcases hev with ⟨k, hk⟩; exact ⟨k, by omega⟩
  have ho2 : Odd ((x - 1) + y) := by rcases hev with ⟨k, hk⟩; exact ⟨k - 1, by omega⟩
  have ho3 : Odd (x + (y + 1)) := by rcases hev with ⟨k, hk⟩; exact ⟨k, by omega⟩
  have ho4 : Odd (x + (y - 1)) := by rcases hev with ⟨k, hk⟩; exact ⟨k - 1, by omega⟩
  change c ((2 * m + 1) + 1) x y = _
  rw [cell_succ, hP1 _ _ ho1, hP1 _ _ ho2, hP1 _ _ ho3, hP1 _ _ ho4]
  simpa using rule493_s4 (c (2 * m + 1) x y)

private lemma inv493_step {m : ℕ} (hinv : Inv493 m) : Inv493 (m + 1) := by
  have hflip := inv493_even_flip hinv
  obtain ⟨hP1, hP2, hP3, hP4, hP5⟩ := hinv
  have hOutEven : ∀ x y : ℤ, (m : ℤ) + 1 < max |x| |y| → c (2 * m + 2) x y = false := by
    intro x y hgt
    change c ((2 * m + 1) + 1) x y = false
    rw [cell_succ]
    have hmax : ∀ dx dy : ℤ, |dx| + |dy| ≤ 1 → (m : ℤ) < max |x + dx| |y + dy| := by
      intro dx dy hd
      have hx1 : |x| ≤ |x + dx| + |dx| := by
        have := abs_sub (x + dx) dx
        simpa [add_sub_cancel_right] using this
      have hy1 : |y| ≤ |y + dy| + |dy| := by
        have := abs_sub (y + dy) dy
        simpa [add_sub_cancel_right] using this
      have hdx : |dx| ≤ 1 := by have := abs_nonneg dy; omega
      have hdy : |dy| ≤ 1 := by have := abs_nonneg dx; omega
      rcases le_or_gt |x| |y| with hxy | hxy
      · rw [max_eq_right hxy] at hgt
        exact lt_of_lt_of_le (by omega) (le_max_right |x + dx| |y + dy|)
      · rw [max_eq_left (le_of_lt hxy)] at hgt
        exact lt_of_lt_of_le (by omega) (le_max_left |x + dx| |y + dy|)
    rw [hP2 x y (by omega),
        hP2 (x + 1) y (by simpa using hmax 1 0 (by norm_num)),
        hP2 (x - 1) y (by simpa [sub_eq_add_neg] using hmax (-1) 0 (by norm_num)),
        hP2 x (y + 1) (by simpa using hmax 0 1 (by norm_num)),
        hP2 x (y - 1) (by simpa [sub_eq_add_neg] using hmax 0 (-1) (by norm_num))]
    decide
  have hAdjDiag : ∀ k : ℕ, c (2 * m + 2) ((k : ℤ) + 1) (k : ℤ) = decide (k ≤ m) := by
    intro k
    by_cases hkm : k ≤ m
    · simp only [hkm, decide_true]
      change c ((2 * m + 1) + 1) ((k : ℤ) + 1) (k : ℤ) = true
      apply cell_even_of_mix
      · exact hP1 _ _ ⟨k, by omega⟩
      · rcases Nat.even_or_odd k with ⟨r, rfl⟩ | ⟨r, rfl⟩
        · left
          apply hP4
          · exact ⟨r + 1, by push_cast; ring⟩
          · exact ⟨r, by push_cast; ring⟩
          · exact abs_sub_abs_eq_two (by omega) (by omega) (by ring)
        · right; right; right
          apply hP4
          · exact ⟨r + 1, by push_cast; ring⟩
          · exact ⟨r, by push_cast; ring⟩
          · exact abs_sub_abs_eq_two (by omega) (by omega) (by ring)
      · right; left
        have hsub : (k : ℤ) + 1 - 1 = (k : ℤ) := by ring
        rw [hsub]
        exact hP3 (k : ℤ) (k : ℤ) rfl (by rw [abs_of_nonneg (by omega)]; omega)
    · simp only [hkm, decide_false]
      change c ((2 * m + 1) + 1) ((k : ℤ) + 1) (k : ℤ) = false
      rw [cell_succ]
      have h0 : c (2 * m + 1) ((k : ℤ) + 1) (k : ℤ) = true := hP1 _ _ ⟨k, by omega⟩
      have h1 : c (2 * m + 1) ((k : ℤ) + 1 + 1) (k : ℤ) = true := by
        apply hP2; rw [abs_of_nonneg (by omega), abs_of_nonneg (by omega)]; omega
      have h2 : c (2 * m + 1) ((k : ℤ) + 1 - 1) (k : ℤ) = true := by
        apply hP2; rw [abs_of_nonneg (by omega), abs_of_nonneg (by omega)]; omega
      have h3 : c (2 * m + 1) ((k : ℤ) + 1) ((k : ℤ) + 1) = true := by
        apply hP2; rw [abs_of_nonneg (by omega)]; omega
      have h4 : c (2 * m + 1) ((k : ℤ) + 1) ((k : ℤ) - 1) = true := by
        apply hP2
        exact lt_of_lt_of_le (by rw [abs_of_nonneg (by omega)]; omega) (le_max_left _ _)
      rw [h0, h1, h2, h3, h4]; decide
  have hAdjOff2 : ∀ j : ℕ, c (2 * m + 2) (2 * (j : ℤ) + 2) (2 * (j : ℤ) - 1) = decide (2 * j + 1 ≤ m) := by
    intro j
    by_cases hjm : 2 * j + 1 ≤ m
    · simp only [hjm, decide_true]
      change c ((2 * m + 1) + 1) (2 * (j : ℤ) + 2) (2 * (j : ℤ) - 1) = true
      apply cell_even_of_mix
      · exact hP1 _ _ ⟨2 * j, by omega⟩
      · right; right; left
        have hadd : 2 * (j : ℤ) - 1 + 1 = 2 * (j : ℤ) := by ring
        rw [hadd]
        apply hP4
        · exact ⟨j + 1, by ring⟩
        · exact ⟨j, by ring⟩
        · exact abs_sub_abs_eq_two (by omega) (by omega) (by ring)
      · right; left
        have hsub : 2 * (j : ℤ) + 2 - 1 = 2 * (j : ℤ) + 1 := by ring
        rw [hsub]
        cases j with
        | zero =>
          norm_num
          exact hP3 1 (-1) (by norm_num) (by norm_num; omega)
        | succ j' =>
          apply hP5
          · exact ⟨j' + 1, by push_cast; ring⟩
          · exact ⟨j', by push_cast; ring⟩
          · exact abs_sub_abs_eq_two (by omega) (by omega) (by ring)
          · rw [abs_of_nonneg (by omega), abs_of_nonneg (by omega)]; omega
    · simp only [hjm, decide_false]
      change c ((2 * m + 1) + 1) (2 * (j : ℤ) + 2) (2 * (j : ℤ) - 1) = false
      rw [cell_succ]
      have h0 : c (2 * m + 1) (2 * (j : ℤ) + 2) (2 * (j : ℤ) - 1) = true := hP1 _ _ ⟨2 * j, by omega⟩
      have h1 : c (2 * m + 1) (2 * (j : ℤ) + 2 + 1) (2 * (j : ℤ) - 1) = true := by
        apply hP2; exact lt_of_lt_of_le (by rw [abs_of_nonneg (by omega)]; omega) (le_max_left _ _)
      have h2 : c (2 * m + 1) (2 * (j : ℤ) + 2 - 1) (2 * (j : ℤ) - 1) = true := by
        apply hP2; exact lt_of_lt_of_le (by rw [abs_of_nonneg (by omega)]; omega) (le_max_left _ _)
      have h3 : c (2 * m + 1) (2 * (j : ℤ) + 2) (2 * (j : ℤ) - 1 + 1) = true := by
        apply hP2; exact lt_of_lt_of_le (by rw [abs_of_nonneg (by omega)]; omega) (le_max_left _ _)
      have h4 : c (2 * m + 1) (2 * (j : ℤ) + 2) (2 * (j : ℤ) - 1 - 1) = true := by
        apply hP2; exact lt_of_lt_of_le (by rw [abs_of_nonneg (by omega)]; omega) (le_max_left _ _)
      rw [h0, h1, h2, h3, h4]; decide
  have hAdjOff3_le : ∀ j : ℕ, 1 ≤ j → 2 * j + 1 ≤ m →
      c (2 * m + 2) (2 * (j : ℤ) + 1) (2 * (j : ℤ) - 2) = true := by
    intro j hj hjm
    change c ((2 * m + 1) + 1) (2 * (j : ℤ) + 1) (2 * (j : ℤ) - 2) = true
    apply cell_even_of_mix
    · exact hP1 _ _ ⟨2 * j - 1, by omega⟩
    · right; left
      have hsub : 2 * (j : ℤ) + 1 - 1 = 2 * (j : ℤ) := by ring
      rw [hsub]
      apply hP4
      · exact ⟨j, by ring⟩
      · exact ⟨j - 1, by ring⟩
      · exact abs_sub_abs_eq_two (by omega) (by omega) (by ring)
    · right; right; left
      have hadd : 2 * (j : ℤ) - 2 + 1 = 2 * (j : ℤ) - 1 := by ring
      rw [hadd]
      apply hP5
      · exact ⟨j, by ring⟩
      · exact ⟨j - 1, by ring⟩
      · exact abs_sub_abs_eq_two (by omega) (by omega) (by ring)
      · rw [abs_of_nonneg (by omega), abs_of_nonneg (by omega)]; omega
  have hAdjOff3_eq : ∀ j : ℕ, 1 ≤ j → m = 2 * j →
      c (2 * m + 2) (2 * (j : ℤ) + 1) (2 * (j : ℤ) - 2) = false := by
    intro j hj hjm
    change c ((2 * m + 1) + 1) (2 * (j : ℤ) + 1) (2 * (j : ℤ) - 2) = false
    rw [cell_succ]
    have h0 : c (2 * m + 1) (2 * (j : ℤ) + 1) (2 * (j : ℤ) - 2) = true := hP1 _ _ ⟨2 * j - 1, by omega⟩
    have h1 : c (2 * m + 1) (2 * (j : ℤ) + 1 + 1) (2 * (j : ℤ) - 2) = true := by
      apply hP2; exact lt_of_lt_of_le (by rw [abs_of_nonneg (by omega)]; omega) (le_max_left _ _)
    have h2 : c (2 * m + 1) (2 * (j : ℤ) + 1 - 1) (2 * (j : ℤ) - 2) = true := by
      have hsub : 2 * (j : ℤ) + 1 - 1 = 2 * (j : ℤ) := by ring
      rw [hsub]
      apply hP4
      · exact ⟨j, by ring⟩
      · exact ⟨j - 1, by ring⟩
      · exact abs_sub_abs_eq_two (by omega) (by omega) (by ring)
    have h3 : c (2 * m + 1) (2 * (j : ℤ) + 1) (2 * (j : ℤ) - 2 + 1) = true := by
      apply hP2; exact lt_of_lt_of_le (by rw [abs_of_nonneg (by omega)]; omega) (le_max_left _ _)
    have h4 : c (2 * m + 1) (2 * (j : ℤ) + 1) (2 * (j : ℤ) - 2 - 1) = true := by
      apply hP2; exact lt_of_lt_of_le (by rw [abs_of_nonneg (by omega)]; omega) (le_max_left _ _)
    rw [h0, h1, h2, h3, h4]; decide
  -- Now prove the 5 invariants at m + 1 (t = 2*(m+1)+1 = (2*m+2)+1)
  have hP1' : ∀ x y : ℤ, Odd (x + y) → c (2 * (m + 1) + 1) x y = true := by
    intro x y hodd
    have he1 : Even ((x + 1) + y) := by rcases hodd with ⟨k, hk⟩; exact ⟨k + 1, by omega⟩
    have he2 : Even ((x - 1) + y) := by rcases hodd with ⟨k, hk⟩; exact ⟨k, by omega⟩
    have he3 : Even (x + (y + 1)) := by rcases hodd with ⟨k, hk⟩; exact ⟨k + 1, by omega⟩
    have he4 : Even (x + (y - 1)) := by rcases hodd with ⟨k, hk⟩; exact ⟨k, by omega⟩
    change c ((2 * m + 2) + 1) x y = true
    rw [cell_succ, hflip _ _ he1, hflip _ _ he2, hflip _ _ he3, hflip _ _ he4]
    change (493 : ℕ).testBit ((c ((2 * m + 1) + 1) x y).toNat + _) = true
    rw [cell_succ, hP1 x y hodd, Bool.toNat_true]
    exact rule493_true_step2 (c (2 * m + 1) (x + 1) y) (c (2 * m + 1) (x - 1) y)
      (c (2 * m + 1) x (y + 1)) (c (2 * m + 1) x (y - 1))
  have hP2' : ∀ x y : ℤ, ((m + 1 : ℕ) : ℤ) < max |x| |y| → c (2 * (m + 1) + 1) x y = true := by
    intro x y hgt
    rcases Int.even_or_odd (x + y) with hev | hodd
    · rw [← cell_abs]
      set ax := |x|
      set ay := |y|
      have hax : 0 ≤ ax := abs_nonneg x
      have hay : 0 ≤ ay := abs_nonneg y
      have hgt' : (m : ℤ) + 1 < max ax ay := by push_cast at hgt; exact hgt
      have hstep_ge : ∀ u v : ℤ, 0 ≤ v → v ≤ u → (m : ℤ) + 1 < u → c (2 * (m + 1) + 1) u v = true := by
        intro u v hv huv hu
        change c ((2 * m + 2) + 1) u v = true
        rw [cell_succ]
        have hc0 : c (2 * m + 2) u v = false := by
          apply hOutEven; exact lt_of_lt_of_le (by rw [abs_of_nonneg (by omega)]; omega) (le_max_left _ _)
        have h1 : c (2 * m + 2) (u + 1) v = false := by
          apply hOutEven; exact lt_of_lt_of_le (by rw [abs_of_nonneg (by omega)]; omega) (le_max_left _ _)
        have h3 : c (2 * m + 2) u (v + 1) = false := by
          apply hOutEven; exact lt_of_lt_of_le (by rw [abs_of_nonneg (by omega)]; omega) (le_max_left _ _)
        have h4 : c (2 * m + 2) u (v - 1) = false := by
          apply hOutEven; exact lt_of_lt_of_le (by rw [abs_of_nonneg (by omega)]; omega) (le_max_left _ _)
        rw [hc0, h1, h3, h4]
        simp only [Bool.toNat_false, zero_add, add_zero]
        simpa using rule493_false_of_le1 (c (2 * m + 2) (u - 1) v).toNat (Bool.toNat_le _)
      rcases le_or_gt ay ax with hle | hlt
      · rw [max_eq_left hle] at hgt'
        exact hstep_ge ax ay hay hle hgt'
      · rw [max_eq_right (le_of_lt hlt)] at hgt'
        rw [← cell_swap]
        exact hstep_ge ay ax hax (le_of_lt hlt) hgt'
    · exact hP1' x y hodd
  have hP3' : ∀ x y : ℤ, |x| = |y| → |x| ≤ ((m + 1 : ℕ) : ℤ) → c (2 * (m + 1) + 1) x y = false := by
    intro x y heq hle
    rw [← cell_abs, ← heq]
    lift |x| to ℕ using abs_nonneg x with k hk
    have hk_le : k ≤ m + 1 := by omega
    change c ((2 * m + 2) + 1) (k : ℤ) (k : ℤ) = false
    rw [cell_succ]
    have hE_kk : c (2 * m + 2) (k : ℤ) (k : ℤ) = !(c (2 * m + 1) (k : ℤ) (k : ℤ)) :=
      hflip (k : ℤ) (k : ℤ) ⟨k, by ring⟩
    by_cases hkm : k ≤ m
    · have h0 : c (2 * m + 2) (k : ℤ) (k : ℤ) = true := by
        rw [hE_kk, hP3 (k : ℤ) (k : ℤ) rfl (by rw [abs_of_nonneg (by omega)]; omega)]; rfl
      have h1 : c (2 * m + 2) ((k : ℤ) + 1) (k : ℤ) = true := by rw [hAdjDiag k, decide_eq_true hkm]
      have h3 : c (2 * m + 2) (k : ℤ) ((k : ℤ) + 1) = true := by rw [← cell_swap]; exact h1
      have h2 : c (2 * m + 2) ((k : ℤ) - 1) (k : ℤ) = true := by
        cases k with
        | zero =>
          norm_num
          rw [show c (2 * m + 2) (-1) 0 = c (2 * m + 2) 1 0 from cell_neg_x _ 1 0]
          simpa using hAdjDiag 0
        | succ k' =>
          have hsub : ((k' + 1 : ℕ) : ℤ) - 1 = (k' : ℤ) := by push_cast; ring
          rw [hsub, ← cell_swap]
          have hle' : k' ≤ m := by omega
          simpa [Nat.cast_add, Nat.cast_one, hle'] using hAdjDiag k'
      have h4 : c (2 * m + 2) (k : ℤ) ((k : ℤ) - 1) = true := by rw [← cell_swap]; exact h2
      rw [h0, h1, h2, h3, h4]; decide
    · have hkeq : k = m + 1 := by omega
      subst hkeq
      have h0 : c (2 * m + 2) ((m + 1 : ℕ) : ℤ) ((m + 1 : ℕ) : ℤ) = false := by
        rw [hE_kk, hP2 _ _ (by rw [abs_of_nonneg (by omega)]; simp)]; rfl
      have h1 : c (2 * m + 2) (((m + 1 : ℕ) : ℤ) + 1) ((m + 1 : ℕ) : ℤ) = false := by
        rw [hAdjDiag (m + 1), decide_eq_false (by omega)]
      have h3 : c (2 * m + 2) ((m + 1 : ℕ) : ℤ) (((m + 1 : ℕ) : ℤ) + 1) = false := by
        rw [← cell_swap]; exact h1
      have h2 : c (2 * m + 2) (((m + 1 : ℕ) : ℤ) - 1) ((m + 1 : ℕ) : ℤ) = true := by
        have hsub : ((m + 1 : ℕ) : ℤ) - 1 = (m : ℤ) := by push_cast; ring
        rw [hsub, ← cell_swap]
        simpa [Nat.cast_add, Nat.cast_one] using hAdjDiag m
      have h4 : c (2 * m + 2) ((m + 1 : ℕ) : ℤ) (((m + 1 : ℕ) : ℤ) - 1) = true := by
        rw [← cell_swap]; exact h2
      rw [h0, h1, h2, h3, h4]; decide
  have hP4' : ∀ x y : ℤ, Even x → Even y → |(|x| - |y|)| = 2 → c (2 * (m + 1) + 1) x y = true := by
    intro x y hx hy hdiff
    rw [← cell_abs]
    have hcore : ∀ j : ℕ, c (2 * (m + 1) + 1) (2 * (j : ℤ) + 2) (2 * (j : ℤ)) = true := by
      intro j
      change c ((2 * m + 2) + 1) (2 * (j : ℤ) + 2) (2 * (j : ℤ)) = true
      rw [cell_succ]
      have h0 : c (2 * m + 2) (2 * (j : ℤ) + 2) (2 * (j : ℤ)) = false := by
        rw [hflip _ _ ⟨2 * j + 1, by ring⟩]
        rw [hP4 _ _ ⟨j + 1, by ring⟩ ⟨j, by ring⟩ (abs_sub_abs_eq_two (by omega) (by omega) (by ring))]
        rfl
      have hW : c (2 * m + 2) (2 * (j : ℤ) + 2 - 1) (2 * (j : ℤ)) = decide (2 * j ≤ m) := by
        have : 2 * (j : ℤ) + 2 - 1 = ((2 * j : ℕ) : ℤ) + 1 := by push_cast; ring
        have h2j : 2 * (j : ℤ) = ((2 * j : ℕ) : ℤ) := by push_cast; ring
        rw [this, h2j]; exact hAdjDiag (2 * j)
      have hN : c (2 * m + 2) (2 * (j : ℤ) + 2) (2 * (j : ℤ) + 1) = decide (2 * j + 1 ≤ m) := by
        have h1 : 2 * (j : ℤ) + 2 = ((2 * j + 1 : ℕ) : ℤ) + 1 := by push_cast; ring
        have h2 : 2 * (j : ℤ) + 1 = ((2 * j + 1 : ℕ) : ℤ) := by push_cast; ring
        rw [h1, h2]; exact hAdjDiag (2 * j + 1)
      have hS : c (2 * m + 2) (2 * (j : ℤ) + 2) (2 * (j : ℤ) - 1) = decide (2 * j + 1 ≤ m) :=
        hAdjOff2 j
      rw [h0, hW, hN, hS]
      by_cases hle : 2 * j + 1 ≤ m
      · have hle0 : 2 * j ≤ m := by omega
        rw [decide_eq_true hle0, decide_eq_true hle]
        simp only [Bool.toNat_false, Bool.toNat_true]
        have := Bool.toNat_le (c (2 * m + 2) (2 * (j : ℤ) + 2 + 1) (2 * (j : ℤ)))
        exact rule493_false_of_ge3 _ (by omega) (by omega)
      · have hE : c (2 * m + 2) (2 * (j : ℤ) + 2 + 1) (2 * (j : ℤ)) = false := by
          apply hOutEven
          exact lt_of_lt_of_le (by rw [abs_of_nonneg (by omega)]; omega) (le_max_left _ _)
        rw [hE, decide_eq_false hle]
        cases (decide (2 * j ≤ m)) <;> decide
    have hax_ev : Even |x| := by
      rcases le_or_gt 0 x with h | h
      · rwa [abs_of_nonneg h]
      · rw [abs_of_neg h]; exact hx.neg
    have hay_ev : Even |y| := by
      rcases le_or_gt 0 y with h | h
      · rwa [abs_of_nonneg h]
      · rw [abs_of_neg h]; exact hy.neg
    lift |x| to ℕ using abs_nonneg x with nx hnx
    lift |y| to ℕ using abs_nonneg y with ny hny
    have hnx_ev : Even nx := Int.even_coe_nat nx |>.mp hax_ev
    have hny_ev : Even ny := Int.even_coe_nat ny |>.mp hay_ev
    rcases le_or_gt ny nx with hle | hlt
    · rcases hny_ev with ⟨j, rfl⟩
      have hnx_eq : nx = 2 * j + 2 := by
        rw [abs_of_nonneg (by omega)] at hdiff; omega
      subst hnx_eq
      simpa [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, two_mul] using hcore j
    · rcases hnx_ev with ⟨j, rfl⟩
      have hny_eq : ny = 2 * j + 2 := by
        rw [abs_of_neg (by omega)] at hdiff; omega
      subst hny_eq
      rw [← cell_swap]
      simpa [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, two_mul] using hcore j
  have hP5' : ∀ x y : ℤ, Odd x → Odd y → |(|x| - |y|)| = 2 →
      max |x| |y| ≤ ((m + 1 : ℕ) : ℤ) → c (2 * (m + 1) + 1) x y = false := by
    intro x y hx hy hdiff hle
    rw [← cell_abs]
    have hcore : ∀ j : ℕ, 1 ≤ j → 2 * j + 1 ≤ m + 1 →
        c (2 * (m + 1) + 1) (2 * (j : ℤ) + 1) (2 * (j : ℤ) - 1) = false := by
      intro j hj hjm
      change c ((2 * m + 2) + 1) (2 * (j : ℤ) + 1) (2 * (j : ℤ) - 1) = false
      rw [cell_succ]
      have hE0 : c (2 * m + 2) (2 * (j : ℤ) + 1) (2 * (j : ℤ) - 1) =
          !(c (2 * m + 1) (2 * (j : ℤ) + 1) (2 * (j : ℤ) - 1)) :=
        hflip _ _ ⟨2 * j, by ring⟩
      have hN : c (2 * m + 2) (2 * (j : ℤ) + 1) (2 * (j : ℤ) - 1 + 1) = decide (2 * j ≤ m) := by
        have h1 : 2 * (j : ℤ) + 1 = ((2 * j : ℕ) : ℤ) + 1 := by push_cast; ring
        have h2 : 2 * (j : ℤ) - 1 + 1 = ((2 * j : ℕ) : ℤ) := by push_cast; ring
        rw [h1, h2]; exact hAdjDiag (2 * j)
      have hW : c (2 * m + 2) (2 * (j : ℤ) + 1 - 1) (2 * (j : ℤ) - 1) = decide (2 * j - 1 ≤ m) := by
        have h1 : 2 * (j : ℤ) + 1 - 1 = ((2 * j - 1 : ℕ) : ℤ) + 1 := by omega
        have h2 : 2 * (j : ℤ) - 1 = ((2 * j - 1 : ℕ) : ℤ) := by omega
        rw [h1, h2]; exact hAdjDiag (2 * j - 1)
      have hE : c (2 * m + 2) (2 * (j : ℤ) + 1 + 1) (2 * (j : ℤ) - 1) = decide (2 * j + 1 ≤ m) := by
        have h1 : 2 * (j : ℤ) + 1 + 1 = 2 * (j : ℤ) + 2 := by ring
        rw [h1]; exact hAdjOff2 j
      have hS_arg : 2 * (j : ℤ) - 1 - 1 = 2 * (j : ℤ) - 2 := by ring
      rw [hN, hW, hE, hS_arg]
      by_cases hlt : 2 * j + 1 ≤ m
      · have h0 : c (2 * m + 2) (2 * (j : ℤ) + 1) (2 * (j : ℤ) - 1) = true := by
          rw [hE0]
          rw [hP5 _ _ ⟨j, by ring⟩ ⟨j - 1, by ring⟩
            (abs_sub_abs_eq_two (by omega) (by omega) (by ring))
            (by rw [abs_of_nonneg (by omega), abs_of_nonneg (by omega)]; omega)]
          rfl
        have hS : c (2 * m + 2) (2 * (j : ℤ) + 1) (2 * (j : ℤ) - 2) = true := hAdjOff3_le j hj hlt
        have h2j : 2 * j ≤ m := by omega
        have h2j1 : 2 * j - 1 ≤ m := by omega
        rw [h0, hS, decide_eq_true h2j, decide_eq_true h2j1, decide_eq_true hlt]
        decide
      · have hmeq : m = 2 * j := by omega
        have h0 : c (2 * m + 2) (2 * (j : ℤ) + 1) (2 * (j : ℤ) - 1) = false := by
          rw [hE0]
          rw [hP2 _ _ (by exact lt_of_lt_of_le (by rw [abs_of_nonneg (by omega)]; omega) (le_max_left _ _))]
          rfl
        have hS : c (2 * m + 2) (2 * (j : ℤ) + 1) (2 * (j : ℤ) - 2) = false := hAdjOff3_eq j hj hmeq
        have h2j : 2 * j ≤ m := by omega
        have h2j1 : 2 * j - 1 ≤ m := by omega
        rw [h0, hS, decide_eq_true h2j, decide_eq_true h2j1, decide_eq_false hlt]
        decide
    have hax_odd : Odd |x| := by
      rcases le_or_gt 0 x with h | h
      · rwa [abs_of_nonneg h]
      · rw [abs_of_neg h]; exact hx.neg
    have hay_odd : Odd |y| := by
      rcases le_or_gt 0 y with h | h
      · rwa [abs_of_nonneg h]
      · rw [abs_of_neg h]; exact hy.neg
    have nat_odd_of_int : ∀ n : ℕ, Odd (n : ℤ) → Odd n := fun n ⟨k, hk⟩ => ⟨k.toNat, by omega⟩
    lift |x| to ℕ using abs_nonneg x with nx hnx
    lift |y| to ℕ using abs_nonneg y with ny hny
    have hnx_odd : Odd nx := nat_odd_of_int nx hax_odd
    have hny_odd : Odd ny := nat_odd_of_int ny hay_odd
    rcases le_or_gt ny nx with hle' | hlt'
    · rcases hny_odd with ⟨r, rfl⟩
      have hnx_eq : nx = 2 * (r + 1) + 1 := by
        rw [abs_of_nonneg (by omega)] at hdiff; omega
      subst hnx_eq
      have hmax : 2 * (r + 1) + 1 ≤ m + 1 := by omega
      have hcast1 : ((2 * (r + 1) + 1 : ℕ) : ℤ) = 2 * ((r + 1 : ℕ) : ℤ) + 1 := by push_cast; ring
      have hcast2 : ((2 * r + 1 : ℕ) : ℤ) = 2 * ((r + 1 : ℕ) : ℤ) - 1 := by push_cast; ring
      rw [hcast1, hcast2]
      exact hcore (r + 1) (by omega) hmax
    · rcases hnx_odd with ⟨r, rfl⟩
      have hny_eq : ny = 2 * (r + 1) + 1 := by
        rw [abs_of_neg (by omega)] at hdiff; omega
      subst hny_eq
      have hmax : 2 * (r + 1) + 1 ≤ m + 1 := by omega
      rw [← cell_swap]
      have hcast1 : ((2 * (r + 1) + 1 : ℕ) : ℤ) = 2 * ((r + 1 : ℕ) : ℤ) + 1 := by push_cast; ring
      have hcast2 : ((2 * r + 1 : ℕ) : ℤ) = 2 * ((r + 1 : ℕ) : ℤ) - 1 := by push_cast; ring
      rw [hcast1, hcast2]
      exact hcore (r + 1) (by omega) hmax
  exact ⟨hP1', hP2', hP3', hP4', hP5'⟩

private lemma inv493_all (m : ℕ) : Inv493 m := by
  induction m with
  | zero => exact inv493_zero
  | succ m ih => exact inv493_step ih

private lemma diag_odd (m j : ℕ) :
    c (2 * m + 1) (j : ℤ) (j : ℤ) = decide (m < j) := by
  have hinv := inv493_all m
  by_cases hjm : m < j
  · simp only [hjm, decide_true]
    exact hinv.2.1 (j : ℤ) (j : ℤ) (by rw [abs_of_nonneg (by omega)]; simp; omega)
  · simp only [hjm, decide_false]
    exact hinv.2.2.1 (j : ℤ) (j : ℤ) rfl (by rw [abs_of_nonneg (by omega)]; omega)

private lemma diag_even_succ (m j : ℕ) :
    c (2 * m + 2) (j : ℤ) (j : ℤ) = decide (j ≤ m) := by
  rw [inv493_even_flip (inv493_all m) (j : ℤ) (j : ℤ) ⟨j, by ring⟩, diag_odd]
  by_cases h : j ≤ m
  · have h1 : ¬ (m < j) := by omega
    simp [h, h1]
  · have h1 : m < j := by omega
    simp [h, h1]

private lemma a_eq_sum_rev (n : ℕ) :
    a n = ∑ j ∈ Finset.range (n + 1), if c n (j : ℤ) (j : ℤ) then (2 : ℤ) ^ j else 0 := by
  unfold a c
  refine Finset.sum_bij (fun k _ => n - k) ?_ ?_ ?_ ?_
  · intro k hk; rw [Finset.mem_range] at hk ⊢; omega
  · intro k1 hk1 k2 hk2 h; rw [Finset.mem_range] at hk1 hk2; omega
  · intro j hj; rw [Finset.mem_range] at hj
    exact ⟨n - j, by rw [Finset.mem_range]; omega, by omega⟩
  · intro k hk
    rw [Finset.mem_range] at hk
    have hcast : ((n : ℤ) - (k : ℤ)) = ((n - k : ℕ) : ℤ) := by omega
    rw [hcast]

private lemma sum_pow_two (k : ℕ) :
    ∑ j ∈ Finset.range k, (2 : ℤ) ^ j = (2 : ℤ) ^ k - 1 := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

private lemma a_zero : (a 0 : ℚ) = 1 := by decide

private lemma a_even_pos (m : ℕ) : (a (2 * m + 2) : ℚ) = (2 : ℚ) ^ (m + 1) - 1 := by
  have ha : a (2 * m + 2) = (2 : ℤ) ^ (m + 1) - 1 := by
    rw [a_eq_sum_rev]
    have hterm : ∀ j ∈ Finset.range (2 * m + 2 + 1),
        (if c (2 * m + 2) (j : ℤ) (j : ℤ) then (2 : ℤ) ^ j else 0) =
        if j < m + 1 then (2 : ℤ) ^ j else 0 := by
      intro j _
      rw [diag_even_succ m j]
      by_cases h : j ≤ m
      · have h1 : j < m + 1 := by omega
        simp [h, h1]
      · have h1 : ¬ (j < m + 1) := by omega
        simp [h, h1]
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
    have hfilt : (Finset.range (2 * m + 2 + 1)).filter (fun j => j < m + 1) = Finset.range (m + 1) := by
      ext j; simp only [Finset.mem_filter, Finset.mem_range]; omega
    rw [hfilt, sum_pow_two]
  rw [ha]; push_cast; ring

private lemma a_odd (m : ℕ) :
    (a (2 * m + 1) : ℚ) = (2 : ℚ) ^ (2 * m + 2) - (2 : ℚ) ^ (m + 1) := by
  have ha : a (2 * m + 1) = (2 : ℤ) ^ (2 * m + 2) - (2 : ℤ) ^ (m + 1) := by
    rw [a_eq_sum_rev]
    have hterm : ∀ j ∈ Finset.range (2 * m + 1 + 1),
        (if c (2 * m + 1) (j : ℤ) (j : ℤ) then (2 : ℤ) ^ j else 0) =
        if m < j then (2 : ℤ) ^ j else 0 := by
      intro j _
      rw [diag_odd m j]
      simp
    rw [Finset.sum_congr rfl hterm]
    have hsplit : (∑ j ∈ Finset.range (2 * m + 2), (2 : ℤ) ^ j) =
        (∑ j ∈ Finset.range (2 * m + 2), if m < j then (2 : ℤ) ^ j else 0) +
        (∑ j ∈ Finset.range (2 * m + 2), if j ≤ m then (2 : ℤ) ^ j else 0) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases h : m < j
      · have h1 : ¬ (j ≤ m) := by omega
        simp [h, h1]
      · have h1 : j ≤ m := by omega
        simp [h, h1]
    have hlow : (∑ j ∈ Finset.range (2 * m + 2), if j ≤ m then (2 : ℤ) ^ j else 0) =
        (2 : ℤ) ^ (m + 1) - 1 := by
      rw [← Finset.sum_filter]
      have hfilt : (Finset.range (2 * m + 2)).filter (fun j => j ≤ m) = Finset.range (m + 1) := by
        ext j; simp only [Finset.mem_filter, Finset.mem_range]; omega
      rw [hfilt, sum_pow_two]
    have htot := sum_pow_two (2 * m + 2)
    have hlen : 2 * m + 1 + 1 = 2 * m + 2 := by omega
    rw [hlen]
    linarith
  rw [ha]; push_cast; ring

private lemma a_rec (n : ℕ) (hn : 7 ≤ n) :
    (a n : ℚ) = 7 * a (n - 2) - 14 * a (n - 4) + 8 * a (n - 6) := by
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 7 := ⟨n - 7, by omega⟩
  have h2 : r + 7 - 2 = r + 5 := by omega
  have h4 : r + 7 - 4 = r + 3 := by omega
  have h6 : r + 7 - 6 = r + 1 := by omega
  rw [h2, h4, h6]
  rcases Nat.even_or_odd r with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have e1 : k + k + 7 = 2 * (k + 3) + 1 := by omega
    have e2 : k + k + 5 = 2 * (k + 2) + 1 := by omega
    have e3 : k + k + 3 = 2 * (k + 1) + 1 := by omega
    have e4 : k + k + 1 = 2 * k + 1 := by omega
    rw [e1, e2, e3, e4, a_odd, a_odd, a_odd, a_odd]
    have p1 : (2 : ℚ) ^ (2 * (k + 3) + 2) = 64 * (2 : ℚ) ^ (2 * k + 2) := by
      have : 2 * (k + 3) + 2 = (2 * k + 2) + 6 := by omega
      rw [this, pow_add]; ring
    have p2 : (2 : ℚ) ^ (2 * (k + 2) + 2) = 16 * (2 : ℚ) ^ (2 * k + 2) := by
      have : 2 * (k + 2) + 2 = (2 * k + 2) + 4 := by omega
      rw [this, pow_add]; ring
    have p3 : (2 : ℚ) ^ (2 * (k + 1) + 2) = 4 * (2 : ℚ) ^ (2 * k + 2) := by
      have : 2 * (k + 1) + 2 = (2 * k + 2) + 2 := by omega
      rw [this, pow_add]; ring
    have q1 : (2 : ℚ) ^ (k + 3 + 1) = 8 * (2 : ℚ) ^ (k + 1) := by
      have : k + 3 + 1 = (k + 1) + 3 := by omega
      rw [this, pow_add]; ring
    have q2 : (2 : ℚ) ^ (k + 2 + 1) = 4 * (2 : ℚ) ^ (k + 1) := by
      have : k + 2 + 1 = (k + 1) + 2 := by omega
      rw [this, pow_add]; ring
    have q3 : (2 : ℚ) ^ (k + 1 + 1) = 2 * (2 : ℚ) ^ (k + 1) := by
      have : k + 1 + 1 = (k + 1) + 1 := by omega
      rw [this, pow_add]; ring
    rw [p1, p2, p3, q1, q2, q3]
    ring
  · have e1 : 2 * k + 1 + 7 = 2 * (k + 3) + 2 := by omega
    have e2 : 2 * k + 1 + 5 = 2 * (k + 2) + 2 := by omega
    have e3 : 2 * k + 1 + 3 = 2 * (k + 1) + 2 := by omega
    have e4 : 2 * k + 1 + 1 = 2 * k + 2 := by omega
    rw [e1, e2, e3, e4, a_even_pos, a_even_pos, a_even_pos, a_even_pos]
    have q1 : (2 : ℚ) ^ (k + 3 + 1) = 8 * (2 : ℚ) ^ (k + 1) := by
      have : k + 3 + 1 = (k + 1) + 3 := by omega
      rw [this, pow_add]; ring
    have q2 : (2 : ℚ) ^ (k + 2 + 1) = 4 * (2 : ℚ) ^ (k + 1) := by
      have : k + 2 + 1 = (k + 1) + 2 := by omega
      rw [this, pow_add]; ring
    have q3 : (2 : ℚ) ^ (k + 1 + 1) = 2 * (2 : ℚ) ^ (k + 1) := by
      have : k + 1 + 1 = (k + 1) + 1 := by omega
      rw [this, pow_add]; ring
    rw [q1, q2, q3]
    ring

private lemma a_val_1 : (a 1 : ℚ) = 2 := by rw [show (1 : ℕ) = 2 * 0 + 1 from rfl, a_odd 0]; norm_num
private lemma a_val_2 : (a 2 : ℚ) = 1 := by rw [show (2 : ℕ) = 2 * 0 + 2 from rfl, a_even_pos 0]; norm_num
private lemma a_val_3 : (a 3 : ℚ) = 12 := by rw [show (3 : ℕ) = 2 * 1 + 1 from rfl, a_odd 1]; norm_num
private lemma a_val_4 : (a 4 : ℚ) = 3 := by rw [show (4 : ℕ) = 2 * 1 + 2 from rfl, a_even_pos 1]; norm_num
private lemma a_val_5 : (a 5 : ℚ) = 56 := by rw [show (5 : ℕ) = 2 * 2 + 1 from rfl, a_odd 2]; norm_num
private lemma a_val_6 : (a 6 : ℚ) = 7 := by rw [show (6 : ℕ) = 2 * 2 + 2 from rfl, a_even_pos 2]; norm_num

private lemma coeff_mul_X_pow (f : ℚ⟦X⟧) (k n : ℕ) :
    PowerSeries.coeff n (f * X ^ k) = if k ≤ n then PowerSeries.coeff (n - k) f else 0 :=
  PowerSeries.coeff_mul_X_pow' f k n

private lemma gf_eq :
    PowerSeries.mk (fun n => (a n : ℚ)) *
      ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X) * (1 - 2 * X ^ 2) : PowerSeries ℚ) =
      1 + 2 * X - 6 * X ^ 2 - 2 * X ^ 3 + 10 * X ^ 4 - 8 * X ^ 6 := by
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => (a n : ℚ))
  have hD : ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X) * (1 - 2 * X ^ 2) : ℚ⟦X⟧) =
      1 - C (7 : ℚ) * X ^ 2 + C (14 : ℚ) * X ^ 4 - C (8 : ℚ) * X ^ 6 := by
    simp only [map_ofNat]; ring
  have hN : (1 + 2 * X - 6 * X ^ 2 - 2 * X ^ 3 + 10 * X ^ 4 - 8 * X ^ 6 : ℚ⟦X⟧) =
      C (1 : ℚ) + C (2 : ℚ) * X ^ 1 - C (6 : ℚ) * X ^ 2 - C (2 : ℚ) * X ^ 3 +
      C (10 : ℚ) * X ^ 4 - C (8 : ℚ) * X ^ 6 := by
    simp only [map_one, map_ofNat, pow_one]
  rw [hD, hN]
  ext n
  have hmul : A * (1 - C (7 : ℚ) * X ^ 2 + C (14 : ℚ) * X ^ 4 - C (8 : ℚ) * X ^ 6) =
      A - C (7 : ℚ) * (A * X ^ 2) + C (14 : ℚ) * (A * X ^ 4) - C (8 : ℚ) * (A * X ^ 6) := by ring
  rw [hmul]
  simp only [map_add, map_sub, PowerSeries.coeff_C, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow, coeff_mul_X_pow, A, PowerSeries.coeff_mk]
  match n with
  | 0 => simp [a_zero]
  | 1 => simp [a_val_1]
  | 2 => simp [a_zero, a_val_2]; norm_num
  | 3 => simp [a_val_1, a_val_3]; norm_num
  | 4 => simp [a_zero, a_val_2, a_val_4]; norm_num
  | 5 => simp [a_val_1, a_val_3, a_val_5]; norm_num
  | 6 => simp [a_zero, a_val_2, a_val_4, a_val_6]; norm_num
  | r + 7 =>
    have hrec := a_rec (r + 7) (by omega)
    have h0 : r + 7 ≠ 0 := by omega
    have h1 : r + 7 ≠ 1 := by omega
    have h2 : r + 7 ≠ 2 := by omega
    have h3 : r + 7 ≠ 3 := by omega
    have h4 : r + 7 ≠ 4 := by omega
    have h6 : r + 7 ≠ 6 := by omega
    have hge2 : 2 ≤ r + 7 := by omega
    have hge4 : 4 ≤ r + 7 := by omega
    have hge6 : 6 ≤ r + 7 := by omega
    simp only [h0, h1, h2, h3, h4, h6, hge2, hge4, hge6, ↓reduceIte, mul_zero, add_zero, sub_zero]
    linarith

end OMA.Proof_oeis_a288663

theorem OMA.solution : type_of% @OMA.S_oeis_a288663.main :=
  ⟨OMA.Proof_oeis_a288663.gf_eq, OMA.Proof_oeis_a288663.a_rec⟩
