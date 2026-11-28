import OMAReductions.R_Erdos686_erdos_686_R1_H2_R1

-- Step Erdos686.erdos_686.R1.H2.R1.H1: hypothesis H1 of reduction Erdos686.erdos_686.R1.H2.R1
-- Credit: @mjsechrest2

private def step (Y : ℤ) (z : ℤ × ℤ) : ℤ × ℤ :=
  (2 * Y * z.1 - z.2, z.1)

private lemma iter_props (Y : ℤ) (hY : 3 ≤ Y) (j : ℕ) :
    let z := (step Y)^[j] (1, 0)
    z.1 ^ 2 - 2 * Y * z.1 * z.2 + z.2 ^ 2 = 1 ∧ 0 ≤ z.2 ∧ z.2 < z.1 ∧
      (1 ≤ j → 2 * Y ≤ z.1) := by
  induction j with
  | zero =>
    refine ⟨by norm_num, le_rfl, by norm_num, fun h => by omega⟩
  | succ k ih =>
    rcases ih with ⟨hinv, hv0, hvu, _⟩
    set z := (step Y)^[k] (1, 0)
    have hstep : (step Y)^[k + 1] (1, 0) = (2 * Y * z.1 - z.2, z.1) := by
      rw [Function.iterate_succ_apply']
      rfl
    rw [hstep]
    refine ⟨?_, by omega, ?_, ?_⟩
    · dsimp only
      linear_combination hinv
    · dsimp only
      nlinarith
    · intro _
      dsimp only
      by_cases hu1 : z.1 = 1
      · have hvz : z.2 = 0 := by omega
        rw [hu1, hvz]
        linarith
      · have hu2 : 2 ≤ z.1 := by omega
        nlinarith

private lemma descent (Y : ℤ) (hY : 3 ≤ Y) :
    ∀ k : ℕ, ∀ u v : ℤ, u = (k : ℤ) → 0 ≤ v → v < u →
      u ^ 2 - 2 * Y * u * v + v ^ 2 = 1 →
      ∃ j : ℕ, j < k ∧ (step Y)^[j] (1, 0) = (u, v) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro u v huk hv0 hvu hinv
    by_cases hvz : v = 0
    · subst hvz
      have hu1 : u = 1 := by nlinarith
      have hk1 : k = 1 := by omega
      exact ⟨0, by omega, by rw [hu1]; rfl⟩
    · have hvpos : 1 ≤ v := by omega
      have hupos : 0 < u := by omega
      set w : ℤ := 2 * Y * v - u
      have huw : u * w = v ^ 2 - 1 := by
        dsimp only [w]
        linear_combination -hinv
      have hw0 : 0 ≤ w := by nlinarith
      have hwv : w < v := by nlinarith
      have hwinv : v ^ 2 - 2 * Y * v * w + w ^ 2 = 1 := by
        dsimp only [w]
        linear_combination hinv
      set k' : ℕ := v.toNat
      have hk'eq : (k' : ℤ) = v := Int.toNat_of_nonneg hv0
      have hk'lt : k' < k := by omega
      obtain ⟨j, hjk', hjstep⟩ := ih k' hk'lt v w hk'eq.symm hw0 hwv hwinv
      refine ⟨j + 1, by omega, ?_⟩
      rw [Function.iterate_succ_apply', hjstep]
      ext
      · dsimp only [step, w]
        ring
      · rfl

theorem OMA.solution : OMA.R_Erdos686_erdos_686_R1_H2_R1.H1 := by
  intro a ha
  constructor
  · rintro ⟨n, m, hnm, heq⟩
    have heqZ : (a : ℤ) ^ 2 * ((n : ℤ) + 1) * ((n : ℤ) + 2) =
        ((m : ℤ) + 1) * ((m : ℤ) + 2) := by
      exact_mod_cast heq
    set Y : ℤ := 2 * (n : ℤ) + 3
    set X : ℤ := 2 * (m : ℤ) + 3
    set u : ℤ := (a : ℤ)
    set v : ℤ := Y * u - X
    have hY : 3 ≤ Y := by omega
    have hu2 : 2 ≤ u := by omega
    have hXpos : 0 ≤ X := by omega
    have hYu : 0 ≤ Y * u := by nlinarith
    have hXsq : X ^ 2 - (Y ^ 2 - 1) * u ^ 2 = 1 := by
      dsimp only [X, Y, u]
      linear_combination -4 * heqZ
    have hinv : u ^ 2 - 2 * Y * u * v + v ^ 2 = 1 := by
      dsimp only [v]
      linear_combination hXsq
    have hvpos : 1 ≤ v := by
      have hlt : X < Y * u := by nlinarith [hXsq, hXpos, hYu, hu2]
      dsimp only [v]
      linarith
    have hvu : v < u := by
      have hgt : (Y - 1) * u < X := by nlinarith [hXsq, hXpos, hY, hu2]
      dsimp only [v]
      linarith
    have hna : n < a := by
      set w : ℤ := 2 * Y * v - u
      have huw : u * w = v ^ 2 - 1 := by
        dsimp only [w]
        linear_combination -hinv
      have hwv : w < v := by nlinarith
      have hbig : (2 * Y - 1) * v < u := by nlinarith
      have : 2 * Y - 1 < u := by nlinarith
      omega
    obtain ⟨j, hja, hjstep⟩ := descent Y hY a u v rfl (by omega) hvu hinv
    refine ⟨n, hna, j, hja, ?_⟩
    exact congrArg Prod.fst hjstep
  · rintro ⟨n, _, j, _, hj⟩
    set Y : ℤ := 2 * (n : ℤ) + 3
    have hY : 3 ≤ Y := by omega
    have hprops := iter_props Y hY j
    set z := (step Y)^[j] (1, 0)
    rcases hprops with ⟨hinv, hv0, hvu, hjbig⟩
    have hz1 : z.1 = (a : ℤ) := hj
    have hj1 : 1 ≤ j := by
      by_contra h0
      have hj0 : j = 0 := by omega
      subst hj0
      change (1 : ℤ) = (a : ℤ) at hz1
      omega
    have haY : 2 * Y ≤ (a : ℤ) := hz1 ▸ hjbig hj1
    set X : ℤ := Y * z.1 - z.2
    have hXsq : X ^ 2 = 4 * (((a : ℤ) ^ 2) * ((n : ℤ) + 1) * ((n : ℤ) + 2)) + 1 := by
      have h1 : X ^ 2 - (Y ^ 2 - 1) * z.1 ^ 2 = 1 := by
        dsimp only [X]
        linear_combination hinv
      rw [hz1] at h1
      dsimp only [Y] at h1
      linear_combination h1
    have hXodd : X % 2 = 1 := by
      have hmod : X ^ 2 % 2 = 1 := by
        rw [hXsq]
        omega
      have hsq : X ^ 2 = X * X := sq X
      rw [hsq, Int.mul_emod] at hmod
      rcases Int.emod_two_eq_zero_or_one X with h0 | h1
      · rw [h0] at hmod
        norm_num at hmod
      · exact h1
    have hXge : Y + 4 ≤ X := by
      dsimp only [X]
      nlinarith
    set m : ℕ := ((X - 3) / 2).toNat
    have hmX : 2 * (m : ℤ) + 3 = X := by
      have hnonneg : 0 ≤ (X - 3) / 2 := by omega
      have htoNat : (m : ℤ) = (X - 3) / 2 := Int.toNat_of_nonneg hnonneg
      omega
    have hnm : n + 2 ≤ m := by omega
    refine ⟨n, m, hnm, ?_⟩
    have hZ : (a : ℤ) ^ 2 * ((n : ℤ) + 1) * ((n : ℤ) + 2) = ((m : ℤ) + 1) * ((m : ℤ) + 2) := by
      have h4 : 4 * (((m : ℤ) + 1) * ((m : ℤ) + 2)) = X ^ 2 - 1 := by
        rw [← hmX]
        ring
      linarith
    exact_mod_cast hZ
