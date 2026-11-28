import OMAReductions.R_oeis_a136863_R1

-- Reduction oeis-a136863.R1.H1.R1 of step oeis-a136863.R1.H1
-- Credit: @Ciphore

namespace OMA.R_oeis_a136863_R1_H1_R1

open OMA.S_oeis_a136863

/-- A digit outside `0,1,4,7` in the units position is impossible. -/
lemma forbidden_at_zero {n a : ℕ} (h : UsesDigits n) (ha : (n / 10 ^ 0) % 10 = a)
    (hb : a ≠ 0 ∧ a ≠ 1 ∧ a ≠ 4 ∧ a ≠ 7) : False := by
  have hl := OMA.R_oeis_a136863_R1.last_ok (OMA.R_oeis_a136863_R1.div_ok h 0)
  omega

/-- A digit outside `0,1,4,7` in the tens position is impossible. -/
lemma forbidden_at_one {n a : ℕ} (h : UsesDigits n) (ha : (n / 10 ^ 1) % 10 = a)
    (hb : a ≠ 0 ∧ a ≠ 1 ∧ a ≠ 4 ∧ a ≠ 7) : False := by
  have hl := OMA.R_oeis_a136863_R1.last_ok (OMA.R_oeis_a136863_R1.div_ok h 1)
  omega

/-- A digit outside `0,1,4,7` in the hundreds position is impossible. -/
lemma forbidden_at_two {n a : ℕ} (h : UsesDigits n) (ha : (n / 10 ^ 2) % 10 = a)
    (hb : a ≠ 0 ∧ a ≠ 1 ∧ a ≠ 4 ∧ a ≠ 7) : False := by
  have hl := OMA.R_oeis_a136863_R1.last_ok (OMA.R_oeis_a136863_R1.div_ok h 2)
  omega

/-- A digit outside `0,1,4,7` in the thousands position is impossible. -/
lemma forbidden_at_three {n a : ℕ} (h : UsesDigits n) (ha : (n / 10 ^ 3) % 10 = a)
    (hb : a ≠ 0 ∧ a ≠ 1 ∧ a ≠ 4 ∧ a ≠ 7) : False := by
  have hl := OMA.R_oeis_a136863_R1.last_ok (OMA.R_oeis_a136863_R1.div_ok h 3)
  omega

/-- Modular evaluation of the displayed quadratic window. -/
lemma window_mod {u M A B : ℕ} (hu : u ≡ A [MOD M])
    (hB : (2 * A + 10 * A ^ 2) % M = B % M) :
    (2 * u + 10 * u ^ 2) % M = B % M := by
  have hsq : 10 * u ^ 2 ≡ 10 * A ^ 2 [MOD M] := (hu.pow 2).mul_left 10
  have htwo : 2 * u ≡ 2 * A [MOD M] := hu.mul_left 2
  have hsum := htwo.add hsq
  change (2 * u + 10 * u ^ 2) % M = (2 * A + 10 * A ^ 2) % M at hsum
  rwa [hB] at hsum

lemma tens_u_congr {v r : ℕ} (hv : v % 10 = r) :
    (7 + 10 * v) ≡ 7 + 10 * r [MOD 100] := by
  have hv100 : (10 * v) ≡ 10 * r [MOD 100] := by
    change (10 * v) % 100 = (10 * r) % 100
    omega
  simpa using (Nat.ModEq.refl 7).add hv100

lemma hundreds_u_congr {v r : ℕ} (hv : v % 10 = r) :
    (7 + 100 * v) ≡ 7 + 100 * r [MOD 1000] := by
  have hv1000 : (100 * v) ≡ 100 * r [MOD 1000] := by
    change (100 * v) % 1000 = (100 * r) % 1000
    omega
  simpa using (Nat.ModEq.refl 7).add hv1000

/-- Tens-position terminal digit `1` forces digit `2` in the tens position. -/
lemma terminal_one_tens_eliminated {v : ℕ} (hv : v % 10 = 1) :
    ¬ UsesDigits (2 * (7 + 10 * v) + 10 * (7 + 10 * v) ^ 2) := by
  intro hdig
  have hu := tens_u_congr hv
  have hmod : (2 * (7 + 10 * v) + 10 * (7 + 10 * v) ^ 2) % 100 = 24 := by
    simpa using window_mod (u := 7 + 10 * v) (M := 100) (A := 17) (B := 24) hu (by decide)
  have hdigit : ((2 * (7 + 10 * v) + 10 * (7 + 10 * v) ^ 2) / 10 ^ 1) % 10 = 2 := by omega
  exact forbidden_at_one hdig hdigit (by decide)

/-- Tens-position terminal digit `4` forces digit `8` in the tens position. -/
lemma terminal_four_tens_eliminated {v : ℕ} (hv : v % 10 = 4) :
    ¬ UsesDigits (2 * (7 + 10 * v) + 10 * (7 + 10 * v) ^ 2) := by
  intro hdig
  have hu := tens_u_congr hv
  have hmod : (2 * (7 + 10 * v) + 10 * (7 + 10 * v) ^ 2) % 100 = 84 := by
    simpa using window_mod (u := 7 + 10 * v) (M := 100) (A := 47) (B := 84) hu (by decide)
  have hdigit : ((2 * (7 + 10 * v) + 10 * (7 + 10 * v) ^ 2) / 10 ^ 1) % 10 = 8 := by omega
  exact forbidden_at_one hdig hdigit (by decide)

/-- Hundreds-position terminal digit `4` forces digit `3` in the hundreds position. -/
lemma terminal_four_hundreds_eliminated {v : ℕ} (hv : v % 10 = 4) :
    ¬ UsesDigits (2 * (7 + 100 * v) + 10 * (7 + 100 * v) ^ 2) := by
  intro hdig
  have hu := hundreds_u_congr hv
  have hmod : (2 * (7 + 100 * v) + 10 * (7 + 100 * v) ^ 2) % 1000 = 304 := by
    simpa using window_mod (u := 7 + 100 * v) (M := 1000) (A := 407) (B := 304) hu (by decide)
  have hdigit : ((2 * (7 + 100 * v) + 10 * (7 + 100 * v) ^ 2) / 10 ^ 2) % 10 = 3 := by omega
  exact forbidden_at_two hdig hdigit (by decide)

/-- Hundreds-position terminal digit `7` forces digit `9` in the hundreds position. -/
lemma terminal_seven_hundreds_eliminated {v : ℕ} (hv : v % 10 = 7) :
    ¬ UsesDigits (2 * (7 + 100 * v) + 10 * (7 + 100 * v) ^ 2) := by
  intro hdig
  have hu := hundreds_u_congr hv
  have hmod : (2 * (7 + 100 * v) + 10 * (7 + 100 * v) ^ 2) % 1000 = 904 := by
    simpa using window_mod (u := 7 + 100 * v) (M := 1000) (A := 707) (B := 904) hu (by decide)
  have hdigit : ((2 * (7 + 100 * v) + 10 * (7 + 100 * v) ^ 2) / 10 ^ 2) % 10 = 9 := by omega
  exact forbidden_at_two hdig hdigit (by decide)

/-- In the surviving tens branch, tens digit `1` of `v` forces digit `6`. -/
lemma tens_branch_second_one_eliminated {v : ℕ}
    (hv : v % 10 = 7) (ha : (v / 10) % 10 = 1) :
    ¬ UsesDigits (2 * (7 + 10 * v) + 10 * (7 + 10 * v) ^ 2) := by
  intro hdig
  have hu : (7 + 10 * v) ≡ 177 [MOD 1000] := by
    change (7 + 10 * v) % 1000 = 177 % 1000
    omega
  have hmod : (2 * (7 + 10 * v) + 10 * (7 + 10 * v) ^ 2) % 1000 = 644 := by
    simpa using window_mod (u := 7 + 10 * v) (M := 1000) (A := 177) (B := 644) hu (by decide)
  have hdigit : ((2 * (7 + 10 * v) + 10 * (7 + 10 * v) ^ 2) / 10 ^ 2) % 10 = 6 := by omega
  exact forbidden_at_two hdig hdigit (by decide)

/-- In the surviving tens branch, tens digit `4` of `v` forces digit `2`. -/
lemma tens_branch_second_four_eliminated {v : ℕ}
    (hv : v % 10 = 7) (ha : (v / 10) % 10 = 4) :
    ¬ UsesDigits (2 * (7 + 10 * v) + 10 * (7 + 10 * v) ^ 2) := by
  intro hdig
  have hu : (7 + 10 * v) ≡ 477 [MOD 1000] := by
    change (7 + 10 * v) % 1000 = 477 % 1000
    omega
  have hmod : (2 * (7 + 10 * v) + 10 * (7 + 10 * v) ^ 2) % 1000 = 244 := by
    simpa using window_mod (u := 7 + 10 * v) (M := 1000) (A := 477) (B := 244) hu (by decide)
  have hdigit : ((2 * (7 + 10 * v) + 10 * (7 + 10 * v) ^ 2) / 10 ^ 2) % 10 = 2 := by omega
  exact forbidden_at_two hdig hdigit (by decide)

/-- In the surviving tens branch, tens digit `7` of `v` forces digit `8`. -/
lemma tens_branch_second_seven_eliminated {v : ℕ}
    (hv : v % 10 = 7) (ha : (v / 10) % 10 = 7) :
    ¬ UsesDigits (2 * (7 + 10 * v) + 10 * (7 + 10 * v) ^ 2) := by
  intro hdig
  have hu : (7 + 10 * v) ≡ 777 [MOD 1000] := by
    change (7 + 10 * v) % 1000 = 777 % 1000
    omega
  have hmod : (2 * (7 + 10 * v) + 10 * (7 + 10 * v) ^ 2) % 1000 = 844 := by
    simpa using window_mod (u := 7 + 10 * v) (M := 1000) (A := 777) (B := 844) hu (by decide)
  have hdigit : ((2 * (7 + 10 * v) + 10 * (7 + 10 * v) ^ 2) / 10 ^ 2) % 10 = 8 := by omega
  exact forbidden_at_two hdig hdigit (by decide)

/-- In the surviving hundreds branch, tens digit `1` of `v` forces digit `6`. -/
lemma hundreds_branch_second_one_eliminated {v : ℕ}
    (hv : v % 10 = 1) (ha : (v / 10) % 10 = 1) :
    ¬ UsesDigits (2 * (7 + 100 * v) + 10 * (7 + 100 * v) ^ 2) := by
  intro hdig
  have hu : (7 + 100 * v) ≡ 1107 [MOD 10000] := by
    change (7 + 100 * v) % 10000 = 1107 % 10000
    omega
  have hmod : (2 * (7 + 100 * v) + 10 * (7 + 100 * v) ^ 2) % 10000 = 6704 := by
    simpa using window_mod (u := 7 + 100 * v) (M := 10000) (A := 1107) (B := 6704) hu (by decide)
  have hdigit : ((2 * (7 + 100 * v) + 10 * (7 + 100 * v) ^ 2) / 10 ^ 3) % 10 = 6 := by omega
  exact forbidden_at_three hdig hdigit (by decide)

/-- In the surviving hundreds branch, tens digit `4` of `v` forces digit `2`. -/
lemma hundreds_branch_second_four_eliminated {v : ℕ}
    (hv : v % 10 = 1) (ha : (v / 10) % 10 = 4) :
    ¬ UsesDigits (2 * (7 + 100 * v) + 10 * (7 + 100 * v) ^ 2) := by
  intro hdig
  have hu : (7 + 100 * v) ≡ 4107 [MOD 10000] := by
    change (7 + 100 * v) % 10000 = 4107 % 10000
    omega
  have hmod : (2 * (7 + 100 * v) + 10 * (7 + 100 * v) ^ 2) % 10000 = 2704 := by
    simpa using window_mod (u := 7 + 100 * v) (M := 10000) (A := 4107) (B := 2704) hu (by decide)
  have hdigit : ((2 * (7 + 100 * v) + 10 * (7 + 100 * v) ^ 2) / 10 ^ 3) % 10 = 2 := by omega
  exact forbidden_at_three hdig hdigit (by decide)

/-- In the surviving hundreds branch, tens digit `7` of `v` forces digit `8`. -/
lemma hundreds_branch_second_seven_eliminated {v : ℕ}
    (hv : v % 10 = 1) (ha : (v / 10) % 10 = 7) :
    ¬ UsesDigits (2 * (7 + 100 * v) + 10 * (7 + 100 * v) ^ 2) := by
  intro hdig
  have hu : (7 + 100 * v) ≡ 7107 [MOD 10000] := by
    change (7 + 100 * v) % 10000 = 7107 % 10000
    omega
  have hmod : (2 * (7 + 100 * v) + 10 * (7 + 100 * v) ^ 2) % 10000 = 8704 := by
    simpa using window_mod (u := 7 + 100 * v) (M := 10000) (A := 7107) (B := 8704) hu (by decide)
  have hdigit : ((2 * (7 + 100 * v) + 10 * (7 + 100 * v) ^ 2) / 10 ^ 3) % 10 = 8 := by omega
  exact forbidden_at_three hdig hdigit (by decide)

/-- The surviving tens-position carry core: terminal digit `7`. -/
def H1 : Prop := ∀ v : ℕ, 10 ≤ v → v % 100 = 7 → UsesDigits v →
    let u := 7 + 10 * v
    ¬ UsesDigits (2 * u + 10 * u ^ 2)

/-- The surviving hundreds-position carry core: terminal digit `1`. -/
def H2 : Prop := ∀ v : ℕ, 10 ≤ v → v % 100 = 1 → UsesDigits v →
    let u := 7 + 10 ^ 2 * v
    ¬ UsesDigits (2 * u + 10 * u ^ 2)

theorem main : H1 → H2 → OMA.R_oeis_a136863_R1.H1 := by
  intro h17 h21 d v hd1 hd2 hv hv0 hdig
  have hm := OMA.R_oeis_a136863_R1.last_ok hdig
  rcases hm with h0 | h1' | h4' | h7'
  · omega
  · have hd : d = 1 ∨ d = 2 := by omega
    rcases hd with rfl | rfl
    · change ¬ UsesDigits (2 * (7 + 10 * v) + 10 * (7 + 10 * v) ^ 2)
      exact terminal_one_tens_eliminated h1'
    · change ¬ UsesDigits (2 * (7 + 100 * v) + 10 * (7 + 100 * v) ^ 2)
      have ha := OMA.R_oeis_a136863_R1.last_ok (OMA.R_oeis_a136863_R1.div_one_ok hdig)
      rcases ha with ha0 | ha1 | ha4 | ha7
      · exact h21 v hv (by omega) hdig
      · exact hundreds_branch_second_one_eliminated h1' ha1
      · exact hundreds_branch_second_four_eliminated h1' ha4
      · exact hundreds_branch_second_seven_eliminated h1' ha7
  · have hd : d = 1 ∨ d = 2 := by omega
    rcases hd with rfl | rfl
    · change ¬ UsesDigits (2 * (7 + 10 * v) + 10 * (7 + 10 * v) ^ 2)
      exact terminal_four_tens_eliminated h4'
    · change ¬ UsesDigits (2 * (7 + 100 * v) + 10 * (7 + 100 * v) ^ 2)
      exact terminal_four_hundreds_eliminated h4'
  · have hd : d = 1 ∨ d = 2 := by omega
    rcases hd with rfl | rfl
    · change ¬ UsesDigits (2 * (7 + 10 * v) + 10 * (7 + 10 * v) ^ 2)
      have ha := OMA.R_oeis_a136863_R1.last_ok (OMA.R_oeis_a136863_R1.div_one_ok hdig)
      rcases ha with ha0 | ha1 | ha4 | ha7
      · exact h17 v hv (by omega) hdig
      · exact tens_branch_second_one_eliminated h7' ha1
      · exact tens_branch_second_four_eliminated h7' ha4
      · exact tens_branch_second_seven_eliminated h7' ha7
    · change ¬ UsesDigits (2 * (7 + 100 * v) + 10 * (7 + 100 * v) ^ 2)
      exact terminal_seven_hundreds_eliminated h7'

end OMA.R_oeis_a136863_R1_H1_R1
