import OMAReductions.R_OeisA2326_conjecture1_R1

-- Step OeisA2326.conjecture1.R1.H1: hypothesis H1 of reduction OeisA2326.conjecture1.R1
-- uses note #109884
-- Credit: @LiJiaHua1024; adapted from @marcusbuffett (#12421) per @Miura-KR and @JaviSoto

namespace OMA.Step_OeisA2326_conjecture1_R1_H1

def wfOdd : ℕ → ℕ → Bool
  | 0, _ => true
  | f + 1, b =>
    let p := 2 * (b + f) + 53
    ((p % 3 == 0) || (p % 5 == 0) || (p % 7 == 0) || (p % 11 == 0) || (p % 13 == 0) ||
      (p % 17 == 0) || (p % 19 == 0) || (p % 23 == 0) || (p % 29 == 0) || (p % 31 == 0) ||
      (p % 37 == 0) || (p % 41 == 0) || (p % 43 == 0) || (p % 47 == 0) ||
      (2 ^ (p - 1) % p ^ 3 != 1)) && wfOdd f b

lemma wfOdd_spec : ∀ (f b : ℕ), wfOdd f b = true →
    ∀ j, b ≤ j → j < b + f →
      (∀ q ∈ ([3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47] : List ℕ), (2 * j + 53) % q ≠ 0) →
      2 ^ ((2 * j + 53) - 1) % (2 * j + 53) ^ 3 ≠ 1
  | 0, _, _, _, h1, h2, _ => by omega
  | f + 1, b, h, j, h1, h2, hcop => by
    rw [wfOdd, Bool.and_eq_true] at h
    by_cases hj : j = b + f
    · subst hj
      rcases h with ⟨hor, _⟩
      simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne] at hor
      rcases hor with (((((((((((((h3 | h5) | h7) | h11) | h13) | h17) | h19) | h23) | h29) | h31) | h37) | h41) | h43) | h47) | hne
      · exact absurd h3 (hcop 3 (by decide))
      · exact absurd h5 (hcop 5 (by decide))
      · exact absurd h7 (hcop 7 (by decide))
      · exact absurd h11 (hcop 11 (by decide))
      · exact absurd h13 (hcop 13 (by decide))
      · exact absurd h17 (hcop 17 (by decide))
      · exact absurd h19 (hcop 19 (by decide))
      · exact absurd h23 (hcop 23 (by decide))
      · exact absurd h29 (hcop 29 (by decide))
      · exact absurd h31 (hcop 31 (by decide))
      · exact absurd h37 (hcop 37 (by decide))
      · exact absurd h41 (hcop 41 (by decide))
      · exact absurd h43 (hcop 43 (by decide))
      · exact absurd h47 (hcop 47 (by decide))
      · exact hne
    · exact wfOdd_spec f b h.2 j h1 (by omega) hcop

lemma mod_eq_one {p : ℕ} (hp : 2 ≤ p) (h : p ^ 3 ∣ 2 ^ (p - 1) - 1) :
    2 ^ (p - 1) % p ^ 3 = 1 := by
  obtain ⟨k, hk⟩ := h
  have h1 : 1 ≤ 2 ^ (p - 1) := Nat.one_le_two_pow
  have h2 : 2 ^ (p - 1) = p ^ 3 * k + 1 := by omega
  have h3 : 1 < p ^ 3 := Nat.one_lt_pow (by norm_num) (by omega)
  rw [h2, Nat.mul_add_mod, Nat.mod_eq_of_lt h3]

set_option maxRecDepth 20000 in
private def c0 : wfOdd 5000 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c1 : wfOdd 5000 5000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c2 : wfOdd 5000 10000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c3 : wfOdd 5000 15000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c4 : wfOdd 5000 20000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c5 : wfOdd 5000 25000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c6 : wfOdd 5000 30000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c7 : wfOdd 5000 35000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c8 : wfOdd 5000 40000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c9 : wfOdd 5000 45000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c10 : wfOdd 5000 50000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c11 : wfOdd 5000 55000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c12 : wfOdd 5000 60000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c13 : wfOdd 5000 65000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c14 : wfOdd 5000 70000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c15 : wfOdd 5000 75000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c16 : wfOdd 5000 80000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c17 : wfOdd 5000 85000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c18 : wfOdd 5000 90000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c19 : wfOdd 5000 95000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c20 : wfOdd 5000 100000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c21 : wfOdd 5000 105000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c22 : wfOdd 5000 110000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c23 : wfOdd 5000 115000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c24 : wfOdd 5000 120000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c25 : wfOdd 5000 125000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c26 : wfOdd 5000 130000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c27 : wfOdd 5000 135000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c28 : wfOdd 5000 140000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c29 : wfOdd 5000 145000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c30 : wfOdd 5000 150000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c31 : wfOdd 5000 155000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c32 : wfOdd 5000 160000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c33 : wfOdd 5000 165000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c34 : wfOdd 5000 170000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c35 : wfOdd 5000 175000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c36 : wfOdd 5000 180000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c37 : wfOdd 5000 185000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c38 : wfOdd 5000 190000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c39 : wfOdd 5000 195000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c40 : wfOdd 5000 200000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c41 : wfOdd 5000 205000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c42 : wfOdd 5000 210000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c43 : wfOdd 5000 215000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c44 : wfOdd 5000 220000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c45 : wfOdd 5000 225000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c46 : wfOdd 5000 230000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c47 : wfOdd 5000 235000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c48 : wfOdd 5000 240000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c49 : wfOdd 5000 245000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c50 : wfOdd 5000 250000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c51 : wfOdd 5000 255000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c52 : wfOdd 5000 260000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c53 : wfOdd 5000 265000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c54 : wfOdd 5000 270000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c55 : wfOdd 5000 275000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c56 : wfOdd 5000 280000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c57 : wfOdd 5000 285000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c58 : wfOdd 5000 290000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c59 : wfOdd 5000 295000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c60 : wfOdd 5000 300000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c61 : wfOdd 5000 305000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c62 : wfOdd 5000 310000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c63 : wfOdd 5000 315000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c64 : wfOdd 5000 320000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c65 : wfOdd 5000 325000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c66 : wfOdd 5000 330000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c67 : wfOdd 5000 335000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c68 : wfOdd 5000 340000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c69 : wfOdd 5000 345000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c70 : wfOdd 5000 350000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c71 : wfOdd 5000 355000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c72 : wfOdd 5000 360000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c73 : wfOdd 5000 365000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c74 : wfOdd 5000 370000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c75 : wfOdd 5000 375000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c76 : wfOdd 5000 380000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c77 : wfOdd 5000 385000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c78 : wfOdd 5000 390000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c79 : wfOdd 5000 395000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c80 : wfOdd 5000 400000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c81 : wfOdd 5000 405000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c82 : wfOdd 5000 410000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c83 : wfOdd 5000 415000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c84 : wfOdd 5000 420000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c85 : wfOdd 5000 425000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c86 : wfOdd 5000 430000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c87 : wfOdd 5000 435000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c88 : wfOdd 5000 440000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c89 : wfOdd 5000 445000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c90 : wfOdd 5000 450000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c91 : wfOdd 5000 455000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c92 : wfOdd 5000 460000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c93 : wfOdd 5000 465000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c94 : wfOdd 5000 470000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c95 : wfOdd 5000 475000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c96 : wfOdd 5000 480000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c97 : wfOdd 5000 485000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c98 : wfOdd 5000 490000 = true := by decide +kernel
set_option maxRecDepth 20000 in
private def c99 : wfOdd 4974 495000 = true := by decide +kernel

lemma odd_ge53_ne (j : ℕ) (hj : j < 499974)
    (hcop : ∀ q ∈ ([3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47] : List ℕ), (2 * j + 53) % q ≠ 0) :
    2 ^ ((2 * j + 53) - 1) % (2 * j + 53) ^ 3 ≠ 1 := by
  by_cases h_0_100 : j < 250000
  · by_cases h_0_50 : j < 125000
    · by_cases h_0_25 : j < 60000
      · by_cases h_0_12 : j < 30000
        · by_cases h_0_6 : j < 15000
          · by_cases h_0_3 : j < 5000
            · exact wfOdd_spec _ _ c0 j (by omega) (by omega) hcop
            · by_cases h_1_3 : j < 10000
              · exact wfOdd_spec _ _ c1 j (by omega) (by omega) hcop
              · exact wfOdd_spec _ _ c2 j (by omega) (by omega) hcop
          · by_cases h_3_6 : j < 20000
            · exact wfOdd_spec _ _ c3 j (by omega) (by omega) hcop
            · by_cases h_4_6 : j < 25000
              · exact wfOdd_spec _ _ c4 j (by omega) (by omega) hcop
              · exact wfOdd_spec _ _ c5 j (by omega) (by omega) hcop
        · by_cases h_6_12 : j < 45000
          · by_cases h_6_9 : j < 35000
            · exact wfOdd_spec _ _ c6 j (by omega) (by omega) hcop
            · by_cases h_7_9 : j < 40000
              · exact wfOdd_spec _ _ c7 j (by omega) (by omega) hcop
              · exact wfOdd_spec _ _ c8 j (by omega) (by omega) hcop
          · by_cases h_9_12 : j < 50000
            · exact wfOdd_spec _ _ c9 j (by omega) (by omega) hcop
            · by_cases h_10_12 : j < 55000
              · exact wfOdd_spec _ _ c10 j (by omega) (by omega) hcop
              · exact wfOdd_spec _ _ c11 j (by omega) (by omega) hcop
      · by_cases h_12_25 : j < 90000
        · by_cases h_12_18 : j < 75000
          · by_cases h_12_15 : j < 65000
            · exact wfOdd_spec _ _ c12 j (by omega) (by omega) hcop
            · by_cases h_13_15 : j < 70000
              · exact wfOdd_spec _ _ c13 j (by omega) (by omega) hcop
              · exact wfOdd_spec _ _ c14 j (by omega) (by omega) hcop
          · by_cases h_15_18 : j < 80000
            · exact wfOdd_spec _ _ c15 j (by omega) (by omega) hcop
            · by_cases h_16_18 : j < 85000
              · exact wfOdd_spec _ _ c16 j (by omega) (by omega) hcop
              · exact wfOdd_spec _ _ c17 j (by omega) (by omega) hcop
        · by_cases h_18_25 : j < 105000
          · by_cases h_18_21 : j < 95000
            · exact wfOdd_spec _ _ c18 j (by omega) (by omega) hcop
            · by_cases h_19_21 : j < 100000
              · exact wfOdd_spec _ _ c19 j (by omega) (by omega) hcop
              · exact wfOdd_spec _ _ c20 j (by omega) (by omega) hcop
          · by_cases h_21_25 : j < 115000
            · by_cases h_21_23 : j < 110000
              · exact wfOdd_spec _ _ c21 j (by omega) (by omega) hcop
              · exact wfOdd_spec _ _ c22 j (by omega) (by omega) hcop
            · by_cases h_23_25 : j < 120000
              · exact wfOdd_spec _ _ c23 j (by omega) (by omega) hcop
              · exact wfOdd_spec _ _ c24 j (by omega) (by omega) hcop
    · by_cases h_25_50 : j < 185000
      · by_cases h_25_37 : j < 155000
        · by_cases h_25_31 : j < 140000
          · by_cases h_25_28 : j < 130000
            · exact wfOdd_spec _ _ c25 j (by omega) (by omega) hcop
            · by_cases h_26_28 : j < 135000
              · exact wfOdd_spec _ _ c26 j (by omega) (by omega) hcop
              · exact wfOdd_spec _ _ c27 j (by omega) (by omega) hcop
          · by_cases h_28_31 : j < 145000
            · exact wfOdd_spec _ _ c28 j (by omega) (by omega) hcop
            · by_cases h_29_31 : j < 150000
              · exact wfOdd_spec _ _ c29 j (by omega) (by omega) hcop
              · exact wfOdd_spec _ _ c30 j (by omega) (by omega) hcop
        · by_cases h_31_37 : j < 170000
          · by_cases h_31_34 : j < 160000
            · exact wfOdd_spec _ _ c31 j (by omega) (by omega) hcop
            · by_cases h_32_34 : j < 165000
              · exact wfOdd_spec _ _ c32 j (by omega) (by omega) hcop
              · exact wfOdd_spec _ _ c33 j (by omega) (by omega) hcop
          · by_cases h_34_37 : j < 175000
            · exact wfOdd_spec _ _ c34 j (by omega) (by omega) hcop
            · by_cases h_35_37 : j < 180000
              · exact wfOdd_spec _ _ c35 j (by omega) (by omega) hcop
              · exact wfOdd_spec _ _ c36 j (by omega) (by omega) hcop
      · by_cases h_37_50 : j < 215000
        · by_cases h_37_43 : j < 200000
          · by_cases h_37_40 : j < 190000
            · exact wfOdd_spec _ _ c37 j (by omega) (by omega) hcop
            · by_cases h_38_40 : j < 195000
              · exact wfOdd_spec _ _ c38 j (by omega) (by omega) hcop
              · exact wfOdd_spec _ _ c39 j (by omega) (by omega) hcop
          · by_cases h_40_43 : j < 205000
            · exact wfOdd_spec _ _ c40 j (by omega) (by omega) hcop
            · by_cases h_41_43 : j < 210000
              · exact wfOdd_spec _ _ c41 j (by omega) (by omega) hcop
              · exact wfOdd_spec _ _ c42 j (by omega) (by omega) hcop
        · by_cases h_43_50 : j < 230000
          · by_cases h_43_46 : j < 220000
            · exact wfOdd_spec _ _ c43 j (by omega) (by omega) hcop
            · by_cases h_44_46 : j < 225000
              · exact wfOdd_spec _ _ c44 j (by omega) (by omega) hcop
              · exact wfOdd_spec _ _ c45 j (by omega) (by omega) hcop
          · by_cases h_46_50 : j < 240000
            · by_cases h_46_48 : j < 235000
              · exact wfOdd_spec _ _ c46 j (by omega) (by omega) hcop
              · exact wfOdd_spec _ _ c47 j (by omega) (by omega) hcop
            · by_cases h_48_50 : j < 245000
              · exact wfOdd_spec _ _ c48 j (by omega) (by omega) hcop
              · exact wfOdd_spec _ _ c49 j (by omega) (by omega) hcop
  · by_cases h_50_100 : j < 375000
    · by_cases h_50_75 : j < 310000
      · by_cases h_50_62 : j < 280000
        · by_cases h_50_56 : j < 265000
          · by_cases h_50_53 : j < 255000
            · exact wfOdd_spec _ _ c50 j (by omega) (by omega) hcop
            · by_cases h_51_53 : j < 260000
              · exact wfOdd_spec _ _ c51 j (by omega) (by omega) hcop
              · exact wfOdd_spec _ _ c52 j (by omega) (by omega) hcop
          · by_cases h_53_56 : j < 270000
            · exact wfOdd_spec _ _ c53 j (by omega) (by omega) hcop
            · by_cases h_54_56 : j < 275000
              · exact wfOdd_spec _ _ c54 j (by omega) (by omega) hcop
              · exact wfOdd_spec _ _ c55 j (by omega) (by omega) hcop
        · by_cases h_56_62 : j < 295000
          · by_cases h_56_59 : j < 285000
            · exact wfOdd_spec _ _ c56 j (by omega) (by omega) hcop
            · by_cases h_57_59 : j < 290000
              · exact wfOdd_spec _ _ c57 j (by omega) (by omega) hcop
              · exact wfOdd_spec _ _ c58 j (by omega) (by omega) hcop
          · by_cases h_59_62 : j < 300000
            · exact wfOdd_spec _ _ c59 j (by omega) (by omega) hcop
            · by_cases h_60_62 : j < 305000
              · exact wfOdd_spec _ _ c60 j (by omega) (by omega) hcop
              · exact wfOdd_spec _ _ c61 j (by omega) (by omega) hcop
      · by_cases h_62_75 : j < 340000
        · by_cases h_62_68 : j < 325000
          · by_cases h_62_65 : j < 315000
            · exact wfOdd_spec _ _ c62 j (by omega) (by omega) hcop
            · by_cases h_63_65 : j < 320000
              · exact wfOdd_spec _ _ c63 j (by omega) (by omega) hcop
              · exact wfOdd_spec _ _ c64 j (by omega) (by omega) hcop
          · by_cases h_65_68 : j < 330000
            · exact wfOdd_spec _ _ c65 j (by omega) (by omega) hcop
            · by_cases h_66_68 : j < 335000
              · exact wfOdd_spec _ _ c66 j (by omega) (by omega) hcop
              · exact wfOdd_spec _ _ c67 j (by omega) (by omega) hcop
        · by_cases h_68_75 : j < 355000
          · by_cases h_68_71 : j < 345000
            · exact wfOdd_spec _ _ c68 j (by omega) (by omega) hcop
            · by_cases h_69_71 : j < 350000
              · exact wfOdd_spec _ _ c69 j (by omega) (by omega) hcop
              · exact wfOdd_spec _ _ c70 j (by omega) (by omega) hcop
          · by_cases h_71_75 : j < 365000
            · by_cases h_71_73 : j < 360000
              · exact wfOdd_spec _ _ c71 j (by omega) (by omega) hcop
              · exact wfOdd_spec _ _ c72 j (by omega) (by omega) hcop
            · by_cases h_73_75 : j < 370000
              · exact wfOdd_spec _ _ c73 j (by omega) (by omega) hcop
              · exact wfOdd_spec _ _ c74 j (by omega) (by omega) hcop
    · by_cases h_75_100 : j < 435000
      · by_cases h_75_87 : j < 405000
        · by_cases h_75_81 : j < 390000
          · by_cases h_75_78 : j < 380000
            · exact wfOdd_spec _ _ c75 j (by omega) (by omega) hcop
            · by_cases h_76_78 : j < 385000
              · exact wfOdd_spec _ _ c76 j (by omega) (by omega) hcop
              · exact wfOdd_spec _ _ c77 j (by omega) (by omega) hcop
          · by_cases h_78_81 : j < 395000
            · exact wfOdd_spec _ _ c78 j (by omega) (by omega) hcop
            · by_cases h_79_81 : j < 400000
              · exact wfOdd_spec _ _ c79 j (by omega) (by omega) hcop
              · exact wfOdd_spec _ _ c80 j (by omega) (by omega) hcop
        · by_cases h_81_87 : j < 420000
          · by_cases h_81_84 : j < 410000
            · exact wfOdd_spec _ _ c81 j (by omega) (by omega) hcop
            · by_cases h_82_84 : j < 415000
              · exact wfOdd_spec _ _ c82 j (by omega) (by omega) hcop
              · exact wfOdd_spec _ _ c83 j (by omega) (by omega) hcop
          · by_cases h_84_87 : j < 425000
            · exact wfOdd_spec _ _ c84 j (by omega) (by omega) hcop
            · by_cases h_85_87 : j < 430000
              · exact wfOdd_spec _ _ c85 j (by omega) (by omega) hcop
              · exact wfOdd_spec _ _ c86 j (by omega) (by omega) hcop
      · by_cases h_87_100 : j < 465000
        · by_cases h_87_93 : j < 450000
          · by_cases h_87_90 : j < 440000
            · exact wfOdd_spec _ _ c87 j (by omega) (by omega) hcop
            · by_cases h_88_90 : j < 445000
              · exact wfOdd_spec _ _ c88 j (by omega) (by omega) hcop
              · exact wfOdd_spec _ _ c89 j (by omega) (by omega) hcop
          · by_cases h_90_93 : j < 455000
            · exact wfOdd_spec _ _ c90 j (by omega) (by omega) hcop
            · by_cases h_91_93 : j < 460000
              · exact wfOdd_spec _ _ c91 j (by omega) (by omega) hcop
              · exact wfOdd_spec _ _ c92 j (by omega) (by omega) hcop
        · by_cases h_93_100 : j < 480000
          · by_cases h_93_96 : j < 470000
            · exact wfOdd_spec _ _ c93 j (by omega) (by omega) hcop
            · by_cases h_94_96 : j < 475000
              · exact wfOdd_spec _ _ c94 j (by omega) (by omega) hcop
              · exact wfOdd_spec _ _ c95 j (by omega) (by omega) hcop
          · by_cases h_96_100 : j < 490000
            · by_cases h_96_98 : j < 485000
              · exact wfOdd_spec _ _ c96 j (by omega) (by omega) hcop
              · exact wfOdd_spec _ _ c97 j (by omega) (by omega) hcop
            · by_cases h_98_100 : j < 495000
              · exact wfOdd_spec _ _ c98 j (by omega) (by omega) hcop
              · exact wfOdd_spec _ _ c99 j (by omega) (by omega) hcop

lemma prime_mod_ne_zero {q p : ℕ} (hq : q.Prime) (hp : p.Prime) (hlt : q < p) : p % q ≠ 0 := by
  intro hm
  have heq := (Nat.prime_dvd_prime_iff_eq hq hp).mp (Nat.dvd_of_mod_eq_zero hm)
  omega

end OMA.Step_OeisA2326_conjecture1_R1_H1

theorem OMA.solution : OMA.R_OeisA2326_conjecture1_R1.H1 := by
  intro p hp hlt hdvd
  have h2 := hp.two_le
  by_cases hsmall : p < 53
  · interval_cases p <;> revert hp hdvd <;> decide
  · rcases hp.eq_two_or_odd with rfl | hmod2
    · omega
    · let j : ℕ := (p - 53) / 2
      have hpj : p = 2 * j + 53 := by omega
      have hj : j < 499974 := by omega
      have hmod := OMA.Step_OeisA2326_conjecture1_R1_H1.mod_eq_one h2 hdvd
      have hcop : ∀ q ∈ ([3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47] : List ℕ), (2 * j + 53) % q ≠ 0 := by
        intro q hq
        rw [← hpj]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact OMA.Step_OeisA2326_conjecture1_R1_H1.prime_mod_ne_zero (by decide) hp (by omega)
      rw [hpj] at hmod
      exact OMA.Step_OeisA2326_conjecture1_R1_H1.odd_ge53_ne j hj hcop hmod
