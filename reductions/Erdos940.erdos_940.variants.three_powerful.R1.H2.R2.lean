import OMAReductions.R_Erdos940_erdos_940_variants_three_powerful_R1
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Padics.Hensel

-- Reduction Erdos940.erdos_940.variants.three_powerful.R1.H2.R2 of step Erdos940.erdos_940.variants.three_powerful.R1.H2
-- Credit: @kumagi

/-!
Apply the eventual primitive local-to-global consequence of Theorem 1 of B. Z. Moroz,
On the representation of large integers by integral ternary positive definite quadratic forms,
Astérisque 209 (1992), pp. 275–278.
https://www.numdam.org/item/AST_1992__209__275_0/

Theorem 2 of that paper strips up to three factors of 5, then rescales a pair of
squares. The lemmas below formalize this step and verify the local conditions
using Hensel's lemma. The two hypotheses are the remaining analytic input for
coefficient 125 and for the smaller coefficients after descent, respectively.
-/
namespace OMA.R_Erdos940_erdos_940_variants_three_powerful_R1_H2_R2

open Filter Polynomial

private lemma hensel_square {p : ℕ} [Fact p.Prime] {t r : ℤ}
    (h : ‖((r ^ 2 - t : ℤ) : ℤ_[p])‖ < ‖((2 * r : ℤ) : ℤ_[p])‖ ^ 2) :
    ∃ a : ℤ_[p], a ^ 2 = t ∧ ‖a‖ = ‖(r : ℤ_[p])‖ := by
  let f : ℤ_[p][X] := X ^ 2 - C (t : ℤ_[p])
  have eval (x : ℤ_[p]) : f.aeval x = x ^ 2 - t := by simp [f]
  have deriv (x : ℤ_[p]) : f.derivative.aeval x = 2 * x := by
    simp [f, derivative_pow]
  have hh : ‖f.aeval (r : ℤ_[p])‖ < ‖f.derivative.aeval (r : ℤ_[p])‖ ^ 2 := by
    simpa only [eval, deriv, Int.cast_sub, Int.cast_pow, Int.cast_mul, Int.cast_ofNat] using h
  obtain ⟨a, ha, _, hn, _⟩ := hensels_lemma hh
  refine ⟨a, sub_eq_zero.mp (by simpa only [eval] using ha), ?_⟩
  rw [deriv, deriv, norm_mul, norm_mul] at hn
  exact mul_left_cancel₀ (norm_ne_zero_iff.mpr (by norm_num)) hn

private lemma odd_padic_square {p : ℕ} [hp : Fact p.Prime] {t : ℤ} {r : ℕ}
    (hp2 : p ≠ 2) (hr : ¬ p ∣ r) (h : (r : ℤ) ^ 2 ≡ t [ZMOD p]) :
    ∃ a : ℤ_[p], a ^ 2 = t ∧ ‖a‖ = 1 := by
  have hrNorm : ‖(r : ℤ_[p])‖ = 1 :=
    PadicInt.norm_natCast_eq_one_iff.mpr (hp.1.coprime_iff_not_dvd.mpr hr)
  have hTwo : ‖(2 : ℤ_[p])‖ = 1 := by
    apply (PadicInt.norm_natCast_eq_one_iff (p := p) (n := 2)).mpr
    apply hp.1.coprime_iff_not_dvd.mpr
    exact fun hd => hp2 ((Nat.prime_dvd_prime_iff_eq hp.1 Nat.prime_two).mp hd)
  have hSmall : ‖((((r : ℤ) ^ 2 - t) : ℤ) : ℤ_[p])‖ < 1 :=
    (PadicInt.norm_int_lt_one_iff_dvd _).mpr (Int.modEq_iff_dvd.mp h.symm)
  have hh : ‖((((r : ℤ) ^ 2 - t) : ℤ) : ℤ_[p])‖ <
      ‖((2 * (r : ℤ) : ℤ) : ℤ_[p])‖ ^ 2 := by
    simpa [Int.cast_mul, norm_mul, hTwo, hrNorm] using hSmall
  simpa [hrNorm] using hensel_square hh

private lemma two_padic_square {t : ℤ} (h : t ≡ 1 [ZMOD 8]) :
    ∃ a : ℤ_[2], a ^ 2 = t ∧ ‖a‖ = 1 := by
  have hnorm : ‖((1 - t : ℤ) : ℤ_[2])‖ ≤ (2 : ℝ) ^ (-(3 : ℕ) : ℤ) := by
    apply PadicInt.norm_int_le_pow_iff_dvd.mpr
    exact Int.modEq_iff_dvd.mp h
  have hTwo : ‖(2 : ℤ_[2])‖ = (2 : ℝ)⁻¹ := PadicInt.norm_p (p := 2)
  have hh : ‖((1 ^ 2 - t : ℤ) : ℤ_[2])‖ < ‖((2 * 1 : ℤ) : ℤ_[2])‖ ^ 2 := by
    simp only [one_pow, mul_one, Int.cast_ofNat, hTwo]
    exact hnorm.trans_lt (by norm_num)
  simpa using hensel_square hh

private lemma odd_padic_binary {p : ℕ} [hp : Fact p.Prime] {t : ℤ}
    (hp2 : p ≠ 2) (ht : ¬ (p : ℤ) ∣ t) :
    ∃ a b : ℤ_[p], a ^ 2 + b ^ 2 = t ∧ (‖a‖ = 1 ∨ ‖b‖ = 1) := by
  obtain ⟨x, y, _, _, hxy⟩ := Nat.sq_add_sq_zmodEq p t
  have someUnit : ¬ p ∣ x ∨ ¬ p ∣ y := by
    by_contra! h
    have hx : (p : ℤ) ∣ (x : ℤ) := by exact_mod_cast h.1
    have hy : (p : ℤ) ∣ (y : ℤ) := by exact_mod_cast h.2
    exact ht (hxy.dvd_iff.mp (by
      simpa only [pow_two] using dvd_add (dvd_mul_of_dvd_left hx x) (dvd_mul_of_dvd_left hy y)))
  rcases someUnit with hx | hy
  · have hm : (x : ℤ) ^ 2 ≡ t - (y : ℤ) ^ 2 [ZMOD p] := by
      convert hxy.sub_right ((y : ℤ) ^ 2) using 1
      ring
    obtain ⟨a, ha, hu⟩ := odd_padic_square hp2 hx hm
    exact ⟨a, y, by push_cast at ha; linear_combination ha, Or.inl hu⟩
  · have hm : (y : ℤ) ^ 2 ≡ t - (x : ℤ) ^ 2 [ZMOD p] := by
      rw [add_comm] at hxy
      convert hxy.sub_right ((x : ℤ) ^ 2) using 1
      ring
    obtain ⟨b, hb, hu⟩ := odd_padic_square hp2 hy hm
    exact ⟨x, b, by push_cast at hb; linear_combination hb, Or.inr hu⟩

/-- A primitive local representation for the four forms in Moroz's descent. -/
private lemma primitive_padic {e n : ℕ} (hn5 : ¬ 5 ∣ n ∨ e = 0)
    (hn8 : (n : ℤ) ≡ 2 + 5 ^ e [ZMOD 8]) (p : ℕ) [hp : Fact p.Prime] :
    ∃ x y z : ℤ_[p], x ^ 2 + y ^ 2 + (5 : ℤ_[p]) ^ e * z ^ 2 = n ∧
      (‖x‖ = 1 ∨ ‖y‖ = 1 ∨ ‖z‖ = 1) := by
  by_cases hp2 : p = 2
  · subst p
    have hm : (n : ℤ) - 1 - 5 ^ e ≡ 1 [ZMOD 8] := by
      convert (hn8.sub_right 1).sub_right (5 ^ e) using 1
      ring
    obtain ⟨a, ha, hu⟩ := two_padic_square hm
    exact ⟨a, 1, 1, by push_cast at ha; simp; linear_combination ha, Or.inl hu⟩
  · by_cases hpn : (p : ℤ) ∣ (n : ℤ)
    · have hpc : ¬ (p : ℤ) ∣ 5 ^ e := by
        intro hd
        have hNat : p ∣ 5 ^ e := by exact_mod_cast hd
        have hp5 := (Nat.prime_dvd_prime_iff_eq hp.1 (by decide : Nat.Prime 5)).mp
          (hp.1.dvd_of_dvd_pow hNat)
        subst p
        rcases hn5 with hn5 | rfl
        · exact hn5 (by exact_mod_cast hpn)
        · norm_num at hNat
      have ht : ¬ (p : ℤ) ∣ (n : ℤ) - 5 ^ e := by
        intro hd
        apply hpc
        have hdiff := dvd_sub hpn hd
        rwa [show (n : ℤ) - ((n : ℤ) - 5 ^ e) = 5 ^ e by ring] at hdiff
      obtain ⟨a, b, hab, hu⟩ := odd_padic_binary hp2 ht
      exact ⟨a, b, 1, by push_cast at hab; simp; linear_combination hab, by tauto⟩
    · obtain ⟨a, b, hab, hu⟩ := odd_padic_binary hp2 hpn
      exact ⟨a, b, 0, by simpa using hab, by tauto⟩

private lemma strip_fives (n : ℕ) :
    ∃ k m : ℕ, k ≤ 3 ∧ n = 5 ^ k * m ∧ (¬ 5 ∣ m ∨ k = 3) := by
  by_cases h₀ : 5 ∣ n
  · obtain ⟨n₁, hn₁⟩ := h₀
    by_cases h₁ : 5 ∣ n₁
    · obtain ⟨n₂, hn₂⟩ := h₁
      by_cases h₂ : 5 ∣ n₂
      · obtain ⟨n₃, hn₃⟩ := h₂
        exact ⟨3, n₃, by decide, by rw [hn₁, hn₂, hn₃]; ring, Or.inr rfl⟩
      · exact ⟨2, n₂, by decide, by rw [hn₁, hn₂]; ring, Or.inl h₂⟩
    · exact ⟨1, n₁, by decide, by simpa using hn₁, Or.inl h₁⟩
  · exact ⟨0, n, by decide, by simp, Or.inl h₀⟩

private lemma descended_residue {n k m : ℕ} (hk : k ≤ 3) (he : n = 5 ^ k * m)
    (h : n % 8 = 7) : (m : ℤ) ≡ 2 + 5 ^ (3 - k) [ZMOD 8] := by
  have hm : (5 : ℤ) ^ k * (m : ℤ) ≡ 7 [ZMOD 8] := by
    have hm' : (n : ℤ) ≡ 7 [ZMOD 8] := by
      exact_mod_cast (show n ≡ 7 [MOD 8] by exact h)
    simpa [he] using hm'
  have hSquare : ((5 : ℤ) ^ k) ^ 2 ≡ 1 [ZMOD 8] := by
    interval_cases k <;> decide
  have hCoeff : (5 : ℤ) ^ k * 7 ≡ 2 + 5 ^ (3 - k) [ZMOD 8] := by
    interval_cases k <;> decide
  have hLeft : (5 : ℤ) ^ k * ((5 : ℤ) ^ k * (m : ℤ)) ≡ (m : ℤ) [ZMOD 8] := by
    convert hSquare.mul_right (m : ℤ) using 1 <;> ring
  exact hLeft.symm.trans ((hm.mul_left ((5 : ℤ) ^ k)).trans hCoeff)

private lemma lift_form {m k : ℕ} (hk : k ≤ 3) {x y z : ℤ}
    (h : x ^ 2 + y ^ 2 + (5 : ℤ) ^ (3 - k) * z ^ 2 = m) :
    ∃ a b : ℤ, a ^ 2 + b ^ 2 + 125 * z ^ 2 = (5 : ℤ) ^ k * m := by
  have hPow : (5 : ℤ) ^ k * (5 : ℤ) ^ (3 - k) = 125 := by
    rw [← pow_add, show k + (3 - k) = 3 by omega]
    norm_num
  have hPair : ∀ j : ℕ, ∃ a b : ℤ, a ^ 2 + b ^ 2 = 5 ^ j * (x ^ 2 + y ^ 2) := by
    intro j
    induction j with
    | zero => exact ⟨x, y, by simp⟩
    | succ j ih =>
      obtain ⟨a, b, hab⟩ := ih
      refine ⟨a - 2 * b, 2 * a + b, ?_⟩
      rw [pow_succ]
      linear_combination 5 * hab
  obtain ⟨a, b, hab⟩ := hPair k
  refine ⟨a, b, ?_⟩
  rw [hab, ← hPow, ← h]
  ring

/-- Moroz's descent from the four forms at odd arguments prime to their determinant. -/
private lemma eventually_form125
    (global : ∀ e ≤ 3, ∀ᶠ m : ℕ in atTop, Odd m → (¬ 5 ∣ m ∨ e = 0) →
      (∀ (p : ℕ) [Fact p.Prime], ∃ x y z : ℤ_[p],
        x ^ 2 + y ^ 2 + (5 : ℤ_[p]) ^ e * z ^ 2 = m ∧
        (‖x‖ = 1 ∨ ‖y‖ = 1 ∨ ‖z‖ = 1)) →
      ∃ x y z : ℤ, x ^ 2 + y ^ 2 + 5 ^ e * z ^ 2 = m) :
    ∀ᶠ n : ℕ in atTop, n % 8 = 7 →
      ∃ x y z : ℤ, x ^ 2 + y ^ 2 + 125 * z ^ 2 = n := by
  obtain ⟨N₀, h₀⟩ := eventually_atTop.mp (global 0 (by decide))
  obtain ⟨N₁, h₁⟩ := eventually_atTop.mp (global 1 (by decide))
  obtain ⟨N₂, h₂⟩ := eventually_atTop.mp (global 2 (by decide))
  obtain ⟨N₃, h₃⟩ := eventually_atTop.mp (global 3 (by decide))
  let N := N₀ + N₁ + N₂ + N₃
  refine eventually_atTop.mpr ⟨125 * N, ?_⟩
  intro n hn hn8
  obtain ⟨k, m, hk, he, hm5⟩ := strip_fives n
  have hm : N ≤ m := by
    have hkm : 5 ^ k * m ≤ 125 * m :=
      Nat.mul_le_mul_right m (by interval_cases k <;> decide)
    omega
  have hmOdd : Odd m :=
    (Nat.odd_iff.mpr (by omega : n % 2 = 1)).of_dvd_nat ⟨5 ^ k, by rw [he, mul_comm]⟩
  have hCoprime : ¬ 5 ∣ m ∨ 3 - k = 0 := by omega
  have hLocal : ∀ (p : ℕ) [Fact p.Prime], ∃ x y z : ℤ_[p],
      x ^ 2 + y ^ 2 + (5 : ℤ_[p]) ^ (3 - k) * z ^ 2 = m ∧
      (‖x‖ = 1 ∨ ‖y‖ = 1 ∨ ‖z‖ = 1) :=
    fun p _ => primitive_padic hCoprime (descended_residue hk he hn8) p
  have hGlobal : ∃ x y z : ℤ, x ^ 2 + y ^ 2 + 5 ^ (3 - k) * z ^ 2 = m := by
    have hm₀ : N₀ ≤ m := by dsimp [N] at hm; omega
    have hm₁ : N₁ ≤ m := by dsimp [N] at hm; omega
    have hm₂ : N₂ ≤ m := by dsimp [N] at hm; omega
    have hm₃ : N₃ ≤ m := by dsimp [N] at hm; omega
    interval_cases k
    · exact h₃ m hm₃ hmOdd hCoprime hLocal
    · exact h₂ m hm₂ hmOdd hCoprime hLocal
    · exact h₁ m hm₁ hmOdd hCoprime hLocal
    · exact h₀ m hm₀ hmOdd hCoprime hLocal
  obtain ⟨x, y, z, hxyz⟩ := hGlobal
  obtain ⟨a, b, hab⟩ := lift_form hk hxyz
  exact ⟨a, b, z, by simpa [he] using hab⟩

/-- The eventual local-to-global implication for coefficient 125. -/
def H1 : Prop :=
  ∀ᶠ m : ℕ in atTop, Odd m → ¬ 5 ∣ m →
    (∀ (p : ℕ) [Fact p.Prime], ∃ x y z : ℤ_[p],
      x ^ 2 + y ^ 2 + (5 : ℤ_[p]) ^ (3 : ℕ) * z ^ 2 = m ∧
      (‖x‖ = 1 ∨ ‖y‖ = 1 ∨ ‖z‖ = 1)) →
    ∃ x y z : ℤ, x ^ 2 + y ^ 2 + 5 ^ (3 : ℕ) * z ^ 2 = m

/-- The eventual local-to-global implication for coefficients 1, 5 and 25. -/
def H2 : Prop :=
  ∀ e : ℕ, e ≤ 2 → ∀ᶠ m : ℕ in atTop, Odd m → (¬ 5 ∣ m ∨ e = 0) →
    (∀ (p : ℕ) [Fact p.Prime], ∃ x y z : ℤ_[p],
      x ^ 2 + y ^ 2 + (5 : ℤ_[p]) ^ e * z ^ 2 = m ∧
      (‖x‖ = 1 ∨ ‖y‖ = 1 ∨ ‖z‖ = 1)) →
    ∃ x y z : ℤ, x ^ 2 + y ^ 2 + 5 ^ e * z ^ 2 = m

private lemma full_125_mul_sq (z : ℕ) : Nat.Full 2 (125 * z ^ 2) := by
  intro p hp
  obtain ⟨hp, hd, _⟩ := Nat.mem_primeFactors.mp hp
  rcases hp.dvd_mul.mp hd with hc | hz
  · change p ∣ 5 ^ 3 at hc
    have he := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5)).mp
      (hp.dvd_of_dvd_pow hc)
    subst p
    exact dvd_mul_of_dvd_left (by decide : 5 ^ 2 ∣ 125) _
  · exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd (hp.dvd_of_dvd_pow hz) 2) _

theorem main : H1 → H2 → OMA.R_Erdos940_erdos_940_variants_three_powerful_R1.H2 := by
  intro large125 small
  have global : ∀ e ≤ 3, ∀ᶠ m : ℕ in atTop, Odd m → (¬ 5 ∣ m ∨ e = 0) →
      (∀ (p : ℕ) [Fact p.Prime], ∃ x y z : ℤ_[p],
        x ^ 2 + y ^ 2 + (5 : ℤ_[p]) ^ e * z ^ 2 = m ∧
        (‖x‖ = 1 ∨ ‖y‖ = 1 ∨ ‖z‖ = 1)) →
      ∃ x y z : ℤ, x ^ 2 + y ^ 2 + 5 ^ e * z ^ 2 = m := by
    intro e he
    by_cases he3 : e = 3
    · subst e
      filter_upwards [large125] with m hm ho hm5 hlocal
      exact hm ho (hm5.resolve_right (by decide)) hlocal
    · exact small e (by omega)
  filter_upwards [eventually_form125 global] with n h hn8
  obtain ⟨x, y, z, h⟩ := h hn8
  have hNat : x.natAbs ^ 2 + y.natAbs ^ 2 + 125 * z.natAbs ^ 2 = n := by
    exact_mod_cast (show (x.natAbs : ℤ) ^ 2 + (y.natAbs : ℤ) ^ 2 + 125 * (z.natAbs : ℤ) ^ 2 = n by
      simpa only [Int.natCast_natAbs, sq_abs] using h)
  exact ⟨_, _, _, OMA.R_Erdos940_erdos_940_variants_three_powerful_R1.sq_full x.natAbs,
    OMA.R_Erdos940_erdos_940_variants_three_powerful_R1.sq_full y.natAbs,
    full_125_mul_sq z.natAbs, hNat.symm⟩

end OMA.R_Erdos940_erdos_940_variants_three_powerful_R1_H2_R2
