import OMAReductions.R_Erdos10_erdos_10_variants_gallagher_R1_H2_R1
import Mathlib

-- Reduction Erdos10.erdos_10.variants.gallagher.R1.H2.R1.H1.R1 of step Erdos10.erdos_10.variants.gallagher.R1.H2.R1.H1
-- Credit: @Aijy0264561

/-! Split Gallagher's averaged prime-pair estimate into an analytic and an
arithmetic part, both over the explicit family `Q(k, M)` of all `k`-element
sets of binary exponents below `M` (distinct exponents, so the shift sums are
distinct).

* The first hypothesis is the analytic input: averaged over all ordered pairs of
  distinct members of `Q(k, M)`, the correlation of the odd-prime weight at the
  shift difference is at most `(1+η)` times the truncated singular series
  model `N * G_R(d)`, up to `η * N * |Q|²`, once `R` and then `k` are large.
* The second hypothesis is Gallagher's arithmetic lemma: for `k` large the mean
  of `G_R` over shift differences of `Q(k, M)` is at most `1 + ε` for all large
  `M`. Here `G_R(d)` is the product over primes `2 < p ≤ R` of `p/(p-1)` when
  `p ∣ d` and `p(p-2)/(p-1)²` otherwise; each local factor has mean `1` over
  the residues mod `p`, and `k`-fold binary sums equidistribute modulo every
  odd modulus as `k` grows (their differences form an aperiodic random walk).

`main` chooses `M = log₂ (N / c)` for a constant `c` depending on `k` and `ε`,
checks the size conditions of the target and chains the two bounds. -/

open Finset Filter Real
open scoped Classical

namespace OMA.R_Erdos10_erdos_10_variants_gallagher_R1_H2_R1_H1_R1

/-- Analytic input: prime-pair correlations averaged over differences of
`k`-fold binary sums follow the truncated singular series model. -/
def H1 : Prop :=
  let v := fun j : ℕ => if (2*j+1).Prime then Real.log (2*j+1 : ℕ)/2 else 0
  let s : Multiset ℕ → ℕ := fun t => (t.map (fun i : ℕ => 2^i)).sum
  let G : ℕ → ℕ → ℝ := fun R d =>
    ∏ p ∈ (Finset.range (R+1)).filter (fun p => p.Prime ∧ 2 < p),
      (if p ∣ d then (p:ℝ)/((p:ℝ)-1) else (p:ℝ)*((p:ℝ)-2)/((p:ℝ)-1)^2)
  ∀ η : ℝ, 0 < η → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
    ∀ᶠ N : ℕ in atTop, ∀ M : ℕ, k*2^M ≤ N → N ≤ 4^M →
      let Q : Finset (Multiset ℕ) := ((Finset.range M).powersetCard k).image Finset.val
      (∑ t ∈ Q, ∑ u ∈ Q.erase t, ∑ j ∈ Finset.range N, v j*v (j+Nat.dist (s t) (s u))) ≤
        (1+η)*N*(∑ t ∈ Q, ∑ u ∈ Q.erase t, G R (Nat.dist (s t) (s u))) + η*N*(Q.card:ℝ)^2

/-- Arithmetic input (Gallagher): the truncated singular series has mean at most
`1 + ε` over differences of `k`-fold binary sums, for some large `k`. -/
def H2 : Prop :=
  let s : Multiset ℕ → ℕ := fun t => (t.map (fun i : ℕ => 2^i)).sum
  let G : ℕ → ℕ → ℝ := fun R d =>
    ∏ p ∈ (Finset.range (R+1)).filter (fun p => p.Prime ∧ 2 < p),
      (if p ∣ d then (p:ℝ)/((p:ℝ)-1) else (p:ℝ)*((p:ℝ)-2)/((p:ℝ)-1)^2)
  ∀ ε : ℝ, 0 < ε → ∀ R k₁ : ℕ, ∃ k : ℕ, k₁ ≤ k ∧ ∀ᶠ M : ℕ in atTop,
    let Q : Finset (Multiset ℕ) := ((Finset.range M).powersetCard k).image Finset.val
    (∑ t ∈ Q, ∑ u ∈ Q.erase t, G R (Nat.dist (s t) (s u))) ≤ (1+ε)*(Q.card:ℝ)^2

lemma card_family (M k : ℕ) :
    (((Finset.range M).powersetCard k).image Finset.val).card = M.choose k := by
  rw [card_image_of_injective _ Finset.val_injective, card_powersetCard, card_range]

lemma injOn_family (M k : ℕ) :
    Set.InjOn (fun t : Multiset ℕ => (t.map (fun i : ℕ => 2^i)).sum)
      ↑(((Finset.range M).powersetCard k).image Finset.val) := by
  intro x hx y hy hxy
  simp only [coe_image, Set.mem_image, mem_coe] at hx hy
  obtain ⟨A, -, rfl⟩ := hx
  obtain ⟨B, -, rfl⟩ := hy
  have h : ∑ i ∈ A, 2^i = ∑ i ∈ B, 2^i := hxy
  rw [Finset.geomSum_injective (le_refl 2) h]

lemma mem_family {M k : ℕ} {t : Multiset ℕ}
    (ht : t ∈ ((Finset.range M).powersetCard k).image Finset.val) :
    Multiset.card t = k ∧ (t.map (fun i : ℕ => 2^i)).sum ≤ k * 2^M := by
  obtain ⟨A, hA, rfl⟩ := mem_image.1 ht
  obtain ⟨hAM, hAk⟩ := mem_powersetCard.1 hA
  refine ⟨by rw [Finset.card_val, hAk], ?_⟩
  have h : (A.val.map (fun i : ℕ => 2^i)).sum = ∑ i ∈ A, 2^i := rfl
  rw [h, ← hAk, ← smul_eq_mul]
  exact Finset.sum_le_card_nsmul A _ _ fun i hi =>
    Nat.pow_le_pow_right (by norm_num) (le_of_lt (mem_range.1 (hAM hi)))

lemma log_le_of_le_four_pow {N M : ℕ} (h : N ≤ 4^M) :
    Real.log (2*(N:ℝ)+1) ≤ 2*((M:ℝ)+1) := by
  have hN : (N:ℝ) ≤ 4^M := by exact_mod_cast h
  have h1 : (1:ℝ) ≤ 4^M := one_le_pow₀ (by norm_num)
  have h2 : 2*(N:ℝ)+1 ≤ 4^(M+1) := by rw [pow_succ]; linarith
  have h4 : Real.log 4 ≤ 2 := by
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
    rw [this]; linarith [Real.log_two_lt_d9]
  calc Real.log (2*(N:ℝ)+1) ≤ Real.log (4^(M+1)) := Real.log_le_log (by positivity) h2
    _ = ((M:ℝ)+1) * Real.log 4 := by rw [Real.log_pow]; push_cast; ring
    _ ≤ ((M:ℝ)+1) * 2 := mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = 2*((M:ℝ)+1) := by ring

lemma choose_large {k : ℕ} (hk : 3 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ M : ℕ in atTop, 4*((M:ℝ)+1)^2 ≤ ε * (M.choose k : ℝ) := by
  filter_upwards [eventually_ge_atTop (2*k),
    eventually_ge_atTop (⌈128 * (k.factorial : ℝ) / ε⌉₊ + 1)] with M hM1 hM2
  have hf : (0:ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hMpos : (1:ℝ) ≤ M := by exact_mod_cast (by omega : 1 ≤ M)
  have hMε : 128 * (k.factorial : ℝ) ≤ ε * M := by
    have h1 : 128 * (k.factorial : ℝ) / ε ≤ ⌈128 * (k.factorial : ℝ) / ε⌉₊ := Nat.le_ceil _
    have h2 : ((⌈128 * (k.factorial : ℝ) / ε⌉₊ : ℕ) : ℝ) ≤ (M:ℝ) :=
      Nat.cast_le.mpr (show ⌈128 * (k.factorial : ℝ) / ε⌉₊ ≤ M by omega)
    rw [div_le_iff₀ hε] at h1
    nlinarith
  -- a := M + 1 - k ≥ M / 2 ≥ 1
  set a : ℕ := M + 1 - k with ha
  have haM : (M:ℝ) / 2 ≤ a := by
    have : M ≤ 2 * a := by omega
    have : (M:ℝ) ≤ 2 * a := by exact_mod_cast this
    linarith
  have hM6 : (2:ℝ) ≤ M := by exact_mod_cast (by omega : 2 ≤ M)
  have ha1 : (1:ℝ) ≤ a := by linarith
  have hpow : (a:ℝ)^3 ≤ (a:ℝ)^k := pow_le_pow_right₀ ha1 hk
  have hch : ((a:ℝ)^k) / k.factorial ≤ M.choose k := by
    have := Nat.pow_le_choose (α := ℝ) k M
    simpa [ha] using this
  have hcube : ((M:ℝ)/2)^3 ≤ (a:ℝ)^3 := pow_le_pow_left₀ (by positivity) haM 3
  have hC : ((M:ℝ)/2)^3 ≤ k.factorial * (M.choose k : ℝ) := by
    rw [div_le_iff₀ hf] at hch
    nlinarith
  -- 4 (M+1)² ≤ 16 M², and 16 M² * 128 k! ≤ 16 M² * ε M = 128 ε (M/2)³ ≤ 128 ε k! C
  have hsq : 4*((M:ℝ)+1)^2 ≤ 16 * (M:ℝ)^2 := by nlinarith
  have hkey : 16 * (M:ℝ)^2 * (128 * k.factorial) ≤ 128 * k.factorial * (ε * (M.choose k : ℝ)) := by
    have e1 : 16 * (M:ℝ)^2 * (128 * k.factorial) ≤ 16 * (M:ℝ)^2 * (ε * M) :=
      mul_le_mul_of_nonneg_left hMε (by positivity)
    have e2 : 16 * (M:ℝ)^2 * (ε * M) = 128 * ε * ((M:ℝ)/2)^3 := by ring
    have e3 : 128 * ε * ((M:ℝ)/2)^3 ≤ 128 * ε * (k.factorial * (M.choose k : ℝ)) :=
      mul_le_mul_of_nonneg_left hC (by positivity)
    nlinarith
  have h128 : (0:ℝ) < 128 * k.factorial := by positivity
  have : 16 * (M:ℝ)^2 ≤ ε * (M.choose k : ℝ) := by
    by_contra hcon
    push Not at hcon
    have := mul_lt_mul_of_pos_left hcon h128
    nlinarith
  linarith

theorem main : H1 → H2 → OMA.R_Erdos10_erdos_10_variants_gallagher_R1_H2_R1.H1 := by
  intro hA hB
  unfold OMA.R_Erdos10_erdos_10_variants_gallagher_R1_H2_R1.H1
  unfold H1 at hA
  unfold H2 at hB
  dsimp only at hA hB ⊢
  intro ε hε
  set η : ℝ := min 1 (ε/4) with hηdef
  have hη : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hη4 : η ≤ ε/4 := min_le_right _ _
  obtain ⟨R₀, hR⟩ := hA η hη
  obtain ⟨k₀, hk₀⟩ := hR R₀ le_rfl
  obtain ⟨k, hkk, hBk⟩ := hB η hη R₀ (max k₀ 3)
  have hAk := hk₀ k (le_trans (le_max_left _ _) hkk)
  have hk3 : 3 ≤ k := le_trans (le_max_right _ _) hkk
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.1 hBk
  obtain ⟨M₁, hM₁⟩ := eventually_atTop.1 (choose_large hk3 hε)
  set c : ℕ := k * (⌈1/ε⌉₊ + 1) with hcdef
  have hc : 0 < c := Nat.mul_pos (by omega) (Nat.succ_pos _)
  have hkc : k ≤ c := Nat.le_mul_of_pos_right k (Nat.succ_pos _)
  have hεc : (k:ℝ) ≤ ε * c := by
    have h1 : 1/ε ≤ (⌈1/ε⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : 1 ≤ ε * ((⌈1/ε⌉₊ : ℝ) + 1) := by
      rw [div_le_iff₀ hε] at h1; nlinarith
    have h3 : (c:ℝ) = k * ((⌈1/ε⌉₊ : ℝ) + 1) := by rw [hcdef]; push_cast; ring
    rw [h3]
    have hk0 : (0:ℝ) ≤ k := by positivity
    nlinarith
  set L : ℕ := max (max M₀ M₁) (max (2*k) (2*c)) with hLdef
  refine ⟨k, ?_⟩
  filter_upwards [hAk, eventually_ge_atTop (c * 2^L)] with N hN hNL
  set M : ℕ := Nat.log 2 (N / c) with hMdef
  have hLle : 2^L ≤ N / c := (Nat.le_div_iff_mul_le hc).2 (by rw [mul_comm]; exact hNL)
  have hML : L ≤ M := Nat.le_log_of_pow_le one_lt_two hLle
  have hNc0 : N / c ≠ 0 := by have := Nat.one_le_two_pow (n := L); omega
  have h2M : 2^M ≤ N / c := Nat.pow_log_le_self 2 hNc0
  have hcM : c * 2^M ≤ N := by
    have := (Nat.le_div_iff_mul_le hc).1 h2M; rw [mul_comm]; exact this
  have hkM : k * 2^M ≤ N := le_trans (Nat.mul_le_mul_right _ hkc) hcM
  have hN4 : N ≤ 4^M := by
    have h1 : N < c * (N / c + 1) := by
      have := Nat.div_add_mod N c
      have := Nat.mod_lt N hc
      nlinarith
    have h2 : N / c + 1 ≤ 2^(M+1) := Nat.lt_pow_succ_log_self one_lt_two _
    have h3 : 2*c ≤ 2^M := by
      have a1 : 2*c ≤ L := le_trans (le_max_right _ _) (le_max_right _ _)
      have a2 : L < 2^L := Nat.lt_two_pow_self
      have a3 : 2^L ≤ 2^M := Nat.pow_le_pow_right (by norm_num) hML
      omega
    have h4 : (4:ℕ)^M = 2^M * 2^M := by rw [show (4:ℕ) = 2*2 by rfl, mul_pow]
    rw [h4]
    calc N ≤ c * (N / c + 1) := h1.le
      _ ≤ c * 2^(M+1) := Nat.mul_le_mul_left _ h2
      _ = (2*c) * 2^M := by rw [pow_succ]; ring
      _ ≤ 2^M * 2^M := Nat.mul_le_mul_right _ h3
  have hkMle : k ≤ M := by
    have : 2*k ≤ L := le_trans (le_max_left _ _) (le_max_right _ _)
    omega
  have hM0 : M₀ ≤ M := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hML
  have hM1 : M₁ ≤ M := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hML
  have hoff := hN M hkM hN4
  have hG := hM₀ M hM0
  have hch := hM₁ M hM1
  refine ⟨((Finset.range M).powersetCard k).image Finset.val, ?_, ?_, injOn_family M k, ?_, ?_⟩
  · rw [← Finset.card_pos, card_family]; exact Nat.choose_pos hkMle
  · intro t ht
    obtain ⟨hcard, hs⟩ := mem_family ht
    refine ⟨hcard.le, ?_⟩
    have hs' : (((t.map (fun i : ℕ => 2^i)).sum : ℕ) : ℝ) ≤ (k:ℝ) * 2^M := by
      have := Nat.cast_le (α := ℝ) |>.mpr hs
      push_cast at this ⊢
      exact this
    have hcM' : (c:ℝ) * 2^M ≤ N := by exact_mod_cast hcM
    have hp : (0:ℝ) ≤ 2^M := by positivity
    calc (((t.map (fun i : ℕ => 2^i)).sum : ℕ) : ℝ) ≤ (k:ℝ) * 2^M := hs'
      _ ≤ ε * c * 2^M := mul_le_mul_of_nonneg_right hεc hp
      _ = ε * (c * 2^M) := by ring
      _ ≤ ε * N := mul_le_mul_of_nonneg_left hcM' hε.le
  · rw [card_family]
    have hl0 : 0 ≤ Real.log (2*(N:ℝ)+1) :=
      Real.log_nonneg (by linarith [show (0:ℝ) ≤ N from Nat.cast_nonneg N])
    have hl := log_le_of_le_four_pow hN4
    calc Real.log (2*(N:ℝ)+1)^2 ≤ (2*((M:ℝ)+1))^2 := pow_le_pow_left₀ hl0 hl 2
      _ = 4*((M:ℝ)+1)^2 := by ring
      _ ≤ ε * (M.choose k : ℝ) := hch
  · set Qc : ℝ := ((((Finset.range M).powersetCard k).image Finset.val).card : ℝ)
    have hN0 : (0:ℝ) ≤ N := by positivity
    have hQ0 : (0:ℝ) ≤ Qc^2 := by positivity
    have e1 := mul_le_mul_of_nonneg_left hG (show (0:ℝ) ≤ (1+η)*N by positivity)
    have e2 : ((1+η)*(1+η) + η) * (N * Qc^2) ≤ (1+ε) * (N * Qc^2) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      nlinarith
    nlinarith

end OMA.R_Erdos10_erdos_10_variants_gallagher_R1_H2_R1_H1_R1
