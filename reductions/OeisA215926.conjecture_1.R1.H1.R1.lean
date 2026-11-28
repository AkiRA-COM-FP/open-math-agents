import OMAReductions.R_OeisA215926_conjecture_1_R1
import Mathlib

-- Reduction OeisA215926.conjecture_1.R1.H1.R1 of step OeisA215926.conjecture_1.R1.H1
-- Credit: @chinwas

/-!
# Odd almost perfect numbers: squares, and none with at most two prime factors

The parent step says that every odd `k` with `σ(k) = 2k - 1` (an odd *almost perfect* number)
is `k = 1`. This reduction proves two structural facts unconditionally:

1. `isSquare_of_odd_sigma`: if `k` is odd and `σ(k)` is odd then `k` is a perfect square.
   (`σ(k) = ∏ σ(p^e)`, and for odd `p` the sum `1 + p + ⋯ + p^e` is odd iff `e` is even.)
   Since `σ(k) = 2k - 1` is odd, every odd almost perfect number is a square.
2. `not_card_le_two`: there is no odd almost perfect number `k > 1` with at most two distinct
   prime factors.
   * One prime: `σ(p^e)(p - 1) = p^(e+1) - 1` together with `σ(p^e) = 2p^e - 1` gives
     `(p - 2)(p^e - 1) = 0`, impossible for an odd prime `p` and `e ≥ 1`.
   * Two primes `p ≠ q`: the abundancy bound `(p-1)(q-1)σ(k) < pq·k` contradicts
     `σ(k) = 2k - 1`, because `(p-2)(q-2) ≥ 3` for distinct odd primes.

What remains is split by the number of distinct prime factors:
- `H1`: odd squares with exactly three distinct prime factors;
- `H2`: odd squares with at least four distinct prime factors.
-/

namespace OMA.R_OeisA215926_conjecture_1_R1_H1_R1

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- No odd square with exactly three distinct prime factors is almost perfect. -/
def H1 : Prop :=
  ∀ k : ℕ, Odd k → IsSquare k → k.primeFactors.card = 3 → 1 + σ 1 k = 2 * k → False

/-- No odd square with at least four distinct prime factors is almost perfect. -/
def H2 : Prop :=
  ∀ k : ℕ, Odd k → IsSquare k → 4 ≤ k.primeFactors.card → 1 + σ 1 k = 2 * k → False

section Proof

/-- `σ(p^e)·(p - 1) = p^(e+1) - 1`, in `ℤ`. -/
theorem sigma_prime_pow_mul (p e : ℕ) (hp : p.Prime) :
    (σ 1 (p ^ e) : ℤ) * ((p : ℤ) - 1) = (p : ℤ) ^ (e + 1) - 1 := by
  rw [sigma_one_apply_prime_pow hp]
  push_cast
  exact geom_sum_mul _ _

/-- For odd `p`, `1 + p + ⋯ + p^(n-1)` has the parity of `n`. -/
theorem geom_sum_mod_two (p : ℕ) (hp : Odd p) (n : ℕ) :
    (∑ i ∈ Finset.range n, p ^ i) % 2 = n % 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.add_mod, ih, Nat.odd_iff.1 hp.pow]
    omega

/-- If `k` is odd and `σ(k)` is odd, then `k` is a perfect square. -/
theorem isSquare_of_odd_sigma {k : ℕ} (hk : Odd k) (hs : Odd (σ 1 k)) : IsSquare k := by
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk
  have hev : ∀ p ∈ k.primeFactors, Even (k.factorization p) := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpodd : Odd p := hk.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp)
    have hdvd : σ 1 (p ^ k.factorization p) ∣ σ 1 k := by
      rw [IsMultiplicative.multiplicative_factorization (σ 1) isMultiplicative_sigma hk0]
      unfold Finsupp.prod
      exact Finset.dvd_prod_of_mem (fun q => σ 1 (q ^ k.factorization q))
        (by simpa using hp)
    have hodd : Odd (σ 1 (p ^ k.factorization p)) := hs.of_dvd_nat hdvd
    rw [sigma_one_apply_prime_pow hpp, Nat.odd_iff, geom_sum_mod_two p hpodd] at hodd
    rw [Nat.even_iff]
    omega
  refine ⟨∏ p ∈ k.primeFactors, p ^ (k.factorization p / 2), ?_⟩
  rw [← Finset.prod_mul_distrib]
  conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hk0]
  apply Finset.prod_congr rfl
  intro p hp
  rw [← pow_add]
  congr 1
  obtain ⟨r, hr⟩ := hev p hp
  omega

/-- `(p - 2)(q - 2) ≥ 3` for distinct odd primes. -/
theorem prod_sub_two_ge {p q : ℕ} (hp : 3 ≤ p) (hq : 3 ≤ q) (hpo : Odd p) (hqo : Odd q)
    (hpq : p ≠ q) : (3 : ℤ) ≤ ((p : ℤ) - 2) * ((q : ℤ) - 2) := by
  rcases Nat.odd_iff.1 hpo with hp2
  rcases Nat.odd_iff.1 hqo with hq2
  rcases (by omega : p = 3 ∨ 5 ≤ p) with rfl | hp5
  · have : 5 ≤ q := by omega
    have : (5 : ℤ) ≤ q := by exact_mod_cast this
    push_cast; nlinarith
  · have hp5' : (5 : ℤ) ≤ p := by exact_mod_cast hp5
    have hq' : (3 : ℤ) ≤ q := by exact_mod_cast hq
    nlinarith

/-- No odd almost perfect number `k > 1` has at most two distinct prime factors. -/
theorem not_card_le_two {k : ℕ} (hk : Odd k) (hk1 : k ≠ 1) (hc : k.primeFactors.card ≤ 2)
    (h : 1 + σ 1 k = 2 * k) : False := by
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk
  have hdecomp := Nat.prod_primeFactors_pow_factorization hk0
  have hodd_of_mem : ∀ p ∈ k.primeFactors, Odd p :=
    fun p hp => hk.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp)
  have hpos_of_mem : ∀ p ∈ k.primeFactors, 0 < k.factorization p :=
    fun p hp => (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd hk0
      (Nat.dvd_of_mem_primeFactors hp)
  rcases (by omega : k.primeFactors.card = 0 ∨ k.primeFactors.card = 1 ∨
      k.primeFactors.card = 2) with h0 | h1 | h2
  · -- no prime factors: `k = 1`
    rcases Nat.primeFactors_eq_empty.1 (Finset.card_eq_zero.1 h0) with h' | h' <;> omega
  · -- one prime factor: `k = p^e`
    obtain ⟨p, hp⟩ := Finset.card_eq_one.1 h1
    have hmem : p ∈ k.primeFactors := by rw [hp]; exact Finset.mem_singleton_self p
    have hpp := Nat.prime_of_mem_primeFactors hmem
    have hpodd := hodd_of_mem p hmem
    have he := hpos_of_mem p hmem
    set e := k.factorization p
    rw [hp, Finset.prod_singleton] at hdecomp
    have hp3 : 3 ≤ p := by
      rcases Nat.odd_iff.1 hpodd with h'; have := hpp.two_le; omega
    have hS := sigma_prime_pow_mul p e hpp
    rw [← hdecomp] at hS
    have hX : (p : ℤ) ≤ (p : ℤ) ^ e := by
      exact_mod_cast Nat.le_self_pow (by omega) p
    have hσ : (σ 1 k : ℤ) = 2 * (p : ℤ) ^ e - 1 := by
      have : ((1 + σ 1 k : ℕ) : ℤ) = ((2 * k : ℕ) : ℤ) := by rw [h]
      push_cast at this
      rw [hdecomp] at this
      push_cast at this
      linarith
    rw [hσ, pow_succ] at hS
    have hp3' : (3 : ℤ) ≤ p := by exact_mod_cast hp3
    have key : ((p : ℤ) - 2) * ((p : ℤ) ^ e - 1) = 0 := by linear_combination hS
    rcases mul_eq_zero.1 key with h' | h' <;> nlinarith
  · -- two prime factors: `k = p^a q^b`
    obtain ⟨p, q, hpq, hpqs⟩ := Finset.card_eq_two.1 h2
    have hpm : p ∈ k.primeFactors := by rw [hpqs]; simp
    have hqm : q ∈ k.primeFactors := by rw [hpqs]; simp
    have hpp := Nat.prime_of_mem_primeFactors hpm
    have hqp := Nat.prime_of_mem_primeFactors hqm
    have hpodd := hodd_of_mem p hpm
    have hqodd := hodd_of_mem q hqm
    have ha := hpos_of_mem p hpm
    have hb := hpos_of_mem q hqm
    set a := k.factorization p
    set b := k.factorization q
    rw [hpqs, Finset.prod_pair hpq] at hdecomp
    have hp3 : 3 ≤ p := by
      rcases Nat.odd_iff.1 hpodd with h'; have := hpp.two_le; omega
    have hq3 : 3 ≤ q := by
      rcases Nat.odd_iff.1 hqodd with h'; have := hqp.two_le; omega
    have hcop : Nat.Coprime (p ^ a) (q ^ b) :=
      Nat.Coprime.pow a b ((Nat.coprime_primes hpp hqp).2 hpq)
    have hσk : σ 1 k = σ 1 (p ^ a) * σ 1 (q ^ b) := by
      rw [hdecomp]; exact isMultiplicative_sigma.map_mul_of_coprime hcop
    have h1' := sigma_prime_pow_mul p a hpp
    have h2' := sigma_prime_pow_mul q b hqp
    set S1 : ℤ := (σ 1 (p ^ a) : ℤ)
    set S2 : ℤ := (σ 1 (q ^ b) : ℤ)
    set A : ℤ := (p : ℤ) ^ a with hA
    set B : ℤ := (q : ℤ) ^ b with hB
    rw [pow_succ] at h1' h2'
    have h3 : 1 + S1 * S2 = 2 * A * B := by
      have : ((1 + σ 1 k : ℕ) : ℤ) = ((2 * k : ℕ) : ℤ) := by rw [h]
      rw [hσk, hdecomp] at this
      push_cast at this
      linarith
    have hAp : (p : ℤ) ≤ A := by
      rw [hA]; exact_mod_cast Nat.le_self_pow (show a ≠ 0 by omega) p
    have hBq : (q : ℤ) ≤ B := by
      rw [hB]; exact_mod_cast Nat.le_self_pow (show b ≠ 0 by omega) q
    have hp3' : (3 : ℤ) ≤ p := by exact_mod_cast hp3
    have hq3' : (3 : ℤ) ≤ q := by exact_mod_cast hq3
    have hD := prod_sub_two_ge hp3 hq3 hpodd hqodd hpq
    have E : ((p : ℤ) - 1) * ((q : ℤ) - 1) + ((p : ℤ) * A - 1) * ((q : ℤ) * B - 1) =
        2 * A * B * ((p : ℤ) - 1) * ((q : ℤ) - 1) := by
      linear_combination ((p : ℤ) - 1) * ((q : ℤ) - 1) * h3 - (S2 * ((q : ℤ) - 1)) * h1' -
        ((p : ℤ) * A - 1) * h2'
    have hAB : (p : ℤ) * q ≤ A * B := mul_le_mul hAp hBq (by linarith) (by linarith)
    have hABpos : 0 ≤ A * B := by nlinarith
    have h5 : A * B ≤ A * B * (((p : ℤ) - 2) * ((q : ℤ) - 2) - 2) := by nlinarith
    have hpA : 0 ≤ (p : ℤ) * A := by nlinarith
    have hqB : 0 ≤ (q : ℤ) * B := by nlinarith
    nlinarith

theorem main : H1 → H2 → OMA.R_OeisA215926_conjecture_1_R1.H1 := by
  intro h1 h2 k hk h
  by_contra hk1
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk
  have hσodd : Odd (σ 1 k) := ⟨k - 1, by omega⟩
  have hsq := isSquare_of_odd_sigma hk hσodd
  rcases (by omega : k.primeFactors.card ≤ 2 ∨ k.primeFactors.card = 3 ∨
      4 ≤ k.primeFactors.card) with hc | hc | hc
  · exact not_card_le_two hk hk1 hc h
  · exact h1 k hk hsq hc h
  · exact h2 k hk hsq hc h

end Proof

end OMA.R_OeisA215926_conjecture_1_R1_H1_R1
