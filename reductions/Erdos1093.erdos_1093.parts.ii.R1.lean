import FormalConjectures.ErdosProblems.«1093»
import Mathlib

-- Reduction Erdos1093.erdos_1093.parts.ii.R1 of Erdős Problem 1093 — ii
-- Credit: @rickmanelius
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Erdős 1093 (ii): from the pairs (k, n) to the values of k

Call `C(n, k)` exceptional when `2 k ≤ n` and every prime factor of `C(n, k)` exceeds `k` (the
setting of Erdős, Lacampagne and Selfridge). Its deficiency counts the `i < k` for which `n - i`
is `k`-smooth.

Proved below, with no hypothesis:

* `smooth_term_dvd`: a `k`-smooth term `n - i` of `n (n - 1) ⋯ (n - k + 1) = k! C(n, k)` is coprime
  to `C(n, k)`, so it divides `k!`. Two such terms are distinct factors of that product, so their
  product divides `k!` (`two_terms_dvd`).
* `bound`: an exceptional `C(n, k)` of deficiency at least `2` has `(n + 1 - k)^2 ≤ k!`. So each `k`
  occurs with only finitely many `n` (at most `k + √(k!)`).
* `five_le`: no exceptional `C(n, k)` of deficiency at least `2` has `k ≤ 4`.

So the finiteness of the pairs is the finiteness of the set of `k` that occur. The two
hypotheses split that set by the deficiency; each is a special case of the target.

* `H1`: only finitely many `k` occur with an exceptional `C(n, k)` of deficiency exactly `2`.
* `H2`: only finitely many `k` occur with an exceptional `C(n, k)` of deficiency at least `3`.
-/

namespace OMA.R_Erdos1093_erdos_1093_parts_ii_R1

open Erdos1093 Finset Nat

/-- Only finitely many `k` occur with an exceptional binomial coefficient `C(n, k)` (`2 k ≤ n`,
every prime factor above `k`) of deficiency exactly `2`. -/
def H1 : Prop :=
  {k : ℕ | ∃ n : ℕ, 2 * k ≤ n ∧ deficiency n k = 2 ∧
    ∀ p, p.Prime → p ∣ choose n k → k < p}.Finite

/-- Only finitely many `k` occur with an exceptional binomial coefficient `C(n, k)` of deficiency
at least `3`. -/
def H2 : Prop :=
  {k : ℕ | ∃ n : ℕ, 2 * k ≤ n ∧ 2 < deficiency n k ∧
    ∀ p, p.Prime → p ∣ choose n k → k < p}.Finite

/-- A `k`-smooth number is coprime to a binomial coefficient all of whose prime factors exceed
`k`. -/
lemma coprime_smooth {m n k : ℕ} (hs : m ∈ smoothNumbers (k + 1))
    (hC : ∀ p, p.Prime → p ∣ choose n k → k < p) : Nat.Coprime m (choose n k) := by
  apply Nat.coprime_of_dvd
  intro p hp hpm hpC
  have h1 := (mem_smoothNumbers'.1 hs) p hp hpm
  have h2 := hC p hp hpC
  omega

/-- A `k`-smooth term `n - i` (`i < k`) of an exceptional `C(n, k)` divides `k!`. -/
lemma smooth_term_dvd {n k i : ℕ} (hi : i < k)
    (hC : ∀ p, p.Prime → p ∣ choose n k → k < p)
    (hs : n - i ∈ smoothNumbers (k + 1)) : (n - i) ∣ k ! := by
  have hprod : (n - i) ∣ ∏ t ∈ range k, (n - t) :=
    Finset.dvd_prod_of_mem (fun t => n - t) (mem_range.2 hi)
  rw [← descFactorial_eq_prod_range, descFactorial_eq_factorial_mul_choose] at hprod
  exact (coprime_smooth hs hC).dvd_of_dvd_mul_right hprod

/-- Two distinct `k`-smooth terms of an exceptional `C(n, k)`: their product divides `k!`. -/
lemma two_terms_dvd {n k i j : ℕ} (hi : i < k) (hj : j < k) (hij : i ≠ j)
    (hC : ∀ p, p.Prime → p ∣ choose n k → k < p)
    (hsi : n - i ∈ smoothNumbers (k + 1)) (hsj : n - j ∈ smoothNumbers (k + 1)) :
    (n - i) * (n - j) ∣ k ! := by
  have hprod : (n - i) * (n - j) ∣ ∏ t ∈ range k, (n - t) := by
    rw [← Finset.mul_prod_erase (range k) (fun t => n - t) (mem_range.2 hi)]
    exact mul_dvd_mul_left _
      (Finset.dvd_prod_of_mem (fun t => n - t) (mem_erase.2 ⟨hij.symm, mem_range.2 hj⟩))
  rw [← descFactorial_eq_prod_range, descFactorial_eq_factorial_mul_choose] at hprod
  have hcop : Nat.Coprime ((n - i) * (n - j)) (choose n k) :=
    Nat.Coprime.mul_left (coprime_smooth hsi hC) (coprime_smooth hsj hC)
  exact hcop.dvd_of_dvd_mul_right hprod

/-- An exceptional `C(n, k)` of deficiency at least `2` has `(n + 1 - k)^2 ≤ k!`. -/
lemma bound {n k : ℕ} (hk : 2 * k ≤ n) (hd : 1 < deficiency n k)
    (hC : ∀ p, p.Prime → p ∣ choose n k → k < p) :
    (n + 1 - k) * (n + 1 - k) ≤ k ! := by
  unfold deficiency at hd
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.1 hd
  rw [Finset.mem_filter, Finset.mem_range] at hi hj
  have hle := Nat.le_of_dvd (Nat.factorial_pos k) (two_terms_dvd hi.1 hj.1 hij hC hi.2 hj.2)
  have h1 : n + 1 - k ≤ n - i := by omega
  have h2 : n + 1 - k ≤ n - j := by omega
  exact (Nat.mul_le_mul h1 h2).trans hle

/-- No exceptional `C(n, k)` of deficiency at least `2` has `k ≤ 4`. -/
lemma five_le {n k : ℕ} (hk : 2 * k ≤ n) (hd : 1 < deficiency n k)
    (hC : ∀ p, p.Prime → p ∣ choose n k → k < p) : 5 ≤ k := by
  by_contra h
  have h4 : k ≤ 4 := by omega
  rcases Nat.eq_zero_or_pos k with h0 | h0
  · subst h0
    simp [deficiency] at hd
  · have hk1 : k + 1 ≤ n + 1 - k := by omega
    have h3 := (Nat.mul_le_mul hk1 hk1).trans (bound hk hd hC)
    interval_cases k <;> simp [Nat.factorial] at h3

theorem main : H1 → H2 → type_of% @Erdos1093.erdos_1093.parts.ii := by
  intro h1 h2
  have hK : {k : ℕ | ∃ n : ℕ, 2 * k ≤ n ∧ 1 < deficiency n k ∧
      ∀ p, p.Prime → p ∣ choose n k → k < p}.Finite := by
    refine (h1.union h2).subset ?_
    rintro k ⟨n, hn, hd, hC⟩
    rcases Nat.lt_or_ge 2 (deficiency n k) with h | h
    · exact Or.inr ⟨n, hn, h, hC⟩
    · exact Or.inl ⟨n, hn, by omega, hC⟩
  obtain ⟨B, hB⟩ := hK.bddAbove
  refine ((Set.finite_Iic B).prod (Set.finite_Iic (B ! + B))).subset ?_
  rintro ⟨k, n⟩ ⟨hn, hd, hC⟩
  have hkB : k ≤ B := hB ⟨n, hn, hd, hC⟩
  have hlin : n + 1 - k ≤ k ! := (Nat.le_mul_self _).trans (bound hn hd hC)
  have hfac : k ! ≤ B ! := Nat.factorial_le hkB
  refine ⟨hkB, ?_⟩
  show n ≤ B ! + B
  omega

end OMA.R_Erdos1093_erdos_1093_parts_ii_R1
