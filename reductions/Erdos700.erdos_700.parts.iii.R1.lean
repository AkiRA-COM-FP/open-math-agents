import FormalConjectures.ErdosProblems.«700»
import Mathlib

-- Reduction Erdos700.erdos_700.parts.iii.R1 of Erdős Problem 700 — iii
-- Credit: @rickmanelius
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Erdős 700 (iii): the largest prime-power divisor settles all but the flat numbers

Let `f(n) = min_{1 < k ≤ n/2} gcd(n, C(n, k))` and let `Q(n)` be the largest prime-power divisor
`p ^ v_p(n)` of `n`. Proved below, with no hypothesis:

* `choose_prime_pow_modEq` (Lucas, iterated): if `p ^ a ∣ n` then `C(n, p ^ a) ≡ n / p ^ a (mod p)`.
* `gcd_choose_component`: for a prime `p ∣ n` with `v = v_p(n)`, `gcd(n, C(n, p ^ v)) = n / p ^ v`.
  Indeed `C(n, p ^ v) = (n / p ^ v) C(n - 1, p ^ v - 1)`, and `p` does not divide `C(n, p ^ v)`.
* `f_le_div_component`: hence `f(n) ≤ n / p ^ v` whenever `n ≠ p ^ v`; in particular
  `f(n) ≤ n / Q(n)` for every `n` that is not a prime power.
* `prime_pow_case`: for `n = p ^ a` with `a ≥ 2`, `f(n) = p ≤ √n`, and `(log n) ^ A ≤ (2 A) ^ A √n`
  (`log_rpow_le_sqrt`), so `f(n) ≤ (2 A) ^ A n / (log n) ^ A`.
* `nonflat_bound`: so `f(n) ≤ max(1, (2 A) ^ A) n / (log n) ^ A` for every composite `n` with
  `Q(n) ≥ (log n) ^ A`.
* `flat_log_bound`: if `Q(n) < L` then every prime factor of `n` is below `L` and
  `n ≤ Q(n) ^ ω(n)`, so `log n ≤ (L + 1) log L`.
* `flat_small`: for `A < 1`, with `L = (log n) ^ A` this fails for large `n` (`key_ineq`), so only
  finitely many `n` are flat, and they cost a constant (`f(n) ≤ n`, `f_le_self`).

So `main` proves the target outright for every `0 < A < 1`, and for `A ≥ 1` on every composite
`n` with `Q(n) ≥ (log n) ^ A`. What remains are the flat composite `n` for `A ≥ 1`, whose
prime-power divisors all lie below `(log n) ^ A`. The two hypotheses are the target on these
numbers, split by squarefreeness; each is a special case of the target. (`A = 1` is the
Erdős–Szekeres bound, which they prove; `A > 1` is open.)

* `H1`: for `A ≥ 1`, the bound for squarefree flat composite `n` (all prime factors below
  `(log n) ^ A`).
* `H2`: for `A ≥ 1`, the bound for flat composite `n` that are not squarefree.
-/

namespace OMA.R_Erdos700_erdos_700_parts_iii_R1

open Erdos700

/-- For `A ≥ 1`: the bound `f(n) ≤ C n / (log n) ^ A` for squarefree composite `n` all of whose
prime factors (equivalently its largest prime-power divisor `Q n`) lie below `(log n) ^ A`. -/
def H1 : Prop :=
  ∀ A : ℝ, 1 ≤ A → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ¬ n.Prime → 1 < n → Squarefree n →
    (Q n : ℝ) < Real.log n ^ A → (f n : ℝ) ≤ C * (n : ℝ) / Real.log n ^ A

/-- For `A ≥ 1`: the bound `f(n) ≤ C n / (log n) ^ A` for composite `n` that are not squarefree
and whose largest prime-power divisor `Q n` lies below `(log n) ^ A`. -/
def H2 : Prop :=
  ∀ A : ℝ, 1 ≤ A → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ¬ n.Prime → 1 < n → ¬ Squarefree n →
    (Q n : ℝ) < Real.log n ^ A → (f n : ℝ) ≤ C * (n : ℝ) / Real.log n ^ A

/-- Lucas' theorem, iterated: if `p ^ a ∣ n` then `C(n, p ^ a) ≡ n / p ^ a (mod p)`. -/
lemma choose_prime_pow_modEq {p : ℕ} (hp : p.Prime) :
    ∀ (a n : ℕ), p ^ a ∣ n → n.choose (p ^ a) ≡ n / p ^ a [MOD p] := by
  have : Fact p.Prime := ⟨hp⟩
  intro a
  induction a with
  | zero =>
    intro n _
    rw [pow_zero, Nat.choose_one_right, Nat.div_one]
  | succ a ih =>
    intro n hn
    have hpn : p ∣ n := (dvd_pow_self p (Nat.succ_ne_zero a)).trans hn
    have hlucas : n.choose (p ^ (a + 1)) ≡
        (n % p).choose (p ^ (a + 1) % p) * (n / p).choose (p ^ (a + 1) / p) [MOD p] :=
      Choose.choose_modEq_choose_mod_mul_choose_div_nat
    have h1 : n % p = 0 := Nat.mod_eq_zero_of_dvd hpn
    have h2 : p ^ (a + 1) % p = 0 := Nat.mod_eq_zero_of_dvd (dvd_pow_self p (Nat.succ_ne_zero a))
    have h3 : p ^ (a + 1) / p = p ^ a := by
      rw [pow_succ]
      exact Nat.mul_div_cancel _ hp.pos
    rw [h1, h2, h3, Nat.choose_zero_right, one_mul] at hlucas
    have hdiv : p ^ a ∣ n / p := Nat.dvd_div_of_mul_dvd (by rw [← pow_succ']; exact hn)
    have hih := ih (n / p) hdiv
    rw [Nat.div_div_eq_div_mul, ← pow_succ'] at hih
    exact hlucas.trans hih

/-- For a prime `p ∣ n` with `v = v_p(n)`: `gcd(n, C(n, p ^ v)) = n / p ^ v`. -/
lemma gcd_choose_component {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    Nat.gcd n (n.choose (p ^ n.factorization p)) = n / p ^ n.factorization p := by
  set v := n.factorization p with hv
  set m := n / p ^ v with hm
  have hpv : p ^ v ∣ n := Nat.ordProj_dvd n p
  have hnm : n = p ^ v * m := (Nat.mul_div_cancel' hpv).symm
  have hpm : ¬ p ∣ m := Nat.not_dvd_ordCompl hp hn
  have hpv0 : 0 < p ^ v := pow_pos hp.pos v
  have hmC : m ∣ n.choose (p ^ v) := by
    have key := Nat.add_one_mul_choose_eq (n - 1) (p ^ v - 1)
    have h1 : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hn)
    have h2 : p ^ v - 1 + 1 = p ^ v := Nat.succ_pred_eq_of_pos hpv0
    rw [h1, h2] at key
    refine ⟨(n - 1).choose (p ^ v - 1), ?_⟩
    have hh : p ^ v * (m * (n - 1).choose (p ^ v - 1)) = p ^ v * n.choose (p ^ v) := by
      rw [← mul_assoc, ← hnm, key, mul_comm]
    exact (Nat.eq_of_mul_eq_mul_left hpv0 hh).symm
  have hpC : ¬ p ∣ n.choose (p ^ v) := by
    intro h
    have hmod : n.choose (p ^ v) % p = m % p := choose_prime_pow_modEq hp v n hpv
    have h0 : n.choose (p ^ v) % p = 0 := Nat.mod_eq_zero_of_dvd h
    rw [hmod] at h0
    exact hpm (Nat.dvd_of_mod_eq_zero h0)
  have hcop : Nat.Coprime (p ^ v) (n.choose (p ^ v)) :=
    Nat.Coprime.pow_left v ((Nat.Prime.coprime_iff_not_dvd hp).2 hpC)
  calc Nat.gcd n (n.choose (p ^ v)) = Nat.gcd (p ^ v * m) (n.choose (p ^ v)) := by
        rw [← hnm]
    _ = Nat.gcd m (n.choose (p ^ v)) := Nat.Coprime.gcd_mul_left_cancel m hcop
    _ = m := Nat.gcd_eq_left hmC

/-- `f(n) ≤ n / p ^ v` for a prime `p ∣ n`, `v = v_p(n)`, when `n` is not the power `p ^ v`. -/
lemma f_le_div_component {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) (hpn : p ∣ n)
    (hne : n ≠ p ^ n.factorization p) : f n ≤ n / p ^ n.factorization p := by
  have hpv : p ^ n.factorization p ∣ n := Nat.ordProj_dvd n p
  have hv1 : 1 ≤ n.factorization p := (hp.dvd_iff_one_le_factorization hn).1 hpn
  have h1 : 1 < p ^ n.factorization p := Nat.one_lt_pow (by omega) hp.one_lt
  obtain ⟨m, hm⟩ := hpv
  have hm2 : 2 ≤ m := by
    by_contra hlt
    rcases (show m = 0 ∨ m = 1 by omega) with h0 | h0
    · rw [h0, mul_zero] at hm
      exact hn hm
    · rw [h0, mul_one] at hm
      exact hne hm
  have h2 : p ^ n.factorization p ≤ n / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    calc p ^ n.factorization p * 2 ≤ p ^ n.factorization p * m := Nat.mul_le_mul_left _ hm2
      _ = n := hm.symm
  have hf := f_le n (p ^ n.factorization p) h1 h2
  rwa [gcd_choose_component hp hn] at hf

/-- `(log x) ^ A ≤ (2 A) ^ A √x` for `x ≥ 1` and `A > 0`. -/
lemma log_rpow_le_sqrt {A x : ℝ} (hA : 0 < A) (hx : 1 ≤ x) :
    Real.log x ^ A ≤ (2 * A) ^ A * Real.sqrt x := by
  have hA0 : A ≠ 0 := hA.ne'
  have hε : 0 < 1 / (2 * A) := by positivity
  have hx0 : 0 ≤ x := by linarith
  have hlog := Real.log_le_rpow_div hx0 hε
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hxe : 0 ≤ x ^ (1 / (2 * A)) := Real.rpow_nonneg hx0 _
  calc Real.log x ^ A ≤ (x ^ (1 / (2 * A)) / (1 / (2 * A))) ^ A :=
        Real.rpow_le_rpow hlog0 hlog hA.le
    _ = ((2 * A) * x ^ (1 / (2 * A))) ^ A := by
        congr 1
        field_simp
    _ = (2 * A) ^ A * (x ^ (1 / (2 * A))) ^ A := Real.mul_rpow (by positivity) hxe
    _ = (2 * A) ^ A * x ^ (1 / (2 * A) * A) := by rw [← Real.rpow_mul hx0]
    _ = (2 * A) ^ A * Real.sqrt x := by
        rw [Real.sqrt_eq_rpow]
        congr 2
        field_simp

/-- The prime powers: `f(p ^ a) = p ≤ (2 A) ^ A p ^ a / (log p ^ a) ^ A` for `a ≥ 2`. -/
lemma prime_pow_case {p a : ℕ} (hp : p.Prime) (ha : 2 ≤ a) {A : ℝ} (hA : 0 < A) :
    (f (p ^ a) : ℝ) ≤ (2 * A) ^ A * ((p ^ a : ℕ) : ℝ) / Real.log ((p ^ a : ℕ) : ℝ) ^ A := by
  rw [erdos_700.variants.prime_pow p a hp ha]
  have hpa : p ^ 2 ≤ p ^ a := Nat.pow_le_pow_right hp.pos ha
  have hp2 : 2 ≤ p := hp.two_le
  have hn1 : (1 : ℝ) < ((p ^ a : ℕ) : ℝ) := by
    have : 4 ≤ p ^ a := le_trans (by nlinarith) hpa
    exact_mod_cast (show 1 < p ^ a by omega)
  have hL : 0 < Real.log ((p ^ a : ℕ) : ℝ) ^ A := Real.rpow_pos_of_pos (Real.log_pos hn1) A
  rw [le_div_iff₀ hL]
  have hsq : (p : ℝ) ≤ Real.sqrt ((p ^ a : ℕ) : ℝ) := by
    rw [show (p : ℝ) = Real.sqrt ((p : ℝ) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    apply Real.sqrt_le_sqrt
    exact_mod_cast hpa
  have hb := log_rpow_le_sqrt hA hn1.le
  calc (p : ℝ) * Real.log ((p ^ a : ℕ) : ℝ) ^ A
        ≤ Real.sqrt ((p ^ a : ℕ) : ℝ) * ((2 * A) ^ A * Real.sqrt ((p ^ a : ℕ) : ℝ)) :=
        mul_le_mul hsq hb (by positivity) (Real.sqrt_nonneg _)
    _ = (2 * A) ^ A * ((p ^ a : ℕ) : ℝ) := by
        rw [mul_comm, mul_assoc, Real.mul_self_sqrt (by positivity)]

/-- `Q n` is attained: it is `p ^ v_p(n)` for some prime factor `p` of `n`. -/
lemma Q_spec {n : ℕ} (hn1 : 1 < n) :
    ∃ p ∈ n.primeFactors, Q n = p ^ n.factorization p := by
  have hne : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.2 hn1
  obtain ⟨p, hpmem, hpQ⟩ :=
    Finset.exists_mem_eq_sup n.primeFactors hne (fun p => p ^ n.factorization p)
  refine ⟨p, hpmem, ?_⟩
  unfold Q
  exact hpQ

/-- Every prime-power component `p ^ v_p(n)` is at most `Q n`. -/
lemma component_le_Q {n p : ℕ} (hp : p ∈ n.primeFactors) : p ^ n.factorization p ≤ Q n := by
  unfold Q
  exact Finset.le_sup (f := fun p => p ^ n.factorization p) hp

/-- A prime factor `p` of `n` is at most its component `p ^ v_p(n)`. -/
lemma prime_le_component {n p : ℕ} (hp : p ∈ n.primeFactors) : p ≤ p ^ n.factorization p := by
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hn0 : n ≠ 0 := (Nat.mem_primeFactors.1 hp).2.2
  have hv : 1 ≤ n.factorization p :=
    (hpp.dvd_iff_one_le_factorization hn0).1 (Nat.dvd_of_mem_primeFactors hp)
  calc p = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ n.factorization p := Nat.pow_le_pow_right hpp.pos hv

/-- `Q n ≥ 2` for `n > 1`. -/
lemma two_le_Q {n : ℕ} (hn1 : 1 < n) : 2 ≤ Q n := by
  obtain ⟨p, hpmem, hpQ⟩ := Q_spec hn1
  rw [hpQ]
  exact (Nat.prime_of_mem_primeFactors hpmem).two_le.trans (prime_le_component hpmem)

/-- `n ≤ Q(n) ^ ω(n)`. -/
lemma le_Q_pow {n : ℕ} (hn0 : n ≠ 0) : n ≤ Q n ^ n.primeFactors.card := by
  have h := Nat.prod_factorization_pow_eq_self hn0
  rw [Finsupp.prod, Nat.support_factorization] at h
  calc n = ∏ p ∈ n.primeFactors, p ^ n.factorization p := h.symm
    _ ≤ Q n ^ n.primeFactors.card :=
        Finset.prod_le_pow_card _ _ _ (fun p hp => component_le_Q hp)

/-- If `Q(n) < L` then `log n ≤ (L + 1) log L`: all prime factors lie below `L`, so there are at
most `L + 1` of them, and `n ≤ Q(n) ^ ω(n)`. -/
lemma flat_log_bound {n : ℕ} (hn1 : 1 < n) {L : ℝ} (hQL : (Q n : ℝ) < L) :
    Real.log n ≤ (L + 1) * Real.log L := by
  have hn0 : n ≠ 0 := by omega
  have hQ2 : (2 : ℝ) ≤ Q n := by exact_mod_cast two_le_Q hn1
  have hsub : n.primeFactors ⊆ Finset.range ⌈L⌉₊ := by
    intro p hp
    rw [Finset.mem_range]
    have h2 : (p : ℝ) < L :=
      lt_of_le_of_lt (by exact_mod_cast (prime_le_component hp).trans (component_le_Q hp)) hQL
    exact_mod_cast (lt_of_lt_of_le h2 (Nat.le_ceil L))
  have hcard : (n.primeFactors.card : ℝ) ≤ L + 1 := by
    have h3 := Finset.card_le_card hsub
    rw [Finset.card_range] at h3
    have h4 : (⌈L⌉₊ : ℝ) < L + 1 := Nat.ceil_lt_add_one (by linarith)
    have h5 : (n.primeFactors.card : ℝ) ≤ ⌈L⌉₊ := by exact_mod_cast h3
    linarith
  have hle : (n : ℝ) ≤ (Q n : ℝ) ^ n.primeFactors.card := by exact_mod_cast le_Q_pow hn0
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hQpos : (0 : ℝ) < Q n := by linarith
  calc Real.log n ≤ Real.log ((Q n : ℝ) ^ n.primeFactors.card) := Real.log_le_log hnpos hle
    _ = n.primeFactors.card * Real.log (Q n) := Real.log_pow _ _
    _ ≤ (L + 1) * Real.log L :=
        mul_le_mul hcard (Real.log_le_log hQpos hQL.le) (Real.log_nonneg (by linarith))
          (by linarith)

/-- For `0 < A < 1`, `(u ^ A + 1) A log u < u` for all large `u`. -/
lemma key_ineq {A : ℝ} (hA0 : 0 < A) (hA1 : A < 1) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ u : ℝ, B ≤ u → (u ^ A + 1) * (A * Real.log u) < u := by
  have hε0 : 0 < (1 - A) / 2 := by linarith
  have hεne : (1 - A) / 2 ≠ 0 := hε0.ne'
  have hK : 0 ≤ 2 * A / ((1 - A) / 2) + 1 := by positivity
  refine ⟨max 1 ((2 * A / ((1 - A) / 2) + 1) ^ (1 / ((1 - A) / 2))), le_max_left _ _, ?_⟩
  intro u hu
  have hu1 : 1 ≤ u := le_trans (le_max_left _ _) hu
  have hu0 : 0 < u := by linarith
  have hlog : Real.log u ≤ u ^ ((1 - A) / 2) / ((1 - A) / 2) := Real.log_le_rpow_div hu0.le hε0
  have hlog0 : 0 ≤ Real.log u := Real.log_nonneg hu1
  have huA : 1 ≤ u ^ A := Real.one_le_rpow hu1 hA0.le
  have hueps : 2 * A / ((1 - A) / 2) < u ^ ((1 - A) / 2) := by
    have h1 : (2 * A / ((1 - A) / 2) + 1) ^ (1 / ((1 - A) / 2)) ≤ u := le_trans (le_max_right _ _) hu
    have h2 : ((2 * A / ((1 - A) / 2) + 1) ^ (1 / ((1 - A) / 2))) ^ ((1 - A) / 2) ≤
        u ^ ((1 - A) / 2) := Real.rpow_le_rpow (Real.rpow_nonneg hK _) h1 hε0.le
    rw [← Real.rpow_mul hK, one_div_mul_cancel hεne, Real.rpow_one] at h2
    linarith
  calc (u ^ A + 1) * (A * Real.log u)
      ≤ (2 * u ^ A) * (A * (u ^ ((1 - A) / 2) / ((1 - A) / 2))) :=
        mul_le_mul (by linarith) (mul_le_mul_of_nonneg_left hlog hA0.le)
          (mul_nonneg hA0.le hlog0) (by positivity)
    _ = (2 * A / ((1 - A) / 2)) * (u ^ A * u ^ ((1 - A) / 2)) := by
        field_simp
    _ < u ^ ((1 - A) / 2) * (u ^ A * u ^ ((1 - A) / 2)) :=
        mul_lt_mul_of_pos_right hueps (by positivity)
    _ = u := by
        rw [← Real.rpow_add hu0, ← Real.rpow_add hu0]
        have hsum : (1 - A) / 2 + (A + (1 - A) / 2) = 1 := by ring
        rw [hsum, Real.rpow_one]

/-- For `0 < A < 1` only finitely many `n` are flat: `Q(n) < (log n) ^ A` forces `n < N`. -/
lemma flat_small {A : ℝ} (hA0 : 0 < A) (hA1 : A < 1) :
    ∃ N : ℕ, ∀ n : ℕ, 1 < n → (Q n : ℝ) < Real.log n ^ A → n < N := by
  obtain ⟨B, hB1, hB⟩ := key_ineq hA0 hA1
  refine ⟨⌈Real.exp B⌉₊ + 1, ?_⟩
  intro n hn1 hQ
  by_contra hge
  have hge' : ⌈Real.exp B⌉₊ + 1 ≤ n := not_lt.mp hge
  have hnR : Real.exp B ≤ n := by
    have h1 : (⌈Real.exp B⌉₊ : ℝ) ≤ n := by exact_mod_cast (show ⌈Real.exp B⌉₊ ≤ n by omega)
    exact le_trans (Nat.le_ceil _) h1
  have hu : B ≤ Real.log n := by
    rw [← Real.log_exp B]
    exact Real.log_le_log (Real.exp_pos B) hnR
  have hupos : 0 < Real.log n := lt_of_lt_of_le (by linarith) hu
  have h1 := flat_log_bound hn1 hQ
  rw [Real.log_rpow hupos] at h1
  have h2 := hB (Real.log n) hu
  linarith

/-- `f(n) ≤ n` for composite `n`. -/
lemma f_le_self {n : ℕ} (hnp : ¬ n.Prime) (hn1 : 1 < n) : f n ≤ n := by
  have h4 : 4 ≤ n := by
    by_contra h
    interval_cases n <;> norm_num at hnp
  calc f n ≤ Nat.gcd n (n.choose 2) := f_le n 2 (by norm_num) (by omega)
    _ ≤ n := Nat.gcd_le_left _ (by omega)

/-- Enlarging the constant. -/
lemma mono_C {x C' C n L : ℝ} (hL : 0 < L) (hn : 0 ≤ n) (hC : C' ≤ C) (h : x ≤ C' * n / L) :
    x ≤ C * n / L :=
  h.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC hn) hL.le)

/-- The non-flat case: `f(n) ≤ max(1, (2 A) ^ A) n / (log n) ^ A` when `Q(n) ≥ (log n) ^ A`. -/
lemma nonflat_bound {A : ℝ} (hA : 0 < A) {n : ℕ} (hnp : ¬ n.Prime) (hn1 : 1 < n)
    (hQ' : Real.log n ^ A ≤ (Q n : ℝ)) :
    (f n : ℝ) ≤ max 1 ((2 * A) ^ A) * n / Real.log n ^ A := by
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn1
  have hL : 0 < Real.log n ^ A := Real.rpow_pos_of_pos (Real.log_pos hnR) A
  obtain ⟨p, hpmem, hQeq⟩ := Q_spec hn1
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
  have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors hpmem
  have hn0 : n ≠ 0 := by omega
  by_cases hpow : n = p ^ n.factorization p
  · have ha2 : 2 ≤ n.factorization p := by
      by_contra h
      rcases (show n.factorization p = 1 ∨ n.factorization p = 0 by omega) with h' | h'
      · rw [h', pow_one] at hpow
        exact hnp (by rw [hpow]; exact hp)
      · rw [h', pow_zero] at hpow
        omega
    have hpp := prime_pow_case hp ha2 hA
    rw [← hpow] at hpp
    exact mono_C hL (Nat.cast_nonneg n) (le_max_right _ _) hpp
  · have hfle := f_le_div_component hp hn0 hpn hpow
    have hdvd : p ^ n.factorization p ∣ n := Nat.ordProj_dvd n p
    have hQpos : (0 : ℝ) < ((p ^ n.factorization p : ℕ) : ℝ) := by
      have : 0 < p ^ n.factorization p := pow_pos hp.pos _
      exact_mod_cast this
    have hcast : ((n / p ^ n.factorization p : ℕ) : ℝ) =
        (n : ℝ) / ((p ^ n.factorization p : ℕ) : ℝ) := Nat.cast_div hdvd hQpos.ne'
    have hQ'' : Real.log n ^ A ≤ ((p ^ n.factorization p : ℕ) : ℝ) := by
      rw [← hQeq]
      exact hQ'
    have step : (f n : ℝ) ≤ 1 * n / Real.log n ^ A := by
      calc (f n : ℝ) ≤ ((n / p ^ n.factorization p : ℕ) : ℝ) := by exact_mod_cast hfle
        _ = (n : ℝ) / ((p ^ n.factorization p : ℕ) : ℝ) := hcast
        _ ≤ (n : ℝ) / Real.log n ^ A := div_le_div_of_nonneg_left (by positivity) hL hQ''
        _ = 1 * n / Real.log n ^ A := by ring
    exact mono_C hL (Nat.cast_nonneg n) (le_max_left _ _) step

theorem main : H1 → H2 → type_of% @Erdos700.erdos_700.parts.iii := by
  intro h1 h2 A hA
  by_cases hA1 : 1 ≤ A
  · obtain ⟨C1, hC1, hb1⟩ := h1 A hA1
    obtain ⟨C2, hC2, hb2⟩ := h2 A hA1
    have hCpos : 0 < max (max C1 C2) (max 1 ((2 * A) ^ A)) :=
      lt_of_lt_of_le one_pos (le_trans (le_max_left _ _) (le_max_right _ _))
    refine ⟨max (max C1 C2) (max 1 ((2 * A) ^ A)), hCpos, ?_⟩
    intro n hnp hn1
    have hnR : (1 : ℝ) < n := by exact_mod_cast hn1
    have hL : 0 < Real.log n ^ A := Real.rpow_pos_of_pos (Real.log_pos hnR) A
    by_cases hQ : (Q n : ℝ) < Real.log n ^ A
    · by_cases hsq : Squarefree n
      · exact mono_C hL (Nat.cast_nonneg n) (le_trans (le_max_left _ _) (le_max_left _ _))
          (hb1 n hnp hn1 hsq hQ)
      · exact mono_C hL (Nat.cast_nonneg n) (le_trans (le_max_right _ _) (le_max_left _ _))
          (hb2 n hnp hn1 hsq hQ)
    · exact mono_C hL (Nat.cast_nonneg n) (le_max_right _ _)
        (nonflat_bound hA hnp hn1 (not_lt.mp hQ))
  · have hA1' : A < 1 := not_le.mp hA1
    obtain ⟨N, hN⟩ := flat_small hA hA1'
    have hCpos : 0 < max (max 1 ((2 * A) ^ A)) (Real.log N ^ A) :=
      lt_of_lt_of_le one_pos (le_trans (le_max_left _ _) (le_max_left _ _))
    refine ⟨max (max 1 ((2 * A) ^ A)) (Real.log N ^ A), hCpos, ?_⟩
    intro n hnp hn1
    have hnR : (1 : ℝ) < n := by exact_mod_cast hn1
    have hL : 0 < Real.log n ^ A := Real.rpow_pos_of_pos (Real.log_pos hnR) A
    by_cases hQ : (Q n : ℝ) < Real.log n ^ A
    · have hnN : n < N := hN n hn1 hQ
      have hfn : (f n : ℝ) ≤ n := by exact_mod_cast f_le_self hnp hn1
      have hnNR : (n : ℝ) ≤ N := by exact_mod_cast hnN.le
      have hlogle : Real.log n ^ A ≤ Real.log N ^ A :=
        Real.rpow_le_rpow (Real.log_nonneg hnR.le) (Real.log_le_log (by linarith) hnNR) hA.le
      have step : (f n : ℝ) ≤ Real.log N ^ A * n / Real.log n ^ A := by
        refine hfn.trans ?_
        rw [le_div_iff₀ hL, mul_comm (Real.log N ^ A)]
        exact mul_le_mul_of_nonneg_left hlogle (Nat.cast_nonneg n)
      exact mono_C hL (Nat.cast_nonneg n) (le_max_right _ _) step
    · exact mono_C hL (Nat.cast_nonneg n) (le_max_left _ _)
        (nonflat_bound hA hnp hn1 (not_lt.mp hQ))

end OMA.R_Erdos700_erdos_700_parts_iii_R1
