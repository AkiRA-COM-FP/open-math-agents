import OMAReductions.R_arxiv_2604_17847_R1
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.NumberTheory.LegendreSymbol.Basic

-- Reduction of the finite-cover step from PR 20911 and board note 93655.
-- Credit: @wispiANt

namespace OMA.R_arxiv_2604_17847_R1_H1_R1

open OMA.S_arxiv_2604_17847
open OMA.R_arxiv_2604_17847_R1 (finite_prime_cover_iff fixed_rank_family totient_fib_witness)

-- When the common factor is prime to q, exclude multiples of the normalized square rank.
def H1 : Prop :=
  ∀ q r : ℕ, q.Prime → 53 < q → r < pisano q → ¬ q ∣ (Nat.fib (pisano q)).totient →
    48 < r → (Odd r → 4 * q < Nat.fib r) →
    let g := r.gcd (pisano q)
    ¬ q ∣ Nat.fib g → ∃ t : ℕ, 0 < t ∧ g * t ≡ r [MOD pisano q] ∧
      ¬ rankOfApparition (q ^ 2) / (rankOfApparition (q ^ 2)).gcd g ∣ t ∧
        ∀ p : ℕ, p.Prime → p ≡ 1 [MOD q] → ¬ rankOfApparition p / (rankOfApparition p).gcd g ∣ t

-- When the common factor supplies one copy of q, the multiplier must avoid q.
def H2 : Prop :=
  ∀ q r : ℕ, q.Prime → 53 < q → r < pisano q → ¬ q ∣ (Nat.fib (pisano q)).totient →
    48 < r → (Odd r → 4 * q < Nat.fib r) →
    let g := r.gcd (pisano q)
    q ∣ Nat.fib g → ∃ t : ℕ, 0 < t ∧ g * t ≡ r [MOD pisano q] ∧
      ¬ q ∣ t ∧
        ∀ p : ℕ, p.Prime → p ≡ 1 [MOD q] → ¬ rankOfApparition p / (rankOfApparition p).gcd g ∣ t

lemma gcd_dvd_class {r P m : ℕ} (hm : m ≡ r [MOD P]) : r.gcd P ∣ m :=
  Nat.modEq_zero_iff_dvd.mp ((hm.of_dvd (Nat.gcd_dvd_right _ _)).trans
    (Nat.gcd_dvd_left _ _).modEq_zero_nat)

lemma fib_quotient_product (g t : ℕ) :
    Nat.fib g * (Nat.fib (g * t) / Nat.fib g) = Nat.fib (g * t) :=
  Nat.mul_div_cancel' (Nat.fib_dvd _ _ (dvd_mul_right g t))

-- Dividing out the common factor preserves strong divisibility in the multiplier.
lemma gcd_fib_quotients {g : ℕ} (hg : 0 < g) (a b : ℕ) :
    (Nat.fib (g * a) / Nat.fib g).gcd (Nat.fib (g * b) / Nat.fib g) =
      Nat.fib (g * a.gcd b) / Nat.fib g := by
  apply Nat.eq_of_mul_eq_mul_left (Nat.fib_pos.mpr hg)
  rw [← Nat.gcd_mul_left, fib_quotient_product, fib_quotient_product, ← Nat.fib_gcd,
    Nat.gcd_mul_left, fib_quotient_product]

lemma coprime_fib_quotients {g a b : ℕ} (hg : 0 < g) (hab : a.Coprime b) :
    (Nat.fib (g * a) / Nat.fib g).Coprime (Nat.fib (g * b) / Nat.fib g) := by
  change _ = 1
  rw [gcd_fib_quotients hg, hab.gcd_eq_one, Nat.mul_one, Nat.div_self (Nat.fib_pos.mpr hg)]

-- At a zero index modulo q, the common factor has been removed exactly once
-- in forming the quotient. The remaining divisibility by q is read from t.
lemma prime_dvd_quotient_iff {q g : ℕ} (hq : q.Prime) (hg : 0 < g)
    (hz : q ∣ Nat.fib g) (t : ℕ) : q ∣ Nat.fib (g * t) / Nat.fib g ↔ q ∣ t := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hg.ne'
  let g := k + 1
  change q ∣ Nat.fib g at hz
  let u : ZMod q := Nat.fib (g + 1)
  let : Fact q.Prime := ⟨hq⟩
  have zero : (Nat.fib g : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff ..).mpr hz
  have unit : u ≠ 0 := by
    intro h
    have hd := (ZMod.natCast_eq_zero_iff (Nat.fib (g + 1)) q).mp h
    exact hq.not_dvd_one (by simpa only [(Nat.fib_coprime_fib_succ g).gcd_eq_one] using Nat.dvd_gcd hz hd)
  have prev : (Nat.fib k : ZMod q) = u := by
    change _ = (Nat.fib (k + 2) : ZMod q)
    rw [Nat.fib_add_two, Nat.cast_add, zero, add_zero]
  have neighbor (s : ℕ) : (Nat.fib (g * s + 1) : ZMod q) = u ^ s := by
    induction s with
    | zero => simp
    | succ s ih =>
      rw [Nat.mul_succ, Nat.fib_add, Nat.cast_add, Nat.cast_mul, Nat.cast_mul, zero, ih, pow_succ]
      simp [u]
  let c := fun s => Nat.fib (g * s) / Nat.fib g
  have step (s : ℕ) : c (s + 1) = c s * Nat.fib k + Nat.fib (g * s + 1) := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.fib_pos.mpr hg)
    change Nat.fib g * (Nat.fib (g * (s + 1)) / Nat.fib g) = _
    rw [fib_quotient_product, Nat.mul_succ, Nat.mul_add, ← Nat.mul_assoc]
    change Nat.fib (g * s + (k + 1)) = Nat.fib g * (Nat.fib (g * s) / Nat.fib g) * _ + _
    rw [fib_quotient_product, ← Nat.add_assoc, Nat.fib_add]
    simp only [g, Nat.mul_comm]
  have coefficient (s : ℕ) : (c s : ZMod q) * u = (s : ZMod q) * u ^ s := by
    induction s with
    | zero => simp [c]
    | succ s ih =>
      rw [step, Nat.cast_add, Nat.cast_mul, prev, neighbor, Nat.cast_succ, pow_succ]
      linear_combination u * ih
  rw [← ZMod.natCast_eq_zero_iff, ← ZMod.natCast_eq_zero_iff]
  change (c t : ZMod q) = 0 ↔ (t : ZMod q) = 0
  have eq := coefficient t
  constructor
  · intro h
    rw [h, zero_mul] at eq
    exact (mul_eq_zero.mp eq.symm).resolve_right (pow_ne_zero _ unit)
  · intro h
    rw [h, zero_mul] at eq
    exact (mul_eq_zero.mp eq).resolve_right unit

lemma totient_witness_iff {q n : ℕ} (hq : q.Prime) (hn : 0 < n) :
    q ∣ (Nat.fib n).totient ↔ q ^ 2 ∣ Nat.fib n ∨
      ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD q] ∧ p ∣ Nat.fib n := by
  constructor
  · intro h
    rcases totient_fib_witness hq h with hs | ⟨p, hp, hc, hd⟩
    · exact Or.inl hs
    · have pos := Nat.pos_of_dvd_of_pos hd hn
      have ex := Nat.nonempty_of_pos_sInf (s := {k : ℕ | 0 < k ∧ p ∣ Nat.fib k}) pos
      have first : 0 < rankOfApparition p ∧ p ∣ Nat.fib (rankOfApparition p) := Nat.sInf_mem ex
      exact Or.inr ⟨p, hp, hc, first.2.trans (Nat.fib_dvd _ _ hd)⟩
  · rintro (hs | ⟨p, hp, hc, hd⟩)
    · have h : q ∣ (q ^ 2).totient := by
        rw [Nat.totient_prime_pow_succ hq 1, pow_one]
        exact dvd_mul_right _ _
      exact h.trans (Nat.totient_dvd_of_dvd hs)
    · have h : q ∣ p.totient := by rw [Nat.totient_prime hp]; exact hc.symm.dvd'
      exact h.trans (Nat.totient_dvd_of_dvd hd)

lemma square_in_product {q a c : ℕ} (hq : q.Prime) (hs : ¬ q ^ 2 ∣ a) :
    q ^ 2 ∣ a * c ↔ (if q ∣ a then q else q ^ 2) ∣ c := by
  split_ifs with ha
  · obtain ⟨b, rfl⟩ := ha
    have hb : ¬ q ∣ b := fun h => hs (by simpa [pow_two] using Nat.mul_dvd_mul_left q h)
    rw [pow_two, Nat.mul_assoc]
    constructor
    · intro h
      exact (hq.coprime_iff_not_dvd.mpr hb).dvd_of_dvd_mul_left (Nat.dvd_of_mul_dvd_mul_left hq.pos h)
    · intro h
      exact Nat.mul_dvd_mul_left _ (dvd_mul_of_dvd_right h _)
  · exact ⟨((hq.coprime_iff_not_dvd.mpr ha).pow_left 2).dvd_of_dvd_mul_left,
      fun h => dvd_mul_of_dvd_right h _⟩

-- The sInf convention also gives divisibility at index zero if the rank is zero.
lemma fib_at_rank (b : ℕ) : b ∣ Nat.fib (rankOfApparition b) := by
  by_cases h : rankOfApparition b = 0
  · simp [h]
  · have ex := Nat.nonempty_of_pos_sInf (s := {j : ℕ | 0 < j ∧ b ∣ Nat.fib j})
        (Nat.pos_of_ne_zero h)
    exact (Nat.sInf_mem ex).2

lemma rank_dvd_iff_fib {b n : ℕ} : rankOfApparition b ∣ n ↔ b ∣ Nat.fib n := by
  constructor
  · exact fun h => (fib_at_rank b).trans (Nat.fib_dvd _ _ h)
  · by_cases h : n = 0
    · simp [h]
    · exact OMA.R_arxiv_2604_17847_R1.rank_dvd_index (Nat.pos_of_ne_zero h)

-- At an ordinary prime the next zero modulo q² is reached at multiplier q.
lemma square_rank {q : ℕ} (hq : q.Prime) :
    rankOfApparition (q ^ 2) =
      if q ^ 2 ∣ Nat.fib (rankOfApparition q) then rankOfApparition q
      else q * rankOfApparition q := by
  let z := rankOfApparition q
  let w := rankOfApparition (q ^ 2)
  have first : q ∣ Nat.fib z := fib_at_rank q
  have second : q ^ 2 ∣ Nat.fib w := fib_at_rank _
  have sub : z ∣ w := rank_dvd_iff_fib.mpr ((dvd_pow_self q (by decide : 2 ≠ 0)).trans second)
  split_ifs with he
  · exact Nat.dvd_antisymm (rank_dvd_iff_fib.mpr he) sub
  · have hz : 0 < z := by
      by_contra! hz
      have eq : z = 0 := by omega
      exact he (by change q ^ 2 ∣ Nat.fib z; simp [eq])
    have lift (t : ℕ) : q ^ 2 ∣ Nat.fib (z * t) ↔ q ∣ t := by
      calc
        q ^ 2 ∣ Nat.fib (z * t) ↔ q ^ 2 ∣ Nat.fib z * (Nat.fib (z * t) / Nat.fib z) := by
          rw [fib_quotient_product]
        _ ↔ q ∣ Nat.fib (z * t) / Nat.fib z := by
          simpa only [if_pos first] using square_in_product (a := Nat.fib z) (c := Nat.fib (z * t) / Nat.fib z) hq he
        _ ↔ q ∣ t := prime_dvd_quotient_iff hq hz first t
    apply Nat.dvd_antisymm
    · exact rank_dvd_iff_fib.mpr (by simpa [Nat.mul_comm] using (lift q).mpr (dvd_refl q))
    · obtain ⟨t, ht⟩ := sub
      rw [ht] at second
      change q * z ∣ w
      rw [ht, Nat.mul_comm q z]
      exact Nat.mul_dvd_mul_left z ((lift t).mp second)

lemma normalized_rank_test {b g t : ℕ} (hg : 0 < g) :
    b ∣ Nat.fib (g * t) ↔
      rankOfApparition b / (rankOfApparition b).gcd g ∣ t := by
  rw [← rank_dvd_iff_fib]
  let w := rankOfApparition b
  let d := w.gcd g
  have hd : 0 < d := Nat.gcd_pos_of_pos_right _ hg
  obtain ⟨a, b, cop, ha, hb⟩ := Nat.exists_coprime w g
  have quot : w / d = a := by
    calc
      w / d = (a * d) / d := congrArg (· / d) ha
      _ = a := Nat.mul_div_cancel _ hd
  change w ∣ g * t ↔ w / d ∣ t
  rw [quot]
  have left : w = d * a := ha.trans (Nat.mul_comm ..)
  have right : g = d * b := hb.trans (Nat.mul_comm ..)
  constructor
  · intro h
    rw [left, right, Nat.mul_assoc] at h
    exact cop.dvd_of_dvd_mul_left (Nat.dvd_of_mul_dvd_mul_left hd h)
  · intro h
    rw [left, right, Nat.mul_assoc]
    exact Nat.mul_dvd_mul_left d (dvd_mul_of_dvd_right h _)

lemma normalized_square_test {q g t : ℕ} (hg : 0 < g) :
    q ^ 2 ∣ Nat.fib (g * t) ↔
      rankOfApparition (q ^ 2) / (rankOfApparition (q ^ 2)).gcd g ∣ t :=
  normalized_rank_test hg

-- At a prime multiplier, only the normalized square rank itself can introduce a square.
lemma square_at_prime_multiplier {q g l : ℕ} (hg : 0 < g) (hl : l.Prime)
    (hbase : ¬ q ^ 2 ∣ Nat.fib g) :
    q ^ 2 ∣ Nat.fib (g * l) ↔ rankOfApparition (q ^ 2) / (rankOfApparition (q ^ 2)).gcd g = l := by
  have hunit : ¬ rankOfApparition (q ^ 2) / (rankOfApparition (q ^ 2)).gcd g ∣ 1 := by
    intro h
    exact hbase (by simpa using (normalized_square_test (t := 1) hg).mpr h)
  rw [normalized_square_test hg, Nat.dvd_prime hl]
  exact ⟨fun h => h.resolve_left (fun e => hunit (by rw [e])), Or.inr⟩

-- If p already divides F_g its reappearance is controlled by p itself.
-- Otherwise the reduced rank determines exactly when p enters the quotient.
lemma quotient_prime_test {p g t : ℕ} (hp : p.Prime) (hg : 0 < g) :
    p ∣ Nat.fib (g * t) / Nat.fib g ↔
      (if p ∣ Nat.fib g then p else rankOfApparition p / (rankOfApparition p).gcd g) ∣ t := by
  split_ifs with ha
  · exact prime_dvd_quotient_iff hp hg ha t
  · rw [← normalized_rank_test hg, ← fib_quotient_product g t,
      Nat.mul_div_cancel_left _ (Nat.fib_pos.mpr hg)]
    exact ⟨fun h => dvd_mul_of_dvd_right h _, (hp.coprime_iff_not_dvd.mpr ha).dvd_of_dvd_mul_left⟩

lemma quotient_at_prime_multiplier {p g l : ℕ} (hp : p.Prime) (hg : 0 < g) (hl : l.Prime) :
    p ∣ Nat.fib (g * l) / Nat.fib g ↔
      (if p ∣ Nat.fib g then p else rankOfApparition p / (rankOfApparition p).gcd g) = l := by
  have no : ¬ p ∣ Nat.fib (g * 1) / Nat.fib g := by
    simpa [Nat.div_self (Nat.fib_pos.mpr hg)] using hp.not_dvd_one
  rw [quotient_prime_test hp hg] at no
  rw [quotient_prime_test hp hg, Nat.dvd_prime hl]
  exact ⟨fun h => h.resolve_left (fun e => no (by rw [e])), Or.inr⟩

-- A single prime multiplier in the requested class evades a whole finite list,
-- even when some of the listed primes divide the common Fibonacci factor.
lemma finite_quotient_avoidance {q r P : ℕ} (hP : 0 < P) (W : Finset ℕ)
    (hbase : ¬ q ^ 2 ∣ Nat.fib (r.gcd P)) (B : ℕ) :
    let g := r.gcd P
    ∃ l > B, l.Prime ∧ g * l ≡ r [MOD P] ∧ ¬ q ^ 2 ∣ Nat.fib (g * l) ∧
      ∀ p ∈ W, p.Prime → ¬ p ∣ Nat.fib (g * l) / Nat.fib g := by
  let g := r.gcd P
  have hg := Nat.gcd_pos_of_pos_right r hP
  let divisor := fun p => if p ∣ Nat.fib g then p else rankOfApparition p / (rankOfApparition p).gcd g
  let square := rankOfApparition (q ^ 2) / (rankOfApparition (q ^ 2)).gcd g
  obtain ⟨l, hbound, hl, hc⟩ := OMA.R_arxiv_2604_17847_R1.normalized_prime_indices
    (r := r) hP (max B (max square (W.sup divisor)))
  have big := lt_of_le_of_lt (le_max_right ..) hbound
  have hs : square < l := lt_of_le_of_lt (le_max_left ..) big
  refine ⟨l, lt_of_le_of_lt (le_max_left ..) hbound, hl, hc, ?_, ?_⟩
  · exact fun h => hs.ne ((square_at_prime_multiplier hg hl hbase).mp h)
  · intro p hw hp h
    have bound : divisor p ≤ W.sup divisor := Finset.le_sup hw
    have small := lt_of_le_of_lt (bound.trans (le_max_right ..)) big
    exact small.ne ((quotient_at_prime_multiplier hp hg hl).mp h)

lemma witness_sieve_iff {q g P t : ℕ} (hq : q.Prime) (hP : 0 < P) (hgP : g ∣ P)
    (hbad : ¬ q ∣ (Nat.fib P).totient) :
    (∀ p : ℕ, p.Prime → p ≡ 1 [MOD q] → ¬ p ∣ Nat.fib (g * t) / Nat.fib g) ↔
    ∀ p : ℕ, p.Prime → p ≡ 1 [MOD q] → ¬ rankOfApparition p / (rankOfApparition p).gcd g ∣ t := by
  have test (p : ℕ) (hp : p.Prime) (hc : p ≡ 1 [MOD q]) :
      p ∣ Nat.fib (g * t) / Nat.fib g ↔ rankOfApparition p / (rankOfApparition p).gcd g ∣ t := by
    have ha : ¬ p ∣ Nat.fib g := fun h =>
      hbad ((totient_witness_iff hq hP).mpr (Or.inr ⟨p, hp, hc, h.trans (Nat.fib_dvd _ _ hgP)⟩))
    simpa only [if_neg ha] using quotient_prime_test (t := t) hp (Nat.pos_of_dvd_of_pos hgP hP)
  constructor
  · exact fun h p hp hc => mt (test p hp hc).mpr (h p hp hc)
  · exact fun h p hp hc => mt (test p hp hc).mp (h p hp hc)

-- Failure of descent on a good class forces coverage of every prime in the
-- normalized progression except possibly the single square multiplier.
lemma prime_progression_coverage {q r l : ℕ} (hq : q.Prime) (hr : r ∈ S q)
    (hbad : ¬ q ∣ (Nat.fib (pisano q)).totient) (hl : l.Prime)
    (hc : r.gcd (pisano q) * l ≡ r [MOD pisano q]) :
    let g := r.gcd (pisano q)
    rankOfApparition (q ^ 2) / (rankOfApparition (q ^ 2)).gcd g = l ∨
      ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD q] ∧ rankOfApparition p / (rankOfApparition p).gcd g = l := by
  let g := r.gcd (pisano q)
  have hP := Nat.zero_lt_of_lt hr.1
  have hg : 0 < g := Nat.gcd_pos_of_pos_right r hP
  have common : Nat.fib g ∣ Nat.fib (pisano q) := Nat.fib_dvd _ _ (Nat.gcd_dvd_right r _)
  have no := mt (totient_witness_iff hq hP).mpr hbad
  rcases (totient_witness_iff hq (Nat.mul_pos hg hl.pos)).mp (hr.2 _ hc) with hs | ⟨p, hp, hmod, hd⟩
  · exact Or.inl ((square_at_prime_multiplier hg hl (fun h => no (Or.inl (h.trans common)))).mp hs)
  · have ha : ¬ p ∣ Nat.fib g := fun h => no (Or.inr ⟨p, hp, hmod, h.trans common⟩)
    have prod : p ∣ Nat.fib g * (Nat.fib (g * l) / Nat.fib g) := by
      rwa [fib_quotient_product]
    have eq := (quotient_at_prime_multiplier hp hg hl).mp ((hp.dvd_mul.mp prod).resolve_left ha)
    exact Or.inr ⟨p, hp, hmod, by simpa only [if_neg ha] using eq⟩

-- Cassini's expression changes sign at each Fibonacci step.
lemma signed_cassini (p n : ℕ) :
    let a : ZMod p := Nat.fib n
    let b : ZMod p := Nat.fib (n + 1)
    b ^ 2 - a * b - a ^ 2 = (-1) ^ n := by
  dsimp
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.fib_add_two, Nat.cast_add, pow_succ]
    linear_combination -ih

lemma four_dvd_of_odd_zero {p n : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (hn : Odd n)
    (hd : p ∣ Nat.fib n) : 4 ∣ p - 1 := by
  let : Fact p.Prime := ⟨hp⟩
  have hz := (ZMod.natCast_eq_zero_iff ..).mpr hd
  have sq : (Nat.fib (n + 1) : ZMod p) ^ 2 = -1 := by
    simpa [hz, hn.neg_one_pow] using signed_cassini p n
  have := ZMod.mod_four_ne_three_of_sq_eq_neg_one sq
  have := hp.eq_two_or_odd.resolve_left h2
  omega

-- This form of Binet's identity avoids division by the difference of the two roots.
lemma fib_root_difference {K : Type*} [Field K] {a b : K}
    (ha : a ^ 2 = a + 1) (hb : b ^ 2 = b + 1) (n : ℕ) :
    (Nat.fib n : K) * (a - b) = a ^ n - b ^ n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n h0 h1 =>
    rw [Nat.fib_add_two, Nat.cast_add, add_mul, h0, h1, pow_add a n 2, pow_add b n 2, ha, hb, pow_succ, pow_succ]
    ring

-- Frobenius permutes the two distinct roots of X²-X-1 in characteristic p.
lemma rank_dvd_neighbor {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h5 : p ≠ 5) :
    rankOfApparition p ∣ p - 1 ∨ rankOfApparition p ∣ p + 1 := by
  let : Fact p.Prime := ⟨hp⟩
  let K := AlgebraicClosure (ZMod p)
  have two : (2 : K) ≠ 0 := CharP.cast_ne_zero_of_ne_of_prime K Nat.prime_two h2
  have five : (5 : K) ≠ 0 := CharP.cast_ne_zero_of_ne_of_prime K (by decide : Nat.Prime 5) h5
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (5 : K) (by decide : 0 < 2)
  let a := (1 + s) / 2
  let b := 1 - a
  have twice : a * 2 = 1 + s := div_mul_cancel₀ _ two
  have ha : a ^ 2 = a + 1 := by
    have h : (2 : K)^2 * (a ^ 2 - (a + 1)) = 0 := by
      linear_combination (2 * a - 1 + s) * twice + hs
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (pow_ne_zero _ two))
  have hb : b ^ 2 = b + 1 := by dsimp [b]; linear_combination ha
  have diff : a - b ≠ 0 := by
    intro h
    have ab : a - b = s := by dsimp only [b]; linear_combination twice
    rw [ab] at h
    exact five (by simpa [h] using hs.symm)
  have zero_of_equal (n : ℕ) (h : a ^ n = b ^ n) : rankOfApparition p ∣ n := by
    apply rank_dvd_iff_fib.mpr
    apply (CharP.cast_eq_zero_iff K p _).mp
    apply (mul_eq_zero.mp ?_).resolve_right diff
    rw [fib_root_difference ha hb, h, sub_self]
  have hroot : (a ^ p) ^ 2 = a ^ p + 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, ha, add_pow_char _ _ p, one_pow]
  have poly : (a ^ p - a) * (a ^ p - b) = 0 := by
    dsimp [b]
    linear_combination hroot - ha
  have conj : b ^ p = 1 - a ^ p := by simp [b, sub_pow_char]
  rcases mul_eq_zero.mp poly with h | h
  · have fix := sub_eq_zero.mp h
    have fixb : b ^ p = b := by rw [conj, fix]
    have unit (x : K) (hx : x ^ 2 = x + 1) (hf : x ^ p = x) : x ^ (p - 1) = 1 := by
      have hn : x ≠ 0 := by rintro rfl; simp at hx
      apply mul_right_cancel₀ hn
      rw [one_mul, ← pow_succ, Nat.sub_add_cancel hp.one_lt.le, hf]
    exact Or.inl (zero_of_equal _ ((unit a ha fix).trans (unit b hb fixb).symm))
  · have swap := sub_eq_zero.mp h
    have swapb : b ^ p = a := by rw [conj, swap]; dsimp [b]; ring
    exact Or.inr (zero_of_equal _ (by rw [pow_succ, pow_succ, swap, swapb, mul_comm]))

lemma aligned_odd_factor {q p n : ℕ} (hq : q.Prime) (hq5 : 5 < q) (hp : p.Prime)
    (hc : p ≡ 1 [MOD q]) (hn : Odd n) (hd : p ∣ Nat.fib n) : 4 * q ∣ p - 1 := by
  have hqdiv : q ∣ p - 1 := hc.symm.dvd'
  have pos : 0 < p - 1 := by have := hp.one_lt; omega
  have lower := Nat.le_of_dvd pos hqdiv
  have four := four_dvd_of_odd_zero hp (by omega) hn hd
  have cop : Nat.Coprime 4 q := by
    apply Nat.Coprime.symm
    apply hq.coprime_iff_not_dvd.mpr
    exact fun h => (Nat.not_le_of_lt (by omega : 4 < q)) (Nat.le_of_dvd (by decide) h)
  exact cop.mul_dvd_of_dvd_of_dvd four hqdiv

lemma odd_totient_lower_bound {q n : ℕ} (hq : q.Prime) (hq5 : 5 < q) (hn : Odd n)
    (ht : q ∣ (Nat.fib n).totient) : 4 * q < Nat.fib n := by
  have pos : 0 < n := by obtain ⟨k, hk⟩ := hn; omega
  have hf := Nat.fib_pos.mpr pos
  rcases (totient_witness_iff hq pos).mp ht with hs | ⟨p, hp, hc, hd⟩
  · have bound := Nat.le_of_dvd hf hs
    exact lt_of_lt_of_le (by rw [pow_two]; exact Nat.mul_lt_mul_of_pos_right (by omega) hq.pos) bound
  · have h := Nat.le_of_dvd (show 0 < p - 1 by have := hp.one_lt; omega)
        (aligned_odd_factor hq hq5 hp hc hn hd)
    have := Nat.le_of_dvd hf hd
    omega

-- F₁₃ = 233, so the residue represented by 13 is excluded uniformly from q = 59 onward.
lemma thirteen_not_good {q : ℕ} (hq : q.Prime) (h : 59 ≤ q) : 13 ∉ S q := by
  intro hr
  have bound := odd_totient_lower_bound hq (by omega) (n := 13) (by decide) (hr.2 13 rfl)
  have fib : Nat.fib 13 = 233 := by decide
  omega

-- The congruences alone admit arbitrarily large candidate primes for every positive index.
lemma congruence_candidates_unbounded {q l : ℕ} (hq : 0 < q) (hl : 0 < l) (B : ℕ) :
    ∃ p > B, p.Prime ∧ 4 * q ∣ p - 1 ∧ l ∣ p - 1 := by
  let m := 4 * q * l
  have hm : m ≠ 0 := by dsimp [m]; positivity
  obtain ⟨p, hB, hp, hc⟩ := Nat.forall_exists_prime_gt_and_modEq B hm (Nat.coprime_one_left m)
  have hd : m ∣ p - 1 := hc.symm.dvd'
  exact ⟨p, hB, hp, (dvd_mul_right (4*q) l).trans hd, (dvd_mul_left l (4*q)).trans hd⟩

lemma coprime_progression_witness {q r l : ℕ} (hq : q.Prime) (hq5 : 5 < q) (hr : r ∈ S q)
    (hg : r.Coprime (pisano q)) (hbad : ¬ q ∣ (Nat.fib (pisano q)).totient)
    (hl : l.Prime) (hodd : Odd l) (hc : l ≡ r [MOD pisano q])
    (hex : rankOfApparition (q ^ 2) ≠ l) :
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD q] ∧ rankOfApparition p = l ∧
      4 * q ∣ p - 1 ∧ (l ∣ p - 1 ∨ l ∣ p + 1) := by
  have hc' : r.gcd (pisano q) * l ≡ r [MOD pisano q] := by simpa [hg.gcd_eq_one] using hc
  have cover := prime_progression_coverage hq hr hbad hl hc'
  simp only [hg.gcd_eq_one, Nat.gcd_one_right, Nat.div_one] at cover
  obtain ⟨p, hp, hmod, he⟩ := cover.resolve_left hex
  have hd : q ∣ p - 1 := hmod.symm.dvd'
  have ple := Nat.le_of_dvd (show 0 < p - 1 by have := hp.one_lt; omega) hd
  have p2 : p ≠ 2 := by omega
  have p5 : p ≠ 5 := by omega
  have four := aligned_odd_factor hq hq5 hp hmod hodd (rank_dvd_iff_fib.mp (he ▸ dvd_refl l))
  exact ⟨p, hp, hmod, he, four, he ▸ rank_dvd_neighbor hp p2 p5⟩

lemma square_quotient_test {q g t : ℕ} (hq : q.Prime) (hg : 0 < g) (hd : ¬ q ∣ Nat.fib g) :
    q ^ 2 ∣ Nat.fib (g * t) / Nat.fib g ↔
      rankOfApparition (q ^ 2) / (rankOfApparition (q ^ 2)).gcd g ∣ t := by
  rw [← normalized_square_test hg, ← fib_quotient_product g t]
  rw [Nat.mul_div_cancel_left _ (Nat.fib_pos.mpr hg)]
  exact ⟨fun h => dvd_mul_of_dvd_right h _, ((hq.coprime_iff_not_dvd.mpr hd).pow_left 2).dvd_of_dvd_mul_left⟩

lemma quotient_exception_iff {q g P t : ℕ} (hq : q.Prime) (hP : 0 < P)
    (hgP : g ∣ P) (ht : 0 < t) (hbad : ¬ q ∣ (Nat.fib P).totient) :
    let c := Nat.fib (g * t) / Nat.fib g
    (¬ q ∣ (Nat.fib (g * t)).totient) ↔
      (¬ (if q ∣ Nat.fib g then q else q ^ 2) ∣ c) ∧
        ∀ p : ℕ, p.Prime → p ≡ 1 [MOD q] → ¬ p ∣ c := by
  dsimp only
  have hg := Nat.pos_of_dvd_of_pos hgP hP
  have common := Nat.fib_dvd _ _ hgP
  have badg : ¬ q ∣ (Nat.fib g).totient :=
    fun h => hbad (h.trans (Nat.totient_dvd_of_dvd common))
  rw [totient_witness_iff hq hg, not_or] at badg
  rw [totient_witness_iff hq (Nat.mul_pos hg ht), ← fib_quotient_product g t,
    not_or, square_in_product hq badg.1, Nat.mul_div_cancel_left _ (Nat.fib_pos.mpr hg)]
  constructor
  · rintro ⟨hs, hp⟩
    exact ⟨hs, fun p hpr hc hd => hp ⟨p, hpr, hc, dvd_mul_of_dvd_right hd _⟩⟩
  · rintro ⟨hs, hp⟩
    refine ⟨hs, ?_⟩
    rintro ⟨p, hpr, hc, hd⟩
    rcases hpr.dvd_mul.mp hd with ha | hb
    · exact badg.2 ⟨p, hpr, hc, ha⟩
    · exact hp p hpr hc hb

-- An exception has positive index since the totient at index zero is zero.
lemma exception_multiplier {q r P : ℕ}
    (h : ¬ ∀ m : ℕ, m ≡ r [MOD P] → q ∣ (Nat.fib m).totient) :
    ∃ t : ℕ, 0 < t ∧ r.gcd P * t ≡ r [MOD P] ∧ ¬ q ∣ (Nat.fib (r.gcd P * t)).totient := by
  push Not at h
  obtain ⟨m, hm, hbad⟩ := h
  obtain ⟨t, rfl⟩ := gcd_dvd_class hm
  refine ⟨t, Nat.pos_of_ne_zero ?_, hm, hbad⟩
  rintro rfl
  simp at hbad

-- All primes in a totient witness at indices 1 through 48 come either from
-- a repeated Fibonacci factor or from the predecessor of a Fibonacci factor.
set_option maxRecDepth 4000 in
set_option maxHeartbeats 3000000 in
lemma small_candidate_pairs {q r : ℕ} (hq : q.Prime) (hl : 53 < q)
    (hr : 0 < r) (hb : r ≤ 48) (ht : q ∣ (Nat.fib r).totient) :
    (q, r) ∈ ([(199,23), (139,31), (151,31), (1103,32), (181,41), (89,43),
      (199,43), (211,43), (199,46), (139,47), (461,47)] : List (ℕ × ℕ)) := by
  let factors : List ℕ :=
    [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 61, 73, 89, 107,
     109, 113, 139, 149, 199, 211, 233, 281, 307, 421, 461, 521, 557, 1103, 1597,
     2161, 2207, 2221, 2417, 2789, 3001, 3571, 9349, 19801, 28657, 59369, 109441,
     135721, 141961, 514229, 433494437, 2971215073]
  let predecessors : List ℕ :=
    [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 53, 89, 139, 151, 181, 199, 211, 461, 1103]
  have primes : ∀ a ∈ factors, Nat.Prime a := by norm_num [factors, List.forall_mem_cons]
  have predpr : ∀ a ∈ predecessors, Nat.Prime a := by norm_num [predecessors, List.forall_mem_cons]
  have fibs : ∀ j : Fin 49, 0 < j.val → Nat.fib j.val ∣ factors.prod ^ 8 := by decide
  have preds : ∀ p ∈ factors, p - 1 ∣ predecessors.prod ^ 16 := by decide
  have mem (p : ℕ) (hp : p.Prime) (hd : p ∣ Nat.fib r) : p ∈ factors :=
    OMA.R_arxiv_2604_17847_R1.prime_mem_of_dvd_product hp factors primes
      (hp.dvd_of_dvd_pow (hd.trans (fibs ⟨r, by omega⟩ hr)))
  have sq : ∀ a ∈ factors, 53 < a → ∀ j : Fin 49, 0 < j.val → ¬ a ^ 2 ∣ Nat.fib j.val := by decide
  rcases (totient_witness_iff hq hr).mp ht with hs | ⟨p, hp, hc, hd⟩
  · exact (sq q (mem q hq ((dvd_pow_self q (by decide : 2 ≠ 0)).trans hs)) hl ⟨r, by omega⟩ hr hs).elim
  · have pm := mem p hp hd
    have qm := OMA.R_arxiv_2604_17847_R1.prime_mem_of_dvd_product hq predecessors predpr
      (hq.dvd_of_dvd_pow (hc.symm.dvd'.trans (preds p pm)))
    have table : ∀ a ∈ predecessors, 53 < a → ∀ j : Fin 49, 0 < j.val →
        ∀ b ∈ factors, b ≡ 1 [MOD a] → b ∣ Nat.fib j.val →
        (a, j.val) ∈ ([(199,23), (139,31), (151,31), (1103,32), (181,41), (89,43),
          (199,43), (211,43), (199,46), (139,47), (461,47)] : List (ℕ × ℕ)) := by decide
    exact table q qm hl ⟨r, by omega⟩ hr p pm hc hd

lemma period_1103 : pisano 1103 = 96 :=
  OMA.R_arxiv_2604_17847_R1.pisano_eq_of_certificate (by decide) (by decide) (by decide)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 3000000 in
lemma positive_through_48 {q r : ℕ} (hq : q.Prime) (hl : 53 < q)
    (hr : 0 < r) (hb : r ≤ 48) : r ∈ S q ↔ q = 1103 ∧ r = 32 := by
  let candidates : List (ℕ × ℕ) := [(199,23), (139,31), (151,31), (1103,32), (181,41),
    (89,43), (199,43), (211,43), (199,46), (139,47), (461,47)]
  let periods : List (ℕ × ℕ) := [(199,22), (139,46), (151,50), (1103,96),
    (181,90), (89,44), (211,42), (461,46)]
  constructor
  · intro good
    by_contra hn
    have member : (q,r) ∈ candidates := small_candidate_pairs hq hl hr hb (good.2 r rfl)
    have lookup : ∀ c ∈ candidates, c.1 ∈ periods.map Prod.fst := by decide
    obtain ⟨⟨a,P⟩, hrow, heq⟩ := List.mem_map.mp (lookup _ member)
    change a = q at heq
    subst a
    have certificates : ∀ row ∈ periods, let Q := row.1; let T := row.2
        (0 < T ∧ Nat.fib T ≡ 0 [MOD Q] ∧ Nat.fib (T+1) ≡ 1 [MOD Q]) ∧
        ∀ j : Fin T, 0 < j.val → ¬ (Nat.fib j.val ≡ 0 [MOD Q] ∧ Nat.fib (j.val+1) ≡ 1 [MOD Q]) := by decide
    obtain ⟨⟨hP, h0, h1⟩, hm⟩ := certificates _ hrow
    have period : pisano q = P := OMA.R_arxiv_2604_17847_R1.pisano_eq_of_certificate hP ⟨h0,h1⟩ hm
    -- The only second representatives needed are 77, 81, 87, and 131.
    have large : Nat.Prime 1066340417491710595814572169 := by
      apply OMA.R_arxiv_2604_17847_R1.prime_of_predecessor_factors _ 3
        [2, 2, 2, 11, 89, 131, 199, 521, 2081, 9901, 19801, 24571] (by decide)
      · norm_num [List.forall_mem_cons]
      · reduce_mod_char
      · simp only [List.forall_mem_cons]
        repeat' apply And.intro
        all_goals (reduce_mod_char; decide)
    let primes : List ℕ := [2, 13, 17, 53, 89, 109, 173, 2269, 4373, 19441, 514229,
      988681, 4832521, 3821263937, 1066340417491710595814572169]
    have prime_entries : ∀ p ∈ primes, Nat.Prime p := by
      simp only [primes, List.forall_mem_cons, large, true_and]
      norm_num
    have data : ∀ row ∈ periods, ∀ c ∈ candidates, c.1 = row.1 → c.2 < row.2 →
        ¬ (c.1 = 1103 ∧ c.2 = 32) →
        let n := c.2 + row.2
        let safe := primes.filter (fun p => decide (¬ p ≡ 1 [MOD row.1]))
        ¬ row.1 ^ 2 ∣ Nat.fib n ∧ Nat.fib n ∣ safe.prod ^ 2 := by decide
    have lt : r < P := period ▸ good.1
    obtain ⟨hs, hd⟩ := data _ hrow _ member rfl lt hn
    let safe := primes.filter (fun p => decide (¬ p ≡ 1 [MOD q]))
    have pr : ∀ p ∈ safe, Nat.Prime p ∧ ¬ p ≡ 1 [MOD q] := fun p h =>
      ⟨prime_entries p (List.mem_filter.mp h).1, of_decide_eq_true (List.mem_filter.mp h).2⟩
    have bad := OMA.R_arxiv_2604_17847_R1.totient_exception_of_factors hq
      (show 0 < r + P by omega) safe pr hs hd
    exact bad (good.2 _ (by rw [period]; simp [Nat.ModEq]))
  · rintro ⟨rfl,rfl⟩
    apply OMA.R_arxiv_2604_17847_R1.good_residue_of_common_index (p := 2207) (d := 32)
    · rw [period_1103]; decide
    · norm_num
    · decide
    · decide
    · decide
    · rw [period_1103]; decide

lemma large_residue_of_failed_descent {q r : ℕ} (hq : q.Prime) (hl : 53 < q) (good : r ∈ S q)
    (hbad : ¬ q ∣ (Nat.fib (pisano q)).totient) : 48 < r := by
  by_contra! hb
  by_cases hz : r = 0
  · subst r
    exact hbad (good.2 _ (Nat.modEq_zero_iff_dvd.mpr (dvd_refl _)))
  obtain ⟨rfl,rfl⟩ := (positive_through_48 hq hl (Nat.pos_of_ne_zero hz) hb).mp good
  apply hbad
  rw [period_1103]
  apply (totient_witness_iff (by norm_num : Nat.Prime 1103) (by decide : 0 < 96)).mpr
  exact Or.inr ⟨2207, by norm_num, by decide, by decide⟩

theorem main : H1 → H2 → OMA.R_arxiv_2604_17847_R1.H1 := by
  intro first second q r hq hlarge hr _
  have hP := Nat.zero_lt_of_lt hr.1
  apply (finite_prime_cover_iff hq hP).mpr
  by_contra hbad
  let g := r.gcd (pisano q)
  have fail (t : ℕ) (ht : 0 < t) (hc : g * t ≡ r [MOD pisano q]) :=
    mt (quotient_exception_iff hq hP (Nat.gcd_dvd_right r _) ht hbad).mpr
      (not_not_intro (hr.2 _ hc))
  have large (h : Odd r) := odd_totient_lower_bound hq (by omega) h (hr.2 r rfl)
  have sieve (t : ℕ) := witness_sieve_iff (t := t) hq hP (Nat.gcd_dvd_right r _) hbad
  by_cases hd : q ∣ Nat.fib (r.gcd (pisano q))
  · obtain ⟨t, ht, hc, hs, hp⟩ := second q r hq hlarge hr.1 hbad (large_residue_of_failed_descent hq hlarge hr hbad) large hd
    have hg := Nat.gcd_pos_of_pos_right r hP
    have no := mt (prime_dvd_quotient_iff hq hg hd t).mp hs
    exact fail t ht hc ⟨by simpa only [if_pos hd] using no, (sieve t).mpr hp⟩
  · obtain ⟨t, ht, hc, hs, hp⟩ := first q r hq hlarge hr.1 hbad (large_residue_of_failed_descent hq hlarge hr hbad) large hd
    have no := mt (square_quotient_test (t := t) hq (Nat.gcd_pos_of_pos_right r hP) hd).mp hs
    exact fail t ht hc ⟨by simpa only [if_neg hd] using no, (sieve t).mpr hp⟩

-- Conversely, failure of descent supplies the recurring rank family used by the parent.
lemma quotient_problems_of_cover (cover : OMA.R_arxiv_2604_17847_R1.H1) : H1 ∧ H2 := by
  have pick (q r : ℕ) (hq : q.Prime) (hl : 53 < q) (hr : r < pisano q)
      (hbad : ¬ q ∣ (Nat.fib (pisano q)).totient) :
      let g := r.gcd (pisano q)
      ∃ t : ℕ, 0 < t ∧ g * t ≡ r [MOD pisano q] ∧
        (¬ (if q ∣ Nat.fib g then q else q ^ 2) ∣ (Nat.fib (g * t) / Nat.fib g)) ∧
        ∀ p : ℕ, p.Prime → p ≡ 1 [MOD q] → ¬ p ∣ (Nat.fib (g * t) / Nat.fib g) := by
    have hP := Nat.zero_lt_of_lt hr
    have missing : ¬ ∀ m : ℕ, m ≡ r [MOD pisano q] → q ∣ (Nat.fib m).totient := by
      intro hall
      have good : r ∈ S q := ⟨hr, hall⟩
      exact hbad ((finite_prime_cover_iff hq hP).mp (cover q r hq hl good (fixed_rank_family hq good hbad)))
    obtain ⟨t, ht, hc, he⟩ := exception_multiplier missing
    exact ⟨t, ht, hc, (quotient_exception_iff hq hP (Nat.gcd_dvd_right r _) ht hbad).mp he⟩
  constructor
  · intro q r hq hl hr hbad _ _
    dsimp only
    intro hd
    obtain ⟨t, ht, hc, hs, hp⟩ := pick q r hq hl hr hbad
    rw [if_neg hd, square_quotient_test hq (Nat.gcd_pos_of_pos_right r (Nat.zero_lt_of_lt hr)) hd] at hs
    exact ⟨t, ht, hc, hs, (witness_sieve_iff hq (Nat.zero_lt_of_lt hr) (Nat.gcd_dvd_right r _) hbad).mp hp⟩
  · intro q r hq hl hr hbad _ _
    dsimp only
    intro hd
    obtain ⟨t, ht, hc, hs, hp⟩ := pick q r hq hl hr hbad
    rw [if_pos hd, prime_dvd_quotient_iff hq (Nat.gcd_pos_of_pos_right r (Nat.zero_lt_of_lt hr)) hd] at hs
    exact ⟨t, ht, hc, hs, (witness_sieve_iff hq (Nat.zero_lt_of_lt hr) (Nat.gcd_dvd_right r _) hbad).mp hp⟩

end OMA.R_arxiv_2604_17847_R1_H1_R1
