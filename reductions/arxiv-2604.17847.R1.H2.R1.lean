import OMAReductions.R_arxiv_2604_17847_R1
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

-- Reduction arxiv-2604.17847.R1.H2.R1 of the exceptional square step.
-- Credit: @wispiANt

namespace OMA.R_arxiv_2604_17847_R1_H2_R1

open OMA.S_arxiv_2604_17847
open OMA.R_arxiv_2604_17847_R1 (rank_dvd_index pisano_eq_of_certificate)

-- An aligned companion forces the upper neighbor to be the square zero.
def H1 : Prop :=
  ∀ q : ℕ, q.Prime → 1000 < q → 96 < pisano q →
    (q ^ 2 ∣ Nat.fib (q-1) ∨ q ^ 2 ∣ Nat.fib (q+1)) →
    (2*q+1).Prime ∧ q ^ 2 ∣ Nat.fib (q+1)

-- At the upper neighbor, only the common part of the two indices matters.
def H2 : Prop :=
  ∀ q : ℕ, q.Prime → 1000 < q → 96 < pisano q → q ^ 2 ∣ Nat.fib (q+1) →
    (2*q+1).Prime → 2*q+1 ∣ Nat.fib ((pisano q).gcd (2*(q+1)))

-- Consecutive values form a finite reversible orbit for every positive modulus.
lemma fib_pair_iterate (q n : ℕ) :
    (fun x : ZMod q × ZMod q => (x.2, x.1 + x.2))^[n] (0, 1) =
      ((Nat.fib n : ZMod q), (Nat.fib (n + 1) : ZMod q)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    simp [Nat.fib_add_two]

lemma period_and_returns (q : ℕ) [NeZero q] :
    0 < pisano q ∧ ∀ n : ℕ, pisano q ∣ n ↔
      (q ∣ Nat.fib n ∧ Nat.fib (n + 1) ≡ 1 [MOD q]) := by
  let T := fun x : ZMod q × ZMod q => (x.2, x.1 + x.2)
  let x : ZMod q × ZMod q := (0, 1)
  have inj : Function.Injective T := by
    rintro ⟨a,b⟩ ⟨c,d⟩ h
    obtain ⟨rfl, he⟩ : b = d ∧ a + b = c + d := Prod.mk.inj h
    exact Prod.ext (add_right_cancel he) rfl
  have ret (n : ℕ) : Function.IsPeriodicPt T n x ↔
      q ∣ Nat.fib n ∧ Nat.fib (n + 1) ≡ 1 [MOD q] := by
    change T^[n] x = x ↔ _
    rw [show T^[n] x = _ from fib_pair_iterate q n]
    change (_, _) = (0, 1) ↔ _
    rw [Prod.mk.injEq, ZMod.natCast_eq_zero_iff, ← Nat.cast_one (R := ZMod q),
      ZMod.natCast_eq_natCast_iff]
  let P := Function.minimalPeriod T x
  have pos : 0 < P := Function.minimalPeriod_pos_of_mem_periodicPts (inj.mem_periodicPts x)
  have starts := (ret P).mp (Function.isPeriodicPt_minimalPeriod T x)
  have eq : pisano q = P := by
    apply pisano_eq_of_certificate pos ⟨Nat.modEq_zero_iff_dvd.mpr starts.1, starts.2⟩
    intro j hj h
    have hd := ((ret j).mpr ⟨Nat.modEq_zero_iff_dvd.mp h.1, h.2⟩).minimalPeriod_dvd
    exact (Nat.not_le_of_lt j.isLt) (Nat.le_of_dvd hj hd)
  rw [eq]
  exact ⟨pos, fun n => Function.isPeriodicPt_iff_minimalPeriod_dvd.symm.trans (ret n)⟩

-- Cassini gives the determinant of the Fibonacci recurrence after k steps.
lemma cassini_signed (q n : ℕ) :
    let a : ZMod q := Nat.fib n
    let b : ZMod q := Nat.fib (n + 1)
    b ^ 2 - a * b - a ^ 2 = (-1) ^ n := by
  dsimp
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.fib_add_two, Nat.cast_add, pow_succ]
    linear_combination -ih

-- The odd half-index test uses the Lucas number L_k = 2 F_(k+1) - F_k.
lemma period_dvd_double_iff (m k : ℕ) [NeZero m] :
    pisano m ∣ 2 * k ↔ m ∣ (if Even k then Nat.fib k else 2 * Nat.fib (k+1) - Nat.fib k) := by
  let a : ZMod m := Nat.fib k
  let b : ZMod m := Nat.fib (k+1)
  have le : Nat.fib k ≤ 2 * Nat.fib (k+1) := by have := Nat.fib_le_fib_succ (n := k); omega
  have pair : pisano m ∣ 2 * k ↔ a * (2*b-a) = 0 ∧ b^2 + a^2 = 1 := by
    rw [(period_and_returns m).2, ← ZMod.natCast_eq_zero_iff, ← ZMod.natCast_eq_natCast_iff,
      Nat.fib_two_mul, Nat.fib_two_mul_add_one, Nat.cast_mul, Nat.cast_sub le]
    simp [a, b]
  rw [pair]
  by_cases he : Even k
  · rw [if_pos he, ← ZMod.natCast_eq_zero_iff]
    change _ ↔ a = 0
    have det : b^2 - a*b - a^2 = 1 := by simpa only [he.neg_one_pow] using cassini_signed m k
    constructor
    · rintro ⟨hy, hx⟩
      linear_combination (b-a) * hx - a * hy - b * det
    · intro h
      exact ⟨by rw [h, zero_mul], by simpa [h] using det⟩
  · rw [if_neg he, ← ZMod.natCast_eq_zero_iff, Nat.cast_sub le, Nat.cast_mul, Nat.cast_ofNat]
    change _ ↔ 2*b-a = 0
    have odd : Odd k := Nat.not_even_iff_odd.mp he
    have det : b^2 - a*b - a^2 = -1 := by simpa only [odd.neg_one_pow] using cassini_signed m k
    constructor
    · rintro ⟨hy,hx⟩
      linear_combination (a-b) * hx + a * hy + b * det
    · intro h
      exact ⟨by rw [h, mul_zero], by linear_combination b * h - det⟩

-- The gcd of the two return coordinates has the same closed form as the period test.
lemma double_return_gcd (k : ℕ) :
    (Nat.fib (2*k)).gcd (Nat.fib (2*k+1) - 1) =
      (if Even k then Nat.fib k else 2 * Nat.fib (k+1) - Nat.fib k) := by
  by_cases hk : k = 0
  · subst k; decide
  let G := (Nat.fib (2*k)).gcd (Nat.fib (2*k+1) - 1)
  let C := if Even k then Nat.fib k else 2 * Nat.fib (k+1) - Nat.fib k
  have first : 0 < Nat.fib (2*k) := Nat.fib_pos.mpr (by omega)
  have next : 1 ≤ Nat.fib (2*k+1) := Nat.fib_pos.mpr (by omega)
  have hg : 0 < G := Nat.gcd_pos_of_pos_left _ first
  have hc : 0 < C := by
    have pos := Nat.fib_pos.mpr (Nat.pos_of_ne_zero hk)
    have le := Nat.fib_le_fib_succ (n := k)
    dsimp [C]
    split <;> omega
  have equiv (m : ℕ) (hm : 0 < m) : m ∣ G ↔ m ∣ C := by
    let : NeZero m := ⟨hm.ne'⟩
    rw [show m ∣ C ↔ pisano m ∣ 2*k from (period_dvd_double_iff m k).symm,
      (period_and_returns m).2]
    change m ∣ (Nat.fib (2*k)).gcd _ ↔ _
    rw [Nat.dvd_gcd_iff, ← Nat.modEq_iff_dvd' next]
    exact and_congr_right fun _ => Nat.ModEq.comm
  exact Nat.dvd_antisymm ((equiv G hg).mp (dvd_refl _)) ((equiv C hc).mpr (dvd_refl _))

lemma even_period {m : ℕ} (hm : 2 < m) : Even (pisano m) := by
  let : NeZero m := ⟨by omega⟩
  by_contra he
  have odd := Nat.not_even_iff_odd.mp he
  have ret := ((period_and_returns m).2 _).mp (dvd_refl (pisano m))
  have zero := (ZMod.natCast_eq_zero_iff ..).mpr ret.1
  have one : (Nat.fib (pisano m + 1) : ZMod m) = 1 := by
    simpa only [Nat.cast_one] using (ZMod.natCast_eq_natCast_iff _ 1 m).mpr ret.2
  have bad : (1 : ZMod m) = -1 := by simpa [zero, one, odd.neg_one_pow] using cassini_signed m (pisano m)
  have two : ((2 : ℕ) : ZMod m) = 0 := by push_cast; linear_combination bad
  exact (Nat.not_le_of_lt hm) (Nat.le_of_dvd (by decide) ((ZMod.natCast_eq_zero_iff ..).mp two))

-- Each Fibonacci step negates the Cassini expression and preserves its square.
lemma cassini_square (q n : ℕ) :
    let a : ZMod q := Nat.fib n
    let b : ZMod q := Nat.fib (n + 1)
    (b ^ 2 - a * b - a ^ 2) ^ 2 = 1 := by
  have h := congrArg (fun x : ZMod q => x ^ 2) (cassini_signed q n)
  apply h.trans
  rw [← pow_mul, Nat.mul_comm n 2, pow_mul, neg_one_sq, one_pow]

lemma fourfold_return {q n : ℕ} [NeZero q] (hz : q ∣ Nat.fib n) :
    pisano q ∣ 2 * (2 * n) := by
  apply ((period_and_returns q).2 _).mpr
  have twice := hz.trans (Nat.fib_dvd _ _ (dvd_mul_left n 2))
  have four := twice.trans (Nat.fib_dvd _ _ (dvd_mul_left (2 * n) 2))
  refine ⟨four, (ZMod.natCast_eq_natCast_iff _ _ _).mp ?_⟩
  have a := (ZMod.natCast_eq_zero_iff _ _).mpr hz
  have b := (ZMod.natCast_eq_zero_iff _ _).mpr twice
  have inv := cassini_square q n
  simpa [Nat.fib_two_mul_add_one, Nat.cast_add, Nat.cast_pow, b, a] using
    (show (((Nat.fib (n + 1) : ZMod q) ^ 2) ^ 2) = 1 by simpa [a] using inv)

lemma power_at_double (k : ℕ) {q n : ℕ} (hq : q.Prime) (hodd : 2 < q) (hz : q ∣ Nat.fib n) :
    q ^ k ∣ Nat.fib (2 * n) ↔ q ^ k ∣ Nat.fib n := by
  rw [Nat.fib_two_mul]
  have hc : q.Coprime (2 * Nat.fib (n + 1) - Nat.fib n) := by
    apply hq.coprime_iff_not_dvd.mpr
    intro h
    have le : Nat.fib n ≤ 2 * Nat.fib (n + 1) := by
      have := Nat.fib_le_fib_succ (n := n)
      omega
    have hd := Nat.dvd_add h hz
    rw [Nat.sub_add_cancel le] at hd
    rcases hq.dvd_mul.mp hd with htwo | hnext
    · exact (Nat.not_le_of_lt hodd) (Nat.le_of_dvd (by decide) htwo)
    · have hone := Nat.dvd_gcd hz hnext
      rw [Nat.fib_coprime_fib_succ n] at hone
      exact hq.not_dvd_one hone
  exact ⟨(hc.pow_left k).dvd_of_dvd_mul_right, fun h => dvd_mul_of_dvd_left h _⟩

-- The period and the first zero give the same divisibility test for every power of q.
lemma power_at_rank_iff (k : ℕ) {q : ℕ} (hq : q.Prime) (hodd : 2 < q) :
    q ^ k ∣ Nat.fib (pisano q) ↔ q ^ k ∣ Nat.fib (rankOfApparition q) := by
  let : NeZero q := ⟨hq.ne_zero⟩
  obtain ⟨hP, returns⟩ := period_and_returns q
  have hz := ((returns _).mp (dvd_refl (pisano q))).1
  have first : 0 < rankOfApparition q ∧ q ∣ Nat.fib (rankOfApparition q) :=
    Nat.sInf_mem (s := {j : ℕ | 0 < j ∧ q ∣ Nat.fib j}) ⟨_, hP, hz⟩
  have twice := first.2.trans (Nat.fib_dvd _ _ (dvd_mul_left _ 2))
  constructor
  · intro h
    exact (power_at_double k hq hodd first.2).mp ((power_at_double k hq hodd twice).mp
      (h.trans (Nat.fib_dvd _ _ (fourfold_return first.2))))
  · exact fun h => h.trans (Nat.fib_dvd _ _ (rank_dvd_index hP hz))

-- A return modulo b is also a return modulo every positive divisor of b.
lemma period_dvd_of_dvd {a b : ℕ} [NeZero a] [NeZero b] (h : a ∣ b) :
    pisano a ∣ pisano b := by
  have ret := ((period_and_returns b).2 _).mp (dvd_refl (pisano b))
  exact ((period_and_returns a).2 _).mpr ⟨h.trans ret.1, ret.2.of_dvd h⟩

lemma fourth_root_at_zero {m n : ℕ} (hz : m ∣ Nat.fib n) :
    Nat.fib (n + 1) ^ 4 ≡ 1 [MOD m] := by
  have zero := (ZMod.natCast_eq_zero_iff ..).mpr hz
  apply (ZMod.natCast_eq_natCast_iff ..).mp
  simpa [zero, ← pow_mul] using cassini_square m n

-- The cofactor in u^4 - 1 reduces to 4 modulo q and is a unit at every odd prime q.
lemma lift_fourth_root {q u : ℕ} (k : ℕ) (hq : q.Prime) (hodd : 2 < q)
    (hu : 0 < u) (hone : u ≡ 1 [MOD q]) (hfour : u ^ 4 ≡ 1 [MOD q ^ k]) :
    u ≡ 1 [MOD q ^ k] := by
  obtain ⟨v, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hu.ne'
  let u := v + 1
  let c := u ^ 3 + u ^ 2 + u + 1
  have hc : c ≡ 4 [MOD q] := by
    simpa [c, u] using (((hone.pow 3).add (hone.pow 2)).add hone).add
      (Nat.ModEq.refl (n := q) 1)
  have cop : q.Coprime c := by
    apply hq.coprime_iff_not_dvd.mpr
    intro hd
    have four := (hc.dvd_iff (dvd_refl q)).mp hd
    have two := hq.dvd_of_dvd_pow (show q ∣ 2 ^ 2 from four)
    exact (Nat.not_le_of_lt hodd) (Nat.le_of_dvd (by decide) two)
  have factor : v * c + 1 = u ^ 4 := by dsimp [u, c]; ring
  have prod : v * c ≡ 0 [MOD q ^ k] := by
    apply Nat.ModEq.add_right_cancel (Nat.ModEq.refl (n := q ^ k) 1)
    rw [factor]
    exact hfour
  have hd := (cop.pow_left k).dvd_of_dvd_mul_right (Nat.modEq_zero_iff_dvd.mp prod)
  exact (Nat.modEq_zero_iff_dvd.mpr hd).add (Nat.ModEq.refl 1)

-- The first zero supplies the first return at the old period as soon as its
-- Fibonacci value is divisible by the higher power.
lemma period_power_eq_iff_at_period {q k : ℕ} (hq : q.Prime) (hodd : 2 < q) (hk : 0 < k) :
    pisano (q ^ k) = pisano q ↔ q ^ k ∣ Nat.fib (pisano q) := by
  let : NeZero q := ⟨hq.ne_zero⟩
  have returns := (period_and_returns (q ^ k)).2
  have lower := period_dvd_of_dvd (dvd_pow_self q hk.ne')
  have old := ((period_and_returns q).2 _).mp (dvd_refl (pisano q))
  constructor
  · intro heq
    exact ((returns _).mp (heq ▸ dvd_refl (pisano q))).1
  · intro hz
    have hpos : 0 < Nat.fib (pisano q + 1) := Nat.fib_pos.mpr (by omega)
    exact Nat.dvd_antisymm ((returns _).mpr
      ⟨hz, lift_fourth_root k hq hodd hpos old.2 (fourth_root_at_zero hz)⟩) lower

lemma period_power_eq_iff {q k : ℕ} (hq : q.Prime) (hodd : 2 < q) (hk : 0 < k) :
    pisano (q ^ k) = pisano q ↔ q ^ k ∣ Nat.fib (rankOfApparition q) :=
  (period_power_eq_iff_at_period hq hodd hk).trans (power_at_rank_iff k hq hodd)

-- Over ZMod (q²), a return modulo q has an error divisible by q. Repetition
-- adds these errors, since all products of two errors vanish.
lemma period_square_dvd_mul (q : ℕ) [NeZero q] : pisano (q ^ 2) ∣ q * pisano q := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (period_and_returns q).1.ne'
  let n := k + 1
  have ret := ((period_and_returns q).2 _).mp (dvd_refl (pisano q))
  rw [hk] at ret
  obtain ⟨c, hc⟩ := ret.1
  have hu : 1 ≤ Nat.fib (n + 1) := Nat.fib_pos.mpr (Nat.succ_pos _)
  obtain ⟨d, hd⟩ := (Nat.modEq_iff_dvd' hu).mp ret.2.symm
  have hu' : Nat.fib (n + 1) = 1 + q * d := by omega
  have zero : (q : ZMod (q ^ 2)) * q = 0 := by
    rw [← Nat.cast_mul, ← pow_two, ZMod.natCast_eq_zero_iff]
  have a : (Nat.fib n : ZMod (q ^ 2)) = q * (c : ZMod (q ^ 2)) := by
    rw [← Nat.cast_mul, show Nat.fib n = q * c from hc]
  have b : (Nat.fib (n + 1) : ZMod (q ^ 2)) = 1 + q * (d : ZMod (q ^ 2)) := by
    rw [hu', Nat.cast_add, Nat.cast_one, Nat.cast_mul]
  have prev : (Nat.fib k : ZMod (q ^ 2)) = 1 + q * ((d : ZMod (q ^ 2)) - c) := by
    change (Nat.fib (k + 2) : ZMod (q ^ 2)) = _ at b
    rw [Nat.fib_add_two, Nat.cast_add, a] at b
    linear_combination b
  have linear (t : ℕ) :
      (Nat.fib (t * n) : ZMod (q ^ 2)) = t * (q * (c : ZMod (q ^ 2))) ∧
      (Nat.fib (t * n + 1) : ZMod (q ^ 2)) = 1 + t * (q * (d : ZMod (q ^ 2))) := by
    induction t with
    | zero => simp
    | succ t ih =>
      rw [Nat.succ_mul, Nat.cast_succ]
      constructor
      · change (Nat.fib (t * n + (k + 1)) : ZMod (q ^ 2)) = _
        rw [← Nat.add_assoc, Nat.fib_add, Nat.cast_add, Nat.cast_mul, Nat.cast_mul, ih.1, ih.2, a, prev]
        linear_combination (t : ZMod (q ^ 2)) * c * (2 * d - c) * zero
      · rw [Nat.fib_add, Nat.cast_add, Nat.cast_mul, Nat.cast_mul, ih.1, ih.2, a, b]
        linear_combination (t : ZMod (q ^ 2)) * ((c : ZMod (q ^ 2)) ^ 2 + d ^ 2) * zero
  apply ((period_and_returns _).2 _).mpr
  rw [hk]
  obtain ⟨h0, h1⟩ := linear q
  constructor
  · apply (ZMod.natCast_eq_zero_iff ..).mp
    simpa [← mul_assoc, zero] using h0
  · apply (ZMod.natCast_eq_natCast_iff ..).mp
    simpa [← mul_assoc, zero] using h1

lemma period_square_dichotomy {q : ℕ} (hq : q.Prime) :
    pisano (q ^ 2) = pisano q ∨ pisano (q ^ 2) = q * pisano q := by
  let : NeZero q := ⟨hq.ne_zero⟩
  obtain ⟨t, ht⟩ := period_dvd_of_dvd (dvd_pow_self q (by decide : 2 ≠ 0))
  have hd := period_square_dvd_mul q
  rw [ht, Nat.mul_comm q] at hd
  rcases (Nat.dvd_prime hq).mp (Nat.dvd_of_mul_dvd_mul_left (period_and_returns q).1 hd) with h | h
  · exact Or.inl (by simpa [h] using ht)
  · exact Or.inr (by simpa [h, Nat.mul_comm] using ht)

lemma period_square_formula {q : ℕ} (hq : q.Prime) (hodd : 2 < q) :
    pisano (q ^ 2) = if q ^ 2 ∣ Nat.fib (rankOfApparition q) then pisano q else q * pisano q := by
  have stable := period_power_eq_iff (k := 2) hq hodd (by decide)
  split_ifs with h
  · exact stable.mpr h
  · exact (period_square_dichotomy hq).resolve_left (mt stable.mp h)

-- No primality is needed: the old modulus divides its positive powers.
lemma stable_half_period_iff {m j : ℕ} (hm : 2 < m) (hj : 0 < j) :
    pisano (m ^ j) = pisano m ↔
    let k := pisano m / 2
    m ^ j ∣ (if Even k then Nat.fib k else 2 * Nat.fib (k+1) - Nat.fib k) := by
  let : NeZero m := ⟨by omega⟩
  have lower := period_dvd_of_dvd (dvd_pow_self m hj.ne')
  have half : 2 * (pisano m / 2) = pisano m := Nat.mul_div_cancel' (even_iff_two_dvd.mp (even_period hm))
  dsimp only
  rw [← period_dvd_double_iff, half]
  exact ⟨fun h => h ▸ dvd_refl _, fun h => Nat.dvd_antisymm h lower⟩

-- For a prime above 53, no half-index value through k=48 contains its square.
-- The product bound certifies that the table includes every possible prime divisor.
set_option maxRecDepth 4000 in
set_option maxHeartbeats 3000000 in
lemma large_period_of_stability {q : ℕ} (hq : q.Prime) (hl : 53 < q)
    (stable : pisano (q ^ 2) = pisano q) : 96 < pisano q := by
  let : NeZero q := ⟨hq.ne_zero⟩
  let k := pisano q / 2
  let value (i : ℕ) := if Even i then Nat.fib i else 2 * Nat.fib (i+1) - Nat.fib i
  have square : q ^ 2 ∣ value k := (stable_half_period_iff (by omega : 2 < q) (by decide : 0 < 2)).mp stable
  have half : 2 * k = pisano q := Nat.mul_div_cancel' (even_iff_two_dvd.mp (even_period (by omega : 2 < q)))
  have pos := (period_and_returns q).1
  by_contra! short
  have hk : 0 < k := by omega
  let factors : List ℕ :=
    [2, 3, 5, 7, 11, 13, 17, 19, 23, 29,
     31, 37, 41, 43, 47, 59, 61, 71, 79, 89,
     101, 107, 113, 139, 151, 181, 199, 211, 233, 281,
     307, 421, 461, 521, 541, 859, 911, 1103, 1597, 2161,
     2207, 3571, 5779, 6709, 9349, 9901, 19489, 28657, 144481, 3010349,
     54018521, 370248451, 6643838879]
  have primes : ∀ p ∈ factors, Nat.Prime p := by norm_num [factors, List.forall_mem_cons]
  have bound : ∀ i : Fin 49, 0 < i.val → value i.val ∣ factors.prod ^ 8 := by decide
  have j : k < 49 := by omega
  have member := OMA.R_arxiv_2604_17847_R1.prime_mem_of_dvd_product hq factors primes
    (hq.dvd_of_dvd_pow (((dvd_pow_self q (by decide : 2 ≠ 0)).trans square).trans (bound ⟨k,j⟩ hk)))
  have test : ∀ p ∈ factors, 53 < p → ∀ i : Fin 49, 0 < i.val → ¬ p ^ 2 ∣ value i.val := by decide
  exact test q member hl ⟨k,j⟩ hk square

lemma period_square_through_96 {q : ℕ} (hq : q.Prime) (hl : 53 < q) (hs : pisano q ≤ 96) :
    pisano (q ^ 2) = q * pisano q :=
  (period_square_dichotomy hq).resolve_left (fun h => (Nat.not_lt_of_ge hs) (large_period_of_stability hq hl h))

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

-- Adapted from PR #30640. Frobenius permutes the two distinct roots of X²-X-1 in characteristic p.
lemma zero_at_neighbor {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h5 : p ≠ 5) :
    p ∣ Nat.fib (p - 1) ∨ p ∣ Nat.fib (p + 1) := by
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
  have zero_of_equal (n : ℕ) (h : a ^ n = b ^ n) : p ∣ Nat.fib n := by
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

-- Both neighbors cannot be zeros: the gcd of the two indices divides their difference, two.
lemma neighbors_not_both {q : ℕ} (hq : q.Prime) :
    ¬ (q ∣ Nat.fib (q-1) ∧ q ∣ Nat.fib (q+1)) := by
  rintro ⟨hlo,hhi⟩
  let g := (q-1).gcd (q+1)
  have hd : g ∣ 2 := by
    have h := Nat.dvd_sub (Nat.gcd_dvd_right (q-1) (q+1)) (Nat.gcd_dvd_left (q-1) (q+1))
    have eq : q+1-(q-1) = 2 := by have := hq.two_le; omega
    rwa [eq] at h
  have hf : q ∣ Nat.fib g := by rw [Nat.fib_gcd]; exact Nat.dvd_gcd hlo hhi
  exact hq.not_dvd_one (by simpa using hf.trans (Nat.fib_dvd _ _ hd))

-- At any positive zero index prime to q, the square test detects period stability.
lemma stable_iff_at_coprime_zero {q n : ℕ} (hq : q.Prime) (ho : 2 < q) (hn : 0 < n)
    (hz : q ∣ Nat.fib n) (hc : ¬ q ∣ n) :
    pisano (q^2) = pisano q ↔ q^2 ∣ Nat.fib n := by
  constructor
  · intro stable
    exact ((period_power_eq_iff hq ho (by decide : 0 < 2)).mp stable).trans
      (Nat.fib_dvd _ _ (rank_dvd_index hn hz))
  · intro hs
    let : NeZero q := ⟨hq.ne_zero⟩
    rcases period_square_dichotomy hq with eq | growth
    · exact eq
    · have ret := fourfold_return hs
      rw [growth] at ret
      have hd := (dvd_mul_right q (pisano q)).trans ret
      have two : ¬ q ∣ 2 := fun h => (Nat.not_le_of_lt ho) (Nat.le_of_dvd (by decide) h)
      exact (hc ((hq.dvd_mul.mp ((hq.dvd_mul.mp hd).resolve_left two)).resolve_left two)).elim

lemma stable_neighbor_iff {q : ℕ} (hq : q.Prime) (hl : 5 < q) :
    pisano (q^2) = pisano q ↔ q^2 ∣ Nat.fib (q-1) ∨ q^2 ∣ Nat.fib (q+1) := by
  have left : ¬ q ∣ q-1 := by
    intro h
    have := Nat.le_of_dvd (show 0 < q-1 by omega) h
    omega
  have right : ¬ q ∣ q+1 := fun h => hq.not_dvd_one ((Nat.dvd_add_iff_right (dvd_refl q)).mpr h)
  have lo := stable_iff_at_coprime_zero (q := q) (n := q-1) hq (by omega) (by omega)
  have hi := stable_iff_at_coprime_zero (q := q) (n := q+1) hq (by omega) (by omega)
  have base : q ∣ q^2 := dvd_pow_self q (by decide)
  constructor
  · intro stable
    rcases zero_at_neighbor hq (by omega) (by omega) with h | h
    · exact Or.inl ((lo h left).mp stable)
    · exact Or.inr ((hi h right).mp stable)
  · rintro (h | h)
    · exact (lo (base.trans h) left).mpr h
    · exact (hi (base.trans h) right).mpr h

lemma prime_not_dvd_period {q : ℕ} (hq : q.Prime) (hl : 5 < q) : ¬ q ∣ pisano q := by
  let : NeZero q := ⟨hq.ne_zero⟩
  intro hd
  have transfer (n : ℕ) (hz : q ∣ Nat.fib n) : q ∣ n := by
    have h := hd.trans (fourfold_return hz)
    have two : ¬ q ∣ 2 := fun h => (Nat.not_le_of_lt (by omega : 2 < q)) (Nat.le_of_dvd (by decide) h)
    exact (hq.dvd_mul.mp ((hq.dvd_mul.mp h).resolve_left two)).resolve_left two
  rcases zero_at_neighbor hq (by omega) (by omega) with h | h
  · have := Nat.le_of_dvd (show 0 < q-1 by omega) (transfer _ h)
    omega
  · exact hq.not_dvd_one ((Nat.dvd_add_iff_right (dvd_refl q)).mpr (transfer _ h))

-- The p-1 branch for p=2q+1 can only share a rank dividing 2 with the period.
lemma companion_alignment_iff {q : ℕ} (hq : q.Prime) (hl : 5 < q) (hp : (2*q+1).Prime) :
    2*q+1 ∣ Nat.fib (pisano q) ↔ 2*q+1 ∣ Nat.fib ((pisano q).gcd (2*(q+1))) := by
  constructor
  · intro aligned
    have plus : 2*q+1 ∣ Nat.fib (2*(q+1)) := by
      rcases zero_at_neighbor hp (by omega) (by omega) with lo | hi
      · simp only [Nat.add_sub_cancel] at lo
        let d := (pisano q).gcd (2*q)
        have zero : 2*q+1 ∣ Nat.fib d := by rw [Nat.fib_gcd]; exact Nat.dvd_gcd aligned lo
        have cop : d.Coprime q := (hq.coprime_iff_not_dvd.mpr
          (fun h => prime_not_dvd_period hq hl (h.trans (Nat.gcd_dvd_left _ _)))).symm
        have small : d ∣ 2 := cop.dvd_of_dvd_mul_right (Nat.gcd_dvd_right _ _)
        exact (hp.not_dvd_one (by simpa using zero.trans (Nat.fib_dvd _ _ small))).elim
      · rwa [show 2*(q+1) = 2*q+1+1 by omega]
    rw [Nat.fib_gcd]
    exact Nat.dvd_gcd aligned plus
  · exact fun h => h.trans (Nat.fib_dvd _ _ (Nat.gcd_dvd_left _ _))

-- Even the companion's upper branch cannot align if q itself has a lower-neighbor zero.
lemma aligned_companion_forces_upper {q : ℕ} (hq : q.Prime) (hl : 53 < q)
    (hp : (2*q+1).Prime) (ha : 2*q+1 ∣ Nat.fib (pisano q)) : q ∣ Nat.fib (q+1) := by
  let : NeZero q := ⟨hq.ne_zero⟩
  rcases zero_at_neighbor hq (by omega) (by omega) with lo | hi
  · let d := (pisano q).gcd (2*(q+1))
    have zero : 2*q+1 ∣ Nat.fib d := (companion_alignment_iff hq (by omega) hp).mp ha
    have below : d ∣ 2*(2*(q-1)) := (Nat.gcd_dvd_left _ _).trans (fourfold_return lo)
    have above : d ∣ 2*(2*(q+1)) :=
      (Nat.gcd_dvd_right _ _).trans (dvd_mul_left _ 2)
    have small : d ∣ 8 := by
      have diff := Nat.dvd_sub above below
      rwa [show 2*(2*(q+1))-2*(2*(q-1)) = 8 by omega] at diff
    have h := Nat.le_of_dvd (by decide : 0 < Nat.fib 8) (zero.trans (Nat.fib_dvd _ _ small))
    have : Nat.fib 8 = 21 := by decide
    omega
  · exact hi

-- The bounded test uses Mathlib's proven binary Fibonacci evaluator.
set_option maxRecDepth 6000 in
set_option maxHeartbeats 2000000 in
lemma large_prime_of_stability {q : ℕ} (hq : q.Prime) (hl : 5 < q)
    (stable : pisano (q^2) = pisano q) : 1000 < q := by
  by_contra! small
  have test : ∀ j : Fin 1001, 5 < j.val →
      ¬ (j.val ^ 2 ∣ Nat.fastFib (j.val-1) ∨ j.val ^ 2 ∣ Nat.fastFib (j.val+1)) := by decide
  have hz := (stable_neighbor_iff hq hl).mp stable
  rw [Nat.fib_eq_fastFib] at hz
  exact test ⟨q, Nat.lt_succ_of_le small⟩ hl hz

lemma square_period_through_1000 {q : ℕ} (hq : q.Prime) (hl : 5 < q) (small : q ≤ 1000) :
    pisano (q^2) = q * pisano q :=
  (period_square_dichotomy hq).resolve_left (fun h => (Nat.not_lt_of_ge small) (large_prime_of_stability hq hl h))

-- This equivalence audits the chosen 2q+1 witness strategy in both directions.
lemma canonical_companion_iff : (H1 ∧ H2) ↔
    ∀ q : ℕ, q.Prime → 53 < q → pisano (q^2) = pisano q →
      (2*q+1).Prime ∧ 2*q+1 ∣ Nat.fib (pisano q) := by
  constructor
  · rintro ⟨first, second⟩ q hq hl stable
    have large := large_prime_of_stability hq (by omega) stable
    have long := large_period_of_stability hq hl stable
    obtain ⟨hp, upper⟩ := first q hq large long ((stable_neighbor_iff hq (by omega)).mp stable)
    exact ⟨hp, (companion_alignment_iff hq (by omega) hp).mpr (second q hq large long upper hp)⟩
  · intro canonical
    constructor
    · intro q hq large _ neighbor
      have stable := (stable_neighbor_iff hq (by omega)).mpr neighbor
      obtain ⟨hp, aligns⟩ := canonical q hq (by omega) stable
      have hz := aligned_companion_forces_upper hq (by omega) hp aligns
      have upper := (stable_iff_at_coprime_zero hq (by omega) (Nat.succ_pos q) hz
        (fun h => hq.not_dvd_one ((Nat.dvd_add_iff_right (dvd_refl q)).mpr h))).mp stable
      exact ⟨hp, upper⟩
    · intro q hq large _ upper hp
      have stable := (stable_neighbor_iff hq (by omega)).mpr (Or.inr upper)
      exact (companion_alignment_iff hq (by omega) hp).mp (canonical q hq (by omega) stable).2

theorem main : H1 → H2 → OMA.R_arxiv_2604_17847_R1.H2 := by
  intro first second q hq hlarge hs
  let : NeZero q := ⟨hq.ne_zero⟩
  have stable := (period_power_eq_iff_at_period hq (by omega) (by decide : 0 < 2)).mpr hs
  obtain ⟨hp, divides⟩ := canonical_companion_iff.mp ⟨first,second⟩ q hq hlarge stable
  refine ⟨2*q+1, hp, ?_, rank_dvd_index (period_and_returns q).1 divides⟩
  simp [Nat.ModEq, Nat.add_mod]

end OMA.R_arxiv_2604_17847_R1_H2_R1
