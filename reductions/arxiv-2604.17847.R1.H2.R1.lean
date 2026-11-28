import OMAReductions.R_arxiv_2604_17847_R1
import Mathlib.Dynamics.PeriodicPts.Lemmas

-- Reduction arxiv-2604.17847.R1.H2.R1 of the exceptional square step.
-- Credit: @wispiANt

namespace OMA.R_arxiv_2604_17847_R1_H2_R1

open OMA.S_arxiv_2604_17847
open OMA.R_arxiv_2604_17847_R1 (rank_dvd_index pisano_eq_of_certificate)

-- The two remaining assertions concern only exceptional primes at their first zero.
def H1 : Prop :=
  ∀ q : ℕ, q.Prime → 53 < q → q ^ 2 ∣ Nat.fib (rankOfApparition q) → (2 * q + 1).Prime

def H2 : Prop :=
  ∀ q : ℕ, q.Prime → 53 < q → q ^ 2 ∣ Nat.fib (rankOfApparition q) →
    (2 * q + 1).Prime → 2 * q + 1 ∣ Nat.fib (pisano q)

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

-- Each Fibonacci step negates the Cassini expression and preserves its square.
lemma cassini_square (q n : ℕ) :
    let a : ZMod q := Nat.fib n
    let b : ZMod q := Nat.fib (n + 1)
    (b ^ 2 - a * b - a ^ 2) ^ 2 = 1 := by
  dsimp
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.fib_add_two, Nat.cast_add]
    convert ih using 1
    ring

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

theorem main : H1 → H2 → OMA.R_arxiv_2604_17847_R1.H2 := by
  intro primality divides q hq hlarge hs
  let : NeZero q := ⟨hq.ne_zero⟩
  have first := (power_at_rank_iff 2 hq (by omega)).mp hs
  have hp := primality q hq hlarge first
  refine ⟨2 * q + 1, hp, ?_, rank_dvd_index (period_and_returns q).1 (divides q hq hlarge first hp)⟩
  simp [Nat.ModEq, Nat.add_mod]

end OMA.R_arxiv_2604_17847_R1_H2_R1
