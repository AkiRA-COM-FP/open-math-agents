import OMAStatements.S_oeis_a283050
import Mathlib

/-!
# Proof of OEIS A283050 conjecture

Credit: @AkiRA-COM-FP
-/

open OMA.S_oeis_a283050

private theorem isTerm_four_mul (t : ℕ) : IsTerm (4 * (t + 1)) := by
  have h : 2 ∣ 4 * (t + 1) :=
    dvd_trans (by decide : 2 ∣ 4) (dvd_mul_right 4 (t + 1))
  refine ⟨by omega, ?_⟩
  rw [(Nat.minFac_eq_two_iff _).mpr h]
  exact dvd_mul_right 4 (t + 1)

theorem OMA.solution : type_of% @OMA.S_oeis_a283050.main := by
  classical
  have hinf : Set.Infinite {m | IsTerm m} := by
    refine Set.infinite_iff_exists_gt.mpr fun m => ?_
    exact ⟨4 * (m + 1), isTerm_four_mul m, by omega⟩
  have hmono : StrictMono a := Nat.nth_strictMono hinf
  intro n
  let q := 4 * (a n / 4 + 1)
  have hlt : a n < q := by
    dsimp [q]
    omega
  have hle : q ≤ a n + 4 := by
    dsimp [q]
    omega
  have hterm : IsTerm q := isTerm_four_mul (a n / 4)
  have hindex : a (Nat.count IsTerm q) = q := Nat.nth_count hterm
  have hn : n < Nat.count IsTerm q := by
    apply hmono.lt_iff_lt.mp
    rwa [hindex]
  have hnext : a (n + 1) ≤ q := by
    rw [← hindex]
    exact hmono.monotone hn
  have hstrict : a n < a (n + 1) := hmono (Nat.lt_succ_self n)
  omega
