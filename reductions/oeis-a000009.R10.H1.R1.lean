import OMAReductions.R_oeis_a000009_R10

/-!
# Counting candidates for the representation step of A000009

At x = n / 2 + 1, R10 can descend from n using a primitive strict partition
value in [x, 3*x/2]. Remove values divisible by a partition value s ≥ 1000
with s² ≤ x. Count the remaining values and the distinct values among them
that still have a proper partition divisor. For the latter, only cofactors k
with 2*k² < 3*a need to be considered. The cutoff for x comes from R10's
256-value base. Both uniform counting estimates below are open.
-/
namespace OMA.R_oeis_a000009_R10_H1_R1
open OMA.S_oeis_a000009

/-- Lower bound on distinct values surviving the small-divisor sieve. -/
def H1 : Prop :=
  let Q := fun a : ℕ => ∃ m : ℕ, 0 < m ∧ a = strictPartitionCount m
  ∀ x : ℕ, 30020900773769688559070113208459541809716021698140392739697 ≤ x →
    ∃ A : Finset ℕ, x.log2 / 32 < A.card ∧ ∀ a ∈ A,
      Q a ∧ x ≤ a ∧ 2*a ≤ 3*x ∧ ∀ s, 1000 ≤ s → Q s → s*s ≤ x → ¬ s ∣ a

/-- Upper bound on distinct surviving values with a short cofactor k
whose complementary factor a/k is itself an eligible partition value. -/
def H2 : Prop :=
  let Q := fun a : ℕ => ∃ m : ℕ, 0 < m ∧ a = strictPartitionCount m
  ∀ x : ℕ, 30020900773769688559070113208459541809716021698140392739697 ≤ x →
    ∀ B : Finset ℕ, (∀ a ∈ B,
      (Q a ∧ x ≤ a ∧ 2*a ≤ 3*x ∧ ∀ s, 1000 ≤ s → Q s → s*s ≤ x → ¬ s ∣ a) ∧
      ∃ k : ℕ, 2 ≤ k ∧ 2*k*k < 3*a ∧ k ∣ a ∧ 1000 ≤ a/k ∧ Q (a/k)) →
      B.card ≤ x.log2 / 32

/-- After sieving, a proper partition divisor exists exactly when a short
cofactor gives one. Multiple factorizations of the same value cost one exception. -/
theorem short_cofactor_iff (Q : ℕ → Prop) (x a : ℕ) (hi : 2*a ≤ 3*x)
    (clean : ∀ s, 1000 ≤ s → Q s → s*s ≤ x → ¬ s ∣ a) :
    (∃ s, 1000 ≤ s ∧ Q s ∧ 2*s ≤ a ∧ s ∣ a) ↔
      ∃ k : ℕ, 2 ≤ k ∧ 2*k*k < 3*a ∧ k ∣ a ∧ 1000 ≤ a/k ∧ Q (a/k) := by
  constructor
  · rintro ⟨s,hs,qs,low,d⟩
    have large : x < s*s := by
      by_contra! small
      exact clean s hs qs small d
    obtain ⟨k,rfl⟩ := d
    have hk : 2 ≤ k := by
      by_contra! h
      have h' : k = 0 ∨ k = 1 := by omega
      rcases h' with rfl | rfl <;> simp at low <;> omega
    have prod : s*(2*k) < s*(3*s) := by nlinarith
    have short := Nat.lt_of_mul_lt_mul_left prod
    have sq := Nat.mul_lt_mul_of_pos_right short (by omega : 0 < k)
    have div : s*k/k = s := Nat.mul_div_cancel _ (by omega)
    exact ⟨k,hk,by nlinarith only [sq],dvd_mul_left _ _,by rwa [div],by rwa [div]⟩
  · rintro ⟨k,hk,_,dvd,big,qs⟩
    have h := Nat.div_mul_cancel dvd
    exact ⟨a/k,big,qs,by nlinarith [Nat.mul_le_mul_left (a/k) hk],⟨k,h.symm⟩⟩

theorem main : H1 → H2 → OMA.R_oeis_a000009_R10.H1 := by
  intro supply exceptions
  apply OMA.R_oeis_a000009_R10.H1_of_intervals
  intro n hn
  let x := n/2+1
  have start : 30020900773769688559070113208459541809716021698140392739697 ≤ x := by
    dsimp only [x]; omega
  obtain ⟨A,count,good⟩ := supply x start
  classical
  by_contra! missing
  apply (Nat.not_le_of_gt count)
  apply exceptions x start A
  intro a ha
  obtain ⟨qa,lo,hi,clean⟩ := good a ha
  refine ⟨good a ha,(short_cofactor_iff _ x a hi clean).mp ?_⟩
  exact missing a qa (by omega) (by dsimp only [x] at hi; omega)
    (by dsimp only [x] at lo; omega) (by dsimp only [x] at lo; omega)

end OMA.R_oeis_a000009_R10_H1_R1
