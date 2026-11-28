import OMAReductions.R_Erdos945_erdos_945_R1

-- Reduction Erdos945.erdos_945.R1.H1.R1 of step Erdos945.erdos_945.R1.H1
-- Credit: @hiattco

namespace OMA.R_Erdos945_erdos_945_R1_H1_R1

open Finset
open scoped Classical

/-- Multiples of small prime squares occupy at most seven eighths of the interval. -/
def H1 : Prop := ∀ n H : ℕ, 64 ≤ H →
    ((Ioc n (n + H)).filter fun q =>
      ∃ p : ℕ, p.Prime ∧ p ≤ H / 8 ∧ p * p ∣ q).card ≤ 7 * H / 8

/-- Bound the number of positions hit by a large prime square at a polynomial
length in the binary size parameter. -/
def H2 : Prop := ∃ A D : ℕ, ∀ m n : ℕ, n ≤ 2^m →
    let H := D * (m + 1)^A
    64 ≤ H ∧ ((Ioc n (n + H)).filter fun q =>
      ∃ p : ℕ, p.Prime ∧ H / 8 < p ∧ p * p ∣ q).card < H - 7 * H / 8

theorem main : H1 → H2 → OMA.R_Erdos945_erdos_945_R1.H1 := by
  intro smallBound largeBound
  obtain ⟨A, D, hAD⟩ := largeBound
  refine ⟨A, D, ?_⟩
  intro m n hn
  let H := D * (m + 1)^A
  let I := Ioc n (n + H)
  let small := I.filter fun q => ∃ p : ℕ, p.Prime ∧ p ≤ H / 8 ∧ p * p ∣ q
  let large := I.filter fun q => ∃ p : ℕ, p.Prime ∧ H / 8 < p ∧ p * p ∣ q
  obtain ⟨hH, hLarge⟩ := hAD m n hn
  have hs : small.card ≤ 7 * H / 8 := smallBound n H hH
  have hl : large.card < H - 7 * H / 8 := hLarge
  by_contra hnone
  have cover : I ⊆ small ∪ large := by
    intro q hq
    obtain ⟨hlo, hhi⟩ := mem_Ioc.mp hq
    have hbad : ¬ Squarefree q := fun hqfree => hnone ⟨q, hlo, hhi, hqfree⟩
    rw [Nat.squarefree_iff_prime_squarefree] at hbad
    push_neg at hbad
    obtain ⟨p, hp, hd⟩ := hbad
    by_cases h : p ≤ H / 8
    · exact mem_union_left _ (mem_filter.mpr ⟨hq, p, hp, h, hd⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hq, p, hp, Nat.lt_of_not_ge h, hd⟩)
  have hcard : I.card = H := by simp [I]
  have hcount := (card_le_card cover).trans (card_union_le small large)
  omega

end OMA.R_Erdos945_erdos_945_R1_H1_R1
