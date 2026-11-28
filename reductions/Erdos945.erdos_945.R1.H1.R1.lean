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
    push Not at hbad
    obtain ⟨p, hp, hd⟩ := hbad
    by_cases h : p ≤ H / 8
    · exact mem_union_left _ (mem_filter.mpr ⟨hq, p, hp, h, hd⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hq, p, hp, Nat.lt_of_not_ge h, hd⟩)
  have hcard : I.card = H := by simp [I]
  have hcount := (card_le_card cover).trans (card_union_le small large)
  omega

private theorem square_div_le_difference (H d : Nat) (hd : 2 ≤ d) :
    H / d ^ 2 ≤ H / (d - 1) - H / d := by
  rw [Nat.pow_two, ← Nat.div_div_eq_div_mul]
  let q := H / d
  change q / d ≤ H / (d - 1) - q
  apply Nat.le_sub_of_add_le
  apply (Nat.le_div_iff_mul_le (by omega : 0 < d - 1)).2
  have hsmall : q / d * (d - 1) ≤ q := by
    exact Nat.le_trans (Nat.mul_le_mul_left _ (Nat.sub_le d 1)) (Nat.div_mul_le_self q d)
  have hsplit : q * (d - 1) + q = q * d := by
    rw [← Nat.mul_succ]
    have : (d - 1).succ = d := by omega
    rw [this]
  rw [Nat.add_mul]
  exact Nat.le_trans (Nat.add_le_add_right hsmall _) (by
    rw [Nat.add_comm q, hsplit]
    exact Nat.div_mul_le_self H d)

/-- An interval of length H contains at most H / b + 1 multiples of b. -/
private theorem interval_multiple_bound (n H b : Nat) (hb : 0 < b) :
    (n + H) / b - n / b ≤ H / b + 1 := by
  rw [Nat.add_div hb]
  generalize n / b = q, H / b = r
  split <;> omega

private theorem interval_multiple_card (n H b : ℕ) (hb : 0 < b) :
    ((Finset.Ioc n (n + H)).filter fun x => b ∣ x).card =
      (n + H) / b - n / b := by
  rw [← Nat.card_Ioc]
  apply Finset.card_bij' (fun x _ => x / b) (fun k _ => k * b)
  · intro x hx
    obtain ⟨hx, hdvd⟩ := Finset.mem_filter.mp hx
    obtain ⟨hl, hr⟩ := Finset.mem_Ioc.mp hx
    exact Finset.mem_Ioc.mpr ⟨(Nat.div_lt_iff_lt_mul hb).2 (by
      rwa [Nat.div_mul_cancel hdvd]), Nat.div_le_div_right hr⟩
  · intro k hk
    obtain ⟨hl, hr⟩ := Finset.mem_Ioc.mp hk
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Ioc.mpr ⟨(Nat.div_lt_iff_lt_mul hb).1 hl, (Nat.le_div_iff_mul_le hb).1 hr⟩,
       dvd_mul_left b k⟩
  · intro x hx
    exact Nat.div_mul_cancel (Finset.mem_filter.mp hx).2
  · intro k _
    exact Nat.mul_div_cancel k hb

/-- Sum multiplicities for the square divisors 3² through (k+2)². -/
private def tailCount (n H : Nat) : Nat → Nat
  | 0 => 0
  | k+1 =>
      tailCount n H k + ((n+H) / ((k+3)^2) - n / ((k+3)^2))

private theorem tail_bound (n H k : Nat)
    (step : ∀ a : Nat, H / ((a+3)^2) + H / (a+3) ≤ H / (a+2)) :
    tailCount n H k + H/(k+2) ≤ H/2 + k := by
  induction k with
  | zero => simp [tailCount]
  | succ k ih =>
    have hm := interval_multiple_bound n H ((k+3)^2)
      (Nat.pow_pos (by omega))
    have hs := step k
    change tailCount n H k + ((n+H)/((k+3)^2) - n/((k+3)^2)) + H/(k+3) ≤ H/2+(k+1)
    omega

/-- Upper bound with multiplicity for the entire small-square contribution. -/
private theorem small_square_budget (n H : Nat) (hH : 64 ≤ H) :
    ((n+H)/4 - n/4) + tailCount n H (H/8-2) ≤ 7*H/8 := by
  have step (a : Nat) : H / ((a+3)^2) + H / (a+3) ≤ H / (a+2) := by
    have h := square_div_le_difference H (a+3) (by omega)
    have m : H / (a+3) ≤ H / (a+2) := Nat.div_le_div_left (by omega) (by omega)
    change H / ((a+3)^2) ≤ H / (a+2) - H / (a+3) at h
    omega
  have h₂ := interval_multiple_bound n H 4 (by decide)
  have ht := tail_bound n H (H/8-2) step
  have bound := Nat.le_trans (Nat.le_add_right ..) ht
  omega

private noncomputable def hits (n H t : ℕ) : Finset ℕ :=
  (Ioc n (n + H)).filter fun q => ∃ d : ℕ, 2 ≤ d ∧ d ≤ t ∧ d ^ 2 ∣ q

private theorem hits_card (n H k : ℕ) :
    (hits n H (k+2)).card ≤ (n+H)/4 - n/4 + tailCount n H k := by
  induction k with
  | zero =>
    have hs : hits n H 2 ⊆ (Ioc n (n+H)).filter fun q => 4 ∣ q := by
      intro q hq
      obtain ⟨hi,d,hd,hle,hdvd⟩ := mem_filter.mp hq
      have : d = 2 := by omega
      subst d
      exact mem_filter.mpr ⟨hi,hdvd⟩
    simpa only [tailCount, Nat.add_zero, interval_multiple_card n H 4 (by decide)] using card_le_card hs
  | succ k ih =>
    let last := (Ioc n (n+H)).filter fun q => (k+3)^2 ∣ q
    have cover : hits n H (k+3) ⊆ hits n H (k+2) ∪ last := by
      intro q hq
      obtain ⟨hi,d,hd,hle,hdiv⟩ := mem_filter.mp hq
      by_cases h : d ≤ k+2
      · exact mem_union_left _ (mem_filter.mpr ⟨hi,d,hd,h,hdiv⟩)
      · have eq : d = k+3 := by omega
        subst d
        exact mem_union_right _ (mem_filter.mpr ⟨hi,hdiv⟩)
    have hpos : 0 < (k+3)^2 := Nat.pow_pos (by omega)
    have hlast : last.card = (n+H)/((k+3)^2) - n/((k+3)^2) := interval_multiple_card n H _ hpos
    have hcount := (card_le_card cover).trans (card_union_le _ _)
    apply hcount.trans
    simpa only [hlast, tailCount, Nat.add_assoc] using
      (Nat.add_le_add_right ih ((n+H)/((k+3)^2) - n/((k+3)^2)))

/-- The small-square hypothesis holds uniformly in the interval start. -/
theorem small_prime_bound : H1 := by
  intro n H hH
  have cover : ((Ioc n (n + H)).filter fun q =>
      ∃ p : ℕ, p.Prime ∧ p ≤ H / 8 ∧ p * p ∣ q) ⊆ hits n H (H/8 - 2 + 2) := by
    intro q hq
    obtain ⟨hi, p, hp, hle, hdiv⟩ := mem_filter.mp hq
    exact mem_filter.mpr ⟨hi, p, hp.two_le, by omega, by simpa only [pow_two] using hdiv⟩
  exact (card_le_card cover).trans ((hits_card n H (H/8-2)).trans
    (small_square_budget n H hH))

/-- A bound on the large prime squares alone yields the squarefree gap criterion. -/
theorem of_large_squares (h : H2) : OMA.R_Erdos945_erdos_945_R1.H1 :=
  main small_prime_bound h

end OMA.R_Erdos945_erdos_945_R1_H1_R1
