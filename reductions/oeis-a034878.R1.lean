import OMAStatements.S_oeis_a034878
import Mathlib

/-!
# OEIS A034878: reduce the conjecture to composite consecutive inputs

Appending `(k - 1)!` proves the forward inclusion of Jordan–Pólya numbers, as observed
by Murthy and Sondow (https://oeis.org/A034878/internal). The examples at 9 and 10
also come from that entry.

If a prime divides a product of factorials, it must divide one of the factors, whose
index is therefore at least that prime. This eliminates prime inputs and proves the
converse when the predecessor is prime, by cancellation of the forced factor.
-/

namespace OMA.R_oeis_a034878_R1

open OMA.S_oeis_a034878

private theorem jp_in_sequence {k : ℕ} (hk : 1 ≤ k) (hk₂ : k ≠ 2)
    (hjp : IsJordanPolya k) : InA034878 k := by
  by_cases hk₁ : k = 1
  · subst k
    exact ⟨[], by simp, by decide⟩
  have hk₃ : 3 ≤ k := by omega
  obtain ⟨l, hl⟩ := hjp
  refine ⟨(k - 1) :: l, ?_, ?_⟩
  · intro m hm
    rcases List.mem_cons.mp hm with rfl | hm
    · omega
    · have hd : m.factorial ∣ k := by
        rw [← hl]
        exact List.dvd_prod (List.mem_map.mpr ⟨m, hm, rfl⟩)
      have hle := Nat.le_of_dvd (by omega : 0 < k) hd
      by_contra! hkm
      exact (not_lt_of_ge (Nat.le_trans (Nat.factorial_le hkm) hle))
        (Nat.lt_factorial_self hk₃)
  · simp only [List.map_cons, List.prod_cons, hl]
    rw [Nat.mul_comm, Nat.mul_factorial_pred (by omega : k ≠ 0)]

private theorem split_at_prime {p : ℕ} (hp : p.Prime) (l : List ℕ)
    (hd : p ∣ (l.map Nat.factorial).prod) :
    ∃ m ∈ l, p ≤ m ∧ ∃ rest : List ℕ,
      (l.map Nat.factorial).prod = m.factorial * (rest.map Nat.factorial).prod := by
  induction l with
  | nil => exact (hp.not_dvd_one (by simpa using hd)).elim
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons] at hd
    rcases hp.dvd_mul.mp hd with ha | ht
    · exact ⟨a, by simp, hp.dvd_factorial.mp ha, l, rfl⟩
    · obtain ⟨m, hm, hpm, rest, hrest⟩ := ih ht
      refine ⟨m, List.mem_cons_of_mem _ hm, hpm, a :: rest, ?_⟩
      simp only [List.map_cons, List.prod_cons]
      rw [hrest, Nat.mul_left_comm a.factorial]

private theorem prime_excluded {p : ℕ} (hp : p.Prime) : ¬ InA034878 p := by
  rintro ⟨l, hl, hprod⟩
  have hd : p ∣ (l.map Nat.factorial).prod := by
    rw [hprod]
    exact Nat.dvd_factorial hp.pos le_rfl
  obtain ⟨m, hm, hpm, _⟩ := split_at_prime hp l hd
  exact (not_lt_of_ge hpm) (hl m hm)

private theorem jp_of_prime_pred {p : ℕ} (hp : p.Prime)
    (hseq : InA034878 (p + 1)) : IsJordanPolya (p + 1) := by
  obtain ⟨l, hl, hprod⟩ := hseq
  have hd : p ∣ (l.map Nat.factorial).prod := by
    rw [hprod]
    exact Nat.dvd_factorial hp.pos (by omega)
  obtain ⟨m, hm, hpm, rest, hrest⟩ := split_at_prime hp l hd
  have hlt := hl m hm
  have heq : m = p := by omega
  subst m
  rw [hprod, Nat.factorial_succ, Nat.mul_comm (p + 1)] at hrest
  exact ⟨rest, (Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos p) hrest).symm⟩

private theorem jp_eq_one_of_odd {k : ℕ} (hjp : IsJordanPolya k) (hodd : ¬ 2 ∣ k) :
    k = 1 := by
  obtain ⟨l, rfl⟩ := hjp
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons] at hodd ⊢
    have ha : a.factorial = 1 := by
      apply Nat.factorial_eq_one.mpr
      by_contra! h
      exact hodd (dvd_mul_of_dvd_left (Nat.dvd_factorial (by decide) h) _)
    simpa [ha] using ih (by simpa [ha] using hodd)

/-- The remaining converse for even inputs. -/
def H1 : Prop :=
  ∀ k : ℕ, 3 ≤ k → ¬ k.Prime → ¬ (k - 1).Prime → 2 ∣ k →
    InA034878 k → IsJordanPolya k ∨ k = 10

/-- Beyond one, the remaining odd case is to show that nine is the only term. -/
def H2 : Prop :=
  ∀ k : ℕ, 3 ≤ k → ¬ k.Prime → ¬ (k - 1).Prime → ¬ 2 ∣ k →
    InA034878 k → k = 9

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a034878.main := by
  intro heven hodd k hk
  constructor
  · intro hseq
    by_cases hk₁ : k = 1
    · subst k
      exact Or.inl ⟨⟨[], by decide⟩, by decide⟩
    have hnp : ¬ k.Prime := fun hp => prime_excluded hp hseq
    have hk₂ : k ≠ 2 := by
      rintro rfl
      exact hnp (by decide)
    have hk₃ : 3 ≤ k := by omega
    have jp_when_prev_prime (hprev : (k - 1).Prime) : IsJordanPolya k := by
      obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      exact jp_of_prime_pred (by simpa using hprev) hseq
    by_cases hkEven : 2 ∣ k
    · by_cases hprev : (k - 1).Prime
      · exact Or.inl ⟨jp_when_prev_prime hprev, hk₂⟩
      · rcases heven k hk₃ hnp hprev hkEven hseq with hjp | hten
        · exact Or.inl ⟨hjp, hk₂⟩
        · exact Or.inr (Or.inr hten)
    · have hprev : ¬ (k - 1).Prime := fun hp =>
        hk₁ (jp_eq_one_of_odd (jp_when_prev_prime hp) hkEven)
      exact Or.inr (Or.inl (hodd k hk₃ hnp hprev hkEven hseq))
  · rintro (⟨hjp, hk₂⟩ | rfl | rfl)
    · exact jp_in_sequence hk hk₂ hjp
    · exact ⟨[7, 3, 3, 2], by decide, by decide⟩
    · exact ⟨[7, 6], by decide, by decide⟩

end OMA.R_oeis_a034878_R1
