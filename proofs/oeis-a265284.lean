import OMAStatements.S_oeis_a265284
import Mathlib.Tactic

/-!
Proof of Colin Barker's formulas, recurrence, and generating function for OEIS A265284:
For k >= 1, Rule 94 rows follow an exact 2-step periodic pattern with alternating interior:
- row (2 * k)     = [true, true] ++ alt (2 * k - 1) ++ [true]
- row (2 * k + 1) = [true, true, true] ++ alt (2 * k - 1) ++ [true, true]
where alt m repeats [false, true] m times. Counting ones gives
4 * ones (row m) = 4 * m + 10 - 2 * (-1)^m for m >= 2,
which yields 4 * a n = 2*n^2 + 12*n - (-1)^n + 1 by induction and immediately
implies all four remaining claims.
-/

namespace OMA.P_oeis_a265284

private def alt : ℕ → List Bool
  | 0 => []
  | m + 1 => false :: true :: alt m

private def flipAlt : ℕ → List Bool
  | 0 => []
  | m + 1 => true :: false :: flipAlt m

private lemma scan_ft_alt (m : ℕ) (tail : List Bool) :
    OMA.S_oeis_a265284.scan false true (alt m ++ tail) =
      flipAlt m ++ OMA.S_oeis_a265284.scan false true tail := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [alt, flipAlt, List.cons_append, OMA.S_oeis_a265284.scan,
      OMA.S_oeis_a265284.rule94]
    exact congrArg (fun r => true :: false :: r) ih

private lemma scan_tt_alt (m : ℕ) (tail : List Bool) :
    OMA.S_oeis_a265284.scan true true (alt (m + 1) ++ tail) =
      true :: false :: flipAlt m ++ OMA.S_oeis_a265284.scan false true tail := by
  simp only [alt, List.cons_append, OMA.S_oeis_a265284.scan, OMA.S_oeis_a265284.rule94]
  exact congrArg (fun r => true :: false :: r) (scan_ft_alt m tail)

private lemma flipAlt_append_true (m : ℕ) : flipAlt m ++ [true] = true :: alt m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [flipAlt, alt, List.cons_append]
    exact congrArg (fun r => true :: false :: r) ih

private lemma alt_append_ft (m : ℕ) : alt m ++ [false, true] = alt (m + 1) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [alt, List.cons_append]
    exact congrArg (fun r => false :: true :: r) ih

private lemma row_pattern : ∀ k : ℕ,
    OMA.S_oeis_a265284.row (2 * (k + 1)) = [true, true] ++ alt (2 * k + 1) ++ [true] ∧
    OMA.S_oeis_a265284.row (2 * (k + 1) + 1) =
      [true, true, true] ++ alt (2 * k + 1) ++ [true, true] := by
  intro k
  induction k with
  | zero =>
    constructor <;> decide
  | succ k ih =>
    have hodd := ih.2
    have heven_succ :
        OMA.S_oeis_a265284.row (2 * (k + 1 + 1)) =
          OMA.S_oeis_a265284.next (OMA.S_oeis_a265284.row (2 * (k + 1) + 1)) := rfl
    have heven_eq :
        OMA.S_oeis_a265284.row (2 * (k + 1 + 1)) =
          [true, true] ++ alt (2 * (k + 1) + 1) ++ [true] := by
      rw [heven_succ, hodd, OMA.S_oeis_a265284.next]
      simp only [List.append_assoc, List.cons_append, List.nil_append,
        OMA.S_oeis_a265284.scan, OMA.S_oeis_a265284.rule94,
        Bool.false_bne, Bool.not_false, Bool.not_true, Bool.and_false, Bool.and_true,
        Bool.or_false, Bool.true_bne]
      rw [scan_tt_alt (2 * k) [true, true, false, false]]
      simp only [OMA.S_oeis_a265284.scan, OMA.S_oeis_a265284.rule94,
        Bool.false_bne, Bool.true_bne, Bool.not_false, Bool.not_true,
        Bool.and_true, Bool.and_false, Bool.or_false]
      have hflip :
          flipAlt (2 * k) ++ [true, false, true, true] =
            true :: alt (2 * k + 1) ++ [true] := by
        calc flipAlt (2 * k) ++ [true, false, true, true]
            = (flipAlt (2 * k) ++ [true]) ++ [false, true, true] := by
              simp [List.append_assoc]
          _ = (true :: alt (2 * k)) ++ [false, true, true] := by
              rw [flipAlt_append_true]
          _ = true :: (alt (2 * k) ++ [false, true]) ++ [true] := by
              simp [List.append_assoc]
          _ = true :: alt (2 * k + 1) ++ [true] := by
              rw [alt_append_ft]
      have halt2 : alt (2 * (k + 1) + 1) =
          false :: true :: false :: true :: alt (2 * k + 1) := by
        rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by ring]
        rfl
      simp only [List.cons_append] at hflip ⊢
      rw [hflip, halt2]
      simp
    have hodd_succ :
        OMA.S_oeis_a265284.row (2 * (k + 1 + 1) + 1) =
          OMA.S_oeis_a265284.next (OMA.S_oeis_a265284.row (2 * (k + 1 + 1))) := rfl
    have hodd_eq :
        OMA.S_oeis_a265284.row (2 * (k + 1 + 1) + 1) =
          [true, true, true] ++ alt (2 * (k + 1) + 1) ++ [true, true] := by
      rw [hodd_succ, heven_eq, OMA.S_oeis_a265284.next]
      simp only [List.append_assoc, List.cons_append, List.nil_append,
        OMA.S_oeis_a265284.scan, OMA.S_oeis_a265284.rule94,
        Bool.false_bne, Bool.not_false, Bool.not_true, Bool.and_false, Bool.and_true,
        Bool.or_false]
      rw [show 2 * (k + 1) + 1 = (2 * k + 2) + 1 by ring]
      rw [scan_tt_alt (2 * k + 2) [true, false, false]]
      simp only [OMA.S_oeis_a265284.scan, OMA.S_oeis_a265284.rule94,
        Bool.false_bne, Bool.true_bne, Bool.not_false, Bool.not_true,
        Bool.and_true, Bool.and_false, Bool.or_false]
      have hflip2 :
          flipAlt (2 * k + 2) ++ [true, true, true] =
            true :: alt (2 * k + 2) ++ [true, true] := by
        calc flipAlt (2 * k + 2) ++ [true, true, true]
            = (flipAlt (2 * k + 2) ++ [true]) ++ [true, true] := by
              simp [List.append_assoc]
          _ = (true :: alt (2 * k + 2)) ++ [true, true] := by
              rw [flipAlt_append_true]
          _ = true :: alt (2 * k + 2) ++ [true, true] := by
              simp
      simp only [List.cons_append] at hflip2 ⊢
      rw [hflip2]
      rfl
    exact ⟨heven_eq, hodd_eq⟩

private lemma ones_append (xs ys : List Bool) :
    OMA.S_oeis_a265284.ones (xs ++ ys) =
      OMA.S_oeis_a265284.ones xs + OMA.S_oeis_a265284.ones ys := by
  induction xs with
  | nil => simp [OMA.S_oeis_a265284.ones]
  | cons x xs ih =>
    simp only [List.cons_append, OMA.S_oeis_a265284.ones, ih]
    ring

private lemma ones_alt (m : ℕ) : OMA.S_oeis_a265284.ones (alt m) = m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [alt, OMA.S_oeis_a265284.ones, ih]
    push_cast
    ring

private lemma ones_row_ge2 : ∀ m : ℕ, 2 ≤ m →
    4 * OMA.S_oeis_a265284.ones (OMA.S_oeis_a265284.row m) =
      4 * (m : ℤ) + 10 - 2 * (-1 : ℤ) ^ m := by
  intro m hm
  set k := m / 2 - 1
  rcases Nat.even_or_odd m with ⟨r, hr⟩ | ⟨r, hr⟩
  · have hm_eq : m = 2 * (k + 1) := by omega
    rw [hm_eq, (row_pattern k).1, ones_append, ones_append, ones_alt]
    have hpow : (-1 : ℤ) ^ (2 * (k + 1)) = 1 := by
      rw [pow_mul]
      norm_num
    rw [hpow]
    simp only [OMA.S_oeis_a265284.ones]
    push_cast
    ring
  · have hm_eq : m = 2 * (k + 1) + 1 := by omega
    rw [hm_eq, (row_pattern k).2, ones_append, ones_append, ones_alt]
    have hpow : (-1 : ℤ) ^ (2 * (k + 1) + 1) = -1 := by
      rw [pow_succ, pow_mul]
      norm_num
    rw [hpow]
    simp only [OMA.S_oeis_a265284.ones]
    push_cast
    ring

private lemma formula_pos : ∀ n : ℕ, 0 < n →
    4 * OMA.S_oeis_a265284.a n = 2 * (n : ℤ) ^ 2 + 12 * n - (-1) ^ n + 1 := by
  intro n hn
  induction n with
  | zero => omega
  | succ k ih =>
    match k with
    | 0 => decide
    | m + 1 =>
      have ha_step : OMA.S_oeis_a265284.a (m + 2) =
          OMA.S_oeis_a265284.a (m + 1) + OMA.S_oeis_a265284.ones (OMA.S_oeis_a265284.row (m + 2)) :=
        rfl
      have hih := ih (by omega)
      have hones := ones_row_ge2 (m + 2) (by omega)
      have hpow : (-1 : ℤ) ^ (m + 2) = -(-1 : ℤ) ^ (m + 1) := by
        rw [pow_succ]
        ring
      rw [ha_step, mul_add, hih, hones]
      push_cast
      rw [hpow]
      ring

end OMA.P_oeis_a265284

theorem OMA.solution : type_of% @OMA.S_oeis_a265284.main := by
  have h1 : ∀ n : ℕ, 0 < n →
      4 * OMA.S_oeis_a265284.a n = 2 * (n : ℤ) ^ 2 + 12 * n - (-1) ^ n + 1 :=
    OMA.P_oeis_a265284.formula_pos
  have h2 : ∀ n : ℕ, 1 < n → Even n →
      2 * OMA.S_oeis_a265284.a n = (n : ℤ) ^ 2 + 6 * n := by
    intro n hn heven
    have h := h1 n (by omega)
    rw [heven.neg_one_pow] at h
    linarith
  have h3 : ∀ n : ℕ, Odd n →
      2 * OMA.S_oeis_a265284.a n = (n : ℤ) ^ 2 + 6 * n + 1 := by
    intro n hodd
    have hn_pos : 0 < n := Nat.pos_of_ne_zero (fun h0 => by subst h0; simp at hodd)
    have h := h1 n hn_pos
    rw [hodd.neg_one_pow] at h
    linarith
  have h4 : ∀ n : ℕ, 4 < n →
      OMA.S_oeis_a265284.a n =
        2 * OMA.S_oeis_a265284.a (n - 1) - 2 * OMA.S_oeis_a265284.a (n - 3) +
          OMA.S_oeis_a265284.a (n - 4) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    have hm1 : m + 5 - 1 = m + 4 := by omega
    have hm3 : m + 5 - 3 = m + 2 := by omega
    have hm4 : m + 5 - 4 = m + 1 := by omega
    rw [hm1, hm3, hm4]
    have e5 := h1 (m + 5) (by omega)
    have e4 := h1 (m + 4) (by omega)
    have e2 := h1 (m + 2) (by omega)
    have e1 := h1 (m + 1) (by omega)
    have hp5 : (-1 : ℤ) ^ (m + 5) = (-1 : ℤ) ^ (m + 1) := by
      rw [show m + 5 = (m + 1) + 4 by omega, pow_add]
      norm_num
    have hp4 : (-1 : ℤ) ^ (m + 4) = -(-1 : ℤ) ^ (m + 1) := by
      rw [show m + 4 = (m + 1) + 3 by omega, pow_add]
      norm_num
    have hp2 : (-1 : ℤ) ^ (m + 2) = -(-1 : ℤ) ^ (m + 1) := by
      rw [pow_succ]
      ring
    rw [hp5] at e5
    rw [hp4] at e4
    rw [hp2] at e2
    push_cast at e5 e4 e2 e1
    linarith
  refine ⟨h1, h2, h3, h4, ?_⟩
  intro n
  match n with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | 4 => decide
  | m + 5 =>
    have hrec := h4 (m + 5) (by omega)
    have h51 : m + 5 - 1 = m + 4 := by omega
    have h53 : m + 5 - 3 = m + 2 := by omega
    have h54 : m + 5 - 4 = m + 1 := by omega
    rw [h51, h53, h54] at hrec
    change OMA.S_oeis_a265284.a (m + 5) - 2 * OMA.S_oeis_a265284.a (m + 4) +
        2 * OMA.S_oeis_a265284.a (m + 2) - OMA.S_oeis_a265284.a (m + 1) = 0
    linarith
