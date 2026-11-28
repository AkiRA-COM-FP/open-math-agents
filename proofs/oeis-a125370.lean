import OMAStatements.S_oeis_a125370

-- Credit: @Aryan-Poonacha
-- The finite path-to-trace argument adapts the base-six formalization for OEIS
-- A125316 in https://github.com/lefttosolve2/open-math-agents/pull/25779.
-- The transfer-matrix method is given by Rafał Wiktorowicz, Proposition 2,
-- https://oeis.org/A126371/a126371_1.pdf (2026). Formulas: Colin Barker (2017).
namespace CircularBaseSeven

open OMA.S_oeis_a125370 Finset PowerSeries

private abbrev Digit := Fin 7

private abbrev cons {n : ℕ} (u : Digit) (w : Fin n → Digit) : Fin (n + 1) → Digit :=
  @Fin.cons n (fun _ ↦ Digit) u w

private abbrev snoc {n : ℕ} (w : Fin n → Digit) (v : Digit) : Fin (n + 1) → Digit :=
  @Fin.snoc n (fun _ ↦ Digit) w v

private abbrev Edge := adjOk

private def matrix : Matrix Digit Digit ℚ := fun u v ↦ if Edge u v then 1 else 0

private def Path {n : ℕ} (u v : Digit) (w : Fin n → Digit) : Prop :=
  ∀ i : Fin (n + 1),
    Edge (snoc (cons u w) v i.castSucc) (snoc (cons u w) v i.succ)

private instance {n : ℕ} (u v : Digit) (w : Fin n → Digit) : Decidable (Path u v w) := by
  unfold Path
  infer_instance

private lemma path_empty (u v : Digit) (w : Fin 0 → Digit) : Path u v w ↔ Edge u v := by
  have h0 : Edge (snoc (cons u w) v (0 : Fin 1).castSucc)
      (snoc (cons u w) v (Fin.last 1)) ↔ Edge u v := by
    rw [show snoc (cons u w) v (Fin.last 1) = v from Fin.snoc_last ..,
      show snoc (cons u w) v (0 : Fin 1).castSucc = u from
        (Fin.snoc_castSucc ..).trans (Fin.cons_zero ..)]
  constructor
  · intro h
    exact h0.1 (h 0)
  · intro h i
    have hi : i = 0 := Fin.ext (by have hi := i.isLt; simp at hi; omega)
    subst i
    exact h0.2 h

private lemma path_cons {n : ℕ} (u v x : Digit) (w : Fin n → Digit) :
    Path u v (cons x w) ↔ Edge u x ∧ Path x v w := by
  unfold Path
  have hs : snoc (cons u (cons x w)) v = cons u (snoc (cons x w) v) :=
    (Fin.cons_snoc_eq_snoc_cons u (cons x w) v).symm
  rw [hs, Fin.forall_fin_succ]
  have hcast (i : Fin (n + 1)) : i.succ.castSucc = i.castSucc.succ := Fin.ext rfl
  have hzero : snoc (cons x w) v 0 = x := by
    change snoc (cons x w) v (0 : Fin (n + 1)).castSucc = x
    simp [snoc, cons]
  simp only [Fin.castSucc_zero, cons, Fin.cons_zero, Fin.cons_succ, hcast]
  change (Edge u (snoc (cons x w) v 0) ∧ _) ↔ _
  rw [hzero]

private lemma path_sum (n : ℕ) (u v : Digit) :
    (∑ w : Fin n → Digit, (if Path u v w then 1 else 0 : ℚ)) = (matrix ^ (n + 1)) u v := by
  induction n generalizing u v with
  | zero =>
    simp only [path_empty, Fintype.sum_unique, Nat.zero_add, pow_one, matrix]
  | succ n ih =>
    let e := Fin.consEquiv (fun _ : Fin (n + 1) ↦ Digit)
    have hs :
        (∑ w : Fin (n + 1) → Digit, (if Path u v w then 1 else 0 : ℚ)) =
          ∑ p : Digit × (Fin n → Digit), (if Path u v (cons p.1 p.2) then 1 else 0 : ℚ) := by
      exact (Fintype.sum_equiv e _ _ fun p ↦ rfl).symm
    rw [hs, Fintype.sum_prod_type, pow_succ', Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro x _
    simp only [path_cons]
    by_cases hx : Edge u x
    · simp only [hx, true_and, matrix, if_true, one_mul]
      exact ih x v
    · simp only [hx, false_and, if_false, sum_const_zero, matrix, zero_mul]

private lemma snoc_next {n : ℕ} (w : Fin (n + 1) → Digit) (i : Fin (n + 1)) :
    snoc w (w 0) i.succ = w ⟨(i.val + 1) % (n + 1), Nat.mod_lt _ (by omega)⟩ := by
  by_cases h : i.val + 1 < n + 1
  · have heq : i.succ = (⟨(i.val + 1) % (n + 1), Nat.mod_lt _ (by omega)⟩ : Fin (n + 1)).castSucc :=
      Fin.ext (by simp [Nat.mod_eq_of_lt h])
    rw [heq]
    exact Fin.snoc_castSucc ..
  · have hv : i.val + 1 = n + 1 := by omega
    have heq : i.succ = Fin.last (n + 1) := Fin.ext hv
    rw [heq, show snoc w (w 0) (Fin.last (n + 1)) = w 0 from Fin.snoc_last ..]
    congr 1
    exact Fin.ext (by simp [hv])

private lemma path_cycle {n : ℕ} (u : Digit) (w : Fin n → Digit) :
    Path u u w ↔ ∀ i : Fin (n + 1),
      Edge ((cons u w) i)
        ((cons u w) ⟨(i.val + 1) % (n + 1), Nat.mod_lt _ (by omega)⟩) := by
  unfold Path
  apply forall_congr'
  intro i
  have h0 : snoc (cons u w) u i.castSucc = (cons u w) i := Fin.snoc_castSucc ..
  have hn : snoc (cons u w) u i.succ =
      (cons u w) ⟨(i.val + 1) % (n + 1), Nat.mod_lt _ (by omega)⟩ := by
    simpa only [cons, Fin.cons_zero] using snoc_next (cons u w) i
  rw [h0, hn]

private lemma count_as_trace (n : ℕ) :
    (a (n + 1) : ℚ) = Matrix.trace (matrix ^ (n + 1)) := by
  classical
  let e := Fin.consEquiv (fun _ : Fin (n + 1) ↦ Digit)
  have hs :
      (∑ w : Fin (n + 1) → Digit, (if ∀ i : Fin (n + 1),
        Edge (w i) (w ⟨(i.val + 1) % (n + 1), Nat.mod_lt _ (by omega)⟩) then 1 else 0 : ℚ)) =
      ∑ p : Digit × (Fin n → Digit), (if Path p.1 p.1 p.2 then 1 else 0 : ℚ) := by
    symm
    apply Fintype.sum_equiv e
    intro p
    simp only [path_cycle]
    rfl
  rw [Fintype.sum_prod_type] at hs
  simp_rw [path_sum] at hs
  rw [Matrix.trace]
  change _ = ∑ x, (matrix ^ (n + 1)) x x
  rw [← hs]
  simp only [a, isValid, Edge]
  exact (Finset.sum_boole _ _).symm

/-- The five middle digits have identical adjacency rows. -/
private lemma matrix_relation :
    matrix ^ 4 = (7 : ℚ) • matrix ^ 3 - matrix ^ 2 - (5 : ℚ) • matrix := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide +kernel

private lemma recurrence (n : ℕ) (hn : 4 ≤ n) :
    (a n : ℚ) = 7 * a (n - 1) - a (n - 2) - 5 * a (n - 3) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  have H := congrArg (fun A : Matrix Digit Digit ℚ ↦ Matrix.trace (matrix ^ k * A)) matrix_relation
  simp only [mul_sub, mul_smul_comm, ← pow_add, ← pow_succ,
    Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul] at H
  rw [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega,
    show k + 4 - 3 = k + 1 by omega]
  exact (count_as_trace (k + 3)).trans (H.trans (by
    rw [count_as_trace (k + 2), count_as_trace (k + 1), count_as_trace k]))

private lemma v0 : a 0 = 1 := by decide +kernel

private lemma v1 : a 1 = 7 := by
  have h := count_as_trace 0
  change (a 1 : ℚ) = Matrix.trace (matrix ^ 1) at h
  rw [show Matrix.trace (matrix ^ 1) = 7 by decide +kernel] at h
  exact_mod_cast h

private lemma v2 : a 2 = 47 := by
  have h := count_as_trace 1
  change (a 2 : ℚ) = Matrix.trace (matrix ^ 2) at h
  rw [show Matrix.trace (matrix ^ 2) = 47 by decide +kernel] at h
  exact_mod_cast h

private lemma v3 : a 3 = 307 := by
  have h := count_as_trace 2
  change (a 3 : ℚ) = Matrix.trace (matrix ^ 3) at h
  rw [show Matrix.trace (matrix ^ 3) = 307 by decide +kernel] at h
  exact_mod_cast h

private lemma gf :
    PowerSeries.mk (fun n => (a n : ℚ)) * ((1-X)*(1-6*X-5*X^2)) = 1-X^2-10*X^3 := by
  let F : PowerSeries ℚ := PowerSeries.mk (fun n => (a n : ℚ))
  change F * _ = _
  have hmul : F * ((1 - X) * (1 - 6 * X - 5 * X ^ 2)) =
      F - C 7 * (X ^ 1 * F) + X ^ 2 * F + C 5 * (X ^ 3 * F) := by
    simp only [map_ofNat]
    ring
  have hnum : (1 - X ^ 2 - 10 * X ^ 3 : PowerSeries ℚ) =
      1 - X ^ 2 - C 10 * X ^ 3 := by simp only [map_ofNat]
  rw [hmul, hnum]
  ext n
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul', coeff_X_pow, coeff_one, F, coeff_mk]
  by_cases hn : 4 ≤ n
  · simp only [if_pos (show 1 ≤ n by omega), if_pos (show 2 ≤ n by omega),
      if_pos (show 3 ≤ n by omega), if_neg (show n ≠ 0 by omega),
      if_neg (show n ≠ 2 by omega), if_neg (show n ≠ 3 by omega), mul_zero, sub_zero]
    linarith [recurrence n hn]
  · interval_cases n <;> norm_num [v0, v1, v2, v3]

private lemma root_step (x : ℝ) (hx : x ^ 2 = 6*x+5) (k : ℕ) :
    x^(k+3) = 7*x^(k+2) - x^(k+1) - 5*x^k := by
  have h3 : x^3 = 7*x^2-x-5 := by linear_combination (x-1)*hx
  simp only [pow_add]
  rw [h3]
  ring

private lemma closed (n : ℕ) (hn : 1 ≤ n) :
    (a n : ℝ) = 1 + (3 - Real.sqrt 14)^n + (3 + Real.sqrt 14)^n := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 14 by norm_num)
  have hm : (3 - Real.sqrt 14)^2 = 6*(3 - Real.sqrt 14)+5 := by nlinarith
  have hp : (3 + Real.sqrt 14)^2 = 6*(3 + Real.sqrt 14)+5 := by nlinarith
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hsmall : n ≤ 3
    · interval_cases n <;> norm_num [v1, v2, v3] <;> ring_nf <;> nlinarith
    · obtain ⟨k, rfl⟩ : ∃ k, n = k+3 := ⟨n-3, by omega⟩
      have hrec : (a (k+3) : ℝ) = 7*a (k+2) - a (k+1) - 5*a k := by
        have h := recurrence (k+3) (by omega)
        rw [show k+3-1 = k+2 by omega, show k+3-2 = k+1 by omega,
          show k+3-3 = k by omega] at h
        exact_mod_cast h
      rw [hrec, ih (k+2) (by omega) (by omega), ih (k+1) (by omega) (by omega),
        ih k (by omega) (by omega), root_step _ hm, root_step _ hp]
      ring

end CircularBaseSeven

theorem OMA.solution : type_of% @OMA.S_oeis_a125370.main := by
  refine ⟨CircularBaseSeven.gf, CircularBaseSeven.closed, ?_⟩
  intro n hn
  exact_mod_cast CircularBaseSeven.recurrence n hn
