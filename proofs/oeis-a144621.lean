import OMAStatements.S_oeis_a144621

-- Problem: A144621, a(n+1) = det of the 2^n x 2^n matrix 1 + v_2(i+j-1) (Stephan's conjecture).
-- Credit: @bnb9001

namespace OMA_A144621_Proof

open Matrix OMA.S_oeis_a144621
open scoped Kronecker

def Mq (n : ℕ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℚ :=
  Matrix.of fun i j => (1 + (padicValNat 2 (i.val + j.val + 1) : ℚ))

def sw : Matrix (Fin 2) (Fin 2) ℚ := !![0, 1; 1, 0]

def Jm (ι : Type) [Fintype ι] : Matrix ι ι ℚ := Matrix.of fun _ _ => 1

def e (n : ℕ) : Fin (2 ^ n) × Fin 2 ≃ Fin (2 ^ (n + 1)) :=
  finProdFinEquiv.trans (finCongr (pow_succ 2 n).symm)

theorem e_val (n : ℕ) (x : Fin (2 ^ n)) (b : Fin 2) :
    ((e n) (x, b)).val = b.val + 2 * x.val := rfl

theorem v2_odd (k : ℕ) : padicValNat 2 (2 * k + 1) = 0 :=
  padicValNat.eq_zero_of_not_dvd (by omega)

theorem v2_even (k : ℕ) : padicValNat 2 (2 * (k + 1)) = 1 + padicValNat 2 (k + 1) := by
  rw [padicValNat.mul (by norm_num) (by omega), padicValNat.self (by norm_num)]

theorem entry (x y : ℕ) (p q : Fin 2) :
    (1 + (padicValNat 2 (p.val + 2 * x + (q.val + 2 * y) + 1) : ℚ)) =
      (1 + (padicValNat 2 (x + y + 1) : ℚ)) * sw p q + 1 := by
  fin_cases p <;> fin_cases q <;> simp [sw]
  · omega
  · rw [show 2 * x + (1 + 2 * y) + 1 = 2 * (x + y + 1) by ring, v2_even]; push_cast; ring
  · rw [show 1 + 2 * x + 2 * y + 1 = 2 * (x + y + 1) by ring, v2_even]; push_cast; ring
  · omega

theorem Mq_succ (n : ℕ) : Mq (n + 1) = reindex (e n) (e n) (Mq n ⊗ₖ sw + Jm _) := by
  ext i j
  obtain ⟨⟨x, p⟩, rfl⟩ := (e n).surjective i
  obtain ⟨⟨y, q⟩, rfl⟩ := (e n).surjective j
  rw [reindex_apply, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
    Matrix.add_apply, kronecker_apply]
  simp only [Mq, Jm, of_apply, e_val]
  exact entry x.val y.val p q

theorem sw_rowsum (p : Fin 2) : ∑ q, sw p q = 1 := by
  fin_cases p <;> simp [sw, Fin.sum_univ_two]

theorem rowsum (n : ℕ) : ∀ i, ∑ j, Mq n i j = (2 : ℚ) ^ (n + 1) - 1 := by
  induction n with
  | zero =>
    intro i
    have hsub : ∀ x : Fin (2 ^ 0), x = ⟨0, by norm_num⟩ := fun x => Fin.ext (by
      have := x.2; simp at this; simp [this])
    rw [Fintype.sum_eq_single (⟨0, by norm_num⟩ : Fin (2 ^ 0)) (fun x hx => absurd (hsub x) hx)]
    rw [hsub i]; simp [Mq]; norm_num
  | succ n ih =>
    intro i
    obtain ⟨⟨x, p⟩, rfl⟩ := (e n).surjective i
    rw [Mq_succ]
    simp only [reindex_apply, submatrix_apply, Equiv.symm_apply_apply]
    rw [← (e n).sum_comp]
    simp only [Equiv.symm_apply_apply, Matrix.add_apply, kronecker_apply, Jm, of_apply]
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, kroneckerMap_apply, kronecker_apply]
    simp only [← Finset.mul_sum, sw_rowsum, mul_one, ih]
    push_cast; ring

theorem det_add_J {ι : Type} [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℚ) (s : ℚ) (hs : s ≠ 0)
    (hB : ∀ i, ∑ j, B i j = s) :
    (B + Jm ι).det = B.det * (1 + (Fintype.card ι : ℚ) / s) := by
  have key : B + Jm ι = B * (1 + replicateCol Unit (fun _ : ι => s⁻¹) *
      replicateRow Unit (fun _ : ι => (1 : ℚ))) := by
    rw [Matrix.mul_add, Matrix.mul_one]
    congr 1
    ext i j
    have h1 : ∀ x, (replicateCol Unit (fun _ : ι => s⁻¹) * replicateRow Unit (fun _ : ι => (1 : ℚ))) x j
        = s⁻¹ := by
      intro x; simp [Matrix.mul_apply]
    rw [Matrix.mul_apply]
    simp only [h1, Jm, of_apply]
    rw [← Finset.sum_mul, hB i, mul_inv_cancel₀ hs]
  rw [key, det_mul, det_one_add_replicateCol_mul_replicateRow]
  congr 1
  simp [dotProduct, div_eq_mul_inv]

theorem kron_rowsum (n : ℕ) (i : Fin (2 ^ n) × Fin 2) :
    ∑ j, (Mq n ⊗ₖ sw) i j = (2 : ℚ) ^ (n + 1) - 1 := by
  obtain ⟨x, p⟩ := i
  rw [Fintype.sum_prod_type]
  simp only [kronecker_apply, ← Finset.mul_sum, sw_rowsum, mul_one, rowsum]

noncomputable def D (n : ℕ) : ℚ := (Mq n).det

theorem D_succ (n : ℕ) :
    D (n + 1) = D n ^ 2 * (-1) ^ (2 ^ n) * (1 + 2 ^ (n + 1) / (2 ^ (n + 1) - 1)) := by
  unfold D
  rw [Mq_succ, det_reindex_self]
  have hs : (2 : ℚ) ^ (n + 1) - 1 ≠ 0 := by
    have : (2 : ℚ) ≤ 2 ^ (n + 1) := by
      calc (2 : ℚ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  rw [det_add_J _ _ hs (kron_rowsum n), det_kronecker]
  simp only [Fintype.card_prod, Fintype.card_fin]
  have hsw : sw.det = -1 := by simp [sw, det_fin_two]
  rw [hsw]
  push_cast
  ring

theorem D_zero : D 0 = 1 := by
  unfold D
  haveI : Subsingleton (Fin (2 ^ 0)) := ⟨fun x y => Fin.ext (by
    have := x.2; have := y.2; simp only [pow_zero] at *; omega)⟩
  rw [det_eq_elem_of_subsingleton _ ⟨0, by norm_num⟩]
  simp [Mq]

theorem D_one : D 1 = -3 := by
  rw [D_succ, D_zero]; norm_num

theorem D_two : D 2 = 21 := by
  rw [D_succ, D_one]; norm_num

theorem D_rec (k : ℕ) :
    D (k + 2) = D (k + 1) ^ 2 * (1 + 2 ^ (k + 2) / (2 ^ (k + 2) - 1)) := by
  rw [D_succ]
  have : ((-1 : ℚ)) ^ (2 ^ (k + 1)) = 1 := Even.neg_one_pow ⟨2 ^ k, by ring⟩
  rw [this, mul_one]

theorem main_q : ∀ k : ℕ, (a (k + 3) : ℚ) = D (k + 2) ∧ (a (k + 2) : ℚ) ^ 2 = D (k + 1) ^ 2 := by
  intro k
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · have : a 3 = 21 := by simp [a]
      rw [D_two, this]; norm_num
    · have : a 2 = 3 := by simp [a]
      rw [D_one, this]; norm_num
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    have ha : a (k + 4) = a (k + 3) * (3 * a (k + 3) - 2 * a (k + 2) ^ 2) := rfl
    refine ⟨?_, ?_⟩
    · have hT : (4 : ℚ) ≤ 2 ^ (k + 2) := by
        calc (4 : ℚ) = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (k + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
      set T : ℚ := 2 ^ (k + 2) with hTdef
      have hT3 : (2 : ℚ) ^ (k + 3) = 2 * T := by rw [hTdef]; ring
      have e1 := D_rec k
      have e2 := D_rec (k + 1)
      rw [show k + 1 + 2 = k + 3 by ring, show k + 1 + 1 = k + 2 by ring, hT3] at e2
      rw [← hTdef] at e1
      rw [show k + 1 + 3 = k + 4 by ring, show k + 1 + 2 = k + 3 by ring, ha]
      push_cast
      rw [h1, h2, e2]
      have hT1 : T - 1 ≠ 0 := by linarith
      have hT2 : 2 * T - 1 ≠ 0 := by linarith
      have h2T : T - 1 + T ≠ 0 := by linarith
      have hD1 : D (k + 1) ^ 2 = D (k + 2) / (1 + T / (T - 1)) := by
        rw [e1]; field_simp
      rw [hD1]
      field_simp
      ring
    · rw [show k + 1 + 2 = k + 3 by ring, show k + 1 + 1 = k + 2 by ring, h1]

end OMA_A144621_Proof

open Matrix OMA.S_oeis_a144621 OMA_A144621_Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a144621.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have hmap : (Int.castRingHom ℚ).mapMatrix (M (k + 2)) = Mq (k + 2) := by
    ext i j
    simp [M, Mq]
  have h := (Int.castRingHom ℚ).map_det (M (k + 2))
  rw [hmap] at h
  have hq := (main_q k).1
  have hc : (((M (k + 2)).det : ℤ) : ℚ) = D (k + 2) := by
    unfold D; simpa using h
  apply Int.cast_injective (α := ℚ)
  rw [show k + 2 + 1 = k + 3 by ring, hq, hc]
