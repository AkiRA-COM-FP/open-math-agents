import OMAStatements.S_oeis_a066933

namespace OMA.P_oeis_a066933

open Polynomial Matrix

private lemma coeff_f_n (n k : ℕ) :
    (OMA.S_oeis_a066933.f n).coeff k =
      if 1 ≤ k ∧ k ≤ n then ((Nat.nth Nat.Prime (k - 1) : ℕ) : ℤ) else 0 := by
  unfold OMA.S_oeis_a066933.f
  rw [finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  by_cases hk : 1 ≤ k ∧ k ≤ n
  · rw [if_pos hk, Finset.sum_eq_single k]
    · simp
    · intro b _ hbk
      rw [if_neg (Ne.symm hbk)]
    · intro hnot
      exfalso
      exact hnot (Finset.mem_Icc.mpr hk)
  · rw [if_neg hk]
    apply Finset.sum_eq_zero
    intro b hb
    have hbk : k ≠ b := by
      intro h
      subst h
      exact hk (Finset.mem_Icc.mp hb)
    rw [if_neg hbk]

private lemma natDegree_f_n {n : ℕ} (hn : 0 < n) :
    (OMA.S_oeis_a066933.f n).natDegree = n := by
  apply le_antisymm
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro k hk
    rw [coeff_f_n, if_neg]
    omega
  · apply Polynomial.le_natDegree_of_ne_zero
    rw [coeff_f_n, if_pos ⟨hn, le_rfl⟩]
    have hp : (Nat.nth Nat.Prime (n - 1)).Prime :=
      Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime (n - 1)
    exact_mod_cast hp.ne_zero

private lemma natDegree_X_pow_sub_one {n : ℕ} (hn : 0 < n) :
    ((X ^ n - 1 : ℤ[X])).natDegree = n := by
  have h1 : (X ^ n : ℤ[X]).natDegree = n := Polynomial.natDegree_X_pow n
  have h2 : (1 : ℤ[X]).natDegree < (X ^ n : ℤ[X]).natDegree := by
    rw [Polynomial.natDegree_one, h1]
    exact hn
  rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt h2, h1]

private lemma coeff_X_pow_sub_one {n : ℕ} (hn : 0 < n) (k : ℕ) :
    ((X ^ n - 1 : ℤ[X])).coeff k =
      if k = n then 1 else if k = 0 then -1 else 0 := by
  rw [coeff_sub, coeff_X_pow, coeff_one]
  by_cases hkn : k = n
  · subst hkn
    have hne : k ≠ 0 := Nat.ne_of_gt hn
    simp [hne]
  · by_cases hk0 : k = 0
    · subst hk0
      simp [hkn]
    · simp [hkn, hk0]

private def swapPair (n : ℕ) (k : ℕ) : Equiv.Perm (Fin n) :=
  if hk : k < n ∧ n - 1 - k < n then
    Equiv.swap ⟨k, hk.1⟩ ⟨n - 1 - k, hk.2⟩
  else 1

private def revPrefix (n : ℕ) : ℕ → Equiv.Perm (Fin n)
  | 0 => 1
  | m + 1 => revPrefix n m * swapPair n m

private lemma revPrefix_apply (n m : ℕ) (hm : 2 * m ≤ n) (x : Fin n) :
    (revPrefix n m x).val =
      if x.val < m ∨ n - m ≤ x.val then n - 1 - x.val else x.val := by
  induction m generalizing x with
  | zero =>
    simp [revPrefix]
  | succ m ih =>
    have hm' : 2 * m ≤ n := by omega
    have hlt1 : m < n := by omega
    have hlt2 : n - 1 - m < n := by omega
    have hsp : swapPair n m = Equiv.swap ⟨m, hlt1⟩ ⟨n - 1 - m, hlt2⟩ := by
      simp [swapPair, hlt1, hlt2]
    change (revPrefix n m (swapPair n m x)).val = _
    rw [ih hm' (swapPair n m x), hsp]
    by_cases hx1 : x = ⟨m, hlt1⟩
    · subst hx1
      rw [Equiv.swap_apply_left]
      simp only
      split_ifs <;> omega
    · by_cases hx2 : x = ⟨n - 1 - m, hlt2⟩
      · subst hx2
        rw [Equiv.swap_apply_right]
        simp only
        split_ifs <;> omega
      · rw [Equiv.swap_apply_of_ne_of_ne hx1 hx2]
        have h1 : x.val ≠ m := fun h => hx1 (Fin.ext h)
        have h2 : x.val ≠ n - 1 - m := fun h => hx2 (Fin.ext h)
        split_ifs <;> omega

private lemma revPrefix_eq_revPerm (n : ℕ) : revPrefix n (n / 2) = Fin.revPerm := by
  ext x
  have h := revPrefix_apply n (n / 2) (by omega) x
  rw [h, Fin.revPerm_apply, Fin.val_rev]
  by_cases hcond : x.val < n / 2 ∨ n - n / 2 ≤ x.val
  · rw [if_pos hcond]
    omega
  · rw [if_neg hcond]
    omega

private lemma sign_revPrefix (n m : ℕ) (hm : 2 * m ≤ n) :
    (Equiv.Perm.sign (revPrefix n m) : ℤ) = (-1 : ℤ) ^ m := by
  induction m with
  | zero =>
    simp [revPrefix]
  | succ m ih =>
    have hlt1 : m < n := by omega
    have hlt2 : n - 1 - m < n := by omega
    have hne : (⟨m, hlt1⟩ : Fin n) ≠ ⟨n - 1 - m, hlt2⟩ := by
      intro h
      have hv := congrArg Fin.val h
      dsimp at hv
      omega
    have hsp : swapPair n m = Equiv.swap ⟨m, hlt1⟩ ⟨n - 1 - m, hlt2⟩ := by
      simp [swapPair, hlt1, hlt2]
    change ((Equiv.Perm.sign (revPrefix n m * swapPair n m) : ℤˣ) : ℤ) = _
    rw [map_mul, Units.val_mul, ih (by omega), hsp, Equiv.Perm.sign_swap hne]
    simp [pow_succ]

private lemma sign_revPerm (n : ℕ) :
    (Equiv.Perm.sign (Fin.revPerm (n := n)) : ℤ) = (-1 : ℤ) ^ (n / 2) := by
  rw [← revPrefix_eq_revPerm, sign_revPrefix n (n / 2) (by omega)]

private lemma main_pos {n : ℕ} (hn : 0 < n) :
    OMA.S_oeis_a066933.a n =
      (-1) ^ (n + n / 2) *
        Polynomial.resultant (OMA.S_oeis_a066933.f n) (X ^ n - 1) := by
  let f := OMA.S_oeis_a066933.f n
  let g : ℤ[X] := X ^ n - 1
  have hdegf : f.natDegree = n := natDegree_f_n hn
  have hdegg : g.natDegree = n := natDegree_X_pow_sub_one hn
  change OMA.S_oeis_a066933.a n = (-1) ^ (n + n / 2) * Polynomial.resultant f g
  have hres : Polynomial.resultant f g = (Polynomial.sylvester f g n n).det := by
    unfold Polynomial.resultant
    rw [hdegf, hdegg]
  rw [hres]
  let S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ :=
    (Polynomial.sylvester f g n n).reindex finSumFinEquiv.symm finSumFinEquiv.symm
  have hSdet : (Polynomial.sylvester f g n n).det = S.det := by
    rw [Matrix.det_reindex_self]
  rw [hSdet]
  let B : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i j =>
    if j.val < i.val then ((Nat.nth Nat.Prime (i.val - j.val - 1) : ℕ) : ℤ) else 0
  let D : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i j =>
    if i.val ≤ j.val then ((Nat.nth Nat.Prime (n + i.val - j.val - 1) : ℕ) : ℤ) else 0
  have hSblock : S = Matrix.fromBlocks (-(1 : Matrix (Fin n) (Fin n) ℤ)) B 1 D := by
    ext r c
    cases r with
    | inl i =>
      cases c with
      | inl j =>
        simp only [S, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
          finSumFinEquiv_apply_left, Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left,
          Set.mem_Icc, Fin.val_castAdd, Matrix.fromBlocks_apply₁₁, Matrix.neg_apply,
          Matrix.one_apply]
        have hi := i.isLt
        have hj := j.isLt
        by_cases hij : j.val ≤ i.val
        · have hle : i.val ≤ j.val + n := by omega
          rw [if_pos ⟨hij, hle⟩, coeff_X_pow_sub_one hn]
          have hne : i.val - j.val ≠ n := by omega
          rw [if_neg hne]
          by_cases heq : i = j
          · subst heq
            simp
          · have hne0 : i.val - j.val ≠ 0 := by
              intro h0
              exact heq (Fin.ext (by omega))
            rw [if_neg hne0, if_neg heq, neg_zero]
        · rw [if_neg (fun h => hij h.1)]
          have hne : i ≠ j := by
            intro h
            subst h
            exact hij le_rfl
          rw [if_neg hne, neg_zero]
      | inr j =>
        simp only [S, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
          finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Polynomial.sylvester,
          Matrix.of_apply, Fin.addCases_right, Set.mem_Icc, Fin.val_castAdd,
          Matrix.fromBlocks_apply₁₂, B]
        have hi := i.isLt
        have hj := j.isLt
        by_cases hij : j.val < i.val
        · rw [if_pos ⟨by omega, by omega⟩, if_pos hij, coeff_f_n, if_pos ⟨by omega, by omega⟩]
        · rw [if_neg hij]
          by_cases hle : j.val ≤ i.val
          · have heq : i.val = j.val := by omega
            rw [if_pos ⟨hle, by omega⟩, coeff_f_n, if_neg (by omega)]
          · rw [if_neg (fun h => hle h.1)]
    | inr i =>
      cases c with
      | inl j =>
        simp only [S, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
          finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Polynomial.sylvester,
          Matrix.of_apply, Fin.addCases_left, Set.mem_Icc, Fin.val_natAdd,
          Matrix.fromBlocks_apply₂₁, Matrix.one_apply]
        have hi := i.isLt
        have hj := j.isLt
        by_cases hij : i.val ≤ j.val
        · rw [if_pos ⟨by omega, by omega⟩, coeff_X_pow_sub_one hn]
          by_cases heq : i = j
          · subst heq
            have hsub : n + i.val - i.val = n := by omega
            rw [if_pos hsub, if_pos rfl]
          · have hne1 : n + i.val - j.val ≠ n := by
              intro h
              exact heq (Fin.ext (by omega))
            have hne0 : n + i.val - j.val ≠ 0 := by omega
            rw [if_neg hne1, if_neg hne0, if_neg heq]
        · rw [if_neg (fun h => hij (by omega))]
          have hne : i ≠ j := by
            intro h
            subst h
            exact hij le_rfl
          rw [if_neg hne]
      | inr j =>
        simp only [S, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
          finSumFinEquiv_apply_right, Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right,
          Set.mem_Icc, Fin.val_natAdd, Matrix.fromBlocks_apply₂₂, D]
        have hi := i.isLt
        have hj := j.isLt
        by_cases hij : i.val ≤ j.val
        · rw [if_pos ⟨by omega, by omega⟩, if_pos hij, coeff_f_n, if_pos ⟨by omega, by omega⟩]
        · rw [if_neg (fun h => hij (by omega)), if_neg hij]
  rw [hSblock]
  let _ : Invertible (-(1 : Matrix (Fin n) (Fin n) ℤ)) :=
    ⟨-1, by simp, by simp⟩
  have hinv : ⅟(-(1 : Matrix (Fin n) (Fin n) ℤ)) = -1 := by
    exact invOf_eq_right_inv (by simp)
  rw [Matrix.det_fromBlocks₁₁, hinv, Matrix.det_neg, Matrix.det_one, mul_one,
    Fintype.card_fin, Matrix.one_mul, Matrix.neg_mul, sub_neg_eq_add, Matrix.one_mul]
  let A : Matrix (Fin n) (Fin n) ℤ :=
    Matrix.of fun i j : Fin n => ((Nat.nth Nat.Prime ((i.val + j.val) % n) : ℕ) : ℤ)
  have hDB : (D + B).submatrix id Fin.revPerm = A := by
    ext i j
    simp only [Matrix.submatrix_apply, id_eq, Matrix.add_apply, D, B, A, Matrix.of_apply,
      Fin.revPerm_apply, Fin.val_rev]
    have hi := i.isLt
    have hj := j.isLt
    by_cases hsum : i.val + j.val < n
    · have h1 : i.val ≤ n - (j.val + 1) := by omega
      have h2 : ¬ (n - (j.val + 1) < i.val) := by omega
      rw [if_pos h1, if_neg h2, add_zero]
      have hidx : n + i.val - (n - (j.val + 1)) - 1 = (i.val + j.val) % n := by
        rw [Nat.mod_eq_of_lt hsum]
        omega
      rw [hidx]
    · have h1 : ¬ (i.val ≤ n - (j.val + 1)) := by omega
      have h2 : n - (j.val + 1) < i.val := by omega
      rw [if_neg h1, if_pos h2, zero_add]
      have hidx : i.val - (n - (j.val + 1)) - 1 = (i.val + j.val) % n := by
        have hmod : (i.val + j.val) % n = i.val + j.val - n := by
          have := Nat.mod_eq_sub_mod (by omega : n ≤ i.val + j.val)
          rw [this, Nat.mod_eq_of_lt (by omega)]
        rw [hmod]
        omega
      rw [hidx]
  have hdetA : A.det = (Equiv.Perm.sign (Fin.revPerm (n := n)) : ℤ) * (D + B).det := by
    rw [← hDB]
    simpa [Matrix.submatrix] using Matrix.det_permute' Fin.revPerm (D + B)
  rw [sign_revPerm] at hdetA
  change A.det = (-1) ^ (n + n / 2) * ((-1) ^ n * (D + B).det)
  rw [hdetA, pow_add]
  have hsq1 : ((-1 : ℤ) ^ n) * ((-1 : ℤ) ^ n) = 1 := by
    rw [← mul_pow]; norm_num
  calc
    (-1 : ℤ) ^ (n / 2) * (D + B).det
      = ((-1) ^ n * (-1) ^ n) * ((-1) ^ (n / 2) * (D + B).det) := by rw [hsq1, one_mul]
    _ = (-1) ^ n * (-1) ^ (n / 2) * ((-1) ^ n * (D + B).det) := by ring

theorem main_proof : ∀ n : ℕ,
    OMA.S_oeis_a066933.a n =
      (-1) ^ (n + n / 2) *
        Polynomial.resultant (OMA.S_oeis_a066933.f n) (X ^ n - 1) := by
  intro n
  cases n with
  | zero =>
    have hf0 : OMA.S_oeis_a066933.f 0 = 0 := by simp [OMA.S_oeis_a066933.f]
    have hg0 : (X ^ 0 - 1 : ℤ[X]) = 0 := by simp
    rw [hf0, hg0]
    simp [OMA.S_oeis_a066933.a, Polynomial.resultant]
  | succ m =>
    exact main_pos (Nat.succ_pos m)

end OMA.P_oeis_a066933

theorem OMA.solution : type_of% @OMA.S_oeis_a066933.main :=
  OMA.P_oeis_a066933.main_proof
