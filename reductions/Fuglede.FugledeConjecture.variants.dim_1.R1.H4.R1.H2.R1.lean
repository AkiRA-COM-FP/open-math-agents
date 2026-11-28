import OMAReductions.R_Fuglede_FugledeConjecture_variants_dim_1_R1_H4_R1
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.GroupTheory.Coset.Basic

/-!
Reduction to the spectral-implies-tile direction for individual sets.
The lifting uses the cyclic layer construction of Farkas, Matolcsi and Móra,
On Fuglede's conjecture and the existence of universal spectra, Remark 2.
Prescribed powers of a radix distinguish the contributions of the layers.
-/

namespace OMA.R_Fuglede_FugledeConjecture_variants_dim_1_R1_H4_R1_H2_R1

/-- Every nonempty spectral set in a finite cyclic group tiles that group. -/
def H1 : Prop :=
  ∀ (M : ℕ) (_ : NeZero M) (W K : Finset (ZMod M)),
    0 < W.card → K.card = W.card →
    (∀ ξ₁ ∈ K, ∀ ξ₂ ∈ K, ξ₁ ≠ ξ₂ →
      ∑ w ∈ W, Complex.exp (2 * Real.pi * Complex.I *
        (((ξ₁.val : ℝ) - (ξ₂.val : ℝ)) * (w.val : ℝ) / (M : ℝ))) = 0) →
    ∃ C : Finset (ZMod M), ∀ m : ZMod M,
      ∃! q : {w // w ∈ W} × {c // c ∈ C}, q.1.1 + q.2.1 = m

/-- Lift a family with a shared spectrum to a single spectral set by taking
prescribed copies of its members in a cyclic extension. -/
def H2 : Prop :=
  ∀ (N : ℕ) (_ : NeZero N) (p r : ℕ), 0 < p → 0 < r →
    ∀ (Λ : Finset (ZMod N)) (A : Fin r → Finset (ZMod N)),
      Λ.card = p →
      (∀ i, (A i).card = p ∧
        ∀ ξ₁ ∈ Λ, ∀ ξ₂ ∈ Λ, ξ₁ ≠ ξ₂ →
          ∑ k ∈ A i, Complex.exp (2 * Real.pi * Complex.I *
            (((ξ₁.val : ℝ) - (ξ₂.val : ℝ)) * (k.val : ℝ) / (N : ℝ))) = 0) →
      ∃ (M : ℕ) (_ : NeZero M) (π : ZMod M →+ ZMod N) (W K : Finset (ZMod M)),
        M = N * (∑ i : Fin r, (2 * N) ^ i.val) ∧ Function.Surjective π ∧
        0 < W.card ∧ K.card = W.card ∧
        (∀ ξ₁ ∈ K, ∀ ξ₂ ∈ K, ξ₁ ≠ ξ₂ →
          ∑ w ∈ W, Complex.exp (2 * Real.pi * Complex.I *
            (((ξ₁.val : ℝ) - (ξ₂.val : ℝ)) * (w.val : ℝ) / (M : ℝ))) = 0) ∧
        (∀ x, (W.filter fun w => π w = x).card =
          ∑ i : Fin r, if x ∈ A i then (2 * N) ^ i.val else 0)

/-- Count a tiling in each fiber of the projection onto the smaller group. -/
lemma weighted_tile_counts {N M p r : ℕ} [NeZero N] [NeZero M] (hp : 0 < p)
    (A : Fin r → Finset (ZMod N)) (π : ZMod M →+ ZMod N) (W C : Finset (ZMod M))
    (hsize : M = N * (∑ i : Fin r, (2 * N) ^ i.val))
    (hsurj : Function.Surjective π) (hA : ∀ i, (A i).card = p)
    (hproj : ∀ x, (W.filter fun w => π w = x).card =
      ∑ i : Fin r, if x ∈ A i then (2 * N) ^ i.val else 0)
    (hC : ∀ m : ZMod M, ∃! q : {w // w ∈ W} × {c // c ∈ C}, q.1.1 + q.2.1 = m) :
    C.card ≤ N ∧ ∀ x : ZMod N,
      (∑ i : Fin r, (2 * N) ^ i.val * (C.filter fun c => x - π c ∈ A i).card) =
        ∑ i : Fin r, (2 * N) ^ i.val := by
  classical
  let weight (i : Fin r) := (2 * N) ^ i.val
  let L := ∑ i : Fin r, weight i
  change M = N * L at hsize
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne _)
  have hL : 0 < L := by
    by_contra hn
    have : L = 0 := by omega
    rw [this, mul_zero] at hsize
    exact NeZero.ne M hsize
  let addPair (q : W × C) : ZMod M := q.1.val + q.2.val
  have hadd : Function.Bijective addPair := (Function.bijective_iff_existsUnique _).2 hC
  let e : W × C ≃ ZMod M := Equiv.ofBijective addPair hadd
  have htile : W.card * C.card = M := by
    simpa only [Fintype.card_prod, Fintype.card_coe, ZMod.card] using Fintype.card_congr e
  have hW : W.card = p * L := by
    calc
      W.card = ∑ x : ZMod N, (W.filter fun w => π w = x).card := by
        symm
        simpa only [Finset.mem_univ, Finset.filter_true] using
          (Finset.sum_card_fiberwise_eq_card_filter W (Finset.univ : Finset (ZMod N)) π)
      _ = ∑ x : ZMod N, ∑ i : Fin r, if x ∈ A i then weight i else 0 := by
        exact Finset.sum_congr rfl (fun x _ => hproj x)
      _ = p * L := by
        rw [Finset.sum_comm, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero,
          Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const,
          hA i, nsmul_eq_mul]
        rfl
  refine ⟨?_, ?_⟩
  · have hmul : p * C.card = N := by
      apply Nat.eq_of_mul_eq_mul_right hL
      calc
        (p * C.card) * L = W.card * C.card := by rw [hW]; ac_rfl
        _ = N * L := htile.trans hsize
    calc
      C.card = 1 * C.card := (one_mul _).symm
      _ ≤ p * C.card := Nat.mul_le_mul_right _ hp
      _ = N := hmul
  · intro x
    let Fiber (z : ZMod N) := {m : ZMod M // π m = z}
    have hconst (z : ZMod N) : Fintype.card (Fiber z) = Fintype.card (Fiber x) :=
      Fintype.card_congr (AddMonoidHom.fiberEquivOfSurjective hsurj z x)
    have hFiber : Fintype.card (Fiber x) = L := by
      have hsigma := Fintype.card_congr (Equiv.sigmaFiberEquiv (fun m => π m))
      change Fintype.card (Σ z, Fiber z) = Fintype.card (ZMod M) at hsigma
      rw [Fintype.card_sigma, ZMod.card] at hsigma
      simp_rw [hconst] at hsigma
      rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul] at hsigma
      exact Nat.eq_of_mul_eq_mul_left hN (hsigma.trans hsize)
    let LeftFiber (c : C) := {w : W // π w.val = x - π c.val}
    let f : (Σ c : C, LeftFiber c) ≃ {q : W × C // π (e q) = x} :=
      { toFun := fun q => ⟨(q.2.val, q.1), by
          change π (q.2.val.val + q.1.val) = x
          rw [map_add, q.2.property, sub_add_cancel]⟩
        invFun := fun q => ⟨q.val.2, ⟨q.val.1, by
          have eq : π (q.val.1.val + q.val.2.val) = x := q.property
          rw [map_add] at eq
          exact eq_sub_iff_add_eq.mpr eq⟩⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have hleft (c : C) :
        Fintype.card (LeftFiber c) = (W.filter fun w => π w = x - π c.val).card := by
      rw [← Fintype.card_coe]
      apply Fintype.card_congr
      exact
        { toFun := fun w => ⟨w.val.val, Finset.mem_filter.mpr ⟨w.val.property, w.property⟩⟩
          invFun := fun w => ⟨⟨w.val, (Finset.mem_filter.mp w.property).1⟩,
            (Finset.mem_filter.mp w.property).2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    have hcount := Fintype.card_congr
      (f.trans (e.subtypeEquivOfSubtype (p := fun z => π z = x)))
    change Fintype.card (Σ c : C, LeftFiber c) = Fintype.card (Fiber x) at hcount
    rw [Fintype.card_sigma, hFiber] at hcount
    simp_rw [hleft, hproj] at hcount
    change (∑ i : Fin r, weight i * (C.filter fun c => x - π c ∈ A i).card) = L
    rw [← hcount, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.card_filter, Finset.mul_sum]
    rw [Finset.univ_eq_attach,
      Finset.sum_attach C (fun c : ZMod M => if x - π c ∈ A i then (2 * N) ^ i.val else 0)]
    apply Finset.sum_congr rfl
    intro c _
    by_cases h : x - π c ∈ A i <;> simp [h, weight]

lemma radix_digits_unique {r b : ℕ} (hb : 0 < b) (a d : Fin r → ℕ)
    (ha : ∀ i, a i < b) (hd : ∀ i, d i < b)
    (h : (∑ i : Fin r, b ^ i.val * a i) = ∑ i : Fin r, b ^ i.val * d i) :
    a = d := by
  induction r with
  | zero =>
    funext i
    exact Fin.elim0 i
  | succ r ih =>
    simp only [Fin.sum_univ_succ, Fin.val_zero, pow_zero, one_mul, Fin.val_succ,
      pow_succ', mul_assoc, ← Finset.mul_sum] at h
    have hzero := congrArg (fun n => n % b) h
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (ha 0),
      Nat.mod_eq_of_lt (hd 0)] at hzero
    rw [hzero] at h
    have htail := Nat.eq_of_mul_eq_mul_left hb (Nat.add_left_cancel h)
    have heq := ih (fun i => a i.succ) (fun i => d i.succ)
      (fun i => ha i.succ) (fun i => hd i.succ) htail
    funext i
    exact Fin.cases hzero (fun j => congrFun heq j) i

lemma projected_complement {N M r : ℕ} (A : Fin r → Finset (ZMod N))
    (π : ZMod M →+ ZMod N) (C : Finset (ZMod M))
    (h : ∀ i, ∀ m : ZMod N, (C.filter fun c => m - π c ∈ A i).card = 1) :
    ∃ B : Finset (ZMod N), ∀ i, ∀ m : ZMod N,
      ∃! q : {k // k ∈ A i} × {b // b ∈ B}, q.1.1 + q.2.1 = m := by
  classical
  refine ⟨C.image π, ?_⟩
  intro i m
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp (h i m)
  have hcmem : c ∈ C.filter (fun c => m - π c ∈ A i) := by
    rw [hc]
    exact Finset.mem_singleton_self _
  obtain ⟨hcC, hcA⟩ := Finset.mem_filter.mp hcmem
  refine ⟨(⟨m - π c, hcA⟩, ⟨π c, Finset.mem_image_of_mem π hcC⟩),
    sub_add_cancel _ _, ?_⟩
  intro q hq
  change q.1.val + q.2.val = m at hq
  obtain ⟨c', hc'C, hc'q⟩ := Finset.mem_image.mp q.2.property
  have hfirst : q.1.val = m - π c' := by
    rw [hc'q, ← hq, add_sub_cancel_right]
  have hc'A : m - π c' ∈ A i := hfirst ▸ q.1.property
  have hc'mem : c' ∈ C.filter (fun c => m - π c ∈ A i) :=
    Finset.mem_filter.mpr ⟨hc'C, hc'A⟩
  rw [hc] at hc'mem
  have hcc : c' = c := Finset.mem_singleton.mp hc'mem
  subst c'
  exact Prod.ext (Subtype.ext hfirst) (Subtype.ext hc'q.symm)

theorem main : H1 → H2 → OMA.R_Fuglede_FugledeConjecture_variants_dim_1_R1_H4_R1.H2 := by
  classical
  intro hsingle hlift N hN p hp Λ ℬ hΛ hℬ
  by_cases hnonempty : ℬ.Nonempty
  · obtain ⟨S₀, hS₀⟩ := hnonempty
    let r := Fintype.card {S // S ∈ ℬ}
    let e : {S // S ∈ ℬ} ≃ Fin r := Fintype.equivFin _
    have hr : 0 < r := Fintype.card_pos_iff.mpr ⟨⟨S₀, hS₀⟩⟩
    let A (i : Fin r) : Finset (ZMod N) := (e.symm i).val
    have hA (i : Fin r) := hℬ (A i) (e.symm i).property
    obtain ⟨M, hM, π, W, K, hsize, hsurj, hW, hcard, horth, hproj⟩ :=
      hlift N hN p r hp hr Λ A hΛ hA
    obtain ⟨C, hC⟩ := hsingle M hM W K hW hcard horth
    obtain ⟨hbound, hweighted⟩ := @weighted_tile_counts N M p r hN hM hp A π W C hsize hsurj
      (fun i => (hA i).1) hproj hC
    have hNpos : 0 < N := Nat.pos_of_ne_zero hN.out
    have hcount (i : Fin r) (m : ZMod N) :
        (C.filter fun c => m - π c ∈ A i).card = 1 := by
      have heq := radix_digits_unique (b := 2 * N) (by omega)
        (fun j : Fin r => (C.filter fun c => m - π c ∈ A j).card) (fun _ => 1)
        (fun j => (Finset.card_filter_le _ _).trans_lt (by omega : C.card < 2 * N))
        (fun _ => by omega) (by simpa only [mul_one] using hweighted m)
      exact congrFun heq i
    obtain ⟨B, hB⟩ := projected_complement A π C hcount
    refine ⟨B, ?_⟩
    intro S hS m
    have hi : A (e ⟨S, hS⟩) = S := congrArg Subtype.val (e.symm_apply_apply ⟨S, hS⟩)
    exact (congrArg (fun U : Finset (ZMod N) =>
      ∃! q : {k // k ∈ U} × {b // b ∈ B}, q.1.1 + q.2.1 = m) hi).mp
        (hB (e ⟨S, hS⟩) m)
  · exact ⟨∅, fun S hS _ => (hnonempty ⟨S, hS⟩).elim⟩

end OMA.R_Fuglede_FugledeConjecture_variants_dim_1_R1_H4_R1_H2_R1
