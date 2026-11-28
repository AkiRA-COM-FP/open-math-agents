import OMAReductions.R_Erdos651_erdos_651_R1_H1_R1_H1_R1
import Mathlib

/-! Exact generic perturbation of a strictly containing affine orthant. -/

/- Small positive changes of basis give nested negative orthants. -/

namespace OMA.Erdos651OrthantMatrix

open Matrix

/-- The row estimate for a matrix whose entries are uniformly close to the identity. -/
theorem mulVec_sub_bound (M : Matrix (Fin 3) (Fin 3) ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hM : ∀ i j, |M i j - (if i = j then 1 else 0)| ≤ ε)
    (x : Fin 3 → ℝ) :
    ‖M.mulVec x - x‖ ≤ 3 * ε * ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (x := M.mulVec x - x) (by positivity)).2
  intro i
  simp only [Pi.sub_apply, Real.norm_eq_abs]
  have hsum : (M.mulVec x) i - x i =
      ∑ j : Fin 3, (M i j - (if i = j then 1 else 0)) * x j := by
    simp [Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib, ite_mul]
  rw [hsum]
  calc
    _ ≤ ∑ j : Fin 3, |(M i j - (if i = j then 1 else 0)) * x j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin 3, ε * ‖x‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul (hM i j) (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x j)
        (abs_nonneg _) hε
    _ = _ := by simp [mul_assoc]

/-- The inverse of the small perturbation has a useful uniform error bound. -/
theorem lower_norm_mulVec (M : Matrix (Fin 3) (Fin 3) ℝ) {ε : ℝ}
    (hε : 0 ≤ ε) (hsmall : 3 * ε ≤ 1 / 2)
    (hM : ∀ i j, |M i j - (if i = j then 1 else 0)| ≤ ε)
    (x : Fin 3 → ℝ) :
    ‖x‖ ≤ 2 * ‖M.mulVec x‖ := by
  have htri : ‖x‖ ≤ ‖M.mulVec x‖ + ‖M.mulVec x - x‖ := by
    simpa only [sub_sub_cancel] using (norm_sub_le (M.mulVec x) (M.mulVec x - x))
  have herr := mulVec_sub_bound M hε hM x
  have hsc := mul_le_mul_of_nonneg_right hsmall (norm_nonneg x)
  linarith

theorem injective_mulVec (M : Matrix (Fin 3) (Fin 3) ℝ) {ε : ℝ}
    (hε : 0 ≤ ε) (hsmall : 3 * ε ≤ 1 / 2)
    (hM : ∀ i j, |M i j - (if i = j then 1 else 0)| ≤ ε) :
    Function.Injective (M.mulVecLin : (Fin 3 → ℝ) → (Fin 3 → ℝ)) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  have hz : M.mulVec x = 0 := hx
  have hn := lower_norm_mulVec M hε hsmall hM x
  rw [hz, norm_zero, mul_zero] at hn
  exact norm_le_zero_iff.mp hn

/-- A nonnegative basis carries the new closed negative orthant into the old. -/
theorem negative_of_mulVec (M : Matrix (Fin 3) (Fin 3) ℝ)
    (hM : ∀ i j, 0 ≤ M i j) {x : Fin 3 → ℝ} (hx : ∀ j, x j ≤ 0) :
    ∀ i, (M.mulVec x) i ≤ 0 := by
  intro i
  change (∑ j : Fin 3, M i j * x j) ≤ 0
  exact Finset.sum_nonpos fun j _ => mul_nonpos_of_nonneg_of_nonpos (hM i j) (hx j)

/-- A finite strictly negative family stays negative after applying the inverse
of a sufficiently small change of basis. -/
theorem inverse_coordinates_stay_negative (M : Matrix (Fin 3) (Fin 3) ℝ) {ε δ B : ℝ}
    (hε : 0 ≤ ε) (hsmall : 3 * ε ≤ 1 / 2)
    (hM : ∀ i j, |M i j - (if i = j then 1 else 0)| ≤ ε)
    (hmargin : 6 * ε * B ≤ δ)
    (x y : Fin 3 → ℝ) (hxy : M.mulVec y = x) (hxB : ‖x‖ ≤ B)
    (hx : ∀ i, x i ≤ -δ) :
    ∀ i, y i ≤ 0 := by
  have hbound := lower_norm_mulVec M hε hsmall hM y
  rw [hxy] at hbound
  have herr := mulVec_sub_bound M hε hM y
  rw [hxy] at herr
  have hE : ‖x - y‖ ≤ δ := by
    calc
      _ ≤ 3 * ε * ‖y‖ := herr
      _ ≤ 3 * ε * (2 * B) := mul_le_mul_of_nonneg_left
        (hbound.trans (by linarith : 2 * ‖x‖ ≤ 2 * B)) (by positivity)
      _ ≤ δ := by linarith only [hmargin]
  intro i
  have hdelta : |x i - y i| ≤ δ := by
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using
      (norm_le_pi_norm (x - y) i |>.trans hE)
  linarith [(abs_le.mp hdelta).1, hx i]

theorem finite_margin {V : Type*} (U : Finset V) (p : V → Fin 3 → ℝ)
    (hU : ∀ x ∈ U, ∀ j, p x j < 0) :
    ∃ δ B : ℝ, 0 < δ ∧ 0 < B ∧
      (∀ x ∈ U, ∀ j, p x j ≤ -δ) ∧ (∀ x ∈ U, ‖p x‖ ≤ B) := by
  classical
  let B := 1 + ∑ x ∈ U, ‖p x‖
  have hB : 0 < B := by
    dsimp [B]
    have hs := Finset.sum_nonneg (s := U) (fun x _ => norm_nonneg (p x))
    linarith
  have hBS (x : V) (hx : x ∈ U) : ‖p x‖ ≤ B := by
    have hl := Finset.single_le_sum (s := U) (f := fun x => ‖p x‖)
      (fun x _ => norm_nonneg (p x)) hx
    dsimp [B]
    linarith
  by_cases hne : U.Nonempty
  · have hUp : (U.product (Finset.univ : Finset (Fin 3))).Nonempty :=
      hne.product ⟨0, Finset.mem_univ 0⟩
    obtain ⟨a, ha, hmin⟩ := Finset.exists_min_image _ (fun a : V × Fin 3 => -p a.1 a.2) hUp
    have hp : 0 < -p a.1 a.2 := neg_pos.mpr (hU a.1 (Finset.mem_product.mp ha).1 a.2)
    refine ⟨-p a.1 a.2, B, hp, hB, ?_, hBS⟩
    intro x hx j
    have hl := hmin (x, j) (Finset.mem_product.mpr ⟨hx, Finset.mem_univ j⟩)
    linarith
  · refine ⟨1, B, by norm_num, hB, ?_, hBS⟩
    intro x hx
    exact (hne ⟨x, hx⟩).elim

theorem exists_perturbation_radius {δ B : ℝ} (hδ : 0 < δ) (hB : 0 < B) :
    ∃ ε : ℝ, 0 < ε ∧ 3 * ε ≤ 1 / 2 ∧ 6 * ε * B ≤ δ := by
  let ε := min (1 / 12 : ℝ) (δ / (12 * B))
  have hp : 0 < ε := lt_min (by norm_num) (by positivity)
  have h1 : ε ≤ 1 / 12 := min_le_left _ _
  have h2 : ε ≤ δ / (12 * B) := min_le_right _ _
  have haux := (le_div_iff₀ (show 0 < 12 * B by positivity)).mp h2
  exact ⟨ε, hp, by linarith, by linarith⟩

end OMA.Erdos651OrthantMatrix

namespace OMA.Erdos651GenericProjection

open Filter
open scoped Topology

/-- Generic simultaneous directions can be chosen in any nonempty open set of frames. -/
theorem exists_frame_outside {E ι ν : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Finite ι]
    (S : ι → Submodule ℝ E) (hS : ∀ i, S i ≠ ⊤)
    (O : Set (ν → E)) (hO : IsOpen O) (hne : O.Nonempty) :
    ∃ b ∈ O, ∀ j i, b j ∉ S i := by
  have hd (i : ι) : Dense ((S i : Set E)ᶜ) := by
    rw [← interior_eq_empty_iff_dense_compl]
    by_contra hn
    have : Filter.NeBot (𝓝[{x : ℝ | IsUnit x}] 0) := by
      have hset : ({x : ℝ | IsUnit x}) = ({0} : Set ℝ)ᶜ := by
        ext x
        simp [isUnit_iff_ne_zero]
      rw [hset]
      infer_instance
    exact hS i ((S i).eq_top_of_nonempty_interior' (Set.nonempty_iff_ne_empty.mpr hn))
  let T : Set E := ⋂ i, (S i : Set E)ᶜ
  have hT : Dense T := by
    rw [show T = ⋂₀ Set.range (fun i => (S i : Set E)ᶜ) from (Set.sInter_range _).symm]
    apply (Set.finite_range _).dense_sInter
    · rintro _ ⟨i,rfl⟩
      exact (S i).closed_of_finiteDimensional.isOpen_compl
    · rintro _ ⟨i,rfl⟩
      exact hd i
  have hD : Dense (Set.pi (Set.univ : Set ν) (fun _ => T)) :=
    dense_pi Set.univ (fun _ _ => hT)
  obtain ⟨b,hbO,hb⟩ := hD.inter_open_nonempty O hO hne
  exact ⟨b,hbO,fun j i => Set.mem_iInter.mp (hb j (Set.mem_univ j)) i⟩

/-- The directions spanned by at most three points form a proper subspace in dimension three. -/
theorem vectorSpan_ne_top (Z : Finset (Fin 3 → ℝ)) (hz : Z.card ≤ 3) :
    vectorSpan ℝ (Z : Set (Fin 3 → ℝ)) ≠ ⊤ := by
  classical
  rcases Z.eq_empty_or_nonempty with rfl | hne
  · simp
  let f : Z → (Fin 3 → ℝ) := Subtype.val
  have : Nonempty Z := ⟨⟨hne.choose,hne.choose_spec⟩⟩
  have hr : Set.range f = (Z : Set (Fin 3 → ℝ)) := Subtype.range_coe_subtype
  have hm := finrank_vectorSpan_range_add_one_le ℝ f
  rw [hr, Fintype.card_coe] at hm
  intro htop
  rw [htop, finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hm
  omega

/-- Choose all columns generically for every small subset of a finite planar-projection input. -/
theorem exists_frame_no_small_span {ν : Type*} (Y : Finset (Fin 3 → ℝ))
    (O : Set (ν → (Fin 3 → ℝ))) (hO : IsOpen O) (hne : O.Nonempty) :
    ∃ b ∈ O, ∀ j (Z : Finset (Fin 3 → ℝ)), Z ⊆ Y → Z.card ≤ 3 →
      b j ∉ vectorSpan ℝ (Z : Set (Fin 3 → ℝ)) := by
  classical
  let F := Y.powerset.filter (fun Z => Z.card ≤ 3)
  let V (i : F) := vectorSpan ℝ (i.val : Set (Fin 3 → ℝ))
  obtain ⟨b,hb,hgen⟩ := exists_frame_outside V
    (fun i => vectorSpan_ne_top i.val (Finset.mem_filter.mp i.property).2) O hO hne
  refine ⟨b,hb,fun j Z hZY hZ => ?_⟩
  exact hgen j ⟨Z,Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hZY,hZ⟩⟩

/-- The generic columns can be chosen with positive coordinates arbitrarily
close to the identity columns. -/
theorem exists_positive_columns_close (Y : Finset (Fin 3 → ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ b : Fin 3 → Fin 3 → ℝ, (∀ j i, 0 < b j i) ∧
      (∀ j i, |b j i - (if i = j then 1 else 0)| < ε) ∧
      ∀ j (Z : Finset (Fin 3 → ℝ)), Z ⊆ Y → Z.card ≤ 3 →
        b j ∉ vectorSpan ℝ (Z : Set (Fin 3 → ℝ)) := by
  let d (j i : Fin 3) : ℝ := if i = j then 1 else 0
  let O : Set (Fin 3 → Fin 3 → ℝ) := ⋂ j, ⋂ i,
    {b | 0 < b j i} ∩ {b | |b j i - d j i| < ε}
  have hO : IsOpen O := by
    apply isOpen_iInter_of_finite
    intro j
    apply isOpen_iInter_of_finite
    intro i
    have hC : Continuous (fun b : Fin 3 → Fin 3 → ℝ => b j i) :=
      (continuous_apply i).comp (continuous_apply j)
    exact (isOpen_lt continuous_const hC).inter (isOpen_lt (hC.sub continuous_const).abs continuous_const)
  have hMem (b : Fin 3 → Fin 3 → ℝ) : b ∈ O ↔ ∀ j i, 0 < b j i ∧ |b j i - d j i| < ε := by
    simp [O]
  have hne : O.Nonempty := by
    refine ⟨fun j i => d j i + ε / 2, (hMem _).mpr fun j i => ⟨?_, ?_⟩⟩
    · have hd : 0 ≤ d j i := by simp only [d]; split <;> norm_num
      linarith
    · have he : d j i + ε / 2 - d j i = ε / 2 := by ring
      rw [he, abs_of_pos (by positivity)]
      linarith
  obtain ⟨b, hb, hg⟩ := exists_frame_no_small_span Y O hO hne
  exact ⟨b,fun j i => ((hMem b).mp hb j i).1,fun j i => ((hMem b).mp hb j i).2,hg⟩

/-- An affine map preserves an affinely independent family when its linear kernel
meets the span of that family's differences only at zero. -/
theorem independent_map_of_disjoint {ι E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] {p : ι → E} (hp : AffineIndependent ℝ p)
    (f : E →ᵃ[ℝ] F) (hf : Disjoint (vectorSpan ℝ (Set.range p)) (LinearMap.ker f.linear)) :
    AffineIndependent ℝ (f ∘ p) := by
  rcases isEmpty_or_nonempty ι with h | h
  · exact affineIndependent_of_subsingleton ℝ (f ∘ p)
  obtain ⟨i⟩ := h
  rw [vectorSpan_range_eq_span_range_vsub_right_ne ℝ p i] at hf
  rw [affineIndependent_iff_linearIndependent_vsub ℝ p i] at hp
  simp_rw [affineIndependent_iff_linearIndependent_vsub ℝ (f ∘ p) i, Function.comp_apply,
    ← f.linearMap_vsub]
  exact hp.map hf

/-- Delete coordinate `j` from a three-dimensional Euclidean vector. -/
def drop (j : Fin 3) : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun x k := x (j.succAbove k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- In old coordinates the kernel of the projected coordinate map is the line
of the deleted inverse coordinate column. -/
theorem ker_drop_comp_le (B : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ)) (j : Fin 3) :
    LinearMap.ker ((drop j).comp B.symm.toLinearMap) ≤
      ℝ ∙ (B (Pi.single j 1)) := by
  intro x hx
  let u := B.symm x
  have hu (i : Fin 2) : u (j.succAbove i) = 0 :=
    congrFun (LinearMap.mem_ker.mp hx) i
  have hsingle : u = u j • (Pi.single j 1 : Fin 3 → ℝ) := by
    ext i
    change u i = u j * (Pi.single j 1 : Fin 3 → ℝ) i
    by_cases hi : i = j
    · subst i
      simp
    · obtain ⟨k,rfl⟩ := Fin.exists_succAbove_eq hi
      simp [hu, Fin.succAbove_ne]
  apply Submodule.mem_span_singleton.mpr
  use u j
  rw [← map_smul, ← hsingle, LinearEquiv.apply_symm_apply]

/-- Each projected subset remains affinely independent as soon as the
corresponding inverse coordinate column avoids its difference span. -/
theorem projection_independent {ι : Type*} (f : ι → Fin 3 → ℝ)
    (hf : AffineIndependent ℝ f) (B : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ)) (j : Fin 3)
    (hgeneric : B (Pi.single j 1) ∉ vectorSpan ℝ (Set.range f)) :
    AffineIndependent ℝ (fun x => fun k : Fin 2 => B.symm (f x) (j.succAbove k)) := by
  let F := ((drop j).comp B.symm.toLinearMap).toAffineMap
  apply independent_map_of_disjoint hf F
  have hker : LinearMap.ker F.linear ≤ ℝ ∙ (B (Pi.single j 1)) := ker_drop_comp_le B j
  apply Disjoint.mono_right hker
  exact Submodule.disjoint_span_singleton_of_notMem hgeneric

end OMA.Erdos651GenericProjection

/- Combine generic frame directions with a quantitative orthant shrinkage. -/

open scoped EuclideanGeometry

namespace OMA.Erdos651OrthantMatrix

theorem perturbation
    (Y U : Finset (ℝ^3)) (e : (ℝ^3) ≃ᵃ[ℝ] (ℝ^3))
    (hY : Erdos651.IsInGeneralPosition Y)
    (hU : ∀ x ∈ U, ∀ s : Fin 3, e x s < 0) :
    ∃ f : (ℝ^3) ≃ᵃ[ℝ] (ℝ^3),
      (∀ x ∈ U, ∀ s : Fin 3, f x s ≤ 0) ∧
      {x | ∀ s : Fin 3, f x s ≤ 0} ⊆ {x | ∀ s : Fin 3, e x s ≤ 0} ∧
      ∀ (j : Fin 3) (Z : Finset (ℝ^3)), Z ⊆ Y → Z.card ≤ 3 →
        AffineIndependent ℝ
          (fun z : ↥(Z : Set (ℝ^3)) => fun s : Fin 2 => f z (j.succAbove s)) := by
  classical
  let c : (ℝ^3) ≃ₗ[ℝ] (Fin 3 → ℝ) := (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin 3)).toLinearEquiv
  let p := e.trans c.toAffineEquiv
  have hp (x : ℝ^3) (i : Fin 3) : p x i = e x i := rfl
  obtain ⟨δ, B, hδ, hB, hmargin, hnorm⟩ := finite_margin U p (by simpa only [hp] using hU)
  obtain ⟨ε, hε, hs, hr⟩ := exists_perturbation_radius hδ hB
  obtain ⟨g, hgPos, hgNear, hgen⟩ :=
    OMA.Erdos651GenericProjection.exists_positive_columns_close (Y.image p) hε
  let M : Matrix (Fin 3) (Fin 3) ℝ := fun i j => g j i
  have hM (i j : Fin 3) : |M i j - (if i = j then 1 else 0)| ≤ ε := (hgNear j i).le
  have hMnonneg (i j : Fin 3) : 0 ≤ M i j := (hgPos j i).le
  let A : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ) :=
    LinearEquiv.ofInjectiveEndo M.mulVecLin (injective_mulVec M hε.le hs hM)
  have hA (v : Fin 3 → ℝ) : M.mulVec (A.symm v) = v := A.apply_symm_apply v
  have hAcol (j : Fin 3) : A (Pi.single j 1) = g j := by
    ext i
    change ∑ s : Fin 3, M i s * (Pi.single j (1 : ℝ) : Fin 3 → ℝ) s = g j i
    simp [M, Pi.single_apply, mul_ite]
  let f := p.trans (A.symm.trans c.symm).toAffineEquiv
  have hf (x : ℝ^3) (i : Fin 3) : f x i = A.symm (p x) i := rfl
  refine ⟨f, ?_, ?_, ?_⟩
  · intro x hx i
    rw [hf]
    exact inverse_coordinates_stay_negative M hε.le hs hM hr
      (p x) (A.symm (p x)) (hA (p x)) (hnorm x hx) (hmargin x hx) i
  · intro x hx i
    rw [← hp, ← hA (p x)]
    exact negative_of_mulVec M hMnonneg (fun j => by simpa only [hf] using hx j) i
  · intro j Z hZY hZ
    have hsmall : (Z.image p).card ≤ 3 := Finset.card_image_le.trans hZ
    have hsub : Z.image p ⊆ Y.image p := Finset.image_mono p hZY
    have hdir := hgen j (Z.image p) hsub hsmall
    have hrange : Set.range (fun z : ↥(Z : Set (ℝ^3)) => p z) =
        ((Z.image p : Finset (Fin 3 → ℝ)) : Set (Fin 3 → ℝ)) := by
      ext v
      simp only [Set.mem_range, Finset.mem_coe, Finset.mem_image]
      exact ⟨fun ⟨z, hz⟩ => ⟨z, z.property, hz⟩, fun ⟨z, hz, he⟩ => ⟨⟨z, hz⟩, he⟩⟩
    have hdir' : A (Pi.single j 1) ∉ vectorSpan ℝ
        (Set.range (fun z : ↥(Z : Set (ℝ^3)) => p z)) := by simpa only [hAcol, hrange] using hdir
    have hind : AffineIndependent ℝ (fun z : ↥(Z : Set (ℝ^3)) => p z) :=
      p.affineIndependent_iff.mpr (hY Z hZY (by omega))
    change AffineIndependent ℝ
      (fun z : ↥(Z : Set (ℝ^3)) => fun k : Fin 2 => A.symm (p z) (j.succAbove k))
    exact OMA.Erdos651GenericProjection.projection_independent _ hind A j hdir'

end OMA.Erdos651OrthantMatrix

theorem OMA.solution : OMA.R_Erdos651_erdos_651_R1_H1_R1_H1_R1.H3 :=
  OMA.Erdos651OrthantMatrix.perturbation
