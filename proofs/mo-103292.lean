import OMAStatements.S_mo_103292
import Mathlib

-- Problem: mo-103292, in some dimension n >= 2 there are a closed convex K with nonempty
-- interior and a map F that is strongly pseudomonotone but not strongly monotone on K.
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- Take n = 2, K the whole plane and F(x) = phi(x) x with phi(x) = 1 if |x| <= 1 and 1/4
-- otherwise. If <F x, y - x> >= 0 then <x, y - x> >= 0, so <y, y - x> >= |y - x|^2 and
-- <F y, y - x> >= (1/4) |y - x|^2: F is strongly pseudomonotone. But for a unit vector e,
-- <F(2e) - F(e), 2e - e> = <e/2 - e, e> = -1/2 < 0, so F is not even monotone.

open scoped RealInnerProductSpace

namespace MO103292

noncomputable def φ (x : EuclideanSpace ℝ (Fin 2)) : ℝ := if ‖x‖ ≤ 1 then 1 else 1 / 4

theorem φ_ge (x : EuclideanSpace ℝ (Fin 2)) : 1 / 4 ≤ φ x := by
  unfold φ
  split_ifs <;> norm_num

theorem φ_pos (x : EuclideanSpace ℝ (Fin 2)) : 0 < φ x := by
  have h := φ_ge x
  linarith

end MO103292

theorem OMA.solution : type_of% @OMA.S_mo_103292.main := by
  refine ⟨2, le_rfl, Set.univ, isClosed_univ, convex_univ, by simp,
    fun x => MO103292.φ x • x, ?_, ?_⟩
  · unfold OMA.S_mo_103292.StronglyPseudomonotoneOn
    refine ⟨1 / 4, by norm_num, ?_⟩
    intro x _ y _ hxy
    beta_reduce at hxy ⊢
    rw [ge_iff_le, real_inner_smul_left] at hxy
    have h1 : 0 ≤ ⟪x, y - x⟫ := by
      by_contra hneg
      have h0 := mul_neg_of_pos_of_neg (MO103292.φ_pos x) (not_le.mp hneg)
      linarith
    have h2 : ⟪y, y - x⟫ = ⟪x, y - x⟫ + ‖y - x‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, ← inner_add_left]
      congr 1
      abel
    rw [ge_iff_le, real_inner_smul_left, h2]
    have h3 := MO103292.φ_ge y
    nlinarith [mul_nonneg (sub_nonneg.mpr h3) (add_nonneg h1 (sq_nonneg ‖y - x‖))]
  · intro hSM
    unfold OMA.S_mo_103292.StronglyMonotoneOn at hSM
    obtain ⟨γ, hγ, hmono⟩ := hSM
    obtain ⟨e, he⟩ : ∃ e : EuclideanSpace ℝ (Fin 2), ‖e‖ = 1 :=
      ⟨EuclideanSpace.single 0 1, by simp⟩
    have h := hmono e (Set.mem_univ _) ((2 : ℝ) • e) (Set.mem_univ _)
    beta_reduce at h
    have hφe : MO103292.φ e = 1 := by
      unfold MO103292.φ
      rw [if_pos he.le]
    have hn2 : ‖(2 : ℝ) • e‖ = 2 := by
      rw [norm_smul, he]
      norm_num
    have hφ2 : MO103292.φ ((2 : ℝ) • e) = 1 / 4 := by
      unfold MO103292.φ
      rw [if_neg (by rw [hn2]; norm_num)]
    have e1 : (1 / 4 : ℝ) • ((2 : ℝ) • e) - (1 : ℝ) • e = (-(1 / 2) : ℝ) • e := by
      rw [smul_smul, ← sub_smul]
      norm_num
    have e2 : (2 : ℝ) • e - e = e := by
      rw [two_smul]
      abel
    rw [hφe, hφ2, e1, e2, real_inner_smul_left, real_inner_self_eq_norm_sq, he] at h
    norm_num at h
    linarith
