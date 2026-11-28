import OMAStatements.S_oeis_a390007
import Mathlib.Tactic.Linarith

-- Problem: A390007 (Rodrigo): for every integer n ≥ 3, the square of side n has a unique minimum-defect
--   set of three distinct rectangular tiles, except n = 4.
-- First proof: @alan-phobos-claude. Shorter version: the six residue cases are handled by one argument inside `key`.
-- Proof: the optimum is always the tee with a = ⌊(n+1)/3⌋ and b = ⌊(n−1)/2⌋. Its defect D is 8q, 5q+1,
--   8q+2, 4q+2, 8q+6 or 5q+4 for n = 6q + r, r = 0, …, 5. A tee (a, b) with defect at most D has
--   (n−2b)(n−a) ≤ D, n·a − b(n−a) ≤ D and (n−b)(n−a) − n·a ≤ D. If n − 2b is larger than at the
--   optimum (so ≥ 3, or ≥ 4 for even n), the first two force 2n² − nD − 2D ≤ 0 (resp. 8n² − 3nD − 8D ≤ 0),
--   which is false. Otherwise b is the optimal one, and the last two pin a down. Strips cost
--   n(z − x) ≥ 2n > D. At n = 4 the tees (1, 1) and (2, 1) tie with defect 6.

open OMA.S_oeis_a390007

namespace A390007

lemma spread_le {x l h D : ℤ} (hs : spread x l h ≤ D) : h - l ≤ D ∧ x - l ≤ D ∧ h - x ≤ D := by
  unfold spread at hs
  exact ⟨le_trans (le_max_left _ _) hs, le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hs,
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hs⟩

/-- The optimal set: the tee with `a = ⌊(n+1)/3⌋` and `b = ⌊(n-1)/2⌋`. -/
def starTile (n : ℤ) : TileSet := .tee ((n + 1) / 3) ((n - 1) / 2)

lemma key (n : ℤ) (hn : 3 ≤ n) : defect n (starTile n) < 2 * n ∧
    ∀ a b, valid n (.tee a b) → n ≠ 4 → defect n (.tee a b) ≤ defect n (starTile n) →
      a = (n + 1) / 3 ∧ b = (n - 1) / 2 := by
  simp only [defect, starTile, valid]
  generalize hA : (n + 1) / 3 = A
  generalize hB : (n - 1) / 2 = B
  obtain ⟨q, D, c, k, h⟩ : ∃ q D c k : ℤ,
      n = 6*q ∧ A = 2*q ∧ B = 3*q-1 ∧ D = 8*q ∧ c = 4 ∧ k = 1 ∨
      n = 6*q+1 ∧ A = 2*q ∧ B = 3*q ∧ D = 5*q+1 ∧ c = 3 ∧ k = 1 ∨
      n = 6*q+2 ∧ A = 2*q+1 ∧ B = 3*q ∧ D = 8*q+2 ∧ c = 4 ∧ k = 1 ∨
      n = 6*q+3 ∧ A = 2*q+1 ∧ B = 3*q+1 ∧ D = 4*q+2 ∧ c = 3 ∧ k = 0 ∨
      n = 6*q+4 ∧ A = 2*q+1 ∧ B = 3*q+1 ∧ D = 8*q+6 ∧ c = 4 ∧ k = 1 ∨
      n = 6*q+5 ∧ A = 2*q+2 ∧ B = 3*q+2 ∧ D = 5*q+4 ∧ c = 3 ∧ k = 0 := by
    rcases (by omega : n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 2 ∨ n % 6 = 3 ∨ n % 6 = 4 ∨ n % 6 = 5) with
      r | r | r | r | r | r <;> [refine ⟨n/6, 8*(n/6), 4, 1, ?_⟩; refine ⟨n/6, 5*(n/6)+1, 3, 1, ?_⟩; refine ⟨n/6, 8*(n/6)+2, 4, 1, ?_⟩; refine ⟨n/6, 4*(n/6)+2, 3, 0, ?_⟩; refine ⟨n/6, 8*(n/6)+6, 4, 1, ?_⟩; refine ⟨n/6, 5*(n/6)+4, 3, 0, ?_⟩] <;>
      repeat (first | (left; omega) | right)
    omega
  clear hA hB
  have hD : spread (n * A) (B * (n - A)) ((n - B) * (n - A)) ≤ D := by
    refine max_le ?_ (max_le ?_ ?_) <;> casesm* _ ∨ _, _ ∧ _ <;> subst_vars <;> nlinarith
  refine ⟨by omega, fun a b ⟨ha, ha', hb, hb'⟩ h4 hd => ?_⟩
  obtain ⟨e1, e2, e3⟩ := spread_le (hd.trans hD)
  have hq : k ≤ q := by omega
  have hbB : b = B := by
    by_contra hne
    have hg : (0:ℤ) ≤ n - 2*b - c := by omega
    have hm : (0:ℤ) ≤ n - a := by omega
    have h3 : c * (n - a) ≤ D := by nlinarith [mul_nonneg hg hm]
    have p := mul_nonneg (show (0:ℤ) ≤ n by omega) (sub_nonneg.2 h3)
    have p' := mul_nonneg hg hm
    casesm* _ ∨ _, _ ∧ _ <;> subst_vars <;> nlinarith [p, p', mul_self_nonneg q]
  refine ⟨le_antisymm (not_lt.1 fun h' => ?_) (not_lt.1 fun h' => ?_), hbB⟩
  · have p := mul_nonneg (show (0:ℤ) ≤ a - (A + 1) by omega) (show (0:ℤ) ≤ q by omega)
    casesm* _ ∨ _, _ ∧ _ <;> subst_vars <;> nlinarith [p]
  · have p := mul_nonneg (show (0:ℤ) ≤ A - 1 - a by omega) (show (0:ℤ) ≤ q by omega)
    casesm* _ ∨ _, _ ∧ _ <;> subst_vars <;> nlinarith [p]

/-- At `n = 4` the tees `(1, 1)` and `(2, 1)` are both optimal (defect 6). -/
lemma four_optimal (a : ℤ) (ha : a = 1 ∨ a = 2) : optimal 4 (.tee a 1) := by
  refine ⟨by simp only [valid]; omega, fun t ht => ?_⟩
  cases t with
  | strips x y z => simp only [valid] at ht; omega
  | tee c d =>
    simp only [valid] at ht
    obtain rfl : d = 1 := by omega
    rcases ha with rfl | rfl <;> rcases (by omega : c = 1 ∨ c = 2 ∨ c = 3) with rfl | rfl | rfl <;> decide

end A390007

open A390007 in
theorem OMA.solution : type_of% @OMA.S_oeis_a390007.main := by
  intro n hn
  obtain ⟨hlt, huniq⟩ := key n hn
  have hsv : valid n (starTile n) := by simp only [starTile, valid]; omega
  have hbest : n ≠ 4 → ∀ t, valid n t → t ≠ starTile n → defect n (starTile n) < defect n t := by
    intro h4 t ht hne
    cases t with
    | strips x y z =>
      simp only [valid] at ht
      rw [show defect n (.strips x y z) = n * (z - x) from rfl]
      nlinarith [mul_le_mul_of_nonneg_left (show (2:ℤ) ≤ z - x by omega) (show (0:ℤ) ≤ n by omega)]
    | tee a b =>
      by_contra hle
      obtain ⟨rfl, rfl⟩ := huniq a b ht h4 (not_lt.1 hle)
      exact hne rfl
  constructor
  · rintro ⟨s, -, hu⟩ rfl
    have h1 := hu _ (four_optimal 1 (Or.inl rfl))
    have h2 := hu _ (four_optimal 2 (Or.inr rfl))
    rw [← h2] at h1
    cases h1
  · intro h4
    refine ⟨starTile n, ⟨hsv, fun t ht => ?_⟩, fun s hs => ?_⟩
    · by_cases he : t = starTile n
      · rw [he]
      · exact (hbest h4 t ht he).le
    · by_contra hne
      exact absurd (hs.2 _ hsv) (not_le.2 (hbest h4 s hs.1 hne))
