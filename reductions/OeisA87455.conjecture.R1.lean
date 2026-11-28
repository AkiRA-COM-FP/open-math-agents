import FormalConjectures.OEIS.«87455»

-- Conditional research reduction, not a proof of Benford's law.
-- The arithmetic independence condition is a genuine unresolved obstacle.
-- Analytic route: Berger--Eshun, A characterization of Benford's Law in discrete-time
-- linear systems, Lemma 2.6 and Theorem 3.16.

namespace OMA.R_OeisA87455_conjecture_R1

open OeisA87455

-- Arithmetic task: a concrete three-number rational independence statement.
def H1 : Prop :=
  ∀ q₀ q₁ q₂ : ℚ,
    (q₀ : ℝ) + (q₁ : ℝ) * Real.logb 10 (Real.sqrt 3) +
      (q₂ : ℝ) * (Real.arctan (Real.sqrt 2) / Real.pi) = 0 →
      q₀ = 0 ∧ q₁ = 0 ∧ q₂ = 0

-- Analytic task: equidistribution on the two-torus implies Benford behavior for
-- integer-valued exponentially scaled cosines. The criterion is reusable for any radius/angle.
def H2 : Prop :=
  ∀ (r θ : ℝ) (s : ℕ → ℤ), 0 < r →
    (∀ q₀ q₁ q₂ : ℚ,
      (q₀ : ℝ) + (q₁ : ℝ) * Real.logb 10 r +
        (q₂ : ℝ) * (θ / Real.pi) = 0 →
        q₀ = 0 ∧ q₁ = 0 ∧ q₂ = 0) →
    (∀ n : ℕ, (s n : ℝ) = r ^ n * Real.cos ((n : ℝ) * θ)) →
    OeisA87455.SatisfiesBenford s

-- Exact algebraic representation, discharged here rather than left as an open step.
lemma scaled_cos_add_two (r θ : ℝ) (hr : r * Real.cos θ = 1) (hr2 : r ^ 2 = 3)
    (n : ℕ) :
    r ^ (n + 2) * Real.cos (((n + 2 : ℕ) : ℝ) * θ) =
      2 * r ^ (n + 1) * Real.cos (((n + 1 : ℕ) : ℝ) * θ) -
        3 * r ^ n * Real.cos ((n : ℝ) * θ) := by
  have hc := Real.cos_add_cos (x := (((n + 2 : ℕ) : ℝ) * θ)) (y := (n : ℝ) * θ)
  have hmean : ((((n + 2 : ℕ) : ℝ) * θ + (n : ℝ) * θ) / 2) =
      (((n + 1 : ℕ) : ℝ) * θ) := by
    simp only [Nat.cast_add, Nat.cast_ofNat]
    ring
  have hdiff : ((((n + 2 : ℕ) : ℝ) * θ - (n : ℝ) * θ) / 2) = θ := by
    simp only [Nat.cast_add, Nat.cast_ofNat]
    ring
  rw [hmean, hdiff] at hc
  calc
    _ = r ^ (n + 2) *
          (Real.cos (((n + 2 : ℕ) : ℝ) * θ) + Real.cos ((n : ℝ) * θ)) -
        r ^ (n + 2) * Real.cos ((n : ℝ) * θ) := by ring
    _ = r ^ (n + 2) *
          (2 * Real.cos (((n + 1 : ℕ) : ℝ) * θ) * Real.cos θ) -
        r ^ (n + 2) * Real.cos ((n : ℝ) * θ) := by rw [hc]
    _ = 2 * r ^ (n + 1) * Real.cos (((n + 1 : ℕ) : ℝ) * θ) * (r * Real.cos θ) -
        r ^ n * r ^ 2 * Real.cos ((n : ℝ) * θ) := by
      simp only [pow_add, pow_one]
      ring
    _ = 2 * r ^ (n + 1) * Real.cos (((n + 1 : ℕ) : ℝ) * θ) -
        3 * r ^ n * Real.cos ((n : ℝ) * θ) := by rw [hr, hr2]; ring

lemma a_cosine (n : ℕ) :
    (a n : ℝ) =
      (Real.sqrt 3) ^ n * Real.cos ((n : ℝ) * Real.arctan (Real.sqrt 2)) := by
  have hs2 : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs3 : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hr : Real.sqrt 3 * Real.cos (Real.arctan (Real.sqrt 2)) = 1 := by
    rw [Real.cos_arctan, hs2]
    simp only [show (1 : ℝ) + 2 = 3 by norm_num, one_div]
    exact mul_inv_cancel₀ ((Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3)).ne')
  induction n using Nat.twoStepInduction with
  | zero => simp [a]
  | one => simpa [a] using hr.symm
  | more n ih0 ih1 =>
      change (((2 : ℤ) * a (n + 1) - 3 * a n : ℤ) : ℝ) = _
      simp only [Int.cast_sub, Int.cast_mul, Int.cast_ofNat]
      rw [ih0, ih1]
      simpa [mul_assoc] using
        (scaled_cos_add_two (Real.sqrt 3) (Real.arctan (Real.sqrt 2)) hr hs3 n).symm

theorem main : H1 → H2 → type_of% @OeisA87455.conjecture := by
  intro h₁ h₂
  exact h₂ (Real.sqrt 3) (Real.arctan (Real.sqrt 2)) OeisA87455.a
    (Real.sqrt_pos.2 (by norm_num)) h₁ a_cosine

end OMA.R_OeisA87455_conjecture_R1
