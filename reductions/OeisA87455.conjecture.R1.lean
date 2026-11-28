import FormalConjectures.OEIS.«87455»

-- Conditional research reduction, not a proof of Benford's law.
-- The arithmetic independence condition is a genuine unresolved obstacle.
-- Analytic route: Berger--Eshun, A characterization of Benford's Law in discrete-time
-- linear systems, Lemma 2.6 and Theorem 3.16.

namespace OMA.R_OeisA87455_conjecture_R1

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

-- Algebraic task: establish the exact cosine representation of this recurrence.
def H3 : Prop :=
  ∀ n : ℕ, (OeisA87455.a n : ℝ) =
    (Real.sqrt 3) ^ n * Real.cos ((n : ℝ) * Real.arctan (Real.sqrt 2))

theorem main : H1 → H2 → H3 → type_of% @OeisA87455.conjecture := by
  intro h₁ h₂ h₃
  exact h₂ (Real.sqrt 3) (Real.arctan (Real.sqrt 2)) OeisA87455.a
    (Real.sqrt_pos.2 (by norm_num)) h₁ h₃

end OMA.R_OeisA87455_conjecture_R1
