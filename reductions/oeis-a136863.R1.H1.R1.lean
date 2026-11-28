import OMAReductions.R_oeis_a136863_R1

-- Reduction oeis-a136863.R1.H1.R1 of step oeis-a136863.R1.H1
-- Credit: @Ciphore

namespace OMA.R_oeis_a136863_R1_H1_R1

open OMA.S_oeis_a136863

/-- The terminal-digit `1` carry core. -/
def H1 : Prop := ∀ d v : ℕ, 1 ≤ d → d ≤ 2 → 10 ≤ v → v % 10 = 1 →
  UsesDigits v →
    let u := 7 + 10 ^ d * v
    ¬ UsesDigits (2 * u + 10 * u ^ 2)

/-- The terminal-digit `4` carry core. -/
def H2 : Prop := ∀ d v : ℕ, 1 ≤ d → d ≤ 2 → 10 ≤ v → v % 10 = 4 →
  UsesDigits v →
    let u := 7 + 10 ^ d * v
    ¬ UsesDigits (2 * u + 10 * u ^ 2)

/-- The terminal-digit `7` carry core. -/
def H3 : Prop := ∀ d v : ℕ, 1 ≤ d → d ≤ 2 → 10 ≤ v → v % 10 = 7 →
  UsesDigits v →
    let u := 7 + 10 ^ d * v
    ¬ UsesDigits (2 * u + 10 * u ^ 2)

theorem main : H1 → H2 → H3 → OMA.R_oeis_a136863_R1.H1 := by
  intro h1 h4 h7 d v hd1 hd2 hv hv0 hdig
  have hm := OMA.R_oeis_a136863_R1.last_ok hdig
  rcases hm with h0 | h1' | h4' | h7'
  · omega
  · exact h1 d v hd1 hd2 hv h1' hdig
  · exact h4 d v hd1 hd2 hv h4' hdig
  · exact h7 d v hd1 hd2 hv h7' hdig

end OMA.R_oeis_a136863_R1_H1_R1
