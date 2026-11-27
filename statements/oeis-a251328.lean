import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Analysis.Real.Sqrt

/-!
# Two-column arrays with restricted block sums (OEIS A251328)

R. H. Hardin counts ordered arrays with entries 0, 1, or 2. Colin Barker
proposed the generating function and the closed form on 29 November 2018.
The first OEIS term has two rows. Source: https://oeis.org/A251328
-/

namespace OMA.S_oeis_a251328

abbrev Row := Fin 3 × Fin 3

/-- All nine ordered rows, in lexicographic order. -/
def rows : List Row :=
  [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]

def rowSum (r : Row) : ℕ := r.1.val + r.2.val

def fits (r s : Row) : Bool :=
  let t := rowSum r + rowSum s
  t == 2 || t == 4 || t == 6

/-- All valid arrays with a specified first row and `n` further rows. -/
def strips : ℕ → Row → List (List Row)
  | 0, r => [[r]]
  | n + 1, r => rows.flatMap fun s =>
      if fits r s then (strips n s).map (r :: ·) else []

/-- Number of valid arrays with `n + 1` rows and two columns. -/
def a (n : ℕ) : ℕ := (rows.flatMap (strips n)).length

/-- The series starts at index one, as in the source. -/
noncomputable def series : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then 0 else (a n : ℤ)

open PowerSeries in
/-- Barker's generating function, with its unit denominator cleared, and his closed form. -/
theorem main :
    (1 - C 4 * X) * (1 - C 4 * X - C 3 * X ^ 2) * series =
      C 3 * X * (C 13 - C 47 * X - C 36 * X ^ 2) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (7 * 2 ^ (3 + 2 * n) + (35 - 13 * Real.sqrt 7) * (2 - Real.sqrt 7) ^ n +
        (2 + Real.sqrt 7) ^ n * (35 + 13 * Real.sqrt 7)) / 14 := by
  sorry

end OMA.S_oeis_a251328
