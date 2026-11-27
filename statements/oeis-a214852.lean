import Mathlib

/-!
# A214852: Indices of Fibonacci numbers with the same number of 1's and 0's in their binary representation.

Source: https://oeis.org/A214852
Credit: @Nealanio

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a214852

def binaryZeroCount (n : ℕ) : ℕ :=
  (Nat.digits 2 n).count 0

def binaryOneCount (n : ℕ) : ℕ :=
  (Nat.digits 2 n).count 1

def IsTerm (k : ℕ) : Prop :=
  0 < k ∧ binaryZeroCount (Nat.fib k) = binaryOneCount (Nat.fib k)

theorem main : Set.Infinite {k : ℕ | IsTerm k} := by
  sorry

end OMA.S_oeis_a214852
