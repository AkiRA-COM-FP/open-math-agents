import OMAStatements.S_oeis_a163250
import Mathlib

open OMA.S_oeis_a163250 in
theorem OMA.solution : type_of% @OMA.S_oeis_a163250.main := by
  first
  | (have hb : ∀ m, m ^ 2 + 4 * m + 8 ≤ Nat.fib (m + 6) ∧
         (m + 1) ^ 2 + 4 * (m + 1) + 8 ≤ Nat.fib (m + 1 + 6) := by
       intro m
       induction m with
       | zero => exact ⟨by decide, by decide⟩
       | succ m ih =>
         refine ⟨ih.2, ?_⟩
         rw [show m + 1 + 1 + 6 = (m + 6) + 2 by ring, Nat.fib_add_two,
           show m + 6 + 1 = m + 1 + 6 by ring]
         nlinarith [ih.1, ih.2]
     intro n hn
     obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
     rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega]
     have b3 := (hb (m + 3)).1
     have b2 := (hb (m + 2)).1
     have b1 := (hb (m + 1)).1
     have hf : Nat.fib (m + 3 + 6) = Nat.fib (m + 2 + 6) + Nat.fib (m + 1 + 6) := by
       rw [show m + 3 + 6 = (m + 7) + 2 by ring, Nat.fib_add_two, show m + 7 + 1 = m + 2 + 6 by ring,
         show m + 7 = m + 1 + 6 by ring]
       ring
     simp only [a]
     zify [b1, b2, b3] at hf ⊢
     rw [hf]
     push_cast
     ring)
  | (intro n hn
     obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
     rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega]
     have h := Nat.fib_add_two (n := m + 7)
     simp only [OMA.S_oeis_a163250.a, show m + 3 + 6 = m + 7 + 2 by omega,
       show m + 2 + 6 = m + 7 + 1 by omega, show m + 1 + 6 = m + 7 by omega, h]
     push_cast
     ring)
