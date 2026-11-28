import OMAStatements.S_oeis_a111883

open OMA.S_oeis_a111883

theorem OMA.solution : type_of% @OMA.S_oeis_a111883.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  simp only [a, show m + 3 - 1 = m + 2 from rfl, show m + 3 - 2 = m + 1 from rfl,
    show m + 3 - 3 = m from rfl,
    show involutions (m + 3) = involutions (m + 2) + ((m + 1 : ℕ) + 1) * involutions (m + 1) from rfl,
    show involutions (m + 2) = involutions (m + 1) + ((m : ℕ) + 1) * involutions m from rfl]
  push_cast
  ring
