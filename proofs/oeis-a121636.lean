import OMAStatements.S_oeis_a121636

theorem OMA.solution : type_of% @OMA.S_oeis_a121636.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  rw [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
    show m + 5 - 3 = m + 2 by omega]
  simp only [OMA.S_oeis_a121636.a, Nat.factorial_succ]
  push_cast
  ring
