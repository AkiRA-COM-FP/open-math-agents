import OMAStatements.S_oeis_a121639

theorem OMA.solution : type_of% @OMA.S_oeis_a121639.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
  rw [show m + 7 - 1 = m + 6 by omega, show m + 7 - 2 = m + 5 by omega,
    show m + 7 - 3 = m + 4 by omega, show m + 7 - 4 = m + 3 by omega]
  simp only [OMA.S_oeis_a121639.a, Nat.factorial_succ]
  push_cast
  ring
