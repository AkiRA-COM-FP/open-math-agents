import FormalConjectures.ErdosProblems.«151»

open SimpleGraph

theorem OMA.solution : type_of% @Erdos151.erdos_151.variants.cliqueFree_three := by
  intro n G hG
  obtain ⟨I, hI⟩ := Nat.sSup_mem (s := {k | ∀ F : SimpleGraph (Fin n), F.CliqueFree 3 →
      ∃ s, F.IsNIndepSet k s}) ⟨0, fun _ _ => ⟨∅, by simp [isNIndepSet_iff]⟩⟩
    ⟨n, fun k hk => by obtain ⟨s, hs⟩ := hk ⊥ (by simp); simpa [hs.card_eq] using s.card_le_univ⟩ G hG
  refine Nat.sInf_le ⟨Iᶜ, fun t ht => ?_, by rw [Finset.card_compl, Fintype.card_fin, hI.card_eq]; rfl⟩
  obtain ⟨a, b, ha, hb, hab⟩ := Finset.one_lt_card_iff.mp ht.2
  by_cases h : a ∈ I
  · exact ⟨b, hb, Finset.mem_compl.mpr fun hb' => hI.isIndepSet h hb' hab (ht.1.1 ha hb hab)⟩
  · exact ⟨a, ha, Finset.mem_compl.mpr h⟩
