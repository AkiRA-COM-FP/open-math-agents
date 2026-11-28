import FormalConjectures.ErdosProblems.«151»

/-! An independent set's complement meets all cliques of size at least two.
The prior proof's extremal argument is retained, with the set membership
handled directly and the clique argument expressed as a contradiction. -/
open SimpleGraph Erdos151

theorem OMA.solution : type_of% @Erdos151.erdos_151.variants.cliqueFree_three := by
  intro n G hG
  let S : Set ℕ := {k | ∀ F : SimpleGraph (Fin n), F.CliqueFree 3 → ∃ s, F.IsNIndepSet k s}
  have h0 : 0 ∈ S := fun F _ => ⟨∅, by simp [isNIndepSet_iff]⟩
  have hfin : S.Finite := (Set.finite_Iic n).subset fun k hk => by
    obtain ⟨s, hs⟩ := hk G hG
    simpa [hs.card_eq] using Finset.card_le_univ s
  have hs : sSup S ∈ S := (show S.Nonempty from ⟨0,h0⟩).csSup_mem hfin
  obtain ⟨s, hi⟩ := hs G hG
  apply csInf_le'
  refine ⟨sᶜ, ?_, by rw [Finset.card_compl, Fintype.card_fin, hi.card_eq]; rfl⟩
  intro t ht
  obtain ⟨a,b,ha,hb,hab⟩ := Finset.one_lt_card_iff.mp ht.2
  by_cases h : a ∈ s
  · exact ⟨b,hb,Finset.mem_compl.mpr fun h' => hi.isIndepSet h h' hab (ht.1.1 ha hb hab)⟩
  · exact ⟨a,ha,Finset.mem_compl.mpr h⟩

-- Original proof from the upstream repository, last author @VestigeClub.
