import FormalConjectures.Wikipedia.Conway99Graph

-- Reduction Conway99Graph.conway99Graph.R1 of Conway's 99-graph problem
-- Credit: @Cryptokraken974

namespace OMA.R_Conway99Graph_conway99Graph_R1

/-- Find a packing three edges short of the extremal edge count. -/
def H1 : Prop :=
  ∃ G : SimpleGraph (Fin 99), G.edgeSet.ncard = 690 ∧
    ∀ x y, x ≠ y →
      (G.neighborSet x ∩ G.neighborSet y).ncard ≤ 2 ∧
      (G.Adj x y → (G.neighborSet x ∩ G.neighborSet y).ncard ≤ 1)

/-- Between 690 and 692 edges, some missing edge can be inserted while preserving both caps. -/
def H2 : Prop :=
  ∀ G : SimpleGraph (Fin 99), 690 ≤ G.edgeSet.ncard → G.edgeSet.ncard ≤ 692 →
    (∀ x y, x ≠ y →
      (G.neighborSet x ∩ G.neighborSet y).ncard ≤ 2 ∧
      (G.Adj x y → (G.neighborSet x ∩ G.neighborSet y).ncard ≤ 1)) →
    ∃ K : SimpleGraph (Fin 99),
      (∃ u v, u ≠ v ∧ ¬ G.Adj u v ∧ K = G ⊔ SimpleGraph.edge u v) ∧
      K.edgeSet.ncard = G.edgeSet.ncard + 1 ∧
      ∀ x y, x ≠ y →
        (K.neighborSet x ∩ K.neighborSet y).ncard ≤ 2 ∧
        (K.Adj x y → (K.neighborSet x ∩ K.neighborSet y).ncard ≤ 1)

/-- At 693 edges all local common-neighbor bounds are attained. -/
def H3 : Prop :=
  ∀ G : SimpleGraph (Fin 99), G.edgeSet.ncard = 693 →
    (∀ x y, x ≠ y →
      (G.neighborSet x ∩ G.neighborSet y).ncard ≤ 2 ∧
      (G.Adj x y → (G.neighborSet x ∩ G.neighborSet y).ncard ≤ 1)) →
    G.LocallyLinear ∧ ∀ x y, x ≠ y → ¬ G.Adj x y →
      (G.neighborSet x ∩ G.neighborSet y).ncard = 2

theorem main : H1 → H2 → H3 → type_of% @Conway99Graph.conway99Graph := by
  rintro ⟨G, hG, cG⟩ extend extremal
  obtain ⟨J, _, hJ, cJ⟩ := extend G (by omega) (by omega) cG
  obtain ⟨K, _, hK, cK⟩ := extend J (by omega) (by omega) cJ
  obtain ⟨L, _, hL, cL⟩ := extend K (by omega) (by omega) cK
  obtain ⟨hlin, hdiag⟩ := extremal L (by omega) cL
  exact ⟨L, hlin, fun x y hxy ↦ hdiag x y hxy⟩

end OMA.R_Conway99Graph_conway99Graph_R1
