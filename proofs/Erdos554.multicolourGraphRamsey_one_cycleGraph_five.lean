import FormalConjectures.ErdosProblems.«554»

-- The one-color Ramsey number of the five-cycle is five.
open SimpleGraph

theorem OMA.solution : type_of% @Erdos554.multicolourGraphRamsey_one_cycleGraph_five := by
  unfold multicolourGraphRamsey
  apply IsLeast.csInf_eq
  constructor
  · intro C
    refine ⟨0, IsContained.of_le ?_⟩
    intro x y edge
    rw [TopEdgeLabeling.labelGraph_adj]
    exact ⟨edge.ne, Subsingleton.elim _ _⟩
  · intro n hn
    obtain ⟨_, ⟨copy⟩⟩ := hn (EdgeLabeling.mk (fun _ _ _ => 0) (fun _ _ _ => rfl))
    simpa only [Fintype.card_fin] using Fintype.card_le_of_embedding copy.toEmbedding
