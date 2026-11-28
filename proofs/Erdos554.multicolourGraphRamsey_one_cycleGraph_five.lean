import FormalConjectures.ErdosProblems.«554»

/-! The original five-cycle proof was submitted by @eitanteperman.
This argument builds on the shorter proofs by @VestigeClub and @katiem08. -/

open SimpleGraph

theorem OMA.solution : type_of% @Erdos554.multicolourGraphRamsey_one_cycleGraph_five := by

  refine IsLeast.csInf_eq ⟨fun C ↦ ⟨0, .of_le fun _ _ h ↦ ?_⟩, ?_⟩
  · grind [TopEdgeLabeling.labelGraph_adj]
  · intro n hn
    obtain ⟨_, ⟨f⟩⟩ := hn (fun _ ↦ 0)
    simpa using Fintype.card_le_of_embedding f.toEmbedding
