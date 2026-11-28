import FormalConjectures.ErdosProblems.«23»

/-!
Five-vertex case of Erdos Problem 23, via a kernel-checked finite coloring certificate.
Credit: @AminAhantab. This shortens an existing proof of a known special case.
The ten bits encode the unordered edges; the ten triples encode every possible triangle.
-/

namespace OMA.Five

def pairs : Fin 10 → Fin 5 × Fin 5 :=
  ![(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]

def triples : Fin 10 → Fin 10 × Fin 10 × Fin 10 :=
  ![(0, 1, 4), (0, 2, 5), (0, 3, 6), (1, 2, 7), (1, 3, 8),
    (2, 3, 9), (4, 5, 7), (4, 6, 8), (5, 6, 9), (7, 8, 9)]

def TriangleFree (b : Fin 10 → Bool) : Prop :=
  ∀ t, ¬ (b (triples t).1 = true ∧ b (triples t).2.1 = true ∧
    b (triples t).2.2 = true)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma certificate : ∀ b : Fin 10 → Bool, TriangleFree b →
    ∃ c : Fin 5 → Fin 2, ∃ k : Fin 10, ∀ e : Fin 10,
      b e = true → c (pairs e).1 = c (pairs e).2 → e = k := by
  unfold TriangleFree
  decide +kernel

lemma enumerate : ∀ a b : Fin 5, a ≠ b →
    ∃ e : Fin 10, s(a, b) = s((pairs e).1, (pairs e).2) := by
  decide

end OMA.Five

theorem OMA.solution : type_of% @Erdos23.erdos_23.variants.n1 := by
  classical
  intro G hG
  let b : Fin 10 → Bool := fun e => decide (G.Adj (Five.pairs e).1 (Five.pairs e).2)
  have ht : Five.TriangleFree b := by
    intro t
    intro h
    have h1 := of_decide_eq_true h.1
    have h2 := of_decide_eq_true h.2.1
    have h3 := of_decide_eq_true h.2.2
    fin_cases t <;> exact hG _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1, h2, h3⟩)
  obtain ⟨c, k, hc⟩ := Five.certificate b ht
  let H : SimpleGraph (Fin 5) :=
    { Adj := fun a b => G.Adj a b ∧ c a ≠ c b
      symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
      loopless := ⟨fun a h => h.2 rfl⟩ }
  refine ⟨H, fun _ _ h => h.1, ⟨SimpleGraph.Coloring.mk c (fun h => h.2)⟩, ?_⟩
  have hs : G.edgeFinset \ H.edgeFinset ⊆ {s((Five.pairs k).1, (Five.pairs k).2)} := by
    intro e he
    obtain ⟨heG, heH⟩ := Finset.mem_sdiff.mp he
    induction e using Sym2.inductionOn with
    | _ a d =>
      have had : G.Adj a d := SimpleGraph.mem_edgeFinset.mp heG
      obtain ⟨i, hi⟩ := Five.enumerate a d had.ne
      rw [hi] at heG heH ⊢
      have hg : G.Adj (Five.pairs i).1 (Five.pairs i).2 :=
        SimpleGraph.mem_edgeFinset.mp heG
      have hm : c (Five.pairs i).1 = c (Five.pairs i).2 := by
        by_contra h
        exact heH (SimpleGraph.mem_edgeFinset.mpr (show H.Adj _ _ from ⟨hg, h⟩))
      have hik := hc i (by simpa [b] using hg) hm
      simp [hik]
  apply Finset.card_le_one.mpr
  intro e he f hf
  have he' := hs (by simpa only [Finset.mem_sdiff, SimpleGraph.mem_edgeFinset] using he)
  have hf' := hs (by simpa only [Finset.mem_sdiff, SimpleGraph.mem_edgeFinset] using hf)
  exact (Finset.mem_singleton.mp he').trans (Finset.mem_singleton.mp hf').symm
