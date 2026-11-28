import OMAStatements.S_arxiv_1805_00840

-- Credit: @ryansolves
-- Matching-split proof and six-slot reduction for Conjecture 2 of arXiv:1805.00840.

namespace OMA.R_arxiv_1805_00840_R1
open SimpleGraph OMA.S_arxiv_1805_00840

variable {V : Type*} {G : SimpleGraph V} {A N : G.Subgraph} {u v : V}

/-- Restricting a matching to a set closed under taking partners preserves matching. -/
theorem matching_induce_closed (hN : N.IsMatching) {s : Set V} (hs : s ⊆ N.verts)
    (hc : ∀ {x y}, x ∈ s → N.Adj x y → y ∈ s) : (N.induce s).IsMatching := by
  intro x hx
  obtain ⟨y, hy, _⟩ := hN (hs hx)
  exact ⟨y, ⟨hx, hc hx hy, hy⟩, fun z hz => hN.eq_of_adj_left hz.2.2 hy⟩

/-- A matching already covering every vertex of a larger matching is maximal inside it. -/
theorem matching_eq_of_le_verts (hA : A.IsMatching) (hN : N.IsMatching)
    (hle : A ≤ N) (hv : N.verts = A.verts) : N = A := by
  apply le_antisymm _ hle
  refine ⟨hv.le, ?_⟩
  intro x y hxy
  obtain ⟨z, hz, _⟩ := hA (hv ▸ hxy.fst_mem)
  rwa [hN.eq_of_adj_left hxy (hle.2 hz)]

/-- If u cannot reach an old covered vertex, its new partner v is forced. -/
theorem uniquelyRestricted_add_forced (hA : IsUniquelyRestricted A) (e : G.Adj u v)
    (hu : u ∉ A.verts) (hv : v ∉ A.verts)
    (hfree : ∀ x ∈ A.verts, ¬G.Adj u x) :
    IsUniquelyRestricted (A ⊔ G.subgraphOfAdj e) := by
  have hd : Disjoint A.support (G.subgraphOfAdj e).support := by
    apply Set.disjoint_left.mpr
    intro x hx he
    have hxa := A.support_subset_verts hx
    have hxe := (G.subgraphOfAdj e).support_subset_verts he
    simp only [subgraphOfAdj_verts, Set.mem_insert_iff, Set.mem_singleton_iff] at hxe
    rcases hxe with rfl | rfl
    · exact hu hxa
    · exact hv hxa
  have hsup := hA.1.sup (Subgraph.IsMatching.subgraphOfAdj e) hd
  refine ⟨hsup, ?_⟩
  intro N hN hverts
  have memN (x : V) : x ∈ N.verts ↔ x ∈ A.verts ∨ x = u ∨ x = v := by
    rw [hverts]
    change x ∈ A.verts ∪ {u, v} ↔ _
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  obtain ⟨w, hw, _⟩ := hN ((memN u).2 (.inr (.inl rfl)))
  have forced : N.Adj u v := by
    rcases (memN w).1 hw.snd_mem with ha | rfl | rfl
    · exact (hfree w ha (N.adj_sub hw)).elim
    · exact (G.loopless.irrefl _ (N.adj_sub hw)).elim
    · exact hw
  have closed {x y : V} (hx : x ∈ A.verts) (hxy : N.Adj x y) : y ∈ A.verts := by
    rcases (memN y).1 hxy.snd_mem with h | rfl | rfl
    · exact h
    · exact (hv (hN.eq_of_adj_left hxy.symm forced ▸ hx)).elim
    · exact (hu (hN.eq_of_adj_left hxy.symm forced.symm ▸ hx)).elim
  have hres := matching_induce_closed hN (fun x hx => (memN x).2 (.inl hx)) @closed
  have heq := hA.2 (N.induce A.verts) hres rfl
  apply matching_eq_of_le_verts hsup hN _ hverts
  apply sup_le
  · refine ⟨fun x hx => (memN x).2 (.inl hx), ?_⟩
    intro x y ha
    have h : (N.induce A.verts).Adj x y := heq ▸ ha
    exact h.2.2
  · exact (subgraphOfAdj_le_iff e N).2 forced

end OMA.R_arxiv_1805_00840_R1

namespace OMA.R_arxiv_1805_00840_R1
open SimpleGraph OMA.S_arxiv_1805_00840
variable {V : Type*} {G : SimpleGraph V}


theorem empty_ur : IsUniquelyRestricted (⊥ : G.Subgraph) := by
  constructor
  · intro x hx
    exact hx.elim
  · intro N _ hv
    apply bot_unique
    exact ⟨hv.le, fun _ _ h => (hv.le h.fst_mem).elim⟩

/-- A peeled edge can go into one of the two classes when at most one other
    neighbor of its first endpoint belongs to the old matching. -/
theorem split_insert {M : G.Subgraph} (hM : M.IsMatching) {u v : V} (e : M.Adj u v)
    (hlow : ∀ x ∈ M.verts, ∀ y ∈ M.verts, G.Adj u x → G.Adj u y →
      x ≠ v → y ≠ v → x = y)
    (h : ∃ A B : G.Subgraph, IsUniquelyRestricted A ∧ IsUniquelyRestricted B ∧ Disjoint A.verts B.verts ∧ A ⊔ B = M.induce {x | x ∈ M.verts ∧ x ≠ u ∧ x ≠ v}) : ∃ A B : G.Subgraph, IsUniquelyRestricted A ∧ IsUniquelyRestricted B ∧ Disjoint A.verts B.verts ∧ A ⊔ B = M := by
  classical
  obtain ⟨A, B, hA, hB, hAB, heq⟩ := h
  let S := {x | x ∈ M.verts ∧ x ≠ u ∧ x ≠ v}
  have cover : A.verts ∪ B.verts = S := congrArg Subgraph.verts heq
  have inS {x : V} (hx : x ∈ A.verts ∪ B.verts) : x ∈ M.verts ∧ x ≠ u ∧ x ≠ v :=
    show x ∈ S from cover ▸ hx
  have oldle : M.induce S ≤ M := ⟨fun _ hx => hx.1, fun _ _ h => h.2.2⟩
  have attach {P Q : G.Subgraph} (hP : IsUniquelyRestricted P) (hQ : IsUniquelyRestricted Q)
      (hd : Disjoint P.verts Q.verts) (hPQ : P ⊔ Q = M.induce S)
      (hf : ∀ x ∈ P.verts, ¬G.Adj u x) : ∃ A B : G.Subgraph, IsUniquelyRestricted A ∧ IsUniquelyRestricted B ∧ Disjoint A.verts B.verts ∧ A ⊔ B = M := by
    have vPQ : P.verts ∪ Q.verts = S := congrArg Subgraph.verts hPQ
    have bound {x : V} (hx : x ∈ P.verts ∪ Q.verts) : x ∈ M.verts ∧ x ≠ u ∧ x ≠ v :=
      show x ∈ S from vPQ ▸ hx
    have hnew := uniquelyRestricted_add_forced hP (M.adj_sub e)
      (fun hu => (bound (.inl hu)).2.1 rfl) (fun hv => (bound (.inl hv)).2.2 rfl) hf
    let E := G.subgraphOfAdj (M.adj_sub e)
    have vertsE (x : V) : x ∈ E.verts ↔ x = u ∨ x = v := by
      simp [E]
    have disj : Disjoint (P ⊔ E).verts Q.verts := by
      apply Set.disjoint_left.mpr
      intro x hx hq
      rcases hx with hp | he
      · exact Set.disjoint_left.mp hd hp hq
      · rcases (vertsE x).1 he with hx | hx
        · exact (bound (.inr hq)).2.1 hx
        · exact (bound (.inr hq)).2.2 hx
    refine ⟨P ⊔ E, Q, hnew, hQ, disj, ?_⟩
    have lePQ : P ⊔ Q ≤ M := hPQ ▸ oldle
    have hle : (P ⊔ E) ⊔ Q ≤ M := sup_le
      (sup_le (le_sup_left.trans lePQ) (subgraphOfAdj_le_of_adj M e)) (le_sup_right.trans lePQ)
    have hverts : M.verts = ((P ⊔ E) ⊔ Q).verts := by
      apply Set.Subset.antisymm _ hle.1
      intro x hx
      by_cases he : x = u ∨ x = v
      · exact Or.inl (Or.inr ((vertsE x).2 he))
      · have hs : x ∈ S := ⟨hx, fun h => he (.inl h), fun h => he (.inr h)⟩
        rcases vPQ.symm ▸ hs with hp | hq
        · exact Or.inl (Or.inl hp)
        · exact Or.inr hq
    exact (matching_eq_of_le_verts (hnew.1.sup hQ.1
      (disj.mono (P ⊔ E).support_subset_verts Q.support_subset_verts)) hM hle hverts).symm
  by_cases hf : ∀ x ∈ A.verts, ¬G.Adj u x
  · exact attach hA hB hAB heq hf
  · push Not at hf
    obtain ⟨x, hx, hux⟩ := hf
    apply attach hB hA hAB.symm ((sup_comm B A).trans heq)
    intro y hy huy
    have hxs := inS (.inl hx)
    have hys := inS (.inr hy)
    have eq := hlow x hxs.1 y hys.1 hux huy hxs.2.2 hys.2.2
    exact Set.disjoint_left.mp hAB hx (eq ▸ hy)

end OMA.R_arxiv_1805_00840_R1

namespace OMA.R_arxiv_1805_00840_R1
open SimpleGraph OMA.S_arxiv_1805_00840
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- In every nonempty vertex set of a connected noncubic subcubic graph,
    some vertex has at most two neighbors inside that set. -/
theorem subcubic_sparse_vertex (hc : G.Connected) (hd : ∀ v, G.degree v ≤ 3)
    (hn : ∃ v, G.degree v < 3) (s : Finset V) (hs : s.Nonempty) :
    ∃ u ∈ s, ((G.neighborFinset u).filter (· ∈ s)).card ≤ 2 := by
  classical
  by_contra! h
  have sat {u : V} (hu : u ∈ s) : (G.neighborFinset u).filter (· ∈ s) = G.neighborFinset u := by
    apply Finset.eq_of_subset_of_card_le (Finset.filter_subset ..)
    have h1 := h u hu
    have h2 := hd u
    rw [← G.card_neighborFinset_eq_degree u] at h2
    omega
  obtain ⟨a, ha⟩ := hs
  have all_mem (v : V) : v ∈ s := by
    have path := (G.reachable_iff_reflTransGen a v).1 (hc.preconnected a v)
    induction path with
    | refl => exact ha
    | tail _ e ih =>
      have he := (G.mem_neighborFinset ..).2 e
      rw [← sat ih] at he
      exact (Finset.mem_filter.mp he).2
  obtain ⟨v, hv⟩ := hn
  have h3 := h v (all_mem v)
  rw [sat (all_mem v), G.card_neighborFinset_eq_degree v] at h3
  omega

/-- Deleting the designated neighbor from a set of at most two leaves at most one. -/
theorem unique_other_neighbor {s : Finset V} {u v : V} (hv : v ∈ s) (huv : G.Adj u v)
    (hd : ((G.neighborFinset u).filter (· ∈ s)).card ≤ 2)
    {x y : V} (hx : x ∈ s) (hy : y ∈ s) (hux : G.Adj u x) (huy : G.Adj u y)
    (hxv : x ≠ v) (hyv : y ≠ v) : x = y := by
  classical
  by_contra hxy
  have hsub : ({x, y, v} : Finset V) ⊆ (G.neighborFinset u).filter (· ∈ s) := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset _ _).2 hux, hx⟩
    · exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset _ _).2 huy, hy⟩
    · exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset _ _).2 huv, hv⟩
  have hcard := Finset.card_le_card hsub
  simp [hxy, hxv, hyv] at hcard
  omega

end OMA.R_arxiv_1805_00840_R1

namespace OMA.R_arxiv_1805_00840_R1
open SimpleGraph OMA.S_arxiv_1805_00840
variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Every matching of a connected noncubic subcubic graph is a disjoint union of
    two uniquely restricted matchings of the original graph. -/
theorem subcubic_matching_split (hc : G.Connected) (hd : ∀ v, G.degree v ≤ 3)
    (hn : ∃ v, G.degree v < 3) (M : G.Subgraph) (hM : M.IsMatching) : ∃ A B : G.Subgraph, IsUniquelyRestricted A ∧ IsUniquelyRestricted B ∧ Disjoint A.verts B.verts ∧ A ⊔ B = M := by
  classical
  by_cases hne : M.verts.Nonempty
  · obtain ⟨u, hu, hd2⟩ := subcubic_sparse_vertex hc hd hn M.verts.toFinset
      (Set.toFinset_nonempty.mpr hne)
    have hum : u ∈ M.verts := Set.mem_toFinset.mp hu
    obtain ⟨v, e, _⟩ := hM hum
    let S : Set V := {x | x ∈ M.verts ∧ x ≠ u ∧ x ≠ v}
    have closed {x y : V} (hx : x ∈ S) (hxy : M.Adj x y) : y ∈ S := by
      refine ⟨hxy.snd_mem, ?_, ?_⟩
      · rintro rfl
        exact hx.2.2 (hM.eq_of_adj_left hxy.symm e)
      · rintro rfl
        exact hx.2.1 (hM.eq_of_adj_left hxy.symm e.symm)
    have hm' := matching_induce_closed hM (s := S) (fun _ hx => hx.1) @closed
    apply split_insert hM e _ (subcubic_matching_split hc hd hn (M.induce S) hm')
    intro x hx y hy hux huy hxv hyv
    exact unique_other_neighbor (Set.mem_toFinset.mpr e.snd_mem) (M.adj_sub e) hd2
      (Set.mem_toFinset.mpr hx) (Set.mem_toFinset.mpr hy) hux huy hxv hyv
  · have hbot : M = ⊥ := by
      apply bot_unique
      exact ⟨fun x hx => (hne ⟨x,hx⟩).elim, fun x _ h => (hne ⟨x,h.fst_mem⟩).elim⟩
    exact ⟨⊥, ⊥, empty_ur, empty_ur, disjoint_bot_left, by simp [hbot]⟩
termination_by M.verts.ncard
decreasing_by
  refine Set.ncard_lt_ncard ?_ (Set.toFinite _)
  exact Set.ssubset_iff_subset_ne.mpr ⟨fun _ h => h.1, fun he =>
    have h : u ∈ S := (congrArg (fun t : Set V => u ∈ t) he).mpr hum
    h.2.1 rfl⟩

end OMA.R_arxiv_1805_00840_R1

namespace OMA.R_arxiv_1805_00840_R1
open SimpleGraph OMA.S_arxiv_1805_00840
variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Three copies of each half of a matching give enough internal edges in
    aggregate, while leaving every vertex free in at least three slots. -/
theorem six_slots_from_matching (hc : G.Connected) (hd : ∀ v, G.degree v ≤ 3)
    (hn : ∃ v, G.degree v < 3) (M : G.Subgraph) (hm : M.IsMatching)
    (hsize : G.edgeFinset.card ≤ 3 * M.edgeSet.ncard) :
    ∃ L : Fin 6 → G.Subgraph, (∀ i, IsUniquelyRestricted (L i)) ∧
      G.edgeFinset.card ≤ ∑ i, (L i).edgeSet.ncard ∧
      ∀ x, 3 ≤ {i : Fin 6 | x ∉ (L i).verts}.ncard := by
  classical
  obtain ⟨A, B, hA, hB, hab, heq⟩ := subcubic_matching_split hc hd hn M hm
  let L (i : Fin 6) := if i.val < 3 then A else B
  refine ⟨L, fun i => by dsimp [L]; split <;> assumption, ?_, ?_⟩
  · rw [← heq, Subgraph.edgeSet_sup] at hsize
    have hsum := Set.ncard_union_le A.edgeSet B.edgeSet
    simp [L, Fin.sum_univ_succ]
    omega
  · intro x
    by_cases hx : x ∈ A.verts
    · have hb : x ∉ B.verts := Set.disjoint_left.mp hab hx
      have hs : ({3,4,5} : Set (Fin 6)) ⊆ {i : Fin 6 | x ∉ (L i).verts} := by
        intro i hi
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
        rcases hi with rfl | rfl | rfl <;> simpa [L] using hb
      exact le_trans (by decide : 3 ≤ ({3,4,5} : Finset (Fin 6)).card)
        (by simpa using Set.ncard_le_ncard hs)
    · have hs : ({0,1,2} : Set (Fin 6)) ⊆ {i : Fin 6 | x ∉ (L i).verts} := by
        intro i hi
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
        rcases hi with rfl | rfl | rfl <;> simpa [L] using hx
      exact le_trans (by decide : 3 ≤ ({0,1,2} : Finset (Fin 6)).card)
        (by simpa using Set.ncard_le_ncard hs)

end OMA.R_arxiv_1805_00840_R1

namespace OMA.R_arxiv_1805_00840_R1
open SimpleGraph OMA.S_arxiv_1805_00840

/-- Ordinary matching bound for a bridgeless block with at least two degree-two vertices. -/
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected →
    (∀ e ∈ G.edgeSet, ¬ G.IsBridge e) → (∀ x, 2 ≤ G.degree x ∧ G.degree x ≤ 3) →
    (∃ u v, u ≠ v ∧ G.degree u = 2 ∧ G.degree v = 2) →
    ∃ M : G.Subgraph, M.IsMatching ∧ G.edgeFinset.card ≤ 3 * M.edgeSet.ncard

/-- Six local matchings for the exceptional bridgeless cases (including a singleton).
    The demand at a vertex records how many future bridge endpoints need room there. -/
def H2 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected →
    (∀ e ∈ G.edgeSet, ¬ G.IsBridge e) → (∀ x, G.degree x ≤ 3) →
    IsEmpty (G ≃g completeBipartiteGraph (Fin 3) (Fin 3)) →
    ((∃ x, G.degree x < 2) ∨ ∀ u v, G.degree u = 2 → G.degree v = 2 → u = v) →
    ∀ t : V → ℕ, (∀ x, G.degree x + t x ≤ 3) →
    ∃ L : Fin 6 → G.Subgraph, (∀ i, IsUniquelyRestricted (L i)) ∧
      G.edgeFinset.card ≤ ∑ i, (L i).edgeSet.ncard ∧
      ∀ x, 2 * t x ≤ {i : Fin 6 | x ∉ (L i).verts}.ncard

/-- Combine certificates on the two sides of a specified bridge. The side
    oracle is restricted to the components produced by deleting that one edge. -/
def H3 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected →
    (∀ x, G.degree x ≤ 3) → IsEmpty (G ≃g completeBipartiteGraph (Fin 3) (Fin 3)) →
    ∀ e ∈ G.edgeSet, G.IsBridge e →
    (∀ c : (G.deleteEdges {e}).ConnectedComponent,
      let B := G.induce c.supp
      ∀ [Fintype c.supp] [DecidableRel B.Adj], Fintype.card c.supp < Fintype.card V →
      B.Connected → (∀ x, B.degree x ≤ 3) →
      IsEmpty (B ≃g completeBipartiteGraph (Fin 3) (Fin 3)) →
      ∀ t : c.supp → ℕ, (∀ x, B.degree x + t x ≤ 3) →
      ∃ L : Fin 6 → B.Subgraph, (∀ i, IsUniquelyRestricted (L i)) ∧
        B.edgeFinset.card + {f ∈ B.edgeSet | B.IsBridge f}.ncard ≤ ∑ i, (L i).edgeSet.ncard ∧
        ∀ x, 2 * t x ≤ {i : Fin 6 | x ∉ (L i).verts}.ncard) →
    ∀ t : V → ℕ, (∀ x, G.degree x + t x ≤ 3) →
    ∃ L : Fin 6 → G.Subgraph, (∀ i, IsUniquelyRestricted (L i)) ∧
      G.edgeFinset.card + {f ∈ G.edgeSet | G.IsBridge f}.ncard ≤ ∑ i, (L i).edgeSet.ncard ∧
      ∀ x, 2 * t x ≤ {i : Fin 6 | x ∉ (L i).verts}.ncard

theorem certificates_by_order (h1 : H1) (h2 : H2) (h3 : H3) (n : ℕ) :
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj], Fintype.card V = n →
    G.Connected → (∀ x, G.degree x ≤ 3) → IsEmpty (G ≃g completeBipartiteGraph (Fin 3) (Fin 3)) →
    ∀ t : V → ℕ, (∀ x, G.degree x + t x ≤ 3) →
    ∃ L : Fin 6 → G.Subgraph, (∀ i, IsUniquelyRestricted (L i)) ∧
      G.edgeFinset.card + {f ∈ G.edgeSet | G.IsBridge f}.ncard ≤ ∑ i, (L i).edgeSet.ncard ∧
      ∀ x, 2 * t x ≤ {i : Fin 6 | x ∉ (L i).verts}.ncard := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ G _ horder hc hd hk t ht
    by_cases hb : ∃ e ∈ G.edgeSet, G.IsBridge e
    · obtain ⟨e, he, heb⟩ := hb
      apply h3 V G hc hd hk e he heb _ t ht
      intro c
      dsimp only
      intro _ _ hlt
      exact ih _ (hlt.trans_le horder.le) c.supp (G.induce c.supp) rfl
    · have noBridge : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e := by simpa using hb
      have hempty : {e ∈ G.edgeSet | G.IsBridge e} = ∅ := by
        exact Set.eq_empty_iff_forall_notMem.mpr (fun e h => noBridge e h.1 h.2)
      simp only [hempty, Set.ncard_empty, Nat.add_zero]
      by_cases hmin : ∀ x, 2 ≤ G.degree x
      · by_cases htwo : ∃ u v, u ≠ v ∧ G.degree u = 2 ∧ G.degree v = 2
        · obtain ⟨M, hm, hsize⟩ := h1 V G hc noBridge (fun x => ⟨hmin x, hd x⟩) htwo
          obtain ⟨u, _, _, hu, _⟩ := htwo
          obtain ⟨L, hL, hs, hf⟩ := six_slots_from_matching hc hd ⟨u, by omega⟩ M hm hsize
          refine ⟨L, hL, hs, fun x => ?_⟩
          have := ht x
          have := hmin x
          have := hf x
          omega
        · apply h2 V G hc noBridge hd hk (.inr ?_) t ht
          intro u v hu hv
          by_contra hne
          exact htwo ⟨u,v,hne,hu,hv⟩
      · apply h2 V G hc noBridge hd hk (.inl ?_) t ht
        simpa using hmin

theorem main : H1 → H2 → H3 → type_of% @OMA.S_arxiv_1805_00840.main := by
  intro h1 h2 h3 V _ G _ hc hd hk
  classical
  obtain ⟨L, hL, hs, _⟩ := certificates_by_order h1 h2 h3 _ V G rfl hc hd hk (fun _ => 0)
    (by simpa using hd)
  let f (i : Fin 6) := (L i).edgeSet.ncard
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ f (by simp)
  refine ⟨L i, hL i, hs.trans ?_⟩
  exact (Finset.sum_le_sum (fun j hj => hi j hj)).trans (by simp [f])

end OMA.R_arxiv_1805_00840_R1
