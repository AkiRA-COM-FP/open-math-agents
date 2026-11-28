import OMAReductions.R_Erdos64_erdos_64_R3
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-! Credit: @wispiANt. The single-edge degree bound and cycle lifting are
adapted from @JamesSlash (PR 466). The cut predicate comes from
@Hennyrick (PR 2088). -/

namespace OMA.R_Erdos64_erdos_64_R3_H1_R1

open SimpleGraph

-- The vertices of degree greater than three form an independent set.
def H1 : Prop :=
    ∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
    3 ≤ G.minDegree →
    (∀ (z : V) (S : Set V), z ∈ S → (∃ x ∈ S, x ≠ z) → (∃ y : V, y ∉ S) →
      ∃ x ∈ S, x ≠ z ∧ ∃ y ∉ S, G.Adj x y) →
    (∀ a b, G.Adj a b → G.degree a = 3 ∨ G.degree b = 3) →
    ∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k

-- Every edge between two high-degree vertices becomes the sole edge of
-- an explicit nontrivial cut upon removing a third vertex.
def H2 : Prop :=
    ∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
    3 ≤ G.minDegree →
    (∀ (z : V) (S : Set V), z ∈ S → (∃ x ∈ S, x ≠ z) → (∃ y : V, y ∉ S) →
      ∃ x ∈ S, x ≠ z ∧ ∃ y ∉ S, G.Adj x y) →
    (∃ a b, G.Adj a b ∧ 3 < G.degree a ∧ 3 < G.degree b) →
    (∀ a b, G.Adj a b → 3 < G.degree a → 3 < G.degree b →
      ∃ z : V, ∃ S : Set V, z ∈ S ∧
        ((a ∈ S ∧ a ≠ z ∧ b ∉ S) ∨ (b ∈ S ∧ b ≠ z ∧ a ∉ S)) ∧
        ∀ x ∈ S, x ≠ z → ∀ y ∉ S, G.Adj x y → s(x, y) = s(a, b)) →
    ∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k

theorem delete_edge_degree {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (a b : V) (minimum : 3 ≤ G.minDegree)
    (ha : 3 < G.degree a) (hb : 3 < G.degree b) (x : V) :
    3 ≤ (G.deleteEdges {s(a, b)}).degree x := by
  let H := G.deleteEdges {s(a, b)}
  change 3 ≤ H.degree x
  let removed : Finset V := if x = a then {b} else if x = b then {a} else ∅
  have inclusion : G.neighborFinset x ⊆ H.neighborFinset x ∪ removed := by
    intro y hy
    have adj := (G.mem_neighborFinset x y).mp hy
    apply Finset.mem_union.mpr
    by_cases h : s(x, y) = s(a, b)
    · right
      rcases (Sym2.mk_eq_mk_iff (p := (x, y)) (q := (a, b))).mp h with hd | hd
      · have hx : x = a := congrArg Prod.fst hd
        have hyb : y = b := congrArg Prod.snd hd
        simp [removed, hx, hyb]
      · have hx : x = b := congrArg Prod.fst hd
        have hya : y = a := congrArg Prod.snd hd
        by_cases hab : a = b <;> simp [removed, hx, hya, hab, eq_comm]
    · left
      apply (H.mem_neighborFinset x y).mpr
      exact SimpleGraph.deleteEdges_adj.mpr ⟨adj, by simpa using h⟩
  have cardinal : G.degree x ≤ H.degree x + removed.card := by
    simpa only [card_neighborFinset_eq_degree] using
      (Finset.card_le_card inclusion).trans (Finset.card_union_le _ _)
  have loss : removed.card ≤ 1 := by
    dsimp [removed]
    split
    · simp
    · split <;> simp
  by_cases endpoints : x = a ∨ x = b
  · have larger : 3 < G.degree x := endpoints.elim (fun hx => hx.symm ▸ ha)
      (fun hx => hx.symm ▸ hb)
    omega
  · have noLoss : removed.card = 0 := by simp [removed, (not_or.mp endpoints).1,
      (not_or.mp endpoints).2]
    have lower := minimum.trans (G.minDegree_le_degree x)
    omega

theorem critical_cut {V : Type} (G : SimpleGraph V) (a b : V)
    (block : (∀ (z : V) (S : Set V), z ∈ S → (∃ x ∈ S, x ≠ z) → (∃ y : V, y ∉ S) →
      ∃ x ∈ S, x ≠ z ∧ ∃ y ∉ S, G.Adj x y))
    (essential : ¬ (∀ (z : V) (S : Set V), z ∈ S → (∃ x ∈ S, x ≠ z) → (∃ y : V, y ∉ S) →
      ∃ x ∈ S, x ≠ z ∧ ∃ y ∉ S, (G.deleteEdges {s(a, b)}).Adj x y)) :
    ∃ z : V, ∃ S : Set V, z ∈ S ∧
        ((a ∈ S ∧ a ≠ z ∧ b ∉ S) ∨ (b ∈ S ∧ b ≠ z ∧ a ∉ S)) ∧
        ∀ x ∈ S, x ≠ z → ∀ y ∉ S, G.Adj x y → s(x, y) = s(a, b) := by
  classical
  push Not at essential
  obtain ⟨z, S, hz, inside, outside, noEdge⟩ := essential
  obtain ⟨x, hx, hxz, y, hy, xy⟩ := block z S hz inside outside
  have unique : ∀ u ∈ S, u ≠ z → ∀ v ∉ S, G.Adj u v → s(u, v) = s(a, b) := by
    intro u hu huz v hv uv
    by_contra ne
    exact noEdge u hu huz v hv (SimpleGraph.deleteEdges_adj.mpr ⟨uv, by simpa using ne⟩)
  refine ⟨z, S, hz, ?_, unique⟩
  rcases (Sym2.mk_eq_mk_iff (p := (x, y)) (q := (a, b))).mp (unique x hx hxz y hy xy) with e | e
  · have xa : x = a := congrArg Prod.fst e
    have yb : y = b := congrArg Prod.snd e
    exact Or.inl ⟨xa ▸ hx, xa ▸ hxz, yb ▸ hy⟩
  · have xb : x = b := congrArg Prod.fst e
    have ya : y = a := congrArg Prod.snd e
    exact Or.inr ⟨xb ▸ hx, xb ▸ hxz, ya ▸ hy⟩

theorem descend (independent : H1) (separated : H2) (n : ℕ) :
    ∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
    G.edgeFinset.card = n → 3 ≤ G.minDegree →
    (∀ (z : V) (S : Set V), z ∈ S → (∃ x ∈ S, x ≠ z) → (∃ y : V, y ∉ S) →
      ∃ x ∈ S, x ≠ z ∧ ∃ y ∉ S, G.Adj x y) →
    ∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V G finite dec size low block
    classical
    let B (D : SimpleGraph V) : Prop := (∀ (z : V) (S : Set V), z ∈ S → (∃ x ∈ S, x ≠ z) → (∃ y : V, y ∉ S) →
      ∃ x ∈ S, x ≠ z ∧ ∃ y ∉ S, D.Adj x y)
    by_cases prune : ∃ a b, G.Adj a b ∧ 3 < G.degree a ∧ 3 < G.degree b ∧
        B (G.deleteEdges {s(a, b)})
    · obtain ⟨a, b, ab, ha, hb, remains⟩ := prune
      let D := G.deleteEdges {s(a, b)}
      haveI : Nonempty V := ⟨a⟩
      have lowD : 3 ≤ D.minDegree :=
        D.le_minDegree_of_forall_le_degree 3 (delete_edge_degree G a b low ha hb)
      have erased : D.edgeFinset = G.edgeFinset.erase s(a, b) := by
        ext e
        simp [D, edgeSet_deleteEdges, and_comm]
      have lt : D.edgeFinset.card < n := by
        rw [← size, erased]
        exact Finset.card_erase_lt_of_mem (G.mem_edgeFinset.mpr ab)
      obtain ⟨k, v, c, hk, hc, len⟩ := ih _ lt V D rfl lowD remains
      let incl : D ≤ G := G.deleteEdges_le _
      exact ⟨k, v, c.mapLe incl, hk, hc.mapLe incl, by simpa using len⟩
    · by_cases high : ∃ a b, G.Adj a b ∧ 3 < G.degree a ∧ 3 < G.degree b
      · apply separated V G low block high
        intro a b ab ha hb
        exact critical_cut G a b block (fun survives => prune ⟨a, b, ab, ha, hb, survives⟩)
      · apply independent V G low block
        intro a b ab
        have da := low.trans (G.minDegree_le_degree a)
        have db := low.trans (G.minDegree_le_degree b)
        by_contra! both
        exact high ⟨a, b, ab, by omega, by omega⟩

theorem main : H1 → H2 → OMA.R_Erdos64_erdos_64_R3.H1 := by
  intro independent separated V G finite dec low block
  exact descend independent separated _ V G rfl low block

end OMA.R_Erdos64_erdos_64_R3_H1_R1
