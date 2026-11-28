import OMAReductions.R_Erdos64_erdos_64_R3
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Set.Card

/-!
# Cycles through edges of a smallest biconnected counterexample to Erdős 64

This reduces H1 of project PR #2088. In a vertex-minimal counterexample within
the biconnected class, every edge whose endpoints do not separate the graph
lies on a cycle of length 2^k+1 with k ≥ 1. Such edges span a biconnected
subgraph with at least n+2 edges on n vertices. If an edge lies on no such
cycle, its endpoints form a separating pair.

Ducoffe and Dumitru, arXiv:2609.28594, Lemma 2.1, prove the all-edge statement
for counterexamples minimal among all graphs. Within a block, contracting an
adjacent separating pair can create a cut vertex. We keep track of this
condition under the quotient and delete edges of separating pairs to obtain
a biconnected spanning subgraph. The cycle lifting theorem applies at every
length, even for infinite input graphs. A bipartite block admits a smaller
block whose even cycle lengths all occur in the input, with one endpoint of
the contracted edge prescribed and another vertex excluded.

The spanning theorem for contractible edges is the finite graph theorem
recorded in Tsz Lung Chan, Electronic Journal of Combinatorics 22(2), 2015,
P2.47, Theorem 1. The cut proof below also covers the degenerate cases of
the parent cut predicate.

A descent inside regions attached along an adjacent pair finds a nonempty
subregion with every incident edge nonseparating. Minimum degree three gives
an internal edge. Repeating away from its endpoints yields four distinct
vertices with all incident edges nonseparating. Degree-sum gives the bound
n+2, attained for contractible edges in the complete graph on four vertices.

Related Lean work includes the marked path decomposition in PR #2529, the
bipartite contraction in PR #31338, and the high-degree edge deletion in
PR #21911. The two remaining hypotheses are open cases of the block problem.
-/

namespace OMA.R_Erdos64_erdos_64_R3_H1_R2

open SimpleGraph
open scoped Classical

private theorem closeSame {V : Type*} {G : SimpleGraph V} {s u v : V}
    (p : G.Walk u v) (hp : p.IsPath) (hs : s ∉ p.support)
    (hu : G.Adj s u) (hv : G.Adj v s) (positive : 0 < p.length) :
    ∃ c : G.Walk s s, c.IsCycle ∧ c.length = p.length + 2 := by
  refine ⟨.cons hu (p.concat hv), ?_, by simp [Nat.add_assoc]⟩
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  constructor
  · rw [Walk.tail_cons]
    exact (Walk.isPath_copy _ _ _).mpr (hp.concat hs hv)
  · simp only [Walk.length_cons, Walk.length_concat]
    omega

private theorem closeAcross {V : Type*} {G : SimpleGraph V} {s t u v : V}
    (p : G.Walk u v) (hp : p.IsPath) (hs : s ∉ p.support) (ht : t ∉ p.support)
    (hu : G.Adj s u) (hv : G.Adj v t) (hts : G.Adj t s) :
    ∃ c : G.Walk t t, c.IsCycle ∧ c.length = p.length + 3 ∧ s(t,s) ∈ c.edges := by
  refine ⟨.cons hts (.cons hu (p.concat hv)), ?_, by simp [Nat.add_assoc], by simp⟩
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  constructor
  · have h : s ∉ (p.concat hv).support := by simp [hs, hts.ne.symm]
    rw [Walk.tail_cons]
    exact (Walk.isPath_copy _ _ _).mpr ((hp.concat ht hv).cons h (h := hu))
  · simp only [Walk.length_cons, Walk.length_concat]
    omega

/-- A single merged vertex can lengthen a simple cycle by exactly one edge.
The conclusion is valid at every cycle length and on infinite graphs. -/
theorem liftMergedCycle {V W : Type*} (G : SimpleGraph V) (K : SimpleGraph W)
    (f : W ↪ V) (z : W) {a : V} (link : G.Adj a (f z)) (miss : ∀ t, f t ≠ a)
    (interior : ∀ u v, u ≠ z → v ≠ z → K.Adj u v → G.Adj (f u) (f v))
    (star : ∀ u, K.Adj z u → G.Adj a (f u) ∨ G.Adj (f z) (f u))
    {w : W} (c : K.Walk w w) (hc : c.IsCycle) :
    ∃ v, ∃ d : G.Walk v v, d.IsCycle ∧
      (d.length = c.length ∨ (d.length = c.length + 1 ∧ s(a,f z) ∈ d.edges)) := by
  classical
  let F := G.comap f
  let hom : F →g G := ⟨f, fun h => h⟩
  have edges {u v : W} (p : K.Walk u v) (away : z ∉ p.support) :
      ∀ e ∈ p.edges, e ∈ F.edgeSet := by
    rintro ⟨i,j⟩ he
    exact interior i j (fun h => away (h ▸ p.fst_mem_support_of_mem_edges he))
      (fun h => away (h ▸ p.snd_mem_support_of_mem_edges he)) (p.edges_subset_edgeSet he)
  by_cases hz : z ∈ c.support
  · let rot := c.rotate z hz
    have rc : rot.IsCycle := hc.rotate hz
    have rl : rot.length = c.length := c.length_rotate _ _
    clear_value rot
    cases rot with
    | nil => exact (rc.not_nil .nil).elim
    | @cons _ u _ zu tail =>
      have tp : tail.IsPath := ((Walk.cons_isCycle_iff ..).mp rc).1
      have nz : ¬ tail.Nil := fun h => zu.ne.symm h.eq
      have vz := tail.adj_penultimate nz
      let p := tail.dropLast
      have eq : p.concat vz = tail := Walk.concat_dropLast vz
      obtain ⟨pp,away⟩ := (Walk.concat_isPath_iff vz).mp (eq ▸ tp)
      let q := (p.transfer F (edges p away)).map hom
      have qp : q.IsPath := (pp.transfer (edges p away)).map f.injective
      have qs : q.support = p.support.map f := by
        rw [show q.support = _ from Walk.support_map hom _, Walk.support_transfer]
        rfl
      have qa : a ∉ q.support := by
        rw [qs]
        rintro h
        obtain ⟨i,_,e⟩ := List.mem_map.mp h
        exact miss i e
      have qb : f z ∉ q.support := by
        rw [qs]
        rintro h
        obtain ⟨i,hi,e⟩ := List.mem_map.mp h
        exact away (f.injective e ▸ hi)
      have ql : q.length = p.length := by simp [q]
      have len : q.length + 2 = c.length := by
        rw [Walk.length_cons, ← eq, Walk.length_concat] at rl
        omega
      have minlen := hc.three_le_length
      have pos : 0 < q.length := by omega
      rcases star u zu with au | bu <;> rcases star _ vz.symm with av | bv
      · obtain ⟨d,hd,hl⟩ := closeSame q qp qa au av.symm pos
        exact ⟨_,d,hd,Or.inl (hl.trans len)⟩
      · obtain ⟨d,hd,hl,he⟩ := closeAcross q qp qa qb au bv.symm link.symm
        exact ⟨_,d,hd,Or.inr ⟨by omega, (Sym2.eq_swap ..) ▸ he⟩⟩
      · obtain ⟨d,hd,hl,he⟩ := closeAcross q qp qb qa bu av.symm link
        exact ⟨_,d,hd,Or.inr ⟨by omega,he⟩⟩
      · obtain ⟨d,hd,hl⟩ := closeSame q qp qb bu bv.symm pos
        exact ⟨_,d,hd,Or.inl (hl.trans len)⟩
  · let d := (c.transfer F (edges c hz)).map hom
    exact ⟨_,d,(hc.transfer (edges c hz)).map f.injective, Or.inl (by simp [d])⟩

/-- Push the one-vertex and two-vertex cut conditions through a contraction.
The fibers away from the marked vertex are singletons. -/
private theorem blockAfterFold {V W : Type*} (G : SimpleGraph V)
    (π : V → W) (rep : W → V) (z : W) (a b : V)
    (rightInv : ∀ t, π (rep t) = t)
    (single : ∀ {v t}, π v = t → t ≠ z → v = rep t)
    (fiber : ∀ v, π v = z ↔ v = a ∨ v = b)
    (block : ∀ (t : V) (S : Set V), t ∈ S → (∃ x ∈ S, x ≠ t) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ t ∧ ∃ y ∉ S, G.Adj x y)
    (pair : ∀ S : Set V, a ∈ S → b ∈ S → (∃ x ∈ S, x ≠ a ∧ x ≠ b) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ a ∧ x ≠ b ∧ ∃ y ∉ S, G.Adj x y) :
    ∀ (t : W) (S : Set W), t ∈ S → (∃ x ∈ S, x ≠ t) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ t ∧ ∃ y ∉ S, (G.map π).Adj x y := by
  rintro t S ht ⟨u,hu,hut⟩ ⟨v,hv⟩
  let T := π ⁻¹' S
  have mem (w : W) : rep w ∈ T ↔ w ∈ S := by simp [T, rightInv]
  have out : ∃ y, y ∉ T := ⟨rep v,fun h => hv ((mem v).1 h)⟩
  have liftEdge {i j : V} (hi : i ∈ T) (hj : j ∉ T) (e : G.Adj i j) :
      (G.map π).Adj (π i) (π j) :=
    map_adj_apply' e (fun h => hj (show π j ∈ S from h ▸ (show π i ∈ S from hi)))
  by_cases tz : t = z
  · subst t
    have off : π (rep u) ≠ z := by rwa [rightInv]
    have outside := mt (fiber _).2 off
    obtain ⟨i,hi,hia,hib,j,hj,e⟩ := pair T
      (show π a ∈ S from ((fiber a).2 (Or.inl rfl)) ▸ ht)
      (show π b ∈ S from ((fiber b).2 (Or.inr rfl)) ▸ ht)
      ⟨rep u,(mem u).2 hu,fun h => outside (.inl h),fun h => outside (.inr h)⟩ out
    exact ⟨π i,hi,fun h => ((fiber i).1 h).elim hia hib,π j,hj,liftEdge hi hj e⟩
  · have ne : rep u ≠ rep t := fun h => hut (by simpa only [rightInv] using congrArg π h)
    obtain ⟨i,hi,hit,j,hj,e⟩ := block (rep t) T ((mem t).2 ht) ⟨rep u,(mem u).2 hu,ne⟩ out
    exact ⟨π i,hi,fun h => hit (single h tz),π j,hj,liftEdge hi hj e⟩

/-- Contract a triangle-free edge whose endpoints do not separate the block.
Every cycle of the smaller block has an equal-length lift or a lift one edge
longer through the contracted edge. -/
theorem contractInBlock {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {a b : V} (ab : G.Adj a b) (floor : ∀ t, 3 ≤ G.degree t)
    (common : ∀ t, G.Adj a t → G.Adj b t → False)
    (block : ∀ (t : V) (S : Set V), t ∈ S → (∃ x ∈ S, x ≠ t) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ t ∧ ∃ y ∉ S, G.Adj x y)
    (pair : ∀ S : Set V, a ∈ S → b ∈ S → (∃ x ∈ S, x ≠ a ∧ x ≠ b) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ a ∧ x ≠ b ∧ ∃ y ∉ S, G.Adj x y) :
    let W := {t : V // t ≠ a}
    ∃ (K : SimpleGraph W) (z : W), z.val = b ∧
      K = G.map (fun v => if h : v = a then z else ⟨v,h⟩) ∧ Fintype.card W < Fintype.card V ∧
      (∀ t, 3 ≤ K.degree t) ∧ 4 ≤ K.degree z ∧
      (∀ (t : W) (S : Set W), t ∈ S → (∃ x ∈ S, x ≠ t) → (∃ y, y ∉ S) →
        ∃ x ∈ S, x ≠ t ∧ ∃ y ∉ S, K.Adj x y) ∧
      ∀ w (c : K.Walk w w), c.IsCycle → ∃ v, ∃ d : G.Walk v v, d.IsCycle ∧
        (d.length = c.length ∨ (d.length = c.length + 1 ∧ s(a,b) ∈ d.edges)) := by
  classical
  let W := {t : V // t ≠ a}
  let z : W := ⟨b,ab.ne.symm⟩
  let π (v : V) : W := if h : v = a then z else ⟨v,h⟩
  let K := G.map π
  let : DecidableRel K.Adj := fun _ _ => Classical.propDecidable _
  let f : W ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  have re (t : W) : π (f t) = t := by simp [π,f,t.property]
  have fiber (v : V) : π v = z ↔ v = a ∨ v = b := by
    by_cases h : v = a
    · simp [π,h]
    · unfold π
      rw [dif_neg h, or_iff_right h]
      exact ⟨fun e => congrArg Subtype.val e, fun e => Subtype.ext e⟩
  have single {v : V} {t : W} (h : π v = t) (ht : t ≠ z) : v = f t := by
    have ne : v ≠ a := fun e => ht (h.symm.trans ((fiber v).2 (Or.inl e)))
    simpa [π,ne,f] using congrArg Subtype.val h
  have pBlock := blockAfterFold G π f z a b re (fun h ht => single h ht) fiber block pair
  have off (t : W) (ht : t ≠ z) : 3 ≤ K.degree t := by
    have maps : Set.MapsTo π (G.neighborFinset (f t)) (K.neighborFinset t) := by
      intro v hv
      have e := (G.mem_neighborFinset ..).1 hv
      apply (K.mem_neighborFinset ..).2
      rw [← re t]
      exact map_adj_apply' e (fun h => e.ne (single (h.symm.trans (re t)) ht).symm)
    have inj : (↑(G.neighborFinset (f t)) : Set V).InjOn π := by
      intro v hv w hw eq
      by_cases h : π w = z
      · have avoid (x y : V) (hx : G.Adj (f t) x) (hy : G.Adj (f t) y)
            (ex : x = a ∨ x = b) (ey : y = a ∨ y = b) : x = y := by
          rcases ex with rfl | rfl <;> rcases ey with rfl | rfl
          · rfl
          · exact (common _ hx.symm hy.symm).elim
          · exact (common _ hy.symm hx.symm).elim
          · rfl
        exact avoid v w ((G.mem_neighborFinset ..).1 hv) ((G.mem_neighborFinset ..).1 hw)
          ((fiber v).1 (eq.trans h)) ((fiber w).1 h)
      · exact (single eq h).trans (single rfl h).symm
    have count := Finset.card_le_card_of_injOn π maps inj
    simpa only [card_neighborFinset_eq_degree] using (floor (f t)).trans count
  let A := (G.neighborFinset a).erase b
  let B := (G.neighborFinset b).erase a
  have memA (v) (hv : v ∈ A) : v ≠ b ∧ G.Adj a v := by simpa [A] using hv
  have memB (v) (hv : v ∈ B) : v ≠ a ∧ G.Adj b v := by simpa [B] using hv
  have fresh (v) (hv : v ∈ A ∪ B) : π v ≠ z := by
    rcases Finset.mem_union.mp hv with h | h
    · exact fun e => ((fiber _).1 e).elim (memA v h).2.ne.symm (memA v h).1
    · exact fun e => ((fiber _).1 e).elim (memB v h).1 (memB v h).2.ne.symm
  have disj : Disjoint A B := Finset.disjoint_left.mpr fun v hv hw => common v (memA v hv).2 (memB v hw).2
  have maps : Set.MapsTo π (↑(A ∪ B) : Set V) (K.neighborFinset z) := by
    intro v hv
    apply (K.mem_neighborFinset ..).2
    have ne := (fresh v hv).symm
    rcases Finset.mem_union.mp hv with h | h
    · exact ⟨ne,a,v,(memA v h).2,(fiber a).2 (.inl rfl),rfl⟩
    · exact ⟨ne,b,v,(memB v h).2,(fiber b).2 (.inr rfl),rfl⟩
  have inj : (↑(A ∪ B) : Set V).InjOn π := fun _ _ w hw eq =>
    (single eq (fresh w hw)).trans (single rfl (fresh w hw)).symm
  have count := Finset.card_le_card_of_injOn π maps inj
  have ac : A.card = G.degree a - 1 := by
    rw [show A = _ from rfl,Finset.card_erase_of_mem ((G.mem_neighborFinset ..).2 ab),card_neighborFinset_eq_degree]
  have bc : B.card = G.degree b - 1 := by
    rw [show B = _ from rfl,Finset.card_erase_of_mem ((G.mem_neighborFinset ..).2 ab.symm),card_neighborFinset_eq_degree]
  rw [Finset.card_union_of_disjoint disj,ac,bc,card_neighborFinset_eq_degree] at count
  have root : 4 ≤ K.degree z := by have := floor a; have := floor b; omega
  refine ⟨K,z,rfl,rfl,Fintype.card_lt_of_injective_of_notMem f f.injective (b := a)
    (by rintro ⟨v,h⟩; exact v.property h),fun t => ?_,root,pBlock,?_⟩
  · by_cases h : t = z
    · exact h ▸ (by omega : 3 ≤ K.degree z)
    · exact off t h
  · intro w c hc
    apply liftMergedCycle G K f z ab (fun t => t.property) _ _ c hc
    · rintro u v hu hv ⟨_,x,y,e,hx,hy⟩
      simpa only [← single hx hu, ← single hy hv] using e
    · rintro u e
      obtain ⟨ne,x,y,xy,hx,hy⟩ := e
      rw [single hy ne.symm] at xy
      rcases (fiber x).1 hx with he | he
      · exact Or.inl (he ▸ xy)
      · exact Or.inr (show G.Adj b (f u) from he ▸ xy)

/-- A nonempty region attached to the rest only at two terminals must join
their sides in every cut that is constant along each edge touching the region. -/
private theorem bankJoins {V : Type*} (G : SimpleGraph V) {a b : V} (C : Set V)
    (nonempty : C.Nonempty) (ca : a ∉ C) (cb : b ∉ C)
    (closed : ∀ x ∈ C, ∀ y, G.Adj x y → y ∈ C ∨ y = a ∨ y = b)
    (block : ∀ (z : V) (S : Set V), z ∈ S → (∃ x ∈ S, x ≠ z) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ z ∧ ∃ y ∉ S, G.Adj x y)
    (P : Set V) (same : ∀ x ∈ C, ∀ y, G.Adj x y → (x ∈ P ↔ y ∈ P)) :
    a ∈ P ↔ b ∈ P := by
  have cut (Q : Set V) (u v : V) (q₁ : u ∈ Q) (q₂ : v ∉ Q) (hv : v ∉ C)
      (stable : ∀ x ∈ C, ∀ y, G.Adj x y → (x ∈ Q ↔ y ∈ Q))
      (near : ∀ x ∈ C, ∀ y, G.Adj x y → y ∈ C ∨ y = u ∨ y = v) :
      ∀ x ∈ C, x ∈ Q → x = u := by
    intro x hx hq
    by_contra xu
    let S := {y : V | y = u ∨ y ∈ C ∧ y ∈ Q}
    have vout : v ∉ S := by rintro (h | h); exact q₂ (h ▸ q₁); exact hv h.1
    obtain ⟨i,hi,ine,j,hj,e⟩ := block u S (Or.inl rfl) ⟨x,Or.inr ⟨hx,hq⟩,xu⟩ ⟨v,vout⟩
    have icq : i ∈ C ∧ i ∈ Q := hi.resolve_left ine
    have jq := (stable i icq.1 j e).1 icq.2
    rcases near i icq.1 j e with jc | ju | jv
    · exact hj (Or.inr ⟨jc,jq⟩)
    · exact hj (Or.inl ju)
    · exact q₂ (jv ▸ jq)
  obtain ⟨w,hw⟩ := nonempty
  have near' (x) (hx : x ∈ C) (y) (e : G.Adj x y) : y ∈ C ∨ y = b ∨ y = a :=
    (closed x hx y e).imp_right Or.symm
  have opp (x) (hx : x ∈ C) (y) (e : G.Adj x y) : x ∈ Pᶜ ↔ y ∈ Pᶜ := (same x hx y e).not
  constructor
  · intro ha
    by_contra hb
    by_cases h : w ∈ P
    · exact ca (cut P a b ha hb cb same closed w hw h ▸ hw)
    · exact cb (cut Pᶜ b a hb (fun q => q ha) ca opp near' w hw h ▸ hw)
  · intro hb
    by_contra ha
    by_cases h : w ∈ P
    · exact cb (cut P b a hb ha ca same near' w hw h ▸ hw)
    · exact ca (cut Pᶜ a b ha (fun q => q hb) cb opp closed w hw h ▸ hw)

/-- If the endpoints of an edge separate a block, deleting the edge itself
retains the one-vertex cut property. Finiteness and degree bounds are unnecessary. -/
theorem deleteSeparatingEdge {V : Type*} (G : SimpleGraph V) {a b : V}
    (block : ∀ (t : V) (S : Set V), t ∈ S → (∃ x ∈ S, x ≠ t) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ t ∧ ∃ y ∉ S, G.Adj x y)
    (split : ¬ ∀ S : Set V, a ∈ S → b ∈ S → (∃ x ∈ S, x ≠ a ∧ x ≠ b) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ a ∧ x ≠ b ∧ ∃ y ∉ S, G.Adj x y) :
    ∀ (t : V) (S : Set V), t ∈ S → (∃ x ∈ S, x ≠ t) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ t ∧ ∃ y ∉ S, (G.deleteEdges {s(a,b)}).Adj x y := by
  classical
  push Not at split
  obtain ⟨T,ta,tb,⟨i,hi,ia,ib⟩,⟨j,hj⟩,gap⟩ := split
  intro z S hz inside outside
  by_contra! noCross
  obtain ⟨x,hx,hxz,y,hy,e⟩ := block z S hz inside outside
  have marked : s(x,y) = s(a,b) := by
    by_contra ne
    exact noCross x hx hxz y hy (deleteEdges_adj.mpr ⟨e,by simpa using ne⟩)
  have ends : a ≠ z ∧ b ≠ z ∧ ¬ (a ∈ S ↔ b ∈ S) := by
    have hyz : y ≠ z := fun h => hy (h ▸ hz)
    rw [Sym2.eq,Sym2.rel_iff'] at marked
    rcases marked with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨hxz,hyz,fun eq => hy (eq.mp hx)⟩
    · exact ⟨hyz,hxz,fun eq => hy (eq.mpr hx)⟩
  have bank : ∃ C : Set V, C.Nonempty ∧ a ∉ C ∧ b ∉ C ∧ z ∉ C ∧
      ∀ x ∈ C, ∀ y, G.Adj x y → y ∈ C ∨ y = a ∨ y = b := by
    by_cases zT : z ∈ T
    · refine ⟨Tᶜ,⟨j,hj⟩,fun h => h ta,fun h => h tb,fun h => h zT,?_⟩
      intro u hu v edge
      by_contra! bad
      exact gap v (by simpa using bad.1) bad.2.1 bad.2.2 u hu edge.symm
    · let C := {v : V | v ∈ T ∧ v ≠ a ∧ v ≠ b}
      refine ⟨C,⟨i,hi,ia,ib⟩,fun h => h.2.1 rfl,fun h => h.2.2 rfl,fun h => zT h.1,?_⟩
      intro u hu v edge
      by_contra! bad
      have vt : v ∉ T := fun h => bad.1 ⟨h,bad.2.1,bad.2.2⟩
      exact gap u hu.1 hu.2.1 hu.2.2 v vt edge
  obtain ⟨C,hC,ca,cb,cz,near⟩ := bank
  apply ends.2.2
  apply bankJoins G C hC ca cb near block S
  intro u hu v uv
  have uz : u ≠ z := fun h => cz (h ▸ hu)
  have vz : v ≠ z := by
    rcases near u hu v uv with h | h | h
    · exact fun eq => cz (eq ▸ h)
    · exact h ▸ ends.1
    · exact h ▸ ends.2.1
  have kept : (G.deleteEdges {s(a,b)}).Adj u v := by
    apply deleteEdges_adj.mpr
    refine ⟨uv,?_⟩
    simp only [Set.mem_singleton_iff,Sym2.eq,Sym2.rel_iff',Prod.mk.injEq,Prod.swap_prod_mk]
    rintro (⟨h,_⟩ | ⟨h,_⟩)
    · exact ca (h ▸ hu)
    · exact cb (h ▸ hu)
  constructor
  · intro h
    by_contra hv
    exact noCross u h uz v hv kept
  · intro h
    by_contra hu'
    exact noCross v h vz u hu' kept.symm

/-- Every finite block has a spanning block using only edges whose endpoints
can be deleted together without disconnecting the original graph. -/
theorem spanningNonseparatingEdges {V : Type*} [Fintype V] (G : SimpleGraph V)
    (block : ∀ (t : V) (S : Set V), t ∈ S → (∃ x ∈ S, x ≠ t) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ t ∧ ∃ y ∉ S, G.Adj x y) :
    ∃ H : SimpleGraph V, H ≤ G ∧
      (∀ (t : V) (S : Set V), t ∈ S → (∃ x ∈ S, x ≠ t) → (∃ y, y ∉ S) →
        ∃ x ∈ S, x ≠ t ∧ ∃ y ∉ S, H.Adj x y) ∧
      ∀ a b, H.Adj a b → ∀ S : Set V, a ∈ S → b ∈ S →
        (∃ x ∈ S, x ≠ a ∧ x ≠ b) → (∃ y, y ∉ S) →
          ∃ x ∈ S, x ≠ a ∧ x ≠ b ∧ ∃ y ∉ S, G.Adj x y := by
  classical
  let B (D : SimpleGraph V) := ∀ (t : V) (S : Set V), t ∈ S → (∃ x ∈ S, x ≠ t) →
    (∃ y, y ∉ S) → ∃ x ∈ S, x ≠ t ∧ ∃ y ∉ S, D.Adj x y
  let good (a b : V) := ∀ S : Set V, a ∈ S → b ∈ S → (∃ x ∈ S, x ≠ a ∧ x ≠ b) →
    (∃ y, y ∉ S) → ∃ x ∈ S, x ≠ a ∧ x ≠ b ∧ ∃ y ∉ S, G.Adj x y
  have shrink (n : ℕ) (D : SimpleGraph V) (size : D.edgeFinset.card = n)
      (sub : D ≤ G) (bd : B D) : ∃ H : SimpleGraph V, H ≤ G ∧ B H ∧ ∀ a b, H.Adj a b → good a b := by
    induction n using Nat.strong_induction_on generalizing D with
    | h n ih =>
      by_cases keep : ∀ a b, D.Adj a b → good a b
      · exact ⟨D,sub,bd,keep⟩
      · push Not at keep
        obtain ⟨a,b,ab,bad⟩ := keep
        let E := D.deleteEdges {s(a,b)}
        let : DecidableRel E.Adj := fun _ _ => Classical.propDecidable _
        have be : B E := deleteSeparatingEdge D (a := a) (b := b) bd (by
          intro stuck
          apply bad
          intro S ha hb inside outside
          obtain ⟨i,hi,ia,ib,j,hj,edge⟩ := stuck S ha hb inside outside
          exact ⟨i,hi,ia,ib,j,hj,sub edge⟩)
        have removed : E.edgeFinset = D.edgeFinset.erase s(a,b) := by
          ext e
          simp [E,edgeSet_deleteEdges,and_comm]
        have lt : E.edgeFinset.card < n := by
          rw [← size,removed]
          exact Finset.card_erase_lt_of_mem (D.mem_edgeFinset.mpr ab)
        exact ih _ lt E rfl ((D.deleteEdges_le _).trans sub) be
  exact shrink _ G rfl le_rfl block

/-- A clique on two vertices cannot meet both sides of a vertex cut, except
at the deleted vertices. -/
private theorem sideAvoidingEdge {V : Type*} (G : SimpleGraph V) {a b u v : V}
    (ab : G.Adj a b)
    (split : ¬ ∀ S : Set V, u ∈ S → v ∈ S → (∃ x ∈ S, x ≠ u ∧ x ≠ v) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ u ∧ x ≠ v ∧ ∃ y ∉ S, G.Adj x y) :
    ∃ R : Set V, R.Nonempty ∧ u ∉ R ∧ v ∉ R ∧ a ∉ R ∧ b ∉ R ∧
      ∀ x ∈ R, ∀ y, G.Adj x y → y ∈ R ∨ y = u ∨ y = v := by
  classical
  push Not at split
  obtain ⟨T,tu,tv,⟨i,hi,iu,iv⟩,⟨j,hj⟩,gap⟩ := split
  let X := {w : V | w ∈ T ∧ w ≠ u ∧ w ≠ v}
  have leftSide (p) (hp : p ∈ X) (q) (edge : G.Adj p q) : q ∈ X ∨ q = u ∨ q = v := by
    by_contra! miss
    exact gap p hp.1 hp.2.1 hp.2.2 q (fun h => miss.1 ⟨h,miss.2.1,miss.2.2⟩) edge
  have rightSide (p) (hp : p ∈ Tᶜ) (q) (edge : G.Adj p q) : q ∈ Tᶜ ∨ q = u ∨ q = v := by
    by_contra! miss
    exact gap q (by simpa using miss.1) miss.2.1 miss.2.2 p hp edge.symm
  have rightWitness (ha : a ∈ T) (hb : b ∈ T) := (show
      ∃ R : Set V, R.Nonempty ∧ u ∉ R ∧ v ∉ R ∧ a ∉ R ∧ b ∉ R ∧
        ∀ x ∈ R, ∀ y, G.Adj x y → y ∈ R ∨ y = u ∨ y = v from
    ⟨Tᶜ,⟨j,hj⟩,fun h => h tu,fun h => h tv,fun h => h ha,fun h => h hb,rightSide⟩)
  by_cases ax : a ∈ X
  · exact rightWitness ax.1 (by by_contra h; exact gap a ax.1 ax.2.1 ax.2.2 b h ab)
  by_cases bx : b ∈ X
  · exact rightWitness (by by_contra h; exact gap b bx.1 bx.2.1 bx.2.2 a h ab.symm) bx.1
  exact ⟨X,⟨i,hi,iu,iv⟩,fun h => h.2.1 rfl,fun h => h.2.2 rfl,ax,bx,leftSide⟩

/-- Each region attached along an adjacent pair has a nonempty subregion all
of whose vertices have only nonseparating incident edges in the entire graph.
The subregion is again attached along an adjacent pair. -/
theorem regionOfNonseparatingStars {V : Type*} [Finite V] (G : SimpleGraph V)
    (block : ∀ (t : V) (S : Set V), t ∈ S → (∃ x ∈ S, x ≠ t) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ t ∧ ∃ y ∉ S, G.Adj x y)
    {a b : V} (ab : G.Adj a b) (C : Set V) (nonempty : C.Nonempty)
    (ca : a ∉ C) (cb : b ∉ C)
    (boundary : ∀ x ∈ C, ∀ y, G.Adj x y → y ∈ C ∨ y = a ∨ y = b) :
    ∃ (p q : V) (R : Set V), R ⊆ C ∧ R.Nonempty ∧ G.Adj p q ∧ p ∉ R ∧ q ∉ R ∧
      (∀ x ∈ R, ∀ y, G.Adj x y → y ∈ R ∨ y = p ∨ y = q) ∧
      ∀ u ∈ R, ∀ v, G.Adj u v → ∀ S : Set V, u ∈ S → v ∈ S →
        (∃ x ∈ S, x ≠ u ∧ x ≠ v) → (∃ y, y ∉ S) →
          ∃ x ∈ S, x ≠ u ∧ x ≠ v ∧ ∃ y ∉ S, G.Adj x y := by
  classical
  let good (u v : V) := ∀ S : Set V, u ∈ S → v ∈ S → (∃ x ∈ S, x ≠ u ∧ x ≠ v) →
    (∃ y, y ∉ S) → ∃ x ∈ S, x ≠ u ∧ x ≠ v ∧ ∃ y ∉ S, G.Adj x y
  have inside (n : ℕ) (A : Set V) (size : A.ncard = n) (p q : V) (pq : G.Adj p q)
      (live : A.Nonempty) (pa : p ∉ A) (qa : q ∉ A)
      (near : ∀ x ∈ A, ∀ y, G.Adj x y → y ∈ A ∨ y = p ∨ y = q) :
      ∃ (i j : V) (T : Set V), T ⊆ A ∧ T.Nonempty ∧ G.Adj i j ∧ i ∉ T ∧ j ∉ T ∧
        (∀ x ∈ T, ∀ y, G.Adj x y → y ∈ T ∨ y = i ∨ y = j) ∧
        ∀ u ∈ T, ∀ v, G.Adj u v → good u v := by
    induction n using Nat.strong_induction_on generalizing A p q with
    | h n ih =>
      by_cases safe : ∀ u ∈ A, ∀ v, G.Adj u v → good u v
      · exact ⟨p,q,A,(by intro x hx; exact hx),live,pq,pa,qa,near,safe⟩
      · push Not at safe
        obtain ⟨u,hu,v,uv,bad⟩ := safe
        obtain ⟨R,rne,ru,rv,rp,rq,closed⟩ := sideAvoidingEdge G pq bad
        have sub : R ⊆ A := by
          intro w hw
          by_contra wa
          let S := {t : V | t = v ∨ t ∈ R ∧ t ∉ A}
          have un : u ∉ S := by rintro (e | e); exact uv.ne e; exact ru e.1
          have wv : w ≠ v := fun e => rv (e ▸ hw)
          obtain ⟨i,hi,iv,j,hj,ij⟩ := block v S (Or.inl rfl) ⟨w,Or.inr ⟨hw,wa⟩,wv⟩ ⟨u,un⟩
          have ir := hi.resolve_left iv
          have ja : j ∉ A := by
            intro mem
            rcases near j mem i ij.symm with h | h | h
            · exact ir.2 h
            · exact rp (h ▸ ir.1)
            · exact rq (h ▸ ir.1)
          rcases closed i ir.1 j ij with h | h | h
          · exact hj (Or.inr ⟨h,ja⟩)
          · exact ja (h ▸ hu)
          · exact hj (Or.inl h)
        have lt : R.ncard < n := (Set.ncard_lt_ncard (show R ⊂ A from
          ⟨sub,fun back => ru (back hu)⟩)).trans_eq size
        obtain ⟨i,j,T,tSub,rest⟩ := ih R.ncard lt R rfl u v uv rne ru rv closed
        exact ⟨i,j,T,tSub.trans sub,rest⟩
  exact inside C.ncard C rfl a b ab nonempty ca cb boundary

/-- Any graph containing the nonseparating edges of a biconnected graph of
minimum degree three has at least n+2 edges on n vertices. Four vertices have degree at least three
in the covering graph: two disjoint edges have both whole stars preserved. -/
theorem card_of_nonseparating_edges {V : Type*} [Fintype V] [Nonempty V]
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (floor : ∀ t, 3 ≤ G.degree t)
    (block : ∀ (t : V) (S : Set V), t ∈ S → (∃ x ∈ S, x ≠ t) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ t ∧ ∃ y ∉ S, G.Adj x y)
    (contains : ∀ a b, G.Adj a b →
      (∀ S : Set V, a ∈ S → b ∈ S → (∃ x ∈ S, x ≠ a ∧ x ≠ b) → (∃ y, y ∉ S) →
        ∃ x ∈ S, x ≠ a ∧ x ≠ b ∧ ∃ y ∉ S, G.Adj x y) → H.Adj a b) :
    Fintype.card V + 2 ≤ H.edgeFinset.card := by
  classical
  obtain ⟨J,sub,bJ,edges⟩ := spanningNonseparatingEdges G block
  have jh : J ≤ H := fun {u v} e => contains u v (sub e) (edges u v e)
  have many (t : V) : 1 < (G.neighborFinset t).card := by
    rw [card_neighborFinset_eq_degree]
    exact (by decide : 1 < 3).trans_le (floor t)
  have third (t r : V) : ∃ y, y ≠ t ∧ y ≠ r := by
    obtain ⟨y,hy,yr⟩ := Finset.exists_mem_ne (many t) r
    exact ⟨y,((G.mem_neighborFinset ..).1 hy).ne.symm,yr⟩
  have another (t r : V) (tr : t ≠ r) : ∃ b, H.Adj t b ∧ b ≠ r := by
    let S : Set V := {t,r}
    obtain ⟨y,yt,yr⟩ := third t r
    obtain ⟨x,hx,xr,b,hb,xb⟩ := bJ r S (by simp [S]) ⟨t,by simp [S],tr⟩ ⟨y,by simp [S,yt,yr]⟩
    have xt : x = t := by simpa [S,xr] using hx
    exact ⟨b,xt ▸ jh xb,fun e => hb (by simp [S,e])⟩
  have base (t : V) : 2 ≤ H.degree t := by
    obtain ⟨r,rt,_⟩ := third t t
    obtain ⟨y,ty,_⟩ := another t r rt.symm
    obtain ⟨z,tz,zy⟩ := another t y ty.ne
    rw [← card_neighborFinset_eq_degree]
    exact Finset.one_lt_card.mpr ⟨z,(H.mem_neighborFinset ..).2 tz,y,(H.mem_neighborFinset ..).2 ty,zy⟩
  have edgeAway (a b : V) (ab : G.Adj a b) :
      ∃ u v, u ≠ a ∧ u ≠ b ∧ v ≠ a ∧ v ≠ b ∧ G.Adj u v ∧ 3 ≤ H.degree u ∧ 3 ≤ H.degree v := by
    let C := {x : V | x ≠ a ∧ x ≠ b}
    obtain ⟨y,ya,yb⟩ := third a b
    obtain ⟨p,q,R,subR,⟨u,hu⟩,_,_,_,near,safe⟩ :=
      regionOfNonseparatingStars G block ab C ⟨y,ya,yb⟩
        (fun h => h.1 rfl) (fun h => h.2 rfl) (by
          intro x hx z _
          by_cases za : z = a
          · exact Or.inr (Or.inl za)
          by_cases zb : z = b
          · exact Or.inr (Or.inr zb)
          · exact Or.inl ⟨za,zb⟩)
    have cap : ({p,q} : Finset V).card ≤ 2 := by
      calc
        _ ≤ ({q} : Finset V).card + 1 := Finset.card_insert_le ..
        _ = 2 := by simp
    have outside : ¬ G.neighborFinset u ⊆ {p,q} := by
      intro h
      have upper := (Finset.card_le_card h).trans cap
      rw [card_neighborFinset_eq_degree] at upper
      have := floor u
      omega
    obtain ⟨v,hv,away⟩ := Finset.not_subset.mp outside
    have uv := (G.mem_neighborFinset ..).1 hv
    have vr : v ∈ R := (near u hu v uv).resolve_right (by simpa using away)
    have high (w) (hw : w ∈ R) : 3 ≤ H.degree w := by
      have incl : G.neighborFinset w ⊆ H.neighborFinset w := by
        intro t ht
        have e := (G.mem_neighborFinset ..).1 ht
        exact (H.mem_neighborFinset ..).2 (contains w t e (safe w hw t e))
      exact (floor w).trans (by simpa only [card_neighborFinset_eq_degree] using Finset.card_le_card incl)
    exact ⟨u,v,(subR hu).1,(subR hu).2,(subR vr).1,(subR vr).2,uv,high u hu,high v vr⟩
  let a := Classical.arbitrary V
  obtain ⟨b,hb,_⟩ := Finset.exists_mem_ne (many a) a
  obtain ⟨u,v,_,_,_,_,uv,hu,hv⟩ := edgeAway a b ((G.mem_neighborFinset ..).1 hb)
  obtain ⟨s,t,su,sv,tu,tv,st,hs,ht⟩ := edgeAway u v uv
  let Q : Finset V := {u,v,s,t}
  have qcard : Q.card = 4 := by simp [Q,uv.ne,su.symm,sv.symm,tu.symm,tv.symm,st.ne]
  have point (w : V) : 2 + (if w ∈ Q then 1 else 0) ≤ H.degree w := by
    by_cases hw : w ∈ Q
    · simp only [hw, if_true]
      simp only [Q,Finset.mem_insert,Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl | rfl <;> assumption
    · simpa [hw] using base w
  have total := Finset.sum_le_sum (s := Finset.univ) (fun w _ => point w)
  simp [Finset.sum_add_distrib,H.sum_degrees_eq_twice_card_edges,qcard] at total
  omega

/-- The obstruction works for an arbitrary set of forbidden cycle lengths.
A triangle is the sole exception where contraction can lower an outside degree. -/
theorem cycleThroughNonseparatingEdge {V : Type} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (lengths : Set ℕ)
    (floor : ∀ t, 3 ≤ G.degree t)
    (block : ∀ (t : V) (S : Set V), t ∈ S → (∃ x ∈ S, x ≠ t) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ t ∧ ∃ y ∉ S, G.Adj x y)
    (avoid : ∀ w (c : G.Walk w w), c.IsCycle → c.length ∉ lengths)
    (smaller : ∀ (W : Type) [Fintype W] (K : SimpleGraph W) (z : W),
      Fintype.card W < Fintype.card V → (∀ t, 3 ≤ K.degree t) → 4 ≤ K.degree z →
      (∀ (t : W) (S : Set W), t ∈ S → (∃ x ∈ S, x ≠ t) → (∃ y, y ∉ S) →
        ∃ x ∈ S, x ≠ t ∧ ∃ y ∉ S, K.Adj x y) →
      ∃ w, ∃ c : K.Walk w w, c.IsCycle ∧ c.length ∈ lengths)
    {a b : V} (ab : G.Adj a b)
    (pair : ∀ S : Set V, a ∈ S → b ∈ S → (∃ x ∈ S, x ≠ a ∧ x ≠ b) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ a ∧ x ≠ b ∧ ∃ y ∉ S, G.Adj x y) :
    ∃ w, ∃ c : G.Walk w w, c.IsCycle ∧ s(a,b) ∈ c.edges ∧
      (c.length = 3 ∨ ∃ n ∈ lengths, c.length = n + 1) := by
  classical
  by_cases triangle : ∃ t, G.Adj a t ∧ G.Adj b t
  · obtain ⟨t,at',bt⟩ := triangle
    let c : G.Walk a a := .cons ab (.cons bt (.cons at'.symm .nil))
    refine ⟨a,c,?_,by simp [c],Or.inl rfl⟩
    apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    constructor
    · rw [show c = _ from rfl,Walk.tail_cons]
      apply (Walk.isPath_copy _ _ _).mpr
      simp [Walk.cons_isPath_iff,ab.ne.symm,bt.ne,at'.ne.symm]
    · exact le_rfl
  · obtain ⟨K,z,_,_,lt,degs,high,kept,lift⟩ := contractInBlock G ab floor
      (fun t ha hb => triangle ⟨t,ha,hb⟩) block pair
    obtain ⟨w,c,hc,len⟩ := smaller _ K z lt degs high kept
    obtain ⟨v,d,hd,same | ⟨long,edge⟩⟩ := lift w c hc
    · exact (avoid v d hd (same.symm ▸ len)).elim
    · exact ⟨v,d,hd,edge,Or.inr ⟨c.length,len,long⟩⟩

/-- A contracted edge can be chosen at any prescribed vertex, avoiding a
second prescribed vertex. Both degree and biconnectivity survive; in a
bipartite input every even cycle in the smaller block lifts at unchanged length. -/
theorem evenSpectrumOfBipartiteBlock {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (color : G.Coloring Bool)
    (floor : ∀ x, 3 ≤ G.degree x)
    (block : ∀ (t : V) (S : Set V), t ∈ S → (∃ x ∈ S, x ≠ t) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ t ∧ ∃ y ∉ S, G.Adj x y)
    (a r : V) (ar : a ≠ r) :
    ∃ b, G.Adj a b ∧ b ≠ r ∧
      let W := {t : V // t ≠ a}
      ∃ K : SimpleGraph W, ∃ z : W, z.val = b ∧
        K = G.map (fun v => if h : v = a then z else ⟨v,h⟩) ∧ Fintype.card W + 1 = Fintype.card V ∧
        (∀ t, 3 ≤ K.degree t) ∧ 4 ≤ K.degree z ∧
        (∀ (t : W) (S : Set W), t ∈ S → (∃ x ∈ S, x ≠ t) → (∃ y, y ∉ S) →
          ∃ x ∈ S, x ≠ t ∧ ∃ y ∉ S, K.Adj x y) ∧
        ∀ w (c : K.Walk w w), c.IsCycle → Even c.length →
          ∃ v, ∃ d : G.Walk v v, d.IsCycle ∧ d.length = c.length := by
  classical
  obtain ⟨H,sub,blockH,safe⟩ := spanningNonseparatingEdges G block
  have count : 1 < (G.neighborFinset a).card := by rw [card_neighborFinset_eq_degree]; have := floor a; omega
  obtain ⟨y,hy,yr⟩ := Finset.exists_mem_ne count r
  have ya := ((G.mem_neighborFinset ..).1 hy).ne.symm
  let S : Set V := {a,r}
  obtain ⟨x,hx,xr,b,hb,e⟩ := blockH r S (by simp [S]) ⟨a,by simp [S],ar⟩ ⟨y,by simp [S,ya,yr]⟩
  have xa : x = a := by simpa [S,xr] using hx
  subst x
  have common (v : V) (av : G.Adj a v) (bv : G.Adj b v) : False := by
    have h₁ := color.valid av
    have h₂ := color.valid bv
    have h₃ := color.valid (sub e)
    cases h : color a <;> cases j : color b <;> cases l : color v <;> simp [h,j,l] at h₁ h₂ h₃
  obtain ⟨K,z,hz,quotient,lt,degs,high,bK,lift⟩ := contractInBlock G (sub e) floor common block (safe a b e)
  have card : Fintype.card {v : V // v ≠ a} = Fintype.card V - 1 := by
    rw [Fintype.card_subtype_compl (fun x : V => x = a),Fintype.card_subtype_eq]
  refine ⟨b,sub e,fun eq => hb (by simp [S,eq]),K,z,hz,quotient,by omega,degs,high,bK,?_⟩
  intro w c hc even
  obtain ⟨v,d,hd,same | ⟨extra,_⟩⟩ := lift w c hc
  · exact ⟨v,d,hd,same⟩
  · have ed := (color.even_length_iff_congr d).2 Iff.rfl
    rw [extra,Nat.even_add_one] at ed
    exact (ed even).elim

/-- Blocks in which every edge is on a cycle one longer than a power of two. -/
def H1 : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
    3 ≤ G.minDegree →
    (∀ (z : V) (S : Set V), z ∈ S → (∃ x ∈ S, x ≠ z) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ z ∧ ∃ y ∉ S, G.Adj x y) →
    (∀ a b, G.Adj a b → ∃ (k : ℕ) (w : V) (c : G.Walk w w),
      1 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k + 1 ∧ s(a,b) ∈ c.edges) →
    ∃ (k : ℕ) (w : V) (c : G.Walk w w), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k

/-- Every uncovered edge is a separating pair. The covered edges contain a biconnected
spanning subgraph with at least n+2 edges on n vertices. The covering cycles are in G. -/
def H2 : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
    let covered (a b : V) := ∃ (k : ℕ) (w : V) (c : G.Walk w w),
      1 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k + 1 ∧ s(a,b) ∈ c.edges
    3 ≤ G.minDegree →
    (∃ a b, G.Adj a b ∧ ¬ covered a b) →
    (∀ a b, G.Adj a b → ¬ covered a b → ∃ S : Set V, a ∈ S ∧ b ∈ S ∧
      (∃ x ∈ S, x ≠ a ∧ x ≠ b) ∧ (∃ y, y ∉ S) ∧
      ∀ x ∈ S, x ≠ a → x ≠ b → ∀ y ∉ S, ¬ G.Adj x y) →
    (∃ H : SimpleGraph V, H ≤ G ∧ Fintype.card V + 2 ≤ H.edgeFinset.card ∧
      (∀ (z : V) (S : Set V), z ∈ S → (∃ x ∈ S, x ≠ z) → (∃ y, y ∉ S) →
        ∃ x ∈ S, x ≠ z ∧ ∃ y ∉ S, H.Adj x y) ∧
      ∀ a b, H.Adj a b → covered a b) →
    ∃ (k : ℕ) (w : V) (c : G.Walk w w), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k

theorem main : H1 → H2 → OMA.R_Erdos64_erdos_64_R3.H1 := by
  intro full separated
  have descend (n : ℕ) : ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
      Fintype.card V = n → 3 ≤ G.minDegree →
      (∀ (t : V) (S : Set V), t ∈ S → (∃ x ∈ S, x ≠ t) → (∃ y, y ∉ S) →
        ∃ x ∈ S, x ≠ t ∧ ∃ y ∉ S, G.Adj x y) →
      ∃ (k : ℕ) (w : V) (c : G.Walk w w), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro V finite G dec size low block
      classical
      by_contra none
      let lengths : Set ℕ := {m | ∃ k : ℕ, 2 ≤ k ∧ m = 2^k}
      let covered (a b : V) := ∃ (k : ℕ) (w : V) (c : G.Walk w w),
        1 ≤ k ∧ c.IsCycle ∧ c.length = 2^k + 1 ∧ s(a,b) ∈ c.edges
      let good (a b : V) := ∀ S : Set V, a ∈ S → b ∈ S → (∃ x ∈ S, x ≠ a ∧ x ≠ b) →
        (∃ y, y ∉ S) → ∃ x ∈ S, x ≠ a ∧ x ≠ b ∧ ∃ y ∉ S, G.Adj x y
      have avoid (w) (c : G.Walk w w) (hc : c.IsCycle) : c.length ∉ lengths := by
        rintro ⟨k,hk,leq⟩
        exact none ⟨k,w,c,hk,hc,leq⟩
      have cert (a b : V) (ab : G.Adj a b) (safe : good a b) : covered a b := by
        obtain ⟨w,c,hc,edge,tri | ⟨m,⟨k,hk,hm⟩,hl⟩⟩ :=
          cycleThroughNonseparatingEdge G lengths (fun t => low.trans (G.minDegree_le_degree t))
            block avoid (by
              intro W inst K z lt degs _ smallerBlock
              have : Nonempty W := ⟨z⟩
              obtain ⟨k,w,c,hk,hc,hl⟩ := ih _ (lt.trans_eq size) W K rfl
                (K.le_minDegree_of_forall_le_degree 3 degs) smallerBlock
              exact ⟨w,c,hc,k,hk,hl⟩) ab safe
        · exact ⟨1,w,c,by decide,hc,tri,edge⟩
        · exact ⟨k,w,c,by omega,hc,hm ▸ hl,edge⟩
      by_cases allCovered : ∀ a b, G.Adj a b → covered a b
      · exact none (full V G low block allCovered)
      · push Not at allCovered
        apply none
        apply separated V G low allCovered
        · intro a b ab uncovered
          have split : ¬ good a b := fun safe => uncovered (cert a b ab safe)
          unfold good at split
          push Not at split
          exact split
        · obtain ⟨x,y,xy,_⟩ := allCovered
          have : Nonempty V := ⟨x⟩
          let D := SimpleGraph.fromRel (fun a b => G.Adj a b ∧ covered a b)
          let : DecidableRel D.Adj := fun _ _ => Classical.propDecidable _
          have inD (a b : V) (ab : G.Adj a b) (p : good a b) : D.Adj a b :=
            ⟨ab.ne, Or.inl ⟨ab,cert a b ab p⟩⟩
          have fromD (a b : V) (d : D.Adj a b) : G.Adj a b ∧ covered a b := by
            rcases d.2 with h | ⟨ba,k,w,c,hk,hc,hl,he⟩
            · exact h
            · exact ⟨ba.symm,k,w,c,hk,hc,hl,(Sym2.eq_swap ..) ▸ he⟩
          have count := card_of_nonseparating_edges G D (fun t => low.trans (G.minDegree_le_degree t))
            block inD
          obtain ⟨J,sub,blockJ,edges⟩ := spanningNonseparatingEdges G block
          refine ⟨D,fun {a b} e => (fromD a b e).1,count,?_,fun a b e => (fromD a b e).2⟩
          intro t S ht i o
          obtain ⟨a,ha,at',b,hb,edge⟩ := blockJ t S ht i o
          exact ⟨a,ha,at',b,hb,inD a b (sub edge) (edges a b edge)⟩
  intro V G finite dec
  exact descend _ V G rfl

end OMA.R_Erdos64_erdos_64_R3_H1_R2
