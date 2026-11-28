import OMAReductions.R_Erdos64_erdos_64_R3_H2_R1

/-!
Contract the prescribed edge in the bipartite marked problem of PR #2529. PR #31004 motivates the marked bipartite case.
The contraction has one fewer vertex and becomes bipartite upon deletion of its
merged vertex. Every even simple cycle lifts at unchanged length, avoiding the
mark. The interior path between the two neighbors of the merged vertex has even
length, so both ends use the same original terminal. In particular a bipartite
counterexample to marked-edge avoidance would refute the ordinary conjecture.
Credit: @wispiANt.
-/
namespace OMA.R_Erdos64_erdos_64_R3_H2_R1_H1_R2
open SimpleGraph
open scoped Classical

def H1 : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] (r : V),
    (∀ v, 3 ≤ G.degree v) → 4 ≤ G.degree r →
    (∃ color : V → Bool, ∀ u v, u ≠ r → v ≠ r → G.Adj u v → color u ≠ color v) →
    ∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k

def H2 : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] (a b : V),
    G.Adj b a → 3 ≤ G.minDegree →
    (∀ (z : V) (S : Set V), z ∈ S → (∃ u ∈ S, u ≠ z) → (∃ v, v ∉ S) →
      ∃ u ∈ S, u ≠ z ∧ ∃ v ∉ S, G.Adj u v) →
    (¬ ∃ color : V → Bool, ∀ u v, G.Adj u v → color u ≠ color v) →
    ∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧
      ((c.length = 2^k ∧ s(b,a) ∉ c.edges) ∨ (c.length + 1 = 2^k ∧ s(b,a) ∈ c.edges))

/-- On a walk avoiding the exceptional vertex, endpoint colors agree exactly at even length. -/
theorem colorParity {V : Type} {K : SimpleGraph V} (z : V) (color : V → Bool)
    (proper : ∀ u v, u ≠ z → v ≠ z → K.Adj u v → color u ≠ color v)
    {u v : V} (p : K.Walk u v) (away : z ∉ p.support) :
    (color u = color v ↔ p.length % 2 = 0) := by
  induction p with
  | nil => simp
  | @cons u v w uv p ih =>
    have av : z ∉ p.support := fun h => away (by simp [h])
    have cu := proper u v (fun e => away (by simp [e]))
      (fun e => av (e ▸ p.start_mem_support)) uv
    have h := ih av
    simp only [Walk.length_cons]
    cases h₁ : color u <;> cases h₂ : color v <;> cases h₃ : color w <;>
      simp [h₁,h₂,h₃] at cu h ⊢ <;> omega

private theorem interiorEdges {V : Type} {K F : SimpleGraph V} {z : V}
    (awayEdge : ∀ u v, u ≠ z → v ≠ z → K.Adj u v → F.Adj u v)
    {u v : V} (p : K.Walk u v) (away : z ∉ p.support) :
    ∀ e ∈ p.edges, e ∈ F.edgeSet := by
  rintro ⟨i,j⟩ he
  exact awayEdge _ _ (fun h => away (h ▸ p.fst_mem_support_of_mem_edges he))
    (fun h => away (h ▸ p.snd_mem_support_of_mem_edges he)) (p.edges_subset_edgeSet he)

private theorem liftAt {V : Type} {K F : SimpleGraph V} {z u v : V}
    (zu : K.Adj z u) (vz : K.Adj v z) (p : K.Walk u v)
    (hc : (Walk.cons zu (p.concat vz)).IsCycle) (fu : F.Adj z u) (fv : F.Adj v z)
    (inside : ∀ e ∈ p.edges, e ∈ F.edgeSet) :
    ∃ d : F.Walk z z, d.IsCycle ∧ d.length = (Walk.cons zu (p.concat vz)).length := by
  let c := Walk.cons zu (p.concat vz)
  have valid : ∀ e ∈ c.edges, e ∈ F.edgeSet := by
    intro e he
    simp only [c,Walk.edges_cons,Walk.edges_concat,List.mem_cons,List.concat_eq_append,List.mem_append,
      List.not_mem_nil,or_false] at he
    rcases he with rfl | he | rfl
    · exact fu
    · exact inside _ he
    · exact fv
  exact ⟨c.transfer F valid,hc.transfer valid,c.length_transfer valid⟩

private theorem splitCycle {V : Type} (K F J : SimpleGraph V) (z : V) (color : V → Bool)
    (proper : ∀ u v, u ≠ z → v ≠ z → K.Adj u v → color u ≠ color v)
    (both : ∀ u v, u ≠ z → v ≠ z → K.Adj u v → F.Adj u v ∧ J.Adj u v)
    (star : ∀ u, K.Adj z u → (if color u then F.Adj z u else J.Adj z u))
    {w : V} (c : K.Walk w w) (hc : c.IsCycle) (even : c.length % 2 = 0) :
    (∃ w, ∃ d : F.Walk w w, d.IsCycle ∧ d.length = c.length) ∨
    (∃ w, ∃ d : J.Walk w w, d.IsCycle ∧ d.length = c.length) := by
  classical
  by_cases hz : z ∈ c.support
  · let rot := c.rotate z hz
    have rc : rot.IsCycle := hc.rotate hz
    have rl : rot.length = c.length := c.length_rotate _ _
    clear_value rot
    cases rot with
    | nil => exact (rc.not_nil .nil).elim
    | @cons _ u _ zu tail =>
      have tp : tail.IsPath := (Walk.cons_isCycle_iff ..).mp rc |>.1
      have nz : ¬ tail.Nil := by
        intro h
        exact zu.ne.symm h.eq
      have vz := tail.adj_penultimate nz
      let p := tail.dropLast
      have hp : p.concat vz = tail := Walk.concat_dropLast vz
      have away := ((Walk.concat_isPath_iff vz).mp (hp ▸ tp)).2
      have hlen := tail.length_dropLast_add_one nz
      have pe : p.length % 2 = 0 := by
        change tail.dropLast.length % 2 = 0
        rw [Walk.length_cons] at rl
        omega
      have same := (colorParity z color proper p away).2 pe
      have h₁ := star u zu
      have h₂ := star _ vz.symm
      have cyc : (Walk.cons zu (p.concat vz)).IsCycle := by rwa [hp]
      have len : (Walk.cons zu (p.concat vz)).length = c.length := by rwa [hp]
      cases h : color u
      · rw [← same,h] at h₂
        rw [h] at h₁
        obtain ⟨d,hd,dl⟩ := liftAt zu vz p cyc h₁ (show J.Adj _ _ from h₂).symm
          (interiorEdges (fun i j ia ja e => (both i j ia ja e).2) p away)
        exact Or.inr ⟨z,d,hd,dl.trans len⟩
      · rw [← same,h] at h₂
        rw [h] at h₁
        obtain ⟨d,hd,dl⟩ := liftAt zu vz p cyc h₁ (show F.Adj _ _ from h₂).symm
          (interiorEdges (fun i j ia ja e => (both i j ia ja e).1) p away)
        exact Or.inl ⟨z,d,hd,dl.trans len⟩
  · have valid := interiorEdges (fun i j ia ja e => (both i j ia ja e).1) c hz
    exact Or.inl ⟨w,c.transfer F valid,hc.transfer valid,c.length_transfer valid⟩

private theorem liftChart {V W : Type} (G : SimpleGraph V) (f : W → V)
    (inj : Function.Injective f) {a b : V} (miss : (∀ t, f t ≠ a) ∨ (∀ t, f t ≠ b))
    {w : W} (d : (G.comap f).Walk w w) (hd : d.IsCycle) :
    ∃ v, ∃ c : G.Walk v v, c.IsCycle ∧ c.length = d.length ∧ s(b,a) ∉ c.edges ∧ (a ∉ c.support ∨ b ∉ c.support) := by
  let hom : G.comap f →g G := ⟨f,fun h => h⟩
  let c := d.map hom
  have fresh (i : V) (h : ∀ t, f t ≠ i) : i ∉ c.support := by
    rw [show c.support = d.support.map hom from d.support_map hom]
    rintro hit
    obtain ⟨t,_,eq⟩ := List.mem_map.mp hit
    exact h t eq
  have omits := miss.imp (fresh a) (fresh b)
  exact ⟨_,c,hd.map inj,d.length_map hom,fun h => omits.elim
    (fun ha => ha (c.snd_mem_support_of_mem_edges h))
    (fun hb => hb (c.fst_mem_support_of_mem_edges h)),omits⟩

/-- Contract any edge of a two-colored graph of minimum degree three. Every even
simple cycle of the smaller graph lifts to a simple cycle avoiding that edge. -/
theorem contractMarked {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {a b : V} (ba : G.Adj b a) (floor : ∀ t, 3 ≤ G.degree t)
    (col : V → Bool) (proper : ∀ u v, G.Adj u v → col u ≠ col v) :
    let W := {t : V // t ≠ a}
    ∃ (K : SimpleGraph W) (z : W), Fintype.card W < Fintype.card V ∧
      (∀ t, 3 ≤ K.degree t) ∧ 4 ≤ K.degree z ∧
      (∃ color : W → Bool, ∀ u v, u ≠ z → v ≠ z → K.Adj u v → color u ≠ color v) ∧
      ∀ w (c : K.Walk w w), c.IsCycle → c.length % 2 = 0 →
        ∃ v, ∃ d : G.Walk v v, d.IsCycle ∧ d.length = c.length ∧ s(b,a) ∉ d.edges ∧
          (a ∉ d.support ∨ b ∉ d.support) := by
  classical
  let W := {t : V // t ≠ a}
  let z : W := ⟨b,ba.ne⟩
  let f (t : W) := t.val
  let g (t : W) := if t = z then a else t.val
  let π (v : V) : W := if h : v = a then z else ⟨v,h⟩
  have fa (t : W) : f t ≠ a := t.property
  have gb (t : W) : g t ≠ b := by
    by_cases h : t = z
    · simpa [g,h] using ba.ne.symm
    · simpa [g,h] using (fun e => h (Subtype.ext e) : t.val ≠ b)
  have gi : Function.Injective g := by
    intro t u eq
    by_cases ht : t = z <;> by_cases hu : u = z
    · exact ht.trans hu.symm
    · exact (u.property (by simpa [g,ht,hu] using eq.symm)).elim
    · exact (t.property (by simpa [g,ht,hu] using eq)).elim
    · exact Subtype.ext (by simpa [g,ht,hu] using eq)
  let F := G.comap f
  let J := G.comap g
  let K := F ⊔ J
  let : DecidableRel K.Adj := fun _ _ => Classical.propDecidable _
  let color (t : W) := decide (col t.val = col a)
  have abCol := proper b a ba
  have common (v : V) (av : G.Adj a v) (bv : G.Adj b v) : False := by
    have ac := proper a v av
    have bc := proper b v bv
    cases h₁ : col a <;> cases h₂ : col b <;> cases h₃ : col v <;> simp_all
  have away {t u : W} (ht : t ≠ z) (hu : u ≠ z) (e : K.Adj t u) : G.Adj t.val u.val := by
    rcases e with h | h
    · exact h
    · simpa [J,comap_adj,g,ht,hu] using h
  have both (t u : W) (ht : t ≠ z) (hu : u ≠ z) (e : K.Adj t u) : F.Adj t u ∧ J.Adj t u := by
    have h := away ht hu e
    exact ⟨h,by simpa [J,comap_adj,g,ht,hu] using h⟩
  have colorOK (t u : W) (ht : t ≠ z) (hu : u ≠ z) (e : K.Adj t u) : color t ≠ color u := by
    have h := proper _ _ (away ht hu e)
    cases h₁ : col t.val <;> cases h₂ : col u.val <;> cases h₃ : col a <;> simp_all [color]
  have star (u : W) (e : K.Adj z u) : (if color u then F.Adj z u else J.Adj z u) := by
    have uz := e.ne.symm
    rcases e with h | h
    · have bad := proper b u h
      have eq : col u.val = col a := by
        cases h₁ : col u.val <;> cases h₂ : col a <;> cases h₃ : col b <;> simp_all
      simpa [color,eq] using h
    · have au : G.Adj a u.val := by simpa [J,comap_adj,g,uz] using h
      have ne := (proper a u au).symm
      simpa [color,ne] using h
  have adjFold (t : W) (ht : t ≠ z) (v : V) (tv : G.Adj t.val v) : K.Adj t (π v) := by
    by_cases va : v = a
    · subst v
      right
      simpa [J,comap_adj,π,g,ht] using tv
    · left
      simpa [F,comap_adj,f,π,va] using tv
  have off (t : W) (ht : t ≠ z) : 3 ≤ K.degree t := by
    have maps : Set.MapsTo π (G.neighborFinset t.val) (K.neighborFinset t) := by
      intro w hw
      exact (K.mem_neighborFinset ..).2 (adjFold t ht w ((G.mem_neighborFinset ..).1 hw))
    have inj : (↑(G.neighborFinset t.val) : Set V).InjOn π := by
      intro u hu v hv eq
      have tu := (G.mem_neighborFinset ..).1 hu
      have tv := (G.mem_neighborFinset ..).1 hv
      have e := congrArg Subtype.val eq
      by_cases ua : u = a <;> by_cases va : v = a
      · exact ua.trans va.symm
      · have bv : b = v := by simpa [π,ua,va,z] using e
        exact (common t (ua ▸ tu.symm) (bv ▸ tv.symm)).elim
      · have ub : u = b := by simpa [π,ua,va,z] using e
        exact (common t (va ▸ tv.symm) (ub ▸ tu.symm)).elim
      · simpa [π,ua,va] using e
    have bound := Finset.card_le_card_of_injOn π maps inj
    simpa only [card_neighborFinset_eq_degree] using (floor t).trans bound
  let A := (G.neighborFinset a).erase b
  let B := (G.neighborFinset b).erase a
  have aN (v) (hv : v ∈ A) : v ≠ b ∧ G.Adj a v := by simpa [A] using hv
  have bN (v) (hv : v ∈ B) : v ≠ a ∧ G.Adj b v := by simpa [B] using hv
  have outsideA {v} (h : v ∈ A ∪ B) : v ≠ a :=
    (Finset.mem_union.mp h).elim (fun hv => (aN v hv).2.ne.symm) (fun hv => (bN v hv).1)
  have distinct : Disjoint A B := Finset.disjoint_left.mpr fun _ hv hw => common _ (aN _ hv).2 (bN _ hw).2
  have rootMaps : Set.MapsTo π (↑(A ∪ B) : Set V) (K.neighborFinset z) := by
    intro v hv
    have va := outsideA hv
    apply (K.mem_neighborFinset ..).2
    rcases Finset.mem_union.mp hv with ha | hb
    · obtain ⟨vb,av⟩ := aN v ha
      have vz : (⟨v,va⟩ : W) ≠ z := fun e => vb (congrArg Subtype.val e)
      right
      simpa [J,comap_adj,π,g,va,vz] using av
    · left
      simpa [F,comap_adj,f,z,π,va] using (bN v hb).2
  have rootInj : (↑(A ∪ B) : Set V).InjOn π := by
    intro t ht u hu eq
    simpa [π,outsideA ht,outsideA hu] using congrArg Subtype.val eq
  have count := Finset.card_le_card_of_injOn π rootMaps rootInj
  have ac : A.card = G.degree a - 1 := by
    rw [show A = _ from rfl, Finset.card_erase_of_mem ((G.mem_neighborFinset a b).2 ba.symm),
      card_neighborFinset_eq_degree]
  have bc : B.card = G.degree b - 1 := by
    rw [show B = _ from rfl, Finset.card_erase_of_mem ((G.mem_neighborFinset b a).2 ba),
      card_neighborFinset_eq_degree]
  rw [Finset.card_union_of_disjoint distinct,ac,bc,card_neighborFinset_eq_degree] at count
  have root : 4 ≤ K.degree z := by
    have := floor a
    have := floor b
    omega
  refine ⟨K,z,Fintype.card_lt_of_injective_of_notMem f Subtype.val_injective
    (b := a) (fun ⟨u,h⟩ => fa u h),fun t => ?_,root,⟨color,colorOK⟩,?_⟩
  · by_cases h : t = z
    · exact h ▸ (by omega : 3 ≤ K.degree z)
    · exact off t h
  · intro w c hc he
    rcases splitCycle K F J z color colorOK (fun u v hu hv e => both u v hu hv e) star c hc he
        with ⟨_,d,hd,dl⟩ | ⟨_,d,hd,dl⟩
    · obtain ⟨v,p,hp,pl,miss⟩ := liftChart G f Subtype.val_injective (Or.inl fa) d hd (b := b)
      exact ⟨v,p,hp,pl.trans dl,miss⟩
    · obtain ⟨v,p,hp,pl,miss⟩ := liftChart G g gi (Or.inr gb) d hd (a := a)
      exact ⟨v,p,hp,pl.trans dl,miss⟩


/-- Failure of marked avoidance already supplies a smaller counterexample
to the ordinary (unmarked) conjecture. No connectivity hypothesis is needed. -/
theorem smallerCounterexample {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {a b : V} (ba : G.Adj b a) (floor : ∀ v, 3 ≤ G.degree v)
    (col : V → Bool) (proper : ∀ u v, G.Adj u v → col u ≠ col v)
    (obstruction : ∀ k v (c : G.Walk v v), 2 ≤ k → c.IsCycle → c.length = 2^k → s(b,a) ∈ c.edges) :
    let W := {v : V // v ≠ a}
    ∃ K : SimpleGraph W, Fintype.card W < Fintype.card V ∧ 3 ≤ K.minDegree ∧
      ∀ k w (c : K.Walk w w), 2 ≤ k → c.IsCycle → c.length ≠ 2^k := by
  classical
  obtain ⟨K,z,lt,deg,_,_,lift⟩ := contractMarked G ba floor col proper
  have : Nonempty {v : V // v ≠ a} := ⟨z⟩
  refine ⟨K,lt,K.le_minDegree_of_forall_le_degree 3 deg,?_⟩
  intro k w c hk hc hl
  have even : c.length % 2 = 0 := by
    rw [hl,show k = (k-1)+1 by omega,pow_succ]
    omega
  obtain ⟨v,d,hd,dl,miss,_⟩ := lift w c hc even
  exact miss (obstruction k v d hk hd (dl.trans hl))

/-- A verified order bound for the ordinary conjecture gives edge avoidance
one order higher for bipartite graphs. The numerical bound is an input. -/
theorem avoidBelow (n : ℕ)
    (small : ∀ (W : Type) (K : SimpleGraph W) [Fintype W] [DecidableRel K.Adj],
      Fintype.card W ≤ n → 3 ≤ K.minDegree →
      ∃ (k : ℕ) (w : W) (c : K.Walk w w), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k)
    {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] {a b : V}
    (ba : G.Adj b a) (floor : ∀ v, 3 ≤ G.degree v) (size : Fintype.card V ≤ n+1)
    (col : V → Bool) (proper : ∀ u v, G.Adj u v → col u ≠ col v) :
    ∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k ∧ s(b,a) ∉ c.edges ∧
      (a ∉ c.support ∨ b ∉ c.support) := by
  classical
  obtain ⟨K,z,lt,deg,_,_,lift⟩ := contractMarked G ba floor col proper
  have : Nonempty {t : V // t ≠ a} := ⟨z⟩
  obtain ⟨k,w,c,hk,hc,hl⟩ := small _ K (by omega) (K.le_minDegree_of_forall_le_degree 3 deg)
  have even : c.length % 2 = 0 := by
    rw [hl,show k = (k-1)+1 by omega,pow_succ]
    omega
  obtain ⟨v,d,hd,dl,miss⟩ := lift w c hc even
  exact ⟨k,v,d,hk,hd,dl.trans hl,miss⟩

/-- A side of a two-edge cut with two nonadjacent opposite-color terminals.
Close the side by a virtual edge, then find a cycle avoiding it. The other
side of the cut is unrestricted. Ducoffe–Dumitru (arXiv:2609.28594) report the
ordinary bound n = 40; that external computation is not used as a Lean axiom. -/
theorem cycleOnBank (n : ℕ)
    (small : ∀ (W : Type) (K : SimpleGraph W) [Fintype W] [DecidableRel K.Adj],
      Fintype.card W ≤ n → 3 ≤ K.minDegree →
      ∃ (k : ℕ) (w : W) (c : K.Walk w w), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k)
    {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] {a b : V}
    (nonedge : ¬ G.Adj a b) (da : 2 ≤ G.degree a) (db : 2 ≤ G.degree b)
    (interior : ∀ t, t ≠ a → t ≠ b → 3 ≤ G.degree t) (size : Fintype.card V ≤ n+1)
    (col : V → Bool) (opposite : col a ≠ col b)
    (proper : ∀ u v, G.Adj u v → col u ≠ col v) :
    ∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k := by
  classical
  have ab : a ≠ b := fun e => opposite (congrArg col e)
  let K := G ⊔ fromEdgeSet {s(b,a)}
  have adj (u v : V) : K.Adj u v ↔ G.Adj u v ∨ (u = a ∧ v = b) ∨ (u = b ∧ v = a) :=
    OMA.R_Erdos64_erdos_64_R3_H2_R1.adjacent_or_mark ab
  have ba : K.Adj b a := (adj b a).2 (Or.inr (Or.inr ⟨rfl,rfl⟩))
  have mono : G ≤ K := le_sup_left
  have gain {x y : V} (xy : K.Adj x y) (old : ¬ G.Adj x y) : G.degree x + 1 ≤ K.degree x := by
    have sub : insert y (G.neighborFinset x) ⊆ K.neighborFinset x := by
      intro t ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact (K.mem_neighborFinset ..).2 xy
      · exact (K.mem_neighborFinset ..).2 (mono ((G.mem_neighborFinset ..).1 ht))
    have bound := Finset.card_le_card sub
    rwa [Finset.card_insert_of_notMem (fun h => old ((G.mem_neighborFinset ..).1 h)),
      card_neighborFinset_eq_degree,card_neighborFinset_eq_degree] at bound
  have deg (t : V) : 3 ≤ K.degree t := by
    by_cases h : t = a
    · subst t
      have := gain ba.symm nonedge
      omega
    by_cases h' : t = b
    · subst t
      have := gain ba (fun e => nonedge e.symm)
      omega
    exact (interior t h h').trans (G.degree_le_of_le mono)
  have colorOK (u v : V) (h : K.Adj u v) : col u ≠ col v := by
    rcases (adj u v).1 h with h | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    exacts [proper _ _ h,opposite,opposite.symm]
  obtain ⟨k,v,c,hk,hc,hl,miss,_⟩ := avoidBelow n small K ba deg size col colorOK
  have valid := OMA.R_Erdos64_erdos_64_R3_H2_R1.forgetAddedEdge c miss
  exact ⟨k,v,c.transfer G valid,hk,hc.transfer valid,(c.length_transfer valid).trans hl⟩

theorem main : H1 → H2 → OMA.R_Erdos64_erdos_64_R3_H2_R1.H1 := by
  intro smaller odd V G _ _ a b ba min cuts
  classical
  by_cases h : ∃ col : V → Bool, ∀ u v, G.Adj u v → col u ≠ col v
  · obtain ⟨col,proper⟩ := h
    obtain ⟨K,z,_,floor,high,colors,lift⟩ :=
      contractMarked G ba (fun t => min.trans (G.minDegree_le_degree t)) col proper
    obtain ⟨k,w,c,hk,hc,hl⟩ := smaller _ K z floor high colors
    have even : c.length % 2 = 0 := by
      rw [hl,show k = (k-1)+1 by omega,pow_succ]
      omega
    obtain ⟨v,d,hd,dl,miss,_⟩ := lift w c hc even
    exact ⟨k,v,d,hk,hd,Or.inl ⟨dl.trans hl,miss⟩⟩
  · exact odd V G a b ba min cuts h

end OMA.R_Erdos64_erdos_64_R3_H2_R1_H1_R2
