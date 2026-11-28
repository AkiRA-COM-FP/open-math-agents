import OMAReductions.R_Erdos64_erdos_64_R1_H1_R1_H1_R2

/-!
In the rooted triangle-contraction step of PR #27543, every dyadic cycle
contains the whole orbit of the required vertex. In the transitive case
any dyadic witness therefore supplies a Hamiltonian cyclic labeling. A
single commuting point in the matching coordinates of PR #5246 gives a
hexagon through six specified vertices, each solving the rooted length
condition with 6 + 2 = 8. Credit: @wispiANt.
-/
namespace OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R2_H2_R1
open SimpleGraph

/-- The forced orbit is proper. A suitable cycle only has to meet it. -/
def H1 : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] (r : V),
    G.Connected → (∀ v, G.degree v = 3) →
    (∀ ⦃a b⦄, G.Adj a b → ¬ G.IsBridge s(a,b)) →
    (∃ v, ∀ f : G ≃g G, f r ≠ v) →
    (∀ n, n = 3 ∨ n = 6 → ∀ c : (cycleGraph n).Copy G, ∀ f : G ≃g G, f r ∉ Set.range c) →
    (∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ G) →
    (∀ k : ℕ, 2 ≤ k → ∀ c : (cycleGraph (2^k)).Copy G, ∀ f : G ≃g G, f r ∈ Set.range c) →
    ∃ (n k : ℕ) (c : (cycleGraph n).Copy G) (f : G ≃g G),
      3 ≤ n ∧ 2 ≤ k ∧ f r ∈ Set.range c ∧ (n+1=2^k ∨ n+2=2^k)

/-- In cyclic labels the dyadic Hamiltonian cycle is already present.
Only the cubic transitive extensions without a shorter dyadic cycle remain. -/
def H2 : Prop :=
  ∀ (t : ℕ), 5 ≤ t → ∀ (D : SimpleGraph (Fin (2^t))) [DecidableRel D.Adj],
    (∀ i, D.degree i = 3) → ∀ mate : Fin (2^t) → Fin (2^t),
    Function.Involutive mate → (∀ i, mate i ≠ i ∧ ¬ (cycleGraph (2^t)).Adj i (mate i)) →
    (∀ i j, D.Adj i j ↔ (cycleGraph (2^t)).Adj i j ∨ j = mate i) →
    (∀ i j, ∃ f : D ≃g D, f i = j) →
    (¬ cycleGraph 3 ⊑ D) → (¬ cycleGraph 6 ⊑ D) →
    (∀ j : ℕ, 2 ≤ j → j < t → ¬ cycleGraph (2^j) ⊑ D) →
    ∃ n k : ℕ, 3 ≤ n ∧ 2 ≤ k ∧ cycleGraph n ⊑ D ∧ (n+1=2^k ∨ n+2=2^k)

/-- A cyclic list gives a copy whose vertex set includes every entry.
The cyclic-index argument is adapted from PR #27543. -/
theorem rootedRing {V : Type*} (G : SimpleGraph V) (l : List V)
    (large : 3 ≤ l.length) (distinct : l.Nodup) (path : l.IsChain G.Adj)
    (close : ∀ h : l ≠ [], G.Adj (l.getLast h) (l.head h)) :
    ∃ c : (cycleGraph l.length).Copy G, ∀ v ∈ l, v ∈ Set.range c := by
  let : NeZero l.length := ⟨by omega⟩
  have pos : 1 < l.length := by omega
  have next (i : Fin l.length) : G.Adj (l.get i) (l.get (i+1)) := by
    have val : (i+1 : Fin l.length).val = (i.val+1) % l.length := by
      rw [Fin.val_add,Fin.val_one',Nat.mod_eq_of_lt pos]
    by_cases inside : i.val+1 < l.length
    · have eq : (i+1 : Fin l.length).val = i.val+1 := val.trans (Nat.mod_eq_of_lt inside)
      simpa only [List.get_eq_getElem,eq] using path.getElem i.val inside
    · have last : i.val=l.length-1 := by omega
      have start : (i+1 : Fin l.length).val = 0 := by rw [val,show i.val+1=l.length by omega,Nat.mod_self]
      have h := close (List.length_pos_iff.mp (by omega))
      simpa only [List.get_eq_getElem,last,start,List.head_eq_getElem,List.getLast_eq_getElem] using h
  have adj {i j : Fin l.length} (h : (cycleGraph l.length).Adj i j) : G.Adj (l.get i) (l.get j) := by
    have diff : i-j=1 ∨ j-i=1 := by
      simpa only [Fin.ext_iff,Fin.val_one',Nat.mod_eq_of_lt pos] using cycleGraph_adj'.mp h
    rcases diff with e | e
    · have eq : i=j+1 := by simpa [add_comm] using sub_eq_iff_eq_add.mp e
      simpa only [eq] using (next j).symm
    · have eq : j=i+1 := by simpa [add_comm] using sub_eq_iff_eq_add.mp e
      simpa only [eq] using next i
  refine ⟨⟨⟨l.get,fun h => adj h⟩,distinct.injective_get⟩,?_⟩
  intro v hv
  exact List.mem_iff_get.mp hv

/-- One commuting point, along with the three disjoint matchings at the
indicated vertices, suffices. The conclusion specifies all six possible roots. -/
theorem commutingHexagon {X : Type*} (G : SimpleGraph (Bool × X)) (p q : Equiv.Perm X)
    (sep : ∀ x, p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x)
    (idEdge : ∀ x, G.Adj (false,x) (true,x))
    (pEdge : ∀ x, G.Adj (false,x) (true,p x))
    (qEdge : ∀ x, G.Adj (false,x) (true,q x))
    (x : X) (comm : p (q x) = q (p x)) :
    ∃ c : (cycleGraph 6).Copy G, ∀ v ∈ ([(false,x),(true,p x),(false,p x),
      (true,q (p x)),(false,q x),(true,q x)] : List (Bool × X)), v ∈ Set.range c := by
  let l : List (Bool × X) := [(false,x),(true,p x),(false,p x),(true,q (p x)),(false,q x),(true,q x)]
  have x₁ := (sep x).1
  have x₂ := (sep x).2.1
  have x₃ := (sep x).2.2
  have r₁ := (sep (p x)).2.1
  have r₂ : q (p x) ≠ q x := fun e => x₁ (q.injective e)
  have lastEdge : G.Adj (true,q (p x)) (false,q x) := comm ▸ (pEdge (q x)).symm
  exact rootedRing G l (by exact (by decide : 3 ≤ 6))
    (by simp [l,x₁.symm,x₂.symm,x₃,r₁.symm,r₂])
    (by simp [l,pEdge,idEdge,qEdge,(idEdge _).symm,lastEdge]) (by simpa [l] using (qEdge x).symm)

/-- In the globally commuting case every vertex is on a hexagon. -/
theorem everyRootOfCommuting {X : Type*} (G : SimpleGraph (Bool × X)) (p q : Equiv.Perm X)
    (sep : ∀ x, p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x)
    (idEdge : ∀ x, G.Adj (false,x) (true,x)) (pEdge : ∀ x, G.Adj (false,x) (true,p x))
    (qEdge : ∀ x, G.Adj (false,x) (true,q x)) (comm : ∀ x, p (q x) = q (p x))
    (r : Bool × X) : ∃ c : (cycleGraph 6).Copy G, r ∈ Set.range c := by
  obtain ⟨b,y⟩ := r
  cases b with
  | false =>
    obtain ⟨c,h⟩ := commutingHexagon G p q sep idEdge pEdge qEdge y (comm y)
    exact ⟨c,h _ (by simp)⟩
  | true =>
    obtain ⟨c,h⟩ := commutingHexagon G p q sep idEdge pEdge qEdge (p.symm y) (comm _)
    exact ⟨c,h _ (by simp)⟩

/-- At most two vertices per defective permutation coordinate lack a rooted
hexagon. Charge a left vertex to itself and a right vertex to its p-preimage. -/
theorem uncoveredBound {X : Type} [Fintype X] [DecidableEq X] (G : SimpleGraph (Bool × X))
    (p q : Equiv.Perm X) (sep : ∀ x, p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x)
    (idEdge : ∀ x, G.Adj (false,x) (true,x)) (pEdge : ∀ x, G.Adj (false,x) (true,p x))
    (qEdge : ∀ x, G.Adj (false,x) (true,q x)) :
    {r : Bool × X | ¬ ∃ c : (cycleGraph 6).Copy G, r ∈ Set.range c}.ncard ≤
      2 * {x : X | p (q x) ≠ q (p x)}.ncard := by
  classical
  let bad := {r : Bool × X | ¬ ∃ c : (cycleGraph 6).Copy G, r ∈ Set.range c}
  let defect := {x : X | p (q x) ≠ q (p x)}
  let f : Bool × X → Bool × X := fun r => (r.1,if r.1 then p.symm r.2 else r.2)
  have maps (r : Bool × X) (h : r ∈ bad) : f r ∈ (Set.univ : Set Bool) ×ˢ defect := by
    refine ⟨Set.mem_univ _,?_⟩
    obtain ⟨b,y⟩ := r
    cases b with
    | false =>
      change p (q y) ≠ q (p y)
      intro eq
      obtain ⟨c,roots⟩ := commutingHexagon G p q sep idEdge pEdge qEdge y eq
      exact h ⟨c,roots _ (by simp)⟩
    | true =>
      change p (q (p.symm y)) ≠ q (p (p.symm y))
      intro eq
      obtain ⟨c,roots⟩ := commutingHexagon G p q sep idEdge pEdge qEdge _ eq
      exact h ⟨c,roots _ (by simp)⟩
  have inj : Function.Injective f := by
    rintro ⟨i,x⟩ ⟨j,y⟩ h
    cases i <;> cases j <;> simp_all [f]
  have bound := Set.ncard_le_ncard_of_injOn f maps inj.injOn
  simpa [bad,defect,Set.ncard_prod] using bound

private theorem backToRoot {V : Type} {G : SimpleGraph V} {r : V} {n : ℕ}
    (c : (cycleGraph n).Copy G) (f : G ≃g G) (hit : f r ∈ Set.range c) :
    ∃ d : (cycleGraph n).Copy G, r ∈ Set.range d := by
  obtain ⟨i,hi⟩ := hit
  exact ⟨f.symm.toCopy.comp c,i,by change f.symm (c i) = r; rw [hi]; exact f.symm_apply_apply r⟩

theorem forcedOrbit {V : Type} {G : SimpleGraph V} {r : V} {n : ℕ}
    (forced : ∀ c : (cycleGraph n).Copy G, r ∈ Set.range c) (c : (cycleGraph n).Copy G)
    (f : G ≃g G) : f r ∈ Set.range c := by
  obtain ⟨i,hi⟩ := forced (f.symm.toCopy.comp c)
  exact ⟨i,(f.symm_apply_eq.mp hi)⟩

theorem forcedOrbitBound {V : Type} [Fintype V] {G : SimpleGraph V} {r : V} {n : ℕ}
    (forced : ∀ c : (cycleGraph n).Copy G, r ∈ Set.range c) (c : (cycleGraph n).Copy G) :
    {v | ∃ f : G ≃g G, f r = v}.ncard ≤ n := by
  have sub : {v | ∃ f : G ≃g G, f r = v} ⊆ Set.range c := by
    rintro _ ⟨f,rfl⟩
    exact forcedOrbit forced c f
  have card : (Set.range (fun i : Fin n => c i)).ncard = Nat.card (Fin n) :=
    Set.ncard_range_of_injective (f := fun i : Fin n => c i) c.injective
  exact (Set.ncard_le_ncard sub).trans_eq (card.trans (Nat.card_fin n))

/-- The edges outside a spanning ring in a cubic graph give a perfect matching. -/
theorem chordMatching {n : ℕ} (large : 3 ≤ n) (D : SimpleGraph (Fin n)) [DecidableRel D.Adj]
    (ring : cycleGraph n ≤ D) (deg : ∀ i, D.degree i = 3) :
    ∃ mate : Fin n → Fin n, Function.Involutive mate ∧
      (∀ i, mate i ≠ i ∧ ¬ (cycleGraph n).Adj i (mate i)) ∧
      ∀ i j, D.Adj i j ↔ (cycleGraph n).Adj i j ∨ j = mate i := by
  classical
  have rd (i : Fin n) : (cycleGraph n).degree i = 2 := by
    obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le' large
    exact cycleGraph_degree_three_le
  have unique (i : Fin n) : ∃ j, ∀ u, (D.Adj i u ∧ ¬ (cycleGraph n).Adj i u) ↔ u = j := by
    have sub : (cycleGraph n).neighborFinset i ⊆ D.neighborFinset i := by
      intro j h
      exact (D.mem_neighborFinset ..).2 (ring (((cycleGraph n).mem_neighborFinset ..).1 h))
    have card : ((D.neighborFinset i) \ ((cycleGraph n).neighborFinset i)).card = 1 := by
      rw [Finset.card_sdiff_of_subset sub,card_neighborFinset_eq_degree,card_neighborFinset_eq_degree,deg,rd]
    obtain ⟨j,hj⟩ := Finset.card_eq_one.mp card
    exact ⟨j,fun u => by simpa using Finset.ext_iff.mp hj u⟩
  choose mate spec using unique
  have chord (i) := (spec i (mate i)).2 rfl
  refine ⟨mate,fun i => (Eq.symm ((spec _ _).1 ⟨(chord i).1.symm,fun h => (chord i).2 h.symm⟩)),?_,?_⟩
  · exact fun i => ⟨(chord i).1.ne.symm,(chord i).2⟩
  · intro i j
    constructor
    · intro h
      by_cases e : (cycleGraph n).Adj i j
      · exact Or.inl e
      · exact Or.inr ((spec i j).1 ⟨h,e⟩)
    · rintro (h | rfl)
      · exact ring h
      · exact (chord i).1

/-- Check one row of a matching search. Each possible chord partner either
remains for a later row or has an explicit cycle using the known chords. -/
private theorem certificateRow {n : ℕ} (D : SimpleGraph (Fin n)) (mate : Fin n → Fin n)
    (inv : Function.Involutive mate)
    (chord : ∀ i, mate i ≠ i ∧ ¬ (cycleGraph n).Adj i (mate i))
    (edges : ∀ i j, D.Adj i j ↔ (cycleGraph n).Adj i j ∨ j = mate i)
    (a : Fin n) (known : List (Fin n × Fin n)) (pending : List (Fin n))
    (routes : List (List (Fin n))) (fixed : ∀ e ∈ known, mate e.1 = e.2)
    (fresh : ∀ e ∈ known, a ≠ e.1 ∧ a ≠ e.2)
    (cert : ∀ j : Fin n, j ∉ pending → j ≠ a → ¬ (cycleGraph n).Adj a j →
      (∀ e ∈ known, j ≠ e.1 ∧ j ≠ e.2) →
      let l := routes.getD j.val []
      (l.length = 3 ∨ l.length = 6 ∨ l.length = 7 ∨ (l.length = 4 ∧ 4 < n) ∨ (l.length = 8 ∧ 8 < n)) ∧
      l.Nodup ∧ ∀ i k : Fin l.length, (cycleGraph l.length).Adj i k →
        (cycleGraph n).Adj (l.get i) (l.get k) ∨
        (l.get i,l.get k) ∈ (a,j)::known ∨ (l.get k,l.get i) ∈ (a,j)::known) :
    (∃ m, (m = 3 ∨ m = 6 ∨ m = 7 ∨ (m = 4 ∧ 4 < n) ∨ (m = 8 ∧ 8 < n)) ∧ cycleGraph m ⊑ D) ∨
      mate a ∈ pending := by
  by_cases wait : mate a ∈ pending
  · exact Or.inr wait
  have free (e) (he : e ∈ known) : mate a ≠ e.1 ∧ mate a ≠ e.2 := by
    have fix := fixed e he
    have h := fresh e he
    refine ⟨fun eq => h.2 ((inv a).symm.trans ((congrArg mate eq).trans fix)),
      fun eq => h.1 (inv.injective (eq.trans fix.symm))⟩
  let l := routes.getD (mate a).val []
  obtain ⟨size,unique,links⟩ := cert (mate a) wait (chord a).1 (chord a).2 free
  have marked (i j : Fin n) (h : (i,j) ∈ (a,mate a)::known) : D.Adj i j := by
    rcases List.mem_cons.mp h with h | h
    · cases h
      exact (edges _ _).2 (Or.inr rfl)
    · exact (edges _ _).2 (Or.inr (fixed _ h).symm)
  refine Or.inl ⟨l.length,size,⟨⟨⟨l.get,?_⟩,unique.injective_get⟩⟩⟩
  intro i j adj
  exact (links i j adj).elim (fun h => (edges _ _).2 (Or.inl h))
    (fun h => h.elim (marked _ _) (fun rev => (marked _ _ rev).symm))

set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
private theorem small4 (D : SimpleGraph (Fin 4)) (mate : Fin 4 → Fin 4)
    (inv : Function.Involutive mate)
    (chord : ∀ i, mate i ≠ i ∧ ¬ (cycleGraph 4).Adj i (mate i))
    (edges : ∀ i j, D.Adj i j ↔ (cycleGraph 4).Adj i j ∨ j = mate i) :
    ∃ m, (m = 3 ∨ m = 6 ∨ m = 7 ∨ (m = 4 ∧ 4 < 4) ∨ (m = 8 ∧ 8 < 4)) ∧ cycleGraph m ⊑ D := by
  obtain done | next := certificateRow D mate inv chord edges 0 [] []
    [[],[],[0,1,2],[]] (by simp) (by decide) (by decide)
  · exact done
  · simp at next

set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
private theorem small8 (D : SimpleGraph (Fin 8)) (mate : Fin 8 → Fin 8)
    (inv : Function.Involutive mate)
    (chord : ∀ i, mate i ≠ i ∧ ¬ (cycleGraph 8).Adj i (mate i))
    (edges : ∀ i j, D.Adj i j ↔ (cycleGraph 8).Adj i j ∨ j = mate i) :
    ∃ m, (m = 3 ∨ m = 6 ∨ m = 7 ∨ (m = 4 ∧ 4 < 8) ∨ (m = 8 ∧ 8 < 8)) ∧ cycleGraph m ⊑ D := by
  obtain done | next := certificateRow D mate inv chord edges 0 [] [4]
    [[],[],[0,1,2],[0,1,2,3],
      [],[0,5,6,7],[0,6,7],[]] (by simp) (by decide) (by decide)
  · exact done
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at next
    have h0 := next
    obtain done | next := certificateRow D mate inv chord edges 1 [(0,4)] []
      [[],[],[],[1,2,3],
        [],[0,1,5,4],[0,1,6,7],[0,1,7]] (by simp_all) (by decide) (by decide)
    · exact done
    · simp at next

set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
private theorem small16 (D : SimpleGraph (Fin 16)) (mate : Fin 16 → Fin 16)
    (inv : Function.Involutive mate)
    (chord : ∀ i, mate i ≠ i ∧ ¬ (cycleGraph 16).Adj i (mate i))
    (edges : ∀ i j, D.Adj i j ↔ (cycleGraph 16).Adj i j ∨ j = mate i) :
    ∃ m, (m = 3 ∨ m = 6 ∨ m = 7 ∨ (m = 4 ∧ 4 < 16) ∨ (m = 8 ∧ 8 < 16)) ∧ cycleGraph m ⊑ D := by
  obtain done | next := certificateRow D mate inv chord edges 0 [] [4, 8, 12]
    [[],[],[0,1,2],[0,1,2,3],
      [],[0,1,2,3,4,5],[0,1,2,3,4,5,6],[0,1,2,3,4,5,6,7],
      [],[0,9,10,11,12,13,14,15],[0,10,11,12,13,14,15],[0,11,12,13,14,15],
      [],[0,13,14,15],[0,14,15],[]] (by simp) (by decide) (by decide)
  · exact done
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at next
    rcases next with h0 | h0 | h0
    · obtain done | next := certificateRow D mate inv chord edges 1 [(0,4)] []
        [[],[],[],[1,2,3],
          [],[0,1,5,4],[1,2,3,4,5,6],[0,1,7,6,5,4],
          [0,1,8,7,6,5,4],[0,1,9,8,7,6,5,4],[0,1,10,11,12,13,14,15],[0,1,11,12,13,14,15],
          [0,1,12,13,14,15],[0,4,3,2,1,13,14,15],[0,1,14,15],[0,1,15]] (by simp_all) (by decide) (by decide)
      · exact done
      · simp at next
    · obtain done | next := certificateRow D mate inv chord edges 1 [(0,8)] []
        [[],[],[],[1,2,3],
          [1,2,3,4],[0,1,5,6,7,8],[1,2,3,4,5,6],[0,1,7,8],
          [],[0,1,9,8],[0,1,10,11,12,13,14,15],[0,1,11,10,9,8],
          [0,1,12,13,14,15],[0,1,13,12,11,10,9,8],[0,1,14,15],[0,1,15]] (by simp_all) (by decide) (by decide)
      · exact done
      · simp at next
    · obtain done | next := certificateRow D mate inv chord edges 1 [(0,12)] [5]
        [[],[],[],[1,2,3],
          [1,2,3,4],[],[1,2,3,4,5,6],[1,2,3,4,5,6,7],
          [0,1,8,9,10,11,12],[0,1,9,10,11,12],[0,1,10,11,12,13,14,15],[0,1,11,12],
          [],[0,1,13,12],[0,1,14,15],[0,1,15]] (by simp_all) (by decide) (by decide)
      · exact done
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at next
        have h1 := next
        obtain done | next := certificateRow D mate inv chord edges 2 [(0,12),(1,5)] []
          [[],[],[],[],
            [2,3,4],[],[1,2,6,5],[2,3,4,5,6,7],
            [1,2,8,7,6,5],[0,1,2,9,10,11,12],[0,1,2,10,11,12],[0,1,2,11,12,13,14,15],
            [],[0,1,2,13,14,15],[0,1,2,14,13,12],[0,1,2,15]] (by simp_all) (by decide) (by decide)
        · exact done
        · simp at next

/-- Every cubic Hamiltonian chord diagram at orders 4, 8 and 16 has a
triangle, a hexagon, a heptagon, or a strictly shorter dyadic cycle. -/
theorem smallRingResult {t : ℕ} (ht : 2 ≤ t) (upper : t ≤ 4)
    (D : SimpleGraph (Fin (2^t))) [DecidableRel D.Adj]
    (ring : cycleGraph (2^t) ≤ D) (cubic : ∀ i, D.degree i = 3) :
    ∃ m, (m = 3 ∨ m = 6 ∨ m = 7 ∨ (m = 4 ∧ 4 < 2^t) ∨ (m = 8 ∧ 8 < 2^t)) ∧ cycleGraph m ⊑ D := by
  have large : 3 ≤ 2^t := by
    have := Nat.pow_le_pow_right (by decide : 0 < 2) ht
    omega
  obtain ⟨mate,inv,chord,edges⟩ := chordMatching large D ring cubic
  rcases (show t = 2 ∨ t = 3 ∨ t = 4 by omega) with rfl | rfl | rfl
  exacts [small4 D mate inv chord edges,small8 D mate inv chord edges,small16 D mate inv chord edges]

theorem main : H1 → H2 → OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R2.H2 := by
  intro partialOrbits hamilton V G _ _ r conn cubic bridges triangles witness forced
  classical
  rcases witness with ⟨t,ht,⟨c⟩⟩
  by_cases hex : ∃ (d : (cycleGraph 6).Copy G) (f : G ≃g G), f r ∈ Set.range d
  · obtain ⟨d,f,h⟩ := hex
    obtain ⟨e,hit⟩ := backToRoot d f h
    exact ⟨6,3,e,by decide,by decide,hit,Or.inr rfl⟩
  have away (n : ℕ) (short : n = 3 ∨ n = 6) (d : (cycleGraph n).Copy G) (f : G ≃g G) :
      f r ∉ Set.range d := by
    intro h
    rcases short with rfl | rfl
    · obtain ⟨e,hit⟩ := backToRoot d f h
      exact triangles e hit
    · exact hex ⟨d,f,h⟩
  by_cases trans : ∀ v, ∃ f : G ≃g G, f r = v
  · have onto (k : ℕ) (hk : 2 ≤ k) (d : (cycleGraph (2^k)).Copy G) :
        Function.Surjective d := by
      intro v
      obtain ⟨f,rfl⟩ := trans v
      exact forcedOrbit (forced k hk) d f
    let e := Equiv.ofBijective c ⟨c.injective,onto t ht c⟩
    let D := G.comap e
    let iso : D ≃g G := Iso.comap e G
    have ring : cycleGraph (2^t) ≤ D := fun _ _ h => c.toHom.map_adj h
    have deg (i) : D.degree i = 3 := (iso.degree_eq i).symm.trans (cubic _)
    have sym (i j) : ∃ f : D ≃g D, f i = j := by
      obtain ⟨u,hu⟩ := trans (iso i)
      obtain ⟨v,hv⟩ := trans (iso j)
      refine ⟨((iso.trans u.symm).trans v).trans iso.symm,?_⟩
      change iso.symm (v (u.symm (iso i))) = j
      rw [← hu,u.symm_apply_apply,hv,iso.symm_apply_apply]
    have exclude (n : ℕ) (short : n = 3 ∨ n = 6) : ¬ cycleGraph n ⊑ D := by
      rintro ⟨d⟩
      have pos : 0 < n := by rcases short with rfl | rfl <;> decide
      let i : Fin n := ⟨0,pos⟩
      obtain ⟨f,hf⟩ := trans (iso (d i))
      exact away n short (iso.toCopy.comp d) f ⟨i,hf.symm⟩
    have noshort (j : ℕ) (hj : 2 ≤ j) (lt : j < t) : ¬ cycleGraph (2^j) ⊑ D := by
      rintro ⟨d⟩
      let d' := iso.toCopy.comp d
      have eq := Fintype.card_congr (Equiv.ofBijective d' ⟨d'.injective,onto j hj d'⟩)
      have eq' := Fintype.card_congr e
      have power : (2:ℕ)^j = 2^t := by simpa using eq.trans eq'.symm
      exact (Nat.pow_lt_pow_right (by decide : 1 < 2) lt).ne power
    have large : 3 ≤ 2^t := by
      have h := Nat.pow_le_pow_right (by decide : 0 < 2) ht
      omega
    obtain ⟨mate,inv,chord,edges⟩ := chordMatching large D ring deg
    have goal : ∃ n k : ℕ, 3 ≤ n ∧ 2 ≤ k ∧ cycleGraph n ⊑ D ∧ (n+1=2^k ∨ n+2=2^k) := by
      by_cases big : 5 ≤ t
      · exact hamilton t big D deg mate inv chord edges sym (exclude 3 (Or.inl rfl))
          (exclude 6 (Or.inr rfl)) noshort
      · obtain ⟨m,cases,copy⟩ := smallRingResult ht (by omega) D ring deg
        rcases cases with rfl | rfl | rfl | ⟨rfl,lt⟩ | ⟨rfl,lt⟩
        · exact (exclude 3 (Or.inl rfl) copy).elim
        · exact (exclude 6 (Or.inr rfl) copy).elim
        · exact ⟨7,3,by decide,by decide,copy,Or.inl rfl⟩
        · have less : 2 < t := by
            by_contra! h
            exact lt.not_ge (Nat.pow_le_pow_right (by decide : 0 < 2) h)
          exact (noshort 2 (by decide) less copy).elim
        · have less : 3 < t := by
            by_contra! h
            exact lt.not_ge (Nat.pow_le_pow_right (by decide : 0 < 2) h)
          exact (noshort 3 (by decide) less copy).elim
    obtain ⟨n,k,hn,hk,⟨d⟩,lengths⟩ := goal
    let i : Fin n := ⟨0,by omega⟩
    obtain ⟨f,hf⟩ := trans (iso (d i))
    obtain ⟨d',hit⟩ := backToRoot (iso.toCopy.comp d) f ⟨i,hf.symm⟩
    exact ⟨n,k,d',hn,hk,hit,lengths⟩
  · push Not at trans
    obtain ⟨n,k,d,f,hn,hk,hit,lengths⟩ := partialOrbits V G r conn cubic bridges trans away
      ⟨t,ht,⟨c⟩⟩ (fun k hk => forcedOrbit (forced k hk))
    obtain ⟨d',h⟩ := backToRoot d f hit
    exact ⟨n,k,d',hn,hk,h,lengths⟩

end OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R2_H2_R1
