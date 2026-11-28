import OMAReductions.R_Erdos64_erdos_64_R1_H1_R1_H1_R2
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.GroupTheory.Sylow
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Tactic.IntervalCases

/-!
Reduce the forced-root step of PR #27543 by rerouting a dyadic cycle along a
third internally disjoint path. The rebuilt cycles are tracked with exact
vertex ranges. The transitive case is discharged here using Chad Mazzola's
merged half-order and rooted asymmetry proof from PR #28718
(ff36b7b18d9e661ecc638cda828fffeb38bec073). The site allows only Mathlib
imports after the parent import, so its necessary lemmas are included.
-/
namespace OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R2_H2_R2
open SimpleGraph

/-- Proper root orbit of at most two vertices. -/
def H1 : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] (r : V),
    G.Connected → (∀ v, G.degree v = 3) →
    (∀ ⦃a b⦄, G.Adj a b → ¬ G.IsBridge s(a,b)) →
    (∃ v, ∀ f : G ≃g G, f r ≠ v) →
    (∀ n, n = 3 ∨ n = 6 → ∀ c : (cycleGraph n).Copy G, ∀ f : G ≃g G, f r ∉ Set.range c) →
    (∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ G) →
    (∀ k : ℕ, 2 ≤ k → ∀ c : (cycleGraph (2^k)).Copy G, ∀ f : G ≃g G, f r ∈ Set.range c) →
    ({v | ∃ f : G ≃g G, f r=v}.ncard ≤ 2) →
    (let dyadic := fun d : ℕ => ∃ k : ℕ, 2 ≤ k ∧ d = 2^k
     let near := fun d : ℕ => 3 ≤ d ∧ ∃ k : ℕ, 2 ≤ k ∧ (d+1=2^k ∨ d+2=2^k)
     ∀ (x y : V) (A B P : List V), (x::y::(A++B++P)).Nodup →
       (∀ L ∈ [A,B,P], (x::(L++[y])).IsChain G.Adj) →
       dyadic (A.length+B.length+2) →
       (near (A.length+P.length+2) →
         (∀ f : G ≃g G, f r ∈ B) ∧ ¬ near (B.length+P.length+2)) ∧
       (dyadic (A.length+P.length+2) → dyadic (B.length+P.length+2) →
         ∀ f : G ≃g G, f r = x ∨ f r = y)) →
    ∃ (n k : ℕ) (c : (cycleGraph n).Copy G) (f : G ≃g G),
      3 ≤ n ∧ 2 ≤ k ∧ f r ∈ Set.range c ∧ (n+1=2^k ∨ n+2=2^k)

/-- Proper root orbit of at least three vertices. -/
def H2 : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] (r : V),
    G.Connected → (∀ v, G.degree v = 3) →
    (∀ ⦃a b⦄, G.Adj a b → ¬ G.IsBridge s(a,b)) →
    (∃ v, ∀ f : G ≃g G, f r ≠ v) →
    (∀ n, n = 3 ∨ n = 6 → ∀ c : (cycleGraph n).Copy G, ∀ f : G ≃g G, f r ∉ Set.range c) →
    (∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ G) →
    (∀ k : ℕ, 2 ≤ k → ∀ c : (cycleGraph (2^k)).Copy G, ∀ f : G ≃g G, f r ∈ Set.range c) →
    (3 ≤ {v | ∃ f : G ≃g G, f r=v}.ncard) →
    (∀ (k : ℕ), 2 ≤ k → ∀ (c : (cycleGraph (2^k)).Copy G) (x y : Fin (2^k)),
      (x=y ∨ 3 ≤ k) → ¬ (∀ j, (∃ f : G ≃g G, f r=c j) ↔ j≠x ∧ j≠y)) →
    (let dyadic := fun d : ℕ => ∃ k : ℕ, 2 ≤ k ∧ d = 2^k
     let near := fun d : ℕ => 3 ≤ d ∧ ∃ k : ℕ, 2 ≤ k ∧ (d+1=2^k ∨ d+2=2^k)
     ∀ (x y : V) (A B P : List V), (x::y::(A++B++P)).Nodup →
       (∀ L ∈ [A,B,P], (x::(L++[y])).IsChain G.Adj) →
       dyadic (A.length+B.length+2) →
       (near (A.length+P.length+2) →
         (∀ f : G ≃g G, f r ∈ B) ∧ 3 ≤ B.length ∧ ¬ near (B.length+P.length+2)) ∧
       (dyadic (A.length+P.length+2) → ¬ dyadic (B.length+P.length+2))) →
    ∃ (n k : ℕ) (c : (cycleGraph n).Copy G) (f : G ≃g G),
      3 ≤ n ∧ 2 ≤ k ∧ f r ∈ Set.range c ∧ (n+1=2^k ∨ n+2=2^k)

/-- The cyclic-list argument of PR #27543, with an exact vertex range. -/
theorem exactRing {V : Type*} (G : SimpleGraph V) (l : List V)
    (large : 3 ≤ l.length) (distinct : l.Nodup) (path : l.IsChain G.Adj)
    (close : ∀ h : l ≠ [], G.Adj (l.getLast h) (l.head h)) :
    ∃ c : (cycleGraph l.length).Copy G, ∀ v, v ∈ l ↔ v ∈ Set.range c := by
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
  intro v
  exact List.mem_iff_get

/-- A simple path spanning a proper automorphism orbit in a connected cubic
graph closes up as soon as it has at least three vertices. -/
theorem orbitPathCloses {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : V) (conn : G.Connected) (cubic : ∀ v, G.degree v = 3)
    (proper : ∃ v, ∀ f : G ≃g G, f r ≠ v)
    (l : List V) (large : 3 ≤ l.length) (distinct : l.Nodup)
    (chain : l.IsChain G.Adj) (covers : ∀ v, v ∈ l ↔ ∃ f : G ≃g G, f r = v) :
    ∃ c : (cycleGraph l.length).Copy G, r ∈ Set.range c := by
  classical
  have root : r ∈ l := (covers _).mpr ⟨SimpleGraph.Iso.refl, rfl⟩
  have invariant (f : G ≃g G) (v : V) : f v ∈ l ↔ v ∈ l := by
    rw [covers,covers]
    constructor
    · rintro ⟨g,h⟩
      exact ⟨g.trans f.symm,by change f.symm (g r)=v; rw [h,f.symm_apply_apply]⟩
    · rintro ⟨g,h⟩
      exact ⟨g.trans f,by change f (g r)=f v; rw [h]⟩
  have move (x y : V) (hx : x∈l) (hy : y∈l) : ∃ f : G ≃g G, f x=y := by
    obtain ⟨g,hg⟩ := (covers _).mp hx
    obtain ⟨h,hh⟩ := (covers _).mp hy
    exact ⟨g.symm.trans h,by change h (g.symm x)=y; rw [←hg,g.symm_apply_apply,hh]⟩
  obtain ⟨outside,ho⟩ := proper
  have exitEdge : ∃ x∈l, ∃ z, z∉l ∧ G.Adj x z := by
    by_contra! closed
    obtain ⟨walk⟩ := conn.preconnected r outside
    have follow {a b : V} (p : G.Walk a b) (ha : a∈l) : b∈l := by
      induction p with
      | nil => exact ha
      | cons e _ ih =>
        apply ih
        by_contra missing
        exact closed _ ha _ missing e
    obtain ⟨f,h⟩ := (covers _).mp (follow walk root)
    exact ho f h
  obtain ⟨u,hu,z,hz,uz⟩ := exitEdge
  have third (x : V) (hx : x∈l) : ∃ w, w∉l ∧ G.Adj x w := by
    obtain ⟨f,eq⟩ := move u x hu hx
    exact ⟨f z,fun h => hz ((invariant f z).mp h),eq ▸ f.map_rel_iff.mpr uz⟩
  have sat (x a b w : V) (hx : x∈l) (ha : a∈l) (hb : b∈l) (hw : w∈l)
      (xa : G.Adj x a) (xb : G.Adj x b) (xw : G.Adj x w) (ab : a≠b) :
      w=a ∨ w=b := by
    by_contra! h
    obtain ⟨t,ht,xt⟩ := third x hx
    have subset : ({a,b,w,t} : Finset V) ⊆ G.neighborFinset x := by
      intro v hv
      simp only [Finset.mem_insert,Finset.mem_singleton] at hv
      rcases hv with rfl|rfl|rfl|rfl <;> simpa
    have bound := Finset.card_le_card subset
    have at' : a≠t := fun e => ht (e ▸ ha)
    have bt : b≠t := fun e => ht (e ▸ hb)
    have wt : w≠t := fun e => ht (e ▸ hw)
    simp [ab,Ne.symm h.1,Ne.symm h.2,at',bt,wt,cubic] at bound
  let e := l.get
  have mem (i : Fin l.length) : e i ∈ l := List.get_mem ..
  have inj : Function.Injective e := distinct.injective_get
  let i₀ : Fin l.length := ⟨0,by omega⟩
  let i₁ : Fin l.length := ⟨1,by omega⟩
  let i₂ : Fin l.length := ⟨2,by omega⟩
  let last : Fin l.length := ⟨l.length-1,by omega⟩
  have step (i j : Fin l.length) (h : j.val=i.val+1) : G.Adj (e i) (e j) := by
    simpa only [e,List.get_eq_getElem,h] using chain.getElem i.val (by omega)
  obtain ⟨f,hf⟩ := move (e i₁) (e i₀) (mem _) (mem _)
  have pair (i : Fin l.length) (hi : G.Adj (e i₁) (e i)) :
      G.Adj (e i₀) (f (e i)) := hf ▸ f.map_rel_iff.mpr hi
  have other : ∃ j : Fin l.length, j≠i₁ ∧ G.Adj (e i₀) (e j) := by
    have find (i : Fin l.length) : ∃ j, e j = f (e i) :=
      List.mem_iff_get.mp ((invariant f _).mpr (mem i))
    obtain ⟨a,ha⟩ := find i₀
    obtain ⟨b,hb⟩ := find i₂
    by_cases h : a=i₁
    · refine ⟨b,?_,hb ▸ pair _ (step i₁ i₂ rfl)⟩
      intro eq
      have same := inj (f.injective (ha.symm.trans ((eq.trans h.symm) ▸ hb)))
      exact (by decide : (0:ℕ)≠2) (congrArg Fin.val same)
    · exact ⟨a,h,ha ▸ pair _ (step i₀ i₁ rfl).symm⟩
  obtain ⟨j,ne,edge⟩ := other
  have endpt : j=last := by
    by_contra h
    have pos : j.val≠0 := fun eq => edge.ne (congrArg e (Fin.ext eq.symm))
    have mid : j.val≠1 := fun eq => ne (Fin.ext eq)
    have top : j.val≠l.length-1 := fun eq => h (Fin.ext eq)
    let a : Fin l.length := ⟨j.val-1,by omega⟩
    let b : Fin l.length := ⟨j.val+1,by omega⟩
    have ab : e a≠e b := by
      intro q
      have t := congrArg Fin.val (inj q)
      dsimp [a,b] at t
      omega
    rcases sat _ _ _ _ (mem j) (mem a) (mem b) (mem i₀)
        (step a j (by dsimp [a]; omega)).symm (step j b rfl) edge.symm ab with q|q <;>
      have t := congrArg Fin.val (inj q) <;> dsimp [a,b,i₀] at t <;> omega
  have close (h : l≠[]) : G.Adj (l.getLast h) (l.head h) := by
    subst j
    simpa [e,last,i₀,List.getLast_eq_getElem,List.head_eq_getElem] using edge.symm
  obtain ⟨c,hc⟩ := exactRing G l large distinct chain close
  exact ⟨c,(hc _).mp root⟩

/-- A cyclic interval of orbit vertices can be read from any starting label.
If its length is one or two below a power of two, closing the interval gives
the required cycle through the original root. -/
theorem orbitIntervalSolves {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : V) (conn : G.Connected) (cubic : ∀ v, G.degree v = 3)
    (proper : ∃ v, ∀ f : G ≃g G, f r ≠ v)
    {n m k : ℕ} (c : (cycleGraph n).Copy G) (start : Fin n)
    (large : 3 ≤ m) (fits : m ≤ n) (hk : 2 ≤ k) (near : m+1 = 2^k ∨ m+2 = 2^k)
    (hit : ∀ f : G ≃g G, f r ∈ Set.range c)
    (interval : ∀ i : Fin n, (∃ f : G ≃g G, f r = c (i+start)) ↔ i.val < m) :
    ∃ (d t : ℕ) (w : (cycleGraph d).Copy G),
      3 ≤ d ∧ 2 ≤ t ∧ r ∈ Set.range w ∧ (d+1 = 2^t ∨ d+2 = 2^t) := by
  let : NeZero n := ⟨by omega⟩
  let label (i : Fin m) : Fin n := ⟨i.val,lt_of_lt_of_le i.isLt fits⟩
  let v (i : Fin m) := c (label i + start)
  let l := List.ofFn v
  have len : l.length = m := List.length_ofFn
  have unique : Function.Injective v := by
    intro i j h
    exact Fin.ext (congrArg (Fin.val (n := n)) (add_right_cancel (c.injective h) : label i = label j))
  have clean : l.Nodup := List.nodup_ofFn_ofInjective unique
  have path : l.IsChain G.Adj := by
    apply List.isChain_iff_getElem.mpr
    intro j hj
    have hj' : j+1 < m := by omega
    let a : Fin m := ⟨j,by omega⟩
    let b : Fin m := ⟨j+1,hj'⟩
    have e : (cycleGraph n).Adj (label a) (label b) :=
      pathGraph_le_cycleGraph (pathGraph_adj.mpr (Or.inl rfl))
    have rot : (cycleGraph n).Adj (label a+start) (label b+start) := by
      simpa only [cycleGraph_adj',add_sub_add_right_eq_sub] using e
    simpa [l,v,a,b] using c.toHom.map_rel' rot
  have covers (x : V) : x ∈ l ↔ ∃ f : G ≃g G, f r = x := by
    rw [show l = List.ofFn v from rfl,List.mem_ofFn']
    constructor
    · rintro ⟨j,rfl⟩
      exact (interval (label j)).mpr j.isLt
    · rintro ⟨f,rfl⟩
      obtain ⟨j,hj⟩ := hit f
      have eq : j-start+start = j := sub_add_cancel .. 
      have lt := (interval (j-start)).mp ⟨f,by rw [eq,hj]⟩
      exact ⟨⟨(j-start).val,lt⟩,by change c (j-start+start) = f r; rw [eq,hj]⟩
  obtain ⟨w,hw⟩ := orbitPathCloses G r conn cubic proper l (by omega) clean path covers
  exact ⟨l.length,k,w,by omega,hk,hw,by simpa [len] using near⟩

/-- One omitted label, or two consecutive omitted labels, on a dyadic
cycle force the rooted target whenever at least three orbit vertices remain. -/
theorem omittedBlockSolves {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : V) (conn : G.Connected) (cubic : ∀ v, G.degree v = 3)
    (proper : ∃ v, ∀ f : G ≃g G, f r ≠ v)
    {k d : ℕ} (hk : 2 ≤ k) (gap : d = 1 ∨ d = 2) (large : 3 ≤ 2^k-d)
    (c : (cycleGraph (2^k)).Copy G) (q : Fin (2^k))
    (hit : ∀ f : G ≃g G, f r ∈ Set.range c)
    (orbit : ∀ j, (∃ f : G ≃g G, f r = c j) ↔ j ≠ q ∧ (d = 2 → j ≠ q+1)) :
    ∃ (n t : ℕ) (w : (cycleGraph n).Copy G),
      3 ≤ n ∧ 2 ≤ t ∧ r ∈ Set.range w ∧ (n+1 = 2^t ∨ n+2 = 2^t) := by
  let a : Fin (2^k) := ⟨2^k-d,by omega⟩
  let start := q-a
  have first : a+start = q := by simp [start]
  apply orbitIntervalSolves G r conn cubic proper c start (m := 2^k-d) large
    (by omega) hk (by omega) hit
  intro i
  rw [orbit,←first]
  have h (hd : d = 2) : (a+1 : Fin (2^k)).val = 2^k-1 := by
    have one : (1 : Fin (2^k)).val = 1 := by rw [Fin.val_one',Nat.mod_eq_of_lt (by omega)]
    rw [Fin.val_add,one]
    change (2^k-d+1) % (2^k) = 2^k-1
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have eq : a+start+1 = (a+1)+start := by abel
  rw [eq]
  simp only [ne_eq,add_left_inj,Fin.ext_iff]
  change (¬ i.val = 2^k-d) ∧ (d = 2 → ¬ i.val = (a+1).val) ↔ i.val < 2^k-d
  rcases gap with hd|hd
  · omega
  · rw [h hd]
    omega

/-- A transitive graph of degree two covered by two connected components has
a cycle of either the full order or half the order. -/
private theorem componentRing {S : Type} [Fintype S] (K : SimpleGraph S)
    (trans : ∀ x y : S, ∃ f : K ≃g K, f x = y)
    (degree : ∀ x, (K.neighborSet x).ncard = 2)
    (a b : S) (cover : ∀ x, K.Reachable a x ∨ K.Reachable b x) :
    ∃ (n : ℕ) (_c : (cycleGraph n).Copy K),
      3 ≤ n ∧ (n = Fintype.card S ∨ n+n = Fintype.card S) := by
  classical
  let A := K.connectedComponentMk a
  let B := K.connectedComponentMk b
  have union : A.supp ∪ B.supp = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    rcases cover x with h|h
    · exact Or.inl (ConnectedComponent.sound h.symm)
    · exact Or.inr (ConnectedComponent.sound h.symm)
  obtain ⟨f,hf⟩ := trans a b
  have maps : f.connectedComponentEquiv A = B := by
    change K.connectedComponentMk (f a) = K.connectedComponentMk b
    rw [hf]
  have equal : A.supp.ncard = B.supp.ncard := by
    have e := ConnectedComponent.isoEquivSupp f A
    rw [←maps]
    exact Nat.card_congr e
  have count : A.supp.ncard = Fintype.card S ∨ A.supp.ncard+A.supp.ncard = Fintype.card S := by
    by_cases h : A = B
    · left
      rw [←h,Set.union_self] at union
      simp [union]
    · right
      have dis : Disjoint A.supp B.supp := Set.disjoint_left.mpr fun _ ha hb =>
        h (ConnectedComponent.eq_of_common_vertex ha hb)
      have cnt := Set.ncard_union_eq dis (Set.toFinite _) (Set.toFinite _)
      rw [union,Set.ncard_univ,equal] at cnt
      rw [equal]
      simpa only [Nat.card_eq_fintype_card] using cnt.symm
  have cyc : K.IsCycles := fun {x} _ => degree x
  obtain ⟨p,hp,verts⟩ := cyc.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
    (c := A) (v := a) rfl (Set.nonempty_of_ncard_ne_zero (by rw [degree]; decide))
  have support : {x | x ∈ p.support.tail}=A.supp := by
    ext x
    rw [←verts,Walk.mem_verts_toSubgraph]
    change x ∈ p.support.tail ↔ x ∈ p.support
    cases p with
    | nil => exact (hp.not_nil .nil).elim
    | cons e q => simp [Walk.support_cons]; rintro rfl; exact q.end_mem_support
  have size : p.length = A.supp.ncard := by
    rw [←support]
    have ht := hp.support_nodup
    have eq : ({x | x ∈ p.support.tail} : Set S) = ↑p.support.tail.toFinset := by ext; simp
    rw [eq,Set.ncard_coe_finset,List.toFinset_card_of_nodup ht,List.length_tail,Walk.length_support]
    omega
  obtain ⟨c⟩ := (cycleGraph_isContained_iff hp.three_le_length).mpr ⟨a,p,hp,rfl⟩
  exact ⟨_,c,hp.three_le_length,size ▸ count⟩

/-- Compress the two runs of orbit vertices into one indexed list with a
single possible missing edge. The missing edge may occur anywhere. -/
private theorem twoRunSolves {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : V) (cubic : ∀ v, G.degree v = 3) {m k : ℕ} (hm : 6 ≤ m) (hk : 3 ≤ k)
    (total : m+2 = 2^k) (e : Fin m ↪ V) (t : ℕ)
    (rangeOrbit : ∀ v, v ∈ Set.range e ↔ ∃ f : G ≃g G, f r = v)
    (step : ∀ (i j : Fin m), i.val+1 = j.val → j.val ≠ t → G.Adj (e i) (e j))
    (external : ∃ (i : Fin m) (z : V), G.Adj (e i) z ∧ z ∉ Set.range e) :
    ∃ (n s : ℕ) (w : (cycleGraph n).Copy G),
      3 ≤ n ∧ 2 ≤ s ∧ r ∈ Set.range w ∧ (n+1 = 2^s ∨ n+2 = 2^s) := by
  classical
  let K := G.comap e
  let E := Equiv.ofInjective e e.injective
  have lift (f : G ≃g G) : ∃ g : K ≃g K, ∀ i, e (g i) = f (e i) := by
    have inv (v : V) : v ∈ Set.range e ↔ f v ∈ Set.range e := by
      rw [rangeOrbit,rangeOrbit]
      constructor
      · rintro ⟨g,h⟩
        exact ⟨g.trans f,by change f (g r) = f v; rw [h]⟩
      · rintro ⟨g,h⟩
        exact ⟨g.trans f.symm,by change f.symm (g r) = v; rw [h,f.symm_apply_apply]⟩
    let g := E.trans ((f.toEquiv.subtypeEquiv inv).trans E.symm)
    have hg (i) : e (g i) = f (e i) := Equiv.apply_ofInjective_symm e.injective _
    exact ⟨⟨g,by intro i j; change G.Adj (e (g i)) (e (g j)) ↔ _; rw [hg,hg]; exact f.map_rel_iff⟩,hg⟩
  have trans (i j : Fin m) : ∃ g : K ≃g K, g i = j := by
    obtain ⟨f,hf⟩ := (rangeOrbit _).mp ⟨i,rfl⟩
    obtain ⟨g,hg⟩ := (rangeOrbit _).mp ⟨j,rfl⟩
    obtain ⟨h,hh⟩ := lift (f.symm.trans g)
    apply Exists.intro h
    apply e.injective
    rw [hh]
    change g (f.symm (e i)) = e j
    rw [←hf,f.symm_apply_apply,hg]
  have same (i j : Fin m) : K.degree i = K.degree j := by
    obtain ⟨g,rfl⟩ := trans i j
    exact (g.degree_eq i).symm
  obtain ⟨u,z,uz,hz⟩ := external
  have upper : K.degree u < 3 := by
    let T := (K.neighborFinset u).map e
    have sub : T ⊆ G.neighborFinset (e u) := by
      intro x hx
      obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hx
      exact (G.mem_neighborFinset _ _).mpr ((K.mem_neighborFinset _ _).mp hv)
    have missing : z ∉ T := fun h => by
      obtain ⟨v,_,eq⟩ := Finset.mem_map.mp h
      exact hz ⟨v,eq⟩
    have h := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨sub,fun eq => missing (eq ▸ (G.mem_neighborFinset _ _).mpr uz)⟩)
    simpa [T,cubic] using h
  let j := if t ≤ 2 then 3 else 0
  have h₁ : j+1 ≠ t := by dsimp [j]; split <;> omega
  have h₂ : j+2 ≠ t := by dsimp [j]; split <;> omega
  have fit : j+2 < m := by dsimp [j]; split <;> omega
  let a : Fin m := ⟨j,by omega⟩
  let b : Fin m := ⟨j+1,by omega⟩
  let c : Fin m := ⟨j+2,fit⟩
  have ab : K.Adj a b := step a b rfl h₁
  have bc : K.Adj b c := step b c rfl h₂
  have ac : a ≠ c := fun eq => by have h := congrArg Fin.val eq; dsimp [a,c] at h; omega
  have lower : 2 ≤ K.degree b := by
    have sub : ({a,c} : Finset _) ⊆ K.neighborFinset b := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl|hx
      · exact (K.mem_neighborFinset _ _).mpr ab.symm
      · obtain rfl := Finset.mem_singleton.mp hx
        exact (K.mem_neighborFinset _ _).mpr bc
    simpa [ac] using Finset.card_le_card sub
  have degree (x : Fin m) : (K.neighborSet x).ncard = 2 := by
    have hx := same b x
    have hu := same u x
    rw [Set.ncard_eq_toFinset_card']
    change K.degree x = 2
    omega
  let p : Fin m := ⟨0,by omega⟩
  let q : Fin m := ⟨min t (m-1),by omega⟩
  have cover (x : Fin m) : K.Reachable p x ∨ K.Reachable q x := by
    obtain ⟨i,hi⟩ := x
    induction i with
    | zero => exact Or.inl .rfl
    | succ i ih =>
      by_cases h : i+1 = t
      · right
        have eq : q=⟨i+1,hi⟩ := Fin.ext (by dsimp [q]; omega)
        rw [eq]
      · have edge : K.Adj ⟨i,by omega⟩ ⟨i+1,hi⟩ := step _ _ rfl h
        exact (ih (by omega)).imp (·.trans edge.reachable) (·.trans edge.reachable)
  obtain ⟨n,w,hn,count⟩ := componentRing K trans degree p q cover
  let emb : K.Copy G := ⟨⟨e,fun h => h⟩,e.injective⟩
  let v := w ⟨0,by omega⟩
  obtain ⟨f,hf⟩ := (rangeOrbit _).mp ⟨v,rfl⟩
  have hit : f r ∈ Set.range (emb.comp w) := ⟨⟨0,by omega⟩,hf.symm⟩
  let w' := f.symm.toCopy.comp (emb.comp w)
  obtain ⟨idx,hi⟩ := hit
  have hit' : r ∈ Set.range w' := ⟨idx,by change f.symm ((emb.comp w) idx) = r; rw [hi,f.symm_apply_apply]⟩
  simp only [Fintype.card_fin] at count
  rcases count with h|h
  · exact ⟨n,k,w',hn,by omega,hit',Or.inr (by omega)⟩
  · obtain ⟨s,rfl⟩ : ∃ s, k = s+1 := ⟨k-1,by omega⟩
    rw [pow_succ] at total
    exact ⟨n,s,w',hn,by omega,hit',Or.inl (by omega)⟩

/-- Any two omitted labels on a dyadic cycle of order at least eight force
a cycle through the root of the required length. -/
theorem twoOmissionsSolve {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : V) (cubic : ∀ v, G.degree v = 3) {k : ℕ} (hk : 3 ≤ k)
    (c : (cycleGraph (2^k)).Copy G) (x y : Fin (2^k)) (hne : x ≠ y)
    (hit : ∀ f : G ≃g G, f r ∈ Set.range c)
    (omits : ∀ j, (∃ f : G ≃g G, f r = c j) ↔ j ≠ x ∧ j ≠ y) :
    ∃ (n s : ℕ) (w : (cycleGraph n).Copy G),
      3 ≤ n ∧ 2 ≤ s ∧ r ∈ Set.range w ∧ (n+1 = 2^s ∨ n+2 = 2^s) := by
  have big : 8 ≤ 2^k := Nat.pow_le_pow_right (by decide : 0 < 2) hk
  let m := 2^k-2
  have hm : 6 ≤ m := by dsimp [m]; omega
  have total : m+2 = 2^k := by dsimp [m]; omega
  let q := y-x
  have nonzero : q ≠ 0 := sub_ne_zero.mpr hne.symm
  have pos : 0 < q.val := by
    by_contra! h
    exact nonzero (Fin.ext (by simpa using h))
  let t := q.val-1
  let label (i : Fin m) : Fin (2^k) :=
    ⟨if i.val < t then i.val+1 else i.val+2,by split <;> omega⟩
  have labels (i : Fin m) : (label i).val ≠ 0 ∧ (label i).val ≠ q.val := by
    dsimp [label,t]; split <;> omega
  have inject : Function.Injective label := by
    intro i j h
    have eq := congrArg Fin.val h
    apply Fin.ext
    dsimp [label] at eq
    split at eq <;> split at eq <;> omega
  let e : Fin m ↪ V := ⟨fun i => c (label i+x),fun _ _ h =>
    inject (add_right_cancel (c.injective h))⟩
  have onto (j : Fin (2^k)) (h₀ : j.val ≠ 0) (hq : j.val ≠ q.val) : ∃ i, label i = j := by
    by_cases h : j.val < q.val
    · refine ⟨⟨j.val-1,by omega⟩,Fin.ext ?_⟩
      dsimp [label,t]; split <;> omega
    · refine ⟨⟨j.val-2,by omega⟩,Fin.ext ?_⟩
      dsimp [label,t]; split <;> omega
  have rot (j : Fin (2^k)) : (∃ f : G ≃g G, f r = c (j+x)) ↔ j ≠ 0 ∧ j ≠ q := by
    rw [omits]
    have h : q+x = y := sub_add_cancel ..
    nth_rw 1 [←h]
    simp
  have covers (v : V) : v ∈ Set.range e ↔ ∃ f : G ≃g G, f r = v := by
    constructor
    · rintro ⟨i,rfl⟩
      exact (rot _).mpr ⟨fun h => (labels i).1 (congrArg Fin.val h),
        fun h => (labels i).2 (congrArg Fin.val h)⟩
    · rintro ⟨f,rfl⟩
      obtain ⟨j,eq⟩ := hit f
      have good := (rot (j-x)).mp ⟨f,by simpa using eq.symm⟩
      obtain ⟨i,hi⟩ := onto (j-x) (fun h => good.1 (Fin.ext h)) (fun h => good.2 (Fin.ext h))
      exact ⟨i,by change c (label i+x) = f r; rw [hi,sub_add_cancel,eq]⟩
  have edge (a b : Fin (2^k)) (h : a.val+1 = b.val) : G.Adj (c (a+x)) (c (b+x)) := by
    have base : (cycleGraph (2^k)).Adj a b := pathGraph_le_cycleGraph (pathGraph_adj.mpr (Or.inl h))
    apply c.toHom.map_rel'
    simpa only [cycleGraph_adj',add_sub_add_right_eq_sub] using base
  apply twoRunSolves G r cubic hm hk total e t covers
  · intro i j h hj
    apply edge
    dsimp [label]
    split <;> split <;> omega
  · let i : Fin m := ⟨0,by omega⟩
    let a : Fin (2^k) := ⟨(label i).val-1,by have := (label i).isLt; omega⟩
    have pred : a.val+1 = (label i).val := by have := (labels i).1; dsimp [a]; omega
    refine ⟨i,c (a+x),(edge a _ pred).symm,?_⟩
    intro inside
    have avoid := (rot a).mp ((covers _).mp inside)
    by_cases h : 0 < t
    · apply avoid.1
      apply Fin.ext
      simp [a,label,i,h]
    · apply avoid.2
      apply Fin.ext
      simp [a,label,i,show ¬0 < t from h]
      dsimp [t] at h
      omega

/-- Two paths from x to y with disjoint interiors give a cycle whose
vertex set is exactly their union. Lists contain only interior vertices. -/
theorem twoArmCycle {V : Type*} (G : SimpleGraph V) (x y : V) (A B : List V)
    (distinct : (x::y::(A++B)).Nodup)
    (left : (x::(A++[y])).IsChain G.Adj) (right : (x::(B++[y])).IsChain G.Adj)
    (large : 3 ≤ A.length+B.length+2) :
    ∃ c : (cycleGraph (A.length+B.length+2)).Copy G,
      ∀ z, z ∈ Set.range c ↔ z=x ∨ z=y ∨ z∈A ∨ z∈B := by
  let l := x :: (A ++ y :: B.reverse)
  have back : (y :: (B.reverse ++ [x])).IsChain G.Adj := by
    have h := List.isChain_reverse.mpr (right.imp (fun _ _ e => e.symm))
    simpa using h
  have join := List.IsChain.append_overlap (l₁ := x::A) (l₂ := [y])
    (l₃ := B.reverse++[x]) left back (by simp)
  have closed : (l++[x]).IsChain G.Adj := by
    simpa [l,List.append_assoc] using join
  have size : l.length = A.length+B.length+2 := by simp [l]; omega
  have nd : l.Nodup := by
    simp only [List.nodup_cons,List.nodup_append',List.mem_append,List.mem_cons,
      not_or] at distinct
    simp only [l,List.nodup_cons,List.nodup_append',List.mem_cons,List.mem_append,
      List.mem_reverse,List.nodup_reverse,not_or,List.disjoint_cons_right,List.disjoint_reverse_right]
    tauto
  obtain ⟨c,hc⟩ := exactRing G l (size ▸ large) nd closed.left_of_append (by
    intro ne
    exact closed.rel_getLast_head_of_append ne (by simp))
  have claim : ∃ c : (cycleGraph l.length).Copy G, ∀ z, z∈Set.range c ↔
      z=x ∨ z=y ∨ z∈A ∨ z∈B := by
    refine ⟨c,fun z => (hc z).symm.trans ?_⟩
    simp only [l,List.mem_cons,List.mem_append,List.mem_reverse]
    tauto
  rwa [size] at claim

/-- In a rooted obstruction, every successful-length reroute confines the
entire forced orbit to the discarded interior. If all three pairwise cycles
are dyadic, the orbit is contained in the two common endpoints. -/
theorem thetaObstruction {V : Type} (G : SimpleGraph V) (r : V)
    (forced : ∀ k : ℕ, 2 ≤ k → ∀ c : (cycleGraph (2^k)).Copy G,
      ∀ f : G ≃g G, f r ∈ Set.range c)
    (obstruction : ¬ ∃ (n k : ℕ) (c : (cycleGraph n).Copy G) (f : G ≃g G),
      3 ≤ n ∧ 2 ≤ k ∧ f r ∈ Set.range c ∧ (n+1=2^k ∨ n+2=2^k)) :
     let dyadic := fun d : ℕ => ∃ k : ℕ, 2 ≤ k ∧ d = 2^k
     let near := fun d : ℕ => 3 ≤ d ∧ ∃ k : ℕ, 2 ≤ k ∧ (d+1=2^k ∨ d+2=2^k)
     ∀ (x y : V) (A B P : List V), (x::y::(A++B++P)).Nodup →
       (∀ L ∈ [A,B,P], (x::(L++[y])).IsChain G.Adj) →
       dyadic (A.length+B.length+2) →
       (near (A.length+P.length+2) →
         (∀ f : G ≃g G, f r ∈ B) ∧ ¬ near (B.length+P.length+2)) ∧
       (dyadic (A.length+P.length+2) → dyadic (B.length+P.length+2) →
         ∀ f : G ≃g G, f r = x ∨ f r = y) := by
  dsimp only
  intro x y A B P clean paths base
  have pieces := clean
  simp only [List.nodup_cons,List.mem_cons,List.mem_append,not_or,List.nodup_append',
    List.disjoint_append_left] at pieces
  have ab : (x::y::(A++B)).Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.mem_append,not_or,List.nodup_append']
    tauto
  have ap : (x::y::(A++P)).Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.mem_append,not_or,List.nodup_append']
    tauto
  have bp : (x::y::(B++P)).Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.mem_append,not_or,List.nodup_append']
    tauto
  have hab := twoArmCycle G x y A B ab (paths A (by simp)) (paths B (by simp))
  have hap := twoArmCycle G x y A P ap (paths A (by simp)) (paths P (by simp))
  have hbp := twoArmCycle G x y B P bp (paths B (by simp)) (paths P (by simp))
  have covers (d : ℕ) (s : V → Prop) (dyad : ∃ k : ℕ, 2 ≤ k ∧ d=2^k)
      (build : 3 ≤ d → ∃ c : (cycleGraph d).Copy G, ∀ z, z ∈ Set.range c ↔ s z) :
      ∀ f : G ≃g G, s (f r) := by
    obtain ⟨k,hk,rfl⟩ := dyad
    have big : 4 ≤ 2^k := Nat.pow_le_pow_right (by decide : 0 < 2) hk
    obtain ⟨c,hc⟩ := build (by omega)
    exact fun f => (hc _).mp (forced k hk c f)
  have misses (d : ℕ) (s : V → Prop)
      (near : 3 ≤ d ∧ ∃ k : ℕ, 2 ≤ k ∧ (d+1=2^k ∨ d+2=2^k))
      (build : 3 ≤ d → ∃ c : (cycleGraph d).Copy G, ∀ z, z ∈ Set.range c ↔ s z) :
      ∀ f : G ≃g G, ¬ s (f r) := by
    obtain ⟨hd,k,hk,e⟩ := near
    obtain ⟨c,hc⟩ := build hd
    exact fun f h => obstruction ⟨d,k,c,f,hd,hk,(hc _).mpr h,e⟩
  have original := covers _ _ base hab
  constructor
  · intro near
    have excluded := misses _ _ near hap
    have confined (f : G ≃g G) : f r ∈ B := by
      rcases original f with h | h | h | h
      · exact (excluded f (Or.inl h)).elim
      · exact (excluded f (Or.inr (Or.inl h))).elim
      · exact (excluded f (Or.inr (Or.inr (Or.inl h)))).elim
      · exact h
    refine ⟨confined,?_⟩
    intro other
    let f : G ≃g G := RelIso.refl _
    exact misses _ _ other hbp f (Or.inr (Or.inr (Or.inl (confined f))))
  · intro da db f
    have h₁ := original f
    have h₂ := covers _ _ da hap f
    have h₃ := covers _ _ db hbp f
    have sepAB : A.Disjoint B := List.disjoint_of_nodup_append ab.of_cons.of_cons
    have sepAP : A.Disjoint P := List.disjoint_of_nodup_append ap.of_cons.of_cons
    have sepBP : B.Disjoint P := List.disjoint_of_nodup_append bp.of_cons.of_cons
    by_cases xeq : f r = x
    · exact Or.inl xeq
    by_cases yeq : f r = y
    · exact Or.inr yeq
    simp only [xeq,yeq,false_or] at h₁ h₂ h₃
    rcases h₁ with a|b
    · exact (h₃.elim (sepAB a) (sepAP a)).elim
    · exact (h₂.elim (fun a => sepAB a b) (sepBP b)).elim

/-- Counting possible images of the root inside a discarded path interior. -/
theorem orbitBoundOnList {V : Type} [Fintype V] (G : SimpleGraph V) (r : V) (B : List V)
    (h : ∀ f : G ≃g G, f r ∈ B) :
    {v | ∃ f : G ≃g G, f r=v}.ncard ≤ B.length := by
  classical
  have sub : {v | ∃ f : G ≃g G, f r=v} ⊆ (B.toFinset : Set V) := by
    rintro _ ⟨f,rfl⟩
    exact List.mem_toFinset.mpr (h f)
  calc
    _ ≤ (B.toFinset : Set V).ncard := Set.ncard_le_ncard sub
    _ = B.toFinset.card := Set.ncard_coe_finset _
    _ ≤ B.length := List.toFinset_card_le _

/-- An ear saving one or two edges on a dyadic cycle gives the required
length whenever the retained cycle has at least three vertices. -/
theorem savedEdges {a b p k : ℕ} (base : a+b+2=2^k) (large : 3 ≤ a+p+2)
    (hk : 2 ≤ k) (save : b=p+1 ∨ b=p+2) :
    3 ≤ a+p+2 ∧ ∃ j : ℕ, 2 ≤ j ∧ ((a+p+2)+1=2^j ∨ (a+p+2)+2=2^j) := by
  exact ⟨large,k,hk,by omega⟩

/-- The rerouted copy solves the rooted step if its length is one or two
below the original power and the discarded interior cannot hold the orbit.
The other reroute having a target length suffices at any orbit size. -/
theorem bypassSolves {V : Type} [Fintype V] (G : SimpleGraph V) (r x y : V)
    (A B P : List V) (clean : (x::y::(A++B++P)).Nodup)
    (paths : ∀ L ∈ [A,B,P], (x::(L++[y])).IsChain G.Adj)
    (forced : ∀ k : ℕ, 2 ≤ k → ∀ c : (cycleGraph (2^k)).Copy G,
      ∀ f : G ≃g G, f r ∈ Set.range c)
    {k : ℕ} (hk : 2 ≤ k) (base : A.length+B.length+2=2^k)
    (large : 3 ≤ A.length+P.length+2) (save : B.length=P.length+1 ∨ B.length=P.length+2)
    (hit : B.length < {v | ∃ f : G ≃g G, f r=v}.ncard ∨
      (3 ≤ B.length+P.length+2 ∧ ∃ j : ℕ, 2 ≤ j ∧
        ((B.length+P.length+2)+1=2^j ∨ (B.length+P.length+2)+2=2^j))) :
    ∃ (n k : ℕ) (c : (cycleGraph n).Copy G) (f : G ≃g G),
      3 ≤ n ∧ 2 ≤ k ∧ f r ∈ Set.range c ∧ (n+1=2^k ∨ n+2=2^k) := by
  by_contra h
  obtain ⟨confined,other⟩ := (thetaObstruction G r forced h x y A B P clean paths
    ⟨k,hk,base⟩).1 (savedEdges base large hk save)
  exact hit.elim (fun small => small.not_ge (orbitBoundOnList G r B confined)) other

/-- On any dyadic cycle of length at least four, a chord spanning two
edges settles the rooted step. At length at least eight, a chord spanning
three edges suffices if the forced orbit has at least three vertices. -/
theorem shortChordSolves {V : Type} [Fintype V] (G : SimpleGraph V) (r x y : V)
    (A B : List V) (clean : (x::y::(A++B)).Nodup)
    (left : (x::(A++[y])).IsChain G.Adj) (right : (x::(B++[y])).IsChain G.Adj)
    (chord : G.Adj x y)
    (forced : ∀ k : ℕ, 2 ≤ k → ∀ c : (cycleGraph (2^k)).Copy G,
      ∀ f : G ≃g G, f r ∈ Set.range c)
    {k : ℕ} (hk : 2 ≤ k) (base : A.length+B.length+2=2^k)
    (short : B.length=1 ∨ (B.length=2 ∧ 3 ≤ k ∧ 3 ≤ {v | ∃ f : G ≃g G, f r=v}.ncard)) :
    ∃ (n k : ℕ) (c : (cycleGraph n).Copy G) (f : G ≃g G),
      3 ≤ n ∧ 2 ≤ k ∧ f r ∈ Set.range c ∧ (n+1=2^k ∨ n+2=2^k) := by
  have four : 4 ≤ 2^k := Nat.pow_le_pow_right (by decide : 0<2) hk
  refine bypassSolves G r x y A B [] (by simpa using clean) ?_ forced hk base ?_ ?_ ?_
  · simp only [List.forall_mem_cons,List.not_mem_nil,IsEmpty.forall_iff,implies_true,and_true]
    exact ⟨left,right,by simpa using chord⟩
  · change 3 ≤ A.length+0+2
    rcases short with h|⟨h,three,_⟩
    · omega
    · have eight : 8 ≤ 2^k := Nat.pow_le_pow_right (by decide : 0<2) three
      omega
  · change B.length=0+1 ∨ B.length=0+2
    exact short.imp_right And.left
  · rcases short with h|⟨h,_,orb⟩
    · right
      simp only [List.length_nil,add_zero,h]
      exact ⟨by decide,2,by decide,Or.inl rfl⟩
    · exact Or.inl (by omega)

private theorem backToRoot {V : Type} {G : SimpleGraph V} {r : V} {n : ℕ}
    (c : (cycleGraph n).Copy G) (f : G ≃g G) (hit : f r ∈ Set.range c) :
    ∃ d : (cycleGraph n).Copy G, r ∈ Set.range d := by
  obtain ⟨i,hi⟩ := hit
  exact ⟨f.symm.toCopy.comp c,i,by change f.symm (c i) = r; rw [hi]; exact f.symm_apply_apply r⟩


namespace HalfOrder
open Function Fin.NatCast MulAction

/-- Four cyclically adjacent vertices with distinct opposite pairs form a square. -/
theorem square_of_four {V : Type*} {G : SimpleGraph V} {a b c d : V}
    (ab : G.Adj a b) (bc : G.Adj b c) (cd : G.Adj c d) (da : G.Adj d a)
    (ac : a ≠ c) (bd : b ≠ d) : cycleGraph 4 ⊑ G := by
  obtain ⟨c₄,_⟩ := exactRing G [a,b,c,d] (by simp)
    (by simp [ab.ne,ac,da.ne.symm,bc.ne,bd,cd.ne])
    (by simp [ab,bc,cd]) (by simpa using da)
  exact ⟨c₄⟩

/-- If every copy of a cycle uses r, then every automorphic image of r
lies in every copy, without a transitivity assumption. -/
theorem orbit_on_cycle {V : Type*} {G : SimpleGraph V} {n : ℕ}
    (r : V) (hit : ∀ c : (cycleGraph n).Copy G, r ∈ Set.range c)
    (c : (cycleGraph n).Copy G) (g : G ≃g G) : g r ∈ Set.range c := by
  obtain ⟨i,hi⟩ := hit (g.symm.toCopy.comp c)
  refine ⟨i,?_⟩
  change g.symm (c i) = r at hi
  simpa using congrArg g hi

/-- In a vertex-transitive graph, a length whose every cycle visits one
vertex can only be the full graph order. -/
theorem transitive_cycle_spans {V : Type*} [Fintype V] {G : SimpleGraph V} {n : ℕ}
    (r : V) (transitive : ∀ x, ∃ g : G ≃g G, g r = x)
    (hit : ∀ c : (cycleGraph n).Copy G, r ∈ Set.range c)
    (c : (cycleGraph n).Copy G) : n = Fintype.card V := by
  have onto : Surjective c := by
    intro x
    obtain ⟨g,rfl⟩ := transitive x
    exact orbit_on_cycle r hit c g
  simpa using Fintype.card_congr (Equiv.ofBijective c ⟨fun _ _ h => c.injective h,onto⟩)

/-- A vertex-transitive graph of order other than a power of two has a
dyadic cycle avoiding any specified vertex as soon as one such cycle exists. -/
theorem avoiding_cycle {V : Type*} [Fintype V] {G : SimpleGraph V}
    (r : V) (transitive : ∀ x, ∃ g : G ≃g G, g r = x)
    {k : ℕ} (proper : 2^k ≠ Fintype.card V) (someCycle : cycleGraph (2^k) ⊑ G) :
    ∃ c : (cycleGraph (2^k)).Copy G, r ∉ Set.range c := by
  classical
  by_contra! hit
  exact proper (transitive_cycle_spans r transitive hit someCycle.some)

private theorem cycle_of_period {U Z : Type*} {H : SimpleGraph U} (f : Z → Z)
    (label : Z ↪ U) (adj : ∀ z, H.Adj (label z) (label (f z))) (z : Z)
    (large : 3 ≤ minimalPeriod f z) : cycleGraph (minimalPeriod f z) ⊑ H := by
  let t := minimalPeriod f z
  let : NeZero t := ⟨by change 3 ≤ t at large; omega⟩
  let v (i : Fin t) := label (f^[i.val] z)
  have inj : Injective v := by
    intro i j eq
    exact Fin.ext ((iterate_eq_iterate_iff_of_lt_minimalPeriod i.isLt j.isLt).mp
      (label.injective eq))
  have step (i : Fin t) : H.Adj (v i) (v (i + 1)) := by
    have h1 : 1 < t := by change 3 ≤ t at large; omega
    have hi : (i + 1 : Fin t).val = (i.val + 1) % t := by
      rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt h1]
    change H.Adj (label (f^[i.val] z)) (label (f^[(i + 1 : Fin t).val] z))
    rw [hi, iterate_mod_minimalPeriod_eq, iterate_succ_apply']
    exact adj _
  change cycleGraph t ⊑ H
  refine ⟨⟨⟨v, ?_⟩, inj⟩⟩
  intro i j h
  have h1 : 1 < t := by change 3 ≤ t at large; omega
  have h' : i - j = 1 ∨ j - i = 1 := by
    simpa only [Fin.ext_iff, Fin.val_one', Nat.mod_eq_of_lt h1] using cycleGraph_adj'.mp h
  rcases h' with h' | h'
  · have eq : i = j + 1 := by simpa [add_comm] using sub_eq_iff_eq_add.mp h'
    simpa only [eq] using (step j).symm
  · have eq : j = i + 1 := by simpa [add_comm] using sub_eq_iff_eq_add.mp h'
    simpa only [eq] using step i

/-- A graph covering with fibers of size at most two lifts a simple n-cycle
to a simple n-cycle or 2n-cycle. Local bijectivity is only needed along
the edges of the base cycle. -/
theorem lift_two {U V : Type*} [Fintype U] {G : SimpleGraph U} {B : SimpleGraph V}
    (q : U → V) (onto : Surjective q)
    (small : ∀ v, Nat.card {u : U // q u=v} ≤ 2) {n : ℕ} (large : 3≤n)
    (c : (cycleGraph n).Copy B)
    (liftEdge : ∀ (u : U) (v : V), B.Adj (q u) v → ∃! w : U, G.Adj u w ∧ q w = v) :
    cycleGraph n ⊑ G ∨ cycleGraph (2*n) ⊑ G := by
  classical
  let : NeZero n := ⟨by omega⟩
  have edge (i : Fin n) : B.Adj (c i) (c (i+1)) := by
    apply c.toHom.map_rel'
    apply cycleGraph_adj'.mpr
    right
    simp [Nat.mod_eq_of_lt (show 1<n by omega)]
  let Fiber (i : Fin n) := {u : U // q u=c i}
  let D := Σ i : Fin n, Fiber i
  have next (z : D) : ∃! w : U, G.Adj z.2.val w ∧ q w=c (z.1+1) := by
    apply liftEdge
    rw [z.2.property]
    exact edge z.1
  let f (z : D) : D := ⟨z.1+1,(next z).choose,(next z).choose_spec.1.2⟩
  let label : D ↪ U := ⟨fun z => z.2.val,by
    rintro ⟨i,a,ha⟩ ⟨j,b,hb⟩ (rfl : a=b)
    obtain rfl := c.injective (ha.symm.trans hb)
    rfl⟩
  have adj (z : D) : G.Adj (label z) (label (f z)) := (next z).choose_spec.1.1
  have inject : Injective f := by
    intro x y h
    have phase : x.1=y.1 := add_right_cancel (congrArg Sigma.fst h : x.1+1=y.1+1)
    have eq : label (f x)=label (f y) := congrArg label h
    apply label.injective
    have same : q (label (f x))=c (x.1+1) := (f x).2.property
    have choices := liftEdge (label (f x)) (c x.1) (same ▸ (edge x.1).symm)
    apply choices.unique
    · exact ⟨(adj x).symm,x.2.property⟩
    · exact ⟨eq ▸ (adj y).symm,y.2.property.trans (congrArg c phase.symm)⟩
  obtain ⟨a,ha⟩ := onto (c 0)
  let start : D := ⟨0,a,ha⟩
  let t := minimalPeriod f start
  have pos : 0<t := by
    apply minimalPeriod_pos_of_mem_periodicPts
    exact inject.mem_periodicPts _
  have tick (m : ℕ) : (f^[m] start).1=(m : Fin n) := by
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [iterate_succ_apply']
      change (f^[m] start).1+1 = _
      rw [ih,Nat.cast_succ]
  have period : n ∣ t := by
    apply Fin.natCast_eq_zero.mp
    exact (tick t).symm.trans (congrArg Sigma.fst (iterate_minimalPeriod (f := f) (x := start)))
  have bound : t ≤ 2*n := by
    apply (minimalPeriod_le_card (f := f) (x := start)).trans
    change Fintype.card (Σ i : Fin n, Fiber i) ≤ 2*n
    rw [Fintype.card_sigma]
    calc
      _ ≤ ∑ _i : Fin n, 2 := Finset.sum_le_sum (fun i _ => by
        simpa only [Nat.card_eq_fintype_card,Fiber] using small (c i))
      _ = _ := by simp [mul_comm]
  obtain ⟨m,hm⟩ := period
  have choices : t=n ∨ t=2*n := by
    by_cases two : 3 ≤ m
    · have low : n*3 ≤ n*m := Nat.mul_le_mul_left n two
      omega
    · interval_cases m <;> simp_all [Nat.mul_comm]
  have lift := cycle_of_period f label adj start (show 3≤t by rcases choices with h|h <;> omega)
  exact choices.elim (fun h => Or.inl (h ▸ lift)) (fun h => Or.inr (h ▸ lift))

/-- Three signed edges on the leaves of a claw force a square in a binary cover
of a tetrahedron. At one leaf, the two incident signs agree. -/
theorem claw_square {V : Type*} {G : SimpleGraph V} (t : V → V) {v a b c : V}
    (va : G.Adj v a) (vb : G.Adj v b) (vc : G.Adj v c)
    (ab : a≠b) (bc : b≠c) (ca : c≠a)
    (na : v≠t a) (nb : v≠t b) (nc : v≠t c)
    (dab : G.Adj a b ∨ (G.Adj a (t b) ∧ G.Adj (t a) b))
    (dbc : G.Adj b c ∨ (G.Adj b (t c) ∧ G.Adj (t b) c))
    (dca : G.Adj c a ∨ (G.Adj c (t a) ∧ G.Adj (t c) a)) : cycleGraph 4 ⊑ G := by
  rcases dab with u|u <;> rcases dbc with w|w <;> rcases dca with z|z
  · exact square_of_four va u w vc.symm vb.ne ca.symm
  · exact square_of_four va u w vc.symm vb.ne ca.symm
  · exact square_of_four vc z u vb.symm va.ne bc.symm
  · exact square_of_four vb w.1 z.2 va.symm nc ab.symm
  · exact square_of_four vb w z va.symm vc.ne ab.symm
  · exact square_of_four vc z.1 u.2 vb.symm na bc.symm
  · exact square_of_four va u.1 w.2 vc.symm nb ca.symm
  · exact square_of_four va u.1 w.2 vc.symm nb ca.symm

/-- Every two-sheeted cover of K4 contains a square. -/
theorem square_over_four {V W : Type*} [Fintype W] {G : SimpleGraph V} {B : SimpleGraph W}
    [DecidableRel B.Adj] (order : Fintype.card W=4) (cubic : ∀ w, B.degree w=3)
    (t : V → V) (twice : ∀ x,t (t x)=x) (sym : ∀ a b,G.Adj a b → G.Adj (t a) (t b))
    (q : V → W) (onto : Surjective q) (pair : ∀ x y, q x=q y ↔ x=y ∨ x=t y)
    (lift : ∀ x y, B.Adj (q x) y → ∃ w, G.Adj x w ∧ q w=y) : cycleGraph 4 ⊑ G := by
  classical
  let E := (Fintype.equivFinOfCardEq order).symm
  have allAdj (i j : Fin 4) (diff : i ≠ j) : B.Adj (E i) (E j) :=
    ((B.degree_eq_card_sub_one (E i)).mp (by rw [cubic,order]))
      (fun h => diff (E.injective h))
  obtain ⟨v,hv⟩ := onto (E 0)
  have leaves (i : Fin 4) (h : i≠0) : ∃ a, G.Adj v a ∧ q a=E i := by
    apply lift
    rw [hv]
    exact allAdj _ _ h.symm
  obtain ⟨a,va,ha⟩ := leaves 1 (by decide)
  obtain ⟨b,vb,hb⟩ := leaves 2 (by decide)
  obtain ⟨c,vc,hc⟩ := leaves 3 (by decide)
  have qt (x : V) : q (t x)=q x := (pair _ _).mpr (Or.inr rfl)
  have different {x y : V} {i j : Fin 4} (hx : q x=E i) (hy : q y=E j) (diff : i≠j) :
      x≠y ∧ x≠t y := by
    have neq : q x≠q y := fun h => diff (E.injective (hx.symm.trans (h.trans hy)))
    exact ⟨fun h => neq (congrArg q h),fun h => neq ((congrArg q h).trans (qt y))⟩
  have signs {x y : V} {i j : Fin 4} (hx : q x=E i) (hy : q y=E j) (diff : i≠j) :
      G.Adj x y ∨ (G.Adj x (t y) ∧ G.Adj (t x) y) := by
    obtain ⟨w,adj,hw⟩ := lift x (q y) (by rw [hx,hy]; exact allAdj i j diff)
    rcases (pair w y).mp hw with rfl | rfl
    · exact Or.inl adj
    · exact Or.inr ⟨adj,(twice y) ▸ sym _ _ adj⟩
  exact claw_square t va vb vc (different ha hb (by decide)).1 (different hb hc (by decide)).1
    (different hc ha (by decide)).1 (different hv ha (by decide)).2 (different hv hb (by decide)).2
    (different hv hc (by decide)).2 (signs ha hb (by decide)) (signs hb hc (by decide))
    (signs hc ha (by decide))

/-- For a free involution, its pairs are the fibers of a two-to-one map. -/
theorem pair_projection {V : Type} [Fintype V] (t : V → V) (twice : ∀ x, t (t x)=x)
    (free : ∀ x, t x ≠ x) :
    ∃ (W : Type) (_ : Fintype W) (q : V → W), Surjective q ∧
      (∀ x y, q x=q y ↔ x=y ∨ x=t y) ∧ Fintype.card V = Fintype.card W * 2 ∧
      (∀ w, Nat.card {x : V // q x=w}=2) := by
  classical
  let block (x : V) : Set V := {x,t x}
  let W := Set.range block
  let q (x : V) : W := ⟨block x,⟨x,rfl⟩⟩
  have onto : Surjective q := by rintro ⟨_,x,rfl⟩; exact ⟨x,rfl⟩
  have pair (x y : V) : q x=q y ↔ x=y ∨ x=t y := by
    constructor
    · intro h
      have s : x∈block x := Set.mem_insert _ _
      rw [show block x=block y from congrArg Subtype.val h] at s
      exact s
    · rintro (rfl | rfl)
      · rfl
      · apply Subtype.ext
        change ({t y,t (t y)} : Set V)={y,t y}
        rw [twice]
        exact Set.pair_comm _ _
  let : Finite W := Finite.of_surjective q onto
  let : Fintype W := Fintype.ofFinite W
  have fiber (w : W) : Nat.card {x : V // q x=w}=2 := by
    obtain ⟨x,rfl⟩ := onto w
    let f (b : Bool) : {z : V // q z=q x} := if b then
      ⟨t x,(pair _ _).mpr (Or.inr rfl)⟩ else ⟨x,rfl⟩
    have inj : Injective f := by
      intro i j same
      have eq := congrArg Subtype.val same
      cases i <;> cases j <;> simp_all [f,free x,(free x).symm]
    have sur : Surjective f := by
      rintro ⟨z,hz⟩
      rcases (pair z x).mp hz with rfl | rfl
      · exact ⟨false,rfl⟩
      · exact ⟨true,rfl⟩
    exact (Nat.card_congr (Equiv.ofBijective f ⟨inj,sur⟩)).symm.trans (by simp [Nat.card_eq_fintype_card])
  refine ⟨W,inferInstance,q,onto,pair,?_,fiber⟩
  rw [←Fintype.card_congr (Equiv.sigmaFiberEquiv q),Fintype.card_sigma]
  have size (w : W) : Fintype.card {x : V // q x=w}=2 := by
    simpa only [Nat.card_eq_fintype_card] using fiber w
  simp [size]

/-- If the number of points is a power of two, every Sylow 2-subgroup of a
finite transitive group is still transitive on those points. -/
theorem sylow_transitive {A V : Type*} [Group A] [Finite A] [Finite V] [MulAction A V]
    [IsPretransitive A V] (S : Sylow 2 A) {k : ℕ} (card : Nat.card V=2^k) :
    IsPretransitive S V := by
  classical
  constructor
  intro x y
  let H := stabilizer A x
  have eq : H.index=2^k := (index_stabilizer_of_transitive A x).trans card
  have hd : 2^k ∣ H.relIndex S.1 * S.1.index := by
    rw [← Subgroup.inf_relIndex_right,Subgroup.relIndex_mul_index (show H ⊓ S.1 ≤ S.1 from inf_le_right),←eq]
    exact Subgroup.index_dvd_of_le (show H ⊓ S.1 ≤ H from inf_le_left)
  have d : 2^k ∣ H.relIndex S.1 :=
    (Nat.prime_two.coprime_pow_of_not_dvd S.not_dvd_index).symm.dvd_of_dvd_mul_right hd
  have idx : H.relIndex S.1 = (stabilizer S x).index := rfl
  have count : Nat.card V ≤ (orbit S x).ncard := by
    rw [card,←index_stabilizer S x,←idx]
    apply Nat.le_of_dvd _ d
    rw [idx,index_stabilizer S x]
    exact (Set.ncard_pos (Set.toFinite _)).mpr ⟨x,1,one_smul _ _⟩
  have full : orbit S x=Set.univ := by
    apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _)
    simpa using count
  have mem : y ∈ orbit S x := full ▸ Set.mem_univ y
  exact mem

/-- A nontrivial faithful transitive permutation 2-group contains a central
involution which moves every point. -/
theorem central_pair {V : Type*} [Finite V] (A : Subgroup (Equiv.Perm V))
    [Nontrivial A] (two : IsPGroup 2 A) (transitive : ∀ x y, ∃ g : A, g.val x=y) :
    ∃ t : A, (∀ v, t.val (t.val v)=v) ∧ (∀ v,t.val v≠v) ∧
      (∀ (g : A) v, g.val (t.val v)=t.val (g.val v)) := by
  classical
  let Z := Subgroup.center A
  let : Nontrivial Z := two.center_nontrivial
  obtain ⟨j,pj,card⟩ := (two.to_subgroup Z).nontrivial_iff_card.mp (inferInstance : Nontrivial Z)
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := Z) 2 (card ▸ dvd_pow_self 2 pj.ne')
  have commute (g : A) (v : V) : g.val (z.val.val v) = z.val.val (g.val v) :=
    congrArg (fun h : A => h.val v) (Subgroup.mem_center_iff.mp z.property g)
  have sq : z ^ 2 = 1 := hz ▸ pow_orderOf_eq_one z
  have invol (v : V) : z.val.val (z.val.val v)=v := congrArg (fun g : Z => g.val.val v)
    (show z*z=1 by simpa [pow_two] using sq)
  refine ⟨z.val,invol,?_,commute⟩
  intro x fixed
  have ident : z=1 := by
    apply Subtype.ext
    apply Subtype.ext
    apply Equiv.ext
    intro y
    obtain ⟨g,rfl⟩ := transitive x y
    exact (commute g x).symm.trans (congrArg g.val fixed)
  simp [ident] at hz

/-- An invariant partition gives a quotient action that is again a transitive
permutation 2-group. The only required compatibility is equality of fibers. -/
theorem descend {V W : Type*} (A : Subgroup (Equiv.Perm V)) (two : IsPGroup 2 A)
    (transitive : ∀ x y, ∃ g : A, g.val x=y)
    (q : V → W) (onto : Surjective q) (respects : ∀ (g : A) x y, q x=q y → q (g.val x)=q (g.val y)) :
    ∃ D : Subgroup (Equiv.Perm W), IsPGroup 2 D ∧ (∀ x y, ∃ g : D,g.val x=y) ∧
      ∀ d : D, ∃ g : A, ∀ x, d.val (q x)=q (g.val x) := by
  classical
  let s := surjInv onto
  have qs := rightInverse_surjInv onto
  let f (g : A) (w : W) := q (g.val (s w))
  have equiv (g : A) (v : V) : f g (q v)=q (g.val v) := respects _ _ _ (qs _)
  have mul (g h : A) (w : W) : f g (f h w)=f (g*h) w := by
    obtain ⟨x,rfl⟩ := onto w
    exact (congrArg (f g) (equiv h x)).trans
      ((equiv g (h.val x)).trans (equiv (g*h) x).symm)
  have one (w : W) : f 1 w=w := qs _
  let perm (g : A) : Equiv.Perm W :=
    ⟨f g,f g⁻¹,fun w => (mul _ _ w).trans (by rw [inv_mul_cancel]; exact one w),
      fun w => (mul _ _ w).trans (by rw [mul_inv_cancel]; exact one w)⟩
  let hom : A →* Equiv.Perm W :=
    ⟨⟨perm,Equiv.ext one⟩,fun g h => Equiv.ext (fun w => (mul g h w).symm)⟩
  refine ⟨hom.range,two.of_surjective hom.rangeRestrict hom.rangeRestrict_surjective,?_,?_⟩
  · intro x y
    obtain ⟨a,rfl⟩ := onto x
    obtain ⟨b,rfl⟩ := onto y
    obtain ⟨g,hg⟩ := transitive a b
    exact ⟨hom.rangeRestrict g,(equiv g a).trans (congrArg q hg)⟩
  · rintro ⟨_,g,rfl⟩
    exact ⟨g,equiv g⟩

/-- In a square-free graph of minimum degree three a central free involution
of a transitive group gives a two-sheeted cover preserving the minimum degree. -/
theorem binary_quotient {V : Type} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (degree : ∀ v, 3 ≤ G.degree v) (nosq : ¬cycleGraph 4 ⊑ G)
    (P : Subgroup (Equiv.Perm V)) [Nontrivial P] (two : IsPGroup 2 P)
    (transitive : ∀ x y, ∃ g : P, g.val x=y)
    (auto : ∀ (g : P) x y, G.Adj x y → G.Adj (g.val x) (g.val y)) :
    ∃ (W : Type) (_ : Fintype W) (B : SimpleGraph W) (_ : DecidableRel B.Adj)
      (D : Subgroup (Equiv.Perm W)), Fintype.card V=Fintype.card W*2 ∧
      (∀ w, 3 ≤ B.degree w) ∧ IsPGroup 2 D ∧ (∀ x y, ∃ d : D, d.val x=y) ∧
      (∀ (d : D) x y, B.Adj x y → B.Adj (d.val x) (d.val y)) ∧
      Fintype.card W ≠ 4 ∧
      ∀ n : ℕ, 3 ≤ n → cycleGraph n ⊑ B → cycleGraph n ⊑ G ∨ cycleGraph (2*n) ⊑ G := by
  classical
  obtain ⟨h,twice,free,commuting⟩ := central_pair P two transitive
  let t : V → V := h.val
  have sym (x y : V) : G.Adj x y → G.Adj (t x) (t y) := auto h x y
  obtain ⟨W,fw,q,onto,pair,card,fib⟩ := pair_projection t twice free
  let : Fintype W := fw
  have fixed (x : V) : q (t x)=q x := (pair _ _).mpr (Or.inr rfl)
  have noLoops (x : V) : ¬ G.Adj x (t x) := by
    intro loop
    have loops (y : V) : G.Adj y (t y) := by
      obtain ⟨g,rfl⟩ := transitive x y
      change G.Adj (g.val x) (h.val (g.val x))
      rw [←commuting g x]
      exact auto g x (t x) loop
    have other : ∃ y, G.Adj x y ∧ y≠t x := by
      by_contra! only
      have incl : G.neighborFinset x ⊆ {t x} := fun z hz =>
        Finset.mem_singleton.mpr (only z ((G.mem_neighborFinset _ _).mp hz))
      have bound := Finset.card_le_card incl
      rw [card_neighborFinset_eq_degree,Finset.card_singleton] at bound
      have := degree x
      omega
    obtain ⟨y,xy,neq⟩ := other
    have diff : x≠t y := fun eq => neq ((twice y).symm.trans (congrArg t eq.symm))
    exact nosq (square_of_four xy (loops y) (sym x y xy).symm loop.symm diff neq)
  have edgesDistinct {x y : V} (xy : G.Adj x y) : q x≠q y := by
    intro eq
    rcases (pair _ _).mp eq with rfl|rfl
    · exact xy.ne rfl
    · exact noLoops y xy.symm
  have neighborInj {x y z : V} (xy : G.Adj x y) (xz : G.Adj x z) (eq : q y=q z) : y=z := by
    rcases (pair _ _).mp eq with done|rfl
    · exact done
    · have across : G.Adj z (t x) := (show G.Adj (t x) z from (twice z) ▸ sym _ _ xy).symm
      exact (nosq (square_of_four xz across (sym _ _ xz) xy.symm (free x).symm (free z).symm)).elim
  let B := G.map q
  have lift (x : V) (w : W) (edge : B.Adj (q x) w) :
      ∃! y, G.Adj x y ∧ q y=w := by
    obtain ⟨_,a,b,ab,ha,hb⟩ := (map_adj' q G _ _).mp edge
    have existsLift : ∃ y, G.Adj x y ∧ q y=w := by
      rcases (pair _ _).mp ha with rfl|rfl
      · exact ⟨b,ab,hb⟩
      · exact ⟨t b,(twice x) ▸ sym _ _ ab,(fixed b).trans hb⟩
    obtain ⟨y,xy,hy⟩ := existsLift
    exact ⟨y,⟨xy,hy⟩,fun z hz => neighborInj hz.1 xy (hz.2.trans hy.symm)⟩
  have deg (w : W) : 3 ≤ B.degree w := by
    obtain ⟨v,rfl⟩ := onto w
    have nbr : B.neighborFinset (q v)=(G.neighborFinset v).image q := by
      ext y
      simp only [mem_neighborFinset,Finset.mem_image]
      constructor
      · intro adj
        exact (lift v y adj).exists
      · rintro ⟨u,vu,rfl⟩
        exact (map_adj' q G _ _).mpr ⟨edgesDistinct vu,v,u,vu,rfl,rfl⟩
    suffices inj : Set.InjOn q (G.neighborFinset v) by
      rw [←card_neighborFinset_eq_degree,nbr,Finset.card_image_of_injOn inj,card_neighborFinset_eq_degree]
      exact degree v
    exact fun _ hx _ hy eq => neighborInj ((mem_neighborFinset _ _ _).mp hx)
      ((mem_neighborFinset _ _ _).mp hy) eq
  have respects (g : P) (x y : V) (eq : q x=q y) : q (g.val x)=q (g.val y) := by
    apply (pair _ _).mpr
    rcases (pair _ _).mp eq with rfl|rfl
    · exact Or.inl rfl
    · exact Or.inr (commuting g y)
  obtain ⟨D,twoD,transD,desc⟩ := descend P two transitive q onto respects
  have autoD (d : D) (x y : W) (xy : B.Adj x y) : B.Adj (d.val x) (d.val y) := by
    obtain ⟨g,act⟩ := desc d
    obtain ⟨neq,a,b,ab,rfl,rfl⟩ := (map_adj' q G _ _).mp xy
    exact (map_adj' q G _ _).mpr ⟨fun eq => neq (d.val.injective eq),
      g.val a,g.val b,auto g _ _ ab,(act _).symm,(act _).symm⟩
  have notFour (size : Fintype.card W=4) : False := by
    have exactDeg (w : W) : B.degree w=3 := by
      have upper := B.degree_lt_card_verts w
      have lower := deg w
      omega
    exact nosq (square_over_four (G := G) (B := B) size exactDeg t twice sym q onto pair
      (fun x y e => (lift x y e).exists))
  refine ⟨W,fw,B,inferInstance,D,card,deg,twoD,transD,autoD,notFour,?_⟩
  rintro n large ⟨c⟩
  exact lift_two q onto (fun w => (fib w).le) large c lift


/-- At order 2^(m+3) a transitive 2-group guarantees a dyadic cycle on at
most half of the vertices, assuming only minimum degree three. -/
theorem short_of_two (m : ℕ) : ∀ (V : Type) [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj], Fintype.card V=2^(m+3) → (∀ v, 3 ≤ G.degree v) →
    ∀ P : Subgroup (Equiv.Perm V), IsPGroup 2 P → (∀ x y, ∃ g : P, g.val x=y) →
    (∀ (g : P) x y, G.Adj x y → G.Adj (g.val x) (g.val y)) →
    ∃ d : ℕ, 2 ≤ d ∧ 2^d ≤ 2^(m+2) ∧ cycleGraph (2^d) ⊑ G := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro V _ G _ order degree P two transitive auto
    have four : 4 ≤ 2^(m+2) := Nat.pow_le_pow_right (by decide : 0<2) (show 2 ≤ m+2 by omega)
    by_cases square : cycleGraph 4 ⊑ G
    · exact ⟨2,by decide,four,square⟩
    classical
    have large : 8 ≤ Fintype.card V := order ▸
      Nat.pow_le_pow_right (by decide : 0<2) (show 3 ≤ m+3 by omega)
    let : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨x,y,distinct⟩ := exists_pair_ne V
    obtain ⟨g,move⟩ := transitive x y
    let : Nontrivial P := ⟨g,1,fun eq => distinct (by simpa [eq] using move)⟩
    obtain ⟨W,fw,B,db,D,cards,degreeB,twoD,transD,autoD,notFour,lifts⟩ :=
      binary_quotient degree square P two transitive auto
    let : Fintype W := fw
    let : DecidableRel B.Adj := db
    have next : Fintype.card W=2^(m+2) := by
      rw [order,show m+3=m+2+1 by omega,pow_succ] at cards
      omega
    cases m with
    | zero => exact (notFour next).elim
    | succ j =>
      obtain ⟨d,hd,small,cycle⟩ := ih j (by omega) W B next degreeB D twoD transD autoD
      have low : 4 ≤ 2^d := Nat.pow_le_pow_right (by decide : 0<2) hd
      have upper : 2^(j.succ+2)=2^(j+2)*2 := pow_succ 2 (j+2)
      rcases lifts _ (by omega) cycle with c|c
      · exact ⟨d,hd,by rw [upper]; omega,c⟩
      · refine ⟨d+1,by omega,by rw [upper,pow_succ]; omega,?_⟩
        rwa [pow_succ'] 

/-- Form the full permutation group of graph automorphisms and take a
transitive Sylow subgroup on a power-of-two number of vertices. -/
theorem short_of_transitive {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (degree : ∀ v, 3 ≤ G.degree v) (transitive : ∀ x y, ∃ g : G ≃g G, g x=y)
    {m : ℕ} (order : Fintype.card V=2^(m+3)) :
    ∃ d : ℕ, 2 ≤ d ∧ 2^d ≤ 2^(m+2) ∧ cycleGraph (2^d) ⊑ G := by
  classical
  let A : Subgroup (Equiv.Perm V) :=
    { carrier := {g | ∀ u v, G.Adj (g u) (g v) ↔ G.Adj u v}
      mul_mem' := fun hg hh u v => (hg _ _).trans (hh u v)
      one_mem' := fun _ _ => Iff.rfl
      inv_mem' := fun {g} hg u v => by simpa using (hg (g.symm u) (g.symm v)).symm }
  let : MulAction.IsPretransitive A V := ⟨fun u v => by
    obtain ⟨g,h⟩ := transitive u v
    exact ⟨⟨g.toEquiv,fun _ _ => g.map_rel_iff⟩,h⟩⟩
  let S : Sylow 2 A := Classical.choice inferInstance
  have strans := sylow_transitive (V := V) S (k := m+3) (by simpa [Nat.card_eq_fintype_card] using order)
  let P := S.1.map A.subtype
  have twoP : IsPGroup 2 P := S.2.map A.subtype
  have transP (u v : V) : ∃ g : P, g.val u=v := by
    obtain ⟨s,hs⟩ := strans.exists_smul_eq u v
    exact ⟨⟨s.val.val,s.val,s.property,rfl⟩,hs⟩
  apply short_of_two m V G order degree P twoP transP
  rintro ⟨_,g,_,rfl⟩ u v uv
  exact (g.property u v).mpr uv

/-- If a vertex-transitive graph of minimum degree three has order greater
than four and has any dyadic cycle, each vertex can be avoided by one. -/
theorem avoids_each_vertex {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (degree : ∀ v, 3 ≤ G.degree v) (transitive : ∀ x y, ∃ g : G ≃g G, g x=y)
    (big : 4 < Fintype.card V) (has : ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ G)
    (r : V) : ∃ (k : ℕ) (c : (cycleGraph (2^k)).Copy G), 2 ≤ k ∧ r ∉ Set.range c := by
  obtain ⟨k,hk,w⟩ := has
  by_cases spanning : 2^k=Fintype.card V
  · have three : 3 ≤ k := by
      by_contra! small
      have : k=2 := by omega
      subst k
      omega
    obtain ⟨m,rfl⟩ : ∃ m, k=m+3 := ⟨k-3,by omega⟩
    obtain ⟨d,hd,small,cycle⟩ := short_of_transitive G degree transitive spanning.symm
    have proper : 2^d≠Fintype.card V := by
      rw [←spanning,show m+3=m+2+1 by omega,pow_succ]
      have positive : 0<2^(m+2) := Nat.two_pow_pos _
      omega
    obtain ⟨c,avoid⟩ := avoiding_cycle r (transitive r) proper cycle
    exact ⟨d,c,hd,avoid⟩
  · obtain ⟨c,avoid⟩ := avoiding_cycle r (transitive r) spanning w
    exact ⟨k,c,hk,avoid⟩

/-- In the rooted triangle-contraction branch, vertex transitivity is
impossible. At order four the unique degree-three graph is complete. -/
theorem rooted_obstruction_asymmetric {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (degree : ∀ v, 3 ≤ G.degree v) (r : V)
    (noneThrough : ∀ c : (cycleGraph 3).Copy G, r ∉ Set.range c)
    (has : ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ G)
    (hit : ∀ k : ℕ, 2 ≤ k → ∀ c : (cycleGraph (2^k)).Copy G, r ∈ Set.range c) :
    ¬∀ x y, ∃ g : G ≃g G, g x=y := by
  intro sym
  by_cases big : 4 < Fintype.card V
  · obtain ⟨k,c,hk,avoid⟩ := avoids_each_vertex G degree sym big has r
    exact avoid (hit k hk c)
  · have lower := degree r
    have upper := G.degree_lt_card_verts r
    have four : Fintype.card V=4 := by omega
    let e := (Fin.castSuccEmb : Fin 3 ↪ Fin 4).trans (Fintype.equivFinOfCardEq four).symm.toEmbedding
    have universal (u : V) : G.IsUniversal u := by
      apply (G.degree_eq_card_sub_one u).mp
      have := degree u
      have := G.degree_lt_card_verts u
      omega
    let c : (cycleGraph 3).Copy G :=
      ⟨⟨e,fun h => universal _ (fun eq => h.ne (e.injective eq))⟩,e.injective⟩
    obtain ⟨g,hg⟩ := sym (c 0) r
    exact noneThrough (g.toCopy.comp c) ⟨0,hg⟩

end HalfOrder

theorem main : H1 → H2 → OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R2.H2 := by
  intro small large V G _ _ r conn cubic bridges triangles witness forced
  classical
  by_contra unsolved
  have obstruction : ¬ ∃ (n k : ℕ) (c : (cycleGraph n).Copy G) (f : G ≃g G),
      3 ≤ n ∧ 2 ≤ k ∧ f r ∈ Set.range c ∧ (n+1=2^k ∨ n+2=2^k) := by
    rintro ⟨n,k,c,f,hn,hk,hit,h⟩
    obtain ⟨d,hd⟩ := backToRoot c f hit
    exact unsolved ⟨n,k,d,hn,hk,hd,h⟩
  have asym := HalfOrder.rooted_obstruction_asymmetric G (fun v => (cubic v).ge)
    r triangles witness forced
  have proper : ∃ v, ∀ f : G ≃g G, f r ≠ v := by
    by_contra! all
    apply asym
    intro x y
    obtain ⟨a,ha⟩ := all x
    obtain ⟨b,hb⟩ := all y
    exact ⟨a.symm.trans b,by change b (a.symm x)=y; rw [← ha,a.symm_apply_apply,hb]⟩
  have away (n : ℕ) (h : n=3 ∨ n=6) (c : (cycleGraph n).Copy G) (f : G ≃g G) :
      f r ∉ Set.range c := by
    intro hit
    obtain ⟨d,hd⟩ := backToRoot c f hit
    rcases h with rfl|rfl
    · exact triangles d hd
    · exact unsolved ⟨6,3,d,by decide,by decide,hd,Or.inr rfl⟩
  have images (k : ℕ) (hk : 2 ≤ k) (c : (cycleGraph (2^k)).Copy G) (f : G ≃g G) :
      f r ∈ Set.range c := HalfOrder.orbit_on_cycle r (forced k hk) c f
  have rule := thetaObstruction G r images obstruction
  by_cases few : {v | ∃ f : G ≃g G, f r=v}.ncard ≤ 2
  · exact obstruction (small V G r conn cubic bridges proper away witness images few rule)
  apply obstruction
  apply large V G r conn cubic bridges proper away witness images (by omega)
  · intro k hk c x y valid omits
    by_cases eq : x=y
    · subst y
      have big : 4≤2^k := Nat.pow_le_pow_right (by decide : 0<2) hk
      apply unsolved (omittedBlockSolves G r conn cubic proper (d := 1) hk
        (Or.inl rfl) (by omega) c x (images k hk c) ?_)
      intro j
      simpa using omits j
    · exact unsolved (twoOmissionsSolve G r cubic (valid.resolve_left eq)
        c x y eq (images k hk c) omits)
  dsimp only
  intro x y A B P clean paths base
  obtain ⟨miss,both⟩ := rule x y A B P clean paths base
  constructor
  · intro near
    obtain ⟨inside,noOther⟩ := miss near
    have bound := orbitBoundOnList G r B inside
    exact ⟨inside,by omega,noOther⟩
  · intro a b
    have inside (f : G ≃g G) : f r ∈ [x,y] := by simpa using both a b f
    exact few (orbitBoundOnList G r [x,y] inside)

end OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R2_H2_R2
