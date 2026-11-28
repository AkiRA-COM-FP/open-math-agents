import FormalConjectures.ErdosProblems.«595»

-- Credit: @wispiANt
namespace OMA.R_Erdos595_erdos_595_R3

open SimpleGraph

/-- No deterministic Painter works on every legal play of some fixed ordinal
length. At stage j the input contains only edges with both ends at most j.
The entire play, including its triangles, may depend on the proposed rule. -/
def H1 : Prop :=
  ∃ (I : Type) (_ : LinearOrder I) (_ : WellFoundedLT I) (_ : Infinite I),
    ∀ paint : I → Set (I × I) → I → ℕ,
      ∃ G : SimpleGraph I, G.CliqueFree 4 ∧
        ∃ a b c : I, a < b ∧ b < c ∧ G.Adj a b ∧ G.Adj a c ∧ G.Adj b c ∧
          let past := fun j => {p : I × I | p.1 ≤ j ∧ p.2 ≤ j ∧ G.Adj p.1 p.2}
          paint b (past b) a = paint c (past c) a ∧ paint b (past b) a = paint c (past c) b

/-- No ordinal of cardinality at most the continuum can witness the first
step. A fixed binary cut for each colour already suffices on such a horizon. -/
theorem small_horizon {I : Type} [LinearOrder I] (code : I ↪ (ℕ → Bool)) :
    ∃ paint : I → Set (I × I) → I → ℕ, ∀ (s t : Set (I × I)) (a b c : I),
      a < b → b < c → paint b s a = paint c t a → paint b s a ≠ paint c t b := by
  classical
  let paint (j : I) (_ : Set (I × I)) (i : I) :=
    if h : ∃ n, code i n ≠ code j n then h.choose else 0
  have separates {i j : I} (ij : i < j) (s : Set (I × I)) :
      code i (paint j s i) ≠ code j (paint j s i) := by
    have ex : ∃ n, code i n ≠ code j n := by
      by_contra! same
      exact ij.ne (code.injective (funext same))
    simpa [paint,ex] using ex.choose_spec
  refine ⟨paint,?_⟩
  intro s t a b c ab bc eq eq'
  have x := separates ab s
  have y := separates (ab.trans bc) t
  have z := separates bc t
  rw [←eq] at y
  rw [←eq'] at z
  have impossible (i j k : Bool) : i ≠ j → i ≠ k → j ≠ k → False := by
    cases i <;> cases j <;> cases k <;> decide
  exact impossible _ _ _ x y z

/-- Simultaneously realize all legal presentations, identifying the vertex at
a stage whenever the entire revealed history at that stage is identical. -/
def H2 : Prop :=
  ∀ (I : Type) [LinearOrder I] [Infinite I],
    ∃ (V : Type) (_ : Infinite V) (J : SimpleGraph V), J.CliqueFree 4 ∧
      ∃ node : I → Set (I × I) → V,
        ∀ (G : SimpleGraph I), G.CliqueFree 4 → ∀ a b, G.Adj a b →
          let past := fun j => {p : I × I | p.1 ≤ j ∧ p.2 ≤ j ∧ G.Adj p.1 p.2}
          J.Adj (node a (past a)) (node b (past b))

/-- Every clique has a latest stage. Its entire diagram occurs inside the
history at that stage, where it was already required to be legal. -/
theorem history_amalgamation : H2 := by
  classical
  intro I _ _
  let P := I × Set (I × I)
  let past (G : SimpleGraph I) (j : I) := {p : I × I | p.1 ≤ j ∧ p.2 ≤ j ∧ G.Adj p.1 p.2}
  let edge (x y : P) := ∃ G : SimpleGraph I, G.CliqueFree 4 ∧
    x.2 = past G x.1 ∧ y.2 = past G y.1 ∧ G.Adj x.1 y.1
  let J : SimpleGraph P := {
    Adj := edge
    symm := ⟨by rintro x y ⟨G,h,hx,hy,xy⟩; exact ⟨G,h,hy,hx,xy.symm⟩⟩
    loopless := ⟨by rintro x ⟨G,_,_,_,xx⟩; exact xx.ne rfl⟩ }
  refine ⟨P,inferInstance,J,?_,Prod.mk,fun G h a b ab => ⟨G,h,rfl,rfl,ab⟩⟩
  by_contra bad
  obtain ⟨f⟩ := (not_cliqueFree_iff_top_isContained 4).mp bad
  let x (i : Fin 4) : P := f i
  have pair {i j : Fin 4} (h : i ≠ j) : edge (x i) (x j) := f.toHom.map_rel h
  obtain ⟨t,_,top⟩ := Finset.exists_max_image Finset.univ (fun i => (x i).1) Finset.univ_nonempty
  have bound (i) : (x i).1 ≤ (x t).1 := top i (Finset.mem_univ _)
  obtain ⟨k,hk⟩ := exists_ne t
  obtain ⟨G,free,ht,_,_⟩ := pair (Ne.symm hk)
  have inTop (i : Fin 4) : (x i).2 ⊆ (x t).2 := by
    by_cases eq : i = t
    · subst i; exact Set.Subset.rfl
    obtain ⟨U,_,hi,ht',_⟩ := pair eq
    rw [hi,ht']
    exact fun _ h => ⟨h.1.trans (bound i),h.2.1.trans (bound i),h.2.2⟩
  have localAdj {i j : Fin 4} (ij : i ≠ j) (le : (x i).1 ≤ (x j).1) :
      G.Adj (x i).1 (x j).1 := by
    obtain ⟨U,_,_,hj,adj⟩ := pair ij
    have e : ((x i).1,(x j).1) ∈ (x j).2 := hj ▸ ⟨le,le_rfl,adj⟩
    have h := inTop j e
    rw [ht] at h
    exact h.2.2
  have adj (i j : Fin 4) (ij : i ≠ j) : G.Adj (x i).1 (x j).1 :=
    (le_total (x i).1 (x j).1).elim (localAdj ij) (fun le => (localAdj ij.symm le).symm)
  apply ((not_cliqueFree_iff_top_isContained 4).mpr ?_) free
  exact ⟨⟨⟨fun i => (x i).1,fun h => adj _ _ h⟩,
    fun i j eq => by_contra fun ne => (adj i j ne).ne eq⟩⟩

-- Universe transport adapted from the merged first reduction (PR 9613).
universe u
private theorem lift_witness {V : Type} [Infinite V] (G : SimpleGraph V) (h4 : G.CliqueFree 4)
    (bad : ¬ Erdos595.IsCountableUnionOfTriangleFree G) :
    ∃ (W : Type u) (_ : Infinite W) (J : SimpleGraph W),
      J.CliqueFree 4 ∧ ¬ Erdos595.IsCountableUnionOfTriangleFree J := by
  let down : ULift.{u} V ↪ V := Equiv.ulift.toEmbedding
  let incl : V ↪ ULift.{u} V := Equiv.ulift.symm.toEmbedding
  refine ⟨ULift.{u} V, inferInstance, G.comap down,
    h4.comap (SimpleGraph.Embedding.comap down G).isContained, ?_⟩
  rintro ⟨H, hfree, heq⟩
  apply bad
  refine ⟨fun i => (H i).comap incl,
    fun i => (hfree i).comap (SimpleGraph.Embedding.comap incl (H i)).isContained, ?_⟩
  ext a b
  rw [SimpleGraph.iSup_adj]
  change G.Adj a b ↔ ∃ i, (H i).Adj (incl a) (incl b)
  rw [← SimpleGraph.iSup_adj, ← heq]; rfl

theorem main : H1 → H2 → type_of% @Erdos595.erdos_595 := by
  classical
  rintro ⟨I,order,wf,inf,defeat⟩ realize
  let : LinearOrder I := order
  let : Infinite I := inf
  obtain ⟨V,hV,J,free,node,edges⟩ := realize I
  let : Infinite V := hV
  apply lift_witness J free
  rintro ⟨L,noTriangle,covers⟩
  let colour (x y : V) := if h : ∃ n, (L n).Adj x y then h.choose else 0
  have assigned {x y} (xy : J.Adj x y) : (L (colour x y)).Adj x y := by
    rw [covers,iSup_adj] at xy
    simpa [colour,xy] using xy.choose_spec
  let restrict (s : Set (I × I)) (i : I) := {p : I × I | p.1 ≤ i ∧ p.2 ≤ i ∧ p ∈ s}
  let paint (j : I) (s : Set (I × I)) (i : I) := colour (node i (restrict s i)) (node j s)
  obtain ⟨G,legal,a,b,c,ab,bc,eab,eac,ebc,same⟩ := defeat paint
  let past (i : I) := {p : I × I | p.1 ≤ i ∧ p.2 ≤ i ∧ G.Adj p.1 p.2}
  have trunc {i j} (h : i ≤ j) : restrict (past j) i = past i := by
    ext p
    exact ⟨fun w => ⟨w.1,w.2.1,w.2.2.2.2⟩, fun w =>
      ⟨w.1,w.2.1,w.1.trans h,w.2.1.trans h,w.2.2⟩⟩
  let v (i : I) := node i (past i)
  have eq {i j} (h : i ≤ j) : paint j (past j) i = colour (v i) (v j) := by
    change colour (node i (restrict (past j) i)) _ = _
    rw [trunc h]
  change paint b (past b) a = paint c (past c) a ∧ paint b (past b) a = paint c (past c) b at same
  rw [eq ab.le,eq (ab.trans bc).le,eq bc.le] at same
  have xy := assigned (edges G legal _ _ eab)
  have xz := assigned (edges G legal _ _ eac)
  have yz := assigned (edges G legal _ _ ebc)
  change (L (colour (v a) (v c))).Adj (v a) (v c) at xz
  change (L (colour (v b) (v c))).Adj (v b) (v c) at yz
  rw [←same.1] at xz
  rw [←same.2] at yz
  exact noTriangle _ _ (is3Clique_triple_iff.mpr ⟨xy,xz,yz⟩)

end OMA.R_Erdos595_erdos_595_R3
