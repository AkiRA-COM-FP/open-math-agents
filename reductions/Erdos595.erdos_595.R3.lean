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

/-- On a fixed ordered witness, every chronological rule induces a countable
edge colouring. Sorting a monochromatic triangle gives its three actual moves. -/
theorem fixed_play {I : Type} [LinearOrder I] (G : SimpleGraph I)
    (bad : ¬ Erdos595.IsCountableUnionOfTriangleFree G)
    (paint : I → Set (I × I) → I → ℕ) :
    ∃ a b c : I, a < b ∧ b < c ∧ G.Adj a b ∧ G.Adj a c ∧ G.Adj b c ∧
      let past := fun j => {p : I × I | p.1 ≤ j ∧ p.2 ≤ j ∧ G.Adj p.1 p.2}
      paint b (past b) a = paint c (past c) a ∧ paint b (past b) a = paint c (past c) b := by
  classical
  let past (j : I) := {p : I × I | p.1 ≤ j ∧ p.2 ≤ j ∧ G.Adj p.1 p.2}
  let colour (a b : I) := paint (max a b) (past (max a b)) (min a b)
  let L (n : ℕ) : SimpleGraph I := {
    Adj a b := G.Adj a b ∧ colour a b = n
    symm := ⟨fun a b h => ⟨h.1.symm, by simpa only [colour,max_comm b a,min_comm b a] using h.2⟩⟩
    loopless := ⟨fun _ h => h.1.ne rfl⟩ }
  have union_eq : G = ⨆ n,L n := by
    ext a b
    rw [iSup_adj]
    exact ⟨fun h => ⟨colour a b,h,rfl⟩,fun ⟨_,h⟩ => h.1⟩
  have exists_triple : ∃ n s, (L n).IsNClique 3 s := by
    by_contra! none
    exact bad ⟨L,none,union_eq⟩
  obtain ⟨n,s,cl⟩ := exists_triple
  let v := s.orderEmbOfFin cl.card_eq
  have edge (i j : Fin 3) (h : i < j) :
      G.Adj (v i) (v j) ∧ paint (v j) (past (v j)) (v i) = n := by
    have adj : (L n).Adj (v i) (v j) := cl.isClique
      (s.orderEmbOfFin_mem _ i) (s.orderEmbOfFin_mem _ j) (v.strictMono h).ne
    exact ⟨adj.1, by simpa only [colour,max_eq_right (v.monotone h.le), min_eq_left (v.monotone h.le)] using adj.2⟩
  have ab := edge 0 1 (by decide)
  have ac := edge 0 2 (by decide)
  have bc := edge 1 2 (by decide)
  exact ⟨_,_,_,v.strictMono (by decide : (0 : Fin 3) < 1),v.strictMono (by decide : (1 : Fin 3) < 2),
    ab.1,ac.1,bc.1,ab.2.trans ac.2.symm,ab.2.trans bc.2.symm⟩

/-- Passing to the online subproblem loses no fixed witness in the base universe. -/
theorem from_fixed_witness {V : Type} [Infinite V] (G : SimpleGraph V)
    (free : G.CliqueFree 4) (bad : ¬ Erdos595.IsCountableUnionOfTriangleFree G) : H1 := by
  obtain ⟨order,wf⟩ := exists_wellFoundedLT V
  let : LinearOrder V := order
  exact ⟨V,order,wf,inferInstance,fun paint => ⟨G,free,fixed_play G bad paint⟩⟩

/-- A Painter on a larger order can be simulated on any order-embedded
horizon. Unused stages are isolated; the embedding need not be an initial
segment. The same simulation works for every play on the smaller horizon. -/
theorem horizon_simulation {I J : Type} [LinearOrder I] [LinearOrder J]
    (e : I ↪o J) (paint : J → Set (J × J) → J → ℕ) :
    ∃ run : I → Set (I × I) → I → ℕ, ∀ (G : SimpleGraph I) (i j : I),
      run j {p | p.1 ≤ j ∧ p.2 ≤ j ∧ G.Adj p.1 p.2} i =
        paint (e j) {p | p.1 ≤ e j ∧ p.2 ≤ e j ∧ (G.map e.toEmbedding).Adj p.1 p.2} (e i) := by
  let extend (s : Set (I × I)) := (fun p : I × I => (e p.1,e p.2)) '' s
  refine ⟨fun j s i => paint (e j) (extend s) (e i),?_⟩
  intro G i j
  apply congrArg (fun s => paint (e j) s (e i))
  ext ⟨u,v⟩
  constructor
  · rintro ⟨⟨a,b⟩,⟨ha,hb,ab⟩,eq⟩
    rw [←eq]
    exact ⟨e.monotone ha,e.monotone hb,map_adj_apply.mpr ab⟩
  · rintro ⟨hu,hv,uv⟩
    obtain ⟨a,b,ab,rfl,rfl⟩ := (map_adj e.toEmbedding G u v).mp uv
    exact ⟨(a,b),⟨e.le_iff_le.mp hu,e.le_iff_le.mp hv,ab⟩,rfl⟩

/-- Losing horizons are upward closed under order embeddings. -/
theorem losing_horizon_mono {I J : Type} [LinearOrder I] [LinearOrder J] [Nonempty I] (e : I ↪o J) :
    let loses (X : Type) [LinearOrder X] := ∀ paint : X → Set (X × X) → X → ℕ,
      ∃ G : SimpleGraph X, G.CliqueFree 4 ∧ ∃ a b c : X,
        a < b ∧ b < c ∧ G.Adj a b ∧ G.Adj a c ∧ G.Adj b c ∧
        let past := fun j => {p : X × X | p.1 ≤ j ∧ p.2 ≤ j ∧ G.Adj p.1 p.2}
        paint b (past b) a = paint c (past c) a ∧ paint b (past b) a = paint c (past c) b
    loses I → loses J := by
  intro loses small paint
  obtain ⟨run,matchRun⟩ := horizon_simulation e paint
  obtain ⟨G,free,a,b,c,ab,bc,hab,hac,hbc,h⟩ := small run
  refine ⟨G.map e.toEmbedding,cliqueFree_map_iff.mpr free,e a,e b,e c,
    e.strictMono ab,e.strictMono bc,map_adj_apply.mpr hab,map_adj_apply.mpr hac,
    map_adj_apply.mpr hbc,?_⟩
  exact ⟨(matchRun G a b).symm.trans (h.1.trans (matchRun G a c)),
    (matchRun G a b).symm.trans (h.2.trans (matchRun G b c))⟩

/-- Winning on each induced set of stages suffices when the set of pieces
injects into binary sequences. The pieces may interleave in the stage order. -/
theorem combine_painters {I K : Type} [LinearOrder I] (part : I → K)
    (code : K ↪ (ℕ → Bool)) :
    let wins (X : Type) [LinearOrder X] := ∃ paint : X → Set (X × X) → X → ℕ,
      ∀ (G : SimpleGraph X), G.CliqueFree 4 → ∀ a b c,
        a < b → b < c → G.Adj a b → G.Adj a c → G.Adj b c →
        let past := fun j => {p : X × X | p.1 ≤ j ∧ p.2 ≤ j ∧ G.Adj p.1 p.2}
        paint b (past b) a = paint c (past c) a → paint b (past b) a ≠ paint c (past c) b
    (∀ k, wins {i // part i = k}) → wins I := by
  classical
  intro wins localWins
  choose inner safe using localWins
  let fibre k := {i // part i = k}
  let restrict (k : K) (s : Set (I × I)) := {p : fibre k × fibre k | (p.1.val,p.2.val) ∈ s}
  have split {k l : K} (ne : k ≠ l) : ∃ n, code k n ≠ code l n := by
    by_contra! same
    exact ne (code.injective (funext same))
  let paint (j : I) (s : Set (I × I)) (i : I) :=
    if h : part i = part j then
      2 * inner (part j) ⟨j,rfl⟩ (restrict _ s) ⟨i,h⟩
    else 2 * (split h).choose + 1
  have cross {i j : I} (h : part i ≠ part j) (s) :
      ∃ n, paint j s i = 2*n+1 ∧ code (part i) n ≠ code (part j) n :=
    ⟨_,dif_neg h,(split h).choose_spec⟩
  have within (k : K) {i j : I} (hi : part i = k) (hj : part j = k) (s) :
      paint j s i = 2 * inner k ⟨j,hj⟩ (restrict k s) ⟨i,hi⟩ := by
    cases hj
    simp [paint,hi]
  refine ⟨paint,?_⟩
  intro G legal a b c ab bc hab hac hbc
  let past (j : I) := {p : I × I | p.1 ≤ j ∧ p.2 ≤ j ∧ G.Adj p.1 p.2}
  change paint b (past b) a = paint c (past c) a → paint b (past b) a ≠ paint c (past c) b
  intro x y
  by_cases eq : part a = part b
  · have even := within _ eq rfl (past b)
    by_cases eq' : part b = part c
    · let k := part c
      let inc : fibre k ↪ I := Function.Embedding.subtype _
      let F := G.comap inc
      have free := legal.comap (SimpleGraph.Embedding.comap inc G).isContained
      have ok := safe k F free ⟨a,eq.trans eq'⟩ ⟨b,eq'⟩ ⟨c,rfl⟩ ab bc hab hac hbc
      rw [within k (eq.trans eq') eq',within k (eq.trans eq') rfl] at x
      rw [within k (eq.trans eq') eq',within k eq' rfl] at y
      exact ok (by exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) x)
        (by exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) y)
    · obtain ⟨n,odd,_⟩ := cross eq' (past c)
      omega
  · obtain ⟨n,odd,dab⟩ := cross eq (past b)
    by_cases ac : part a = part c
    · have even := within _ ac rfl (past c)
      omega
    by_cases bc' : part b = part c
    · have even := within _ bc' rfl (past c)
      omega
    obtain ⟨m,om,dac⟩ := cross ac (past c)
    obtain ⟨l,ol,dbc⟩ := cross bc' (past c)
    obtain rfl : m = n := by omega
    obtain rfl : l = m := by omega
    have impossible (i j k : Bool) : i ≠ j → i ≠ k → j ≠ k → False := by
      cases i <;> cases j <;> cases k <;> decide
    exact impossible _ _ _ dab dac dbc

open Filter

/-- A family of bounded natural numbers is constant on a member of an
ultrafilter. The bound can be different for each Painter decision. -/
private theorem bounded_value {A : Type} (u : Ultrafilter A) (v : A → ℕ) (n : ℕ)
    (h : ∀ᶠ t in u, v t ≤ n) : ∃ k ≤ n, ∀ᶠ t in u, v t = k := by
  induction n with
  | zero => exact ⟨0,by omega,h.mono (fun _ ht => by omega)⟩
  | succ n ih =>
    have cases' : ∀ᶠ t in u, v t ≤ n ∨ v t = n+1 := h.mono fun _ ht => by omega
    rcases Ultrafilter.eventually_or.mp cases' with low | top
    · obtain ⟨k,hk,eq⟩ := ih low
      exact ⟨k,by omega,eq⟩
    · exact ⟨n+1,le_rfl,top⟩

/-- Prefix Painters need not agree on common histories. They give a global
Painter exactly when they can be chosen with one finite bound per decision,
independent of the cutoff. No uniform bound across decisions is required. -/
theorem prefix_budget_iff {I : Type} [LinearOrder I] [Nonempty I] :
    let safe := fun (p : I → Set (I × I) → I → ℕ) (c : I) =>
      ∀ (G : SimpleGraph I), G.CliqueFree 4 → ∀ a b,
        a < b → b < c → G.Adj a b → G.Adj a c → G.Adj b c →
        let past := fun j => {q : I × I | q.1 ≤ j ∧ q.2 ≤ j ∧ G.Adj q.1 q.2}
        p b (past b) a = p c (past c) a → p b (past b) a ≠ p c (past c) b
    (∃ p, ∀ c, safe p c) ↔ ∃ budget : I → Set (I × I) → I → ℕ,
      ∀ t : I, ∃ p, (∀ j ≤ t, ∀ s i, p j s i ≤ budget j s i) ∧ ∀ c ≤ t, safe p c := by
  classical
  intro safe
  constructor
  · rintro ⟨p,win⟩
    exact ⟨p,fun _ => ⟨p,fun _ _ _ _ => le_rfl,fun c _ => win c⟩⟩
  · rintro ⟨budget,h⟩
    choose rule bound ok using h
    let u := Ultrafilter.of (Filter.atTop : Filter I)
    have tail (i : I) : ∀ᶠ t in u, i ≤ t := Ultrafilter.of_le _ (Filter.eventually_ge_atTop i)
    have stable (j : I) (s : Set (I × I)) (i : I) :=
      bounded_value u (fun t => rule t j s i) (budget j s i)
        ((tail j).mono fun t hj => bound t j hj s i)
    let p j s i := (stable j s i).choose
    have agree (j s i) : ∀ᶠ t in u, rule t j s i = p j s i := (stable j s i).choose_spec.2
    refine ⟨p,?_⟩
    intro c G legal a b ab bc eab eac ebc past x y
    obtain ⟨t,ht,h₁,h₂,h₃⟩ :=
      ((tail c).and ((agree b (past b) a).and ((agree c (past c) a).and (agree c (past c) b)))).exists
    exact ok t c ht G legal a b ab bc eab eac ebc
      (h₁.trans (x.trans h₂.symm)) (h₁.trans (y.trans h₃.symm))

/-- A test names a legal play and three chronologically ordered vertices.
For a fixed budget, finite simultaneous satisfiability suffices, even when
different tests use different plays but share decisions on identical prefixes. -/
theorem finite_triangle_tests {I : Type} [LinearOrder I]
    (budget : I → Set (I × I) → I → ℕ) :
    let bounded := fun (p : I → Set (I × I) → I → ℕ) => ∀ j s i, p j s i ≤ budget j s i
    let passes := fun (p : I → Set (I × I) → I → ℕ) (t : SimpleGraph I × I × I × I) =>
      let (G,a,b,c) := t
      G.CliqueFree 4 → a < b → b < c → G.Adj a b → G.Adj a c → G.Adj b c →
        let past := fun j => {q : I × I | q.1 ≤ j ∧ q.2 ≤ j ∧ G.Adj q.1 q.2}
        p b (past b) a = p c (past c) a → p b (past b) a ≠ p c (past c) b
    (∀ S : Finset (SimpleGraph I × I × I × I), ∃ p, bounded p ∧ ∀ t ∈ S, passes p t) ↔
      ∃ p, bounded p ∧ ∀ t, passes p t := by
  classical
  intro bounded passes
  constructor
  · intro finiteOK
    choose rule cap ok using finiteOK
    let T := SimpleGraph I × I × I × I
    let u := Ultrafilter.of (Filter.atTop : Filter (Finset T))
    have stable (j : I) (s : Set (I × I)) (i : I) :=
      bounded_value u (fun S => rule S j s i) (budget j s i)
        (Filter.Eventually.of_forall fun S => cap S j s i)
    let p j s i := (stable j s i).choose
    have agree (j s i) : ∀ᶠ S in u, rule S j s i = p j s i := (stable j s i).choose_spec.2
    refine ⟨p,fun j s i => (stable j s i).choose_spec.1,?_⟩
    rintro ⟨G,a,b,c⟩ legal ab bc eab eac ebc past x y
    have fine : ∀ᶠ (S : Finset T) in u, (G,a,b,c) ∈ S :=
      Ultrafilter.of_le _ (Filter.eventually_finset_mem_atTop _)
    obtain ⟨S,mem,h₁,h₂,h₃⟩ :=
      (fine.and ((agree b (past b) a).and ((agree c (past c) a).and (agree c (past c) b)))).exists
    exact ok S _ mem legal ab bc eab eac ebc (h₁.trans (x.trans h₂.symm)) (h₁.trans (y.trans h₃.symm))
  · rintro ⟨p,cap,ok⟩
    exact fun _ => ⟨p,cap,fun t _ => ok t⟩

/-- Painter can handle all plays with countably many earlier neighbours at
each stage, on any horizon. Both spokes into the last vertex of a triangle
receive different colours. The numbering uses only the revealed prefix. -/
theorem countable_incoming {I : Type} [LinearOrder I] :
    ∃ paint : I → Set (I × I) → I → ℕ, ∀ (G : SimpleGraph I),
      (∀ j, Nonempty ({i : I // i < j ∧ G.Adj i j} ↪ ℕ)) → ∀ a b c,
        a < b → b < c → G.Adj a c → G.Adj b c →
        let s := {p : I × I | p.1 ≤ c ∧ p.2 ≤ c ∧ G.Adj p.1 p.2}
        paint c s a ≠ paint c s b := by
  classical
  let row (j : I) (s : Set (I × I)) := {i : I // i < j ∧ (i,j) ∈ s}
  let paint (j : I) (s : Set (I × I)) (i : I) :=
    if h : Nonempty (row j s ↪ ℕ) then
      if hi : i < j ∧ (i,j) ∈ s then h.some ⟨i,hi⟩ else 0
    else 0
  refine ⟨paint,?_⟩
  intro G small a b c ab bc acEdge bcEdge s
  let index : row c s ↪ {i : I // i < c ∧ G.Adj i c} :=
    ⟨fun i => ⟨i.val,i.property.1,i.property.2.2.2⟩,fun _ _ eq => Subtype.ext (congrArg (fun z : {i : I // i < c ∧ G.Adj i c} => z.val) eq)⟩
  have h : Nonempty (row c s ↪ ℕ) := ⟨index.trans (small c).some⟩
  have ac := ab.trans bc
  have ha : a < c ∧ (a,c) ∈ s := ⟨ac,ac.le,le_rfl,acEdge⟩
  have hb : b < c ∧ (b,c) ∈ s := ⟨bc,bc.le,le_rfl,bcEdge⟩
  intro eq
  simp only [paint,dif_pos h,dif_pos ha,dif_pos hb] at eq
  exact ab.ne (congrArg Subtype.val (h.some.injective eq))

/-- The finite Folkman and homogeneous-set inputs are explicit. A Painter
safe even just on finite-support plays must use unbounded colours on some
fixed pair of stages as the revealed graph varies. For the classical
application, the countable-colour pair relation of Erdos and Rado supplies
the homogeneous set above the continuum. -/
theorem unbounded_on_one_pair {I : Type} [LinearOrder I]
    (homogeneous : ∀ bound : I → I → ℕ, ∃ n, ∃ seq : ℕ ↪ I,
      ∀ a b, a ≠ b → bound (min (seq a) (seq b)) (max (seq a) (seq b)) ≤ n)
    (folkman : ∀ n : ℕ, 1 ≤ n → ∃ (V : Type) (_ : Fintype V) (F : SimpleGraph V),
      F.CliqueFree 4 ∧ ∀ L : Fin n → SimpleGraph V, (∀ k, (L k).CliqueFree 3) → F ≠ ⨆ k,L k)
    (paint : I → Set (I × I) → I → ℕ)
    (win : ∀ (G : SimpleGraph I), G.CliqueFree 4 → G.support.Finite → ∀ a b c,
      a < b → b < c → G.Adj a b → G.Adj a c → G.Adj b c →
      let past := fun j => {p : I × I | p.1 ≤ j ∧ p.2 ≤ j ∧ G.Adj p.1 p.2}
      paint b (past b) a = paint c (past c) a → paint b (past b) a ≠ paint c (past c) b) :
    ∃ a b : I, a < b ∧ ∀ n : ℕ, ∃ G : SimpleGraph I, G.CliqueFree 4 ∧
      G.support.Finite ∧ G.Adj a b ∧ n < paint b {p | p.1 ≤ b ∧ p.2 ≤ b ∧ G.Adj p.1 p.2} a := by
  classical
  by_contra! bounded
  have bounds (a b : I) : ∃ n : ℕ, ∀ G : SimpleGraph I, G.CliqueFree 4 → G.support.Finite →
      a < b → G.Adj a b → paint b {p | p.1 ≤ b ∧ p.2 ≤ b ∧ G.Adj p.1 p.2} a ≤ n := by
    by_cases h : a < b
    · obtain ⟨n,hn⟩ := bounded a b h
      exact ⟨n,fun G free fin _ adj => hn G free fin adj⟩
    · exact ⟨0,fun _ _ _ lt => (h lt).elim⟩
  choose B cap using bounds
  obtain ⟨n,seq,flat⟩ := homogeneous B
  obtain ⟨V,fin,F,legal,hard⟩ := folkman (n+1) (by omega)
  let : Fintype V := fin
  cases isEmpty_or_nonempty V with
  | inl empty =>
    exact hard (fun _ => ⊥) (fun _ => cliqueFree_bot (by decide)) (Subsingleton.elim _ _)
  | inr nonempty =>
    let idx := (Fintype.equivFin V).toEmbedding.trans Fin.valEmbedding
    let e := idx.trans seq
    let G := F.map e
    have free : G.CliqueFree 4 := cliqueFree_map_iff.mpr legal
    have finiteSupport : G.support.Finite := by
      rw [show G = F.map e from rfl,support_map]
      exact (Set.toFinite _).image _
    let past (j : I) := {p : I × I | p.1 ≤ j ∧ p.2 ≤ j ∧ G.Adj p.1 p.2}
    let colour (a b : I) := paint (max a b) (past (max a b)) (min a b)
    let L (k : Fin (n+1)) : SimpleGraph I := {
      Adj a b := G.Adj a b ∧ colour a b = k.val
      symm := ⟨fun a b h => ⟨h.1.symm, by simpa only [colour,max_comm b a,min_comm b a] using h.2⟩⟩
      loopless := ⟨fun _ h => h.1.ne rfl⟩ }
    have triangleFree (k : Fin (n+1)) : (L k).CliqueFree 3 := by
      intro s cl
      let v := s.orderEmbOfFin cl.card_eq
      have edge (i j : Fin 3) (h : i < j) :
          G.Adj (v i) (v j) ∧ paint (v j) (past (v j)) (v i) = k.val := by
        have adj : (L k).Adj (v i) (v j) := cl.isClique
          (s.orderEmbOfFin_mem _ i) (s.orderEmbOfFin_mem _ j) (v.strictMono h).ne
        exact ⟨adj.1, by simpa only [colour,max_eq_right (v.monotone h.le),min_eq_left (v.monotone h.le)] using adj.2⟩
      have ab := edge 0 1 (by decide)
      have ac := edge 0 2 (by decide)
      have bc := edge 1 2 (by decide)
      exact win G free finiteSupport _ _ _ (v.strictMono (by decide : (0 : Fin 3) < 1))
        (v.strictMono (by decide : (1 : Fin 3) < 2)) ab.1 ac.1 bc.1
        (ab.2.trans ac.2.symm) (ab.2.trans bc.2.symm)
    apply hard (fun k => (L k).comap e) (fun k =>
      (triangleFree k).comap (SimpleGraph.Embedding.comap e (L k)).isContained)
    ext x y
    rw [iSup_adj]
    constructor
    · intro xy
      have gxy : G.Adj (e x) (e y) := map_adj_apply.mpr xy
      have h : colour (e x) (e y) ≤ n := by
        have bound := flat (idx x) (idx y) (idx.injective.ne xy.ne)
        change B (min (e x) (e y)) (max (e x) (e y)) ≤ n at bound
        apply le_trans _ bound
        rcases lt_or_gt_of_ne (e.injective.ne xy.ne) with lt | gt
        · simpa only [colour,min_eq_left lt.le,max_eq_right lt.le] using
            cap (e x) (e y) G free finiteSupport lt gxy
        · simpa only [colour,min_eq_right gt.le,max_eq_left gt.le] using
            cap (e y) (e x) G free finiteSupport gt gxy.symm
      exact ⟨⟨_,Nat.lt_succ_of_le h⟩,gxy,rfl⟩
    · rintro ⟨k,hk⟩
      exact map_adj_apply.mp hk.1

/-- Encode within-label colours by even numbers and distinguish different
binary labels at an odd coordinate colour. In any monochromatic triangle the
labels coincide and the two incoming within-label colours agree. -/
private theorem binary_label_palette :
    ∃ edge : (ℕ → Bool) → (ℕ → Bool) → ℕ → ℕ, (∀ A i, edge A A i = 2*i) ∧ ∀ A B C i j k,
      edge A B i = edge A C j → edge A B i = edge B C k →
      A = C ∧ B = C ∧ j = k := by
  classical
  have diff {A B : ℕ → Bool} (h : A ≠ B) : ∃ n, A n ≠ B n := by
    by_contra! same
    exact h (funext same)
  let edge (A B : ℕ → Bool) (i : ℕ) := if h : A = B then 2*i else 2*(diff h).choose+1
  refine ⟨edge,fun A i => by simp [edge],?_⟩
  intro A B C i j k ab ac
  by_cases h : A = B
  · subst B
    by_cases g : A = C
    · subst C
      simp only [edge,dif_pos rfl] at ab ac
      exact ⟨rfl,rfl,by omega⟩
    · simp only [edge,dif_pos rfl,dif_neg g] at ab
      omega
  · by_cases g : A = C
    · simp only [edge,dif_neg h,dif_pos g] at ab
      omega
    by_cases f : B = C
    · simp only [edge,dif_neg h,dif_pos f] at ac
      omega
    simp only [edge,dif_neg h,dif_neg g,dif_neg f] at ab ac
    have m : (diff g).choose = (diff h).choose := by omega
    have n : (diff f).choose = (diff h).choose := by omega
    have hg := (diff g).choose_spec
    have hf := (diff f).choose_spec
    rw [m] at hg
    rw [n] at hf
    have impossible (a b c : Bool) : a ≠ b → a ≠ c → b ≠ c → False := by
      cases a <;> cases b <;> cases c <;> decide
    exact False.elim (impossible _ _ _ (diff h).choose_spec hg hf)

/-- Within a label fibre, compare candidate spoke colours with the actual
old edge colour. The even coding is shared by all within-fibre edges. -/
theorem greedy_edge_painter {I : Type} [LinearOrder I] [WellFoundedLT I] :
    ∃ paint : I → Set (I × I) → I → ℕ, ∀ (G : SimpleGraph I) (j : I),
      let past := fun i => {p : I × I | p.1 ≤ i ∧ p.2 ≤ i ∧ G.Adj p.1 p.2}
      (∀ lab : I → (ℕ → Bool), ∃ (k : ℕ → Bool) (d : I → ℕ), ∀ a b,
        a < b → b < j → G.Adj a j → G.Adj b j → G.Adj a b →
        lab a = k → lab b = k → d a = d b → paint b (past b) a ≠ 2*d a) →
      ∀ a b, a < b → b < j → G.Adj a b → G.Adj a j → G.Adj b j →
        paint b (past b) a = paint j (past j) a → paint b (past b) a ≠ paint j (past j) b := by
  classical
  obtain ⟨edge,diag,palette⟩ := binary_label_palette
  let Prefix := Set (I × I)
  let State := (ℕ → Bool) × (I → ℕ)
  let cut (s : Prefix) (i : I) := {p : I × I | p.1 ≤ i ∧ p.2 ≤ i ∧ p ∈ s}
  let labels (j : I) (rec : ∀ i : I, i < j → Prefix → State) (s : Prefix) (i : I) :=
    if h : i < j then (rec i h (cut s i)).1 else fun _ => false
  let oldIndex (j : I) (rec : ∀ i : I, i < j → Prefix → State) (s : Prefix) (a b : I) :=
    if h : b < j then (rec b h (cut s b)).2 a else 0
  let good (j : I) (s : Prefix) (lab : I → ℕ → Bool) (old : I → I → ℕ) (v : State) :=
    ∀ a b : I, a < b → b < j → (a,j) ∈ s → (b,j) ∈ s → (a,b) ∈ s →
      lab a = v.1 → lab b = v.1 → v.2 a = v.2 b → old a b ≠ v.2 a
  let chooseState (j : I) (rec : ∀ i : I, i < j → Prefix → State) (s : Prefix) : State :=
    if h : ∃ v, good j s (labels j rec s) (oldIndex j rec s) v then h.choose
    else (fun _ => false,fun _ => 0)
  let state : I → Prefix → State := wellFounded_lt.fix chooseState
  have law (j : I) (s : Prefix) : state j s = chooseState j (fun i _ => state i) s :=
    congrFun (WellFounded.fix_eq _ _ j) s
  let paint (j : I) (s : Prefix) (a : I) :=
    edge (state a (cut s a)).1 (state j s).1 ((state j s).2 a)
  refine ⟨paint,?_⟩
  intro G j past localOK a b ab bj gab gaj gbj mono clash
  have trunc {u v : I} (le : u ≤ v) : cut (past v) u = past u := by
    ext p
    exact ⟨fun h => ⟨h.1,h.2.1,h.2.2.2.2⟩,fun h =>
      ⟨h.1,h.2.1,h.1.trans le,h.2.1.trans le,h.2.2⟩⟩
  let lab := labels j (fun i _ => state i) (past j)
  have earlier {i : I} (h : i < j) : lab i = (state i (past i)).1 := by
    simp [lab,labels,h,trunc h.le]
  let old := oldIndex j (fun i _ => state i) (past j)
  have stored {u v : I} (vj : v < j) : old u v = (state v (past v)).2 u := by
    simp [old,oldIndex,vj,trunc vj.le]
  obtain ⟨k,d,possible⟩ := localOK lab
  have existsGood : ∃ v, good j (past j) lab old v := by
    refine ⟨(k,d),?_⟩
    intro u v uv vj hu hv he lu lv same collision
    apply possible u v uv vj hu.2.2 hv.2.2 he.2.2 lu lv same
    have labs := (earlier (uv.trans vj)).symm.trans ((lu.trans lv.symm).trans (earlier vj))
    change old u v = d u at collision
    simp only [paint,trunc uv.le,labs,diag,← stored vj,collision]
  have usable : good j (past j) lab old (state j (past j)) := by
    rw [law j (past j)]
    change good j (past j) lab old (if h : ∃ v, good j (past j) lab old v then h.choose else _)
    rw [dif_pos existsGood]
    exact existsGood.choose_spec
  have aj := ab.trans bj
  simp only [paint,trunc ab.le,trunc bj.le,trunc aj.le] at mono clash
  obtain ⟨ha,hb,same⟩ := palette _ _ _ _ _ _ mono clash
  have forbid := usable a b ab bj ⟨aj.le,le_rfl,gaj⟩ ⟨bj.le,le_rfl,gbj⟩ ⟨aj.le,bj.le,gab⟩
    ((earlier aj).trans ha) ((earlier bj).trans hb) same
  rw [ha,hb,diag,diag] at mono
  exact forbid ((stored bj).trans (by omega))

/-- A single Painter localizes any defeat to a large family of disjoint
obstructions in the earlier neighbourhood of the LAST vertex of a bad
triangle. If every assignment of real labels has some countably colourable
fibre there, the triangle is safe regardless of the earlier neighbourhoods. -/
theorem greedy_rim_painter {I : Type} [LinearOrder I] [WellFoundedLT I] :
    ∃ paint : I → Set (I × I) → I → ℕ, ∀ (G : SimpleGraph I) (j : I),
      (∀ lab : I → (ℕ → Bool), ∃ (k : ℕ → Bool) (d : I → ℕ), ∀ a b,
        a < j → b < j → G.Adj a j → G.Adj b j → G.Adj a b →
        lab a = k → lab b = k → d a ≠ d b) →
      ∀ a b, a < b → b < j → G.Adj a b → G.Adj a j → G.Adj b j →
        let past := fun i => {p : I × I | p.1 ≤ i ∧ p.2 ≤ i ∧ G.Adj p.1 p.2}
        paint b (past b) a = paint j (past j) a → paint b (past b) a ≠ paint j (past j) b := by
  obtain ⟨p,works⟩ := greedy_edge_painter (I := I)
  refine ⟨p,?_⟩
  intro G j localOK
  apply works G j
  intro lab
  obtain ⟨k,d,proper⟩ := localOK lab
  exact ⟨k,d,fun a b ab bj ha hb he la lb eq =>
    False.elim (proper a b (ab.trans bj) bj ha hb he la lb eq)⟩

/-- The same Painter works on every play. For a fixed witness take its first
monochromatic triangle stage. A single earlier colouring then obstructs every
even spoke assignment in every fibre of one real labelling of the rim. -/
theorem first_blocked_rim {I : Type} [LinearOrder I] [WellFoundedLT I] :
    ∃ paint : I → Set (I × I) → I → ℕ, ∀ (G : SimpleGraph I),
      ¬ Erdos595.IsCountableUnionOfTriangleFree G →
      let old := fun a b => paint b {p : I × I | p.1 ≤ b ∧ p.2 ≤ b ∧ G.Adj p.1 p.2} a
      let fails := fun t => ∃ a b, a < b ∧ b < t ∧ G.Adj a b ∧ G.Adj a t ∧ G.Adj b t ∧
        old a b = old a t ∧ old a b = old b t
      ∃ j, fails j ∧ (∀ t < j, ¬fails t) ∧ ∃ lab : I → ℕ → Bool,
        ∀ (k : ℕ → Bool) (d : I → ℕ), ∃ a b, a < b ∧ b < j ∧
          G.Adj a j ∧ G.Adj b j ∧ G.Adj a b ∧ lab a = k ∧ lab b = k ∧
          d a = d b ∧ old a b = 2*d a := by
  classical
  obtain ⟨paint,works⟩ := greedy_edge_painter (I := I)
  refine ⟨paint,?_⟩
  intro G bad old fails
  obtain ⟨a,b,c,ab,bc,gab,gac,gbc,mono⟩ := fixed_play G bad paint
  have someFail : {t | fails t}.Nonempty := ⟨c,a,b,ab,bc,gab,gac,gbc,mono⟩
  obtain ⟨j,hj,first⟩ := wellFounded_lt.has_min {t | fails t} someFail
  refine ⟨j,hj,fun t lt ht => first t ht lt,?_⟩
  by_contra! possible
  obtain ⟨u,v,uv,vj,guv,guj,gvj,x,y⟩ := hj
  exact works G j possible u v uv vj guv guj gvj x y

/-- Apply to the ordered rim edges within one fibre of first_blocked_rim.
Deleting any countably vertex-colourable set still leaves an edge of each
even colour. In particular no countable vertex cover hits a whole such layer. -/
theorem blocked_colour_survives {I : Type} (R : I → I → Prop) (old : I → I → ℕ)
    (blocked : ∀ d : I → ℕ, ∃ a b, R a b ∧ d a = d b ∧ old a b = 2*d a)
    (S : Set I) (proper : ∃ f : I → ℕ, ∀ a b, R a b → a ∈ S → b ∈ S → f a ≠ f b)
    (m : ℕ) : ∃ a b, R a b ∧ a ∉ S ∧ b ∉ S ∧ old a b = 2*m := by
  classical
  obtain ⟨f,hf⟩ := proper
  let d (a : I) := if a ∈ S then m+1+f a else m
  obtain ⟨a,b,edge,same,hit⟩ := blocked d
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ S
  · simp only [d,if_pos ha,if_pos hb] at same
    exact False.elim (hf a b edge ha hb (by omega))
  · simp only [d,if_pos ha,if_neg hb] at same
    omega
  · simp only [d,if_neg ha,if_pos hb] at same
    omega
  · exact ⟨a,b,edge,ha,hb,by simpa [d,ha] using hit⟩

/-- Extend unbounded vertex lists to a proper list colouring when every
conflict neighbourhood is countable. Reachable vertices are indexed by finite
walk codes, as in the component argument of the first reduction. -/
private theorem component_list_colouring {I : Type} (F : I → I → Prop)
    (sym : ∀ x y, F x y → F y x) (loop : ∀ x, ¬ F x x)
    (small : ∀ x, Set.Countable {y | F x y}) (A : I → ℕ → Prop)
    (unbounded : ∀ x m, ∃ n, m < n ∧ A x n) :
    ∃ d : I → ℕ, (∀ x, A x (d x)) ∧ ∀ x y, F x y → d x ≠ d y := by
  classical
  let C (x : I) := {y | Relation.ReflTransGen F x y}
  let step (x : I) := Set.enumerateCountable (small x) x
  have size (x : I) : (C x).Countable := by
    apply (Set.countable_range (fun w : List ℕ => w.foldl step x)).mono
    intro y hy
    induction hy with
    | refl => exact ⟨[],rfl⟩
    | @tail b c _ edge ih =>
      obtain ⟨w,hw⟩ := ih
      obtain ⟨n,hn⟩ := Set.subset_range_enumerate (small b) b edge
      exact ⟨w ++ [n], by simpa [List.foldl_append,hw,step] using hn⟩
  have assign (S : Set I) : ∃ g : I → ℕ, S.Countable →
      (∀ x ∈ S, A x (g x)) ∧ Set.InjOn g S := by
    by_cases hs : S.Countable
    · let : Countable S := hs
      let := Encodable.ofCountable S
      let e : S ↪ ℕ := ⟨Encodable.encode, Encodable.encode_injective⟩
      have next (k m : ℕ) : ∃ n, m < n ∧ ∀ x : S, e x = k → A x n := by
        by_cases hit : ∃ x, e x = k
        · obtain ⟨x,rfl⟩ := hit
          obtain ⟨n,lt,ok⟩ := unbounded x m
          exact ⟨n,lt,fun y eq => e.injective eq ▸ ok⟩
        · exact ⟨m+1,by omega,fun x eq => (hit ⟨x,eq⟩).elim⟩
      let seq : ℕ → ℕ := Nat.rec (next 0 0).choose (fun k v => (next (k+1) v).choose)
      have mono : StrictMono seq := strictMono_nat_of_lt_succ fun k =>
        (next (k+1) (seq k)).choose_spec.1
      have valid (k : ℕ) : ∀ x : S, e x = k → A x (seq k) := by
        cases k with
        | zero => exact (next 0 0).choose_spec.2
        | succ k => exact (next (k+1) (seq k)).choose_spec.2
      refine ⟨fun x => if hx : x ∈ S then seq (e ⟨x,hx⟩) else 0, fun _ => ⟨?_,?_⟩⟩
      · intro x hx
        simpa only [dif_pos hx] using valid _ ⟨x,hx⟩ rfl
      · intro x hx y hy eq
        simp only [dif_pos hx,dif_pos hy] at eq
        exact congrArg Subtype.val (e.injective (mono.injective eq))
    · exact ⟨fun _ => 0,fun hc => (hs hc).elim⟩
  choose g hg using assign
  have self (x : I) : x ∈ C x := Relation.ReflTransGen.refl
  refine ⟨fun x => g (C x) x,fun x => (hg _ (size x)).1 x (self x),?_⟩
  intro x y edge
  have eq : C y = C x := Set.ext fun _ => ⟨fun h => Relation.ReflTransGen.head edge h,
    fun h => Relation.ReflTransGen.head (sym _ _ edge) h⟩
  change g (C x) x ≠ g (C y) y
  rw [eq]
  intro same
  exact loop x (((hg _ (size x)).2 (self x) (eq ▸ self y) same).symm ▸ edge)

/-- In a blocked fibre, reserve the old colours 4n as probes. Restricting
to vertices of uncountable degree in all but finitely many probe layers
still blocks every assignment from the remaining old colours 4n+2. -/
theorem blocked_high_degree {I : Type} (R : I → I → Prop) (loop : ∀ x, ¬ R x x)
    (old : I → I → ℕ)
    (blocked : ∀ d : I → ℕ, ∃ a b, R a b ∧ d a = d b ∧ old a b = 2*d a)
    (h : I → ℕ) :
    let near := fun x n => {y | (R x y ∧ old x y = 4*n) ∨ (R y x ∧ old y x = 4*n)}
    let rich := fun x => ∃ m : ℕ, ∀ n > m, ¬ (near x n).Countable
    ∃ a b, R a b ∧ rich a ∧ rich b ∧ h a = h b ∧ old a b = 4*h a+2 := by
  classical
  intro near rich
  let L (x : I) (n : ℕ) := (near x n).Countable
  let F (x y : I) := ¬rich x ∧ ¬rich y ∧ ∃ n, L x n ∧ L y n ∧ y ∈ near x n
  have sym x y (e : F x y) : F y x := by
    obtain ⟨hx,hy,n,lx,ly,xy⟩ := e
    exact ⟨hy,hx,n,ly,lx,Or.symm xy⟩
  have irr x (e : F x x) : False := by
    obtain ⟨_,_,n,_,_,p | p⟩ := e <;> exact loop x p.1
  have small x : Set.Countable {y | F x y} := by
    let B (n : ℕ) : Set I := if L x n then near x n else ∅
    have hb n : (B n).Countable := by
      by_cases hl : L x n
      · simpa [B,hl] using (show (near x n).Countable from hl)
      · simp [B,hl]
    apply (Set.countable_iUnion hb).mono
    rintro y ⟨_,_,n,hx,_,hy⟩
    exact Set.mem_iUnion.mpr ⟨n,by simpa [B,hx] using hy⟩
  have unbd x m : ∃ n, m < n ∧ (rich x ∨ L x n) := by
    by_cases hx : rich x
    · exact ⟨m+1,by omega,Or.inl hx⟩
    · by_contra! hn
      exact hx ⟨m,fun n lt => (hn n lt).2⟩
  obtain ⟨g,allowed,proper⟩ := component_list_colouring F sym irr small _ unbd
  let d (x : I) := if rich x then 2*h x+1 else 2*g x
  obtain ⟨a,b,ab,same,hit⟩ := blocked d
  by_cases ha : rich a <;> by_cases hb : rich b <;> simp only [d,ha,hb,if_true,if_false] at same hit
  · exact ⟨a,b,ab,ha,hb,by omega,by omega⟩
  · omega
  · omega
  · have eq : g a = g b := by omega
    exact (proper a b ⟨ha,hb,g a,(allowed a).resolve_left ha,
      eq ▸ (allowed b).resolve_left hb,Or.inl ⟨ab,by omega⟩⟩ eq).elim

/-- One round of the high-degree argument inside a specified vertex set,
with the surviving palette indexed by an arbitrary injection. -/
private theorem blocked_subset_step {I : Type} (R : I → I → Prop) (loop : ∀ x, ¬ R x x)
    (old : I → I → ℕ) (p : ℕ → ℕ) (inj : Function.Injective p) (S : Set I)
    (bad : ∀ d : I → ℕ, ∃ a b, a ∈ S ∧ b ∈ S ∧ R a b ∧ d a = d b ∧ old a b = p (d a)) :
    ∃ T ⊆ S, (∀ x ∈ T, ∃ m : ℕ, ∀ n > m, ¬ Set.Countable
      {y | y ∈ S ∧ ((R x y ∧ old x y = p (2*n)) ∨ (R y x ∧ old y x = p (2*n)))}) ∧
      ∀ d : I → ℕ, ∃ a b, a ∈ T ∧ b ∈ T ∧ R a b ∧ d a = d b ∧ old a b = p (2*d a+1) := by
  classical
  let E (x y : I) := x ∈ S ∧ y ∈ S ∧ R x y
  let code (v : ℕ) := if h : ∃ n, v = p n then 2*h.choose else 1
  have decode (v n : ℕ) : code v = 2*n ↔ v = p n := by
    by_cases h : ∃ k, v = p k
    · simp only [code,dif_pos h]
      constructor
      · intro e
        have k : h.choose = n := by omega
        exact k ▸ h.choose_spec
      · intro e
        rw [inj (h.choose_spec.symm.trans e)]
    · simp only [code,dif_neg h]
      exact ⟨fun e => by omega,fun e => (h ⟨n,e⟩).elim⟩
  have blocked (d : I → ℕ) : ∃ a b, E a b ∧ d a = d b ∧ code (old a b) = 2*d a := by
    obtain ⟨a,b,ha,hb,ab,same,hit⟩ := bad d
    exact ⟨a,b,⟨ha,hb,ab⟩,same,(decode _ _).2 hit⟩
  let N (x : I) (n : ℕ) := {y | (E x y ∧ code (old x y) = 4*n) ∨
    (E y x ∧ code (old y x) = 4*n)}
  let T := {x | x ∈ S ∧ ∃ m : ℕ, ∀ n > m, ¬ (N x n).Countable}
  refine ⟨T,fun _ hx => hx.1,?_,?_⟩
  · rintro x ⟨_,m,hm⟩
    refine ⟨m,fun n lt hc => hm n lt (hc.mono ?_)⟩
    rintro y (⟨e,hit⟩ | ⟨e,hit⟩)
    · exact ⟨e.2.1,Or.inl ⟨e.2.2,(decode _ _).1 (by omega)⟩⟩
    · exact ⟨e.1,Or.inr ⟨e.2.2,(decode _ _).1 (by omega)⟩⟩
  · intro d
    obtain ⟨a,b,ab,ra,rb,same,hit⟩ := blocked_high_degree E (fun x e => loop x e.2.2)
      (fun x y => code (old x y)) blocked d
    exact ⟨a,b,⟨ab.1,ra⟩,⟨ab.2.1,rb⟩,ab.2.2,same,(decode _ _).1 (by omega)⟩

/-- A blocked fibre has nested nonempty sets at all finite depths. Probe degrees
at depth k+1 are measured inside depth k. The odd half of each palette
remains blocked on the next set. -/
theorem blocked_degree_tower {I : Type} (R : I → I → Prop) (loop : ∀ x, ¬ R x x)
    (old : I → I → ℕ)
    (blocked : ∀ d : I → ℕ, ∃ a b, R a b ∧ d a = d b ∧ old a b = 2*d a) :
    let p : ℕ → ℕ → ℕ := Nat.rec (fun n => 2*n) (fun _ prev n => prev (2*n+1))
    ∃ S : ℕ → Set I, S 0 = Set.univ ∧ ∀ k,
      S (k+1) ⊆ S k ∧ (S k).Nonempty ∧
      (∀ x ∈ S (k+1), ∃ m : ℕ, ∀ n > m, ¬ Set.Countable
        {y | y ∈ S k ∧ ((R x y ∧ old x y = p k (2*n)) ∨ (R y x ∧ old y x = p k (2*n)))}) ∧
      ∀ d : I → ℕ, ∃ a b, a ∈ S k ∧ b ∈ S k ∧ R a b ∧ d a = d b ∧ old a b = p k (d a) := by
  classical
  intro p
  have inj (k : ℕ) : Function.Injective (p k) := by
    induction k with
    | zero => intro a b h; change 2*a = 2*b at h; omega
    | succ k ih => intro a b h; have e : 2*a+1 = 2*b+1 := ih h; omega
  let B (k : ℕ) (S : Set I) := ∀ d : I → ℕ, ∃ a b,
    a ∈ S ∧ b ∈ S ∧ R a b ∧ d a = d b ∧ old a b = p k (d a)
  have start : B 0 Set.univ := by
    intro d
    obtain ⟨a,b,ab,same,hit⟩ := blocked d
    exact ⟨a,b,trivial,trivial,ab,same,hit⟩
  let step (k : ℕ) (s : {S // B k S}) := blocked_subset_step R loop old (p k) (inj k) s.val s.prop
  let seq : (k : ℕ) → {S // B k S} := Nat.rec ⟨Set.univ,start⟩
    (fun k s => ⟨(step k s).choose,(step k s).choose_spec.2.2⟩)
  refine ⟨fun k => (seq k).val,rfl,?_⟩
  intro k
  obtain ⟨a,_,ha,_⟩ := (seq k).prop (fun _ => 0)
  exact ⟨(step k (seq k)).choose_spec.1,⟨a,ha⟩,(step k (seq k)).choose_spec.2.1,(seq k).prop⟩

/-- Reserve the odd assignment indices at the outset. Round k tests the
indices 2*pair k n. The intersection of the successive high-degree sets
still blocks every assignment from the reserved palette. Neighbour counts
in round k are taken inside S k. -/
theorem blocked_degree_intersection {I : Type} (R : I → I → Prop) (loop : ∀ x, ¬ R x x)
    (old : I → I → ℕ)
    (blocked : ∀ d : I → ℕ, ∃ a b, R a b ∧ d a = d b ∧ old a b = 2*d a) :
    let near := fun (S : Set I) x k n => {y | y ∈ S ∧
      ((R x y ∧ old x y = 4*Nat.pair k n) ∨ (R y x ∧ old y x = 4*Nat.pair k n))}
    ∃ S : ℕ → Set I, S 0 = Set.univ ∧
      (∀ k, S (k+1) = {x | x ∈ S k ∧ ∃ m : ℕ, ∀ n > m, ¬ (near (S k) x k n).Countable}) ∧
      ∀ h : I → ℕ, ∃ a b, (∀ k, a ∈ S k) ∧ (∀ k, b ∈ S k) ∧ R a b ∧
        h a = h b ∧ old a b = 4*h a+2 := by
  classical
  intro near
  let S : ℕ → Set I := Nat.rec Set.univ (fun k s =>
    {x | x ∈ s ∧ ∃ m : ℕ, ∀ n > m, ¬ (near s x k n).Countable})
  refine ⟨S,rfl,fun _ => rfl,?_⟩
  let core (x : I) : Prop := ∀ k : ℕ, x ∈ S k
  have leaves (x : I) (hx : ¬core x) : ∃ k, x ∈ S k ∧ x ∉ S (k+1) := by
    by_contra! stays
    apply hx
    intro k
    induction k with
    | zero => exact Set.mem_univ _
    | succ k ih => exact stays k ih
  let inst (x : I) : Decidable (core x) := Classical.propDecidable _
  let rank (x : I) : ℕ := if hx : core x then 0 else (leaves x hx).choose
  have exitAt x (hx : ¬ core x) : x ∈ S (rank x) ∧ x ∉ S (rank x+1) := by
    simpa only [rank,dif_neg hx] using (leaves x hx).choose_spec
  let N (x : I) (n : ℕ) := near (S (rank x)) x (rank x) n
  let L (x : I) (n : ℕ) := (N x n).Countable
  have lists x m : ∃ n, m < n ∧ (core x ∨ L x n) := by
    by_cases hx : core x
    · exact ⟨m+1,by omega,Or.inl hx⟩
    · obtain ⟨mem,gone⟩ := exitAt x hx
      by_contra! bounded
      exact gone ⟨mem,m,fun n lt => (bounded n lt).2⟩
  let F (x y : I) := ¬core x ∧ ¬core y ∧ rank x = rank y ∧
    ∃ n, L x n ∧ L y n ∧ y ∈ N x n ∧ x ∈ N y n
  have sym x y (e : F x y) : F y x := by
    obtain ⟨hx,hy,r,n,lx,ly,xy,yx⟩ := e
    exact ⟨hy,hx,r.symm,n,ly,lx,yx,xy⟩
  have irr x (e : F x x) : False := by
    obtain ⟨_,_,_,n,_,_,⟨_,hit | hit⟩,_⟩ := e <;> exact loop x hit.1
  have small x : Set.Countable {y | F x y} := by
    let B (n : ℕ) : Set I := if L x n then N x n else ∅
    have hb n : (B n).Countable := by
      by_cases l : L x n
      · simpa [B,l] using (show (N x n).Countable from l)
      · simp [B,l]
    apply (Set.countable_iUnion hb).mono
    rintro y ⟨_,_,_,n,l,_,xy,_⟩
    exact Set.mem_iUnion.mpr ⟨n,by simpa [B,l] using xy⟩
  obtain ⟨g,allowed,proper⟩ := component_list_colouring F sym irr small _ lists
  intro h
  let d (x : I) := if core x then 2*h x+1 else 2*Nat.pair (rank x) (g x)
  obtain ⟨a,b,edge,same,hit⟩ := blocked d
  by_cases ha : core a <;> by_cases hb : core b <;> simp only [d,ha,hb,if_true,if_false] at same hit
  · exact ⟨a,b,ha,hb,edge,by omega,by omega⟩
  · omega
  · omega
  · obtain ⟨r,c⟩ := Nat.pair_eq_pair.mp (show Nat.pair (rank a) (g a) = Nat.pair (rank b) (g b) by omega)
    have col : old a b = 4*Nat.pair (rank a) (g a) := by omega
    have ab : b ∈ N a (g a) := ⟨r ▸ (exitAt b hb).1,Or.inl ⟨edge,col⟩⟩
    have ba : a ∈ N b (g a) := ⟨r ▸ (exitAt a ha).1,Or.inr ⟨edge,r ▸ col⟩⟩
    exact (proper a b ⟨ha,hb,r,g a,(allowed a).resolve_left ha,
      c ▸ (allowed b).resolve_left hb,ab,ba⟩ c).elim

/-- A blocked assignment on C forces an edge matching any bounded assignment outside any countable
family of closed neighbourhoods in a triangle-free ambient graph. -/
private theorem blocked_bounded_escape {I J : Type} [Countable J] (G : SimpleGraph I)
    (free : G.CliqueFree 3) (C : Set I) (old : I → I → ℕ) (p : ℕ → ℕ)
    (bad : ∀ d : I → ℕ, ∃ a b, a ∈ C ∧ b ∈ C ∧ G.Adj a b ∧ d a = d b ∧ old a b = p (d a))
    (centre : J → I) (f : I → ℕ) (m : ℕ) (cap : ∀ x, f x ≤ m) :
    ∃ a b, a ∈ C ∧ b ∈ C ∧ G.Adj a b ∧ f a = f b ∧ old a b = p (f a) ∧
      (∀ j, a ≠ centre j ∧ ¬G.Adj (centre j) a) ∧
      (∀ j, b ≠ centre j ∧ ¬G.Adj (centre j) b) := by
  classical
  let := Encodable.ofCountable J
  let close (x : I) := ∃ j, x = centre j ∨ G.Adj (centre j) x
  let tag (x : I) (h : close x) : J × Bool := (h.choose,decide (x = centre h.choose))
  let d (x : I) := if h : close x then m+1+Encodable.encode (tag x h) else f x
  obtain ⟨a,b,ha,hb,ab,same,hit⟩ := bad d
  have away x (hx : ¬close x) (j : J) : x ≠ centre j ∧ ¬G.Adj (centre j) x :=
    ⟨fun eq => hx ⟨j,Or.inl eq⟩,fun e => hx ⟨j,Or.inr e⟩⟩
  have inside x (hx : close x) : d x = m+1+Encodable.encode (tag x hx) := dif_pos hx
  have outside x (hx : ¬close x) : d x = f x := dif_neg hx
  by_cases ca : close a <;> by_cases cb : close b
  · rw [inside a ca,inside b cb] at same
    have code : Encodable.encode (tag a ca) = Encodable.encode (tag b cb) := by omega
    have eq := Encodable.encode_injective code
    have j : ca.choose = cb.choose := congrArg Prod.fst eq
    have flag : decide (a = centre ca.choose) = decide (b = centre cb.choose) := congrArg Prod.snd eq
    rw [←j] at flag
    by_cases ac : a = centre ca.choose
    · have bc : b = centre ca.choose := by
        rw [decide_eq_true ac] at flag
        exact of_decide_eq_true flag.symm
      exact (ab.ne (ac.trans bc.symm)).elim
    · have bc : b ≠ centre ca.choose := by
        rw [decide_eq_false ac] at flag
        exact of_decide_eq_false flag.symm
      have e := cb.choose_spec
      rw [←j] at e
      exact (free _ (is3Clique_triple_iff.mpr ⟨ca.choose_spec.resolve_left ac,e.resolve_left bc,ab⟩)).elim
  · rw [inside a ca,outside b cb] at same
    have := cap b
    omega
  · rw [outside a ca,inside b cb] at same
    have := cap a
    omega
  · rw [outside a ca,outside b cb] at same
    rw [outside a ca] at hit
    exact ⟨a,b,ha,hb,ab,same,hit,away a ca,away b cb⟩

/-- Apply inside the surviving intersection of blocked_degree_intersection,
using the triangle-free graph induced on the rim and p n = 4*n+2.
Any prescribed sequence of palette colours along a well-order with countable
initial segments (in particular omega_1) is realized by an induced matching. -/
theorem blocked_induced_matching {I K : Type} [LinearOrder K] [WellFoundedLT K]
    (small : ∀ k : K, (Set.Iio k).Countable) (G : SimpleGraph I) (free : G.CliqueFree 3)
    (C : Set I) (old : I → I → ℕ) (p : ℕ → ℕ)
    (bad : ∀ d : I → ℕ, ∃ a b, a ∈ C ∧ b ∈ C ∧ G.Adj a b ∧ d a = d b ∧ old a b = p (d a))
    (colour : K → ℕ) :
    ∃ e : K → Bool → I, (∀ k, e k false ∈ C ∧ e k true ∈ C ∧ G.Adj (e k false) (e k true) ∧
      old (e k false) (e k true) = p (colour k)) ∧
      ∀ i j, i < j → ∀ s t, e j t ≠ e i s ∧ ¬G.Adj (e i s) (e j t) := by
  classical
  let Past (k : K) := (i : K) → i < k → Bool → I
  have choosePair (k : K) (prev : Past k) : ∃ f : Bool → I,
      (f false ∈ C ∧ f true ∈ C ∧ G.Adj (f false) (f true) ∧ old (f false) (f true) = p (colour k)) ∧
      ∀ i (lt : i < k) s t, f t ≠ prev i lt s ∧ ¬G.Adj (prev i lt s) (f t) := by
    let : Countable (Set.Iio k) := small k
    let centre (z : Set.Iio k × Bool) := prev z.1.val z.1.prop z.2
    obtain ⟨a,b,ha,hb,ab,_,hit,aa,bb⟩ := blocked_bounded_escape G free C old p bad centre
      (fun _ => colour k) (colour k) (fun _ => le_rfl)
    refine ⟨(fun t => if t then b else a),⟨ha,hb,ab,hit⟩,?_⟩
    intro i lt s t
    cases t
    · exact aa (⟨i,lt⟩,s)
    · exact bb (⟨i,lt⟩,s)
  let step (k : K) (prev : Past k) := (choosePair k prev).choose
  let e : K → Bool → I := wellFounded_lt.fix step
  have rule (k : K) : e k = step k (fun i _ => e i) := WellFounded.fix_eq _ _ k
  refine ⟨e,?_,?_⟩
  · intro k
    rw [rule k]
    exact (choosePair k _).choose_spec.1
  · intro i j lt s t
    rw [rule j]
    exact (choosePair j (fun z _ => e z)).choose_spec.2 i lt s t

/-- Each finite palette has a finite obstruction outside any countably many
closed neighbourhoods. Compactness is applied only to this finite palette. -/
private theorem finite_palette_escape {I J : Type} [Countable J] (G : SimpleGraph I)
    (free : G.CliqueFree 3) (C : Set I) (old : I → I → ℕ) (p : ℕ → ℕ)
    (bad : ∀ d : I → ℕ, ∃ a b, a ∈ C ∧ b ∈ C ∧ G.Adj a b ∧ d a = d b ∧ old a b = p (d a))
    (centre : J → I) (r : ℕ) (q : Fin (r+1) ↪ ℕ) :
    ∃ S : Finset I, (∀ x ∈ S, x ∈ C ∧ ∀ j, x ≠ centre j ∧ ¬G.Adj (centre j) x) ∧
      ∀ d : I → Fin (r+1), ∃ a ∈ S, ∃ b ∈ S, G.Adj a b ∧ d a = d b ∧ old a b = p (q (d a)) := by
  classical
  let A (x : I) := x ∈ C ∧ ∀ j, x ≠ centre j ∧ ¬G.Adj (centre j) x
  let cap := Finset.univ.sup q
  have bound (i : Fin (r+1)) : q i ≤ cap := Finset.le_sup (f := q) (Finset.mem_univ i)
  by_contra h
  have avoid (S : Finset I) : ∃ d : I → Fin (r+1), ∀ a ∈ S, A a → ∀ b ∈ S, A b →
      G.Adj a b → d a = d b → old a b ≠ p (q (d a)) := by
    by_contra! impossible
    apply h
    refine ⟨S.filter A,fun _ hx => (Finset.mem_filter.mp hx).2,?_⟩
    intro d
    obtain ⟨a,sa,ha,b,sb,hb,ab,same,hit⟩ := impossible d
    exact ⟨a,Finset.mem_filter.mpr ⟨sa,ha⟩,b,Finset.mem_filter.mpr ⟨sb,hb⟩,ab,same,hit⟩
  choose rule ok using avoid
  let u := Ultrafilter.of (Filter.atTop : Filter (Finset I))
  have stable (x : I) := bounded_value u (fun S => (rule S x).val) r
    (Filter.Eventually.of_forall fun S => Nat.le_of_lt_succ (rule S x).isLt)
  let d (x : I) : Fin (r+1) := ⟨(stable x).choose,Nat.lt_succ_of_le (stable x).choose_spec.1⟩
  have agree x : ∀ᶠ S in u, rule S x = d x := (stable x).choose_spec.2.mono fun _ e => Fin.ext e
  have fine (x : I) : ∀ᶠ (S : Finset I) in u, x ∈ S := Ultrafilter.of_le _ (Filter.eventually_finset_mem_atTop x)
  obtain ⟨a,b,ha,hb,ab,eq,hit,aa,bb⟩ := blocked_bounded_escape G free C old p bad centre
    (fun x => q (d x)) cap (fun x => bound (d x))
  obtain ⟨S,sa,sb,ea,eb⟩ := ((fine a).and ((fine b).and ((agree a).and (agree b)))).exists
  exact ok S a sa ⟨ha,aa⟩ b sb ⟨hb,bb⟩ ab (ea.trans ((q.injective eq).trans eb.symm)) (ea ▸ hit)

/-- In a triangle-free blocked set, prescribe a nonempty finite palette at
each stage below omega_1. There are mutually anticomplete finite sets such
that every vertex assignment from the stage palette incurs a matching
old-colour conflict on an edge inside that stage's set. -/
theorem blocked_finite_palette_packing {I K : Type} [LinearOrder K] [WellFoundedLT K]
    (small : ∀ k : K, (Set.Iio k).Countable) (G : SimpleGraph I) (free : G.CliqueFree 3)
    (C : Set I) (old : I → I → ℕ) (p : ℕ → ℕ)
    (bad : ∀ d : I → ℕ, ∃ a b, a ∈ C ∧ b ∈ C ∧ G.Adj a b ∧ d a = d b ∧ old a b = p (d a))
    (r : K → ℕ) (q : ∀ k, Fin (r k+1) ↪ ℕ) :
    ∃ S : K → Finset I, (∀ k, (∀ x ∈ S k, x ∈ C) ∧ ∀ d : I → Fin (r k+1),
      ∃ a ∈ S k, ∃ b ∈ S k, G.Adj a b ∧ d a = d b ∧ old a b = p (q k (d a))) ∧
      ∀ i j, i < j → ∀ x ∈ S i, ∀ y ∈ S j, y ≠ x ∧ ¬G.Adj x y := by
  classical
  let Past (k : K) := (i : K) → i < k → Finset I
  have stage (k : K) (prev : Past k) : ∃ T : Finset I,
      ((∀ x ∈ T, x ∈ C) ∧ ∀ d : I → Fin (r k+1), ∃ a ∈ T, ∃ b ∈ T,
        G.Adj a b ∧ d a = d b ∧ old a b = p (q k (d a))) ∧
      ∀ i (lt : i < k), ∀ x ∈ prev i lt, ∀ y ∈ T, y ≠ x ∧ ¬G.Adj x y := by
    let : Countable (Set.Iio k) := small k
    let J := (i : Set.Iio k) × ↥(prev i.val i.prop)
    let centre (z : J) : I := z.2.val
    obtain ⟨T,away,forces⟩ := finite_palette_escape G free C old p bad centre (r k) (q k)
    refine ⟨T,⟨fun x hx => (away x hx).1,forces⟩,?_⟩
    intro i lt x hx y hy
    exact (away y hy).2 ⟨⟨i,lt⟩,⟨x,hx⟩⟩
  let step (k : K) (prev : Past k) := (stage k prev).choose
  let S : K → Finset I := wellFounded_lt.fix step
  have rule (k : K) : S k = step k (fun i _ => S i) := WellFounded.fix_eq _ _ k
  refine ⟨S,?_,?_⟩
  · intro k
    rw [rule k]
    exact (stage k _).choose_spec.1
  · intro i j lt
    rw [rule j]
    exact (stage j (fun z _ => S z)).choose_spec.2 i lt

/-- Diagonalize against a single row of proposed spoke colours. At coordinate
n choose true exactly when a word of colour n extends the current prefix
with false. Applying this rule at the colour of the constructed word
exhibits two words with that colour and first difference there. -/
private theorem binary_row_collision (g : (ℕ → Bool) → ℕ) :
    ∃ u v : ℕ → Bool, g u = g v ∧ u (g u) ≠ v (g u) ∧ ∀ i < g u, u i = v i := by
  classical
  let step (n : ℕ) (prev : (i : ℕ) → i < n → Bool) : Bool :=
    decide (∃ u, g u = n ∧ u n = false ∧ ∀ i (h : i < n), u i = prev i h)
  let v : ℕ → Bool := wellFounded_lt.fix step
  have rule (n : ℕ) : v n = step n (fun i _ => v i) := WellFounded.fix_eq _ _ n
  let n := g v
  let P := ∃ u, g u = n ∧ u n = false ∧ ∀ i < n, u i = v i
  have e : v n = decide P := rule n
  by_cases hit : P
  · have vt : v n = true := e.trans (decide_eq_true hit)
    obtain ⟨u,hu,bit,earlier⟩ := hit
    exact ⟨u,v,hu,hu ▸ (by rw [bit,vt]; decide : u n ≠ v n),hu ▸ earlier⟩
  · have vf : v n = false := e.trans (decide_eq_false hit)
    exact (hit ⟨v,rfl,vf,fun _ _ => rfl⟩).elim

/-- A triangle-free graph can be precoloured with natural-number edge colours
so that no assignment of natural-number colours to the spokes of a new
universal apex avoids a monochromatic triangle. This prescribes the rim
colouring before the spoke assignment is given. -/
theorem precoloured_blocked_rim :
    ∃ (V : Type) (G : SimpleGraph V) (old : V → V → ℕ), G.CliqueFree 3 ∧
      (∀ x y, old x y = old y x) ∧
      ∀ d : V → ℕ, ∃ a b, G.Adj a b ∧ d a = d b ∧ old a b = d a := by
  classical
  let W := ℕ → Bool
  let Row := W → ℕ
  suffices build : ∀ (X : Type) [LinearOrder X], (∀ f : X → Set Row, ¬Function.Injective f) →
      ∃ (V : Type) (G : SimpleGraph V) (old : V → V → ℕ), G.CliqueFree 3 ∧
        (∀ x y, old x y = old y x) ∧
        ∀ d : V → ℕ, ∃ a b, G.Adj a b ∧ d a = d b ∧ old a b = d a by
    exact @build (Set (Set Row)) (linearOrderOfSTO WellOrderingRel) Function.cantor_injective
  intro X _ large
  let V := (X × X) × W
  let link (x y : V) := x.1.1 < x.1.2 ∧ x.1.2 = y.1.1 ∧ y.1.1 < y.1.2
  let G : SimpleGraph V := {
    Adj := fun x y => link x y ∨ link y x
    symm := ⟨fun _ _ => Or.symm⟩
    loopless := ⟨fun x e => by
      rcases e with h | h <;> exact (ne_of_lt h.1) h.2.1.symm⟩ }
  have free : G.CliqueFree 3 := by
    intro s hs
    obtain ⟨x,y,z,xy,xz,yz,_⟩ := is3Clique_iff.mp hs
    change link x y ∨ link y x at xy
    change link x z ∨ link z x at xz
    change link y z ∨ link z y at yz
    rcases xy with ⟨h₀,e₁,h₁⟩ | ⟨h₀,e₁,h₁⟩ <;>
      rcases xz with ⟨h₄,e₂,h₂⟩ | ⟨h₄,e₂,h₂⟩ <;>
      rcases yz with ⟨h₅,e₃,h₃⟩ | ⟨h₅,e₃,h₃⟩ <;> grind
  let first (P : ℕ → Prop) := if h : ∃ i, P i then Nat.find h else 0
  let diff (u v : W) := first (fun i => u i ≠ v i)
  have sym (u v : W) : diff u v = diff v u := by
    exact congrArg first (funext fun i => propext (ne_comm (a := u i) (b := v i)))
  refine ⟨V,G,(fun x y => diff x.2 y.2),free,fun x y => sym x.2 y.2,?_⟩
  intro d
  let row (x y : X) (u : W) := d ((x,y),u)
  let out (x : X) : Set Row := {r | ∃ y, x < y ∧ row x y = r}
  have repeatRow : ∃ x y z : X, x < y ∧ y < z ∧ row x y = row y z := by
    by_contra avoid
    apply large out
    intro x y eq
    have clash (a b : X) (lt : a < b) (same : out a = out b) : False := by
      have mem : row a b ∈ out a := ⟨b,lt,rfl⟩
      rw [same] at mem
      obtain ⟨c,bc,matchRow⟩ := mem
      exact avoid ⟨a,b,c,lt,bc,matchRow.symm⟩
    rcases lt_trichotomy x y with lt | e | gt
    · exact (clash _ _ lt eq).elim
    · exact e
    · exact (clash _ _ gt eq.symm).elim
  obtain ⟨x,y,z,xy,yz,same⟩ := repeatRow
  obtain ⟨u,v,colour,bit,earlier⟩ := binary_row_collision (row x y)
  have first_at (P : ℕ → Prop) (n : ℕ) (hn : P n) (min : ∀ i < n, ¬P i) : first P = n := by
    have ex : ∃ i, P i := ⟨n,hn⟩
    simp only [first,dif_pos ex]
    exact le_antisymm (Nat.find_min' ex hn) (by by_contra! lt; exact min _ lt (Nat.find_spec ex))
  exact ⟨((x,y),u),((y,z),v),Or.inl ⟨xy,rfl,yz⟩,colour.trans (congrFun same v),
    first_at _ _ bit (fun i lt ne => ne (earlier i lt))⟩

/-- In every ordering of a fixed Ramsey witness by a well-order, some earlier
neighbourhood splits into continuum many uncountably chromatic pieces. The
pieces are automatically triangle-free if the witness is four-clique-free. -/
theorem packed_rim_of_witness {I : Type} [LinearOrder I] [WellFoundedLT I]
    (G : SimpleGraph I) (bad : ¬ Erdos595.IsCountableUnionOfTriangleFree G) :
    ∃ (j : I) (lab : I → ℕ → Bool), ∀ (k : ℕ → Bool) (d : I → ℕ),
      ∃ a b, a < j ∧ b < j ∧ G.Adj a j ∧ G.Adj b j ∧ G.Adj a b ∧
        lab a = k ∧ lab b = k ∧ d a = d b := by
  classical
  obtain ⟨paint,works⟩ := greedy_rim_painter (I := I)
  obtain ⟨a,b,j,ab,bj,gab,gaj,gbj,mono⟩ := fixed_play G bad paint
  refine ⟨j,?_⟩
  by_contra! each
  exact works G j each a b ab bj gab gaj gbj mono.1 mono.2

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

/-- The chronological formulation is equivalent to the original witness
problem in the base universe. The two implications may use different hosts. -/
theorem online_iff_witness : H1 ↔
    ∃ (V : Type) (_ : Infinite V) (G : SimpleGraph V),
      G.CliqueFree 4 ∧ ¬ Erdos595.IsCountableUnionOfTriangleFree G := by
  constructor
  · exact fun h => main h history_amalgamation
  · rintro ⟨V,hV,G,free,bad⟩
    let : Infinite V := hV
    exact from_fixed_witness G free bad

end OMA.R_Erdos595_erdos_595_R3
