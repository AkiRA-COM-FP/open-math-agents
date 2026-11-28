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
