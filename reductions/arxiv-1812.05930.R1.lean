import OMAStatements.S_arxiv_1812_05930

-- Credit: @ryansolves
namespace OMA.R_arxiv_1812_05930_R1
open OMA.S_arxiv_1812_05930

/-- Regular-graph density: a positive-degree d-regular graph on n vertices
has an induced matching whose size is at least 2n/(5d). -/
def H1 : Prop :=
  ∀ (n d : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    0 < d → (∀ v, G.degree v = d) → ∃ M, inducedMatching G M ∧ 2*n ≤ 5*d*M.card

/-- The fractional gap only on graphs having two different incidence-block sizes. -/
def H2 : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    (∃ e ∈ edges G, ∃ f ∈ edges G, (incidentBlock G e).card ≠ (incidentBlock G f).card) →
    ∀ x, feasible G x → ∃ M, inducedMatching G M ∧
      (∑ e ∈ edges G, x e) ≤ ((5/8 : ℝ)*degreeBound G+C)*M.card

/-- The uniform polynomial-time integer approximation, independent of fractional weights. -/
def H3 : Prop :=
  ∃ (C : ℝ) (algorithm : List Bool → List Bool), 0 ≤ C ∧
    Nonempty (Turing.TM2ComputableInPolyTime id id algorithm) ∧
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)), ∃ M, inducedMatching G M ∧
      algorithm (graphBits G) = matchingBits M ∧
      ∀ N, inducedMatching G N → (N.card : ℝ) ≤ ((5/8 : ℝ)*degreeBound G+C)*M.card

theorem transpose_sum {α : Type*} [DecidableEq α]
    (E : Finset α) (F : α → Finset α) (k : ℕ)
    (sub : ∀ i ∈ E, F i ⊆ E)
    (sym : ∀ i ∈ E, ∀ j ∈ E, j ∈ F i ↔ i ∈ F j)
    (card : ∀ i ∈ E, (F i).card = k) (x : α → ℝ) :
    (∑ i ∈ E, ∑ j ∈ F i, x j) = (k : ℝ) * ∑ j ∈ E, x j := by
  classical
  have filt (i) (hi : i ∈ E) : E.filter (· ∈ F i) = F i := by
    ext j
    exact Finset.mem_filter.trans ⟨And.right, fun hj => ⟨sub i hi hj,hj⟩⟩
  calc
    _ = ∑ i ∈ E, ∑ j ∈ E, if j ∈ F i then x j else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_filter, filt i hi]
    _ = ∑ j ∈ E, ∑ i ∈ E, if j ∈ F i then x j else 0 := Finset.sum_comm
    _ = ∑ j ∈ E, (k : ℝ) * x j := by
      apply Finset.sum_congr rfl
      intro j hj
      calc
        _ = ∑ i ∈ E, if i ∈ F j then x j else 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          simp only [sym i hi j hj]
        _ = _ := by rw [← Finset.sum_filter, filt j hj]; simp [card j hj]
    _ = _ := (Finset.mul_sum ..).symm

private theorem degree_le_width {n k} (G : SimpleGraph (Fin n))
    (width : ∀ e ∈ edges G, (incidentBlock G e).card = k) : degreeBound G ≤ k := by
  classical
  unfold degreeBound
  apply G.maxDegree_le_of_forall_degree_le
  intro v
  by_cases pos : 0 < G.degree v
  · obtain ⟨w,adj⟩ := (G.degree_pos_iff_exists_adj v).mp pos
    have edge : s(v,w) ∈ edges G := by simpa [edges] using adj
    have sub : G.incidenceFinset v ⊆ incidentBlock G s(v,w) := by
      intro f hf
      rw [G.incidenceFinset_eq_filter] at hf
      obtain ⟨ef,vf⟩ := Finset.mem_filter.mp hf
      apply Finset.mem_filter.mpr
      refine ⟨by simpa [edges] using ef,Finset.nonempty_iff_ne_empty.mp ⟨v,?_⟩⟩
      exact Finset.mem_inter.mpr ⟨Sym2.mem_toFinset.mpr (Sym2.mem_mk_left ..),Sym2.mem_toFinset.mpr vf⟩
    simpa only [G.card_incidenceFinset_eq_degree,width _ edge] using Finset.card_le_card sub
  · omega

private theorem width_positive {n k} {G : SimpleGraph (Fin n)}
    (nonempty : (edges G).Nonempty) (width : ∀ e ∈ edges G, (incidentBlock G e).card = k) : 0 < k := by
  obtain ⟨e,he⟩ := nonempty
  rw [← width e he, Finset.card_pos]
  exact ⟨e, Finset.mem_filter.mpr ⟨he, by simp⟩⟩

private theorem width_bound {n k} {G : SimpleGraph (Fin n)}
    (width : ∀ e ∈ edges G, (incidentBlock G e).card = k) (x) (hx : feasible G x) :
    (k : ℝ)*(∑ e ∈ edges G, x e) ≤ (edges G).card := by
  classical
  have sub : ∀ i ∈ edges G, incidentBlock G i ⊆ edges G := fun _ _ => Finset.filter_subset ..
  have sym : ∀ i ∈ edges G, ∀ j ∈ edges G, j ∈ incidentBlock G i ↔ i ∈ incidentBlock G j := by
    intro i hi j hj
    simp [incidentBlock, hi, hj, Finset.inter_comm]
  have eqn := transpose_sum (edges G) (incidentBlock G) k sub sym width x
  have bound := Finset.sum_le_sum (fun i (hi : i ∈ edges G) => hx.2 i hi)
  rw [eqn] at bound
  simpa using bound

private theorem in_block {n} {G : SimpleGraph (Fin n)} {e f : Sym2 (Fin n)} :
    f ∈ incidentBlock G e ↔ f ∈ edges G ∧ ∃ u, u ∈ e ∧ u ∈ f := by
  classical
  simp only [incidentBlock, Finset.mem_filter, ← Finset.nonempty_iff_ne_empty,
    Finset.Nonempty, Finset.mem_inter, Sym2.mem_toFinset]

private theorem has_mate {n} {G : SimpleGraph (Fin n)} {f : Sym2 (Fin n)}
    (hf : f ∈ edges G) {x} (hx : x ∈ f) : ∃ y ∈ f, G.Adj x y := by
  obtain ⟨y,rfl⟩ := Sym2.mem_iff_exists.mp hx
  exact ⟨y,Sym2.mem_mk_right .., by simpa [edges] using hf⟩

theorem induced_iff_endpoints {n} {G : SimpleGraph (Fin n)} {M : Finset (Sym2 (Fin n))} :
    inducedMatching G M ↔ M ⊆ edges G ∧
    ∀ e ∈ M, ∀ f ∈ M, ∀ a ∈ e, ∀ b ∈ f, G.Adj a b → e = f := by
  classical
  constructor
  · rintro ⟨sub,one⟩
    refine ⟨sub,?_⟩
    intro e he f hf a ha b hb hab
    apply Finset.card_le_one_iff.mp (one s(a,b) (by simpa [edges] using hab))
    · exact Finset.mem_inter.mpr ⟨in_block.mpr ⟨sub he,a,Sym2.mem_mk_left ..,ha⟩,he⟩
    · exact Finset.mem_inter.mpr ⟨in_block.mpr ⟨sub hf,b,Sym2.mem_mk_right ..,hb⟩,hf⟩
  · rintro ⟨sub,noCross⟩
    refine ⟨sub,?_⟩
    intro c hc
    induction c using Sym2.inductionOn with
    | _ u v =>
      have uv : G.Adj u v := by simpa [edges] using hc
      apply Finset.card_le_one_iff.mpr
      intro e f he hf
      obtain ⟨eb,em⟩ := Finset.mem_inter.mp he
      obtain ⟨fb,fm⟩ := Finset.mem_inter.mp hf
      obtain ⟨_,a,ac,ae⟩ := in_block.mp eb
      obtain ⟨_,b,bc,bf⟩ := in_block.mp fb
      by_cases same : a = b
      · subst b
        obtain ⟨z,zf,az⟩ := has_mate (sub fm) bf
        exact noCross e em f fm a ae z zf az
      · have ab : G.Adj a b := by
          rcases Sym2.mem_iff.mp ac with rfl|rfl <;> rcases Sym2.mem_iff.mp bc with rfl|rfl <;> tauto
        exact noCross e em f fm a ae b bf ab

/-- Mapping vertices through any map that preserves and reflects adjacency
preserves both an induced matching and its cardinality. -/
theorem project_induced_matching {n m} {G : SimpleGraph (Fin n)} {H : SimpleGraph (Fin m)}
    (p : Fin n → Fin m) (cover : ∀ u v, G.Adj u v ↔ H.Adj (p u) (p v))
    (M : Finset (Sym2 (Fin n))) (hm : inducedMatching G M) :
    inducedMatching H (M.image (Sym2.map p)) ∧ (M.image (Sym2.map p)).card = M.card := by
  classical
  obtain ⟨sub,noCross⟩ := induced_iff_endpoints.mp hm
  refine ⟨induced_iff_endpoints.mpr ⟨?_,?_⟩,?_⟩
  · intro f hf
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hf
    have valid := sub he
    induction e using Sym2.inductionOn with
    | _ a b =>
      simpa [edges] using (cover a b).mp (by simpa [edges] using valid)
  · intro e he f hf a ha b hb hab
    obtain ⟨e',em,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨f',fm,rfl⟩ := Finset.mem_image.mp hf
    obtain ⟨x,xe,rfl⟩ := Sym2.mem_map.mp ha
    obtain ⟨y,yf,rfl⟩ := Sym2.mem_map.mp hb
    exact congrArg _ (noCross e' em f' fm x xe y yf ((cover x y).mpr hab))
  · apply Finset.card_image_of_injOn
    intro e he f hf eqn
    induction e using Sym2.inductionOn with
    | _ u v =>
      have uv : G.Adj u v := by simpa [edges] using sub he
      have pv : p v ∈ Sym2.map p f := eqn ▸ (Sym2.mem_map.mpr ⟨v,Sym2.mem_mk_right ..,rfl⟩)
      obtain ⟨w,wf,hw⟩ := Sym2.mem_map.mp pv
      apply noCross _ he f hf u (Sym2.mem_mk_left ..) w wf
      exact (cover u w).mpr (hw ▸ (cover u v).mp uv)

/-- If every surviving clone sees total neighboring multiplicity R, the
regular-graph density estimate transfers to the original graph. Zero fibers
are allowed, including isolated vertices. -/
theorem weighted_regular_transfer
    (density : H1)
    {n R : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (w : Fin n → ℕ)
    (pos : 0 < R) (rows : ∀ v, 0 < w v → ∑ u : G.neighborSet v, w u.val = R) :
    ∃ M, inducedMatching G M ∧ 2*(∑ v, w v) ≤ 5*R*M.card := by
  classical
  let V := Σ v : Fin n, Fin (w v)
  let N := Fintype.card V
  let code : V ≃ Fin N := Fintype.equivFin V
  let p (v : Fin N) : Fin n := (code.symm v).1
  let H := G.comap p
  have reg (v : Fin N) : H.degree v = R := by
    let iso : H.neighborSet v ≃ (Σ u : G.neighborSet (p v), Fin (w u.val)) := {
      toFun := fun z => ⟨⟨p z.val,z.property⟩,(code.symm z.val).2⟩
      invFun := fun z => ⟨code ⟨z.1.val,z.2⟩, by
        change G.Adj (p v) ((code.symm (code ⟨z.1.val,z.2⟩)).1)
        rw [code.symm_apply_apply]
        exact z.1.property⟩
      left_inv := fun z => Subtype.ext (code.apply_symm_apply z.val)
      right_inv := by
        rintro ⟨⟨z,hz⟩,i⟩
        simp [p]
        exact (Sigma.ext_iff.mp (code.symm_apply_apply (⟨z,i⟩ : V))).2
    }
    have eq := Fintype.card_congr iso
    simp only [Fintype.card_sigma,Fintype.card_fin,SimpleGraph.card_neighborSet_eq_degree] at eq
    exact eq.trans (rows _ (Nat.zero_lt_of_lt (code.symm v).2.isLt))
  obtain ⟨M,hm,cert⟩ := density N R H pos reg
  obtain ⟨inside,size⟩ := project_induced_matching p (fun _ _ => Iff.rfl) M hm
  refine ⟨_,inside,?_⟩
  rw [size]
  have order : N = ∑ v, w v := by simp [N,V,Fintype.card_sigma]
  simpa only [order] using cert

theorem incident_card_succ {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {a b} (adj : G.Adj a b) :
    (incidentBlock G s(a,b)).card + 1 = G.degree a + G.degree b := by
  classical
  have row : incidentBlock G s(a,b) = G.incidenceFinset a ∪ G.incidenceFinset b := by
    ext f
    simp only [incidentBlock, edges, Finset.mem_filter, ← Finset.nonempty_iff_ne_empty,
      Finset.Nonempty, Finset.mem_inter, Sym2.mem_toFinset, Sym2.mem_iff, Finset.mem_union,
      G.incidenceFinset_eq_filter, SimpleGraph.mem_edgeFinset]
    grind
  have common : G.incidenceFinset a ∩ G.incidenceFinset b = {s(a,b)} := by
    ext f
    simp only [G.incidenceFinset_eq_filter, Finset.mem_inter, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · intro h
      exact (Sym2.mem_and_mem_iff adj.ne).mp ⟨h.1.2,h.2.2⟩
    · rintro rfl
      have edge : s(a,b) ∈ G.edgeFinset := by simpa using adj
      exact ⟨⟨edge,Sym2.mem_mk_left ..⟩,⟨edge,Sym2.mem_mk_right ..⟩⟩
  have tot := Finset.card_union_add_card_inter (G.incidenceFinset a) (G.incidenceFinset b)
  simpa only [row,common,Finset.card_singleton,G.card_incidenceFinset_eq_degree] using tot

/-- Constant edge incidence width reduces to ordinary regular graphs, even
with isolated vertices and components of distinct degree pairs. -/
theorem width_of_regular
    (density : H1)
    {n k : ℕ} (G : SimpleGraph (Fin n))
    (width : ∀ e ∈ edges G, (incidentBlock G e).card = k) :
    ∃ M, inducedMatching G M ∧ 8*(edges G).card ≤ 5*degreeBound G*(k+1)*M.card := by
  classical
  let R := n.factorial
  let w (v : Fin n) := if G.degree v = 0 then 0 else R / (k+1-G.degree v)
  have adjSum {u v : Fin n} (h : G.Adj u v) : G.degree u + G.degree v = k+1 := by
    rw [← incident_card_succ G h,width _ (by simpa [edges] using h)]
  have divisor (v : Fin n) (h : 0 < G.degree v) : G.degree v ∣ R :=
    Nat.dvd_factorial h (by simpa using (G.degree_lt_card_verts v).le)
  have weight {u v : Fin n} (adj : G.Adj u v) : w u = R / G.degree v := by
    have hu := (G.degree_pos_iff_exists_adj u).mpr ⟨v,adj⟩
    have eq := adjSum adj
    simp [w,hu.ne',show k+1-G.degree u = G.degree v by omega]
  have rows (v) (hv : 0 < w v) : ∑ u : G.neighborSet v, w u.val = R := by
    have pos : 0 < G.degree v := by by_contra! hz; simp [w, Nat.eq_zero_of_le_zero hz] at hv
    have fixed (u : G.neighborSet v) : w u.val = R / G.degree v := weight u.property.symm
    simp only [fixed,Finset.sum_const,Finset.card_univ,SimpleGraph.card_neighborSet_eq_degree,nsmul_eq_mul]
    exact Nat.mul_div_cancel' (divisor v pos)
  obtain ⟨M,hm,limit⟩ := weighted_regular_transfer density G w (Nat.factorial_pos n) rows
  have vertex (v : Fin n) : 2*R*G.degree v ≤ (degreeBound G*(k+1))*w v := by
    by_cases zero : G.degree v = 0
    · simp [zero]
    obtain ⟨u,adj⟩ := (G.degree_pos_iff_exists_adj v).mp (Nat.pos_of_ne_zero zero)
    have prod : G.degree u * w v = R := by
      rw [weight adj]
      exact Nat.mul_div_cancel' (divisor u ((G.degree_pos_iff_exists_adj u).mpr ⟨v,adj.symm⟩))
    have du : G.degree u ≤ degreeBound G := by simpa [degreeBound] using G.degree_le_maxDegree u
    have dv : G.degree v ≤ degreeBound G := by simpa [degreeBound] using G.degree_le_maxDegree v
    have ab : 2*G.degree v*G.degree u ≤ degreeBound G*(k+1) := by
      rw [← adjSum adj]
      nlinarith only [Nat.mul_le_mul_right (G.degree v) du,Nat.mul_le_mul_right (G.degree u) dv]
    calc 2*R*G.degree v = (2*G.degree v*G.degree u)*w v := by rw [← prod]; ring
         _ ≤ _ := Nat.mul_le_mul_right _ ab
  have total := Finset.sum_le_sum (s := Finset.univ) (fun v _ => vertex v)
  rw [← Finset.mul_sum, ← Finset.mul_sum] at total
  have hand := G.sum_degrees_eq_twice_card_edges
  have ed : edges G = G.edgeFinset := by ext; simp [edges]
  rw [← ed] at hand
  rw [hand] at total
  refine ⟨M,hm,Nat.le_of_mul_le_mul_right ?_ (Nat.factorial_pos n)⟩
  nlinarith only [total,Nat.mul_le_mul_left (degreeBound G*(k+1)) limit]

private theorem constant_width_gap (density : H1) {n k} {G : SimpleGraph (Fin n)}
    (nonempty : (edges G).Nonempty) (width : ∀ e ∈ edges G, (incidentBlock G e).card = k)
    (x) (hx : feasible G x) : ∃ M, inducedMatching G M ∧
    (∑ e ∈ edges G, x e) ≤ ((5/8 : ℝ)*degreeBound G + 5/8)*M.card := by
  obtain ⟨M,hm,cert⟩ := width_of_regular density G width
  refine ⟨M,hm,?_⟩
  have den : (0:ℝ) < k := by exact_mod_cast width_positive nonempty width
  have degree : (degreeBound G : ℝ) ≤ k := by exact_mod_cast degree_le_width G width
  have cert' : 8*((edges G).card:ℝ) ≤ 5*degreeBound G*((k:ℝ)+1)*M.card := by exact_mod_cast cert
  apply le_of_mul_le_mul_left (a := (k:ℝ)) _ den
  nlinarith only [width_bound width x hx,cert',mul_le_mul_of_nonneg_right degree (Nat.cast_nonneg (α := ℝ) M.card)]

theorem main : H1 → H2 → H3 → type_of% @OMA.S_arxiv_1812_05930.main := by
  classical
  rintro density ⟨C,hC,mixed⟩ ⟨D,alg,_,hpoly,algorithm⟩
  let B := max (max C D) (5/8 : ℝ)
  have cB : C ≤ B := (le_max_left C D).trans (le_max_left ..)
  have dB : D ≤ B := (le_max_right C D).trans (le_max_left ..)
  have small : (5/8 : ℝ) ≤ B := le_max_right .. 
  refine ⟨B,alg,hC.trans cB,hpoly,?_⟩
  intro n G
  dsimp only
  have grow (z : ℝ) (hz : z ≤ B) (k : ℕ) :
      ((5/8 : ℝ)*degreeBound G+z)*k ≤ ((5/8 : ℝ)*degreeBound G+B)*k :=
    mul_le_mul_of_nonneg_right (add_le_add_right hz _) (Nat.cast_nonneg _)
  constructor
  · intro x hx
    by_cases nonempty : (edges G).Nonempty
    · obtain ⟨e,he⟩ := nonempty
      by_cases width : ∀ f ∈ edges G, (incidentBlock G f).card = (incidentBlock G e).card
      · obtain ⟨M,hm,bound⟩ := constant_width_gap density ⟨e,he⟩ width x hx
        exact ⟨M,hm,bound.trans (grow _ small _)⟩
      · push Not at width
        obtain ⟨f,hf,diff⟩ := width
        obtain ⟨M,hm,bound⟩ := mixed n G ⟨f,hf,e,he,diff⟩ x hx
        exact ⟨M,hm,bound.trans (grow _ cB _)⟩
    · have empty := Finset.not_nonempty_iff_eq_empty.mp nonempty
      exact ⟨∅,by simp [inducedMatching,empty],by simp [empty]⟩
  · obtain ⟨M,hm,out,opt⟩ := algorithm n G
    exact ⟨M,hm,out,fun N hn => (opt N hn).trans (grow _ dB _)⟩

end OMA.R_arxiv_1812_05930_R1
