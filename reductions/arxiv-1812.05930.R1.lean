import OMAStatements.S_arxiv_1812_05930

-- Credit: @ryansolves
namespace OMA.R_arxiv_1812_05930_R1
open OMA.S_arxiv_1812_05930

/-- A purely integer density bound for graphs with constant incidence-block size.
For regular graphs of degree d it reads 4m ≤ 5d² times the matching size. -/
def H1 : Prop :=
  ∀ (n k : ℕ) (G : SimpleGraph (Fin n)), (edges G).Nonempty →
    (∀ e ∈ edges G, (incidentBlock G e).card = k) →
    ∃ M, inducedMatching G M ∧
      8*(edges G).card ≤ 5*degreeBound G*(k+1)*M.card

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

private theorem constant_width_gap (density : H1) {n k} {G : SimpleGraph (Fin n)}
    (nonempty : (edges G).Nonempty) (width : ∀ e ∈ edges G, (incidentBlock G e).card = k)
    (x) (hx : feasible G x) : ∃ M, inducedMatching G M ∧
    (∑ e ∈ edges G, x e) ≤ ((5/8 : ℝ)*degreeBound G + 5/8)*M.card := by
  obtain ⟨M,hm,cert⟩ := density n k G nonempty width
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
