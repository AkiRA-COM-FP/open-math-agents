import FormalConjectures.Wikipedia.Conway99Graph
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Tactic

-- Reduction Conway99Graph.conway99Graph.R1 of Conway's 99-graph problem
-- Credit: @Cryptokraken974

namespace OMA.R_Conway99Graph_conway99Graph_R1

open SimpleGraph
open scoped BigOperators

lemma c50_local {V : Type*} (G : SimpleGraph V)
    (h : ∀ x y, G.Adj x y → (G.neighborSet x ∩ G.neighborSet y).ncard = 1) :
    G.LocallyLinear := by
  classical
  constructor
  · intro s hs t ht hst
    change G.IsNClique 3 s at hs
    change G.IsNClique 3 t at ht
    intro x hx y hy
    by_contra hxy
    have hAdj : G.Adj x y := hs.1 hx.1 hy.1 hxy
    obtain ⟨w, hw⟩ := Set.ncard_eq_one.mp (h x y hAdj)
    have hdet (r : Finset V) (hr : G.IsNClique 3 r) (hx' : x ∈ r) (hy' : y ∈ r) :
        r = {x,y,w} := by
      apply Finset.eq_of_subset_of_card_le
      · intro z hz
        by_cases hxz : x = z
        · simp [← hxz]
        by_cases hyz : y = z
        · simp [← hyz]
        have hwz : z ∈ G.neighborSet x ∩ G.neighborSet y :=
          ⟨hr.1 hx' hz hxz, hr.1 hy' hz hyz⟩
        rw [hw] at hwz
        simp [Set.mem_singleton_iff.mp hwz]
      · rw [hr.2]
        exact (Finset.card_insert_le _ _).trans (by
          have hcard := Finset.card_insert_le y ({w} : Finset V)
          simpa using Nat.succ_le_succ hcard)
    exact hst ((hdet s hs hx.1 hy.1).trans (hdet t ht hx.2 hy.2).symm)
  · intro x y hadj
    obtain ⟨w, hw⟩ := Set.ncard_eq_one.mp (h x y hadj)
    have hm : w ∈ G.neighborSet x ∩ G.neighborSet y := by simp [hw]
    exact ⟨{x,y,w}, is3Clique_triple_iff.mpr ⟨hadj, hm.1, hm.2⟩, by simp, by simp⟩

lemma c50_counts
    (a : Fin 99 → Fin 99 → ℤ)
    (asymm : ∀ x y, a x y = a y x)
    (a0 : ∀ x, a x x = 0)
    (abin : ∀ x y, a x y * a x y = a x y)
    (total : (∑ x, ∑ y, a x y) = 1386)
    (cap : ∀ x y, x ≠ y → (∑ z, a x z * a y z) + a x y ≤ 2) :
    ∀ x y, x ≠ y → (∑ z, a x z * a y z) + a x y = 2 := by
  classical
  let d (x : Fin 99) := ∑ y, a x y
  let c (x y : Fin 99) := ∑ z, a x z * a y z
  have dc (x : Fin 99) : c x x = d x := by simp [c, d, abin]
  have sumd : ∑ x, d x = 1386 := total
  have col (z : Fin 99) : ∑ x, a x z = d z := by
    unfold d
    exact Finset.sum_congr rfl (fun x _ ↦ asymm x z)
  have cc (x : Fin 99) : ∑ y, c x y = ∑ z, a x z * d z := by
    unfold c
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, col]
  have sq : ∑ x, ∑ y, c x y = ∑ z, d z ^ 2 := by
    simp_rw [cc]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, col, pow_two]
  let slack (x y : Fin 99) := (if x = y then d x - 2 else 0) + 2 - c x y - a x y
  have nonneg (x y : Fin 99) : 0 ≤ slack x y := by
    by_cases h : x = y
    · subst y; simp [slack, dc, a0]
    · have hc := cap x y h
      change c x y + a x y ≤ 2 at hc
      simp only [slack, if_neg h]; omega
  have row (x : Fin 99) : ∑ y, slack x y = 196 - ∑ y, c x y := by
    simp only [slack, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, if_true]
    change d x - 2 + _ - _ - d x = _
    ring
  have tt : ∑ x, ∑ y, slack x y = 19404 - ∑ z, d z ^ 2 := by
    simp_rw [row]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, sq]
    norm_num
  have lin (x : Fin 99) : (d x - 14)^2 = d x^2 - 28 * d x + 196 := by ring
  have ss : ∑ x, (d x - 14)^2 = ∑ x, d x^2 - 19404 := by
    simp_rw [lin]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, sumd,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have pos : 0 ≤ ∑ x, (d x - 14)^2 := Finset.sum_nonneg (fun i _ ↦ sq_nonneg _)
  have zero : ∑ x, ∑ y, slack x y = 0 := by
    have := Finset.sum_nonneg (s := Finset.univ) (fun x _ ↦
      Finset.sum_nonneg (s := Finset.univ) (fun y _ ↦ nonneg x y))
    omega
  intro x y h
  have zr := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦
    Finset.sum_nonneg (fun j _ ↦ nonneg i j))).mp zero x (Finset.mem_univ x)
  have zv := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ nonneg x j)).mp zr y (Finset.mem_univ y)
  change c x y + a x y = 2
  simp only [slack, if_neg h] at zv
  omega

/-- At 693 edges all local common-neighbor bounds are attained. -/
lemma extremal :
  ∀ G : SimpleGraph (Fin 99), G.edgeSet.ncard = 693 →
    (∀ x y, x ≠ y →
      (G.neighborSet x ∩ G.neighborSet y).ncard ≤ 2 ∧
      (G.Adj x y → (G.neighborSet x ∩ G.neighborSet y).ncard ≤ 1)) →
    G.LocallyLinear ∧ ∀ x y, x ≠ y → ¬ G.Adj x y →
      (G.neighborSet x ∩ G.neighborSet y).ncard = 2 := by
  classical
  intro G hsize hcap
  let c50A (G : SimpleGraph (Fin 99)) (x y : Fin 99) : ℤ := if G.Adj x y then 1 else 0
  have c50_sumA (G : SimpleGraph (Fin 99)) (hm : G.edgeSet.ncard = 693) :
      ∑ x, ∑ y, c50A G x y = 1386 := by
    classical
    have row (x : Fin 99) : ∑ y, c50A G x y = (G.degree x : ℤ) := by
      simp only [c50A, Finset.sum_boole]
      congr 2
      ext y
      simp
    simp_rw [row]
    rw [← Nat.cast_sum, G.sum_degrees_eq_twice_card_edges]
    have he : G.edgeFinset.card = 693 := by
      simpa only [← G.coe_edgeFinset, Set.ncard_coe_finset] using hm
    rw [he]
    decide
  have c50_commonA (G : SimpleGraph (Fin 99)) (x y : Fin 99) :
      ∑ z, c50A G x z * c50A G y z =
        ((G.neighborSet x ∩ G.neighborSet y).ncard : ℤ) := by
    classical
    have h (z : Fin 99) : c50A G x z * c50A G y z =
        (if G.Adj x z ∧ G.Adj y z then 1 else 0 : ℤ) := by
      by_cases hx : G.Adj x z <;> by_cases hy : G.Adj y z <;> simp [c50A, hx, hy]
    simp_rw [h]
    rw [Finset.sum_boole]
    have hset : (↑(Finset.univ.filter (fun z => G.Adj x z ∧ G.Adj y z)) : Set (Fin 99)) =
        G.neighborSet x ∩ G.neighborSet y := by ext z; simp
    rw [← hset, Set.ncard_coe_finset]
  have symm (x y : Fin 99) : c50A G x y = c50A G y x := by
    simp only [c50A, G.adj_comm x y]
  have bot (x : Fin 99) : c50A G x x = 0 := by simp [c50A]
  have idem (x y : Fin 99) : c50A G x y * c50A G x y = c50A G x y := by
    by_cases h : G.Adj x y <;> simp [c50A, h]
  have caps (x y : Fin 99) (h : x ≠ y) :
      (∑ z, c50A G x z * c50A G y z) + c50A G x y ≤ 2 := by
    rw [c50_commonA]
    obtain ⟨hn, he⟩ := hcap x y h
    by_cases hadj : G.Adj x y
    · have := he hadj
      simp only [c50A, if_pos hadj]
      omega
    · simp only [c50A, if_neg hadj]
      omega
  have counted := c50_counts (c50A G) symm bot idem (c50_sumA G hsize) caps
  constructor
  · apply c50_local
    intro x y hadj
    have h := counted x y hadj.ne
    rw [c50_commonA] at h
    simp only [c50A, if_pos hadj] at h
    omega
  · intro x y hne hnot
    have h := counted x y hne
    rw [c50_commonA] at h
    simp only [c50A, if_neg hnot] at h
    omega

/-- Find a packing three edges short of the extremal edge count. -/
def H1 : Prop :=
  ∃ G : SimpleGraph (Fin 99), G.edgeSet.ncard = 690 ∧
    ∀ x y, x ≠ y →
      (G.neighborSet x ∩ G.neighborSet y).ncard ≤ 2 ∧
      (G.Adj x y → (G.neighborSet x ∩ G.neighborSet y).ncard ≤ 1)

/-- Between 690 and 692 edges, some missing edge can be inserted while preserving both caps. -/
def H2 : Prop :=
  ∀ G : SimpleGraph (Fin 99), 690 ≤ G.edgeSet.ncard → G.edgeSet.ncard ≤ 692 →
    (∀ x y, x ≠ y →
      (G.neighborSet x ∩ G.neighborSet y).ncard ≤ 2 ∧
      (G.Adj x y → (G.neighborSet x ∩ G.neighborSet y).ncard ≤ 1)) →
    ∃ K : SimpleGraph (Fin 99),
      (∃ u v, u ≠ v ∧ ¬ G.Adj u v ∧ K = G ⊔ SimpleGraph.edge u v) ∧
      K.edgeSet.ncard = G.edgeSet.ncard + 1 ∧
      ∀ x y, x ≠ y →
        (K.neighborSet x ∩ K.neighborSet y).ncard ≤ 2 ∧
        (K.Adj x y → (K.neighborSet x ∩ K.neighborSet y).ncard ≤ 1)

theorem main : H1 → H2 → type_of% @Conway99Graph.conway99Graph := by
  rintro ⟨G, hG, cG⟩ extend
  obtain ⟨J, _, hJ, cJ⟩ := extend G (by omega) (by omega) cG
  obtain ⟨K, _, hK, cK⟩ := extend J (by omega) (by omega) cJ
  obtain ⟨L, _, hL, cL⟩ := extend K (by omega) (by omega) cK
  obtain ⟨hlin, hdiag⟩ := extremal L (by omega) cL
  exact ⟨L, hlin, fun x y hxy ↦ hdiag x y hxy⟩

end OMA.R_Conway99Graph_conway99Graph_R1
