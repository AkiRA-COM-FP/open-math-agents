import OMAReductions.R_opg_seymours_r_graph_conjecture_R1
import Mathlib

/-! A maximum cut leaves a matching inside the two sides of a subcubic multigraph.
The crossing edges are coloured using a decomposition of their multiplicity matrix. -/

open Finset
open scoped Classical

namespace Shannon

variable {V E : Type}

def flip [DecidableEq V] (s : V → Bool) (v x : V) : Bool := if x = v then !(s x) else s x

lemma flip_identity [DecidableEq V] (s : V → Bool) (v : V) (z : Sym2 V) (hz : ¬ z.IsDiag) :
    (if ¬ (z.map s).IsDiag then 1 else 0 : ℕ) +
      2 * (if v ∈ z ∧ (z.map s).IsDiag then 1 else 0) =
    (if ¬ (z.map (flip s v)).IsDiag then 1 else 0) +
      (if v ∈ z then 1 else 0) := by
  induction z using Sym2.ind with
  | h a b =>
    have hab : a ≠ b := by simpa using hz
    simp only [Sym2.map_mk, Sym2.mk_isDiag_iff, Sym2.mem_iff, flip]
    by_cases ha : a = v
    · subst v
      cases s a <;> cases s b <;> simp [hab, hab.symm]
    by_cases hb : b = v
    · subst v
      cases s a <;> cases s b <;> simp [hab, hab.symm]
    simp [ha, hb, Ne.symm ha, Ne.symm hb]

theorem cut_degree_bound [Fintype V] [DecidableEq V] [Fintype E] (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag)
    (d : ℕ) (hdeg : ∀ v : V, (univ.filter fun e => v ∈ ends e).card ≤ d) :
    ∃ s : V → Bool, ∀ v : V,
      (univ.filter fun e => v ∈ ends e ∧ ((ends e).map s).IsDiag).card ≤ d / 2 := by
  classical
  let cut (s : V → Bool) : ℕ := (univ.filter fun e => ¬ ((ends e).map s).IsDiag).card
  obtain ⟨s, _, hs⟩ := exists_max_image univ cut univ_nonempty
  refine ⟨s, fun v => ?_⟩
  have h := hs (flip s v) (mem_univ _)
  have hsum := sum_congr (s₁ := (univ : Finset E)) rfl (fun e _ => flip_identity s v (ends e) (hloop e))
  simp only [sum_add_distrib, ← mul_sum, ← card_filter] at hsum
  dsimp [cut] at h
  have := hdeg v
  omega

theorem extend_coloring [DecidableEq V] [Fintype E] (ends : E → Sym2 V) (s : V → Bool) (d : ℕ) (hd : d ≤ 3)
    (hcut : ∀ v : V, (univ.filter fun e => v ∈ ends e ∧ ((ends e).map s).IsDiag).card ≤ d / 2)
    (c : {e : E // ¬ ((ends e).map s).IsDiag} → Fin d)
    (hc : ∀ e f, e ≠ f → (∃ v : V, v ∈ ends e.val ∧ v ∈ ends f.val) → c e ≠ c f) :
    ∃ col : E → Fin (3 * d / 2),
      ∀ e f, e ≠ f → (∃ v : V, v ∈ ends e ∧ v ∈ ends f) → col e ≠ col f := by
  classical
  have hi (e : E) (he : ((ends e).map s).IsDiag) : d < 3 * d / 2 := by
    let v := (ends e).out.1
    have hv : v ∈ ends e := Sym2.out_fst_mem _
    have hz := card_pos.mpr (show (univ.filter fun f => v ∈ ends f ∧ ((ends f).map s).IsDiag).Nonempty
      from ⟨e, by simp [hv, he]⟩)
    have := hcut v
    omega
  let col (e : E) : Fin (3 * d / 2) :=
    if h : ((ends e).map s).IsDiag then ⟨d, hi e h⟩ else (c ⟨e,h⟩).castLE (by omega)
  refine ⟨col, fun e f hne ⟨v, he, hf⟩ heq => ?_⟩
  have hval := congrArg Fin.val heq
  by_cases a : ((ends e).map s).IsDiag <;> by_cases b : ((ends f).map s).IsDiag
  · have hu : (univ.filter fun g => v ∈ ends g ∧ ((ends g).map s).IsDiag).card ≤ 1 := by
      have := hcut v
      omega
    exact hne (card_le_one_iff.mp hu (by simp [he, a]) (by simp [hf, b]))
  · simp [col, a, b] at hval
    exact (c ⟨f,b⟩).isLt.ne hval.symm
  · simp [col, a, b] at hval
    exact (c ⟨e,a⟩).isLt.ne hval
  · simp [col, a, b] at hval
    exact hc ⟨e,a⟩ ⟨f,b⟩ (fun h => hne (congrArg Subtype.val h)) ⟨v,he,hf⟩ (Fin.ext hval)

abbrev Crossing (ends : E → Sym2 V) (side : V → Bool) :=
  {e : E // ¬ ((ends e).map side).IsDiag}

theorem oriented_pair (side : V → Bool) (z : Sym2 V) (hz : ¬ (z.map side).IsDiag) :
    ∃ l r : V, z = s(l,r) ∧ side l = false ∧ side r = true := by
  induction z using Sym2.ind with
  | h a b =>
    have hne : side a ≠ side b := by simpa [Sym2.map_mk] using hz
    cases ha : side a <;> cases hb : side b <;> simp_all
    · exact ⟨a,b,Or.inl ⟨rfl,rfl⟩,ha,hb⟩
    · exact ⟨b,a,Or.inr ⟨rfl,rfl⟩,hb,ha⟩

theorem orientation [Fintype E] [DecidableEq V] (ends : E → Sym2 V) (side : V → Bool) :
    ∃ left right : Crossing ends side → V,
      (∀ v, (univ.filter fun e => left e = v).card + (univ.filter fun e => right e = v).card ≤
        (univ.filter fun e => v ∈ ends e).card) ∧
      ∀ e f, (∃ v, v ∈ ends e.val ∧ v ∈ ends f.val) → left e = left f ∨ right e = right f := by
  classical
  choose left right h using fun e : Crossing ends side => oriented_pair side (ends e.val) e.property
  have incident (e : Crossing ends side) (v : V) : v ∈ ends e.val ↔ v = left e ∨ v = right e := by
    rw [(h e).1, Sym2.mem_iff]
  refine ⟨left, right, fun v => ?_, ?_⟩
  · let L := univ.filter fun e => left e = v
    let R := univ.filter fun e => right e = v
    have dis : Disjoint L R := by
      simp only [L, R, disjoint_left, mem_filter, mem_univ, true_and]
      grind
    change L.card + R.card ≤ _
    rw [← card_union_of_disjoint dis]
    apply card_le_card_of_injOn Subtype.val _ (fun _ _ _ _ => Subtype.ext)
    intro e he
    change e ∈ L ∪ R at he
    simpa [L, R, incident, eq_comm] using he
  · rintro e f ⟨v,he,hf⟩
    have := (incident e v).mp he
    have := (incident f v).mp hf
    have := (h e).2
    have := (h f).2
    grind

/-- A natural-valued square matrix with constant positive row and column sums
has a permutation supported on its positive entries. -/
theorem exists_supported_perm {V : Type*} [Fintype V] (M : V → V → ℕ) (k : ℕ)
    (row : ∀ i, ∑ j, M i j = k + 1) (col : ∀ j, ∑ i, M i j = k + 1) :
    ∃ σ : Equiv.Perm V, ∀ i, 0 < M i (σ i) := by
  classical
  let N (i : V) := univ.filter fun j => M i j ≠ 0
  have hall (A : Finset V) : A.card ≤ (A.biUnion N).card := by
    have rows (i : V) : ∑ j ∈ N i, M i j = k + 1 := by
      rw [← row i]
      exact sum_subset (filter_subset _ _) fun j _ hj => by simpa [N] using hj
    have lhs : ∑ i ∈ A, ∑ j ∈ N i, M i j = A.card * (k + 1) := by simp [rows]
    have rhs : ∑ i, ∑ j ∈ A.biUnion N, M i j = (A.biUnion N).card * (k + 1) := by
      rw [sum_comm]
      simp [col]
    apply (Nat.mul_le_mul_right_iff (show 0 < k + 1 by omega)).mp
    rw [← lhs, ← rhs]
    trans ∑ i ∈ A, ∑ j ∈ A.biUnion N, M i j
    · exact sum_le_sum fun i hi => sum_le_sum_of_subset (subset_biUnion_of_mem N hi)
    · exact sum_le_sum_of_subset (subset_univ A)
  obtain ⟨f, hf, hN⟩ := (all_card_le_biUnion_card_iff_existsInjective' N).mp hall
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf),
    fun i => Nat.pos_of_ne_zero (mem_filter.mp (hN i)).2⟩


theorem exists_perm_decomposition {V : Type*} [Fintype V] [DecidableEq V] (d : ℕ)
    (M : V → V → ℕ) (row : ∀ i, ∑ j, M i j = d) (col : ∀ j, ∑ i, M i j = d) :
    ∃ σ : Fin d → Equiv.Perm V, ∀ i j, (univ.filter fun c => σ c i = j).card = M i j := by
  classical
  induction d generalizing M with
  | zero =>
    refine ⟨Fin.elim0, fun i j => ?_⟩
    have h := single_le_sum (f := M i) (fun a _ => Nat.zero_le (M i a)) (mem_univ j)
    simp [row] at h
    simp [h]
  | succ d ih =>
    obtain ⟨π, hπ⟩ := exists_supported_perm M d row col
    let D (i j : V) := if π i = j then 1 else 0
    let R (i j : V) := M i j - D i j
    have add (i j : V) : R i j + D i j = M i j := by
      apply Nat.sub_add_cancel
      have := hπ i
      dsimp [D]
      split_ifs <;> grind
    have rows (i : V) : ∑ j, R i j = d := by
      have h : (∑ j, R i j) + ∑ j, D i j = d+1 := by simp_rw [← sum_add_distrib, add, row]
      simpa [D] using h
    have cols (j : V) : ∑ i, R i j = d := by
      have h : (∑ i, R i j) + ∑ i, D i j = d+1 := by simp_rw [← sum_add_distrib, add, col]
      simpa [D, ← Equiv.eq_symm_apply] using h
    obtain ⟨σ, hσ⟩ := ih R rows cols
    refine ⟨Fin.cons π σ, fun i j => ?_⟩
    rw [← add i j, ← hσ, card_filter, card_filter, Fin.sum_univ_succ]
    simp [D, Nat.add_comm]

/-- Pad the labelled bipartite graph to a regular matrix, then assign each
parallel class distinct colours from its permutation decomposition. -/
theorem color_bipartite {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    (left right : E → V) (d : ℕ)
    (hd : ∀ u, (univ.filter (fun e => left e = u)).card +
      (univ.filter (fun e => right e = u)).card ≤ d) :
    ∃ color : E → Fin d, ∀ e f, color e = color f →
      (left e = left f ∨ right e = right f) → e = f := by
  classical
  let fiber (u v : V) := univ.filter (fun e => left e = u ∧ right e = v)
  let n (u v : V) := (fiber u v).card
  let deg (u : V) := (univ.filter (fun e => left e = u)).card +
    (univ.filter (fun e => right e = u)).card
  have out (a b : E → V) (u : V) : ∑ v, (univ.filter (fun e => a e = u ∧ b e = v)).card =
      (univ.filter (fun e => a e = u)).card := by
    simpa [filter_filter] using (card_eq_sum_card_fiberwise
      (s := univ.filter (fun e => a e = u)) (f := b) (t := univ) (by simp)).symm
  let M (u v : V) := n u v + n v u + if u = v then d - deg u else 0
  have reg (u : V) : ∑ v, M u v = d := by
    have inc : ∑ v, n v u = (univ.filter fun e => right e = u).card := by
      simpa [n, fiber, and_comm] using out right left u
    simpa [M, sum_add_distrib, inc, n, fiber, out, deg] using Nat.add_sub_of_le (hd u)
  have symm (u v : V) : M u v = M v u := by
    by_cases h : u = v
    · subst v; rfl
    · simp [M, h, Ne.symm h, add_comm]
  obtain ⟨σ, hσ⟩ := exists_perm_decomposition d M reg fun v =>
    (sum_congr rfl fun u _ => symm u v).trans (reg v)
  let palette (u v : V) := univ.filter (fun c => σ c u = v)
  have emb (u v : V) : Nonempty (↥(fiber u v) ↪ ↥(palette u v)) := by
    apply Function.Embedding.nonempty_of_card_le
    simp only [Fintype.card_coe, palette, hσ]
    change n u v ≤ n u v + n v u + _
    omega
  let map (u v) := (emb u v).some
  let color e := ((map (left e) (right e)) ⟨e, by simp [fiber]⟩).val
  have matched (e) : σ (color e) (left e) = right e :=
    (mem_filter.mp ((map (left e) (right e)) ⟨e, by simp [fiber]⟩).prop).2
  refine ⟨color, fun e f hc h => ?_⟩
  have hpair : left e = left f ∧ right e = right f := by
    have eq := (σ (color f)).injective.eq_iff (a := left e) (b := left f)
    rw [← hc, matched e, hc, matched f] at eq
    tauto
  have same {u v u' v' : V} (a : fiber u v) (b : fiber u' v')
      (hu : u = u') (hv : v = v') (hc' : (map u v a).val = (map u' v' b).val) : a.val = b.val := by
    subst u'
    subst v'
    exact congrArg Subtype.val ((map u v).injective (Subtype.ext hc'))
  exact same ⟨e, by simp [fiber]⟩ ⟨f, by simp [fiber]⟩ hpair.1 hpair.2 hc

end Shannon

open Shannon in
theorem OMA.solution : OMA.R_opg_seymours_r_graph_conjecture_R1.H1 := by
  classical
  intro V E _ _ _ ends hloop d hd hdeg
  obtain ⟨side, hcut⟩ := cut_degree_bound ends hloop d hdeg
  obtain ⟨left, right, degrees, incident⟩ := orientation ends side
  obtain ⟨c, hc⟩ := color_bipartite left right d (fun v => (degrees v).trans (hdeg v))
  exact extend_coloring ends side d hd hcut c fun e f hne hadj heq =>
    hne (hc e f heq (incident e f hadj))
