import OMAReductions.R_Erdos151_erdos_151_R2

-- Reduction of the guarded K₄-free Ramsey-jump case of Erdős Problem 151.
-- The bound through threshold nine is already kernel-checked in the K₄-free variant.
-- The additional restriction at higher thresholds comes from incidence-matrix rank.

open Finset SimpleGraph
open scoped Classical

namespace OMA.R_Erdos151_erdos_151_R2_H2_R1

/-- The previously proved small-threshold bound, specialized to K₄-free graphs. -/
def H1 : Prop :=
  ∀ m, Erdos151.H m ≤ 9 → ∀ G : SimpleGraph (Fin m), G.CliqueFree 4 →
    cliqueTransversalNumber G ≤ m - Erdos151.H m

/-- The remaining guarded jumps contain a family of triangles with an incidence matching
covering every edge of the family and with each of those edges used at least twice. -/
def H2 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin (n + 1))),
    10 ≤ Erdos151.H (n + 1) → Erdos151.H n < Erdos151.H (n + 1) →
    G.CliqueFree 4 →
    (∀ v, (univ.filter (G.Adj v)).card < Erdos151.H (n + 1)) →
    (¬ ∃ F : SimpleGraph (Fin (n + 1)), F.CliqueFree 3 ∧
      ∀ t, G.IsBigMaximalClique t → ∃ x ∈ t, ∃ y ∈ t, F.Adj x y) →
    (∀ A B : Finset (Fin (n + 1)), B.Nonempty → A ⊆ B →
      (∀ t, G.IsBigMaximalClique t → (∃ x ∈ t, x ∈ A) → ∃ y ∈ t, y ∈ B \ A) →
      A.card + Erdos151.H (n + 1 - B.card) < Erdos151.H (n + 1)) →
    (∃ T : Finset (Finset (Fin (n + 1))), T.Nonempty ∧
      (∀ t ∈ T, G.IsNClique 3 t) ∧
      let edges := fun t : Finset (Fin (n + 1)) => t.sym2.filter (fun e => ¬ e.IsDiag)
      (∀ S ⊆ T.biUnion edges, S.card ≤ (T.filter (fun t => ∃ e ∈ S, e ∈ edges t)).card) ∧
      (∀ e ∈ T.biUnion edges, 2 ≤ (T.filter (fun t => e ∈ edges t)).card)) →
    cliqueTransversalNumber G ≤ (n + 1) - Erdos151.H (n + 1)

section Proof

variable {ι α : Type*} [DecidableEq ι] [DecidableEq α]

/-- Full column rank is necessary for a minimal family without a bichromatic coloring.
A nonzero null vector supplies both signs on every constraint it touches. -/
private lemma incidence_bound (T : Finset ι) (E : ι → Finset α)
    (hbad : ¬ ∃ c : α → Bool, ∀ t ∈ T,
      (∃ e ∈ E t, c e = true) ∧ (∃ e ∈ E t, c e = false))
    (minimal : ∀ U ⊂ T, ∃ c : α → Bool, ∀ t ∈ U,
      (∃ e ∈ E t, c e = true) ∧ (∃ e ∈ E t, c e = false))
    (S : Finset α) (hS : S ⊆ T.biUnion E) :
    S.card ≤ (T.filter (fun t => ∃ e ∈ S, e ∈ E t)).card := by
  let U := T.filter (fun t => ∃ e ∈ S, e ∈ E t)
  let M : Matrix ↥U ↥S ℚ := fun t e => if e.val ∈ E t.val then 1 else 0
  let f := M.mulVecLin
  change S.card ≤ U.card
  by_contra! hsize
  have hni : ¬ Function.Injective f := by
    intro hi
    apply (Nat.not_le_of_lt hsize)
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] using
      LinearMap.finrank_le_finrank_of_injective hi
  have hkernel : ∃ w : ↥S → ℚ, f w = 0 ∧ w ≠ 0 := by
    by_contra! hz
    exact hni (LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr hz))
  obtain ⟨w, hfw, hw⟩ := hkernel
  let T₀ := T.filter (fun t => ∀ e : ↥S, e.val ∈ E t → w e = 0)
  have hT₀ : T₀ ⊂ T := by
    apply ssubset_iff_subset_ne.mpr
    refine ⟨filter_subset _ _, ?_⟩
    intro heq
    apply hw
    funext e
    obtain ⟨t, ht, het⟩ := mem_biUnion.mp (hS e.property)
    have ht₀ : t ∈ T₀ := by simpa only [heq] using ht
    exact (mem_filter.mp ht₀).2 e het
  obtain ⟨base, hbase⟩ := minimal T₀ hT₀
  let c (e : α) : Bool :=
    if h : e ∈ S then if w ⟨e, h⟩ = 0 then base e else decide (0 < w ⟨e, h⟩)
    else base e
  apply hbad
  refine ⟨c, ?_⟩
  intro t ht
  by_cases ht₀ : t ∈ T₀
  · have heq (e : α) (he : e ∈ E t) : c e = base e := by
      by_cases hs : e ∈ S
      · simp [c, hs, (mem_filter.mp ht₀).2 ⟨e, hs⟩ he]
      · simp [c, hs]
    obtain ⟨⟨p, hp, hcp⟩, ⟨q, hq, hcq⟩⟩ := hbase t ht₀
    exact ⟨⟨p, hp, (heq p hp).trans hcp⟩, ⟨q, hq, (heq q hq).trans hcq⟩⟩
  · have hnonzero : ∃ e : ↥S, e.val ∈ E t ∧ w e ≠ 0 := by
      by_contra! hz
      exact ht₀ (mem_filter.mpr ⟨ht, hz⟩)
    obtain ⟨e₀, he₀, hw₀⟩ := hnonzero
    have htU : t ∈ U := mem_filter.mpr ⟨ht, e₀.val, e₀.property, he₀⟩
    let term (e : ↥S) : ℚ := if e.val ∈ E t then w e else 0
    have hsum : ∑ e, term e = 0 := by
      have hrow := congrFun hfw ⟨t, htU⟩
      simpa [f, Matrix.mulVec, dotProduct, M, term, ite_mul] using hrow
    have hpos : ∃ e : ↥S, e.val ∈ E t ∧ 0 < w e := by
      by_contra! hp
      have hle (e : ↥S) : term e ≤ 0 := by
        by_cases he : e.val ∈ E t
        · simpa [term, he] using hp e he
        · simp [term, he]
      have hlt : term e₀ < 0 := by
        simpa [term, he₀] using lt_of_le_of_ne (hp e₀ he₀) hw₀
      have hltSum : ∑ e, term e < 0 := sum_neg' (fun e _ => hle e)
        ⟨e₀, mem_univ _, hlt⟩
      exact (ne_of_lt hltSum) hsum
    have hneg : ∃ e : ↥S, e.val ∈ E t ∧ w e < 0 := by
      by_contra! hn
      have hle (e : ↥S) : 0 ≤ term e := by
        by_cases he : e.val ∈ E t
        · simpa [term, he] using hn e he
        · simp [term, he]
      have hlt : 0 < term e₀ := by
        simpa [term, he₀] using lt_of_le_of_ne (hn e₀ he₀) (Ne.symm hw₀)
      have hltSum : 0 < ∑ e, term e := sum_pos' (fun e _ => hle e)
        ⟨e₀, mem_univ _, hlt⟩
      exact (ne_of_gt hltSum) hsum
    obtain ⟨p, hp, hwp⟩ := hpos
    obtain ⟨q, hq, hwq⟩ := hneg
    exact ⟨⟨p.val, hp, by simp [c, p.property, ne_of_gt hwp, hwp]⟩,
      ⟨q.val, hq, by simp [c, q.property, ne_of_lt hwq, not_lt_of_gt hwq]⟩⟩

private lemma edge_used_twice (T : Finset ι) (E : ι → Finset α)
    (two : ∀ t ∈ T, 2 ≤ (E t).card)
    (hbad : ¬ ∃ c : α → Bool, ∀ t ∈ T,
      (∃ e ∈ E t, c e = true) ∧ (∃ e ∈ E t, c e = false))
    (minimal : ∀ U ⊂ T, ∃ c : α → Bool, ∀ t ∈ U,
      (∃ e ∈ E t, c e = true) ∧ (∃ e ∈ E t, c e = false))
    (e : α) (he : e ∈ T.biUnion E) :
    2 ≤ (T.filter (fun t => e ∈ E t)).card := by
  obtain ⟨t, ht, het⟩ := mem_biUnion.mp he
  by_contra! hsize
  have hone : T.filter (fun u => e ∈ E u) = {t} := by
    symm
    refine eq_of_subset_of_card_le (singleton_subset_iff.mpr (mem_filter.mpr ⟨ht, het⟩)) ?_
    simpa only [card_singleton] using Nat.le_of_lt_succ hsize
  have hex : ∃ a ∈ E t, a ≠ e := by
    by_contra! h
    have hle := card_le_card (show E t ⊆ {e} from fun a ha => mem_singleton.mpr (h a ha))
    simp only [card_singleton] at hle
    have := two t ht
    omega
  obtain ⟨a, hat, hae⟩ := hex
  obtain ⟨base, hbase⟩ := minimal (T.erase t) (erase_ssubset ht)
  let c (x : α) := if x = e then !base a else base x
  apply hbad
  refine ⟨c, ?_⟩
  intro u hu
  by_cases hut : u = t
  · subst u
    cases hc : base a
    · exact ⟨⟨e, het, by simp [c, hc]⟩, ⟨a, hat, by simp [c, hae, hc]⟩⟩
    · exact ⟨⟨a, hat, by simp [c, hae, hc]⟩, ⟨e, het, by simp [c, hc]⟩⟩
  · have hne {x : α} (hx : x ∈ E u) : x ≠ e := by
      rintro rfl
      have hu' := mem_filter.mpr (p := fun u => e ∈ E u) ⟨hu, hx⟩
      rw [hone] at hu'
      exact hut (mem_singleton.mp hu')
    obtain ⟨⟨p, hp, hcp⟩, ⟨q, hq, hcq⟩⟩ := hbase u (mem_erase.mpr ⟨hut, hu⟩)
    exact ⟨⟨p, hp, by simpa [c, hne hp] using hcp⟩, ⟨q, hq, by simpa [c, hne hq] using hcq⟩⟩

private lemma hitting_of_bichromatic {m : ℕ} (G : SimpleGraph (Fin m))
    (c : Sym2 (Fin m) → Bool)
    (hc : ∀ t, G.IsNClique 3 t →
      (∃ e ∈ t.sym2.filter (fun e => ¬ e.IsDiag), c e = true) ∧
      (∃ e ∈ t.sym2.filter (fun e => ¬ e.IsDiag), c e = false)) :
    ∃ F : SimpleGraph (Fin m), F.CliqueFree 3 ∧
      ∀ t, G.IsBigMaximalClique t → ∃ x ∈ t, ∃ y ∈ t, F.Adj x y := by
  let F : SimpleGraph (Fin m) := {
    Adj := fun x y => G.Adj x y ∧ (c s(x, y) = true ∨ ¬ ∃ z, G.Adj x z ∧ G.Adj y z)
    symm := ⟨fun x y h => ⟨h.1.symm,
      h.2.elim (fun h => Or.inl ((congrArg c (Sym2.eq_swap (a := y) (b := x))).trans h))
        (fun h => Or.inr (fun ⟨z, hy, hx⟩ => h ⟨z, hx, hy⟩))⟩⟩
    loopless := ⟨fun _ h => G.irrefl h.1⟩ }
  refine ⟨F, ?_, ?_⟩
  · intro t ht
    have hcl : G.IsNClique 3 t := ⟨fun _ hx _ hy hne => (ht.1 hx hy hne).1, ht.2⟩
    obtain ⟨a, ha, hca⟩ := (hc t hcl).2
    induction a using Sym2.ind with
    | h x y =>
      have ⟨hxy, hne⟩ := mem_filter.mp ha
      have ⟨hx, hy⟩ := mk_mem_sym2_iff.mp hxy
      have hxyne : x ≠ y := fun heq => hne (Sym2.mk_isDiag_iff.mpr heq)
      have hzcard : (t.erase x |>.erase y).card = 1 := by
        rw [card_erase_of_mem (mem_erase.mpr ⟨hxyne.symm, hy⟩), card_erase_of_mem hx, ht.2]
      obtain ⟨z, hz⟩ := card_pos.mp (show 0 < (t.erase x |>.erase y).card by omega)
      obtain ⟨hzy, hzx, hzt⟩ := show z ≠ y ∧ z ≠ x ∧ z ∈ t by
        simpa only [mem_erase] using hz
      have hfxz : F.Adj x z := ht.1 hx hzt hzx.symm
      have hfyz : F.Adj y z := ht.1 hy hzt hzy.symm
      have hfxy : F.Adj x y := ht.1 hx hy hxyne
      exact Bool.false_ne_true (hca.symm.trans
        (hfxy.2.resolve_right (fun h => h ⟨z, hfxz.1, hfyz.1⟩)))
  · intro t ht
    by_cases hcard : 3 ≤ t.card
    · obtain ⟨u, hu, huc⟩ := exists_subset_card_eq hcard
      have hcl : G.IsNClique 3 u := ⟨fun _ hx _ hy hne => ht.1.1 (hu hx) (hu hy) hne, huc⟩
      obtain ⟨a, ha, hca⟩ := (hc u hcl).1
      induction a using Sym2.ind with
      | h x y =>
        have ⟨hxy, hne⟩ := mem_filter.mp ha
        have ⟨hx, hy⟩ := mk_mem_sym2_iff.mp hxy
        exact ⟨x, hu hx, y, hu hy,
          hcl.1 hx hy (fun heq => hne (Sym2.mk_isDiag_iff.mpr heq)), Or.inl hca⟩
    · have htwo : t.card = 2 := by have := ht.2; omega
      obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp htwo
      refine ⟨x, by simp, y, by simp, ht.1.1 (by simp) (by simp) hxy, Or.inr ?_⟩
      rintro ⟨z, hxz, hyz⟩
      have hcl : G.IsClique (↑(insert z ({x, y} : Finset (Fin m))) : Set (Fin m)) := by
        rw [coe_insert]
        apply ht.1.1.insert
        intro a ha _
        simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
        rcases ha with rfl | rfl
        · exact hxz.symm
        · exact hyz.symm
      have hz := ht.1.2 hcl (subset_insert _ _) (mem_insert_self _ _)
      simp only [mem_insert, mem_singleton] at hz
      exact hz.elim hxz.ne.symm hyz.ne.symm

lemma dense_triangle_family {m : ℕ} (G : SimpleGraph (Fin m))
    (hno : ¬ ∃ F : SimpleGraph (Fin m), F.CliqueFree 3 ∧
      ∀ t, G.IsBigMaximalClique t → ∃ x ∈ t, ∃ y ∈ t, F.Adj x y) :
    ∃ T : Finset (Finset (Fin m)), T.Nonempty ∧
      (∀ t ∈ T, G.IsNClique 3 t) ∧
      let E := fun t : Finset (Fin m) => t.sym2.filter (fun e => ¬ e.IsDiag)
      (∀ S ⊆ T.biUnion E, S.card ≤ (T.filter (fun t => ∃ e ∈ S, e ∈ E t)).card) ∧
      (∀ e ∈ T.biUnion E, 2 ≤ (T.filter (fun t => e ∈ E t)).card) := by
  let E := fun t : Finset (Fin m) => t.sym2.filter (fun e => ¬ e.IsDiag)
  let triangles := (univ : Finset (Finset (Fin m))).filter (G.IsNClique 3)
  let good (T : Finset (Finset (Fin m))) := ∃ c : Sym2 (Fin m) → Bool,
    ∀ t ∈ T, (∃ e ∈ E t, c e = true) ∧ (∃ e ∈ E t, c e = false)
  have hbad : ¬ good triangles := by
    rintro ⟨c, hc⟩
    exact hno (hitting_of_bichromatic G c
      (fun t ht => hc t (mem_filter.mpr ⟨mem_univ _, ht⟩)))
  let bad := triangles.powerset.filter (fun T => ¬ good T)
  have hbadmem : triangles ∈ bad := mem_filter.mpr ⟨mem_powerset.mpr Subset.rfl, hbad⟩
  obtain ⟨T, hT, hmin⟩ := exists_min_image bad card ⟨triangles, hbadmem⟩
  have hsub := mem_powerset.mp (mem_filter.mp hT).1
  have hTbad := (mem_filter.mp hT).2
  have hgood (U : Finset (Finset (Fin m))) (hU : U ⊂ T) : good U := by
    by_contra hn
    exact (not_le_of_gt (card_lt_card hU))
      (hmin U (mem_filter.mpr ⟨mem_powerset.mpr (hU.subset.trans hsub), hn⟩))
  have hTtri t (ht : t ∈ T) := (mem_filter.mp (hsub ht)).2
  have htwo t (ht : t ∈ T) : 2 ≤ (E t).card := by
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := is3Clique_iff.mp (hTtri t ht)
    have hm (u v : Fin m) (hu : u ∈ ({x, y, z} : Finset (Fin m)))
        (hv : v ∈ ({x, y, z} : Finset (Fin m))) (hne : u ≠ v) :
        s(u, v) ∈ E {x, y, z} :=
      mem_filter.mpr ⟨mk_mem_sym2_iff.mpr ⟨hu, hv⟩, fun h => hne (Sym2.mk_isDiag_iff.mp h)⟩
    have hne : s(x, y) ≠ s(x, z) := by
      rw [Sym2.eq_iff]
      exact fun h => h.elim (fun h => hyz.ne h.2) (fun h => hxz.ne h.1)
    have hsub' : ({s(x, y), s(x, z)} : Finset (Sym2 (Fin m))) ⊆ E {x, y, z} := by
      intro e he
      simp only [mem_insert, mem_singleton] at he
      rcases he with rfl | rfl
      · exact hm x y (by simp) (by simp) hxy.ne
      · exact hm x z (by simp) (by simp) hxz.ne
    simpa only [card_pair hne] using card_le_card hsub'
  have hne : T.Nonempty := by
    by_contra h
    exact hTbad ⟨fun _ => false, by simp [not_nonempty_iff_eq_empty.mp h]⟩
  exact ⟨T, hne, hTtri, incidence_bound T E hTbad hgood, edge_used_twice T E htwo hTbad hgood⟩

theorem main : H1 → H2 → OMA.R_Erdos151_erdos_151_R2.H2 := by
  intro small large n G _ hjump hK4 hdeg hno hguard
  by_cases hsmall : Erdos151.H (n + 1) ≤ 9
  · exact small (n + 1) hsmall G hK4
  · exact large n G (by omega) hjump hK4 hdeg hno hguard (dense_triangle_family G hno)

end Proof
end OMA.R_Erdos151_erdos_151_R2_H2_R1
