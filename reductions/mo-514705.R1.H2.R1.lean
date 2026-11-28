import OMAReductions.R_mo_514705_R1

/-!
# A pair criterion and a reflection criterion for the weighted union-closed sets conjecture

The excess of coordinate `k` is the left side minus the right side in MathOverflow
514705. We prove two sufficient conditions for some coordinate to have nonnegative excess.

* If adjoining a pair `{a,b}` preserves the family, the excesses of `a` and `b`
  sum to a nonnegative number for every nonnegative increasing set weight. Group
  sets by their trace away from the pair. On each occupied face the upper corner
  is present and compensates the other three corners.
* Fix a greatest member `U` and an `m`-subset `B` of it. After summation over
  coordinates, each member `A` containing `B` contributes with multiplicity
  `|A ∖ B| - |U ∖ A|`. Reflection `A ↦ B ∪ (U ∖ A)` negates this multiplicity.
  If every negative term has its reflection in the family, the total excess is
  nonnegative for arbitrary nonnegative coefficients on the `m`-subsets.

In particular, if every subset missing at most `t` points of `U` occurs, then
`|U| ≤ m + 2*t + 2` suffices. For `t = 0` this uses only the top member.
The bound two at `t = 0` is sharp for the total excess. In degree zero the
union-closed family consisting of the empty set, {a}, {b}, {a,b}, {a,b,c} has
total excess -1; it still has abundant elements.

The reduction separates degree zero and positive degree after excluding
two-element members. The positive-degree case also requires an explicitly
described missing set near the top. The general conjecture remains open.
-/

namespace OMA.R_mo_514705_R1_H2_R1

/-- The signed contributions on one face of the Boolean cube. Closing the face under
adjoining both distinguished elements forces its upper corner whenever the face is occupied. -/
private lemma face_nonneg (e p q t : Prop) [Decidable e] [Decidable p] [Decidable q]
    [Decidable t] (he : e → t) (hp : p → t) (hq : q → t)
    (u v z : ℝ) (hu : 0 ≤ u) (hv : u ≤ v) (hz : u ≤ z) :
    0 ≤ (if e then -u - u else 0) + (if q then u - z else 0) +
        ((if p then u - v else 0) + (if t then z + v else 0)) := by
  by_cases ht : t
  · by_cases h₀ : e <;> by_cases h₁ : p <;> by_cases h₂ : q <;>
      simp only [ht, h₀, h₁, h₂, if_true, if_false] <;> linarith
  · simp [ht, mt he ht, mt hp ht, mt hq ht]

/-- If adjoining a fixed pair preserves a finite family, the two weighted excesses
sum to a nonnegative number, for every nonnegative inclusion-monotone weight. -/
theorem pair_excess_nonneg {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) {a b : α} (hab : a ≠ b)
    (hc : ∀ A ∈ F, insert a (insert b A) ∈ F)
    (w : Finset α → ℝ) (hw : ∀ A, 0 ≤ w A) (hm : Monotone w) :
    0 ≤ ((∑ A ∈ F.filter (a ∈ ·), w (A.erase a)) - ∑ A ∈ F.filter (a ∉ ·), w A) +
        ((∑ A ∈ F.filter (b ∈ ·), w (A.erase b)) - ∑ A ∈ F.filter (b ∉ ·), w A) := by
  classical
  let score (k : α) (A : Finset α) := if k ∈ A then w (A.erase k) else -w A
  have excess (k : α) :
      (∑ A ∈ F.filter (k ∈ ·), w (A.erase k)) - (∑ A ∈ F.filter (k ∉ ·), w A) =
        ∑ A ∈ F, score k A := by
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro A _
    by_cases h : k ∈ A <;> simp [score, h]
  rw [excess, excess, ← Finset.sum_add_distrib]
  let f (A : Finset α) := if A ∈ F then score a A + score b A else 0
  let s := ((F.biUnion id).erase a).erase b
  have ha : a ∉ s := by simp [s]
  have hb : b ∉ s := by simp [s]
  have covers : F ⊆ (insert a (insert b s)).powerset := by
    intro A hA
    apply Finset.mem_powerset.mpr
    intro i hi
    have hiU : i ∈ F.biUnion id := Finset.mem_biUnion.mpr ⟨A, hA, hi⟩
    by_cases hia : i = a <;> by_cases hib : i = b <;> simp [s, *]
  have extend : (∑ A ∈ (insert a (insert b s)).powerset, f A) =
      ∑ A ∈ F, (score a A + score b A) := by
    simp only [f, Finset.sum_ite_mem, Finset.inter_eq_right.mpr covers]
  rw [← extend, Finset.sum_powerset_insert (by simp [hab, ha]), Finset.sum_powerset_insert hb,
    Finset.sum_powerset_insert hb, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_nonneg
  intro A hA
  have hsub := Finset.mem_powerset.mp hA
  have haA : a ∉ A := fun h => ha (hsub h)
  have hbA : b ∉ A := fun h => hb (hsub h)
  have hp (h : insert a A ∈ F) : insert a (insert b A) ∈ F := by
    simpa only [Finset.insert_comm b a, Finset.insert_idem] using hc _ h
  have hq (h : insert b A ∈ F) : insert a (insert b A) ∈ F := by
    simpa using hc _ h
  have face := face_nonneg (A ∈ F) (insert a A ∈ F) (insert b A ∈ F)
    (insert a (insert b A) ∈ F) (hc A) hp hq (w A) (w (insert a A)) (w (insert b A))
    (hw A) (hm (Finset.subset_insert _ _)) (hm (Finset.subset_insert _ _))
  simpa [f, score, haA, hbA, hab, Ne.symm hab, Finset.erase_insert_of_ne, sub_eq_add_neg,
    add_comm, add_left_comm, add_assoc] using face

/-- Extend a sum on the rank-`m` subsets of a member to the corresponding layer of
the whole ground set. -/
private lemma layer_restrict {α : Type*} [DecidableEq α] {A U : Finset α} (h : A ⊆ U)
    (m : ℕ) (c : Finset α → ℝ) :
    ∑ B ∈ A.powersetCard m, c B =
      ∑ B ∈ U.powersetCard m, if B ⊆ A then c B else 0 := by
  classical
  rw [← Finset.sum_filter]
  congr 1
  ext B
  simp only [Finset.mem_filter, Finset.mem_powersetCard]
  exact ⟨fun ⟨hB, hm⟩ => ⟨⟨hB.trans h, hm⟩, hB⟩, fun ⟨⟨_, hm⟩, hB⟩ => ⟨hB, hm⟩⟩

/-- Pair each negative summand injectively with a summand of the opposite sign. -/
private lemma sum_nonneg_of_reflection {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (f : ι → ℝ) (flip : ι → ι)
    (h : ∀ i ∈ S, f i < 0 → flip i ∈ S ∧ f (flip i) = -f i ∧ flip (flip i) = i) :
    0 ≤ ∑ i ∈ S, f i := by
  classical
  let N := S.filter (fun i => f i < 0)
  let P := S.filter (fun i => ¬ f i < 0)
  have pair (i) (hi : i ∈ N) := h i (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hi).2
  have hp : N.image flip ⊆ P := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    have hn := (Finset.mem_filter.mp hi).2
    exact Finset.mem_filter.mpr ⟨(pair i hi).1, by rw [(pair i hi).2.1]; linarith⟩
  have opposite : (∑ i ∈ N.image flip, f i) = -(∑ i ∈ N, f i) := by
    rw [Finset.sum_image, ← Finset.sum_neg_distrib]
    · exact Finset.sum_congr rfl fun i hi => (pair i hi).2.1
    · intro i hi j hj heq
      simpa only [(pair i hi).2.2, (pair j hj).2.2] using congrArg flip heq
  have bound := Finset.sum_le_sum_of_subset_of_nonneg (f := f) hp
    (fun i hi _ => le_of_not_gt (Finset.mem_filter.mp hi).2)
  rw [← Finset.sum_filter_add_sum_filter_not S (fun i => f i < 0) f]
  change 0 ≤ (∑ i ∈ N, f i) + ∑ i ∈ P, f i
  linarith only [opposite, bound]

/-- The reflection of a member in the interval from `B` to `U` swaps its two
distances to the ends of the interval. -/
private lemma reflect_diffs {α : Type*} [DecidableEq α] {B A U : Finset α}
    (hBA : B ⊆ A) (hAU : A ⊆ U) :
    (B ∪ (U \ A)) \ B = U \ A ∧ U \ (B ∪ (U \ A)) = A \ B := by
  constructor <;> ext i <;> simp only [Finset.mem_sdiff, Finset.mem_union] <;>
    by_cases hB : i ∈ B <;> by_cases hA : i ∈ A <;> by_cases hU : i ∈ U <;>
      first | exact False.elim (hA (hBA hB)) | exact False.elim (hU (hAU hA)) | simp [*]

/-- Reflecting the lower half of each rank interval into the family gives
nonnegative total excess for arbitrary nonnegative coefficients on the layer. -/
theorem layer_excess_nonneg_of_reflection {α : Type*} [DecidableEq α] {U : Finset α}
    (F : Finset (Finset α)) (hsub : ∀ A ∈ F, A ⊆ U) (m : ℕ)
    (href : ∀ B ∈ U.powersetCard m, ∀ A ∈ F, B ⊆ A →
      (A \ B).card < (U \ A).card → B ∪ (U \ A) ∈ F)
    (c : Finset α → ℝ) (hc : ∀ B, 0 ≤ c B) :
    (∑ k ∈ U, ∑ A ∈ F.filter (k ∉ ·), ∑ B ∈ A.powersetCard m, c B) ≤
      ∑ k ∈ U, ∑ A ∈ F.filter (k ∈ ·), ∑ B ∈ (A.erase k).powersetCard m, c B := by
  classical
  let sgn (B A : Finset α) (k : α) : ℝ :=
    if B ⊆ A ∧ k ∉ B then (if k ∈ A then 1 else -1) else 0
  have count (B A : Finset α) (hBA : B ⊆ A) (hAU : A ⊆ U) :
      ∑ k ∈ U, sgn B A k = ((A \ B).card : ℝ) - (U \ A).card := by
    calc
      _ = ∑ k ∈ U, ((if k ∈ A \ B then (1 : ℝ) else 0) -
          (if k ∈ U \ A then 1 else 0)) := by
        apply Finset.sum_congr rfl
        intro k hk
        by_cases ha : k ∈ A <;> by_cases hb : k ∈ B <;>
          first | exact False.elim (ha (hBA hb)) | simp [sgn, hBA, ha, hb, hk]
      _ = _ := by
        rw [Finset.sum_sub_distrib]
        have hi : U ∩ (A \ B) = A \ B := Finset.inter_eq_right.mpr
          (Finset.sdiff_subset.trans hAU)
        rw [← Finset.sum_filter, ← Finset.sum_filter, Finset.filter_mem_eq_inter,
          Finset.filter_mem_eq_inter, hi, Finset.inter_eq_right.mpr Finset.sdiff_subset]
        simp
  have fiber (B : Finset α) (hB : B ∈ U.powersetCard m) :
      0 ≤ ∑ A ∈ F, ∑ k ∈ U, sgn B A k := by
    let flip (A : Finset α) := B ∪ (U \ A)
    apply sum_nonneg_of_reflection F _ flip
    intro A hA hn
    have hBA : B ⊆ A := by
      by_contra h
      simp [sgn, h] at hn
    have hAU := hsub A hA
    have hBU := Finset.mem_powersetCard.mp hB |>.1
    have hneg : (A \ B).card < (U \ A).card := by
      rw [count B A hBA hAU] at hn
      exact_mod_cast (sub_neg.mp hn)
    obtain ⟨h₁, h₂⟩ := reflect_diffs hBA hAU
    refine ⟨href B hB A hA hBA hneg, ?_, ?_⟩
    · rw [count B A hBA hAU, count B (flip A) Finset.subset_union_left
        (Finset.union_subset hBU Finset.sdiff_subset)]
      dsimp [flip]
      rw [h₁, h₂]
      abel
    · dsimp [flip]
      rw [h₂, Finset.union_sdiff_of_subset hBA]
  have total : 0 ≤ ∑ k ∈ U, ∑ A ∈ F, ∑ B ∈ U.powersetCard m, c B * sgn B A k := by
    calc
      0 ≤ ∑ B ∈ U.powersetCard m, c B * ∑ A ∈ F, ∑ k ∈ U, sgn B A k :=
        Finset.sum_nonneg fun B hB => mul_nonneg (hc B) (fiber B hB)
      _ = ∑ A ∈ F, ∑ B ∈ U.powersetCard m, ∑ k ∈ U, c B * sgn B A k := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
      _ = ∑ A ∈ F, ∑ k ∈ U, ∑ B ∈ U.powersetCard m, c B * sgn B A k := by
        apply Finset.sum_congr rfl
        intro A _
        rw [Finset.sum_comm]
      _ = _ := Finset.sum_comm
  apply sub_nonneg.mp
  rw [← Finset.sum_sub_distrib]
  apply le_of_le_of_eq total
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro A hA
  have hAU := hsub A hA
  by_cases hkA : k ∈ A
  · simp only [hkA, not_true_eq_false, if_false, if_true, sub_zero]
    rw [layer_restrict ((Finset.erase_subset k A).trans hAU) m c]
    apply Finset.sum_congr rfl
    intro B _
    by_cases h : B ⊆ A ∧ k ∉ B <;> simp [sgn, hkA, Finset.subset_erase, h]
  · simp only [hkA, not_false_eq_true, if_true, if_false, zero_sub]
    rw [layer_restrict hAU m c, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro B _
    by_cases h : B ⊆ A
    · have hkB : k ∉ B := fun hb => hkA (h hb)
      simp [sgn, h, hkB, hkA]
    · simp [sgn, h]

/-- If all subsets missing at most `t` points of the top are present, every degree
with `|U| ≤ m + 2*t + 2` has nonnegative total excess. Setting `t = 0` only
requires the top. Setting `t = 1` also uses its one-element deletions. -/
theorem top_layers_excess_nonneg {α : Type*} [DecidableEq α] {U : Finset α}
    (F : Finset (Finset α)) (hsub : ∀ A ∈ F, A ⊆ U) (m t : ℕ)
    (hd : U.card ≤ m + 2 * t + 2)
    (hfull : ∀ C ⊆ U, (U \ C).card ≤ t → C ∈ F)
    (c : Finset α → ℝ) (hc : ∀ B, 0 ≤ c B) :
    (∑ k ∈ U, ∑ A ∈ F.filter (k ∉ ·), ∑ B ∈ A.powersetCard m, c B) ≤
      ∑ k ∈ U, ∑ A ∈ F.filter (k ∈ ·), ∑ B ∈ (A.erase k).powersetCard m, c B := by
  apply layer_excess_nonneg_of_reflection F hsub m _ c hc
  intro B hB A hA hBA hn
  obtain ⟨hBU, hm⟩ := Finset.mem_powersetCard.mp hB
  have hAU := hsub A hA
  apply hfull _ (Finset.union_subset hBU Finset.sdiff_subset)
  rw [(reflect_diffs hBA hAU).2, Finset.card_sdiff_of_subset hBA]
  rw [Finset.card_sdiff_of_subset hBA, Finset.card_sdiff_of_subset hAU] at hn
  have := Finset.card_le_card hBA
  have := Finset.card_le_card hAU
  omega

/-- The degree-zero case is the usual abundance question, restricted to families
whose nonempty members have size at least three. -/
def H1 : Prop :=
  ∀ (n : ℕ) (F : Finset (Finset (Fin n))),
    (∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F) → (∃ A ∈ F, A.Nonempty) →
    (∀ A ∈ F, A.Nonempty → 3 ≤ A.card) →
    ∃ k : Fin n, (F.filter (k ∉ ·)).card ≤ (F.filter (k ∈ ·)).card

/-- A positive-degree counterexample would have a missing set near the top.
Here `U` is the greatest member and the missing set `C` satisfies
`2 * |U ∖ C| < |U| - m`. In particular, the top must have size at least `m + 3`. -/
def H2 : Prop :=
  ∀ (n m : ℕ) (F : Finset (Finset (Fin n))) (x : Fin n → ℝ),
    0 < m →
    (∃ U ∈ F, (∀ A ∈ F, A ⊆ U) ∧
      ∃ C ⊆ U, C ∉ F ∧ m + 2 * (U \ C).card < U.card) →
    (∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F) →
    (∀ A ∈ F, A.Nonempty → 3 ≤ A.card) → (∀ i, 0 ≤ x i) →
    ∃ k : Fin n,
      (∑ A ∈ F.filter (k ∉ ·), ∑ B ∈ A.powersetCard m, ∏ i ∈ B, x i) ≤
        ∑ A ∈ F.filter (k ∈ ·), ∑ B ∈ (A.erase k).powersetCard m, ∏ i ∈ B, x i

theorem main : H1 → H2 → OMA.R_mo_514705_R1.H2 := by
  classical
  intro h₀ hposCase n m F x _ huc hne hx hsingle
  let c (B : Finset (Fin n)) := ∏ i ∈ B, x i
  have hc (B) : 0 ≤ c B := Finset.prod_nonneg fun i _ => hx i
  by_cases hp : ∃ a b : Fin n, a ≠ b ∧ {a, b} ∈ F
  · obtain ⟨a, b, hab, hp⟩ := hp
    let w (A : Finset (Fin n)) := ∑ B ∈ A.powersetCard m, c B
    have hw (A) : 0 ≤ w A := Finset.sum_nonneg fun B _ => hc B
    have hm : Monotone w := fun _ _ h =>
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.powersetCard_mono h) (fun B _ _ => hc B)
    have hclose (A) (hA : A ∈ F) : insert a (insert b A) ∈ F := by
      simpa using huc {a, b} hp A hA
    have hboth := pair_excess_nonneg F hab hclose w hw hm
    by_contra! hbad
    dsimp [w, c] at hboth
    linarith only [hboth, hbad a, hbad b]
  have hlarge (A) (hA : A ∈ F) (hAne : A.Nonempty) : 3 ≤ A.card := by
    by_contra! h
    have hpos := hAne.card_pos
    rcases (show A.card = 1 ∨ A.card = 2 by omega) with h₁ | h₂
    · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h₁
      exact hsingle a hA
    · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h₂
      exact hp ⟨a, b, hab, hA⟩
  by_cases hm : m = 0
  · subst m
    obtain ⟨k, hk⟩ := h₀ n F huc hne hlarge
    refine ⟨k, ?_⟩
    simpa using (Nat.cast_le.mpr hk : ((F.filter (k ∉ ·)).card : ℝ) ≤ (F.filter (k ∈ ·)).card)
  obtain ⟨A, hA, hAne⟩ := hne
  obtain ⟨U, hU, hmax⟩ := F.exists_max_image Finset.card ⟨A, hA⟩
  have covers (B) (hB : B ∈ F) : B ⊆ U := by
    have eq := Finset.eq_of_subset_of_card_le (Finset.subset_union_right (s₁ := B) (s₂ := U))
      (hmax (B ∪ U) (huc B hB U hU))
    exact eq.symm ▸ Finset.subset_union_left
  by_cases hole : ∃ C ⊆ U, C ∉ F ∧ m + 2 * (U \ C).card < U.card
  · exact hposCase n m F x (by omega) ⟨U, hU, covers, hole⟩ huc hlarge hx
  let t := (U.card - (m + 1)) / 2
  have hd : U.card ≤ m + 2 * t + 2 := by dsimp [t]; omega
  have full (C) (hCU : C ⊆ U) (hsmall : (U \ C).card ≤ t) : C ∈ F := by
    by_contra hCF
    have hneCU : C ≠ U := fun h => hCF (h ▸ hU)
    have hpos : 0 < (U \ C).card := by
      rw [Finset.card_sdiff_of_subset hCU]
      exact Nat.sub_pos_of_lt (Finset.card_lt_card (lt_of_le_of_ne (show C ≤ U from hCU) hneCU))
    exact hole ⟨C, hCU, hCF, by dsimp [t] at hsmall; omega⟩
  have htotal := top_layers_excess_nonneg F covers m t hd full c hc
  obtain ⟨k, _, hk⟩ := Finset.exists_le_of_sum_le (hAne.mono (covers A hA)) htotal
  exact ⟨k, hk⟩

end OMA.R_mo_514705_R1_H2_R1
