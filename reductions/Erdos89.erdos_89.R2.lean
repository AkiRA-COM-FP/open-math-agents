import FormalConjectures.ErdosProblems.«89»

-- Reduction of Erdos89.erdos_89. Credit: @wispiANt
open Filter Finset EuclideanGeometry

namespace OMA.R_Erdos89_erdos_89_R2

/-- Bisector incidence estimate for configurations with at most K points
on any affine line. -/
def H1 : Prop :=
  ∀ (S : Finset ℝ²) (K : ℕ),
    (∀ a b c : ℝ, (a ≠ 0 ∨ b ≠ 0) →
      (S.filter fun p => a*p 0+b*p 1=c).card ≤ K) →
    S.card ≤ (K+1)*(distinctDistances S+1)

/-- Packing problem for disjoint collinear blocks. If each block contains
k points and the family covers at most exp(k²) points, bound the number
of blocks by a constant times the number of distances in their union plus one.
Assume that any collection of at most k lines or circles contains fewer than
half the points of the union. At each pin, assume that ordered equidistant
target pairs in two other distinct blocks exceed k times the number of targets. -/
def H2 : Prop :=
  ∃ C : ℕ, ∀ (k : ℕ) (F : Finset (Finset ℝ²)), 0 < k →
    (F : Set (Finset ℝ²)).PairwiseDisjoint id →
    (∀ T ∈ F, T.card = k ∧ ∃ a b c : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧ ∀ p ∈ T, a*p 0+b*p 1=c) →
    ((F.biUnion id).card : ℝ) ≤ Real.exp ((k : ℝ)^2) →
    (∀ G : Finset (Finset ℝ²), G.card ≤ k →
      (∀ T ∈ G, T ⊆ F.biUnion id ∧ (Collinear ℝ (T : Set ℝ²) ∨ Cospherical (T : Set ℝ²))) →
      2*(G.biUnion id).card < (F.biUnion id).card) →
    (∀ T ∈ F, ∀ p ∈ T,
      let G := F.erase T
      let B := G.biUnion id
      k*B.card < ∑ U ∈ G, ∑ x ∈ U, ((B \ U).filter fun y => dist p y = dist p x).card) →
    F.card ≤ C * (distinctDistances (F.biUnion id)+1)

section Bisectors

private theorem pin_count {α γ : Type*} [DecidableEq γ] (B : Finset α)
    (D : Finset γ) (f : α → γ) (hf : ∀ x ∈ B, f x ∈ D) :
    B.card^2 ≤ D.card * (∑ x ∈ B, ∑ y ∈ B, if f y = f x then 1 else 0) := by
  classical
  let m (r : γ) := (B.filter fun y => f y = r).card
  have hsum : B.card = ∑ r ∈ D, m r := card_eq_sum_card_fiberwise hf
  have he : (∑ r ∈ D, m r ^ 2) = ∑ x ∈ B, m (f x) := by
    rw [← sum_fiberwise_of_maps_to hf (fun x => m (f x))]
    apply sum_congr rfl
    intro r _
    calc
      m r ^ 2 = ∑ _x ∈ B.filter (fun x => f x = r), m r := by simp [m,pow_two]
      _ = _ := sum_congr rfl fun x hx => by rw [(mem_filter.mp hx).2]
  simp only [sum_boole, Nat.cast_id]
  change B.card^2 ≤ D.card * ∑ x ∈ B, m (f x)
  rw [← he, hsum]
  exact sq_sum_le_card_mul_sum_sq

/-- A bound on pins on each bisector controls the number of cross-values. -/
private theorem cross_bound {α β γ : Type*} [DecidableEq γ] (A : Finset α) (B : Finset β)
    (D : Finset γ) (f : α → β → γ) (K : ℕ)
    (hc : ∀ p ∈ A, ∀ x ∈ B, f p x ∈ D)
    (hb : ∀ x ∈ B, ∀ y ∈ B, y ≠ x → (A.filter fun p => f p y = f p x).card ≤ K) :
    A.card * B.card^2 ≤ D.card * (B.card * (A.card + (B.card-1)*K)) := by
  classical
  let c (p : α) (x y : β) : ℕ := if f p y = f p x then 1 else 0
  have hrow (x : β) (hx : x ∈ B) :
      (∑ y ∈ B, ∑ p ∈ A, c p x y) ≤ A.card + (B.card-1)*K := by
    rw [← sum_erase_add B (fun y => ∑ p ∈ A, c p x y) hx]
    have h : (∑ y ∈ B.erase x, ∑ p ∈ A, c p x y) ≤ ∑ _y ∈ B.erase x, K :=
      sum_le_sum fun y hy => by simpa [c] using hb x hx y (mem_of_mem_erase hy) (ne_of_mem_erase hy)
    simpa [c,card_erase_of_mem hx,Nat.add_comm] using Nat.add_le_add_right h A.card
  calc
    _ = ∑ _p ∈ A, B.card^2 := by simp
    _ ≤ ∑ p ∈ A, D.card * (∑ x ∈ B, ∑ y ∈ B, c p x y) :=
      sum_le_sum fun p hp => pin_count B D (f p) (hc p hp)
    _ = D.card * (∑ x ∈ B, ∑ y ∈ B, ∑ p ∈ A, c p x y) := by
      rw [← mul_sum, sum_comm (s := A) (t := B)]
      congr 1
      exact sum_congr rfl fun _ _ => sum_comm
    _ ≤ D.card * (∑ _x ∈ B, (A.card + (B.card-1)*K)) :=
      Nat.mul_le_mul_left _ (sum_le_sum hrow)
    _ = _ := by simp

private theorem self_bound {α β : Type*} [DecidableEq β] (S : Finset α)
    (D : Finset β) (f : α → α → β) (K : ℕ)
    (hm : ∀ p ∈ S, ∀ x ∈ S, f p x ∈ D)
    (hb : ∀ x ∈ S, ∀ y ∈ S, y ≠ x → (S.filter fun p => f p y = f p x).card ≤ K) :
    S.card ≤ D.card*(K+1) := by
  have hh := cross_bound S S D f K hm hb
  by_cases hn : S.card = 0
  · simp [hn]
  have hpos := Nat.pos_of_ne_zero hn
  have hsmall : S.card-1 ≤ S.card := Nat.sub_le _ _
  have hstrong : S.card*(S.card*S.card) ≤
      S.card * (S.card * (D.card * (K+1))) := by
    calc
      _ = S.card*S.card^2 := by ring
      _ ≤ _ := hh
      _ ≤ D.card*(S.card*(S.card+S.card*K)) := by gcongr
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left (Nat.le_of_mul_le_mul_left hstrong hpos) hpos


/-- H1 follows by counting pairs of targets equidistant from each pin.
The pins for each distinct pair lie on a single perpendicular bisector. -/
theorem sparse_estimate : H1 := by
  intro S K hl
  classical
  let D := insert 0 (distanceSet S)
  have hm (p) (hp : p ∈ S) (x) (hx : x ∈ S) : dist p x ∈ D := by
    by_cases he : p = x
    · simp [he,D]
    · exact mem_insert_of_mem (mem_image.mpr ⟨(p,x), mem_offDiag.mpr ⟨hp,hx,he⟩,rfl⟩)
  have hb (x) (_hx : x ∈ S) (y) (_hy : y ∈ S) (hne : y ≠ x) :
      (S.filter fun p => dist p y = dist p x).card ≤ K := by
    let a := 2*(y 0-x 0)
    let b := 2*(y 1-x 1)
    let c := y 0^2+y 1^2-(x 0^2+x 1^2)
    have hcoeff : a ≠ 0 ∨ b ≠ 0 := by
      by_contra! h
      apply hne
      ext i
      fin_cases i <;> simp_all [a,b,sub_eq_zero]
    apply le_trans (card_le_card (t := S.filter fun p => a*p 0+b*p 1=c) ?_) (hl a b c hcoeff)
    intro p hp
    obtain ⟨hp,he⟩ := mem_filter.mp hp
    refine mem_filter.mpr ⟨hp,?_⟩
    have he' := congrArg (fun r : ℝ => r^2) he
    simp only [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq, sq_abs] at he'
    dsimp [a,b,c]
    linear_combination -he'
  have hc := self_bound S D dist K hm hb
  have hD : D.card ≤ distinctDistances S+1 := card_insert_le _ _
  exact hc.trans (by rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ hD)

end Bisectors

private theorem extract_blocks (S : Finset ℝ²) (k : ℕ) (hk : 0 < k) :
    ∃ F : Finset (Finset ℝ²), (F : Set (Finset ℝ²)).PairwiseDisjoint id ∧
      (∀ T ∈ F, T.card = k ∧ ∃ a b c : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧ ∀ p ∈ T, a*p 0+b*p 1=c) ∧
      F.biUnion id ⊆ S ∧ ∀ a b c : ℝ, (a ≠ 0 ∨ b ≠ 0) →
        ((S \ F.biUnion id).filter fun p => a*p 0+b*p 1=c).card < k := by
  classical
  let blocks := S.powerset.filter fun T => T.card = k ∧
    ∃ a b c : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧ ∀ p ∈ T, a*p 0+b*p 1=c
  let families := blocks.powerset.filter fun F : Finset (Finset ℝ²) => (F : Set (Finset ℝ²)).PairwiseDisjoint id
  have hempty : ∅ ∈ families := by simp [families]
  obtain ⟨F,hF,hmax⟩ := exists_max_image families Finset.card ⟨_,hempty⟩
  obtain ⟨hblocks,hdis⟩ := mem_filter.mp hF
  have hsub := mem_powerset.mp hblocks
  refine ⟨F,hdis,fun T hT => (mem_filter.mp (hsub hT)).2,?_,?_⟩
  · intro x hx
    obtain ⟨T,hT,hx⟩ := mem_biUnion.mp hx
    exact mem_powerset.mp (mem_filter.mp (hsub hT)).1 hx
  · intro a b c hab
    by_contra! h
    obtain ⟨T,hT,hsize⟩ := exists_subset_card_eq h
    have hR : T ⊆ S \ F.biUnion id := hT.trans (filter_subset ..)
    have hblock : T ∈ blocks := mem_filter.mpr ⟨mem_powerset.mpr (hR.trans sdiff_subset),
      hsize,a,b,c,hab,fun p hp => (mem_filter.mp (hT hp)).2⟩
    have hsep (U) (hU : U ∈ F) : Disjoint T U := by
      apply disjoint_left.mpr
      intro x hx hxu
      exact (mem_sdiff.mp (hR hx)).2 (mem_biUnion.mpr ⟨U,hU,hxu⟩)
    have hfresh : T ∉ F := by
      intro hmem
      obtain ⟨x,hx⟩ := card_pos.mp (hsize ▸ hk : 0 < T.card)
      exact disjoint_left.mp (hsep T hmem) hx hx
    have hnew : insert T F ∈ families := by
      refine mem_filter.mpr ⟨mem_powerset.mpr (insert_subset hblock hsub),?_⟩
      rw [coe_insert]
      exact (Set.pairwiseDisjoint_insert_of_notMem hfresh).mpr ⟨hdis,hsep⟩
    have := hmax _ hnew
    rw [card_insert_of_notMem hfresh] at this
    omega

private theorem distances_mono {S T : Finset ℝ²} (h : S ⊆ T) :
    distinctDistances S ≤ distinctDistances T := by
  apply card_le_card
  intro r hr
  obtain ⟨⟨x,y⟩,hxy,rfl⟩ := mem_image.mp hr
  obtain ⟨hx,hy,hne⟩ := mem_offDiag.mp hxy
  exact mem_image.mpr ⟨(x,y),mem_offDiag.mpr ⟨h hx,h hy,hne⟩,rfl⟩

/-- A positive-distance fiber on a line or circle through its pin has at most two points.
The pin itself is excluded, which also handles circles of radius zero. -/
private theorem fiber_card_le_two (curve : Set ℝ²) (p : ℝ²) (hp : p ∈ curve)
    (hcurve : Collinear ℝ curve ∨ Cospherical curve)
    (s : Finset ℝ²) (r : ℝ)
    (hs : ∀ x ∈ s, x ∈ curve ∧ x ≠ p ∧ dist x p = r) : #s ≤ 2 := by
  by_contra! h
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp h
  obtain ⟨haC, hap, har⟩ := hs a ha
  obtain ⟨hbC, _, hbr⟩ := hs b hb
  obtain ⟨hcC, _, hcr⟩ := hs c hc
  rcases hcurve with hline | ⟨o, R, hcircle⟩
  · have hcos : Cospherical (s : Set ℝ²) := ⟨p, r, fun x hx => (hs x hx).2.2⟩
    have hind := hcos.affineIndependent_of_mem_of_ne ha hb hc hab hac hbc
    apply (affineIndependent_iff_not_collinear_set.mp hind)
    exact hline.subset (by simp [Set.insert_subset_iff, haC, hbC, hcC])
  · have hpo : p ≠ o := by
      rintro rfl
      have hzero : R = 0 := by simpa using (hcircle p hp).symm
      exact hap (dist_eq_zero.mp ((hcircle a haC).trans hzero))
    have hdim : Module.finrank ℝ ℝ² = 2 := finrank_euclideanSpace_fin
    rcases eq_of_dist_eq_of_dist_eq_of_finrank_eq_two hdim hpo hab
        har hbr hcr (hcircle a haC) (hcircle b hbC) (hcircle c hcC) with he | he
    · exact hac he.symm
    · exact hbc he.symm

private theorem card_on_curve (P : Finset ℝ²) (curve : Set ℝ²)
    (hcurve : Collinear ℝ curve ∨ Cospherical curve) (s : Finset ℝ²)
    (hsP : s ⊆ P) (hsC : ∀ x ∈ s, x ∈ curve) :
    #s ≤ 2 * distinctDistances P + 1 := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | ⟨p, hp⟩
  · simp
  have hmap : ∀ x ∈ s.erase p, dist x p ∈ distanceSet P := by
    intro x hx
    exact Finset.mem_image.mpr ⟨(x, p), Finset.mem_offDiag.mpr
      ⟨hsP (mem_of_mem_erase hx), hsP hp, ne_of_mem_erase hx⟩, rfl⟩
  have h := Finset.card_le_mul_card_image_of_maps_to hmap 2 (by
    intro r _
    apply fiber_card_le_two curve p (hsC p hp) hcurve _ r
    intro x hx
    obtain ⟨hx, hr⟩ := mem_filter.mp hx
    exact ⟨hsC x (mem_of_mem_erase hx), ne_of_mem_erase hx, hr⟩)
  change #(s.erase p) ≤ 2 * distinctDistances P at h
  rw [← card_erase_add_one hp]
  exact Nat.add_le_add_right h 1

/-- Count blocks when at most k collinear or cospherical pieces contain half
the points. Their distance values are measured in the entire union. -/
private theorem curve_packing (k : ℕ) (hk : 0 < k) (F G : Finset (Finset ℝ²))
    (hdis : (F : Set (Finset ℝ²)).PairwiseDisjoint id)
    (hsize : ∀ T ∈ F, T.card = k) (hg : G.card ≤ k)
    (hpieces : ∀ T ∈ G, T ⊆ F.biUnion id ∧
      (Collinear ℝ (T : Set ℝ²) ∨ Cospherical (T : Set ℝ²)))
    (hhalf : (F.biUnion id).card ≤ 2*(G.biUnion id).card) :
    F.card ≤ 4*distinctDistances (F.biUnion id)+2 := by
  classical
  let S := F.biUnion id
  let D := distinctDistances S
  have hcov : (G.biUnion id).card ≤ k*(2*D+1) := calc
    _ ≤ ∑ T ∈ G, T.card := card_biUnion_le
    _ ≤ ∑ _T ∈ G, (2*D+1) := by
      apply sum_le_sum
      intro T hT
      obtain ⟨hsub,hcurve⟩ := hpieces T hT
      exact card_on_curve S (T : Set ℝ²) hcurve T hsub (fun _ hx => hx)
    _ ≤ _ := by simpa using Nat.mul_le_mul_right (2*D+1) hg
  have hs : S.card = F.card*k := by
    dsimp [S]; rw [card_biUnion hdis]
    calc
      _ = ∑ _T ∈ F, k := sum_congr rfl fun T hT => hsize T hT
      _ = _ := by simp
  change F.card ≤ 4*D+2
  apply Nat.le_of_mul_le_mul_right _ hk
  calc
    _ = S.card := hs.symm
    _ ≤ 2*(G.biUnion id).card := hhalf
    _ ≤ 2*(k*(2*D+1)) := Nat.mul_le_mul_left _ hcov
    _ = _ := by ring

/-- One pin with few ordered equidistant target pairs across different blocks
bounds the number of blocks, independently of their locations. -/
private theorem cross_pin_packing (k : ℕ) (hk : 0 < k) (F : Finset (Finset ℝ²))
    (hdis : (F : Set (Finset ℝ²)).PairwiseDisjoint id) (hsize : ∀ T ∈ F, T.card = k)
    (T : Finset ℝ²) (hT : T ∈ F) (p : ℝ²) (hp : p ∈ T) :
    let G := F.erase T
    let B := G.biUnion id
    (∑ U ∈ G, ∑ x ∈ U, ((B \ U).filter fun y => dist p y = dist p x).card) ≤ k*B.card →
    F.card ≤ 2*distinctDistances (F.biUnion id)+1 := by
  classical
  intro G B hlow
  let S := F.biUnion id
  let D := distanceSet S
  have hG : (G : Set (Finset ℝ²)).PairwiseDisjoint id :=
    hdis.subset (by exact_mod_cast erase_subset T F)
  have hcard : B.card = G.card*k := by
    dsimp [B]; rw [card_biUnion hG]
    calc
      _ = ∑ _U ∈ G, k := sum_congr rfl fun U hU => hsize U (mem_of_mem_erase hU)
      _ = _ := by simp
  have hmap (x) (hx : x ∈ B) : dist p x ∈ D := by
    obtain ⟨U,hU,hxU⟩ := mem_biUnion.mp hx
    have hUT := mem_erase.mp hU
    have hne : p ≠ x := fun he => (Finset.disjoint_left.mp
      (hdis hUT.2 hT hUT.1) hxU) (he ▸ hp)
    exact mem_image.mpr ⟨(p,x),mem_offDiag.mpr ⟨mem_biUnion.mpr ⟨T,hT,hp⟩,
      mem_biUnion.mpr ⟨U,hUT.2,hxU⟩,hne⟩,rfl⟩
  let same := fun x y : ℝ² => dist p y = dist p x
  have row (U) (hU : U ∈ G) (x : ℝ²) :
      (B.filter (same x)).card ≤ k+((B \ U).filter (same x)).card := by
    have hs : B.filter (same x) ⊆ U ∪ ((B \ U).filter (same x)) := by
      intro y hy
      obtain ⟨hy,he⟩ := mem_filter.mp hy
      by_cases h : y ∈ U
      · exact mem_union_left _ h
      · exact mem_union_right _ (mem_filter.mpr ⟨mem_sdiff.mpr ⟨hy,h⟩,he⟩)
    exact (card_le_card hs).trans ((card_union_le _ _).trans_eq (by rw [hsize U (mem_of_mem_erase hU)]))
  have energy : (∑ x ∈ B, (B.filter (same x)).card) ≤ 2*k*B.card := by
    rw [show B = G.biUnion id from rfl, sum_biUnion hG]
    calc
      _ ≤ ∑ U ∈ G, ∑ x ∈ U, (k+((B \ U).filter (same x)).card) :=
        sum_le_sum fun U hU => sum_le_sum fun x _ => row U hU x
      _ = B.card*k + ∑ U ∈ G, ∑ x ∈ U, ((B \ U).filter (same x)).card := by
        simp only [sum_add_distrib]
        congr 1
        simpa [B] using (sum_biUnion hG (f := fun _ : ℝ² => k)).symm
      _ ≤ B.card*k + k*B.card := Nat.add_le_add_left hlow _
      _ = _ := by ring
  have hc := pin_count B D (dist p) hmap
  simp only [sum_boole, Nat.cast_id] at hc
  change B.card^2 ≤ D.card * (∑ x ∈ B, (B.filter (same x)).card) at hc
  have hblocks : G.card ≤ 2*D.card := by
    by_cases hb : B.card = 0
    · have hz := hcard.symm.trans hb
      exact ((mul_eq_zero.mp hz).resolve_right hk.ne').le.trans (Nat.zero_le _)
    have he : B.card*B.card ≤ (2*k*D.card)*B.card := by
      calc
        _ = B.card^2 := by ring
        _ ≤ _ := hc.trans (Nat.mul_le_mul_left _ energy)
        _ = _ := by ring
    have h := Nat.le_of_mul_le_mul_right he (Nat.pos_of_ne_zero hb)
    rw [hcard, Nat.mul_right_comm 2 k] at h
    exact Nat.le_of_mul_le_mul_right h hk
  have hF : G.card+1 = F.card := card_erase_add_one hT
  change F.card ≤ 2*D.card+1
  omega

/-- The remaining packing case implies the unrestricted block estimate. -/
private theorem packing_from_curves (packing : H2) :
  ∃ C : ℕ, ∀ (k : ℕ) (F : Finset (Finset ℝ²)), 0 < k →
    (F : Set (Finset ℝ²)).PairwiseDisjoint id →
    (∀ T ∈ F, T.card = k ∧ ∃ a b c : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧ ∀ p ∈ T, a*p 0+b*p 1=c) →
    ((F.biUnion id).card : ℝ) ≤ Real.exp ((k : ℝ)^2) →
    F.card ≤ C * (distinctDistances (F.biUnion id)+1) := by
  classical
  obtain ⟨C,pack⟩ := packing
  refine ⟨max C 4,?_⟩
  intro k F hk hdis hline hcap
  by_cases spread : (∀ G : Finset (Finset ℝ²), G.card ≤ k →
      (∀ T ∈ G, T ⊆ F.biUnion id ∧ (Collinear ℝ (T : Set ℝ²) ∨ Cospherical (T : Set ℝ²))) →
      2*(G.biUnion id).card < (F.biUnion id).card)
  · by_cases many : (∀ T ∈ F, ∀ p ∈ T,
      let G := F.erase T
      let B := G.biUnion id
      k*B.card < ∑ U ∈ G, ∑ x ∈ U, ((B \ U).filter fun y => dist p y = dist p x).card)
    · exact (pack k F hk hdis hline hcap spread many).trans
        (Nat.mul_le_mul_right _ (le_max_left C 4))
    push Not at many
    obtain ⟨T,hT,p,hp,hlow⟩ := many
    have h := cross_pin_packing k hk F hdis (fun U hU => (hline U hU).1) T hT p hp
    have hh := h (by simpa using hlow)
    exact hh.trans ((by omega : 2*distinctDistances (F.biUnion id)+1 ≤
      4*(distinctDistances (F.biUnion id)+1)).trans (Nat.mul_le_mul_right _ (le_max_right C 4)))
  push Not at spread
  obtain ⟨G,hg,hpieces,hhalf⟩ := spread
  have h := curve_packing k hk F G hdis (fun T hT => (hline T hT).1) hg hpieces hhalf
  exact h.trans ((by omega : 4*distinctDistances (F.biUnion id)+2 ≤
    4*(distinctDistances (F.biUnion id)+1)).trans (Nat.mul_le_mul_right _ (le_max_right C 4)))

private theorem finite_bound (sparse : H1) (packing : H2) :
    ∃ C : ℕ, ∀ (S : Finset ℝ²) (k : ℕ), 0 < k → (S.card : ℝ) ≤ Real.exp ((k : ℝ)^2) →
      S.card ≤ k*(C+1)*(distinctDistances S+1) := by
  classical
  obtain ⟨C,pack⟩ := packing_from_curves packing
  refine ⟨C,?_⟩
  intro S k hk hsize
  obtain ⟨F,hdis,hline,hsub,hres⟩ := extract_blocks S k hk
  let U := F.biUnion id
  have hu : U.card = F.card*k := by
    rw [show U=F.biUnion id from rfl,card_biUnion hdis]
    calc
      _ = ∑ _T ∈ F, k := sum_congr rfl fun T hT => (hline T hT).1
      _ = _ := by simp
  have hpack := pack k F hk hdis hline ((by exact_mod_cast card_le_card hsub : (U.card:ℝ) ≤ S.card).trans hsize)
  have hp : F.card ≤ C*(distinctDistances S+1) :=
    hpack.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right (distances_mono hsub) 1))
  have hr := sparse (S \ U) (k-1) (fun a b c h => by dsimp only [U]; have := hres a b c h; omega)
  rw [Nat.sub_add_cancel hk] at hr
  have hleft := hr.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right (distances_mono sdiff_subset) 1))
  calc
    S.card = (S \ U).card + U.card := (card_sdiff_add_card_eq_card hsub).symm
    _ ≤ k*(distinctDistances S+1) + (C*(distinctDistances S+1))*k := by
      rw [hu]; exact Nat.add_le_add hleft (Nat.mul_le_mul_right _ hp)
    _ = _ := by ring

theorem main : H1 → H2 → type_of% @Erdos89.erdos_89 := by
  classical
  intro sparse packing
  obtain ⟨C,hfinite⟩ := finite_bound sparse packing
  apply Asymptotics.IsBigO.of_bound (4*((C:ℝ)+1))
  filter_upwards [eventually_ge_atTop (⌈Real.exp 1⌉₊+2)] with n hn
  have hn2 : 2 ≤ n := by omega
  have hnpos : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hexp : Real.exp 1 ≤ (n:ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (by omega : ⌈Real.exp 1⌉₊ ≤ n))
  have hlog : 1 ≤ Real.log (n:ℝ) := by simpa using Real.log_le_log (Real.exp_pos _) hexp
  let z := Real.sqrt (Real.log n)
  have hz : 1 ≤ z := by simpa [z] using Real.sqrt_le_sqrt hlog
  let k := ⌈z⌉₊
  have hceil : z ≤ (k:ℝ) := Nat.le_ceil _
  have hk : 0 < k := by exact_mod_cast (zero_lt_one.trans_le (hz.trans hceil))
  have hround : (k:ℝ) ≤ 2*z := by
    have h := Nat.ceil_lt_add_one (zero_le_one.trans hz)
    dsimp [k]; linarith
  have hcap : (n:ℝ) ≤ Real.exp ((k:ℝ)^2) := by
    rw [← Real.exp_log hnpos]
    apply Real.exp_le_exp.mpr
    have he : z^2 = Real.log n := Real.sq_sqrt (zero_le_one.trans hlog)
    nlinarith [mul_nonneg (sub_nonneg.mpr hceil) (by positivity : 0 ≤ (k:ℝ)+z)]
  obtain ⟨S₀,h₀⟩ := Infinite.exists_subset_card_eq ℝ² n
  obtain ⟨S,hS,hD⟩ := Nat.sInf_mem (show
    {d : ℕ | ∃ S : Finset ℝ², S.card=n ∧ distinctDistances S=d}.Nonempty from ⟨_,S₀,h₀,rfl⟩)
  change distinctDistances S = minimalDistinctDistances ℝ² n at hD
  have hfb := hfinite S k hk (hS ▸ hcap)
  have hd : 0 < distinctDistances S := by
    obtain ⟨x,hx,y,hy,hxy⟩ := one_lt_card.mp (by omega : 1 < S.card)
    exact card_pos.mpr ⟨_,mem_image.mpr ⟨(x,y),mem_offDiag.mpr ⟨hx,hy,hxy⟩,rfl⟩⟩
  let D : ℝ := distinctDistances S
  have hd' : (1:ℝ) ≤ D := by dsimp [D]; exact_mod_cast (show 1 ≤ distinctDistances S from hd)
  rw [hS] at hfb
  have hh : (n:ℝ) ≤ (k:ℝ)*((C:ℝ)+1)*(D+1) := by dsimp [D]; exact_mod_cast hfb
  change ‖(n:ℝ)/z‖ ≤ 4*((C:ℝ)+1)*‖(minimalDistinctDistances ℝ² n : ℝ)‖
  rw [← hD,Real.norm_eq_abs,abs_of_nonneg (by positivity),Real.norm_eq_abs,Nat.abs_cast,
    div_le_iff₀ (zero_lt_one.trans_le hz)]
  change (n:ℝ) ≤ 4*((C:ℝ)+1)*D*z
  calc
    _ ≤ _ := hh
    _ ≤ (2*z)*((C:ℝ)+1)*(2*D) := by gcongr; linarith
    _ = _ := by ring

end OMA.R_Erdos89_erdos_89_R2
