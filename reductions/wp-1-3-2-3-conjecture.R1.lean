import OMAStatements.S_wp_1_3_2_3_conjecture

-- Credit: @wispiANt
namespace OMA.R_wp_1_3_2_3_conjecture_R1

-- A proper ordinal cut has two nonempty sides, with the whole lower side
-- strictly below the upper side. Restrict the conjecture to orders without one.
def H1 : Prop := ∀ (P : Type) [PartialOrder P] [Fintype P],
    (¬ ∀ x y : P, x ≤ y ∨ y ≤ x) →
    (¬ ∃ L : Set P, L.Nonempty ∧ (∃ y, y ∉ L) ∧
      ∀ x ∈ L, ∀ y ∉ L, x < y) →
    let ext : Finset (P ≃ Fin (Fintype.card P)) := by
      classical
      exact Finset.univ.filter (fun rank => StrictMono rank)
    ∃ x y : P, x ≠ y ∧
      let p := ((ext.filter (fun r => r x < r y)).card : ℚ) / ext.card
      1 / 3 ≤ p ∧ p ≤ 2 / 3

-- A single cut preserves the probability of every comparison inside either side.
def H2 : Prop :=
  let prob (Q : Type) [PartialOrder Q] [Fintype Q] (x y : Q) : ℚ :=
    let ext : Finset (Q ≃ Fin (Fintype.card Q)) := by
      classical
      exact Finset.univ.filter (fun rank => StrictMono rank)
    ((ext.filter (fun rank => rank x < rank y)).card : ℚ) / ext.card
  ∀ (P : Type) [PartialOrder P] (S T : Finset P) (sub : T ⊂ S),
    ((∀ x ∈ T, ∀ y ∈ S, y ∉ T → x < y) ∨
     (∀ x ∈ T, ∀ y ∈ S, y ∉ T → y < x)) →
    ∀ x y : T, prob T x y =
      prob S ⟨x.val, sub.1 x.property⟩ ⟨y.val, sub.1 y.property⟩

-- Transport both extension counts along an order isomorphism. This lets
-- the two steps use small finite types even when the input lives higher.
lemma count_transport {A : Type*} {B : Type*} [PartialOrder A] [PartialOrder B]
    [Fintype A] [Fintype B] (e : A ≃o B) (x y : A) :
    let ea : Finset (A ≃ Fin (Fintype.card A)) := by
      classical
      exact Finset.univ.filter (fun r => StrictMono r)
    let eb : Finset (B ≃ Fin (Fintype.card B)) := by
      classical
      exact Finset.univ.filter (fun r => StrictMono r)
    ((ea.filter (fun r => r x < r y)).card : ℚ) / ea.card =
      ((eb.filter (fun r => r (e x) < r (e y))).card : ℚ) / eb.card := by
  classical
  intro ea eb
  let castRank := Fin.castOrderIso (Fintype.card_congr e.toEquiv)
  let transport := e.toEquiv.equivCongr castRank.toEquiv
  have evalRank (r : A ≃ Fin (Fintype.card A)) (b : B) :
      transport r b = castRank (r (e.symm b)) := rfl
  have mem (r : A ≃ Fin (Fintype.card A)) : r ∈ ea ↔ transport r ∈ eb := by
    simp only [ea, eb, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h a b hab
      rw [evalRank, evalRank]
      exact castRank.strictMono (h (e.symm.strictMono hab))
    · intro h a b hab
      have hlt := h (e.strictMono hab)
      simpa only [evalRank, e.symm_apply_apply, castRank.lt_iff_lt] using hlt
  have pair := Finset.card_equiv (s := ea.filter (fun r => r x < r y))
      (t := eb.filter (fun r => r (e x) < r (e y))) transport (by
        intro r
        simp only [Finset.mem_filter, ← mem, evalRank, e.symm_apply_apply, castRank.lt_iff_lt])
  rw [pair, Finset.card_equiv transport mem]

-- Keep an incomparable pair together while taking a strictly smaller side.
lemma retain_pair {P : Type} [PartialOrder P] (S : Finset P) (a b : S)
    (hab : ¬ a ≤ b) (hba : ¬ b ≤ a) (L : Set S)
    (lo : L.Nonempty) (hi : ∃ y, y ∉ L) (cut : ∀ x ∈ L, ∀ y ∉ L, x < y) :
    ∃ T : Finset P, T ⊂ S ∧ a.val ∈ T ∧ b.val ∈ T ∧
      ((∀ x ∈ T, ∀ y ∈ S, y ∉ T → x < y) ∨
       (∀ x ∈ T, ∀ y ∈ S, y ∉ T → y < x)) := by
  classical
  have takeSide (D : Set S) (ha : a ∈ D) (hb : b ∈ D) (proper : ∃ z, z ∉ D)
      (side : (∀ x ∈ D, ∀ y ∉ D, x < y) ∨ (∀ x ∈ D, ∀ y ∉ D, y < x)) :
      ∃ T : Finset P, T ⊂ S ∧ a.val ∈ T ∧ b.val ∈ T ∧
        ((∀ x ∈ T, ∀ y ∈ S, y ∉ T → x < y) ∨
         (∀ x ∈ T, ∀ y ∈ S, y ∉ T → y < x)) := by
    let T := S.filter (fun x => ∃ h : x ∈ S, (⟨x, h⟩ : S) ∈ D)
    have incl : T ⊆ S := Finset.filter_subset _ _
    have mem (x : S) : x.val ∈ T ↔ x ∈ D := by simp [T, x.property]
    obtain ⟨z, hz⟩ := proper
    refine ⟨T, (Finset.ssubset_iff_of_subset incl).2 ⟨z.val, z.property, fun h => hz ((mem z).1 h)⟩,
      (mem a).2 ha, (mem b).2 hb, ?_⟩
    rcases side with h | h
    · left
      intro x hx y hy outside
      exact h ⟨x, incl hx⟩ ((mem _).1 hx) ⟨y, hy⟩ (fun h => outside ((mem _).2 h))
    · right
      intro x hx y hy outside
      exact h ⟨x, incl hx⟩ ((mem _).1 hx) ⟨y, hy⟩ (fun h => outside ((mem _).2 h))
  by_cases ha : a ∈ L
  · apply takeSide L ha _ hi (Or.inl cut)
    by_contra hb
    exact hab (cut a ha b hb).le
  · apply takeSide Lᶜ ha
    · intro hb
      exact hba (cut b hb a ha).le
    · obtain ⟨z, hz⟩ := lo
      exact ⟨z, fun h => h hz⟩
    · right
      intro x hx y hy
      exact cut y (by simpa using hy) x hx

lemma select_block (oneCut : H2) :
  let prob (Q : Type) [PartialOrder Q] [Fintype Q] (x y : Q) : ℚ :=
    let ext : Finset (Q ≃ Fin (Fintype.card Q)) := by
      classical
      exact Finset.univ.filter (fun rank => StrictMono rank)
    ((ext.filter (fun rank => rank x < rank y)).card : ℚ) / ext.card
  ∀ (P : Type) [PartialOrder P] [Fintype P],
    (¬ ∀ x y : P, x ≤ y ∨ y ≤ x) →
    ∃ S : Finset P,
      (¬ ∀ x y : S, x ≤ y ∨ y ≤ x) ∧
      (¬ ∃ L : Set S, L.Nonempty ∧ (∃ y, y ∉ L) ∧
        ∀ x ∈ L, ∀ y ∉ L, x < y) ∧
      ∀ x y : S, prob S x y = prob P x.val y.val := by
  classical
  intro prob P _ _ nonchain
  obtain ⟨a, b, hab, hba⟩ : ∃ a b : P, ¬ a ≤ b ∧ ¬ b ≤ a := by
    by_contra! h
    exact nonchain (fun a b => or_iff_not_imp_left.mpr (h a b))
  let preservesProb (S : Finset P) := ∀ x y : S, prob S x y = prob P x.val y.val
  have descend (S : Finset P) (ha : a ∈ S) (hb : b ∈ S) (hg : preservesProb S) :
      ∃ T : Finset P, (¬ ∀ x y : T, x ≤ y ∨ y ≤ x) ∧
        (¬ ∃ L : Set T, L.Nonempty ∧ (∃ y, y ∉ L) ∧ ∀ x ∈ L, ∀ y ∉ L, x < y) ∧ preservesProb T := by
    induction S using Finset.strongInductionOn with
    | _ S ih =>
      by_cases split : ∃ L : Set S, L.Nonempty ∧ (∃ y, y ∉ L) ∧ ∀ x ∈ L, ∀ y ∉ L, x < y
      · obtain ⟨L, lo, hi, cut⟩ := split
        obtain ⟨T, sub, haT, hbT, side⟩ := retain_pair S ⟨a, ha⟩ ⟨b, hb⟩ hab hba L lo hi cut
        apply ih T sub haT hbT
        intro x y
        exact (oneCut P S T sub side x y).trans (hg _ _)
      · exact ⟨S, fun total => (total ⟨a, ha⟩ ⟨b, hb⟩).elim hab hba, split, hg⟩
  let e : (Finset.univ : Finset P) ≃o P :=
    { toFun := Subtype.val
      invFun := fun x => ⟨x, Finset.mem_univ x⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  exact descend Finset.univ (Finset.mem_univ _) (Finset.mem_univ _)
    (fun x y => count_transport e x y)

lemma transfer_bounds {p q : ℚ} (h : p = q) (bounds : 1 / 3 ≤ p ∧ p ≤ 2 / 3) :
    1 / 3 ≤ q ∧ q ≤ 2 / 3 := h ▸ bounds

theorem main : H1 → H2 → type_of% @OMA.S_wp_1_3_2_3_conjecture.main := by
  classical
  intro core oneCut P _ _ nonchain
  let e : Shrink.{0} P ≃o P := (orderIsoShrink.{0} P).symm
  have hn : ¬ ∀ x y : Shrink.{0} P, x ≤ y ∨ y ≤ x := by
    intro total
    apply nonchain
    intro a b
    simpa only [e.symm.le_iff_le] using total (e.symm a) (e.symm b)
  obtain ⟨S, hS, hcut, hprob⟩ := select_block oneCut (Shrink.{0} P) hn
  obtain ⟨x, y, hxy, hbounds⟩ := core S hS hcut
  have eqProb := (hprob x y).trans (count_transport e x.val y.val)
  exact ⟨e x.val, e y.val, fun h => hxy (Subtype.ext (e.injective h)),
    transfer_bounds eqProb hbounds⟩

end OMA.R_wp_1_3_2_3_conjecture_R1
