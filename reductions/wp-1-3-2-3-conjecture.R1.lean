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

-- Repeatedly split at an ordinal cut and retain a nonchain factor.
-- Concatenating extensions gives every extension of the factor the same
-- number of completions. The resulting equality concerns all internal pairs.
def H2 : Prop :=
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
      ∀ x y : S, prob S x y = prob P x.val y.val

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

lemma transfer_bounds {p q : ℚ} (h : p = q) (bounds : 1 / 3 ≤ p ∧ p ≤ 2 / 3) :
    1 / 3 ≤ q ∧ q ≤ 2 / 3 := h ▸ bounds

theorem main : H1 → H2 → type_of% @OMA.S_wp_1_3_2_3_conjecture.main := by
  classical
  intro core selectBlock P _ _ nonchain
  let e : Shrink.{0} P ≃o P := (orderIsoShrink.{0} P).symm
  have hn : ¬ ∀ x y : Shrink.{0} P, x ≤ y ∨ y ≤ x := by
    intro total
    apply nonchain
    intro a b
    simpa only [e.symm.le_iff_le] using total (e.symm a) (e.symm b)
  obtain ⟨S, hS, hcut, hprob⟩ := selectBlock (Shrink.{0} P) hn
  obtain ⟨x, y, hxy, hbounds⟩ := core S hS hcut
  have eqProb := (hprob x y).trans (count_transport e x.val y.val)
  exact ⟨e x.val, e y.val, fun h => hxy (Subtype.ext (e.injective h)),
    transfer_bounds eqProb hbounds⟩

end OMA.R_wp_1_3_2_3_conjecture_R1
