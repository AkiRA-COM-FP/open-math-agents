import OMAStatements.S_wp_1_3_2_3_conjecture

-- Credit: @wispiANt
namespace OMA.R_wp_1_3_2_3_conjecture_R1

-- For ordinal-sum indecomposable nonchains, separate Linial's width-two
-- case from the case with a three-element antichain.
def H1 : Prop := ∀ (P : Type) [PartialOrder P] [Fintype P],
    (¬ ∀ x y : P, x ≤ y ∨ y ≤ x) →
    (¬ ∃ L : Set P, L.Nonempty ∧ (∃ y, y ∉ L) ∧
      ∀ x ∈ L, ∀ y ∉ L, x < y) →
    (∀ a b c : P, a ≤ b ∨ b ≤ a ∨ a ≤ c ∨ c ≤ a ∨ b ≤ c ∨ c ≤ b) →
    let ext : Finset (P ≃ Fin (Fintype.card P)) := by
      classical
      exact Finset.univ.filter (fun rank => StrictMono rank)
    ∃ x y : P, x ≠ y ∧
      let p := ((ext.filter (fun r => r x < r y)).card : ℚ) / ext.card
      1 / 3 ≤ p ∧ p ≤ 2 / 3

def H2 : Prop := ∀ (P : Type) [PartialOrder P] [Fintype P],
    (¬ ∀ x y : P, x ≤ y ∨ y ≤ x) →
    (¬ ∃ L : Set P, L.Nonempty ∧ (∃ y, y ∉ L) ∧
      ∀ x ∈ L, ∀ y ∉ L, x < y) →
    (∃ a b c : P, (¬ a ≤ b ∧ ¬ b ≤ a) ∧ (¬ a ≤ c ∧ ¬ c ≤ a) ∧ (¬ b ≤ c ∧ ¬ c ≤ b)) →
    let ext : Finset (P ≃ Fin (Fintype.card P)) := by
      classical
      exact Finset.univ.filter (fun rank => StrictMono rank)
    ∃ x y : P, x ≠ y ∧
      let p := ((ext.filter (fun r => r x < r y)).card : ℚ) / ext.card
      1 / 3 ≤ p ∧ p ≤ 2 / 3

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

-- The rank-interval counting argument also appears in Samuel Schlesinger's
-- OneThirdTwoThirds/OrdinalSum.lean. Here the ranks are equivalences and
-- the partition is an arbitrary pair of factors of the ambient order.
-- Every rank in the lower factor is smaller than every rank in the upper
-- factor. Counting the ranks on either side pins down the boundary.
lemma factor_ranks {A B W : Type} [Fintype A] [Fintype B] [Fintype W]
    (parts : A ⊕ B ≃ W) (r : W ≃ Fin (Fintype.card W))
    (cross : ∀ a b, r (parts (.inl a)) < r (parts (.inr b))) :
    (∀ a, (r (parts (.inl a))).val < Fintype.card A) ∧
    (∀ b, Fintype.card A ≤ (r (parts (.inr b))).val) := by
  classical
  have size : Fintype.card W = Fintype.card A + Fintype.card B :=
    (Fintype.card_congr parts).symm.trans Fintype.card_sum
  constructor
  · intro a
    let v := r (parts (.inl a))
    let above (b : B) : Finset.Ioi v := ⟨r (parts (.inr b)), Finset.mem_Ioi.mpr (cross a b)⟩
    have inj : Function.Injective above := fun _ _ h =>
      Sum.inr_injective (parts.injective (r.injective (congrArg Subtype.val h)))
    have h := Fintype.card_le_of_injective above inj
    rw [Fintype.card_coe, Fin.card_Ioi] at h
    change v.val < Fintype.card A
    have := v.isLt
    omega
  · intro b
    let v := r (parts (.inr b))
    let below (a : A) : Finset.Iio v := ⟨r (parts (.inl a)), Finset.mem_Iio.mpr (cross a b)⟩
    have inj : Function.Injective below := fun _ _ h =>
      Sum.inl_injective (parts.injective (r.injective (congrArg Subtype.val h)))
    simpa only [Fintype.card_coe, Fin.card_Iio] using Fintype.card_le_of_injective below inj

lemma factor_extensions {A B W : Type} [PartialOrder A] [PartialOrder B] [PartialOrder W]
    [Fintype A] [Fintype B] [Fintype W] (parts : A ⊕ B ≃ W)
    (leftOrder : ∀ a a', parts (.inl a) < parts (.inl a') ↔ a < a')
    (rightOrder : ∀ b b', parts (.inr b) < parts (.inr b') ↔ b < b')
    (cross : ∀ a b, parts (.inl a) < parts (.inr b)) :
    let E (Q : Type) [PartialOrder Q] [Fintype Q] :=
      {r : Q ≃ Fin (Fintype.card Q) // StrictMono r}
    ∃ join : E A × E B ≃ E W, ∀ p,
      (∀ a, ((join p).val (parts (.inl a))).val = (p.1.val a).val) ∧
      (∀ b, ((join p).val (parts (.inr b))).val = Fintype.card A + (p.2.val b).val) := by
  classical
  intro E
  have size : Fintype.card A + Fintype.card B = Fintype.card W :=
    Fintype.card_sum.symm.trans (Fintype.card_congr parts)
  let concat (p : E A × E B) : W ≃ Fin (Fintype.card W) :=
    parts.symm.trans ((p.1.val.sumCongr p.2.val).trans (finSumFinEquiv.trans (finCongr size)))
  have leftVal (p : E A × E B) (a : A) :
      ((concat p) (parts (.inl a))).val = (p.1.val a).val := by
    simp [concat]
  have rightVal (p : E A × E B) (b : B) :
      ((concat p) (parts (.inr b))).val = Fintype.card A + (p.2.val b).val := by
    simp [concat]
  have mono (p : E A × E B) : StrictMono (concat p) := by
    intro x y h
    obtain ⟨a | b, rfl⟩ := parts.surjective x
    · obtain ⟨c | d, rfl⟩ := parts.surjective y
      · rw [Fin.lt_def, leftVal, leftVal]
        exact p.1.property ((leftOrder a c).1 h)
      · rw [Fin.lt_def, leftVal, rightVal]
        have := (p.1.val a).isLt
        omega
    · obtain ⟨c | d, rfl⟩ := parts.surjective y
      · exact ((cross c b).not_gt h).elim
      · rw [Fin.lt_def, rightVal, rightVal]
        exact Nat.add_lt_add_left (p.2.property ((rightOrder b d).1 h)) _
  let combine (p : E A × E B) : E W := ⟨concat p, mono p⟩
  have injective : Function.Injective combine := by
    intro p q h
    have valEq (w : W) := congrArg (fun z : E W => (z.val w).val) h
    apply Prod.ext
    · apply Subtype.ext
      apply Equiv.ext
      intro a
      apply Fin.ext
      exact (leftVal p a).symm.trans ((valEq (parts (.inl a))).trans (leftVal q a))
    · apply Subtype.ext
      apply Equiv.ext
      intro b
      apply Fin.ext
      apply Nat.add_left_cancel (n := Fintype.card A)
      exact (rightVal p b).symm.trans ((valEq (parts (.inr b))).trans (rightVal q b))
  have surjective : Function.Surjective combine := by
    rintro ⟨r, hr⟩
    obtain ⟨bottom, top⟩ := factor_ranks parts r (fun a b => hr (cross a b))
    let l (a : A) : Fin (Fintype.card A) := ⟨(r (parts (.inl a))).val, bottom a⟩
    let u (b : B) : Fin (Fintype.card B) :=
      ⟨(r (parts (.inr b))).val - Fintype.card A, by
        have := (r (parts (.inr b))).isLt
        have := top b
        omega⟩
    have li : Function.Injective l := by
      intro a a' h
      exact Sum.inl_injective (parts.injective (r.injective (Fin.ext (congrArg (fun z : Fin (Fintype.card A) => z.val) h))))
    have ui : Function.Injective u := by
      intro b b' h
      apply Sum.inr_injective
      apply parts.injective
      apply r.injective
      apply Fin.ext
      have hv := congrArg Fin.val h
      dsimp [u] at hv
      have := top b
      have := top b'
      omega
    let g := Equiv.ofBijective l ((Fintype.bijective_iff_injective_and_card l).2
      ⟨li, (Fintype.card_fin _).symm⟩)
    let k := Equiv.ofBijective u ((Fintype.bijective_iff_injective_and_card u).2
      ⟨ui, (Fintype.card_fin _).symm⟩)
    have gm : StrictMono g := fun {_ _} h => hr ((leftOrder _ _).2 h)
    have km : StrictMono k := by
      intro b b' h
      have lt := Fin.lt_def.mp (hr ((rightOrder _ _).2 h))
      change (r (parts (.inr b))).val - _ < (r (parts (.inr b'))).val - _
      have := top b
      omega
    let p : E A × E B := (⟨g, gm⟩, ⟨k, km⟩)
    refine ⟨p, Subtype.ext (Equiv.ext fun w => Fin.ext ?_)⟩
    obtain ⟨a | b, rfl⟩ := parts.surjective w
    · exact leftVal p a
    · rw [show ((combine p).val (parts (.inr b))).val = _ from rightVal p b]
      change Fintype.card A + ((r (parts (.inr b))).val - Fintype.card A) = (r (parts (.inr b))).val
      have := top b
      omega
  exact ⟨Equiv.ofBijective combine ⟨injective, surjective⟩, fun p => ⟨leftVal p, rightVal p⟩⟩

lemma rank_exists (Q : Type) [PartialOrder Q] [Fintype Q] :
    Nonempty {r : Q ≃ Fin (Fintype.card Q) // StrictMono r} := by
  classical
  let : Fintype (LinearExtension Q) := inferInstanceAs (Fintype Q)
  let sort := (Fintype.orderIsoFinOfCardEq (LinearExtension Q)
    (show Fintype.card (LinearExtension Q) = Fintype.card Q from rfl)).symm
  let r : Q ≃ Fin (Fintype.card Q) := (Equiv.refl Q).trans sort.toEquiv
  have strict : StrictMono (toLinearExtension : Q → LinearExtension Q) :=
    toLinearExtension.monotone.strictMono_of_injective (fun _ _ h => h)
  exact ⟨⟨r, sort.strictMono.comp strict⟩⟩

-- Counting a predicate depending only on the first coordinate multiplies
-- its numerator and denominator by the size of the second coordinate.
lemma uniform_factor {A B W : Type} [Fintype A] [Fintype B] [Fintype W] [Nonempty B]
    (join : A × B ≃ W) (localEvent : A → Prop) (wholeEvent : W → Prop)
    [DecidablePred localEvent] [DecidablePred wholeEvent]
    (event : ∀ p, localEvent p.1 ↔ wholeEvent (join p)) :
    ((Finset.univ.filter localEvent).card : ℚ) / Fintype.card A =
      ((Finset.univ.filter wholeEvent).card : ℚ) / Fintype.card W := by
  classical
  have num := Finset.card_equiv
    (s := (Finset.univ.filter localEvent) ×ˢ (Finset.univ : Finset B))
    (t := Finset.univ.filter wholeEvent) join (by
      intro p
      simpa only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
        using event p)
  rw [Finset.card_product, Finset.card_univ] at num
  have den := Fintype.card_congr join
  rw [Fintype.card_prod] at den
  rw [← num, ← den, Nat.cast_mul, Nat.cast_mul]
  exact (mul_div_mul_right _ _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)).symm

lemma rank_event (Q : Type) [PartialOrder Q] [Fintype Q] (x y : Q) :
    let E := {r : Q ≃ Fin (Fintype.card Q) // StrictMono r}
    let ext : Finset (Q ≃ Fin (Fintype.card Q)) := by
      classical
      exact Finset.univ.filter (fun r => StrictMono r)
    letI : Fintype E := by classical exact inferInstanceAs (Fintype {r : Q ≃ Fin _ // StrictMono r})
    ((ext.filter (fun r => r x < r y)).card : ℚ) / ext.card =
      ((Finset.univ.filter (fun r : E => r.val x < r.val y)).card : ℚ) / Fintype.card E := by
  classical
  intro E ext
  have den : Fintype.card E = ext.card := Fintype.card_of_subtype ext (by simp [ext])
  have num : (Finset.univ.filter (fun r : E => r.val x < r.val y)).card =
      (ext.filter (fun r => r x < r y)).card := by
    apply Finset.card_bij (fun r _ => r.val)
    · intro r hr
      exact Finset.mem_filter.mpr ⟨by simpa [ext] using r.property, (Finset.mem_filter.mp hr).2⟩
    · intro r _ s _ eq
      exact Subtype.ext eq
    · intro r hr
      obtain ⟨he, hxy⟩ := Finset.mem_filter.mp hr
      exact ⟨⟨r, by simpa [ext] using he⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy⟩, rfl⟩
  rw [den, num]

lemma cut_probabilities {A B W : Type} [PartialOrder A] [PartialOrder B] [PartialOrder W]
    [Fintype A] [Fintype B] [Fintype W] (parts : A ⊕ B ≃ W)
    (leftOrder : ∀ a a', parts (.inl a) < parts (.inl a') ↔ a < a')
    (rightOrder : ∀ b b', parts (.inr b) < parts (.inr b') ↔ b < b')
    (cross : ∀ a b, parts (.inl a) < parts (.inr b)) :
    let prob (Q : Type) [PartialOrder Q] [Fintype Q] (x y : Q) : ℚ :=
      let ext : Finset (Q ≃ Fin (Fintype.card Q)) := by
        classical
        exact Finset.univ.filter (fun r => StrictMono r)
      ((ext.filter (fun r => r x < r y)).card : ℚ) / ext.card
    (∀ a c : A, prob A a c = prob W (parts (.inl a)) (parts (.inl c))) ∧
    (∀ b d : B, prob B b d = prob W (parts (.inr b)) (parts (.inr d))) := by
  classical
  intro prob
  let E (Q : Type) [PartialOrder Q] [Fintype Q] := {r : Q ≃ Fin (Fintype.card Q) // StrictMono r}
  let : Nonempty (E A) := rank_exists A
  let : Nonempty (E B) := rank_exists B
  obtain ⟨join, ranks⟩ := factor_extensions parts leftOrder rightOrder cross
  constructor
  · intro a c
    refine (rank_event A a c).trans (Eq.trans ?_ (rank_event W _ _).symm)
    apply uniform_factor join
    intro p
    simp only [Fin.lt_def, (ranks p).1]
  · intro b d
    refine (rank_event B b d).trans (Eq.trans ?_ (rank_event W _ _).symm)
    apply uniform_factor ((Equiv.prodComm (E B) (E A)).trans join)
    intro p
    change (p.1.val b).val < (p.1.val d).val ↔
      ((join (p.2, p.1)).val (parts (.inr b))).val < ((join (p.2, p.1)).val (parts (.inr d))).val
    simp only [(ranks (p.2, p.1)).2, Nat.add_lt_add_iff_left]

-- A single cut preserves the probability of every comparison inside either side.
lemma cut_identity :
  let prob (Q : Type) [PartialOrder Q] [Fintype Q] (x y : Q) : ℚ :=
    let ext : Finset (Q ≃ Fin (Fintype.card Q)) := by
      classical
      exact Finset.univ.filter (fun rank => StrictMono rank)
    ((ext.filter (fun rank => rank x < rank y)).card : ℚ) / ext.card
  ∀ (P : Type) [PartialOrder P] (S T : Finset P) (sub : T ⊂ S),
    ((∀ x ∈ T, ∀ y ∈ S, y ∉ T → x < y) ∨
     (∀ x ∈ T, ∀ y ∈ S, y ∉ T → y < x)) →
    ∀ x y : T, prob T x y =
      prob S ⟨x.val, sub.1 x.property⟩ ⟨y.val, sub.1 y.property⟩ := by
  classical
  intro prob P _ S T sub side x y
  let B := {z : S // z.val ∉ T}
  let inc : T ≃ {z : S // z.val ∈ T} :=
    { toFun := fun a => ⟨⟨a.val, sub.1 a.property⟩, a.property⟩
      invFun := fun z => ⟨z.val.val, z.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let parts : T ⊕ B ≃ S :=
    (inc.sumCongr (Equiv.refl B)).trans (Equiv.sumCompl (fun z : S => z.val ∈ T))
  rcases side with lower | upper
  · exact (cut_probabilities parts (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl)
      (fun a b => lower a.val a.property b.val.val b.val.property b.property)).1 x y
  · let rev := (Equiv.sumComm B T).trans parts
    exact (cut_probabilities rev (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl)
      (fun b a => upper a.val a.property b.val.val b.val.property b.property)).2 x y

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

lemma select_block :
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
        exact (cut_identity P S T sub side x y).trans (hg _ _)
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
  intro narrow wide P _ _ nonchain
  let e : Shrink.{0} P ≃o P := (orderIsoShrink.{0} P).symm
  have hn : ¬ ∀ x y : Shrink.{0} P, x ≤ y ∨ y ≤ x := by
    intro total
    apply nonchain
    intro a b
    simpa only [e.symm.le_iff_le] using total (e.symm a) (e.symm b)
  obtain ⟨S, hS, hcut, hprob⟩ := select_block (Shrink.{0} P) hn
  have core (Q : Type) [PartialOrder Q] [Fintype Q]
      (hn : ¬ ∀ x y : Q, x ≤ y ∨ y ≤ x)
      (hi : ¬ ∃ L : Set Q, L.Nonempty ∧ (∃ y, y ∉ L) ∧ ∀ x ∈ L, ∀ y ∉ L, x < y) :
      let ext : Finset (Q ≃ Fin (Fintype.card Q)) := by
        classical
        exact Finset.univ.filter (fun r => StrictMono r)
      ∃ x y : Q, x ≠ y ∧
        let p := ((ext.filter (fun r => r x < r y)).card : ℚ) / ext.card
        1 / 3 ≤ p ∧ p ≤ 2 / 3 := by
    by_cases hw : ∀ a b c : Q, a ≤ b ∨ b ≤ a ∨ a ≤ c ∨ c ≤ a ∨ b ≤ c ∨ c ≤ b
    · exact narrow Q hn hi hw
    · simp only [not_forall, not_or] at hw
      obtain ⟨a, b, c, ab, ba, ac, ca, bc, cb⟩ := hw
      exact wide Q hn hi ⟨a, b, c, ⟨ab, ba⟩, ⟨ac, ca⟩, bc, cb⟩
  obtain ⟨x, y, hxy, hbounds⟩ := core S hS hcut
  have eqProb := (hprob x y).trans (count_transport e x.val y.val)
  exact ⟨e x.val, e y.val, fun h => hxy (Subtype.ext (e.injective h)),
    transfer_bounds eqProb hbounds⟩

end OMA.R_wp_1_3_2_3_conjecture_R1
