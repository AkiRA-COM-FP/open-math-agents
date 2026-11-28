import OMAReductions.R_wp_1_3_2_3_conjecture_R1

-- Credit: @wispiANt
namespace OMA.R_wp_1_3_2_3_conjecture_R1_H1_R1

def H1 : Prop := ∀ (P : Type) [PartialOrder P] [Fintype P],
    (¬ ∀ x y : P, x ≤ y ∨ y ≤ x) →
    (¬ ∃ L : Set P, L.Nonempty ∧ (∃ y, y ∉ L) ∧
      ∀ x ∈ L, ∀ y ∉ L, x < y) →
    (∀ (e : P ≃o P) (x : P), e x = x) →
    (∃ s : Finset P, (s : Set P).Pairwise (fun a b => ¬ a ≤ b) ∧ s.card = 3 ∧
      ∀ t : Finset P, (t : Set P).Pairwise (fun a b => ¬ a ≤ b) → t.card ≤ 3) →
    (∀ x : P, ({y : P | ¬ x ≤ y ∧ ¬ y ≤ x} : Set P).ncard ≤ 6) →
    (¬ ∃ x y : P, x ≠ y ∧ (∀ c : P, (c ⋖ x) ↔ (c ⋖ y)) ∧
      (∀ a b, x ≤ a → x ≤ b → a ≤ b ∨ b ≤ a) ∧
      (∀ a b, y ≤ a → y ≤ b → a ≤ b ∨ b ≤ a)) →
    (¬ ∃ x y : P, x ≠ y ∧ (∀ c : P, (x ⋖ c) ↔ (y ⋖ c)) ∧
      (∀ a b, a ≤ x → b ≤ x → a ≤ b ∨ b ≤ a) ∧
      (∀ a b, a ≤ y → b ≤ y → a ≤ b ∨ b ≤ a)) →
    (let count (extra : List (P × P)) :=
      Nat.card {σ : P ≃ Fin (Fintype.card P) //
        (∀ a b : P, a < b → σ a < σ b) ∧ ∀ c ∈ extra, σ c.1 < σ c.2}
     ¬ (∃ x y u v : P, x ≠ y ∧ u ≠ v ∧
      ∀ p ∈ [(x, y), (y, x)], ∀ q ∈ [(u, v), (v, u)],
        count [p] + count [p, q] ≤ count [])) →
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
    (∀ (e : P ≃o P) (x : P), e x = x) →
    (∃ s : Finset P, (s : Set P).Pairwise (fun a b => ¬ a ≤ b) ∧ s.card = 4 ∧
      ∀ t : Finset P, (t : Set P).Pairwise (fun a b => ¬ a ≤ b) → t.card ≤ 4) →
    (∀ x : P, ({y : P | ¬ x ≤ y ∧ ¬ y ≤ x} : Set P).ncard ≤ 6) →
    (¬ ∃ x y : P, x ≠ y ∧ (∀ c : P, (c ⋖ x) ↔ (c ⋖ y)) ∧
      (∀ a b, x ≤ a → x ≤ b → a ≤ b ∨ b ≤ a) ∧
      (∀ a b, y ≤ a → y ≤ b → a ≤ b ∨ b ≤ a)) →
    (¬ ∃ x y : P, x ≠ y ∧ (∀ c : P, (x ⋖ c) ↔ (y ⋖ c)) ∧
      (∀ a b, a ≤ x → b ≤ x → a ≤ b ∨ b ≤ a) ∧
      (∀ a b, a ≤ y → b ≤ y → a ≤ b ∨ b ≤ a)) →
    (let count (extra : List (P × P)) :=
      Nat.card {σ : P ≃ Fin (Fintype.card P) //
        (∀ a b : P, a < b → σ a < σ b) ∧ ∀ c ∈ extra, σ c.1 < σ c.2}
     ¬ (∃ x y u v : P, x ≠ y ∧ u ≠ v ∧
      ∀ p ∈ [(x, y), (y, x)], ∀ q ∈ [(u, v), (v, u)],
        count [p] + count [p, q] ≤ count [])) →
    let ext : Finset (P ≃ Fin (Fintype.card P)) := by
      classical
      exact Finset.univ.filter (fun rank => StrictMono rank)
    ∃ x y : P, x ≠ y ∧
      let p := ((ext.filter (fun r => r x < r y)).card : ℚ) / ext.card
      1 / 3 ≤ p ∧ p ≤ 2 / 3

def H3 : Prop := ∀ (P : Type) [PartialOrder P] [Fintype P],
    (¬ ∀ x y : P, x ≤ y ∨ y ≤ x) →
    (¬ ∃ L : Set P, L.Nonempty ∧ (∃ y, y ∉ L) ∧
      ∀ x ∈ L, ∀ y ∉ L, x < y) →
    (∀ (e : P ≃o P) (x : P), e x = x) →
    (∃ s : Finset P, (s : Set P).Pairwise (fun a b => ¬ a ≤ b) ∧ s.card = 5 ∧
      ∀ t : Finset P, (t : Set P).Pairwise (fun a b => ¬ a ≤ b) → t.card ≤ 5) →
    (∀ x : P, ({y : P | ¬ x ≤ y ∧ ¬ y ≤ x} : Set P).ncard ≤ 6) →
    (¬ ∃ x y : P, x ≠ y ∧ (∀ c : P, (c ⋖ x) ↔ (c ⋖ y)) ∧
      (∀ a b, x ≤ a → x ≤ b → a ≤ b ∨ b ≤ a) ∧
      (∀ a b, y ≤ a → y ≤ b → a ≤ b ∨ b ≤ a)) →
    (¬ ∃ x y : P, x ≠ y ∧ (∀ c : P, (x ⋖ c) ↔ (y ⋖ c)) ∧
      (∀ a b, a ≤ x → b ≤ x → a ≤ b ∨ b ≤ a) ∧
      (∀ a b, a ≤ y → b ≤ y → a ≤ b ∨ b ≤ a)) →
    (let count (extra : List (P × P)) :=
      Nat.card {σ : P ≃ Fin (Fintype.card P) //
        (∀ a b : P, a < b → σ a < σ b) ∧ ∀ c ∈ extra, σ c.1 < σ c.2}
     ¬ (∃ x y u v : P, x ≠ y ∧ u ≠ v ∧
      ∀ p ∈ [(x, y), (y, x)], ∀ q ∈ [(u, v), (v, u)],
        count [p] + count [p, q] ≤ count [])) →
    let ext : Finset (P ≃ Fin (Fintype.card P)) := by
      classical
      exact Finset.univ.filter (fun rank => StrictMono rank)
    ∃ x y : P, x ≠ y ∧
      let p := ((ext.filter (fun r => r x < r y)).card : ℚ) / ext.card
      1 / 3 ≤ p ∧ p ≤ 2 / 3

def H4 : Prop := ∀ (P : Type) [PartialOrder P] [Fintype P],
    (¬ ∀ x y : P, x ≤ y ∨ y ≤ x) →
    (¬ ∃ L : Set P, L.Nonempty ∧ (∃ y, y ∉ L) ∧
      ∀ x ∈ L, ∀ y ∉ L, x < y) →
    (∀ (e : P ≃o P) (x : P), e x = x) →
    (∃ s : Finset P, (s : Set P).Pairwise (fun a b => ¬ a ≤ b) ∧ s.card = 6 ∧
      ∀ t : Finset P, (t : Set P).Pairwise (fun a b => ¬ a ≤ b) → t.card ≤ 6) →
    11 ≤ Fintype.card P →
    (∀ x : P, ({y : P | ¬ x ≤ y ∧ ¬ y ≤ x} : Set P).ncard ≤ 6) →
    (¬ ∃ x y : P, x ≠ y ∧ (∀ c : P, (c ⋖ x) ↔ (c ⋖ y)) ∧
      (∀ a b, x ≤ a → x ≤ b → a ≤ b ∨ b ≤ a) ∧
      (∀ a b, y ≤ a → y ≤ b → a ≤ b ∨ b ≤ a)) →
    (¬ ∃ x y : P, x ≠ y ∧ (∀ c : P, (x ⋖ c) ↔ (y ⋖ c)) ∧
      (∀ a b, a ≤ x → b ≤ x → a ≤ b ∨ b ≤ a) ∧
      (∀ a b, a ≤ y → b ≤ y → a ≤ b ∨ b ≤ a)) →
    (let count (extra : List (P × P)) :=
      Nat.card {σ : P ≃ Fin (Fintype.card P) //
        (∀ a b : P, a < b → σ a < σ b) ∧ ∀ c ∈ extra, σ c.1 < σ c.2}
     ¬ (∃ x y u v : P, x ≠ y ∧ u ≠ v ∧
      ∀ p ∈ [(x, y), (y, x)], ∀ q ∈ [(u, v), (v, u)],
        count [p] + count [p, q] ≤ count [])) →
    let ext : Finset (P ≃ Fin (Fintype.card P)) := by
      classical
      exact Finset.univ.filter (fun rank => StrictMono rank)
    ∃ x y : P, x ≠ y ∧
      let p := ((ext.filter (fun r => r x < r y)).card : ℚ) / ext.card
      1 / 3 ≤ p ∧ p ≤ 2 / 3

-- A saturated antichain has no incomparable neighbors outside itself.
lemma saturated_comparable (P : Type) [PartialOrder P] [Fintype P] (d : ℕ)
    (thin : ∀ x : P, ({y : P | ¬ x ≤ y ∧ ¬ y ≤ x} : Set P).ncard ≤ d)
    (s : Finset P) (anti : (s : Set P).Pairwise (fun a b => ¬ a ≤ b))
    (large : d < s.card) {a z : P} (ha : a ∈ s) (hz : z ∉ s) : a ≤ z ∨ z ≤ a := by
  classical
  by_contra! inc
  let neighbors := Finset.univ.filter (fun y : P => ¬ a ≤ y ∧ ¬ y ≤ a)
  have bound : neighbors.card ≤ d := by
    have same : (neighbors : Set P) = {y : P | ¬ a ≤ y ∧ ¬ y ≤ a} := by ext; simp [neighbors]
    simpa only [← same, Set.ncard_coe_finset] using thin a
  have sub : insert z (s.erase a) ⊆ neighbors := by
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · simpa [neighbors] using inc
    · obtain ⟨ne, mem⟩ := Finset.mem_erase.mp hy
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, anti ha mem ne.symm, anti mem ha ne⟩
  have n := (Finset.card_le_card sub).trans bound
  have nz : z ∉ s.erase a := fun h => hz (Finset.mem_of_mem_erase h)
  rw [Finset.card_insert_of_notMem nz, Finset.card_erase_of_mem ha] at n
  omega

lemma swap_of_same_comparabilities (P : Type) [PartialOrder P] (s : Finset P)
    (anti : (s : Set P).Pairwise (fun a b => ¬ a ≤ b))
    {a b : P} (ha : a ∈ s) (hb : b ∈ s)
    (same : ∀ z ∉ s, (a ≤ z ∨ z ≤ a) ↔ (b ≤ z ∨ z ≤ b)) :
    ∃ e : P ≃o P, e a = b := by
  classical
  let f := Equiv.swap a b
  have comparable (x z : P) (hz : z ∉ s) (cmp : x ≤ z ∨ z ≤ x) : f x ≤ z ∨ z ≤ f x := by
    by_cases xa : x = a
    · subst x
      simpa [f] using (same z hz).1 cmp
    by_cases xb : x = b
    · subst x
      simpa [f] using (same z hz).2 cmp
    simpa [f, Equiv.swap_apply_of_ne_of_ne xa xb] using cmp
  have fixed (z : P) (hz : z ∉ s) : f z = z :=
    Equiv.swap_apply_of_ne_of_ne (fun h => hz (h ▸ ha)) (fun h => hz (h ▸ hb))
  have inside (x : P) (hx : x ∈ s) : f x ∈ s := by
    by_cases xa : x = a
    · simpa [xa, f] using hb
    by_cases xb : x = b
    · simpa [xb, f] using ha
    simpa [f, Equiv.swap_apply_of_ne_of_ne xa xb] using hx
  have eq_inside {x y : P} (hx : x ∈ s) (hy : y ∈ s) (xy : x ≤ y) : x = y :=
    by_contra fun ne => anti hx hy ne xy
  have mono : Monotone f := by
    intro x y xy
    by_cases hx : x ∈ s
    · by_cases hy : y ∈ s
      · rw [eq_inside hx hy xy]
      rw [fixed y hy]
      rcases comparable x y hy (Or.inl xy) with h | h
      · exact h
      · have same := eq_inside hx (inside x hx) (xy.trans h)
        exact (hy ((le_antisymm xy (same ▸ h)) ▸ hx)).elim
    · rw [fixed x hx]
      by_cases hy : y ∈ s
      · rcases comparable y x hx (Or.inr xy) with h | h
        · have same := eq_inside (inside y hy) hy (h.trans xy)
          have yx : y ≤ x := same ▸ h
          exact (hx ((le_antisymm yx xy) ▸ hy)).elim
        · exact h
      · simpa [fixed y hy] using xy
  let e : P ≃o P := { f with
    map_rel_iff' := by
      intro x y
      exact ⟨fun h => by simpa [f] using mono h, fun h => mono h⟩ }
  exact ⟨e, Equiv.swap_apply_left _ _⟩

lemma saturated_swap (P : Type) [PartialOrder P] (s : Finset P)
    (anti : (s : Set P).Pairwise (fun a b => ¬ a ≤ b))
    (comparable : ∀ a ∈ s, ∀ z ∉ s, a ≤ z ∨ z ≤ a)
    {a b : P} (ha : a ∈ s) (hb : b ∈ s) :
    ∃ e : P ≃o P, e a = b := by
  exact swap_of_same_comparabilities P s anti ha hb (fun z hz =>
    ⟨fun _ => comparable b hb z hz, fun _ => comparable a ha z hz⟩)

lemma rigid_antichain_bound (P : Type) [PartialOrder P] [Fintype P] (d : ℕ) (pos : 0 < d)
    (thin : ∀ x : P, ({y : P | ¬ x ≤ y ∧ ¬ y ≤ x} : Set P).ncard ≤ d)
    (rigid : ∀ (e : P ≃o P) (x : P), e x = x)
    (s : Finset P) (anti : (s : Set P).Pairwise (fun a b => ¬ a ≤ b)) : s.card ≤ d := by
  by_contra! large
  obtain ⟨a, ha, b, hb, ne⟩ := Finset.one_lt_card.mp (show 1 < s.card by omega)
  obtain ⟨e, moved⟩ := saturated_swap P s anti
    (fun _ ha _ hz => saturated_comparable P d thin s anti large ha hz) ha hb
  exact ne ((rigid e a).symm.trans moved)

-- At equality in the width bound, each member can have at most one
-- incomparable neighbor outside the antichain.
lemma outside_card_le_one (P : Type) [PartialOrder P] [Fintype P] (s : Finset P)
    (anti : (s : Set P).Pairwise (fun a b => ¬ a ≤ b))
    (thin : ∀ x : P, ({y : P | ¬ x ≤ y ∧ ¬ y ≤ x} : Set P).ncard ≤ s.card)
    {a : P} (ha : a ∈ s) :
    ({y : P | y ∉ s ∧ ¬ a ≤ y ∧ ¬ y ≤ a} : Set P).ncard ≤ 1 := by
  classical
  let outside := Finset.univ.filter (fun y : P => y ∉ s ∧ ¬ a ≤ y ∧ ¬ y ≤ a)
  let neighbors := Finset.univ.filter (fun y : P => ¬ a ≤ y ∧ ¬ y ≤ a)
  have card_out : (outside : Set P) = {y : P | y ∉ s ∧ ¬ a ≤ y ∧ ¬ y ≤ a} := by ext; simp [outside]
  have card_all : (neighbors : Set P) = {y : P | ¬ a ≤ y ∧ ¬ y ≤ a} := by ext; simp [neighbors]
  have cap := thin a
  rw [← card_all, Set.ncard_coe_finset] at cap
  rw [← card_out, Set.ncard_coe_finset]
  have dis : Disjoint (s.erase a) outside := Finset.disjoint_left.mpr (fun _ hi ho =>
    (Finset.mem_filter.mp ho).2.1 (Finset.mem_of_mem_erase hi))
  have sub : s.erase a ∪ outside ⊆ neighbors := by
    intro y hy
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases Finset.mem_union.mp hy with hi | ho
    · obtain ⟨ne, mem⟩ := Finset.mem_erase.mp hi
      exact ⟨anti ha mem ne.symm, anti mem ha ne⟩
    · exact (Finset.mem_filter.mp ho).2.2
  have bound := (Finset.card_le_card sub).trans cap
  rw [Finset.card_union_of_disjoint dis, Finset.card_erase_of_mem ha] at bound
  omega

lemma rigid_near_saturated_size (P : Type) [PartialOrder P] [Fintype P]
    (s : Finset P) (anti : (s : Set P).Pairwise (fun a b => ¬ a ≤ b))
    (thin : ∀ x : P, ({y : P | ¬ x ≤ y ∧ ¬ y ≤ x} : Set P).ncard ≤ s.card)
    (rigid : ∀ (e : P ≃o P) (x : P), e x = x) :
    2 * s.card ≤ Fintype.card P + 1 := by
  classical
  let profile (a : s) := Finset.univ.filter (fun z : P => z ∉ s ∧ ¬ a.val ≤ z ∧ ¬ z ≤ a.val)
  have mem (a : s) (z : P) : z ∈ profile a ↔ z ∉ s ∧ ¬ a.val ≤ z ∧ ¬ z ≤ a.val := by simp [profile]
  have single (a : s) : (profile a).card ≤ 1 := by
    have h : (profile a : Set P) = {z : P | z ∉ s ∧ ¬ a.val ≤ z ∧ ¬ z ≤ a.val} := Set.ext (mem a)
    simpa only [← h, Set.ncard_coe_finset] using outside_card_le_one P s anti thin a.property
  have unique : Function.Injective profile := by
    intro a b eqp
    have comp (z : P) (hz : z ∉ s) : (a.val ≤ z ∨ z ≤ a.val) ↔ (b.val ≤ z ∨ z ≤ b.val) := by
      have eqmem : z ∈ profile a ↔ z ∈ profile b := eqp ▸ Iff.rfl
      rw [mem, mem] at eqmem
      tauto
    obtain ⟨e, moved⟩ := swap_of_same_comparabilities P s anti a.property b.property comp
    exact Subtype.ext ((rigid e a.val).symm.trans moved)
  let code (a : s) : Option (↥(sᶜ)) :=
    if h : (profile a).Nonempty then
      some ⟨h.choose, Finset.mem_compl.mpr ((mem a _).mp h.choose_spec).1⟩ else none
  have decode (a : s) (z : ↥(sᶜ)) : z.val ∈ profile a ↔ code a = some z := by
    unfold code
    split_ifs with h
    · constructor
      · intro hz
        exact congrArg some (Subtype.ext (Finset.card_le_one.mp (single a) _ h.choose_spec _ hz))
      · intro he
        have val := congrArg Subtype.val (Option.some.inj he)
        exact val ▸ h.choose_spec
    · exact ⟨fun hz => (h ⟨z.val, hz⟩).elim, fun he => by cases he⟩
  have inj : Function.Injective code := by
    intro a b eqc
    apply unique
    ext z
    by_cases hz : z ∈ s
    · simp [mem, hz]
    · let u : ↥(sᶜ) := ⟨z, Finset.mem_compl.mpr hz⟩
      exact (decode a u).trans (eqc ▸ (decode b u).symm)
  have bound := Fintype.card_le_of_injective code inj
  simp only [Fintype.card_option, Fintype.card_coe] at bound
  have total := Finset.card_add_card_compl s
  omega

theorem main : H1 → H2 → H3 → H4 → OMA.R_wp_1_3_2_3_conjecture_R1.H1 := by
  classical
  intro w3 w4 w5 w6 P _ _ nonchain indecomp rigid three thin upper lower noGold
  let candidates := Finset.univ.filter (fun s : Finset P => (s : Set P).Pairwise (fun a b => ¬ a ≤ b))
  have mem (s : Finset P) : s ∈ candidates ↔ (s : Set P).Pairwise (fun a b => ¬ a ≤ b) := by
    simp [candidates]
  obtain ⟨a, b, c, ab, ac, bc⟩ := three
  let triple : Finset P := {a, b, c}
  have tripleAnti : (triple : Set P).Pairwise (fun x y => ¬ x ≤ y) := by
    intro x hx y hy ne
    simp only [triple, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> tauto
  have neq {u v : P} (h : ¬ u ≤ v) : u ≠ v := fun e => h e.le
  have size : triple.card = 3 := by simp [triple, neq ab.1, neq ac.1, neq bc.1]
  obtain ⟨s, hs, greatest⟩ := candidates.exists_max_image Finset.card ⟨triple, (mem _).2 tripleAnti⟩
  have ant := (mem s).1 hs
  have high := rigid_antichain_bound P 6 (by decide) thin rigid s ant
  have low := greatest triple ((mem _).2 tripleAnti)
  rw [size] at low
  have width : ∃ t : Finset P, (t : Set P).Pairwise (fun a b => ¬ a ≤ b) ∧ t.card = s.card ∧
      ∀ u : Finset P, (u : Set P).Pairwise (fun a b => ¬ a ≤ b) → u.card ≤ s.card :=
    ⟨s, ant, rfl, fun u hu => greatest u ((mem u).2 hu)⟩
  have cases : s.card = 3 ∨ s.card = 4 ∨ s.card = 5 ∨ s.card = 6 := by omega
  rcases cases with h | h | h | h <;> rw [h] at width
  · exact w3 P nonchain indecomp rigid width thin upper lower noGold
  · exact w4 P nonchain indecomp rigid width thin upper lower noGold
  · exact w5 P nonchain indecomp rigid width thin upper lower noGold
  · have cap (x : P) : ({y : P | ¬ x ≤ y ∧ ¬ y ≤ x} : Set P).ncard ≤ s.card := h ▸ thin x
    have bound := rigid_near_saturated_size P s ant cap rigid
    exact w6 P nonchain indecomp rigid width (by omega) thin upper lower noGold

end OMA.R_wp_1_3_2_3_conjecture_R1_H1_R1
