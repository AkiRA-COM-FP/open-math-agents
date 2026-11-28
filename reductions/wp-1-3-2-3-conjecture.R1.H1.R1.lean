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

-- Members of a common class can be exchanged once a third member has
-- appeared. Inject the extensions with x,y,z in order into those with z before y.
lemma three_exchange (P : Type) [PartialOrder P] [Fintype P] (s : Finset P)
    (anti : (s : Set P).Pairwise (fun a b => ¬ a ≤ b)) :
    let C (extra : List (P × P)) :=
      Nat.card {σ : P ≃ Fin (Fintype.card P) //
        (∀ a b : P, a < b → σ a < σ b) ∧ ∀ c ∈ extra, σ c.1 < σ c.2}
    ∀ x ∈ s, ∀ y ∈ s, ∀ z ∈ s, x ≠ y → y ≠ z →
    (∀ k ∉ s, ¬ y ≤ k → ¬ k ≤ y → ∀ b ∈ s, b ≠ y → k < b) →
    (∀ k ∉ s, ¬ z ≤ k → ¬ k ≤ z → ∀ b ∈ s, b ≠ z → k < b) →
    C [(x,y),(y,z)] ≤ C [(z,y)] := by
  classical
  intro C x hx y hy z hz xy yz ly lz
  let ranks (l : List (P × P)) := {r : P ≃ Fin (Fintype.card P) //
    (∀ a b : P, a < b → r a < r b) ∧ ∀ p ∈ l, r p.1 < r p.2}
  let swap := Equiv.swap y z
  have valid (r : ranks [(x,y),(y,z)]) : StrictMono (swap.trans r.val) := by
    have mono : StrictMono r.val := fun _ _ h => r.property.1 _ _ h
    have first := r.property.2 (x,y) (by simp)
    have next := r.property.2 (y,z) (by simp)
    intro a b ab
    change r.val (swap a) < r.val (swap b)
    by_cases ay : a = y
    · subst a
      have out : b ∉ s := fun hb => anti hy hb ab.ne ab.le
      have bz : b ≠ z := fun h => out (h ▸ hz)
      simp only [swap, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne ab.ne.symm bz]
      apply mono
      by_contra bad
      have zb : ¬ z ≤ b := fun h => bad (lt_of_le_of_ne h bz.symm)
      have bz' : ¬ b ≤ z := fun h => anti hy hz yz (ab.le.trans h)
      exact (lt_asymm ab) (lz b out zb bz' y hy yz)
    by_cases bz : b = z
    · subst b
      have out : a ∉ s := fun ha => anti ha hz ab.ne ab.le
      simp only [swap, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne ay ab.ne]
      by_cases h : a ≤ y
      · exact mono (lt_of_le_of_ne h ay)
      have ya : ¬ y ≤ a := fun h => anti hy hz yz (h.trans ab.le)
      exact lt_trans (mono (ly a out ya h x hx xy)) first
    have left : r.val (swap a) ≤ r.val a := by
      by_cases az : a = z
      · simpa [az,swap] using next.le
      · simp [swap, Equiv.swap_apply_of_ne_of_ne ay az]
    have right : r.val b ≤ r.val (swap b) := by
      by_cases by' : b = y
      · simpa [by',swap] using next.le
      · simp [swap, Equiv.swap_apply_of_ne_of_ne by' bz]
    exact lt_of_le_of_lt left (lt_of_lt_of_le (mono ab) right)
  let move (r : ranks [(x,y),(y,z)]) : ranks [(z,y)] := ⟨swap.trans r.val,
    fun _ _ h => valid r h, by
      intro p hp
      obtain rfl : p = (z,y) := by simpa using hp
      simpa [swap] using r.property.2 (y,z) (by simp)⟩
  apply Nat.card_le_card_of_injective move
  intro r t h
  apply Subtype.ext
  apply Equiv.ext
  intro a
  have eq := congrArg (fun q : ranks [(z,y)] => q.val (swap.symm a)) h
  change r.val (swap (swap.symm a)) = t.val (swap (swap.symm a)) at eq
  simpa using eq

lemma three_lower_gold (P : Type) [PartialOrder P] [Fintype P] (s t : Finset P)
    (anti : (s : Set P).Pairwise (fun a b => ¬ a ≤ b)) (sub : t ⊆ s) (size : 2 < t.card)
    (lower : ∀ a ∈ t, ∀ k ∉ s, ¬ a ≤ k → ¬ k ≤ a → ∀ b ∈ s, b ≠ a → k < b) :
    let C (extra : List (P × P)) :=
      Nat.card {σ : P ≃ Fin (Fintype.card P) //
        (∀ a b : P, a < b → σ a < σ b) ∧ ∀ c ∈ extra, σ c.1 < σ c.2}
    ∃ x y u v : P, x ≠ y ∧ u ≠ v ∧
      ∀ p ∈ [(x, y), (y, x)], ∀ q ∈ [(u, v), (v, u)],
        C [p] + C [p, q] ≤ C [] := by
  classical
  intro C
  by_contra absent
  obtain ⟨_, total, _⟩ := OMA.R_wp_1_3_2_3_conjecture_R1.no_gold_majority_order P absent
  let R (u v : P) := C [] < 2 * C [(u,v)]
  have orient (u v : P) (ne : u ≠ v) : R u v ∨ R v u := total u v ne
  have finish (x y z : P) (hx : x ∈ t) (hy : y ∈ t) (hz : z ∈ t)
      (xy : x ≠ y) (yz : y ≠ z) (xz : x ≠ z) (h : R x y) (k : R y z) : False := by
    have cell : C [(x,y),(y,z)] ≤ C [(z,y)] :=
      three_exchange P s anti x (sub hx) y (sub hy) z (sub hz) xy yz (lower y hy) (lower z hz)
    obtain ⟨_, _, split, _⟩ := OMA.R_wp_1_3_2_3_conjecture_R1.comparison_counts P
    have e : C [(x,y)] + C [(y,x)] = C [] := split [] x y xy
    have f : C [(y,z)] + C [(z,y)] = C [] := split [] y z yz
    dsimp only [R] at h k
    have half : 2 * max (C [(y,x)]) (C [(z,y)]) ≤ C [] := by omega
    exact absent (OMA.R_wp_1_3_2_3_conjecture_R1.balanced_triple_gold P x y z xy yz xz
      (cell.trans (le_max_right _ _)) half)
  obtain ⟨a,b,c,ha,hb,hc,ab,ac,bc⟩ := Finset.two_lt_card_iff.mp size
  rcases orient a b ab with h | h
  · rcases orient b c bc with k | k
    · exact finish a b c ha hb hc ab bc ac h k
    rcases orient a c ac with p | p
    · exact finish a c b ha hc hb ac bc.symm ab p k
    · exact finish c a b hc ha hb ac.symm ab bc.symm p h
  · rcases orient a c ac with k | k
    · exact finish b a c hb ha hc ab.symm ac bc h k
    rcases orient b c bc with p | p
    · exact finish b c a hb hc ha bc ac.symm ab.symm p k
    · exact finish c b a hc hb ha bc.symm ab.symm ac.symm p h

-- At the degree bound an outside exception belongs to at most one member.
-- Its comparisons with the remaining antichain cannot point both ways.
lemma near_antichain_gold (P : Type) [PartialOrder P] [Fintype P] (s : Finset P)
    (anti : (s : Set P).Pairwise (fun a b => ¬ a ≤ b)) (size : 5 ≤ s.card)
    (thin : ∀ x : P, ({y : P | ¬ x ≤ y ∧ ¬ y ≤ x} : Set P).ncard ≤ s.card)
    (rigid : ∀ (e : P ≃o P) (x : P), e x = x) :
    let C (extra : List (P × P)) :=
      Nat.card {σ : P ≃ Fin (Fintype.card P) //
        (∀ a b : P, a < b → σ a < σ b) ∧ ∀ c ∈ extra, σ c.1 < σ c.2}
    ∃ x y u v : P, x ≠ y ∧ u ≠ v ∧
      ∀ p ∈ [(x, y), (y, x)], ∀ q ∈ [(u, v), (v, u)],
        C [p] + C [p, q] ≤ C [] := by
  classical
  intro C
  let exc (a z : P) := z ∉ s ∧ ¬ a ≤ z ∧ ¬ z ≤ a
  have single {a k z : P} (ha : a ∈ s) (hk : exc a k) (hz : exc a z) : k = z := by
    have cap := outside_card_le_one P s anti thin ha
    exact (Set.ncard_le_one_iff_subsingleton.mp cap) hk hz
  have separated {a b z : P} (ha : a ∈ s) (hb : b ∈ s) (az : exc a z) (bz : exc b z) : a = b := by
    have comp (k : P) (hk : k ∉ s) : (a ≤ k ∨ k ≤ a) ↔ (b ≤ k ∨ k ≤ b) := by
      by_cases kz : k = z
      · subst k
        exact iff_of_false (not_or.mpr az.2) (not_or.mpr bz.2)
      · have oriented (c : P) (hc : c ∈ s) (cz : exc c z) : c ≤ k ∨ k ≤ c := by
          by_contra! bad
          exact kz (single hc ⟨hk,bad⟩ cz)
        exact iff_of_true (oriented a ha az) (oriented b hb bz)
    obtain ⟨e, moved⟩ := swap_of_same_comparabilities P s anti ha hb comp
    exact (rigid e a).symm.trans moved
  let lower (a : P) := ∀ k, exc a k → ∀ b ∈ s, b ≠ a → k < b
  let upper (a : P) := ∀ k, exc a k → ∀ b ∈ s, b ≠ a → b < k
  have classes (a : P) (ha : a ∈ s) : lower a ∨ upper a := by
    by_cases l : lower a
    · exact Or.inl l
    right
    change ¬ ∀ k, exc a k → ∀ b ∈ s, b ≠ a → k < b at l
    push Not at l
    obtain ⟨z, az, b, hb, ba, zb⟩ := l
    have cmp (v : P) (hv : v ∈ s) (va : v ≠ a) : v < z ∨ z < v := by
      have vz : v ≠ z := fun h => az.1 (h ▸ hv)
      by_contra! bad
      have ev : exc v z := ⟨az.1, fun le => bad.1 (lt_of_le_of_ne le vz),
        fun le => bad.2 (lt_of_le_of_ne le vz.symm)⟩
      exact va (separated hv ha ev az)
    have bz : b < z := (cmp b hb ba).resolve_right zb
    intro k ak v hv va
    obtain rfl := single ha ak az
    rcases cmp v hv va with h | h
    · exact h
    · have bv := lt_trans bz h
      exact (anti hb hv bv.ne bv.le).elim
  let low := s.filter lower
  let rest := s.filter (fun a => ¬ lower a)
  have partition : low.card + rest.card = s.card := Finset.card_filter_add_card_filter_not _
  by_cases many : 2 < low.card
  · apply three_lower_gold P s low anti (Finset.filter_subset _ _) many
    intro a ha k hk ak ka
    exact (Finset.mem_filter.mp ha).2 k ⟨hk,ak,ka⟩
  · have other : 2 < rest.card := by omega
    have up (a : P) (ha : a ∈ rest) : upper a := by
      obtain ⟨inside, nl⟩ := Finset.mem_filter.mp ha
      exact (classes a inside).resolve_left nl
    apply OMA.R_wp_1_3_2_3_conjecture_R1.gold_of_dual P
    apply three_lower_gold Pᵒᵈ s rest (by intro a ha b hb ne h; exact anti hb ha (Ne.symm ne) h)
      (Finset.filter_subset _ _) other
    intro a ha k hk ak ka
    exact up a ha k ⟨hk,ka,ak⟩

theorem main : H1 → H2 → H3 → OMA.R_wp_1_3_2_3_conjecture_R1.H1 := by
  classical
  intro w3 w4 w5 P _ _ nonchain indecomp rigid three thin upper lower noGold
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
    exact (noGold (near_antichain_gold P s ant (by omega) cap rigid)).elim

end OMA.R_wp_1_3_2_3_conjecture_R1_H1_R1
