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

lemma saturated_swap (P : Type) [PartialOrder P] (s : Finset P)
    (anti : (s : Set P).Pairwise (fun a b => ¬ a ≤ b))
    (comparable : ∀ a ∈ s, ∀ z ∉ s, a ≤ z ∨ z ≤ a)
    {a b : P} (ha : a ∈ s) (hb : b ∈ s) :
    ∃ e : P ≃o P, e a = b := by
  classical
  let f := Equiv.swap a b
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
      rcases comparable (f x) (inside x hx) y hy with h | h
      · exact h
      · have same := eq_inside hx (inside x hx) (xy.trans h)
        exact (hy ((le_antisymm xy (same ▸ h)) ▸ hx)).elim
    · rw [fixed x hx]
      by_cases hy : y ∈ s
      · rcases comparable (f y) (inside y hy) x hx with h | h
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

lemma rigid_antichain_bound (P : Type) [PartialOrder P] [Fintype P] (d : ℕ) (pos : 0 < d)
    (thin : ∀ x : P, ({y : P | ¬ x ≤ y ∧ ¬ y ≤ x} : Set P).ncard ≤ d)
    (rigid : ∀ (e : P ≃o P) (x : P), e x = x)
    (s : Finset P) (anti : (s : Set P).Pairwise (fun a b => ¬ a ≤ b)) : s.card ≤ d := by
  by_contra! large
  obtain ⟨a, ha, b, hb, ne⟩ := Finset.one_lt_card.mp (show 1 < s.card by omega)
  obtain ⟨e, moved⟩ := saturated_swap P s anti
    (fun _ ha _ hz => saturated_comparable P d thin s anti large ha hz) ha hb
  exact ne ((rigid e a).symm.trans moved)

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
  · exact w6 P nonchain indecomp rigid width thin upper lower noGold

end OMA.R_wp_1_3_2_3_conjecture_R1_H1_R1
