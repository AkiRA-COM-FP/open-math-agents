import OMAReductions.R_wp_1_3_2_3_conjecture_R1

-- Credit: @wispiANt
namespace OMA.R_wp_1_3_2_3_conjecture_R1_H2_R1

def H1 : Prop := ∀ (P : Type) [PartialOrder P] [Fintype P],
    (¬ ∀ x y : P, x ≤ y ∨ y ≤ x) →
    (¬ ∃ L : Set P, L.Nonempty ∧ (∃ y, y ∉ L) ∧
      ∀ x ∈ L, ∀ y ∉ L, x < y) →
    (∀ (e : P ≃o P) (x : P), e x = x) →
    (∃ a b c : P, (¬ a ≤ b ∧ ¬ b ≤ a) ∧ (¬ a ≤ c ∧ ¬ c ≤ a) ∧ (¬ b ≤ c ∧ ¬ c ≤ b)) →
    (∃ x : P, let N := {y : P | ¬ x ≤ y ∧ ¬ y ≤ x}
      7 ≤ N.ncard ∧ (∃ a ∈ N, ∃ b ∈ N, ∃ c ∈ N, ∃ d ∈ N, a < b ∧ b < c ∧ c < d)) →
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
    (∃ x : P, let N := {y : P | ¬ x ≤ y ∧ ¬ y ≤ x}
      7 ≤ N.ncard ∧ (¬ ∃ a ∈ N, ∃ b ∈ N, ∃ c ∈ N, ∃ d ∈ N, a < b ∧ b < c ∧ c < d) ∧
      ∃ t : Finset P, x ∈ t ∧ (t : Set P).Pairwise (fun a b => ¬ a ≤ b) ∧
        4 ≤ t.card ∧ N.ncard + 3 ≤ 3 * t.card) →
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

-- The three levels consist of endpoints whose longest chain in s has
-- respectively one, two or three elements.
lemma large_level (P : Type) [PartialOrder P] (s : Finset P)
    (short : ¬ ∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s, ∃ d ∈ s, a < b ∧ b < c ∧ c < d) :
    ∃ t : Finset P, t ⊆ s ∧ (t : Set P).Pairwise (fun a b => ¬ a ≤ b) ∧
      s.card ≤ 3 * t.card := by
  classical
  let pred (b : P) := ∃ a ∈ s, a < b
  let two (c : P) := ∃ b ∈ s, pred b ∧ b < c
  let above := s.filter pred
  let low := s.filter (fun a => ¬ pred a)
  let mid := above.filter (fun a => ¬ two a)
  let high := above.filter two
  have lowerAnti : (low : Set P).Pairwise (fun a b => ¬ a ≤ b) := by
    intro a ha b hb ne ab
    exact (Finset.mem_filter.mp hb).2 ⟨a, (Finset.mem_filter.mp ha).1, lt_of_le_of_ne ab ne⟩
  have middleAnti : (mid : Set P).Pairwise (fun a b => ¬ a ≤ b) := by
    intro a ha b hb ne ab
    obtain ⟨mem, pr⟩ := Finset.mem_filter.mp (Finset.mem_filter.mp ha).1
    exact (Finset.mem_filter.mp hb).2 ⟨a, mem, pr, lt_of_le_of_ne ab ne⟩
  have upperAnti : (high : Set P).Pairwise (fun a b => ¬ a ≤ b) := by
    intro a ha b hb ne ab
    obtain ⟨c, hc, ⟨d, hd, dc⟩, ca⟩ := (Finset.mem_filter.mp ha).2
    exact short ⟨d, hd, c, hc, a, (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).1,
      b, (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).1, dc, ca, lt_of_le_of_ne ab ne⟩
  have cut₁ : above.card + low.card = s.card := Finset.card_filter_add_card_filter_not _
  have cut₂ : high.card + mid.card = above.card := Finset.card_filter_add_card_filter_not _
  have sub : above ⊆ s := Finset.filter_subset _ _
  by_cases l : s.card ≤ 3 * low.card
  · exact ⟨low, Finset.filter_subset _ _, lowerAnti, l⟩
  by_cases m : s.card ≤ 3 * mid.card
  · exact ⟨mid, (Finset.filter_subset _ _).trans sub, middleAnti, m⟩
  exact ⟨high, (Finset.filter_subset _ _).trans sub, upperAnti, by omega⟩

lemma antichain_through_vertex (P : Type) [PartialOrder P] [Fintype P] (x : P) :
    let N := {y : P | ¬ x ≤ y ∧ ¬ y ≤ x}
    (¬ ∃ a ∈ N, ∃ b ∈ N, ∃ c ∈ N, ∃ d ∈ N, a < b ∧ b < c ∧ c < d) →
    ∃ t : Finset P, x ∈ t ∧ (t : Set P).Pairwise (fun a b => ¬ a ≤ b) ∧
      N.ncard + 3 ≤ 3 * t.card := by
  classical
  intro N short
  let s := Finset.univ.filter (fun y : P => y ∈ N)
  have mem (y : P) : y ∈ s ↔ y ∈ N := by simp [s]
  have size : N.ncard = s.card := by
    have h : (s : Set P) = N := Set.ext mem
    rw [← h, Set.ncard_coe_finset]
  obtain ⟨t, sub, anti, bound⟩ := large_level P s (by
    rintro ⟨a, ha, b, hb, c, hc, d, hd, chain⟩
    exact short ⟨a, (mem _).1 ha, b, (mem _).1 hb, c, (mem _).1 hc, d, (mem _).1 hd, chain⟩)
  have inc {a : P} (ha : a ∈ t) : ¬ x ≤ a ∧ ¬ a ≤ x := (mem a).1 (sub ha)
  have outside : x ∉ t := fun h => (inc h).1 le_rfl
  refine ⟨insert x t, Finset.mem_insert_self _ _, ?_, ?_⟩
  · intro a ha b hb ne
    by_cases ax : a = x
    · subst a
      exact (inc ((Finset.mem_insert.mp hb).resolve_left ne.symm)).1
    have at' := (Finset.mem_insert.mp ha).resolve_left ax
    by_cases bx : b = x
    · subst b
      exact (inc at').2
    exact anti at' ((Finset.mem_insert.mp hb).resolve_left bx) ne
  · rw [size, Finset.card_insert_of_notMem outside]
    omega

theorem main : H1 → H2 → OMA.R_wp_1_3_2_3_conjecture_R1.H2 := by
  intro chainCase antichainCase P _ _ nonchain indecomp rigid three wide up down noGold
  obtain ⟨x, hx⟩ := wide
  let N := {y : P | ¬ x ≤ y ∧ ¬ y ≤ x}
  by_cases chain : ∃ a ∈ N, ∃ b ∈ N, ∃ c ∈ N, ∃ d ∈ N, a < b ∧ b < c ∧ c < d
  · exact chainCase P nonchain indecomp rigid three ⟨x, hx, chain⟩ up down noGold
  · obtain ⟨t, xt, anti, bound⟩ := antichain_through_vertex P x chain
    have four : 4 ≤ t.card := by omega
    exact antichainCase P nonchain indecomp rigid ⟨x, hx, chain, t, xt, anti, four, bound⟩ up down noGold

end OMA.R_wp_1_3_2_3_conjecture_R1_H2_R1
