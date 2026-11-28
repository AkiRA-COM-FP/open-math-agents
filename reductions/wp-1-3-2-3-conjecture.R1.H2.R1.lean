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
      7 ≤ N.ncard ∧ (∃ a ∈ N, ∃ b ∈ N, ∃ c ∈ N, ∃ d ∈ N, a < b ∧ b < c ∧ c < d ∧
      let C (l : List (P × P)) := Nat.card {r : P ≃ Fin (Fintype.card P) //
      (∀ a b : P, a < b → r a < r b) ∧ ∀ p ∈ l, r p.1 < r p.2}
      let jump (u v : P) := 3 * C [(x,u)] < C [] ∧ 2 * C [] < 3 * C [(x,v)] ∧
        C [] < 3 * C [(u,x),(x,v)];
      2 * C [] < 3 * C [(x,a)] ∨ 2 * C [] < 3 * C [(d,x)] ∨ jump a b ∨ jump b c ∨ jump c d)) →
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

-- On a chain, the count before v increases from the count before u by
-- exactly the number of extensions inserting x strictly between u and v.
lemma insertion_count (P : Type) [PartialOrder P] [Fintype P] :
    let C (l : List (P × P)) := Nat.card {r : P ≃ Fin (Fintype.card P) //
      (∀ a b : P, a < b → r a < r b) ∧ ∀ p ∈ l, r p.1 < r p.2}
    ∀ x u v : P, x ≠ u → u < v →
      C [(x,u)] + C [(u,x),(x,v)] = C [(x,v)] := by
  intro C x u v xu uv
  obtain ⟨_, _, split, cells⟩ := OMA.R_wp_1_3_2_3_conjecture_R1.comparison_counts P
  have nested : C [(x,v),(x,u)] = C [(x,u)] := by
    apply Nat.card_congr (Equiv.subtypeEquivRight ?_)
    intro r
    simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff]
    constructor
    · exact fun h => ⟨h.1, h.2.2⟩
    · exact fun h => ⟨h.1, lt_trans h.2.1 (h.1 u v uv), h.2⟩
  have parts : C [(x,v),(x,u)] + C [(x,v),(u,x)] = C [(x,v)] := split [(x,v)] x u xu
  have swap : C [(x,v),(u,x)] = C [(u,x),(x,v)] := (cells _ _).2.2
  rwa [nested, swap] at parts

lemma pair_of_count_bounds (P : Type) [PartialOrder P] [Fintype P] :
    let C (l : List (P × P)) := Nat.card {r : P ≃ Fin (Fintype.card P) //
      (∀ a b : P, a < b → r a < r b) ∧ ∀ p ∈ l, r p.1 < r p.2}
    ∀ x y : P, x ≠ y → C [] ≤ 3 * C [(x,y)] → 3 * C [(x,y)] ≤ 2 * C [] →
    let ext : Finset (P ≃ Fin (Fintype.card P)) := by
      classical
      exact Finset.univ.filter (fun rank => StrictMono rank)
    ∃ x y : P, x ≠ y ∧
      let p := ((ext.filter (fun r => r x < r y)).card : ℚ) / ext.card
      1 / 3 ≤ p ∧ p ≤ 2 / 3 := by
  classical
  intro C x y ne lo hi ext
  obtain ⟨den, num, _, _⟩ := OMA.R_wp_1_3_2_3_conjecture_R1.comparison_counts P
  have den' : C [] = ext.card := den
  have num' : C [(x,y)] = (ext.filter (fun r => r x < r y)).card := num x y
  rw [den', num'] at lo hi
  obtain ⟨r, hr⟩ := OMA.R_wp_1_3_2_3_conjecture_R1.rank_exists P
  have pos : 0 < ext.card := Finset.card_pos.mpr ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩⟩
  let k := (ext.filter (fun r => r x < r y)).card
  have l : (ext.card : ℚ) ≤ 3 * (k : ℚ) := by exact_mod_cast lo
  have h : 3 * (k : ℚ) ≤ 2 * (ext.card : ℚ) := by exact_mod_cast hi
  have p : (0 : ℚ) < ext.card := by exact_mod_cast pos
  refine ⟨x, y, ne, (le_div_iff₀ p).2 ?_, (div_le_iff₀ p).2 ?_⟩ <;> linarith

-- A failed balanced-pair search forces either a heavy exterior slot or
-- an interior jump from strictly below one third to strictly above two thirds.
lemma four_chain_slots (P : Type) [PartialOrder P] [Fintype P] :
    let C (l : List (P × P)) := Nat.card {r : P ≃ Fin (Fintype.card P) //
      (∀ a b : P, a < b → r a < r b) ∧ ∀ p ∈ l, r p.1 < r p.2}
    ∀ x a b c d : P, x ≠ a → x ≠ b → x ≠ c → x ≠ d → a < b → b < c → c < d →
    (∃ y ∈ [a,b,c,d], C [] ≤ 3 * C [(x,y)] ∧ 3 * C [(x,y)] ≤ 2 * C []) ∨
    (let jump (u v : P) := 3 * C [(x,u)] < C [] ∧ 2 * C [] < 3 * C [(x,v)] ∧
        C [] < 3 * C [(u,x),(x,v)];
      2 * C [] < 3 * C [(x,a)] ∨ 2 * C [] < 3 * C [(d,x)] ∨ jump a b ∨ jump b c ∨ jump c d) := by
  classical
  intro C x a b c d xa xb xc xd ab bc cd
  apply or_iff_not_imp_left.mpr
  intro ok jump
  have dich (y : P) (hy : y ∈ [a,b,c,d]) : 3 * C [(x,y)] < C [] ∨ 2 * C [] < 3 * C [(x,y)] := by
    by_contra! h
    exact ok ⟨y, hy, h⟩
  have middle (u v : P) (ne : x ≠ u) (uv : u < v)
      (lo : 3 * C [(x,u)] < C []) (hi : 2 * C [] < 3 * C [(x,v)]) : jump u v := by
    have part : C [(x,u)] + C [(u,x),(x,v)] = C [(x,v)] := insertion_count P x u v ne uv
    exact ⟨lo, hi, by omega⟩
  rcases dich a (by simp) with la | ha
  · rcases dich b (by simp) with lb | hb
    · rcases dich c (by simp) with lc | hc
      · rcases dich d (by simp) with ld | hd
        · obtain ⟨_, _, split, _⟩ := OMA.R_wp_1_3_2_3_conjecture_R1.comparison_counts P
          have part : C [(x,d)] + C [(d,x)] = C [] := split [] x d xd
          exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (middle c d xc cd lc hd))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (middle b c xb bc lb hc))))
    · exact Or.inr (Or.inr (Or.inl (middle a b xa ab la hb)))
  · exact Or.inl ha

theorem main : H1 → H2 → OMA.R_wp_1_3_2_3_conjecture_R1.H2 := by
  intro chainCase antichainCase P _ _ nonchain indecomp rigid three wide up down noGold
  obtain ⟨x, hx⟩ := wide
  let N := {y : P | ¬ x ≤ y ∧ ¬ y ≤ x}
  by_cases chain : ∃ a ∈ N, ∃ b ∈ N, ∃ c ∈ N, ∃ d ∈ N, a < b ∧ b < c ∧ c < d
  · obtain ⟨a, ha, b, hb, c, hc, d, hd, ab, bc, cd⟩ := chain
    have ne (y : P) (hy : y ∈ N) : x ≠ y := fun h => hy.1 h.le
    rcases four_chain_slots P x a b c d (ne a ha) (ne b hb) (ne c hc) (ne d hd) ab bc cd with ok | gap
    · obtain ⟨y, hy, lo, hi⟩ := ok
      have yn : y ∈ N := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl | rfl | rfl <;> assumption
      exact pair_of_count_bounds P x y (ne y yn) lo hi
    · exact chainCase P nonchain indecomp rigid three
        ⟨x, hx, a, ha, b, hb, c, hc, d, hd, ab, bc, cd, gap⟩ up down noGold
  · obtain ⟨t, xt, anti, bound⟩ := antichain_through_vertex P x chain
    have four : 4 ≤ t.card := by omega
    exact antichainCase P nonchain indecomp rigid ⟨x, hx, chain, t, xt, anti, four, bound⟩ up down noGold

end OMA.R_wp_1_3_2_3_conjecture_R1_H2_R1
