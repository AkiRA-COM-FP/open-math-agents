import OMAStatements.S_oeis_a000009

/-!
# A000009 via descent on the remainder and a small-divisor test

Credit: @wispiANt. The coefficient tables, small cases, and finite
non-divisibility check come from R8 (PR #20438). The second seed is from
note #92063. The representation proof allows the large summand to vary
with the target. Its divisors need only exceed the remainder.

The finite descent certificate joins 95 intervals above the second seed.
A selected value a covers [a+20301,2a-1]. The finite induction uses only the seed and these 95 summands, so its
divisibility check needs only those 147 values. Their indices are at most 2200.
-/
-- uses note #92063

namespace OMA.R_oeis_a000009_R10

open OMA.S_oeis_a000009

def H1 : Prop :=
  ∀ n : ℕ, 10441840193277271329791737218536447 < n → ∃ a r : ℕ, n = a+r ∧ 1000 ≤ a ∧
    (∃ m : ℕ, 0 < m ∧ a = strictPartitionCount m) ∧ 20301 ≤ r ∧ r < a ∧
    ∀ s : ℕ, 1000 ≤ s → (∃ m : ℕ, 0 < m ∧ s = strictPartitionCount m) → s ∣ a → r < s

def H2 : Prop :=
  ∀ n : ℕ, 1000 < n → ∀ k : Fin 3,
    let q := strictPartitionCount n
    let y := partitionCount n - 1 + k.val
    let d := (q % 9338866572734899200).gcd 9338866572734899200
    d ∣ y % 9338866572734899200 → ¬ q / d ∣ y / d

/-! ## `q(n)` as a subset count -/

/-- Distinct-part partitions of `n` are the subsets of `{1, …, n}` summing to `n`. -/
theorem strictPartitionCount_eq_subsetCount (n : ℕ) :
    strictPartitionCount n =
      ((Finset.Icc 1 n).powerset.filter (fun s => ∑ x ∈ s, x = n)).card := by
  unfold strictPartitionCount
  refine Finset.card_bij' (fun p _ => p.parts.toFinset)
    (fun s hs => ⟨s.val, fun {i} hi => by
        have := (Finset.mem_powerset.1 (Finset.mem_filter.1 hs).1) hi
        exact (Finset.mem_Icc.1 this).1,
      by simpa [Finset.sum_val] using (Finset.mem_filter.1 hs).2⟩) ?_ ?_ ?_ ?_
  · intro p hp
    have hnd : p.parts.Nodup := (Finset.mem_filter.1 hp).2
    simp only [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨fun i hi => ?_, ?_⟩
    · rw [Multiset.mem_toFinset] at hi
      exact Finset.mem_Icc.2 ⟨p.parts_pos hi, by
        have := Multiset.le_sum_of_mem hi; rw [p.parts_sum] at this; exact this⟩
    · rw [Finset.sum_eq_multiset_sum, Multiset.toFinset_val, Multiset.dedup_eq_self.2 hnd]
      simpa using p.parts_sum
  · intro s hs
    simp only [Nat.Partition.distincts, Finset.mem_filter, Finset.mem_univ, true_and]
    exact s.nodup
  · intro p hp
    have hnd : p.parts.Nodup := (Finset.mem_filter.1 hp).2
    ext1
    simp [Multiset.dedup_eq_self.2 hnd]
  · intro s hs
    ext1
    simp

theorem subsetCount_zero (n : ℕ) :
    ((Finset.Icc 1 0).powerset.filter (fun s => ∑ x ∈ s, x = n)).card =
      if n = 0 then 1 else 0 := by
  by_cases h : n = 0 <;> simp [h, Finset.filter_singleton, eq_comm]

theorem subsetCount_succ (K n : ℕ) :
    ((Finset.Icc 1 (K + 1)).powerset.filter (fun s => ∑ x ∈ s, x = n)).card =
      ((Finset.Icc 1 K).powerset.filter (fun s => ∑ x ∈ s, x = n)).card +
        if K + 1 ≤ n then
          ((Finset.Icc 1 K).powerset.filter (fun s => ∑ x ∈ s, x = n - (K + 1))).card
        else 0 := by
  simp only [Finset.card_filter]
  have hIcc : Finset.Icc 1 (K + 1) = insert (K + 1) (Finset.Icc 1 K) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have hnot : K + 1 ∉ Finset.Icc 1 K := by simp
  rw [hIcc, Finset.sum_powerset_insert hnot]
  congr 1
  have key : ∀ t ∈ (Finset.Icc 1 K).powerset,
      (if ∑ x ∈ insert (K + 1) t, x = n then 1 else 0) =
        if K + 1 ≤ n then (if ∑ x ∈ t, x = n - (K + 1) then 1 else 0) else 0 := by
    intro t ht
    have hKt : K + 1 ∉ t := fun h => hnot (Finset.mem_powerset.1 ht h)
    rw [Finset.sum_insert hKt]
    split_ifs <;> omega
  rw [Finset.sum_congr rfl key]
  split_ifs <;> simp

/-- For `n ≤ K` the bound `K` on the parts is irrelevant. -/
theorem subsetCount_of_le (n : ℕ) : ∀ K, n ≤ K →
    ((Finset.Icc 1 K).powerset.filter (fun s => ∑ x ∈ s, x = n)).card =
      ((Finset.Icc 1 n).powerset.filter (fun s => ∑ x ∈ s, x = n)).card := by
  intro K hK
  induction K, hK using Nat.le_induction with
  | base => rfl
  | succ K hK ih =>
    rw [subsetCount_succ, if_neg (by omega), add_zero, ih]

/-! ## The coefficient table of `∏ (1 + x^k)` -/

section Table

variable (N : ℕ) (t : ℕ → List ℕ) (h0 : t 0 = 1 :: List.replicate N 0)
  (hs : ∀ K, t (K + 1) = List.zipWith (· + ·) (t K) (List.replicate (K + 1) 0 ++ t K))
include h0 hs

theorem tbl_length (K : ℕ) : (t K).length = N + 1 := by
  induction K with
  | zero => simp [h0]
  | succ K ih => simp [hs, ih]

theorem tbl_getD (K : ℕ) : ∀ i ≤ N, (t K).getD i 0 =
    ((Finset.Icc 1 K).powerset.filter (fun s => ∑ x ∈ s, x = i)).card := by
  induction K with
  | zero =>
    intro i hi
    rw [subsetCount_zero]
    rcases i with _ | i
    · simp [h0]
    · simp [h0, List.getD_eq_getElem?_getD, List.getElem?_replicate]; split <;> rfl
  | succ K ih =>
    intro i hi
    have hlen := tbl_length N t h0 hs K
    rw [subsetCount_succ, ← ih i hi]
    simp only [hs, List.getD_eq_getElem?_getD, List.getElem?_zipWith]
    have h1 : i < (t K).length := by omega
    rw [List.getElem?_eq_getElem h1]
    by_cases hk : K + 1 ≤ i
    · rw [if_pos hk, ← ih (i - (K + 1)) (by omega), List.getElem?_append_right (by simp; omega)]
      simp only [List.length_replicate, List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_getElem (by omega)]
      simp
    · rw [if_neg hk, List.getElem?_append_left (by simp; omega), List.getElem?_replicate]
      simp [show i < K + 1 by omega]

end Table

/-- One table gives every value `q(n)` with `n ≤ N`. -/
theorem strictPartitionCount_eq_rec (N n : ℕ) (hn : n ≤ N) :
    strictPartitionCount n = (Nat.rec (motive := fun _ => List ℕ) (1 :: List.replicate N 0)
      (fun k l => List.zipWith (· + ·) l (List.replicate (k + 1) 0 ++ l)) N).getD n 0 := by
  rw [strictPartitionCount_eq_subsetCount,
    tbl_getD N (fun K => Nat.rec (motive := fun _ => List ℕ) (1 :: List.replicate N 0)
      (fun k l => List.zipWith (· + ·) l (List.replicate (k + 1) 0 ++ l)) K) rfl (fun _ => rfl)
      N n hn,
    subsetCount_of_le n N hn]

/-- Entries `1, …, N` of the table are values of `q`. -/
theorem mem_qList {N x : ℕ} (hx : x ∈ (Nat.rec (motive := fun _ => List ℕ)
    (1 :: List.replicate N 0)
    (fun k l => List.zipWith (· + ·) l (List.replicate (k + 1) 0 ++ l)) N).drop 1) :
    ∃ m, 0 < m ∧ x = strictPartitionCount m := by
  rw [List.mem_iff_getElem] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  have hlen := tbl_length N (fun K => Nat.rec (motive := fun _ => List ℕ)
    (1 :: List.replicate N 0)
    (fun k l => List.zipWith (· + ·) l (List.replicate (k + 1) 0 ++ l)) K) rfl (fun _ => rfl) N
  simp only [List.length_drop] at hi
  refine ⟨i + 1, by omega, ?_⟩
  rw [strictPartitionCount_eq_rec N (i + 1) (by omega), List.getElem_drop,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  simp [Nat.add_comm]

/-! ## Subset sums as a bitset -/

/-- Bit `s` of `l.foldr (fun a b => b ||| b <<< a) 1` is set iff some subset of `l` sums to `s`. -/
theorem testBit_foldr (l : List ℕ) (hl : l.Nodup) (s : ℕ) :
    (l.foldr (fun a b => b ||| b <<< a) 1).testBit s = true ↔
      ∃ T ⊆ l.toFinset, ∑ x ∈ T, x = s := by
  induction l generalizing s with
  | nil =>
    simp only [List.foldr_nil, List.toFinset_nil, Finset.subset_empty, exists_eq_left,
      Finset.sum_empty]
    rcases s with _ | s <;> simp [Nat.testBit_succ]
  | cons a l ih =>
    have ha : a ∉ l := (List.nodup_cons.1 hl).1
    have hl' : l.Nodup := (List.nodup_cons.1 hl).2
    simp only [List.foldr_cons, Nat.testBit_lor, Nat.testBit_shiftLeft, Bool.or_eq_true,
      Bool.and_eq_true, decide_eq_true_eq, ih hl', List.toFinset_cons]
    constructor
    · rintro (⟨T, hT, hs⟩ | ⟨hsa, T, hT, hs⟩)
      · exact ⟨T, hT.trans (Finset.subset_insert _ _), hs⟩
      · have haT : a ∉ T := fun h => ha (List.mem_toFinset.1 (hT h))
        refine ⟨insert a T, Finset.insert_subset_insert _ hT, ?_⟩
        rw [Finset.sum_insert haT, hs]; omega
    · rintro ⟨T, hT, hs⟩
      by_cases haT : a ∈ T
      · right
        have hle : a ≤ ∑ x ∈ T, x :=
          Finset.single_le_sum (f := fun x => x) (fun _ _ => Nat.zero_le _) haT
        refine ⟨by omega, T.erase a, ?_, ?_⟩
        · intro x hx
          have hx' := Finset.mem_erase.1 hx
          rcases Finset.mem_insert.1 (hT hx'.2) with h | h
          · exact absurd h hx'.1
          · exact h
        · have := Finset.sum_erase_add T (fun x => x) haT
          omega
      · left
        refine ⟨T, fun x hx => ?_, hs⟩
        rcases Finset.mem_insert.1 (hT hx) with h | h
        · exact absurd (h ▸ hx) haT
        · exact h

/-- One big-number identity certifies that bits `L, …, L + k - 1` are all set. -/
theorem testBit_of_mask (B L k : ℕ) (h : (B >>> L) % 2 ^ k = 2 ^ k - 1) :
    ∀ s, L ≤ s → s < L + k → B.testBit s = true := by
  intro s h1 h2
  have := congrArg (fun x => x.testBit (s - L)) h
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one] at this
  rw [show L + (s - L) = s by omega] at this
  simpa [show s - L < k by omega] using this

/-! ## The seed antichain of note #43523, checked by the kernel -/

theorem seed_exists : ∃ seed : List ℕ, seed.Nodup ∧
    (∀ x ∈ seed, x ∈ (Nat.rec (motive := fun _ => List ℕ) (1 :: List.replicate 90 0)
      (fun k l => List.zipWith (· + ·) l (List.replicate (k + 1) 0 ++ l)) 90).drop 1) ∧
    (∀ x ∈ seed, ∀ y ∈ seed, x ≠ y → y % x ≠ 0) ∧
    ((seed.foldr (fun a b => b ||| b <<< a) 1) >>> 237) % 2 ^ 997200 = 2 ^ 997200 - 1 :=
  ⟨[18, 22, 27, 32, 38, 46, 89, 104, 122, 142, 165, 222, 296, 340, 390, 585, 668,
    982, 1113, 1816, 2590, 2910, 3658, 4097, 4582, 5718, 6378, 7108, 7917, 8808, 12076, 13394,
    16444, 20132, 27130, 29927, 48446, 58499, 64234, 84756, 101698, 111322, 159046, 189586],
    by decide +kernel⟩

/-! ## Small cases, checked by the kernel -/

theorem small_exists : ∃ W : List (List ℕ), ∀ i < 236, ((W.getD i []).sum = i + 1 ∧
    (W.getD i []).Nodup ∧
    (∀ x ∈ W.getD i [], x ∈ (Nat.rec (motive := fun _ => List ℕ) (1 :: List.replicate 28 0)
      (fun k l => List.zipWith (· + ·) l (List.replicate (k + 1) 0 ++ l)) 28).drop 1) ∧
    ∀ x ∈ W.getD i [], ∀ y ∈ W.getD i [], x ≠ y → y % x ≠ 0) :=
  ⟨[[1], [2], [3], [4], [5], [6], [5, 2], [8], [5, 4], [10], [8, 3], [12], [10, 3], [10, 4], [15],
    [10, 6], [15, 2], [18], [15, 4], [12, 8], [15, 6], [22], [18, 5], [10, 8, 6], [22, 3], [22, 4],
    [27], [22, 6], [27, 2], [22, 8], [27, 4], [32], [27, 6], [27, 5, 2], [32, 3], [27, 5, 4],
    [32, 5], [38], [27, 12], [32, 5, 3], [38, 3], [38, 4], [38, 5], [38, 6], [38, 4, 3], [46],
    [38, 5, 4], [38, 10], [46, 3], [46, 4], [46, 5], [46, 6], [46, 4, 3], [54], [46, 5, 4],
    [46, 10], [46, 8, 3], [54, 4], [54, 5], [46, 10, 4], [46, 15], [54, 8], [54, 5, 4], [64],
    [46, 15, 4], [54, 12], [64, 3], [54, 10, 4], [64, 5], [64, 6], [54, 12, 5], [64, 5, 3],
    [54, 15, 4], [64, 10], [64, 6, 5], [76], [64, 10, 3], [46, 32], [76, 3], [64, 10, 6], [76, 5],
    [76, 6], [54, 15, 10, 4], [76, 8], [64, 15, 6], [76, 10], [76, 8, 3], [76, 12], [89],
    [76, 8, 6], [89, 2], [89, 3], [89, 4], [89, 5], [89, 6], [89, 5, 2], [89, 8], [89, 5, 4],
    [89, 10], [89, 8, 3], [89, 12], [89, 10, 3], [89, 10, 4], [104], [89, 10, 6], [89, 15, 2],
    [104, 3], [89, 15, 4], [104, 5], [104, 6], [89, 22], [104, 5, 3], [89, 10, 8, 6], [104, 10],
    [104, 6, 5], [104, 12], [104, 10, 3], [89, 27, 2], [104, 15], [104, 10, 6], [104, 12, 5],
    [122], [89, 27, 5, 2], [89, 32, 3], [122, 3], [122, 4], [122, 5], [122, 6], [122, 4, 3],
    [122, 8], [122, 5, 4], [122, 10], [122, 8, 3], [122, 12], [122, 10, 3], [122, 10, 4],
    [122, 15], [122, 10, 6], [122, 12, 5], [122, 18], [122, 15, 4], [142], [122, 15, 6],
    [122, 22], [142, 3], [142, 4], [142, 5], [142, 6], [142, 4, 3], [142, 8], [142, 5, 4],
    [142, 10], [142, 8, 3], [142, 12], [142, 10, 3], [142, 10, 4], [142, 15], [142, 10, 6],
    [142, 12, 5], [142, 18], [142, 15, 4], [142, 12, 8], [142, 15, 6], [142, 22], [165],
    [142, 10, 8, 6], [165, 2], [142, 22, 4], [165, 4], [142, 22, 6], [165, 6], [142, 22, 8],
    [165, 8], [142, 32], [165, 10], [142, 22, 12], [165, 12], [142, 27, 5, 4], [165, 10, 4],
    [142, 38], [165, 10, 6], [142, 32, 5, 3], [165, 18], [142, 38, 4], [165, 12, 8], [142, 38, 6],
    [165, 22], [142, 46], [165, 10, 8, 6], [142, 38, 10], [165, 22, 4], [192], [165, 22, 6],
    [165, 27, 2], [165, 22, 8], [165, 27, 4], [192, 5], [165, 27, 6], [165, 22, 12], [165, 27, 8],
    [165, 22, 10, 4], [192, 10], [165, 38], [165, 27, 12], [165, 22, 18], [165, 27, 10, 4],
    [192, 15], [165, 27, 10, 6], [165, 38, 6], [192, 18], [165, 46], [165, 27, 12, 8],
    [165, 38, 10], [192, 22], [192, 18, 5], [165, 27, 10, 8, 6], [192, 15, 10], [165, 27, 22, 4],
    [192, 27], [192, 18, 10], [165, 46, 10], [222], [165, 54, 4], [192, 27, 5], [192, 18, 15],
    [222, 4], [222, 5], [165, 27, 22, 10, 4], [192, 27, 10], [222, 8], [222, 5, 4], [222, 10],
    [165, 54, 10, 4], [222, 12], [222, 8, 5], [222, 10, 4]],
    by decide +kernel⟩

/-! ## The representation conjecture below one million -/

theorem H1_le (n : ℕ) (hn : 0 < n) (hle : n ≤ 997436) : ∃ T : Finset ℕ,
    (∀ x ∈ T, ∃ m : ℕ, 0 < m ∧ x = strictPartitionCount m) ∧
    (∀ x ∈ T, ∀ y ∈ T, x ≠ y → ¬ x ∣ y) ∧
    (∑ x ∈ T, x) = n := by
  by_cases hs : n < 237
  · obtain ⟨W, hW⟩ := small_exists
    obtain ⟨hsum, hnd, hq, han⟩ := hW (n - 1) (by omega)
    refine ⟨(W.getD (n - 1) []).toFinset, ?_, ?_, ?_⟩
    · intro x hx; exact mem_qList (N := 28) (hq x (List.mem_toFinset.1 hx))
    · intro x hx y hy hxy hd
      exact han x (List.mem_toFinset.1 hx) y (List.mem_toFinset.1 hy) hxy
        (Nat.mod_eq_zero_of_dvd hd)
    · rw [List.sum_toFinset _ hnd, List.map_id', hsum]; omega
  · obtain ⟨seed, hnd, hq, han, hmask⟩ := seed_exists
    have hb := testBit_of_mask _ _ _ hmask n (by omega) (by omega)
    obtain ⟨T, hT, hsum⟩ := (testBit_foldr seed hnd n).1 hb
    refine ⟨T, ?_, ?_, hsum⟩
    · intro x hx; exact mem_qList (N := 90) (hq x (List.mem_toFinset.1 (hT hx)))
    · intro x hx y hy hxy hd
      exact han x (List.mem_toFinset.1 (hT hx)) y (List.mem_toFinset.1 (hT hy)) hxy
        (Nat.mod_eq_zero_of_dvd hd)

/-! ## From sets to the target's form, and the greedy step -/

theorem rep_of_finset (T : Finset ℕ)
    (hq : ∀ x ∈ T, ∃ m : ℕ, 0 < m ∧ x = strictPartitionCount m)
    (hanti : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → ¬ x ∣ y) :
    ∃ k : ℕ, ∃ terms : Fin k → ℕ,
      (∀ i, ∃ m : ℕ, 0 < m ∧ terms i = strictPartitionCount m) ∧
      (∑ i, terms i) = ∑ x ∈ T, x ∧
      (∀ i j, i ≠ j → ¬ terms i ∣ terms j) := by
  let e : T ≃ Fin T.card := T.equivFin
  refine ⟨T.card, fun i => (e.symm i : ℕ), ?_, ?_, ?_⟩
  · intro i
    exact hq _ (e.symm i).2
  · rw [Equiv.sum_comp e.symm (fun x : T => (x : ℕ))]
    exact Finset.sum_coe_sort T (fun x => x)
  · intro i j hij
    apply hanti _ (e.symm i).2 _ (e.symm j).2
    intro h
    exact hij (e.symm.injective (Subtype.ext h))

/-! ## `p(n)` as a table -/

/-- Partitions of `n` with every part at most `K`. -/
theorem pc_le_card (n : ℕ) : ∀ p : n.Partition, ∀ i ∈ p.parts, i ≤ n := by
  intro p i hi
  have := Multiset.le_sum_of_mem hi
  rw [p.parts_sum] at this
  exact this

theorem partitionCount_eq_bounded (n : ℕ) :
    partitionCount n = (Finset.univ.filter (fun p : n.Partition => ∀ i ∈ p.parts, i ≤ n)).card := by
  unfold partitionCount
  rw [Finset.filter_true_of_mem (fun p _ => pc_le_card n p), Finset.card_univ]

theorem bounded_zero (n : ℕ) :
    (Finset.univ.filter (fun p : n.Partition => ∀ i ∈ p.parts, i ≤ 0)).card =
      if n = 0 then 1 else 0 := by
  have key : ∀ p : n.Partition, (∀ i ∈ p.parts, i ≤ 0) ↔ p.parts = 0 := by
    intro p
    constructor
    · intro h
      rw [Multiset.eq_zero_iff_forall_notMem]
      intro i hi
      have := p.parts_pos hi
      have := h i hi
      omega
    · intro h i hi
      rw [h] at hi
      simp at hi
  simp only [key]
  split_ifs with hn
  · subst hn
    rw [Finset.card_eq_one]
    refine ⟨Nat.Partition.indiscrete 0, ?_⟩
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro _; exact Subsingleton.elim _ _
    · intro _
      have := p.parts_sum
      rw [Multiset.eq_zero_iff_forall_notMem]
      intro i hi
      have h1 := p.parts_pos hi
      have h2 := Multiset.le_sum_of_mem hi
      omega
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro p _ hp
    have := p.parts_sum
    rw [hp] at this
    simp at this
    omega

theorem bounded_succ (K n : ℕ) :
    (Finset.univ.filter (fun p : n.Partition => ∀ i ∈ p.parts, i ≤ K + 1)).card =
      (Finset.univ.filter (fun p : n.Partition => ∀ i ∈ p.parts, i ≤ K)).card +
        if K + 1 ≤ n then
          (Finset.univ.filter (fun p : (n - (K + 1)).Partition => ∀ i ∈ p.parts, i ≤ K + 1)).card
        else 0 := by
  rw [← Finset.card_filter_add_card_filter_not (fun p : n.Partition => K + 1 ∈ p.parts),
    Finset.filter_filter, Finset.filter_filter, add_comm]
  congr 1
  · congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h, hK⟩ i hi
      have := h i hi
      have : i ≠ K + 1 := fun e => hK (e ▸ hi)
      omega
    · intro h
      exact ⟨fun i hi => by have := h i hi; omega, fun hm => by have := h _ hm; omega⟩
  · split_ifs with hn
    · refine Finset.card_bij'
        (fun p hp => Nat.Partition.partitionWithPartEquiv (by omega) hn
          ⟨p, (Finset.mem_filter.1 hp).2.2⟩)
        (fun q _ => ((Nat.Partition.partitionWithPartEquiv (n := n) (a := K + 1)
          (by omega) hn).symm q).1) ?_ ?_ ?_ ?_
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        intro i hi
        rw [Nat.Partition.partitionWithPartEquiv_apply_parts] at hi
        exact hp.1 i (Multiset.mem_of_mem_erase hi)
      · intro q hq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
        rw [Nat.Partition.partitionWithPartEquiv_symm_apply_parts]
        refine ⟨fun i hi => ?_, Multiset.mem_cons_self _ _⟩
        rcases Multiset.mem_cons.1 hi with h | h
        · omega
        · exact hq i h
      · intro p hp
        simp
      · intro q hq
        simp
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro p _ ⟨_, hm⟩
      have := pc_le_card n p _ hm
      omega


theorem bounded_of_le (n : ℕ) : ∀ K, n ≤ K →
    (Finset.univ.filter (fun p : n.Partition => ∀ i ∈ p.parts, i ≤ K)).card =
      (Finset.univ.filter (fun p : n.Partition => ∀ i ∈ p.parts, i ≤ n)).card := by
  intro K hK
  induction K, hK using Nat.le_induction with
  | base => rfl
  | succ K hK ih => rw [bounded_succ, if_neg (by omega), add_zero, ih]

/-- The reversed scan computing `new i = old i + new (i - (k+1))`. -/
theorem scan_spec (N k : ℕ) (old : List ℕ) (f : ℕ → ℕ)
    (hf : ∀ i ≤ N, f i = old.getD i 0 + if k + 1 ≤ i then f (i - (k + 1)) else 0) :
    ∀ m ≤ N + 1, (Nat.rec (motive := fun _ => List ℕ) []
      (fun i r => (old.getD i 0 + if k + 1 ≤ i then r.getD k 0 else 0) :: r) m).length = m ∧
      ∀ j < m, (Nat.rec (motive := fun _ => List ℕ) []
      (fun i r => (old.getD i 0 + if k + 1 ≤ i then r.getD k 0 else 0) :: r) m).getD j 0 =
        f (m - 1 - j) := by
  intro m hm
  induction m with
  | zero => simp
  | succ m ih =>
    obtain ⟨hlen, hget⟩ := ih (by omega)
    refine ⟨congrArg Nat.succ hlen, ?_⟩
    intro j hj
    rcases j with _ | j
    · show List.getD (_ :: _) 0 0 = _
      rw [List.getD_cons_zero, show m + 1 - 1 - 0 = m by omega, hf m (by omega)]
      congr 1
      split_ifs with h
      · rw [hget k (by omega)]; congr 1; omega
      · rfl
    · show List.getD (_ :: _) (j + 1) 0 = _
      rw [List.getD_cons_succ, hget j (by omega)]
      congr 1; omega

theorem getD_reverse_of_lt (l : List ℕ) (i : ℕ) (hi : i < l.length) :
    l.reverse.getD i 0 = l.getD (l.length - 1 - i) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_reverse hi]

theorem scan_rev (N k : ℕ) (old : List ℕ) (f : ℕ → ℕ)
    (hf : ∀ i ≤ N, f i = old.getD i 0 + if k + 1 ≤ i then f (i - (k + 1)) else 0) :
    ∀ i ≤ N, (Nat.rec (motive := fun _ => List ℕ) []
      (fun i r => (old.getD i 0 + if k + 1 ≤ i then r.getD k 0 else 0) :: r) (N + 1)).reverse.getD
        i 0 = f i := by
  intro i hi
  obtain ⟨hlen, hget⟩ := scan_spec N k old f hf (N + 1) le_rfl
  rw [getD_reverse_of_lt _ i (by omega), hlen, hget _ (by omega)]
  congr 1; omega

/-- Row `K` of the table holds the number of partitions of `i` with parts `≤ K`. -/
theorem prow_spec (N : ℕ) (K : ℕ) :
    (Nat.rec (motive := fun _ => List ℕ) (1 :: List.replicate N 0)
      (fun k old => (Nat.rec (motive := fun _ => List ℕ) []
        (fun i r => (old.getD i 0 + if k + 1 ≤ i then r.getD k 0 else 0) :: r) (N + 1)).reverse)
      K).length = N + 1 ∧
    ∀ i ≤ N, (Nat.rec (motive := fun _ => List ℕ) (1 :: List.replicate N 0)
      (fun k old => (Nat.rec (motive := fun _ => List ℕ) []
        (fun i r => (old.getD i 0 + if k + 1 ≤ i then r.getD k 0 else 0) :: r) (N + 1)).reverse)
      K).getD i 0 =
      (Finset.univ.filter (fun p : i.Partition => ∀ j ∈ p.parts, j ≤ K)).card := by
  induction K with
  | zero =>
    refine ⟨by simp, fun i hi => ?_⟩
    rw [bounded_zero]
    rcases i with _ | i
    · simp
    · simp [List.getD_eq_getElem?_getD, List.getElem?_replicate]; split <;> rfl
  | succ K ih =>
    obtain ⟨_, hrow⟩ := ih
    have hf : ∀ i ≤ N,
        (Finset.univ.filter (fun p : i.Partition => ∀ j ∈ p.parts, j ≤ K + 1)).card =
          (Nat.rec (motive := fun _ => List ℕ) (1 :: List.replicate N 0)
            (fun k old => (Nat.rec (motive := fun _ => List ℕ) []
              (fun i r => (old.getD i 0 + if k + 1 ≤ i then r.getD k 0 else 0) :: r)
                (N + 1)).reverse) K).getD i 0 +
          if K + 1 ≤ i then
            (Finset.univ.filter (fun p : (i - (K + 1)).Partition => ∀ j ∈ p.parts, j ≤ K + 1)).card
          else 0 := by
      intro i hi
      rw [hrow i hi, bounded_succ]
    obtain ⟨hlen, _⟩ := scan_spec N K _ _ hf (N + 1) le_rfl
    exact ⟨by simp only [List.length_reverse]; exact hlen, scan_rev N K _ _ hf⟩

/-- One table gives every value `p(n)` with `n ≤ N`. -/
theorem partitionCount_eq_rec (N n : ℕ) (hn : n ≤ N) :
    partitionCount n = (Nat.rec (motive := fun _ => List ℕ) (1 :: List.replicate N 0)
      (fun k old => (Nat.rec (motive := fun _ => List ℕ) []
        (fun i r => (old.getD i 0 + if k + 1 ≤ i then r.getD k 0 else 0) :: r) (N + 1)).reverse)
      N).getD n 0 := by
  rw [(prow_spec N N).2 n hn, bounded_of_le n N hn, ← partitionCount_eq_bounded]

theorem partitionCount_pos (n : ℕ) : 1 ≤ partitionCount n :=
  Fintype.card_pos_iff.2 ⟨Nat.Partition.indiscrete n⟩
/-! ## Packed tables: one natural number per row, with `w`-bit slots -/

/-- A packed list with slot width `w` is less than `2 ^ (w * length)`. -/
theorem pack_lt (w : ℕ) (l : List ℕ) (hl : ∀ x ∈ l, x < 2 ^ w) :
    l.foldr (fun a acc => a + 2 ^ w * acc) 0 < 2 ^ (w * l.length) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha : a < 2 ^ w := hl a (by simp)
    have hP := ih (fun x hx => hl x (by simp [hx]))
    simp only [List.foldr_cons, List.length_cons]
    calc a + 2 ^ w * l.foldr (fun a acc => a + 2 ^ w * acc) 0
        < 2 ^ w * (l.foldr (fun a acc => a + 2 ^ w * acc) 0 + 1) := by rw [mul_add]; omega
      _ ≤ 2 ^ w * 2 ^ (w * l.length) := Nat.mul_le_mul_left _ hP
      _ = 2 ^ (w * (l.length + 1)) := by rw [← pow_add]; ring_nf

/-- Slot `i` of a packed list is entry `i`. -/
theorem pack_digit (w : ℕ) (l : List ℕ) (hl : ∀ x ∈ l, x < 2 ^ w) (i : ℕ) :
    (l.foldr (fun a acc => a + 2 ^ w * acc) 0 / 2 ^ (w * i)) % 2 ^ w = l.getD i 0 := by
  induction l generalizing i with
  | nil => simp
  | cons a l ih =>
    have ha : a < 2 ^ w := hl a (by simp)
    have hl' : ∀ x ∈ l, x < 2 ^ w := fun x hx => hl x (by simp [hx])
    have hpos : 0 < 2 ^ w := Nat.two_pow_pos w
    simp only [List.foldr_cons]
    rcases i with _ | i
    · rw [mul_zero, pow_zero, Nat.div_one, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
      simp
    · rw [show w * (i + 1) = w + w * i by ring, pow_add, ← Nat.div_div_eq_div_mul,
        Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt ha, zero_add, ih hl' i]
      simp

theorem pack_append (w : ℕ) (l₁ l₂ : List ℕ) :
    (l₁ ++ l₂).foldr (fun a acc => a + 2 ^ w * acc) 0 =
      l₁.foldr (fun a acc => a + 2 ^ w * acc) 0 +
        2 ^ (w * l₁.length) * l₂.foldr (fun a acc => a + 2 ^ w * acc) 0 := by
  induction l₁ with
  | nil => simp
  | cons a l₁ ih =>
    simp only [List.cons_append, List.foldr_cons, List.length_cons, ih]
    rw [show w * (l₁.length + 1) = w + w * l₁.length by ring, pow_add]
    ring

theorem pack_replicate_zero (w k : ℕ) :
    (List.replicate k 0).foldr (fun a acc => a + 2 ^ w * acc) 0 = 0 := by
  induction k with
  | zero => simp
  | succ k ih => simp [List.replicate_succ, ih]

/-- A shift by `k` slots is a multiplication by `2 ^ (w * k)`. -/
theorem pack_shift (w k : ℕ) (l : List ℕ) :
    (List.replicate k 0 ++ l).foldr (fun a acc => a + 2 ^ w * acc) 0 =
      2 ^ (w * k) * l.foldr (fun a acc => a + 2 ^ w * acc) 0 := by
  rw [pack_append, pack_replicate_zero, List.length_replicate, zero_add]

/-- Entrywise addition (equal lengths) is addition of the packed numbers. -/
theorem pack_add (w : ℕ) (l₁ l₂ : List ℕ) (h : l₁.length = l₂.length) :
    (List.zipWith (· + ·) l₁ l₂).foldr (fun a acc => a + 2 ^ w * acc) 0 =
      l₁.foldr (fun a acc => a + 2 ^ w * acc) 0 + l₂.foldr (fun a acc => a + 2 ^ w * acc) 0 := by
  induction l₁ generalizing l₂ with
  | nil => cases l₂ <;> simp_all
  | cons a l₁ ih =>
    cases l₂ with
    | nil => simp at h
    | cons b l₂ =>
      simp only [List.zipWith_cons_cons, List.foldr_cons, List.length_cons] at h ⊢
      rw [ih l₂ (by omega)]
      ring

/-- Truncation to `m` entries is reduction modulo `2 ^ (w * m)`. -/
theorem pack_take (w m : ℕ) (l : List ℕ) (hl : ∀ x ∈ l, x < 2 ^ w) :
    (l.take m).foldr (fun a acc => a + 2 ^ w * acc) 0 =
      l.foldr (fun a acc => a + 2 ^ w * acc) 0 % 2 ^ (w * m) := by
  have hsplit := pack_append w (l.take m) (l.drop m)
  rw [List.take_append_drop] at hsplit
  have hlt := pack_lt w (l.take m) (fun x hx => hl x (List.mem_of_mem_take hx))
  rw [List.length_take] at hsplit hlt
  rcases le_total m l.length with hm | hm
  · rw [min_eq_left hm] at hsplit hlt
    rw [hsplit, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  · rw [min_eq_right hm] at hsplit hlt
    rw [List.take_of_length_le hm]
    have hfull := pack_lt w l hl
    refine (Nat.mod_eq_of_lt (lt_of_lt_of_le hfull ?_)).symm
    exact Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ hm)

/-! ### The packed q-table -/

section PackQ

variable (w N : ℕ) (hw : N < w) (t : ℕ → List ℕ) (h0 : t 0 = 1 :: List.replicate N 0)
  (hs : ∀ K, t (K + 1) = List.zipWith (· + ·) (t K) (List.replicate (K + 1) 0 ++ t K))
  (Q : ℕ → ℕ) (hQ0 : Q 0 = 1)
  (hQs : ∀ K, Q (K + 1) = Q K + (2 ^ (w * (K + 1)) * Q K) % 2 ^ (w * (N + 1)))
include h0 hs

theorem tbl_entry_le (K x : ℕ) (hx : x ∈ t K) : x ≤ 2 ^ K := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
  have hlen := tbl_length N t h0 hs K
  have h := tbl_getD N t h0 hs K i (by omega)
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at h
  rw [h]
  calc _ ≤ ((Finset.Icc 1 K).powerset).card := Finset.card_filter_le _ _
    _ = 2 ^ K := by rw [Finset.card_powerset, Nat.card_Icc]; congr 1

include hw hQ0 hQs in
theorem Q_eq_pack : ∀ K ≤ N, Q K = (t K).foldr (fun a acc => a + 2 ^ w * acc) 0 := by
  intro K hK
  induction K with
  | zero =>
    rw [hQ0, h0]
    simp only [List.foldr_cons, pack_replicate_zero]
    ring
  | succ K ih =>
    have hl := tbl_length N t h0 hs K
    have hbound : ∀ x ∈ List.replicate (K + 1) 0 ++ t K, x < 2 ^ w := by
      intro x hx
      rcases List.mem_append.1 hx with h | h
      · rw [List.eq_of_mem_replicate h]; exact Nat.two_pow_pos w
      · exact lt_of_le_of_lt (tbl_entry_le N t h0 hs K x h)
          (Nat.pow_lt_pow_right (by norm_num) (by omega))
    rw [hQs, ih (by omega), hs, List.zipWith_eq_zipWith_take_min]
    have hmin : min (t K).length (List.replicate (K + 1) 0 ++ t K).length = N + 1 := by
      simp [hl]
    rw [hmin, List.take_of_length_le (by omega),
      pack_add w _ _ (by simp [hl]), pack_take w (N + 1) _ hbound, pack_shift]

end PackQ

/-- `q(n)` is slot `n` of the packed q-table. -/
theorem strictPartitionCount_eq_packed (w N n : ℕ) (hw : N < w) (hn : n ≤ N) :
    strictPartitionCount n = ((Nat.rec (motive := fun _ => ℕ) 1
      (fun K B => B + (2 ^ (w * (K + 1)) * B) % 2 ^ (w * (N + 1))) N) / 2 ^ (w * n)) % 2 ^ w := by
  have ht0 : (fun K => Nat.rec (motive := fun _ => List ℕ) (1 :: List.replicate N 0)
      (fun k l => List.zipWith (· + ·) l (List.replicate (k + 1) 0 ++ l)) K) 0 =
      1 :: List.replicate N 0 := rfl
  have hts : ∀ K, (fun K => Nat.rec (motive := fun _ => List ℕ) (1 :: List.replicate N 0)
      (fun k l => List.zipWith (· + ·) l (List.replicate (k + 1) 0 ++ l)) K) (K + 1) =
      List.zipWith (· + ·) ((fun K => Nat.rec (motive := fun _ => List ℕ) (1 :: List.replicate N 0)
        (fun k l => List.zipWith (· + ·) l (List.replicate (k + 1) 0 ++ l)) K) K)
        (List.replicate (K + 1) 0 ++ (fun K => Nat.rec (motive := fun _ => List ℕ)
          (1 :: List.replicate N 0)
          (fun k l => List.zipWith (· + ·) l (List.replicate (k + 1) 0 ++ l)) K) K) :=
    fun _ => rfl
  rw [Q_eq_pack w N hw _ ht0 hts (fun K => Nat.rec (motive := fun _ => ℕ) 1
      (fun K B => B + (2 ^ (w * (K + 1)) * B) % 2 ^ (w * (N + 1))) K) rfl (fun _ => rfl) N le_rfl,
    pack_digit w _ (fun x hx => lt_of_le_of_lt (tbl_entry_le N _ ht0 hts N x hx)
      (Nat.pow_lt_pow_right (by norm_num) hw)) n]
  exact strictPartitionCount_eq_rec N n hn


/-! ## Guard bits -/

theorem lt_of_testBit_false (x v : ℕ) (hx : x < 2 ^ (v + 1)) (hb : x.testBit v = false) :
    x < 2 ^ v := by
  rw [Nat.testBit_eq_decide_div_mod_eq] at hb
  have h2 : x / 2 ^ v < 2 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos v)]
    rw [pow_succ] at hx; linarith
  have h0 : x / 2 ^ v = 0 := by
    have hne : x / 2 ^ v % 2 ≠ 1 := by simpa using hb
    generalize x / 2 ^ v = y at h2 hne ⊢
    omega
  exact (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos v)).1 h0

theorem testBit_pack (w : ℕ) (l : List ℕ) (hl : ∀ x ∈ l, x < 2 ^ w) (i b : ℕ) (hb : b < w) :
    (l.foldr (fun a acc => a + 2 ^ w * acc) 0).testBit (w * i + b) = (l.getD i 0).testBit b := by
  rw [← pack_digit w l hl i, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.add_comm]
  simp [hb]

/-- The guard check: if no guard bit is set, every entry is below `2 ^ v`. -/
theorem entries_lt_of_guard (v : ℕ) (l : List ℕ) (hl : ∀ x ∈ l, x < 2 ^ (v + 1))
    (hG : (l.foldr (fun a acc => a + 2 ^ (v + 1) * acc) 0 &&&
      (List.replicate l.length (2 ^ v)).foldr (fun a acc => a + 2 ^ (v + 1) * acc) 0) = 0) :
    ∀ x ∈ l, x < 2 ^ v := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
  apply lt_of_testBit_false _ v (hl _ hx)
  have hrep : ∀ y ∈ List.replicate l.length (2 ^ v), y < 2 ^ (v + 1) := by
    intro y hy; rw [List.eq_of_mem_replicate hy]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have h1 := congrArg (fun z => z.testBit ((v + 1) * i + v)) hG
  simp only [Nat.testBit_land, Nat.zero_testBit] at h1
  rw [testBit_pack _ l hl i v (by omega), testBit_pack _ _ hrep i v (by omega)] at h1
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at h1
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate, if_pos (by omega)] at h1
  simpa [Nat.testBit_two_pow_self] using h1

section Guard

variable (v N : ℕ) (hv : 1 ≤ v) (t : ℕ → List ℕ) (h0 : t 0 = 1 :: List.replicate N 0)
  (hs : ∀ K, t (K + 1) = List.zipWith (· + ·) (t K) (List.replicate (K + 1) 0 ++ t K))
  (Q : ℕ → ℕ) (hQ0 : Q 0 = 1)
  (hQs : ∀ K < N, Q (K + 1) = Q K + (2 ^ ((v + 1) * (K + 1)) * Q K) % 2 ^ ((v + 1) * (N + 1)))
  (hG : ∀ K < N, (Q (K + 1) &&& (List.replicate (N + 1) (2 ^ v)).foldr
    (fun a acc => a + 2 ^ (v + 1) * acc) 0) = 0)
include hv h0 hs hQ0 hQs hG

theorem Q_eq_pack_guard : ∀ K ≤ N, Q K = (t K).foldr (fun a acc => a + 2 ^ (v + 1) * acc) 0 ∧
    ∀ x ∈ t K, x < 2 ^ v := by
  intro K hK
  induction K with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [hQ0, h0]; simp only [List.foldr_cons, pack_replicate_zero]; ring
    · intro x hx
      rw [h0] at hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact Nat.one_lt_two_pow (by omega)
      · rw [List.eq_of_mem_replicate hx]; exact Nat.two_pow_pos v
  | succ K ih =>
    obtain ⟨hQK, hbK⟩ := ih (by omega)
    have hl := tbl_length N t h0 hs K
    have hsbound : ∀ x ∈ List.replicate (K + 1) 0 ++ t K, x < 2 ^ v := by
      intro x hx
      rcases List.mem_append.1 hx with h | h
      · rw [List.eq_of_mem_replicate h]; exact Nat.two_pow_pos v
      · exact hbK x h
    have hsw : ∀ x ∈ List.replicate (K + 1) 0 ++ t K, x < 2 ^ (v + 1) := fun x hx =>
      lt_trans (hsbound x hx) (Nat.pow_lt_pow_right (by norm_num) (by omega))
    -- the new row is exact
    have hpack : Q (K + 1) = (t (K + 1)).foldr (fun a acc => a + 2 ^ (v + 1) * acc) 0 := by
      rw [hQs K (by omega), hQK, hs, List.zipWith_eq_zipWith_take_min]
      have hmin : min (t K).length (List.replicate (K + 1) 0 ++ t K).length = N + 1 := by
        simp [hl]
      rw [hmin, List.take_of_length_le (by omega),
        pack_add _ _ _ (by simp [hl]), pack_take _ (N + 1) _ hsw, pack_shift]
    -- entries of the new row are below `2 ^ (v + 1)` (sums of two entries below `2 ^ v`)
    have hw1 : ∀ x ∈ t (K + 1), x < 2 ^ (v + 1) := by
      intro x hx
      rw [hs] at hx
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
      rw [List.getElem_zipWith]
      simp only [List.length_zipWith, List.length_append, List.length_replicate, hl] at hi
      have ha := hbK ((t K)[i]'(by omega)) (List.getElem_mem _)
      have hb := hsbound ((List.replicate (K + 1) 0 ++ t K)[i]'(by simp [hl]; omega))
        (List.getElem_mem _)
      rw [pow_succ]; omega
    refine ⟨hpack, ?_⟩
    -- the guard check gives entries below `2 ^ v`
    have hG' := hG K (by omega)
    rw [hpack, ← tbl_length N t h0 hs (K + 1)] at hG'
    exact entries_lt_of_guard v _ hw1 hG'

end Guard

/-- One pass: if a guarded recursion (a failed guard gives `0`, and `0` stays `0`) is not `0`
at `N`, then every step before `N` is the normal step, and every guard passed. -/
theorem guard_pass (N H : ℕ) (Q : ℕ → ℕ) (S : ℕ → ℕ → ℕ) (hS0 : ∀ K, S 0 K = 0)
    (hQs : ∀ K, Q (K + 1) = if (S (Q K) K &&& H) == 0 then S (Q K) K else 0)
    (hN : Q N ≠ 0) :
    ∀ K < N, Q (K + 1) = S (Q K) K ∧ (S (Q K) K &&& H) = 0 := by
  -- first: no value up to `N` is `0`
  have hne : ∀ j ≤ N, Q (N - j) ≠ 0 := by
    intro j hj
    induction j with
    | zero => simpa using hN
    | succ j ih =>
      intro h0
      apply ih (by omega)
      rw [show N - j = (N - (j + 1)) + 1 by omega, hQs, h0, hS0]
      simp
  intro K hK
  have hK1 : Q (K + 1) ≠ 0 := by
    have := hne (N - (K + 1)) (by omega); rwa [show N - (N - (K + 1)) = K + 1 by omega] at this
  rw [hQs] at hK1 ⊢
  by_cases hg : (S (Q K) K &&& H) == 0
  · rw [if_pos hg]; exact ⟨rfl, by simpa using hg⟩
  · rw [if_neg hg] at hK1; exact absurd rfl hK1


/-- `q(n)` is slot `n` of the one-pass guarded table (slot width `v + 1`), when the result
at `N` is not `0`, i.e. every guard passed. -/
theorem strictPartitionCount_eq_guarded (v N n : ℕ) (hv : 1 ≤ v) (hn : n ≤ N)
    (hN : (Nat.rec (motive := fun _ => ℕ) 1 (fun K B => if ((B + (2 ^ ((v + 1) * (K + 1)) * B) % 2 ^ ((v + 1) * (N + 1))) &&& (List.replicate (N + 1) (2 ^ v)).foldr (fun a acc => a + 2 ^ (v + 1) * acc) 0) == 0 then B + (2 ^ ((v + 1) * (K + 1)) * B) % 2 ^ ((v + 1) * (N + 1)) else 0) N) ≠ 0) :
    strictPartitionCount n = ((Nat.rec (motive := fun _ => ℕ) 1 (fun K B => if ((B + (2 ^ ((v + 1) * (K + 1)) * B) % 2 ^ ((v + 1) * (N + 1))) &&& (List.replicate (N + 1) (2 ^ v)).foldr (fun a acc => a + 2 ^ (v + 1) * acc) 0) == 0 then B + (2 ^ ((v + 1) * (K + 1)) * B) % 2 ^ ((v + 1) * (N + 1)) else 0) N) / 2 ^ ((v + 1) * n)) % 2 ^ (v + 1) := by
  have ht0 : (fun K => Nat.rec (motive := fun _ => List ℕ) (1 :: List.replicate N 0) (fun k l => List.zipWith (· + ·) l (List.replicate (k + 1) 0 ++ l)) K) 0 = 1 :: List.replicate N 0 := rfl
  have hts : ∀ K, (fun K => Nat.rec (motive := fun _ => List ℕ) (1 :: List.replicate N 0) (fun k l => List.zipWith (· + ·) l (List.replicate (k + 1) 0 ++ l)) K) (K + 1) =
      List.zipWith (· + ·) ((fun K => Nat.rec (motive := fun _ => List ℕ) (1 :: List.replicate N 0) (fun k l => List.zipWith (· + ·) l (List.replicate (k + 1) 0 ++ l)) K) K)
        (List.replicate (K + 1) 0 ++ (fun K => Nat.rec (motive := fun _ => List ℕ) (1 :: List.replicate N 0) (fun k l => List.zipWith (· + ·) l (List.replicate (k + 1) 0 ++ l)) K) K) := fun _ => rfl
  have hpass := guard_pass N ((List.replicate (N + 1) (2 ^ v)).foldr
      (fun a acc => a + 2 ^ (v + 1) * acc) 0) (fun K => Nat.rec (motive := fun _ => ℕ) 1 (fun K B => if ((B + (2 ^ ((v + 1) * (K + 1)) * B) % 2 ^ ((v + 1) * (N + 1))) &&& (List.replicate (N + 1) (2 ^ v)).foldr (fun a acc => a + 2 ^ (v + 1) * acc) 0) == 0 then B + (2 ^ ((v + 1) * (K + 1)) * B) % 2 ^ ((v + 1) * (N + 1)) else 0) K)
    (fun B K => B + (2 ^ ((v + 1) * (K + 1)) * B) % 2 ^ ((v + 1) * (N + 1)))
    (fun K => by simp) (fun _ => rfl) hN
  obtain ⟨hQ, hb⟩ := Q_eq_pack_guard v N hv (fun K => Nat.rec (motive := fun _ => List ℕ) (1 :: List.replicate N 0) (fun k l => List.zipWith (· + ·) l (List.replicate (k + 1) 0 ++ l)) K) ht0 hts
    (fun K => Nat.rec (motive := fun _ => ℕ) 1 (fun K B => if ((B + (2 ^ ((v + 1) * (K + 1)) * B) % 2 ^ ((v + 1) * (N + 1))) &&& (List.replicate (N + 1) (2 ^ v)).foldr (fun a acc => a + 2 ^ (v + 1) * acc) 0) == 0 then B + (2 ^ ((v + 1) * (K + 1)) * B) % 2 ^ ((v + 1) * (N + 1)) else 0) K) rfl (fun K hK => (hpass K hK).1)
    (fun K hK => by rw [(hpass K hK).1]; exact (hpass K hK).2) N le_rfl
  rw [hQ, pack_digit (v + 1) _ (fun x hx => lt_trans (hb x hx)
    (Nat.pow_lt_pow_right (by norm_num) (by omega))) n]
  exact strictPartitionCount_eq_rec N n hn

theorem partitionCount_le_two_pow (n : ℕ) : partitionCount n ≤ 2 ^ n := by
  unfold partitionCount
  calc Fintype.card (Nat.Partition n) ≤ Fintype.card (Composition n) :=
        Fintype.card_le_of_surjective _ Nat.Partition.ofComposition_surj
    _ = 2 ^ (n - 1) := composition_card n
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- Horner iteration: if `P ≡ A + X P`, then `P ≡ A (1 + X + ⋯ + X^j) + X^(j+1) P`. -/
theorem geo_iter (A P X M : ℕ) (G : ℕ → ℕ) (hG0 : G 0 = 1)
    (hGs : ∀ j, G (j + 1) = (1 + X * G j) % M) (h : P ≡ A + X * P [MOD M]) :
    ∀ j, P ≡ A * G j + X ^ (j + 1) * P [MOD M] := by
  intro j
  induction j with
  | zero => simpa [hG0] using h
  | succ j ih =>
    have step : P ≡ A + X * (A * G j + X ^ (j + 1) * P) [MOD M] :=
      h.trans (Nat.ModEq.add_left _ (Nat.ModEq.mul_left _ ih))
    refine step.trans ?_
    have e : A + X * (A * G j + X ^ (j + 1) * P) =
        A * (1 + X * G j) + X ^ (j + 1 + 1) * P := by ring
    rw [e, hGs]
    exact Nat.ModEq.add_right _ (Nat.ModEq.mul_left _ (Nat.mod_modEq _ _).symm)

section PackP

variable (w N : ℕ) (hw : N < w) (pr : ℕ → List ℕ)
  (hpr : ∀ K, pr K = Nat.rec (motive := fun _ => List ℕ) (1 :: List.replicate N 0)
    (fun k old => (Nat.rec (motive := fun _ => List ℕ) []
      (fun i r => (old.getD i 0 + if k + 1 ≤ i then r.getD k 0 else 0) :: r) (N + 1)).reverse) K)
include hpr

theorem pr_length (K : ℕ) : (pr K).length = N + 1 := by rw [hpr]; exact (prow_spec N K).1

theorem pr_getD (K i : ℕ) (hi : i ≤ N) : (pr K).getD i 0 =
    (Finset.univ.filter (fun p : i.Partition => ∀ j ∈ p.parts, j ≤ K)).card := by
  rw [hpr]; exact (prow_spec N K).2 i hi

include hw in
theorem pr_entry_lt (K x : ℕ) (hx : x ∈ pr K) : x < 2 ^ w := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
  have hlen := pr_length N pr hpr K
  have h := pr_getD N pr hpr K i (by omega)
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at h
  rw [h]
  calc _ ≤ (Finset.univ : Finset i.Partition).card := Finset.card_filter_le _ _
    _ = partitionCount i := by rw [Finset.card_univ]; rfl
    _ ≤ 2 ^ i := partitionCount_le_two_pow i
    _ < 2 ^ w := Nat.pow_lt_pow_right (by norm_num) (by omega)

/-- The list identity behind the packed step: `new = old + shift (K+1) new`, truncated. -/
theorem pr_succ_eq (K : ℕ) : pr (K + 1) =
    List.zipWith (· + ·) (pr K) ((List.replicate (K + 1) 0 ++ pr (K + 1)).take (N + 1)) := by
  apply List.ext_getElem
  · simp [pr_length N pr hpr]
  · intro i h1 h2
    have hi : i ≤ N := by rw [pr_length N pr hpr] at h1; omega
    have e1 := pr_getD N pr hpr (K + 1) i hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some] at e1
    rw [e1, List.getElem_zipWith, List.getElem_take, bounded_succ]
    have e0 := pr_getD N pr hpr K i hi
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by rw [pr_length N pr hpr]; omega), Option.getD_some] at e0
    rw [e0]
    congr 1
    by_cases hk : K + 1 ≤ i
    · rw [if_pos hk, List.getElem_append_right (by simp; omega)]
      have e2 := pr_getD N pr hpr (K + 1) (i - (K + 1)) (by omega)
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by rw [pr_length N pr hpr]; omega), Option.getD_some] at e2
      simp only [List.length_replicate]
      rw [e2]
    · rw [if_neg hk, List.getElem_append_left (by simp; omega)]
      simp

include hw in
theorem P_eq_pack (P : ℕ → ℕ) (hP0 : P 0 = 1)
    (hPs : ∀ K, P (K + 1) = (P K * Nat.rec (motive := fun _ => ℕ) 1
      (fun _ g => (1 + 2 ^ (w * (K + 1)) * g) % 2 ^ (w * (N + 1))) (N / (K + 1)))
        % 2 ^ (w * (N + 1))) :
    ∀ K, P K = (pr K).foldr (fun a acc => a + 2 ^ w * acc) 0 := by
  intro K
  induction K with
  | zero =>
    rw [hP0, hpr]
    show 1 = (1 :: List.replicate N 0).foldr (fun a acc => a + 2 ^ w * acc) 0
    simp only [List.foldr_cons, pack_replicate_zero]; ring
  | succ K ih =>
    set M := 2 ^ (w * (N + 1)) with hM
    set X := 2 ^ (w * (K + 1)) with hX
    set A := (pr K).foldr (fun a acc => a + 2 ^ w * acc) 0
    set Pk := (pr (K + 1)).foldr (fun a acc => a + 2 ^ w * acc) 0 with hPk
    have hbound : ∀ x ∈ List.replicate (K + 1) 0 ++ pr (K + 1), x < 2 ^ w := by
      intro x hx
      rcases List.mem_append.1 hx with h | h
      · rw [List.eq_of_mem_replicate h]; exact Nat.two_pow_pos w
      · exact pr_entry_lt w N hw pr hpr (K + 1) x h
    have hP : Pk = A + (X * Pk) % M := by
      rw [hPk]
      conv_lhs => rw [pr_succ_eq N pr hpr K]
      rw [pack_add w _ _ (by simp [pr_length N pr hpr]), pack_take w (N + 1) _ hbound,
        pack_shift]
    have hPlt : Pk < M := by
      have := pack_lt w (pr (K + 1)) (fun x hx => pr_entry_lt w N hw pr hpr (K + 1) x hx)
      rwa [pr_length N pr hpr] at this
    have hmod : Pk ≡ A + X * Pk [MOD M] := by
      conv_lhs => rw [hP]
      exact Nat.ModEq.add_left _ (Nat.mod_modEq _ _)
    have hit := geo_iter A Pk X M (fun j => Nat.rec (motive := fun _ => ℕ) 1
      (fun _ g => (1 + X * g) % M) j) rfl (fun _ => rfl) hmod (N / (K + 1))
    have hdvd : M ∣ X ^ (N / (K + 1) + 1) := by
      rw [hM, hX, ← pow_mul]
      apply Nat.pow_dvd_pow
      have : N + 1 ≤ (K + 1) * (N / (K + 1) + 1) := Nat.lt_mul_div_succ N (by omega)
      calc w * (N + 1) ≤ w * ((K + 1) * (N / (K + 1) + 1)) := Nat.mul_le_mul_left _ this
        _ = w * (K + 1) * (N / (K + 1) + 1) := by ring
    have hzero : X ^ (N / (K + 1) + 1) * Pk ≡ 0 [MOD M] :=
      (Nat.modEq_zero_iff_dvd.2 (Dvd.dvd.mul_right hdvd Pk))
    have hfin := hit.trans (Nat.ModEq.add_left _ hzero)
    rw [add_zero] at hfin
    rw [hPs, ih]
    exact Eq.trans (hfin.symm : _ % M = Pk % M) (Nat.mod_eq_of_lt hPlt)

end PackP

/-- `p(n)` is slot `n` of the packed p-table. -/
theorem partitionCount_eq_packed (w N n : ℕ) (hw : N < w) (hn : n ≤ N) :
    partitionCount n = ((Nat.rec (motive := fun _ => ℕ) 1
      (fun K B => (B * Nat.rec (motive := fun _ => ℕ) 1
        (fun _ g => (1 + 2 ^ (w * (K + 1)) * g) % 2 ^ (w * (N + 1))) (N / (K + 1)))
          % 2 ^ (w * (N + 1))) N) / 2 ^ (w * n)) % 2 ^ w := by
  have hpr : ∀ K, (fun K => Nat.rec (motive := fun _ => List ℕ) (1 :: List.replicate N 0)
      (fun k old => (Nat.rec (motive := fun _ => List ℕ) []
        (fun i r => (old.getD i 0 + if k + 1 ≤ i then r.getD k 0 else 0) :: r) (N + 1)).reverse)
      K) K = Nat.rec (motive := fun _ => List ℕ) (1 :: List.replicate N 0)
      (fun k old => (Nat.rec (motive := fun _ => List ℕ) []
        (fun i r => (old.getD i 0 + if k + 1 ≤ i then r.getD k 0 else 0) :: r) (N + 1)).reverse) K :=
    fun _ => rfl
  rw [P_eq_pack w N hw _ hpr (fun K => Nat.rec (motive := fun _ => ℕ) 1
      (fun K B => (B * Nat.rec (motive := fun _ => ℕ) 1
        (fun _ g => (1 + 2 ^ (w * (K + 1)) * g) % 2 ^ (w * (N + 1))) (N / (K + 1)))
          % 2 ^ (w * (N + 1))) K) rfl (fun _ => rfl) N,
    pack_digit w _ (fun x hx => pr_entry_lt w N hw _ hpr N x hx) n]
  exact partitionCount_eq_rec N n hn

/-- Evaluate the truncated geometric factor by a single natural division. -/
theorem geom_fast (X M j : ℕ) (hx : 1 < X) (hm : 1 < M) :
    Nat.rec (motive := fun _ => ℕ) 1 (fun _ g => (1 + X * g) % M) j =
      ((X^(j+1)-1)/(X-1)) % M := by
  let F (t : ℕ) := Nat.rec (motive := fun _ => ℕ) 1 (fun _ g => 1 + X*g) t
  have series (t : ℕ) : F t * (X-1) + 1 = X^(t+1) := by
    induction t with
    | zero => change 1 * (X-1) + 1 = X^1; simp; omega
    | succ t ih =>
      change (1+X*F t)*(X-1)+1 = X^(t+1+1)
      rw [pow_succ, ← ih]
      have h : X-1+1 = X := by omega
      calc
        _ = F t*(X-1)*X + (X-1+1) := by ring
        _ = _ := by rw [h]; ring
  have reduction (t : ℕ) :
      Nat.rec (motive := fun _ => ℕ) 1 (fun _ g => (1 + X*g) % M) t = F t % M := by
    induction t with
    | zero => exact (Nat.mod_eq_of_lt hm).symm
    | succ t ih =>
      change (1+X*_ ) % M = (1+ X*F t) % M
      rw [ih]
      exact Nat.ModEq.add_left 1 (Nat.ModEq.mul_left X (Nat.mod_modEq _ _))
  rw [reduction, ← series, Nat.add_sub_cancel, Nat.mul_div_cancel _ (by omega)]

theorem partitionCount_eq_fast (w N n : ℕ) (hw : N < w) (hn : n ≤ N) :
    partitionCount n = ((Nat.rec (motive := fun _ => ℕ) 1 (fun K B =>
      (B * (((2 ^ (w*(K+1)*(N/(K+1)+1))-1) / (2 ^ (w*(K+1))-1)) % 2 ^ (w*(N+1))))
        % 2 ^ (w*(N+1))) N) / 2^(w*n)) % 2^w := by
  rw [partitionCount_eq_packed w N n hw hn]
  have hwpos : 0 < w := by omega
  have factor (K : ℕ) :
      Nat.rec (motive := fun _ => ℕ) 1
        (fun _ g => (1+2^(w*(K+1))*g) % 2^(w*(N+1))) (N/(K+1)) =
        ((2^(w*(K+1)*(N/(K+1)+1))-1)/(2^(w*(K+1))-1)) % 2^(w*(N+1)) := by
    rw [geom_fast, ← pow_mul] <;> apply Nat.one_lt_two_pow <;> positivity
  simp_rw [factor]

/-! ## The finite range `8 ≤ n ≤ 1000`, checked by the kernel -/

/-- From the Boolean range check to the three claims, for each `8 ≤ n ≤ N`. -/
theorem nondiv_of_check (w N : ℕ) (hw : N < w)
    (h : (List.range (N + 1)).all (fun n => n ≤ 7 ||
      (((Nat.rec (motive := fun _ => ℕ) 1
        (fun K B => (B * (((2^(w*(K+1)*(N/(K+1)+1))-1)/(2^(w*(K+1))-1)) % 2^(w*(N+1))))
            % 2 ^ (w * (N + 1))) N) / 2 ^ (w * n)) % 2 ^ w %
        (((Nat.rec (motive := fun _ => ℕ) 1
          (fun K B => B + (2 ^ (w * (K + 1)) * B) % 2 ^ (w * (N + 1))) N) / 2 ^ (w * n)) % 2 ^ w)
          != 0 &&
       ((((Nat.rec (motive := fun _ => ℕ) 1
        (fun K B => (B * (((2^(w*(K+1)*(N/(K+1)+1))-1)/(2^(w*(K+1))-1)) % 2^(w*(N+1))))
            % 2 ^ (w * (N + 1))) N) / 2 ^ (w * n)) % 2 ^ w) - 1) %
        (((Nat.rec (motive := fun _ => ℕ) 1
          (fun K B => B + (2 ^ (w * (K + 1)) * B) % 2 ^ (w * (N + 1))) N) / 2 ^ (w * n)) % 2 ^ w)
          != 0 &&
       ((((Nat.rec (motive := fun _ => ℕ) 1
        (fun K B => (B * (((2^(w*(K+1)*(N/(K+1)+1))-1)/(2^(w*(K+1))-1)) % 2^(w*(N+1))))
            % 2 ^ (w * (N + 1))) N) / 2 ^ (w * n)) % 2 ^ w) + 1) %
        (((Nat.rec (motive := fun _ => ℕ) 1
          (fun K B => B + (2 ^ (w * (K + 1)) * B) % 2 ^ (w * (N + 1))) N) / 2 ^ (w * n)) % 2 ^ w)
          != 0)) = true)
    (n : ℕ) (h7 : 7 < n) (hn : n ≤ N) :
    ¬ strictPartitionCount n ∣ partitionCount n ∧
    ¬ strictPartitionCount n ∣ partitionCount n - 1 ∧
    ¬ strictPartitionCount n ∣ partitionCount n + 1 := by
  rw [List.all_eq_true] at h
  have hb := h n (List.mem_range.2 (by omega))
  rw [← strictPartitionCount_eq_packed w N n hw hn, ← partitionCount_eq_fast w N n hw hn] at hb
  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, bne_iff_ne, ne_eq] at hb
  rcases hb with hb | hb
  · omega
  · simp only [Nat.dvd_iff_mod_eq_zero]
    exact ⟨hb.1.1, hb.1.2, hb.2⟩

theorem nondiv_le (n : ℕ) (h7 : 7 < n) (hn : n ≤ 1000) :
    ¬ strictPartitionCount n ∣ partitionCount n ∧
    ¬ strictPartitionCount n ∣ partitionCount n - 1 ∧
    ¬ strictPartitionCount n ∣ partitionCount n + 1 :=
  nondiv_of_check (1000 + 1) 1000 (by norm_num) (by decide +kernel) n h7 hn


open Finset

/-- For each target, use a fresh large summand whose eligible divisors all
exceed the remainder. Each target may use a different collection of values. -/
theorem descent (Q : ℕ → Prop) (B L U cap : ℕ) (positive : 0 < B)
    (base : ∀ n, L ≤ n → n ≤ U → ∃ T : Finset ℕ,
      (∀ s ∈ T, B ≤ s ∧ Q s) ∧
      (∀ x ∈ T, ∀ y ∈ T, x ≠ y → ¬ x ∣ y) ∧ (∑ s ∈ T, s) = n)
    (tail : ∀ n, U < n → n ≤ cap → ∃ a r : ℕ, n = a+r ∧ B ≤ a ∧ Q a ∧ L ≤ r ∧ r < a ∧
      ∀ s, B ≤ s → Q s → s ∣ a → r < s) :
    ∀ n, L ≤ n → n ≤ cap → ∃ T : Finset ℕ,
      (∀ s ∈ T, B ≤ s ∧ Q s) ∧
      (∀ x ∈ T, ∀ y ∈ T, x ≠ y → ¬ x ∣ y) ∧ (∑ s ∈ T, s) = n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn hcap
    by_cases hsmall : n ≤ U
    · exact base n hn hsmall
    obtain ⟨a,r,eq,ab,qa,rl,ra,clean⟩ := tail n (by omega) hcap
    obtain ⟨T,good,anti,hs⟩ := ih r (by omega) rl (by omega)
    have bound {s : ℕ} (mem : s ∈ T) : s ≤ r := by
      rw [← hs]
      exact single_le_sum (f := fun i : ℕ => i) (fun _ _ => Nat.zero_le _) mem
    have fresh : a ∉ T := fun mem => (Nat.not_le_of_gt ra) (bound mem)
    refine ⟨insert a T, ?_, ?_, by rw [sum_insert fresh, hs, eq]⟩
    · intro s h
      rcases mem_insert.mp h with rfl | h
      · exact ⟨ab,qa⟩
      · exact good s h
    · intro x hx y hy ne
      rcases mem_insert.mp hx with hxa | hxT <;> rcases mem_insert.mp hy with hya | hyT
      · exact False.elim (ne (hxa.trans hya.symm))
      · rw [hxa]
        intro dv
        have := Nat.le_of_dvd (lt_of_lt_of_le positive (good y hyT).1) dv
        have := bound hyT
        omega
      · rw [hya]
        exact fun dv => (Nat.not_lt_of_ge (bound hxT)) (clean x (good x hxT).1 (good x hxT).2 dv)
      · exact anti x hxT y hyT ne

/-- Read successive intervals [a + L, 2a - 1]; only an overlapping
interval may raise the upper endpoint. -/
theorem window_union (L n : ℕ) (xs : List ℕ) : ∀ u, n ≤ xs.foldl
    (fun v a => if a+L ≤ v+1 then max v (2*a-1) else v) u →
    n ≤ u ∨ ∃ a ∈ xs, a+L ≤ n ∧ n < 2*a := by
  induction xs with
  | nil => intro u hn; exact Or.inl hn
  | cons a rest ih =>
    intro u hn
    obtain small | ⟨b, hb, fits⟩ := ih _ hn
    · by_cases h : a+L ≤ u+1
      · simp only [if_pos h] at small
        by_cases done : n ≤ u
        · exact Or.inl done
        · exact Or.inr ⟨a, List.mem_cons_self .., by omega, by omega⟩
      · simpa only [if_neg h] using Or.inl (b := ∃ b ∈ a::rest, b+L ≤ n ∧ n < 2*b) small
    · exact Or.inr ⟨b, List.mem_cons_of_mem a hb, fits⟩

/-- A divisor test using two bounded residues, followed by exact cancellation. -/
theorem residual_iff (q y M : ℕ) (hM : 0 < M) :
    let d := (q % M).gcd M
    (¬ q ∣ y) ↔ (d ∣ y % M → ¬ q / d ∣ y / d) := by
  dsimp only
  rw [← Nat.gcd_rec M q, Nat.gcd_comm M q]
  let d := q.gcd M
  have dq : d ∣ q := Nat.gcd_dvd_left _ _
  have dm : d ∣ M := Nat.gcd_dvd_right _ _
  have pos : 0 < d := Nat.gcd_pos_of_pos_right _ hM
  change (¬ q ∣ y) ↔ (d ∣ y % M → ¬ q / d ∣ y / d)
  rw [Nat.dvd_mod_iff dm]
  constructor
  · intro hn dy h
    apply hn
    have hy := (Nat.div_dvd_iff_dvd_mul dq pos).mp h
    simpa only [Nat.mul_div_cancel' dy] using hy
  · intro h hy
    exact h (dvd_trans dq hy) (Nat.div_dvd_div dq hy)

/-- The three original tests are equivalent to checking just the surviving offsets. -/
theorem triple_iff (P Q M : ℕ) (hP : 0 < P) (hM : 0 < M) :
    (¬ Q ∣ P ∧ ¬ Q ∣ P-1 ∧ ¬ Q ∣ P+1) ↔
      ∀ k : Fin 3, let y := P-1+k.val
        let d := (Q % M).gcd M
        d ∣ y % M → ¬ Q / d ∣ y / d := by
  constructor
  · intro h k
    apply (residual_iff _ _ _ hM).mp
    fin_cases k
    · exact h.2.1
    · change ¬ Q ∣ P - 1 + 1
      rw [Nat.sub_add_cancel hP]
      exact h.1
    · change ¬ Q ∣ P - 1 + 2
      rw [show P-1+2 = P+1 by omega]
      exact h.2.2
  · intro h
    have each (k : Fin 3) := (residual_iff _ _ _ hM).mpr (h k)
    have low := each 0
    have mid := each 1
    have high := each 2
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, Nat.add_zero] at low mid high
    exact ⟨by convert mid using 2; omega, low, by convert high using 2; omega⟩


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem bounded_base (n : ℕ) (lo : 20301 ≤ n) (hi : n ≤ 10441840193277271329791737218536447) :
    ∃ T : Finset ℕ, (∀ s ∈ T, 1000 ≤ s ∧ ∃ m : ℕ, 0 < m ∧ s = strictPartitionCount m) ∧
      (∀ x ∈ T, ∀ y ∈ T, x ≠ y → ¬ x ∣ y) ∧ (∑ s ∈ T, s) = n := by
  let seed : List ℕ := [1113, 1260, 1426, 1610, 1816, 2048, 2304, 2590, 2910, 3264, 3658, 4097, 4582, 5120, 5718, 6378, 7108, 7917, 8808, 10880, 12076, 13394, 14848, 16444, 18200, 20132, 22250, 27130, 29927, 32992, 36352, 44046, 48446, 53250, 58499, 64234, 70488, 77312, 84756, 92864, 101698, 111322, 121792, 133184, 145578, 159046, 173682, 189586, 225585, 245920, 267968, 291874]
  let ms : List ℕ := [124, 133, 142, 151, 161, 171, 181, 192, 203, 214, 225, 237, 249, 261, 274, 287, 300, 314, 328, 342, 356, 371, 386, 401, 417, 433, 449, 466, 483, 500, 517, 535, 553, 571, 590, 608, 627, 646, 665, 685, 705, 726, 747, 768, 789, 811, 833, 855, 878, 900, 923, 945, 969, 993, 1017, 1040, 1065, 1090, 1116, 1142, 1168, 1194, 1221, 1248, 1274, 1302, 1330, 1358, 1386, 1415, 1444, 1473, 1503, 1533, 1562, 1591, 1622, 1653, 1684, 1716, 1748, 1779, 1812, 1845, 1876, 1909, 1943, 1976, 2010, 2045, 2080, 2114, 2149, 2185, 2200]
  let word : ℕ := Nat.rec (motive := fun _ => ℕ) 1 (fun K B => if ((B + (2 ^ ((114 + 1) * (K + 1)) * B) % 2 ^ ((114 + 1) * (2200 + 1))) &&& (List.replicate (2200 + 1) (2 ^ 114)).foldr (fun a acc => a + 2 ^ (114 + 1) * acc) 0) == 0 then B + (2 ^ ((114 + 1) * (K + 1)) * B) % 2 ^ ((114 + 1) * (2200 + 1)) else 0) 2200
  let d (j : ℕ) := word / 2 ^ (115*j) % 2 ^ 115
  have guard : word ≠ 0 := by decide +kernel
  have digit (j : ℕ) (hj : j ≤ 2200) : strictPartitionCount j = d j :=
    strictPartitionCount_eq_guarded 114 2200 j (by decide) hj guard
  let as : List ℕ := [
    2974400, 5802008, 11086968, 20792120, 40982540, 79229676, 150473568, 299016608, 583473184,
    1119555488, 2114965120, 4163989458, 8067955712, 15400801856, 30542758738, 59656252987,
    114872472064, 229184682870, 450666531450, 874201606890, 1674182409148, 3313846677248,
    6474200116480, 12493440408000, 24867441720078, 48880168540672, 94946245905984,
    189885350594524, 375210787343946, 732986521245024, 1416439699443142, 2813432400120490,
    5526916854475456, 10743948315198452, 21436830186242063, 40841012493194682, 79850366709300780,
    154605520700705120, 296566421243219584, 583064907329563392, 1135514750730008498,
    2264099687978533120, 4471243846198231222, 8749076605552831010, 16969018471958594188,
    33658554486099838720, 66167480560136966222, 128959762210836804066, 256797752929721054144,
    492244122149966911170, 963936587035181776118, 1819432729601465049152, 3608821796790641279424,
    7099574931537767204250, 13856795874852965173664, 26114238731192528551360,
    51603947016881466592794, 101187082100171176234122, 202217398295763141057824,
    400974246199817583894742, 789100539835396883939358, 1541605650408283495393522,
    3067246836584607264472876, 6057832938243693897513760, 11587856205784909926984270,
    23133214031490814970843946, 45849222558168996948474368, 90237721732402250231404576,
    176399164530456252077526460, 350741742631318772385582430, 692632149839450032033159272,
    1358720023681540379617941670, 2709554728070710803686491766, 5367264525360833458692206290,
    10328159113745691088153035474, 19757024974832794901430315808, 39271931648224901602532811744,
    77564687783000975558719979596, 152245211464478503515661835584,
    303468944818089580243371962908, 601119078496968105240844836482,
    1158781895436941400454219080758, 2316170889443722154127194213952,
    4601150472448384542496370017042, 8720147493887027887169515613502,
    17125122235360043981237309102106, 34122295129109726757172201549258,
    66250476361820092866089672434520, 130500758305232545022214498828800,
    260708483130336361445704424770194, 517825573584622961930450020039098,
    1003110675762233960017588378359296, 1970615048942618101201014150229370,
    3924616451803206622397933581141549, 5220920096638635664895868609268224]
  let small (s : ℕ) := s ∈ seed ++ as
  have lookup : ms.map d = as := by decide +kernel
  have limits : ∀ m ∈ ms, 0 < m ∧ m ≤ 2200 := by decide +kernel
  have seedGood : seed.Nodup ∧ (∀ x ∈ seed, 1000 ≤ x ∧ x ∈ (List.range 95).map (fun j => d (j+1))) ∧
      (∀ x ∈ seed, ∀ y ∈ seed, x ≠ y → y % x ≠ 0) ∧
      (((seed.foldr (fun a b => b ||| b <<< a) 1) >>> 20301) % 2^3048881 = 2^3048881-1) := by decide +kernel
  have fit : (as.foldl (fun v a => if a+20301 ≤ v+1 then max v (2*a-1) else v) 3069181) = 10441840193277271329791737218536447 := by decide +kernel
  have validate : as.all (fun a => decide (1000 ≤ a) &&
      (seed ++ as).all (fun s => decide (1000 ≤ s → s < a → ¬ s ∣ a))) = true := by decide +kernel
  have result := descent small 1000 20301 3069181 10441840193277271329791737218536447 (by decide) (fun t tl tu => ?_) (fun t tl tu => ?_) n lo hi
  · obtain ⟨T, good, anti, total⟩ := result
    refine ⟨T, ?_, anti, total⟩
    intro x hx
    obtain ⟨bound,member⟩ := good x hx
    refine ⟨bound, ?_⟩
    rcases List.mem_append.mp member with hs | ha
    · obtain ⟨j,hj,eq⟩ := List.mem_map.mp (seedGood.2.1 x hs).2
      exact ⟨j+1,by omega,eq.symm.trans (digit (j+1) (by have := List.mem_range.mp hj; omega)).symm⟩
    · rw [← lookup] at ha
      obtain ⟨m,hm,eq⟩ := List.mem_map.mp ha
      exact ⟨m,(limits m hm).1,eq.symm.trans (digit m (limits m hm).2).symm⟩
  · obtain ⟨T,hT,hs⟩ := (testBit_foldr seed seedGood.1 t).mp
      (testBit_of_mask _ _ _ seedGood.2.2.2 t tl (by omega))
    have member {x : ℕ} (hx : x ∈ T) := List.mem_toFinset.mp (hT hx)
    refine ⟨T, ?_, fun x hx y hy ne dv =>
      seedGood.2.2.1 x (member hx) y (member hy) ne (Nat.mod_eq_zero_of_dvd dv), hs⟩
    intro x hx
    exact ⟨(seedGood.2.1 x (member hx)).1, List.mem_append.mpr (Or.inl (member hx))⟩
  · obtain old | ⟨a,ha,lb,ub⟩ := window_union 20301 t as 3069181 (fit.symm ▸ tu)
    · omega
    have test := List.all_eq_true.mp validate a ha
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at test
    refine ⟨a,t-a,by omega,test.1,List.mem_append.mpr (Or.inr ha),by omega,by omega,?_⟩
    intro s hs member divides
    by_contra! smallDiv
    exact test.2 s member hs (by omega) divides

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a000009.main := by
  intro tail residual
  refine ⟨?_, fun n hn => ?_⟩
  · intro n hn
    by_cases hsmall : n < 20301
    · obtain ⟨T,g,anti,total⟩ := H1_le n hn (by omega)
      obtain ⟨k,a,ga,hs,ha⟩ := rep_of_finset T g anti
      exact ⟨k,a,ga,hs.trans total,ha⟩
    obtain ⟨T,g,anti,total⟩ := descent (fun a => ∃ m : ℕ, 0 < m ∧ a = strictPartitionCount m)
      1000 20301 10441840193277271329791737218536447 n (by decide) bounded_base
      (fun m hm _ => tail m hm) n (by omega) le_rfl
    obtain ⟨k,a,ga,hs,ha⟩ := rep_of_finset T (fun x hx => (g x hx).2) anti
    exact ⟨k,a,ga,hs.trans total,ha⟩
  · by_cases hb : n ≤ 1000
    · exact nondiv_le n hn hb
    · exact (triple_iff _ _ _ (partitionCount_pos n) (by decide : 0 < 9338866572734899200)).mpr
        (residual n (by omega))

end OMA.R_oeis_a000009_R10
