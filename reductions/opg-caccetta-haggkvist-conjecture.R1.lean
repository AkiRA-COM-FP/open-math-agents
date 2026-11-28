import OMAStatements.S_opg_caccetta_haggkvist_conjecture

/-!
# Caccetta–Häggkvist: all finite Cayley subdigraphs

This reduction proves the conjectured cycle bound for every loopless digraph
containing a Cayley subdigraph of an arbitrary finite group, with at least `r`
connection elements. The connection set need not generate the group, and the
subdigraph need not be spanning. The unrestricted conjecture is not proved:
H1 and H2 retain the remaining cases with degree bounds two and at least three.

The proof gives reusable results in increasing order of specialization:
* Scherk–Kemperman for finite subsets of any group, including infinite groups;
* a short nonempty identity-product word in any finite group;
* extraction of a simple directed cycle from a nonempty closed walk;
* the sharp ceiling bound for embedded Cayley subdigraphs.

Mathematical sources: Hamidoune's Cayley-graph case, as presented in
M. B. Nathanson, The Caccetta–Häggkvist conjecture and additive number theory,
arXiv:math/0603469 (2006), Theorems 5–7.
https://arxiv.org/abs/math/0603469
The two noncommutative e-transforms use Mathlib's existing ETransform API.
This is a formalization of classical mathematics, not a new resolution of CH.
-/

-- Credit: @qtyan0721
-- Agent: codex
-- Model: gpt-6.2-astra

namespace OMA.R_opg_caccetta_haggkvist_conjecture_R1

namespace Kemperman

open Finset MulOpposite
open scoped Pointwise

variable {G : Type*} [Group G] [DecidableEq G]

private lemma good_subsets {p : Finset G × Finset G}
    (hp : 1 ∈ p.1 ∧ 1 ∈ p.2 ∧ ∀ a ∈ p.1, ∀ b ∈ p.2, a * b = 1 → a = 1) :
    p.1 ⊆ p.1 * p.2 ∧ p.2 ⊆ p.1 * p.2 := by
  constructor
  · intro a ha
    simpa only [mul_one] using mul_mem_mul ha hp.2.1
  · intro b hb
    simpa only [one_mul] using mul_mem_mul hp.1 hb

private lemma good_left {A B : Finset G}
    (h : 1 ∈ A ∧ 1 ∈ B ∧ ∀ a ∈ A, ∀ b ∈ B, a * b = 1 → a = 1)
    {x : G} (hxA : x ∈ A) (hxB : x ∈ B) (hx : x ≠ 1) :
    1 ∈ (mulETransformLeft x⁻¹ (A, B)).1 ∧
      1 ∈ (mulETransformLeft x⁻¹ (A, B)).2 ∧
      ∀ a ∈ (mulETransformLeft x⁻¹ (A, B)).1,
        ∀ b ∈ (mulETransformLeft x⁻¹ (A, B)).2, a * b = 1 → a = 1 := by
  have hA : 1 ∈ A := h.1
  have hB : 1 ∈ B := h.2.1
  change 1 ∈ A ∩ op x⁻¹ • A ∧ 1 ∈ B ∪ x⁻¹⁻¹ • B ∧ _
  refine ⟨mem_inter.mpr ⟨hA, ?_⟩, mem_union_left _ hB, ?_⟩
  · exact mem_smul_finset.mpr ⟨x, hxA, by simp⟩
  · intro a ha b hb hab
    obtain ⟨haA, haT⟩ := mem_inter.mp ha
    rcases mem_union.mp hb with hbB | hbT
    · exact h.2.2 a haA b hbB hab
    · obtain ⟨c, hcB, he⟩ := mem_smul_finset.mp hbT
      have hac : a * (x * c) = 1 := by simpa [← he] using hab
      obtain ⟨d, hdA, hda⟩ := mem_smul_finset.mp haT
      have haxA : a * x ∈ A := by simpa [← hda] using hdA
      have hax : a * x = 1 := h.2.2 (a * x) haxA c hcB (by simpa [mul_assoc] using hac)
      have ha1 : a = 1 := h.2.2 a haA x hxB hax
      exact (hx (by simpa [ha1] using hax)).elim

private lemma good_right {A B : Finset G}
    (h : 1 ∈ A ∧ 1 ∈ B ∧ ∀ a ∈ A, ∀ b ∈ B, a * b = 1 → a = 1)
    {x : G} (hxA : x ∈ A) (hxB : x ∈ B) (hx : x ≠ 1) :
    1 ∈ (mulETransformRight x (A, B)).1 ∧
      1 ∈ (mulETransformRight x (A, B)).2 ∧
      ∀ a ∈ (mulETransformRight x (A, B)).1,
        ∀ b ∈ (mulETransformRight x (A, B)).2, a * b = 1 → a = 1 := by
  have hA : 1 ∈ A := h.1
  have hB : 1 ∈ B := h.2.1
  change 1 ∈ A ∪ op x • A ∧ 1 ∈ B ∩ x⁻¹ • B ∧ _
  refine ⟨mem_union_left _ hA, mem_inter.mpr ⟨hB, ?_⟩, ?_⟩
  · exact mem_smul_finset.mpr ⟨x, hxB, by simp⟩
  · intro a ha b hb hab
    obtain ⟨hbB, hbT⟩ := mem_inter.mp hb
    rcases mem_union.mp ha with haA | haT
    · exact h.2.2 a haA b hbB hab
    · obtain ⟨c, hcA, hca⟩ := mem_smul_finset.mp haT
      obtain ⟨d, hdB, hdb⟩ := mem_smul_finset.mp hbT
      have hxbB : x * b ∈ B := by simpa [← hdb] using hdB
      have hc : c * (x * b) = 1 := by simpa [← hca, mul_assoc] using hab
      have hc1 : c = 1 := h.2.2 c hcA (x * b) hxbB hc
      have hxb : x * b = 1 := by simpa [hc1] using hc
      exact (hx (h.2.2 x hxA b hbB hxb)).elim

private lemma transform_cards (A B : Finset G) (x : G) :
    (mulETransformLeft x⁻¹ (A, B)).1.card +
      (mulETransformLeft x⁻¹ (A, B)).2.card +
      ((mulETransformRight x (A, B)).1.card +
        (mulETransformRight x (A, B)).2.card) =
      A.card + B.card + (A.card + B.card) := by
  have ha : (A ∩ op x⁻¹ • A).card = (A ∩ op x • A).card := by
    rw [← card_smul_finset (op x) (A ∩ op x⁻¹ • A), smul_finset_inter]
    simp only [op_inv, smul_inv_smul, inter_comm]
  have hb : (B ∩ x⁻¹ • B).card = (B ∩ x • B).card := by
    rw [← card_smul_finset x (B ∩ x⁻¹ • B), smul_finset_inter, smul_inv_smul,
      inter_comm]
  change (A ∩ op x⁻¹ • A).card + (B ∪ x⁻¹⁻¹ • B).card +
    ((A ∪ op x • A).card + (B ∩ x⁻¹ • B).card) = _
  rw [inv_inv, ha, hb, add_add_add_comm, card_inter_add_card_union,
    card_union_add_card_inter, card_smul_finset, card_smul_finset]
  omega

private lemma left_card_lt {A B : Finset G}
    (h : 1 ∈ A ∧ 1 ∈ B ∧ ∀ a ∈ A, ∀ b ∈ B, a * b = 1 → a = 1)
    {x : G} (hxB : x ∈ B) (hx : x ≠ 1) :
    (mulETransformLeft x⁻¹ (A, B)).1.card < A.card := by
  change (A ∩ op x⁻¹ • A).card < A.card
  apply card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨inter_subset_left, ?_⟩
  intro he
  have hsub : A ⊆ op x⁻¹ • A := by
    exact he.symm.subset.trans inter_subset_right
  have hEq : A = op x⁻¹ • A := eq_of_subset_of_card_le hsub (by simp)
  have hxi : x⁻¹ ∈ A := by
    rw [hEq]
    exact mem_smul_finset.mpr ⟨1, h.1, by simp⟩
  have hi1 : x⁻¹ = 1 := h.2.2 _ hxi x hxB (inv_mul_cancel x)
  exact hx (inv_eq_one.mp hi1)

/-- **Scherk–Kemperman.** If the identity has a unique representation in
`A * B`, then the product set has at least `|A| + |B| - 1` elements.
The ambient group may be infinite and need not be commutative. -/
theorem card_mul_ge_of_unique_one (A B : Finset G) (hA : 1 ∈ A) (hB : 1 ∈ B)
    (hu : ∀ a ∈ A, ∀ b ∈ B, a * b = 1 → a = 1) :
    A.card + B.card ≤ (A * B).card + 1 := by
  classical
  let C := A * B
  let F : Finset (Finset G × Finset G) :=
    (C.powerset ×ˢ C.powerset).filter fun p =>
      (1 ∈ p.1 ∧ 1 ∈ p.2 ∧ ∀ a ∈ p.1, ∀ b ∈ p.2, a * b = 1 → a = 1) ∧
        p.1 * p.2 ⊆ C
  have memF (p : Finset G × Finset G) :
      p ∈ F ↔
        (1 ∈ p.1 ∧ 1 ∈ p.2 ∧ ∀ a ∈ p.1, ∀ b ∈ p.2, a * b = 1 → a = 1) ∧
          p.1 * p.2 ⊆ C := by
    constructor
    · intro hp
      exact (mem_filter.mp hp).2
    · intro hp
      have hs := good_subsets hp.1
      exact mem_filter.mpr ⟨mem_product.mpr
        ⟨mem_powerset.mpr (hs.1.trans hp.2), mem_powerset.mpr (hs.2.trans hp.2)⟩, hp⟩
  have hAB : (A, B) ∈ F := (memF (A, B)).mpr ⟨⟨hA, hB, hu⟩, Subset.rfl⟩
  obtain ⟨p, hpF, hpmax⟩ :=
    exists_max_image F (fun p => p.1.card + p.2.card) ⟨(A, B), hAB⟩
  let M := F.filter fun q => q.1.card + q.2.card = p.1.card + p.2.card
  have hpM : p ∈ M := mem_filter.mpr ⟨hpF, rfl⟩
  obtain ⟨q, hqM, hqmin⟩ := exists_min_image M (fun q => q.1.card) ⟨p, hpM⟩
  obtain ⟨hqF, hqsum⟩ := mem_filter.mp hqM
  obtain ⟨hqgood, hqC⟩ := (memF q).mp hqF
  have hmax (r : Finset G × Finset G)
      (hr : 1 ∈ r.1 ∧ 1 ∈ r.2 ∧ ∀ a ∈ r.1, ∀ b ∈ r.2, a * b = 1 → a = 1)
      (hrC : r.1 * r.2 ⊆ C) :
      r.1.card + r.2.card ≤ q.1.card + q.2.card := by
    rw [hqsum]
    exact hpmax r ((memF r).mpr ⟨hr, hrC⟩)
  have hstart : A.card + B.card ≤ q.1.card + q.2.card :=
    hmax (A, B) ⟨hA, hB, hu⟩ Subset.rfl
  by_cases hinter : q.1 ∩ q.2 ⊆ {1}
  · have hi : (q.1 ∩ q.2).card ≤ 1 := by simpa using card_le_card hinter
    have hsub := good_subsets hqgood
    have hunion : q.1 ∪ q.2 ⊆ C :=
      union_subset (hsub.1.trans hqC) (hsub.2.trans hqC)
    have huc := card_le_card hunion
    have hsum := card_union_add_card_inter q.1 q.2
    change A.card + B.card ≤ C.card + 1
    omega
  · obtain ⟨x, hxi, hxn⟩ := Finset.not_subset.mp hinter
    obtain ⟨hxA, hxB⟩ := mem_inter.mp hxi
    have hx : x ≠ 1 := by simpa only [mem_singleton] using hxn
    let L := mulETransformLeft x⁻¹ q
    let R := mulETransformRight x q
    have hL : 1 ∈ L.1 ∧ 1 ∈ L.2 ∧ ∀ a ∈ L.1, ∀ b ∈ L.2, a * b = 1 → a = 1 :=
      good_left hqgood hxA hxB hx
    have hR : 1 ∈ R.1 ∧ 1 ∈ R.2 ∧ ∀ a ∈ R.1, ∀ b ∈ R.2, a * b = 1 → a = 1 :=
      good_right hqgood hxA hxB hx
    have hLC : L.1 * L.2 ⊆ C :=
      (mulETransformLeft.fst_mul_snd_subset x⁻¹ q).trans hqC
    have hRC : R.1 * R.2 ⊆ C :=
      (mulETransformRight.fst_mul_snd_subset x q).trans hqC
    have hLt := hmax L hL hLC
    have hRt := hmax R hR hRC
    have hcards : L.1.card + L.2.card + (R.1.card + R.2.card) =
        q.1.card + q.2.card + (q.1.card + q.2.card) :=
      transform_cards q.1 q.2 x
    have hLsum : L.1.card + L.2.card = q.1.card + q.2.card := by omega
    have hLM : L ∈ M := mem_filter.mpr
      ⟨(memF L).mpr ⟨hL, hLC⟩, hLsum.trans hqsum⟩
    have hmin := hqmin L hLM
    have hlt : L.1.card < q.1.card := left_card_lt hqgood hxB hx
    omega


end Kemperman

open Finset
open scoped Pointwise

theorem one_mem_reachableProducts {G : Type*} [Monoid G] [DecidableEq G]
    (S : Finset G) (R : ℕ → Finset G) (hR0 : R 0 = {1})
    (hRsucc : ∀ j, R (j + 1) = R j * insert 1 S) (j : ℕ) : 1 ∈ R j := by
  induction j with
  | zero => simp [hR0]
  | succ j ih =>
    rw [hRsucc]
    simpa only [mul_one] using Finset.mul_mem_mul ih (Finset.mem_insert_self 1 S)

/-- Each reachable product has a list witness, omitting identity padding. -/
theorem mem_reachableProducts_list {G : Type*} [Monoid G] [DecidableEq G]
    (S : Finset G) (R : ℕ → Finset G) (hR0 : R 0 = {1})
    (hRsucc : ∀ j, R (j + 1) = R j * insert 1 S)
    (j : ℕ) (x : G) (hx : x ∈ R j) :
    ∃ l : List G, l.length ≤ j ∧ (∀ a ∈ l, a ∈ S) ∧ l.prod = x := by
  induction j generalizing x with
  | zero =>
    have h : x = 1 := by simpa [hR0] using hx
    exact ⟨[], by simp, by simp, by simpa using h.symm⟩
  | succ j ih =>
    rw [hRsucc] at hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Finset.mem_mul.mp hx
    obtain ⟨l, hl, hmem, hprod⟩ := ih y hy
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact ⟨l, by omega, hmem, by simpa using hprod⟩
    · refine ⟨l ++ [z], by simpa using Nat.add_le_add_right hl 1, ?_, ?_⟩
      · intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · exact hmem a ha
        · simpa using (List.mem_singleton.mp ha ▸ hz)
      · simp [hprod]

/-- In any finite group, `k * |S| ≥ |G|` forces a nonempty word of at most
`k` nonidentity generators whose ordered product is the identity.
Repetition of generators is allowed, and the group need not be commutative. -/
theorem finite_group_one_product_of_one_not_mem {G : Type*} [Group G] [Fintype G]
    [DecidableEq G] (S : Finset G) (h1 : 1 ∉ S) (k : ℕ)
    (hcard : Fintype.card G ≤ k * S.card) :
    ∃ l : List G, l ≠ [] ∧ l.length ≤ k ∧ (∀ a ∈ l, a ∈ S) ∧ l.prod = 1 := by
  classical
  by_contra! hn
  let R : ℕ → Finset G := Nat.rec {1} (fun _ t => t * insert 1 S)
  have hR0 : R 0 = {1} := rfl
  have hRsucc (j : ℕ) : R (j + 1) = R j * insert 1 S := rfl
  have hone (j : ℕ) : 1 ∈ R j := one_mem_reachableProducts S R hR0 hRsucc j
  have hcount (j : ℕ) (hj : j ≤ k) : j * S.card + 1 ≤ (R j).card := by
    induction j with
    | zero => simp [hR0]
    | succ j ih =>
      have hprev := ih (show j ≤ k by omega)
      have hunique (u : G) (hu : u ∈ R j) (v : G) (hv : v ∈ insert 1 S)
          (hprod : u * v = 1) : u = 1 := by
        have hv1 : v = 1 := by
          by_contra hv1
          have hvS : v ∈ S := (Finset.mem_insert.mp hv).resolve_left hv1
          obtain ⟨l, hlen, hmem, hval⟩ :=
            mem_reachableProducts_list S R hR0 hRsucc j u hu
          have hlen' : (l ++ [v]).length ≤ k := by
            simp only [List.length_append, List.length_singleton]
            omega
          apply hn (l ++ [v]) (by simp) hlen' ?_ ?_
          · intro a ha
            rcases List.mem_append.mp ha with ha | ha
            · exact hmem a ha
            · simpa using (List.mem_singleton.mp ha ▸ hvS)
          · simpa [hval] using hprod
        simpa [hv1] using hprod
      have hinc := Kemperman.card_mul_ge_of_unique_one (R j) (insert 1 S)
        (hone j) (Finset.mem_insert_self 1 S) hunique
      rw [Finset.card_insert_of_notMem h1, ← hRsucc] at hinc
      simp only [Nat.succ_mul]
      omega
  have hlarge := hcount k le_rfl
  have hsmall := Finset.card_le_univ (R k)
  omega

/-- A finite subset of any finite group contains a nonempty word of length
at most `k` with product one whenever `k * |S| ≥ |G|`. -/
theorem finite_group_one_product {G : Type*} [Group G] [Fintype G]
    [DecidableEq G] (S : Finset G) (k : ℕ)
    (hcard : Fintype.card G ≤ k * S.card) :
    ∃ l : List G, l ≠ [] ∧ l.length ≤ k ∧ (∀ a ∈ l, a ∈ S) ∧ l.prod = 1 := by
  classical
  by_cases h1 : 1 ∈ S
  · have hk : 1 ≤ k := by
      by_contra! hk
      have hk0 : k = 0 := by omega
      have hp : 0 < Fintype.card G := Fintype.card_pos
      simp only [hk0, Nat.zero_mul] at hcard
      omega
    exact ⟨[1], by simp, by simpa using hk, by simpa using h1, by simp⟩
  · exact finite_group_one_product_of_one_not_mem S h1 k hcard

open OMA.S_opg_caccetta_haggkvist_conjecture


/-- Every nonempty closed walk in a loopless digraph contains a simple directed cycle. -/
theorem cycle_of_closed_walk {V : Type} (G : Digraph V)
    (hloop : ∀ v, ¬ G.Adj v v) (N : ℕ) (f : ℕ → V)
    (hN : 0 < N) (hclose : f N = f 0)
    (hstep : ∀ i < N, G.Adj (f i) (f (i + 1))) :
    ∃ k, k ≤ N ∧ HasDirectedCycleOfLength G k := by
  classical
  induction N using Nat.strong_induction_on generalizing f with
  | h N ih =>
    by_cases hi : Function.Injective (fun i : Fin N => f i.val)
    · have htwo : 2 ≤ N := by
        by_contra hn
        have heq : N = 1 := by omega
        subst N
        have hs := hstep 0 (by omega)
        exact hloop (f 0) (by simpa only [Nat.zero_add, hclose] using hs)
      refine ⟨N, le_rfl, htwo, (fun i => f i.val), hi, ?_⟩
      intro i
      have : NeZero N := ⟨by omega⟩
      rw [finRotate_apply]
      change G.Adj (f i.val) (f (↑(i + 1) : ℕ))
      rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (show 1 < N by omega)]
      by_cases hlast : i.val + 1 = N
      · rw [hlast, Nat.mod_self, ← hclose]
        simpa only [hlast] using hstep i.val i.isLt
      · rw [Nat.mod_eq_of_lt (by omega)]
        exact hstep i.val i.isLt
    · obtain ⟨i, j, heq, hne⟩ := Function.not_injective_iff.mp hi
      have produce (a b : Fin N) (hab : a.val < b.val) (he : f a.val = f b.val) :
          ∃ k, k ≤ N ∧ HasDirectedCycleOfLength G k := by
        have hp : 0 < b.val - a.val := by omega
        have hlt : b.val - a.val < N := by omega
        obtain ⟨k, hk, hc⟩ := ih (b.val - a.val) hlt
          (fun t => f (a.val + t)) hp (by simpa [Nat.add_sub_of_le hab.le] using he.symm)
          (by intro t ht; simpa [Nat.add_assoc] using hstep (a.val + t) (by omega))
        exact ⟨k, hk.trans hlt.le, hc⟩
      rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with hij | hji
      · exact produce i j hij heq
      · exact produce j i hji heq.symm

/-- A nonempty identity-product word gives a short simple cycle in every loopless
digraph containing the corresponding right-multiplication edges. -/
theorem cycle_of_one_product {A : Type*} [Monoid A] {V : Type}
    (G : Digraph V) (hloop : ∀ v, ¬ G.Adj v v) (e : A → V)
    (S : Finset A) (hedge : ∀ x s, s ∈ S → G.Adj (e x) (e (x * s)))
    (l : List A) (hne : l ≠ []) (hmem : ∀ a ∈ l, a ∈ S) (hprod : l.prod = 1) :
    ∃ k, k ≤ l.length ∧ HasDirectedCycleOfLength G k := by
  apply cycle_of_closed_walk G hloop l.length (fun i => e (l.take i).prod)
  · exact List.length_pos_iff.mpr hne
  · simpa using congrArg e hprod
  · intro i hi
    simpa only [List.prod_take_succ l i hi] using
      hedge (l.take i).prod l[i] (hmem l[i] (List.getElem_mem hi))

open OMA.S_opg_caccetta_haggkvist_conjecture


/-- In a loopless finite digraph, every outdegree is smaller than the order. -/
theorem outdegree_lt_card {V : Type} [Fintype V] (G : Digraph V) [DecidableRel G.Adj]
    (hloop : ∀ v, ¬ G.Adj v v) (v : V) : outdegree G v < Fintype.card V := by
  classical
  change (Finset.univ.filter (fun w => G.Adj v w)).card < Finset.univ.card
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩
  intro heq
  have hv : v ∈ Finset.univ.filter (fun w => G.Adj v w) := by rw [heq]; simp
  exact hloop v (Finset.mem_filter.mp hv).2

/-- Positive minimum outdegree forces a simple cycle whose length is at most the order. -/
theorem cycle_of_min_outdegree_pos {V : Type} [Fintype V] [Nonempty V]
    (G : Digraph V) [DecidableRel G.Adj]
    (hloop : ∀ v, ¬ G.Adj v v) (hdegree : ∀ v, 1 ≤ outdegree G v) :
    ∃ k, k ≤ Fintype.card V ∧ HasDirectedCycleOfLength G k := by
  classical
  have hnext : ∀ v : V, ∃ w : V, G.Adj v w := by
    intro v
    have hpos : 0 < (Finset.univ.filter (fun w => G.Adj v w)).card :=
      hdegree v
    obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
    exact ⟨w, (Finset.mem_filter.mp hw).2⟩
  choose next hnext using hnext
  let start : V := Classical.choice inferInstance
  let f : ℕ → V := fun i => next^[i] start
  have hf : ∀ i, G.Adj (f i) (f (i + 1)) := by
    intro i
    simpa only [f, Function.iterate_succ_apply'] using hnext (next^[i] start)
  have hnotinj : ¬ Function.Injective (fun i : Fin (Fintype.card V + 1) => f i.val) :=
    Fintype.not_injective_of_card_lt _ (by simp)
  obtain ⟨i, j, heq, hne⟩ := Function.not_injective_iff.mp hnotinj
  have produce (a b : Fin (Fintype.card V + 1)) (hab : a.val < b.val)
      (he : f a.val = f b.val) :
      ∃ k, k ≤ Fintype.card V ∧ HasDirectedCycleOfLength G k := by
    obtain ⟨k, hk, hc⟩ := cycle_of_closed_walk G hloop
      (b.val - a.val) (fun t => f (a.val + t))
      (by omega)
      (by simpa [Nat.add_sub_of_le hab.le] using he.symm)
      (by intro t ht; simpa [Nat.add_assoc] using hf (a.val + t))
    exact ⟨k, hk.trans (by omega), hc⟩
  rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with hij | hji
  · exact produce i j hij heq
  · exact produce j i hji heq.symm

open OMA.S_opg_caccetta_haggkvist_conjecture


/-- The integral Caccetta–Häggkvist bound for group-labelled edges.
The labelling need not be injective. -/
theorem cycle_of_group_edges {A : Type*} [Group A] [Fintype A] {V : Type}
    (G : Digraph V) (hloop : ∀ v, ¬ G.Adj v v) (e : A → V)
    (S : Finset A)
    (hedge : ∀ x s, s ∈ S → G.Adj (e x) (e (x * s)))
    (k : ℕ) (hcard : Fintype.card A ≤ k * S.card) :
    ∃ t, t ≤ k ∧ HasDirectedCycleOfLength G t := by
  classical
  obtain ⟨l, hne, hlen, hmem, hprod⟩ := finite_group_one_product S k hcard
  obtain ⟨t, ht, hcycle⟩ := cycle_of_one_product G hloop e S hedge l hne hmem hprod
  exact ⟨t, ht.trans hlen, hcycle⟩

/-- Every loopless digraph containing a finite Cayley subdigraph with at least
`r` connection elements satisfies the conjectured bound with denominator `r`. -/
theorem cycle_of_cayley_subgraph {A : Type*} [Group A] [Fintype A]
    {V : Type} [Fintype V] (G : Digraph V) (hloop : ∀ v, ¬ G.Adj v v)
    (e : A ↪ V) (S : Finset A) (r : ℕ) (hr : 1 ≤ r)
    (hS : r ≤ S.card) (hedge : ∀ x s, s ∈ S → G.Adj (e x) (e (x * s))) :
    ∃ k, k ≤ ⌈(Fintype.card V : ℚ) / r⌉₊ ∧ HasDirectedCycleOfLength G k := by
  have hrq : (0 : ℚ) < r := by exact_mod_cast (show 0 < r by omega)
  have hbound : Fintype.card V ≤ ⌈(Fintype.card V : ℚ) / r⌉₊ * r := by
    have h := (div_le_iff₀ hrq).mp (Nat.le_ceil ((Fintype.card V : ℚ) / r))
    exact_mod_cast h
  apply cycle_of_group_edges G hloop e S hedge
  exact (Fintype.card_le_of_injective e e.injective).trans
    (hbound.trans (Nat.mul_le_mul_left _ hS))

open OMA.S_opg_caccetta_haggkvist_conjecture


/-- The remaining outdegree-two case after excluding all embedded finite Cayley subdigraphs. -/
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] [Nonempty V] (G : Digraph V) [DecidableRel G.Adj],
    (∀ v, ¬ G.Adj v v) → (∀ v, 2 ≤ outdegree G v) →
    (∀ (A : Type) [Group A] [Fintype A] (e : A ↪ V) (S : Finset A),
      2 ≤ S.card → ¬ (∀ x s, s ∈ S → G.Adj (e x) (e (x * s)))) →
    ∃ k, k ≤ ⌈(Fintype.card V : ℚ) / 2⌉₊ ∧ HasDirectedCycleOfLength G k

/-- The remaining cases of outdegree at least three after the same Cayley exclusion. -/
def H2 : Prop :=
  ∀ (V : Type) [Fintype V] [Nonempty V] (G : Digraph V) [DecidableRel G.Adj] (r : ℕ),
    3 ≤ r → (∀ v, ¬ G.Adj v v) → (∀ v, r ≤ outdegree G v) →
    (∀ (A : Type) [Group A] [Fintype A] (e : A ↪ V) (S : Finset A),
      r ≤ S.card → ¬ (∀ x s, s ∈ S → G.Adj (e x) (e (x * s)))) →
    ∃ k, k ≤ ⌈(Fintype.card V : ℚ) / r⌉₊ ∧ HasDirectedCycleOfLength G k

theorem main : H1 → H2 → type_of% @OMA.S_opg_caccetta_haggkvist_conjecture.main := by
  classical
  intro htwo hlarge V _ _ G _ r hr hloop hdegree
  by_cases hrone : r = 1
  · subst r
    simpa using cycle_of_min_outdegree_pos G hloop hdegree
  by_cases hnone :
      ∀ (A : Type) [Group A] [Fintype A] (e : A ↪ V) (S : Finset A),
        r ≤ S.card → ¬ (∀ x s, s ∈ S → G.Adj (e x) (e (x * s)))
  · by_cases hrtwo : r = 2
    · subst r
      exact htwo V G hloop hdegree hnone
    · exact hlarge V G r (by omega) hloop hdegree hnone
  · push Not at hnone
    obtain ⟨A, hgroup, hfinite, e, S, hS, hedge⟩ := hnone
    let : Group A := hgroup
    let : Fintype A := hfinite
    exact cycle_of_cayley_subgraph G hloop e S r hr hS hedge

end OMA.R_opg_caccetta_haggkvist_conjecture_R1
