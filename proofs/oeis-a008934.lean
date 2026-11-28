import OMAStatements.S_oeis_a008934
import Mathlib

/-!
# Proof of OEIS A008934 (Irwin's nested-sum formula for tournament sequences)

For `n ≥ 2`, `OMA.S_oeis_a008934.A n = OMA.S_oeis_a008934.nest (n - 1) 2`.

We generalize `tournamentSeqs` to `seqsFrom m s`, the set of sequences `a : Fin (m + 1) → ℕ`
with `a 0 = s` and `a i < a (i + 1) ≤ 2 * a i` for all `i : Fin m`. By induction on `m`,
`seqsFrom m s` is finite with cardinality `nest m s`. Since `tournamentSeqs n = seqsFrom n 1`,
for `n ≥ 2` we get `A n = nest n 1 = ∑ i ∈ Icc 1 1, nest (n - 1) (1 + i) = nest (n - 1) 2`.
-/

namespace OMA.OEIS_A008934

open Finset BigOperators OMA.S_oeis_a008934

private def seqsFrom (m s : ℕ) : Set (Fin (m + 1) → ℕ) :=
  {a | a 0 = s ∧ ∀ i : Fin m, a i.castSucc < a i.succ ∧ a i.succ ≤ 2 * a i.castSucc}

private def consSeq {m : ℕ} (s : ℕ) (b : Fin (m + 1) → ℕ) : Fin (m + 2) → ℕ :=
  Fin.cons s b

private lemma consSeq_injective {m : ℕ} (s : ℕ) :
    Function.Injective (consSeq (m := m) s) := by
  intro b₁ b₂ h
  funext j
  have hj := congrFun h j.succ
  simpa only [consSeq, Fin.cons_succ] using hj

private lemma seqsFrom_zero (s : ℕ) :
    seqsFrom 0 s = {fun _ => s} := by
  ext a
  simp only [seqsFrom, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · intro ⟨h0, _⟩
    funext i
    rw [Fin.eq_zero i, h0]
  · intro ha
    subst ha
    exact ⟨rfl, fun i => Fin.elim0 i⟩

private lemma seqsFrom_succ_eq_biUnion (m s : ℕ) :
    seqsFrom (m + 1) s = ⋃ i ∈ Finset.Icc 1 s, (consSeq s) '' seqsFrom m (s + i) := by
  ext a
  simp only [seqsFrom, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_image, Finset.mem_Icc]
  constructor
  · intro ⟨h0, hstep⟩
    have hfirst := hstep 0
    simp only [Fin.castSucc_zero, h0] at hfirst
    refine ⟨a (0 : Fin (m + 1)).succ - s, ⟨by omega, by omega⟩, fun j => a j.succ, ?_, ?_⟩
    · refine ⟨?_, fun k => ?_⟩
      · change a (0 : Fin (m + 1)).succ = s + (a (0 : Fin (m + 1)).succ - s)
        omega
      · simpa only [Fin.castSucc_succ] using hstep k.succ
    · funext j
      refine Fin.cases ?_ ?_ j
      · simpa only [consSeq, Fin.cons_zero] using h0.symm
      · intro k
        simp only [consSeq, Fin.cons_succ]
  · rintro ⟨i, ⟨hi1, his⟩, b, ⟨hb0, hbstep⟩, rfl⟩
    refine ⟨by simp only [consSeq, Fin.cons_zero], fun j => ?_⟩
    refine Fin.cases ?_ ?_ j
    · simp only [Fin.castSucc_zero, consSeq, Fin.cons_zero, Fin.cons_succ, hb0]
      omega
    · intro k
      simpa only [Fin.castSucc_succ, consSeq, Fin.cons_succ] using hbstep k

private lemma ncard_biUnion_finset {α β : Type*} [DecidableEq α] (t : Finset α) (f : α → Set β)
    (hfin : ∀ x ∈ t, (f x).Finite)
    (hdisj : Set.Pairwise (t : Set α) (fun x y => Disjoint (f x) (f y))) :
    (⋃ x ∈ t, f x).ncard = ∑ x ∈ t, (f x).ncard := by
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    have hfin_a : (f a).Finite := hfin a (Finset.mem_insert_self a t)
    have hfin_t : ∀ x ∈ t, (f x).Finite := fun x hx => hfin x (Finset.mem_insert_of_mem hx)
    have hdisj_t : Set.Pairwise (t : Set α) (fun x y => Disjoint (f x) (f y)) :=
      hdisj.mono (by intro x hx; exact Finset.mem_insert_of_mem hx)
    have hUnion_eq : (⋃ x ∈ insert a t, f x) = f a ∪ ⋃ x ∈ t, f x := by
      ext y; simp
    have hUnion_fin : (⋃ x ∈ t, f x).Finite :=
      t.finite_toSet.biUnion hfin_t
    have hdisj_a : Disjoint (f a) (⋃ x ∈ t, f x) := by
      rw [Set.disjoint_iUnion₂_right]
      intro x hx
      exact hdisj (Finset.mem_insert_self a t) (Finset.mem_insert_of_mem hx) (fun h => ha (h ▸ hx))
    rw [hUnion_eq, Set.ncard_union_eq hdisj_a hfin_a hUnion_fin, Finset.sum_insert ha,
      ih hfin_t hdisj_t]

private lemma seqsFrom_finite_and_ncard (m : ℕ) :
    ∀ s : ℕ, (seqsFrom m s).Finite ∧ (seqsFrom m s).ncard = nest m s := by
  induction m with
  | zero =>
    intro s
    rw [seqsFrom_zero]
    exact ⟨Set.finite_singleton _, Set.ncard_singleton _⟩
  | succ m ih =>
    intro s
    rw [seqsFrom_succ_eq_biUnion]
    have hfin : ∀ i ∈ Finset.Icc 1 s, ((consSeq s) '' seqsFrom m (s + i)).Finite := fun i _ =>
      (ih (s + i)).1.image (consSeq s)
    have hdisj : Set.Pairwise (Finset.Icc 1 s : Set ℕ)
        (fun i j => Disjoint ((consSeq s) '' seqsFrom m (s + i))
          ((consSeq s) '' seqsFrom m (s + j))) := by
      intro i _ j _ hij
      rw [Set.disjoint_left]
      rintro a ⟨b₁, ⟨hb₁, _⟩, rfl⟩ ⟨b₂, ⟨hb₂, _⟩, heq⟩
      have h1 := congrFun heq (0 : Fin (m + 1)).succ
      simp only [consSeq, Fin.cons_succ, hb₁, hb₂] at h1
      exact hij (by omega)
    refine ⟨(Finset.Icc 1 s).finite_toSet.biUnion hfin, ?_⟩
    rw [ncard_biUnion_finset (Finset.Icc 1 s) _ hfin hdisj]
    simp only [nest]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Set.ncard_image_of_injective _ (consSeq_injective s), (ih (s + i)).2]

end OMA.OEIS_A008934

theorem OMA.solution : type_of% @OMA.S_oeis_a008934.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hA : OMA.S_oeis_a008934.A (m + 1) = OMA.S_oeis_a008934.nest (m + 1) 1 :=
    (OMA.OEIS_A008934.seqsFrom_finite_and_ncard (m + 1) 1).2
  rw [hA, Nat.add_sub_cancel]
  have h11 : Finset.Icc 1 1 = {1} := by decide
  simp only [OMA.S_oeis_a008934.nest, h11, Finset.sum_singleton]
