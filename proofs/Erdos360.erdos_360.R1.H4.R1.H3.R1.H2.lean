import OMAReductions.R_Erdos360_erdos_360_R1_H4_R1_H3_R1
import Mathlib

open scoped BigOperators

/-- A covered interval survives adjoining an endpoint pair. The two
translates are adjacent or overlap because the old width is at least
the maximum endpoint distance minus one. -/
theorem OMA.solution : OMA.R_Erdos360_erdos_360_R1_H4_R1_H3_R1.H2 := by
  classical
  intro n S I T a w D p
  induction T using Finset.induction_on with
  | empty =>
    intro _ _ _ h
    exact ⟨a, by simpa using h⟩
  | @insert i T hi ih =>
    intro hdis hD hend hstart
    have dis : Disjoint I T :=
      hdis.mono_right (Finset.subset_insert _ _)
    have hnI : i ∉ I := fun h ↦ Finset.disjoint_left.mp hdis h (Finset.mem_insert_self _ _)
    have hn : i ∉ I ∪ T := by simp [hnI,hi]
    obtain ⟨b,hb⟩ := ih dis hD (fun j hj ↦ hend j (Finset.mem_insert_of_mem hj)) hstart
    obtain ⟨x,hx,y,hy,hlo,hhi⟩ := hend i (Finset.mem_insert_self _ _)
    let B := w+T.card*p
    have hB : w ≤ B := Nat.le_add_right _ _
    refine ⟨b+x, ?_⟩
    intro t ht
    have ht' := Finset.mem_Icc.mp ht
    rw [Finset.card_insert_of_notMem hi, Nat.add_mul, one_mul] at ht'
    change b+x ≤ t ∧ t ≤ b+x+(w+(T.card*p+p)) at ht'
    have lift (z : ℕ) (hz : z ∈ S i) (hzt : z ≤ t) (hin : t-z ∈ Finset.Icc b (b+B)) :
        ∃ f : Fin n → ℕ, (∀ j ∈ I ∪ insert i T, f j ∈ S j) ∧
          ∑ j ∈ I ∪ insert i T, f j = t := by
      obtain ⟨f,hf,hs⟩ := hb (t-z) hin
      rw [Finset.union_insert]
      refine ⟨Function.update f i z, ?_, ?_⟩
      · intro j hj
        obtain rfl | hmem := Finset.mem_insert.mp hj
        · simpa using hz
        · have hne : j ≠ i := fun h ↦ hn (h ▸ hmem)
          simpa [Function.update_of_ne hne] using hf j hmem
      · rw [Finset.sum_insert hn, Function.update_self]
        have heq : ∑ j ∈ I ∪ T, Function.update f i z j = ∑ j ∈ I ∪ T, f j := by
          apply Finset.sum_congr rfl
          intro j hj
          have hne : j ≠ i := fun h ↦ hn (h ▸ hj)
          exact Function.update_of_ne hne z f
        rw [heq, hs]
        omega
    by_cases left : t ≤ b+B+x
    · apply lift x hx (by omega)
      exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
    · have hupper : t ≤ b+B+y := by dsimp [B] at *; omega
      apply lift y hy (by omega)
      exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
