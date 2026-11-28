import OMAReductions.R_Erdos552_erdos_552_parts_ii_R2
import Mathlib

/-!
# Saturated quadrilateral-free graphs in the quadrilateral versus star problem

Burr, Erdős, Faudree, Rousseau and Schelp asked whether the deficit below the
square-root bound is unbounded. The preceding reduction uses a star size and
a degree threshold. Here one only chooses the number of vertices. The graphs
to be tested are saturated: adding any missing edge closes a four-cycle.
The reverse implication below shows that the new order criterion is necessary
as well as sufficient.

Lean formalization by @KoaOkano.
-/

namespace OMA.R_Erdos552_erdos_552_parts_ii_R2_H2_R1

open SimpleGraph

/-- Complete a quadrilateral-free graph until every nonedge is the pair of
endpoints of a path of length three with four distinct vertices. -/
def H1 : Prop :=
  ∀ (N : ℕ) (G : SimpleGraph (Fin N)), ¬ (cycleGraph 4).IsContained G →
    ∃ S : SimpleGraph (Fin N), G ≤ S ∧ ¬ (cycleGraph 4).IsContained S ∧
      ∀ x y, x ≠ y → ¬ S.Adj x y →
        ∃ a b, a ≠ y ∧ b ≠ x ∧ S.Adj x a ∧ S.Adj a b ∧ S.Adj b y

/-- At some order every saturated quadrilateral-free graph has a vertex
whose degree falls at least k below the integer square root of the order. -/
def H2 : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, k ≤ N.sqrt ∧
    ∀ (S : SimpleGraph (Fin N)) [DecidableRel S.Adj], ¬ (cycleGraph 4).IsContained S →
      (∀ x y, x ≠ y → ¬ S.Adj x y →
        ∃ a b, a ≠ y ∧ b ≠ x ∧ S.Adj x a ∧ S.Adj a b ∧ S.Adj b y) →
      ∃ v, S.degree v + k ≤ N.sqrt

/-- Every obstruction from the parent problem already gives a witness to the
single-order criterion, even before the saturation restriction is imposed. -/
theorem necessary (obstruction : OMA.R_Erdos552_erdos_552_parts_ii_R2.H2) : H2 := by
  intro k
  obtain ⟨n, d, hsq, hdeg⟩ := obstruction k
  have hroot : d + k ≤ (n + d).sqrt := Nat.le_sqrt'.mpr (hsq.trans (by omega))
  refine ⟨n + d, by omega, ?_⟩
  intro S _ hfree _
  obtain ⟨v, hv⟩ := hdeg S hfree
  exact ⟨v, by omega⟩

theorem main : H1 → H2 → OMA.R_Erdos552_erdos_552_parts_ii_R2.H2 := by
  classical
  intro complete deficient k
  obtain ⟨N, room, sparse⟩ := deficient (k + 2)
  let r := N.sqrt
  let d := r - (k + 2) + 1
  let n := N - d
  change k + 2 ≤ r at room
  have hr : r ≤ N := Nat.sqrt_le_self N
  have hd : d ≤ r := by dsimp [d]; omega
  have sum : n + d = N := Nat.sub_add_cancel (hd.trans hr)
  have ds : d + k = r - 1 := by dsimp [d]; omega
  have square : r ^ 2 ≤ N := Nat.le_sqrt'.mp (le_refl N.sqrt)
  have slack : (r - 1) ^ 2 + r ≤ r ^ 2 := by
    obtain ⟨t, ht⟩ : ∃ t, r = t + 1 := ⟨r - 1, by omega⟩
    rw [ht, Nat.add_sub_cancel]
    nlinarith
  refine ⟨n, d, ?_, ?_⟩
  · rw [ds]
    dsimp [n]
    omega
  · rw [sum]
    intro G _ hfree
    obtain ⟨S, hsub, hS, hsaturated⟩ := complete N G hfree
    obtain ⟨v, hv⟩ := sparse S hS hsaturated
    have mono : G.degree v ≤ S.degree v := G.degree_le_of_le hsub
    change S.degree v + (k + 2) ≤ r at hv
    exact ⟨v, by dsimp [d]; omega⟩

end OMA.R_Erdos552_erdos_552_parts_ii_R2_H2_R1
