import OMAReductions.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R1_H2_R1
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Group.Semiconj.Basic
import Mathlib.Algebra.Group.Commute.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Set.Card.Arithmetic

/-!
# Short cycles from commuting adjacent conjugates

Write r = q p q⁻¹. A conjugate square at y is the equality pr(y) = rp(y).
If these squares close at x, q(x) and r⁻¹(x), the graph of the three
pointwise distinct matchings 1, p, q contains a simple C4, C8 or C16.
The eighteen positions in the certificate are words of length at most
four applied to x. They need not be distinct. With edges labeled 0, 1, 2
for the three matchings, the first closed trace reads 0120121010210201.
A repeated same-shore vertex identifies two positions. Transport these
equalities by the permutations and their inverses to obtain the next
trace or contradict matching separation. A nonbacktracking eight-step
trace that folds at opposite positions contains a four-cycle.

If all three cycle lengths are absent, the three inverse images of the
square-failure set cover X. A union bound gives defect at least |X|/3.
Relabeling the matchings yields the same bound for all three relative
pairs. In particular an abelian normal subgroup cannot contain a
relative matching difference, which rules out index two.

The result extends the odd-order regular-action rectangle of @mejiasd3v
in PR 7828 to arbitrary separated permutation actions. The matching
formulation and the central-commutator case come from PRs 592, 5246
and 5820. The target is the residual step of PR 8157.
Formalization by @bmander.
-/
namespace Erdos64.MatchingConjugate
open SimpleGraph
universe u
variable {X : Type u}
set_option maxHeartbeats 1000000 in
private theorem collision4 {G : SimpleGraph (Bool × X)} (no : ¬ cycleGraph 4 ⊑ G)
    (x0 x1 x2 x3 : X)
    (e0 : G.Adj (false,x0) (true,x1))
    (e1 : G.Adj (false,x2) (true,x1))
    (e2 : G.Adj (false,x2) (true,x3))
    (e3 : G.Adj (false,x0) (true,x3))
    : x0=x2 ∨ x1=x3 := by
  classical
  by_contra! h
  apply no
  let l : List (Bool × X) := [(false,x0),(true,x1),(false,x2),(true,x3)]
  let f : Fin 4 → Bool × X := l.get
  have nd : l.Nodup := by
    obtain ⟨d0_2,d1_3⟩ := h
    simp [l, *]
  have step (i : Fin 4) : G.Adj (f i) (f (i+1)) := by
    fin_cases i
    · exact e0
    · exact e1.symm
    · exact e2
    · exact e3.symm
  refine ⟨⟨⟨f,?_⟩,List.nodup_iff_injective_get.mp nd⟩⟩
  intro i j adj
  rcases cycleGraph_adj.mp adj with h|h
  · exact (sub_eq_iff_eq_add'.mp h) ▸ (step j).symm
  · exact (sub_eq_iff_eq_add'.mp h) ▸ step i

set_option maxHeartbeats 1000000 in
private theorem collision8 {G : SimpleGraph (Bool × X)} (no : ¬ cycleGraph 8 ⊑ G)
    (x0 x1 x2 x3 x4 x5 x6 x7 : X)
    (e0 : G.Adj (false,x0) (true,x1))
    (e1 : G.Adj (false,x2) (true,x1))
    (e2 : G.Adj (false,x2) (true,x3))
    (e3 : G.Adj (false,x4) (true,x3))
    (e4 : G.Adj (false,x4) (true,x5))
    (e5 : G.Adj (false,x6) (true,x5))
    (e6 : G.Adj (false,x6) (true,x7))
    (e7 : G.Adj (false,x0) (true,x7))
    : x0=x2 ∨ x0=x4 ∨ x0=x6 ∨ x1=x3 ∨ x1=x5 ∨ x1=x7 ∨ x2=x4 ∨ x2=x6 ∨ x3=x5 ∨ x3=x7 ∨ x4=x6 ∨ x5=x7 := by
  classical
  by_contra! h
  apply no
  let l : List (Bool × X) := [(false,x0),(true,x1),(false,x2),(true,x3),(false,x4),(true,x5),(false,x6),(true,x7)]
  let f : Fin 8 → Bool × X := l.get
  have nd : l.Nodup := by
    obtain ⟨d0_2,d0_4,d0_6,d1_3,d1_5,d1_7,d2_4,d2_6,d3_5,d3_7,d4_6,d5_7⟩ := h
    simp [l, *]
  have step (i : Fin 8) : G.Adj (f i) (f (i+1)) := by
    fin_cases i
    · exact e0
    · exact e1.symm
    · exact e2
    · exact e3.symm
    · exact e4
    · exact e5.symm
    · exact e6
    · exact e7.symm
  refine ⟨⟨⟨f,?_⟩,List.nodup_iff_injective_get.mp nd⟩⟩
  intro i j adj
  rcases cycleGraph_adj.mp adj with h|h
  · exact (sub_eq_iff_eq_add'.mp h) ▸ (step j).symm
  · exact (sub_eq_iff_eq_add'.mp h) ▸ step i

set_option maxHeartbeats 1000000 in
private theorem collision16 {G : SimpleGraph (Bool × X)} (no : ¬ cycleGraph 16 ⊑ G)
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : X)
    (e0 : G.Adj (false,x0) (true,x1))
    (e1 : G.Adj (false,x2) (true,x1))
    (e2 : G.Adj (false,x2) (true,x3))
    (e3 : G.Adj (false,x4) (true,x3))
    (e4 : G.Adj (false,x4) (true,x5))
    (e5 : G.Adj (false,x6) (true,x5))
    (e6 : G.Adj (false,x6) (true,x7))
    (e7 : G.Adj (false,x8) (true,x7))
    (e8 : G.Adj (false,x8) (true,x9))
    (e9 : G.Adj (false,x10) (true,x9))
    (e10 : G.Adj (false,x10) (true,x11))
    (e11 : G.Adj (false,x12) (true,x11))
    (e12 : G.Adj (false,x12) (true,x13))
    (e13 : G.Adj (false,x14) (true,x13))
    (e14 : G.Adj (false,x14) (true,x15))
    (e15 : G.Adj (false,x0) (true,x15))
    : x0=x2 ∨ x0=x4 ∨ x0=x6 ∨ x0=x8 ∨ x0=x10 ∨ x0=x12 ∨ x0=x14 ∨ x1=x3 ∨ x1=x5 ∨ x1=x7 ∨ x1=x9 ∨ x1=x11 ∨ x1=x13 ∨ x1=x15 ∨ x2=x4 ∨ x2=x6 ∨ x2=x8 ∨ x2=x10 ∨ x2=x12 ∨ x2=x14 ∨ x3=x5 ∨ x3=x7 ∨ x3=x9 ∨ x3=x11 ∨ x3=x13 ∨ x3=x15 ∨ x4=x6 ∨ x4=x8 ∨ x4=x10 ∨ x4=x12 ∨ x4=x14 ∨ x5=x7 ∨ x5=x9 ∨ x5=x11 ∨ x5=x13 ∨ x5=x15 ∨ x6=x8 ∨ x6=x10 ∨ x6=x12 ∨ x6=x14 ∨ x7=x9 ∨ x7=x11 ∨ x7=x13 ∨ x7=x15 ∨ x8=x10 ∨ x8=x12 ∨ x8=x14 ∨ x9=x11 ∨ x9=x13 ∨ x9=x15 ∨ x10=x12 ∨ x10=x14 ∨ x11=x13 ∨ x11=x15 ∨ x12=x14 ∨ x13=x15 := by
  classical
  by_contra! h
  apply no
  let l : List (Bool × X) := [(false,x0),(true,x1),(false,x2),(true,x3),(false,x4),(true,x5),(false,x6),(true,x7),(false,x8),(true,x9),(false,x10),(true,x11),(false,x12),(true,x13),(false,x14),(true,x15)]
  let f : Fin 16 → Bool × X := l.get
  have nd : l.Nodup := by
    obtain ⟨d0_2,d0_4,d0_6,d0_8,d0_10,d0_12,d0_14,d1_3,d1_5,d1_7,d1_9,d1_11,d1_13,d1_15,d2_4,d2_6,d2_8,d2_10,d2_12,d2_14,d3_5,d3_7,d3_9,d3_11,d3_13,d3_15,d4_6,d4_8,d4_10,d4_12,d4_14,d5_7,d5_9,d5_11,d5_13,d5_15,d6_8,d6_10,d6_12,d6_14,d7_9,d7_11,d7_13,d7_15,d8_10,d8_12,d8_14,d9_11,d9_13,d9_15,d10_12,d10_14,d11_13,d11_15,d12_14,d13_15⟩ := h
    simp [l, *]
  have step (i : Fin 16) : G.Adj (f i) (f (i+1)) := by
    fin_cases i
    · exact e0
    · exact e1.symm
    · exact e2
    · exact e3.symm
    · exact e4
    · exact e5.symm
    · exact e6
    · exact e7.symm
    · exact e8
    · exact e9.symm
    · exact e10
    · exact e11.symm
    · exact e12
    · exact e13.symm
    · exact e14
    · exact e15.symm
  refine ⟨⟨⟨f,?_⟩,List.nodup_iff_injective_get.mp nd⟩⟩
  intro i j adj
  rcases cycleGraph_adj.mp adj with h|h
  · exact (sub_eq_iff_eq_add'.mp h) ▸ (step j).symm
  · exact (sub_eq_iff_eq_add'.mp h) ▸ step i

private theorem short4 (p q : Equiv.Perm X) (G : SimpleGraph (Bool × X))
    (sep : ∀ x, p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x)
    (e₀ : ∀ x, G.Adj (false,x) (true,x)) (e₁ : ∀ x, G.Adj (false,x) (true,p x))
    (e₂ : ∀ x, G.Adj (false,x) (true,q x))
    (no : ¬ (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G))
    (c : Fin 4 → Fin 3) (different : ∀ i, c i ≠ c (i+1))
    (x0 x1 x2 x3 : X)
    (w0 : ((![(1 : Equiv.Perm X),p,q] : Fin 3 → Equiv.Perm X) (c 0)) x0 = x1)
    (w1 : ((![(1 : Equiv.Perm X),p,q] : Fin 3 → Equiv.Perm X) (c 1)) x2 = x1)
    (w2 : ((![(1 : Equiv.Perm X),p,q] : Fin 3 → Equiv.Perm X) (c 2)) x2 = x3)
    (w3 : ((![(1 : Equiv.Perm X),p,q] : Fin 3 → Equiv.Perm X) (c 3)) x0 = x3)
    : False := by
  let F := (![(1 : Equiv.Perm X),p,q] : Fin 3 → Equiv.Perm X)
  have apart (i j : Fin 3) (ij : i ≠ j) (x : X) : F i x ≠ F j x := by
    fin_cases i <;> fin_cases j <;> first | exact (ij rfl).elim | exact (sep x).1 | exact (sep x).1.symm | exact (sep x).2.1 | exact (sep x).2.1.symm | exact (sep x).2.2 | exact (sep x).2.2.symm
  have edge (i : Fin 3) (x : X) : G.Adj (false,x) (true,F i x) := by
    fin_cases i <;> first | exact e₀ x | exact e₁ x | exact e₂ x
  have a0 : G.Adj (false,x0) (true,x1) := (w0) ▸ edge (c 0) x0
  have a1 : G.Adj (false,x2) (true,x1) := (w1) ▸ edge (c 1) x2
  have a2 : G.Adj (false,x2) (true,x3) := (w2) ▸ edge (c 2) x2
  have a3 : G.Adj (false,x0) (true,x3) := (w3) ▸ edge (c 3) x0
  have d0 : x0 ≠ x2 := by
    intro hit
    exact apart _ _ (different 0) x0 ((w0).trans (w1.symm.trans (congrArg (F (c 1)) hit.symm)))
  have d1 : x1 ≠ x3 := by
    intro hit
    exact apart _ _ (different 1) x2 ((w1).trans (hit.trans w2.symm))
  have d2 : x2 ≠ x0 := by
    intro hit
    exact apart _ _ (different 2) x2 ((w2).trans (w3.symm.trans (congrArg (F (c 3)) hit.symm)))
  have d3 : x3 ≠ x1 := by
    intro hit
    exact apart _ _ (different 3) x0 ((w3).trans (hit.trans w0.symm))
  rcases collision4 (fun h => no (.inl h)) x0 x1 x2 x3 a0 a1 a2 a3 with h|h
  · exact d0 h
  · exact d1 h

private theorem short8 (p q : Equiv.Perm X) (G : SimpleGraph (Bool × X))
    (sep : ∀ x, p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x)
    (e₀ : ∀ x, G.Adj (false,x) (true,x)) (e₁ : ∀ x, G.Adj (false,x) (true,p x))
    (e₂ : ∀ x, G.Adj (false,x) (true,q x))
    (no : ¬ (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G))
    (c : Fin 8 → Fin 3) (different : ∀ i, c i ≠ c (i+1))
    (x0 x1 x2 x3 x4 x5 x6 x7 : X)
    (w0 : ((![(1 : Equiv.Perm X),p,q] : Fin 3 → Equiv.Perm X) (c 0)) x0 = x1)
    (w1 : ((![(1 : Equiv.Perm X),p,q] : Fin 3 → Equiv.Perm X) (c 1)) x2 = x1)
    (w2 : ((![(1 : Equiv.Perm X),p,q] : Fin 3 → Equiv.Perm X) (c 2)) x2 = x3)
    (w3 : ((![(1 : Equiv.Perm X),p,q] : Fin 3 → Equiv.Perm X) (c 3)) x4 = x3)
    (w4 : ((![(1 : Equiv.Perm X),p,q] : Fin 3 → Equiv.Perm X) (c 4)) x4 = x5)
    (w5 : ((![(1 : Equiv.Perm X),p,q] : Fin 3 → Equiv.Perm X) (c 5)) x6 = x5)
    (w6 : ((![(1 : Equiv.Perm X),p,q] : Fin 3 → Equiv.Perm X) (c 6)) x6 = x7)
    (w7 : ((![(1 : Equiv.Perm X),p,q] : Fin 3 → Equiv.Perm X) (c 7)) x0 = x7)
    : False := by
  let F := (![(1 : Equiv.Perm X),p,q] : Fin 3 → Equiv.Perm X)
  have apart (i j : Fin 3) (ij : i ≠ j) (x : X) : F i x ≠ F j x := by
    fin_cases i <;> fin_cases j <;> first | exact (ij rfl).elim | exact (sep x).1 | exact (sep x).1.symm | exact (sep x).2.1 | exact (sep x).2.1.symm | exact (sep x).2.2 | exact (sep x).2.2.symm
  have edge (i : Fin 3) (x : X) : G.Adj (false,x) (true,F i x) := by
    fin_cases i <;> first | exact e₀ x | exact e₁ x | exact e₂ x
  have a0 : G.Adj (false,x0) (true,x1) := (w0) ▸ edge (c 0) x0
  have a1 : G.Adj (false,x2) (true,x1) := (w1) ▸ edge (c 1) x2
  have a2 : G.Adj (false,x2) (true,x3) := (w2) ▸ edge (c 2) x2
  have a3 : G.Adj (false,x4) (true,x3) := (w3) ▸ edge (c 3) x4
  have a4 : G.Adj (false,x4) (true,x5) := (w4) ▸ edge (c 4) x4
  have a5 : G.Adj (false,x6) (true,x5) := (w5) ▸ edge (c 5) x6
  have a6 : G.Adj (false,x6) (true,x7) := (w6) ▸ edge (c 6) x6
  have a7 : G.Adj (false,x0) (true,x7) := (w7) ▸ edge (c 7) x0
  have d0 : x0 ≠ x2 := by
    intro hit
    exact apart _ _ (different 0) x0 ((w0).trans (w1.symm.trans (congrArg (F (c 1)) hit.symm)))
  have d1 : x1 ≠ x3 := by
    intro hit
    exact apart _ _ (different 1) x2 ((w1).trans (hit.trans w2.symm))
  have d2 : x2 ≠ x4 := by
    intro hit
    exact apart _ _ (different 2) x2 ((w2).trans (w3.symm.trans (congrArg (F (c 3)) hit.symm)))
  have d3 : x3 ≠ x5 := by
    intro hit
    exact apart _ _ (different 3) x4 ((w3).trans (hit.trans w4.symm))
  have d4 : x4 ≠ x6 := by
    intro hit
    exact apart _ _ (different 4) x4 ((w4).trans (w5.symm.trans (congrArg (F (c 5)) hit.symm)))
  have d5 : x5 ≠ x7 := by
    intro hit
    exact apart _ _ (different 5) x6 ((w5).trans (hit.trans w6.symm))
  have d6 : x6 ≠ x0 := by
    intro hit
    exact apart _ _ (different 6) x6 ((w6).trans (w7.symm.trans (congrArg (F (c 7)) hit.symm)))
  have d7 : x7 ≠ x1 := by
    intro hit
    exact apart _ _ (different 7) x0 ((w7).trans (hit.trans w0.symm))
  have o0 : x0 ≠ x4 := by
    intro hit
    rcases collision4 (fun h => no (.inl h)) x0 x1 x2 x3 a0 a1 a2 (hit.symm ▸ a3) with h|h
    · exact d0 h
    · exact d1 h
  have o1 : x1 ≠ x5 := by
    intro hit
    rcases collision4 (fun h => no (.inl h)) x2 x3 x4 x1 a2 a3 (hit.symm ▸ a4) a1 with h|h
    · exact d2 h
    · exact d1 h.symm
  have o2 : x2 ≠ x6 := by
    intro hit
    rcases collision4 (fun h => no (.inl h)) x2 x3 x4 x5 a2 a3 a4 (hit.symm ▸ a5) with h|h
    · exact d2 h
    · exact d3 h
  have o3 : x3 ≠ x7 := by
    intro hit
    rcases collision4 (fun h => no (.inl h)) x4 x5 x6 x3 a4 a5 (hit.symm ▸ a6) a3 with h|h
    · exact d4 h
    · exact d3 h.symm
  rcases collision8 (fun h => no (.inr (.inl h))) x0 x1 x2 x3 x4 x5 x6 x7 a0 a1 a2 a3 a4 a5 a6 a7 with h|h|h|h|h|h|h|h|h|h|h|h
  · exact d0 h
  · exact o0 h
  · exact d6 h.symm
  · exact d1 h
  · exact o1 h
  · exact d7 h.symm
  · exact d2 h
  · exact o2 h
  · exact d3 h
  · exact o3 h
  · exact d4 h
  · exact d5 h

variable (p q : Equiv.Perm X) (v : ℕ → X)
variable (hp : ∀ i : Fin 10, let e := ([(0,1),(2,6),(3,7),(4,9),(5,10),(8,3),(11,5),(12,15),(13,16),(14,17)] : List (ℕ × ℕ)).get i; p (v e.1)=v e.2)
variable (hq : ∀ i : Fin 10, let e := ([(0,2),(1,4),(3,0),(5,1),(7,13),(8,14),(10,16),(11,17),(12,6),(15,9)] : List (ℕ × ℕ)).get i; q (v e.1)=v e.2)

variable (sep : ∀ x, p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x)
variable (G : SimpleGraph (Bool × X))
variable (e₀ : ∀ x, G.Adj (false,x) (true,x))
variable (e₁ : ∀ x, G.Adj (false,x) (true,p x))
variable (e₂ : ∀ x, G.Adj (false,x) (true,q x))
variable (no : ¬ (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G))
include p q v hp hq sep in
private theorem branch10 (_h0 : v 3 = v 11) (h1 : v 0 = v 15) (h2 : v 0 = v 8) : False := by
  have t0 : v 9 = v 2 := Eq.trans (Eq.symm (hq 9)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 0))
  have t1 : v 3 = v 1 := Eq.trans (Eq.symm (hp 5)) (Eq.trans (congrArg p (Eq.symm (h2))) (hp 0))
  have t2 : v 0 = v 4 := Eq.trans (Eq.symm (hq 2)) (Eq.trans (congrArg q (t1)) (hq 1))
  have t3 : v 9 = v 1 := Eq.trans (Eq.symm (hp 3)) (Eq.trans (congrArg p (Eq.symm (t2))) (hp 0))
  exact (sep (v 0)).2.2 (Eq.trans (hp 0) (Eq.symm (Eq.trans (hq 0) (Eq.trans (Eq.symm (t0)) (t3)))))

include p q v hq sep in
private theorem branch11 (_h0 : v 3 = v 11) (_h1 : v 0 = v 15) (h2 : v 0 = v 3) : False := by
  have t0 : v 0 = v 2 := Eq.trans (Eq.symm (hq 2)) (Eq.trans (congrArg q (Eq.symm (h2))) (hq 0))
  exact (sep (v 0)).2.1 (Eq.trans (hq 0) (Eq.symm (t0)))

include p q v hp sep in
private theorem branch9 (_h0 : v 3 = v 11) (h1 : v 0 = v 15) (h2 : v 0 = v 12) : False := by
  have t0 : v 15 = v 1 := Eq.trans (Eq.symm (hp 7)) (Eq.trans (congrArg p (Eq.symm (h2))) (hp 0))
  exact (sep (v 0)).1 (Eq.trans (hp 0) (Eq.trans (Eq.symm (t0)) (Eq.symm (h1))))

include p q v hq sep in
private theorem branch4 (_h0 : v 3 = v 11) (h1 : v 0 = v 3) : False := by
  have t0 : v 0 = v 2 := Eq.trans (Eq.symm (hq 2)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 0))
  exact (sep (v 0)).2.1 (Eq.trans (hq 0) (Eq.symm (t0)))

include p q v hp hq sep in
private theorem branch39 (_h0 : v 3 = v 10) (h1 : v 0 = v 5) : False := by
  have t0 : v 1 = v 2 := Eq.trans (Eq.symm (hq 3)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 0))
  exact (sep (v 0)).2.2 (Eq.trans (hp 0) (Eq.symm (Eq.trans (hq 0) (Eq.symm (t0)))))

include p q v hp sep in
private theorem branch6 (_h0 : v 3 = v 11) (h1 : v 0 = v 1) : False := by
  exact (sep (v 0)).1 (Eq.trans (hp 0) (Eq.symm (h1)))

include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch7 (h0 : v 3 = v 11) (h1 : v 0 = v 4) : False := by
  have t0 : v 9 = v 1 := Eq.trans (Eq.symm (hp 3)) (Eq.trans (congrArg p (Eq.symm (h1))) (hp 0))
  have t1 : v 15 = v 5 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 9)))) (Eq.trans (congrArg q.symm (t0)) (q.symm_apply_eq.mpr (Eq.symm (hq 3))))
  have t2 : v 12 = v 11 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 7)))) (Eq.trans (congrArg p.symm (t1)) (p.symm_apply_eq.mpr (Eq.symm (hp 6))))
  have t3 : v 1 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 1)))) (Eq.trans (congrArg q.symm (Eq.symm (h1))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
  have t4 : v 6 = v 4 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (Eq.trans (Eq.trans (t2) (Eq.symm (h0))) (Eq.symm (t3)))) (hq 1))
  exact short4 p q G sep e₀ e₁ e₂ no ![0,1,0,2] (by decide)
    (v 0) (v 0) (v 2) (v 2)
    (rfl) (Eq.trans (hp 1) (Eq.trans (t4) (Eq.symm (h1)))) (rfl) (hq 0)

include p q v hq sep in
private theorem branch38 (_h0 : v 3 = v 10) (h1 : v 0 = v 3) : False := by
  have t0 : v 0 = v 2 := Eq.trans (Eq.symm (hq 2)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 0))
  exact (sep (v 0)).2.1 (Eq.trans (hq 0) (Eq.symm (t0)))

include p q v hp hq sep in
private theorem branch42 (_h0 : v 3 = v 10) (_h1 : v 0 = v 15) (h2 : v 0 = v 11) : False := by
  have t0 : v 5 = v 1 := Eq.trans (Eq.symm (hp 6)) (Eq.trans (congrArg p (Eq.symm (h2))) (hp 0))
  have t1 : v 1 = v 4 := Eq.trans (Eq.symm (hq 3)) (Eq.trans (congrArg q (t0)) (hq 1))
  exact (sep (v 1)).2.1 (Eq.trans (hq 1) (Eq.symm (t1)))

include p q v hp hq sep in
private theorem branch5 (_h0 : v 3 = v 11) (h1 : v 0 = v 5) : False := by
  have t0 : v 1 = v 2 := Eq.trans (Eq.symm (hq 3)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 0))
  exact (sep (v 0)).2.2 (Eq.trans (hp 0) (Eq.symm (Eq.trans (hq 0) (Eq.symm (t0)))))

include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch12 (h0 : v 3 = v 11) (h1 : v 0 = v 15) (h2 : v 0 = v 16) : False := by
  have t0 : v 5 = v 7 := Eq.trans (Eq.symm (hp 6)) (Eq.trans (congrArg p (Eq.symm (h0))) (hp 2))
  have t1 : v 13 = v 1 := Eq.trans (Eq.symm (hq 4)) (Eq.trans (congrArg q (Eq.symm (t0))) (hq 3))
  have t2 : v 13 = v 12 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 8)))) (Eq.trans (congrArg p.symm (Eq.trans (Eq.symm (h2)) (h1))) (p.symm_apply_eq.mpr (Eq.symm (hp 7))))
  exact short4 p q G sep e₀ e₁ e₂ no ![0,1,0,1] (by decide)
    (v 0) (v 0) (v 1) (v 1)
    (rfl) (Eq.trans (congrArg p (Eq.trans (Eq.symm (t1)) (t2))) (Eq.trans (hp 7) (Eq.symm (h1)))) (rfl) (hp 0)

include p q v hp hq sep in
private theorem branch41 (h0 : v 3 = v 10) (_h1 : v 0 = v 15) (h2 : v 0 = v 7) : False := by
  have t0 : v 13 = v 2 := Eq.trans (Eq.symm (hq 4)) (Eq.trans (congrArg q (Eq.symm (h2))) (hq 0))
  have t1 : v 16 = v 6 := Eq.trans (Eq.symm (hp 8)) (Eq.trans (congrArg p (t0)) (hp 1))
  have t2 : v 16 = v 0 := Eq.trans (Eq.symm (hq 6)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
  have t3 : v 13 = v 3 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 8)))) (Eq.trans (congrArg p.symm (Eq.trans (t2) (h2))) (p.symm_apply_eq.mpr (Eq.symm (hp 2))))
  exact (sep (v 2)).2.2 (Eq.trans (Eq.trans (hp 1) (Eq.trans (Eq.symm (t1)) (t2))) (Eq.symm (Eq.trans (congrArg q (Eq.trans (Eq.symm (t0)) (t3))) (hq 2))))

include p q v hp hq sep in
private theorem branch48 (h0 : v 3 = v 10) (_h1 : v 0 = v 15) (h2 : v 5 = v 17) : False := by
  have t0 : v 5 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.symm (h0))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
  have t1 : v 14 = v 1 := Eq.trans (Eq.symm (hq 5)) (Eq.trans (congrArg q (Eq.symm (t0))) (hq 3))
  have t2 : v 14 = v 11 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 9)))) (Eq.trans (congrArg p.symm (Eq.symm (h2))) (p.symm_apply_eq.mpr (Eq.symm (hp 6))))
  have t3 : v 17 = v 4 := Eq.trans (Eq.symm (hq 7)) (Eq.trans (congrArg q (Eq.trans (Eq.symm (t2)) (t1))) (hq 1))
  exact (sep (v 1)).2.2 (Eq.trans (Eq.trans (congrArg p (Eq.trans (Eq.symm (t1)) (t2))) (Eq.trans (hp 6) (Eq.trans (h2) (t3)))) (Eq.symm (hq 1)))

include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch19 (h0 : v 3 = v 11) (h1 : v 0 = v 9) : False := by
  have t0 : v 17 = v 0 := Eq.trans (Eq.symm (hq 7)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
  have t1 : v 14 = v 4 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 9)))) (Eq.trans (congrArg p.symm (Eq.trans (t0) (h1))) (p.symm_apply_eq.mpr (Eq.symm (hp 3))))
  have t2 : v 8 = v 1 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 5)))) (Eq.trans (congrArg q.symm (t1)) (q.symm_apply_eq.mpr (Eq.symm (hq 1))))
  have t3 : v 15 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 9)))) (Eq.trans (congrArg q.symm (Eq.symm (h1))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
  have t4 : v 12 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 7)))) (Eq.trans (congrArg p.symm (t3)) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
  have t5 : v 6 = v 14 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (t4)) (hq 5))
  exact short8 p q G sep e₀ e₁ e₂ no ![0,2,0,1,2,1,0,2] (by decide)
    (v 0) (v 0) (v 3) (v 3) (v 1) (v 4) (v 2) (v 2)
    (rfl) (hq 2) (rfl) (Eq.trans (congrArg p (Eq.symm (t2))) (hp 5)) (hq 1) (Eq.trans (hp 1) (Eq.trans (t5) (t1))) (rfl) (hq 0)

include p q v hp hq sep in
private theorem branch43 (h0 : v 3 = v 10) (h1 : v 0 = v 15) (h2 : v 12 = v 7) : False := by
  have t0 : v 6 = v 13 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (h2)) (hq 4))
  have t1 : v 16 = v 0 := Eq.trans (Eq.symm (hq 6)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
  have t2 : v 13 = v 12 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 8)))) (Eq.trans (congrArg p.symm (Eq.trans (t1) (h1))) (p.symm_apply_eq.mpr (Eq.symm (hp 7))))
  exact (sep (v 6)).2.1 (Eq.trans (congrArg q (Eq.trans (Eq.trans (t0) (t2)) (h2))) (Eq.trans (hq 4) (Eq.symm (t0))))

include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch14 (_h0 : v 3 = v 11) (h1 : v 0 = v 15) (h2 : v 8 = v 4) : False := by
  have t0 : v 9 = v 2 := Eq.trans (Eq.symm (hq 9)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 0))
  have t1 : v 3 = v 9 := Eq.trans (Eq.symm (hp 5)) (Eq.trans (congrArg p (h2)) (hp 3))
  exact short4 p q G sep e₀ e₁ e₂ no ![0,2,0,2] (by decide)
    (v 0) (v 0) (v 2) (v 2)
    (rfl) (Eq.trans (congrArg q (Eq.trans (Eq.symm (t0)) (Eq.symm (t1)))) (hq 2)) (rfl) (hq 0)

include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch15 (_h0 : v 3 = v 11) (h1 : v 0 = v 15) (h2 : v 3 = v 4) : False := by
  have t0 : v 9 = v 7 := Eq.trans (Eq.symm (hp 3)) (Eq.trans (congrArg p (Eq.symm (h2))) (hp 2))
  have t1 : v 9 = v 2 := Eq.trans (Eq.symm (hq 9)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 0))
  exact short4 p q G sep e₀ e₁ e₂ no ![0,2,1,2] (by decide)
    (v 0) (v 0) (v 3) (v 2)
    (rfl) (hq 2) (Eq.trans (hp 2) (Eq.trans (Eq.symm (t0)) (t1))) (hq 0)

include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch25 (_h0 : v 3 = v 11) (_h1 : v 1 = v 12) (h2 : v 0 = v 10) : False := by
  exact short4 p q G sep e₀ e₁ e₂ no ![0,1,2,1] (by decide)
    (v 0) (v 0) (v 5) (v 1)
    (rfl) (Eq.trans (hp 4) (Eq.symm (h2))) (hq 3) (hp 0)

include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch28 (h0 : v 3 = v 11) (h1 : v 1 = v 12) (h2 : v 8 = v 2) : False := by
  have t0 : v 17 = v 0 := Eq.trans (Eq.symm (hq 7)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
  have t1 : v 3 = v 6 := Eq.trans (Eq.symm (hp 5)) (Eq.trans (congrArg p (h2)) (hp 1))
  have t2 : v 6 = v 4 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 1))
  exact short8 p q G sep e₀ e₁ e₂ no ![0,1,0,2,1,2,0,1] (by decide)
    (v 0) (v 0) (v 14) (v 14) (v 2) (v 3) (v 1) (v 1)
    (rfl) (Eq.trans (hp 9) (t0)) (rfl) (Eq.trans (congrArg q (Eq.symm (h2))) (hq 5)) (Eq.trans (hp 1) (Eq.symm (t1))) (Eq.trans (hq 1) (Eq.trans (Eq.symm (t2)) (Eq.symm (t1)))) (rfl) (hp 0)

include p q v hq sep G e₀ e₁ e₂ no in
private theorem branch29 (_h0 : v 3 = v 11) (_h1 : v 1 = v 12) (h2 : v 3 = v 2) : False := by
  exact short4 p q G sep e₀ e₁ e₂ no ![0,2,0,2] (by decide)
    (v 0) (v 0) (v 2) (v 2)
    (rfl) (Eq.trans (congrArg q (Eq.symm (h2))) (hq 2)) (rfl) (hq 0)

include p q v hq sep G e₀ e₁ e₂ no in
private theorem branch47 (_h0 : v 3 = v 10) (_h1 : v 0 = v 15) (h2 : v 3 = v 2) : False := by
  exact short4 p q G sep e₀ e₁ e₂ no ![0,2,0,2] (by decide)
    (v 0) (v 0) (v 2) (v 2)
    (rfl) (Eq.trans (congrArg q (Eq.symm (h2))) (hq 2)) (rfl) (hq 0)

include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch49 (_h0 : v 3 = v 10) (_h1 : v 0 = v 15) (h2 : v 5 = v 2) : False := by
  exact short4 p q G sep e₀ e₁ e₂ no ![1,2,0,2] (by decide)
    (v 0) (v 1) (v 2) (v 2)
    (hp 0) (Eq.trans (congrArg q (Eq.symm (h2))) (hq 3)) (rfl) (hq 0)

include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch60 (h0 : v 3 = v 10) (h1 : v 1 = v 12) (h2 : v 3 = v 4) : False := by
  have t0 : v 6 = v 4 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 1))
  have t1 : v 2 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 1)))) (Eq.trans (congrArg p.symm (Eq.trans (t0) (Eq.symm (h2)))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
  have t2 : v 5 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.symm (h0))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
  exact short4 p q G sep e₀ e₁ e₂ no ![1,2,0,2] (by decide)
    (v 0) (v 1) (v 2) (v 2)
    (hp 0) (Eq.trans (congrArg q (Eq.trans (t1) (Eq.symm (t2)))) (hq 3)) (rfl) (hq 0)

include p q v hq sep G e₀ e₁ e₂ no in
private theorem branch61 (_h0 : v 3 = v 10) (_h1 : v 1 = v 12) (h2 : v 5 = v 4) : False := by
  exact short4 p q G sep e₀ e₁ e₂ no ![0,2,0,2] (by decide)
    (v 1) (v 1) (v 4) (v 4)
    (rfl) (Eq.trans (congrArg q (Eq.symm (h2))) (hq 3)) (rfl) (hq 1)

include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch13 (h0 : v 3 = v 11) (h1 : v 0 = v 15) (h2 : v 12 = v 16) : False := by
  have t0 : v 5 = v 7 := Eq.trans (Eq.symm (hp 6)) (Eq.trans (congrArg p (Eq.symm (h0))) (hp 2))
  have t1 : v 13 = v 1 := Eq.trans (Eq.symm (hq 4)) (Eq.trans (congrArg q (Eq.symm (t0))) (hq 3))
  have t2 : v 9 = v 2 := Eq.trans (Eq.symm (hq 9)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 0))
  exact short8 p q G sep e₀ e₁ e₂ no ![0,1,0,1,2,0,1,2] (by decide)
    (v 0) (v 0) (v 12) (v 12) (v 1) (v 4) (v 4) (v 2)
    (rfl) (Eq.trans (hp 7) (Eq.symm (h1))) (rfl) (Eq.trans (congrArg p (Eq.symm (t1))) (Eq.trans (hp 8) (Eq.symm (h2)))) (hq 1) (rfl) (Eq.trans (hp 3) (t2)) (hq 0)

include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch16 (_h0 : v 3 = v 11) (h1 : v 0 = v 15) (h2 : v 5 = v 4) : False := by
  have t0 : v 9 = v 2 := Eq.trans (Eq.symm (hq 9)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 0))
  exact short4 p q G sep e₀ e₁ e₂ no ![1,2,1,2] (by decide)
    (v 0) (v 1) (v 4) (v 2)
    (hp 0) (Eq.trans (congrArg q (Eq.symm (h2))) (hq 3)) (Eq.trans (hp 3) (t0)) (hq 0)

include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch27 (h0 : v 3 = v 11) (h1 : v 1 = v 12) (h2 : v 14 = v 15) : False := by
  have t0 : v 17 = v 0 := Eq.trans (Eq.symm (hq 7)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
  have t1 : v 6 = v 4 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 1))
  exact short8 p q G sep e₀ e₁ e₂ no ![0,1,0,1,2,1,0,2] (by decide)
    (v 0) (v 0) (v 14) (v 14) (v 1) (v 4) (v 2) (v 2)
    (rfl) (Eq.trans (hp 9) (t0)) (rfl) (Eq.trans (congrArg p (h1)) (Eq.trans (hp 7) (Eq.symm (h2)))) (hq 1) (Eq.trans (hp 1) (t1)) (rfl) (hq 0)

include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch30 (h0 : v 3 = v 11) (_h1 : v 1 = v 12) (h2 : v 5 = v 2) : False := by
  have t0 : v 5 = v 7 := Eq.trans (Eq.symm (hp 6)) (Eq.trans (congrArg p (Eq.symm (h0))) (hp 2))
  exact short4 p q G sep e₀ e₁ e₂ no ![0,2,1,2] (by decide)
    (v 0) (v 0) (v 3) (v 2)
    (rfl) (hq 2) (Eq.trans (hp 2) (Eq.trans (Eq.symm (t0)) (h2))) (hq 0)

include p q v hp hq sep in
private theorem branch36 (h0 : v 3 = v 5) : False := by
  have t0 : v 1 = v 0 := Eq.trans (Eq.symm (hq 3)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
  exact (sep (v 0)).1 (Eq.trans (hp 0) (t0))

include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch44 (h0 : v 3 = v 10) (h1 : v 0 = v 15) (h2 : v 12 = v 17) : False := by
  have t0 : v 5 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.symm (h0))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
  have t1 : v 14 = v 1 := Eq.trans (Eq.symm (hq 5)) (Eq.trans (congrArg q (Eq.symm (t0))) (hq 3))
  have t2 : v 9 = v 2 := Eq.trans (Eq.symm (hq 9)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 0))
  exact short8 p q G sep e₀ e₁ e₂ no ![0,1,0,1,2,0,1,2] (by decide)
    (v 0) (v 0) (v 12) (v 12) (v 1) (v 4) (v 4) (v 2)
    (rfl) (Eq.trans (hp 7) (Eq.symm (h1))) (rfl) (Eq.trans (congrArg p (Eq.symm (t1))) (Eq.trans (hp 9) (Eq.symm (h2)))) (hq 1) (rfl) (Eq.trans (hp 3) (t2)) (hq 0)

include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch46 (_h0 : v 3 = v 10) (_h1 : v 0 = v 15) (h2 : v 7 = v 2) : False := by
  exact short4 p q G sep e₀ e₁ e₂ no ![0,2,1,2] (by decide)
    (v 0) (v 0) (v 3) (v 2)
    (rfl) (hq 2) (Eq.trans (hp 2) (h2)) (hq 0)

include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch57 (h0 : v 3 = v 10) (h1 : v 1 = v 12) (h2 : v 13 = v 15) : False := by
  have t0 : v 16 = v 0 := Eq.trans (Eq.symm (hq 6)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
  have t1 : v 6 = v 4 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 1))
  exact short8 p q G sep e₀ e₁ e₂ no ![0,1,0,1,2,1,0,2] (by decide)
    (v 0) (v 0) (v 13) (v 13) (v 1) (v 4) (v 2) (v 2)
    (rfl) (Eq.trans (hp 8) (t0)) (rfl) (Eq.trans (congrArg p (h1)) (Eq.trans (hp 7) (Eq.symm (h2)))) (hq 1) (Eq.trans (hp 1) (t1)) (rfl) (hq 0)

include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch59 (_h0 : v 3 = v 10) (h1 : v 1 = v 12) (h2 : v 7 = v 4) : False := by
  have t0 : v 6 = v 4 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 1))
  have t1 : v 3 = v 2 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 2)))) (Eq.trans (congrArg p.symm (Eq.trans (h2) (Eq.symm (t0)))) (p.symm_apply_eq.mpr (Eq.symm (hp 1))))
  exact short4 p q G sep e₀ e₁ e₂ no ![0,2,0,2] (by decide)
    (v 0) (v 0) (v 2) (v 2)
    (rfl) (Eq.trans (congrArg q (Eq.symm (t1))) (hq 2)) (rfl) (hq 0)

include p q v hp sep in
private theorem branch1 (h0 : v 3 = v 8) : False := by
  have t0 : v 3 = v 7 := Eq.trans (Eq.symm (hp 5)) (Eq.trans (congrArg p (Eq.symm (h0))) (hp 2))
  exact (sep (v 3)).1 (Eq.trans (hp 2) (Eq.symm (t0)))

include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch17 (_h0 : v 3 = v 11) (_h1 : v 0 = v 15) (h2 : v 10 = v 4) : False := by
  exact short4 p q G sep e₀ e₁ e₂ no ![0,2,1,2] (by decide)
    (v 1) (v 1) (v 5) (v 4)
    (rfl) (hq 3) (Eq.trans (hp 4) (h2)) (hq 1)

include p q v hp hq sep in
private theorem branch18 (_h0 : v 3 = v 11) (h1 : v 0 = v 12) : False := by
  have t0 : v 6 = v 2 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 0))
  exact (sep (v 2)).1 (Eq.trans (hp 1) (t0))

include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch26 (h0 : v 3 = v 11) (h1 : v 1 = v 12) (h2 : v 14 = v 10) : False := by
  have t0 : v 17 = v 0 := Eq.trans (Eq.symm (hq 7)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
  have t1 : v 5 = v 7 := Eq.trans (Eq.symm (hp 6)) (Eq.trans (congrArg p (Eq.symm (h0))) (hp 2))
  have t2 : v 13 = v 1 := Eq.trans (Eq.symm (hq 4)) (Eq.trans (congrArg q (Eq.symm (t1))) (hq 3))
  have t3 : v 16 = v 15 := Eq.trans (Eq.symm (hp 8)) (Eq.trans (congrArg p (Eq.trans (t2) (h1))) (hp 7))
  have t4 : v 6 = v 4 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 1))
  exact short8 p q G sep e₀ e₁ e₂ no ![0,1,2,1,2,1,0,2] (by decide)
    (v 0) (v 0) (v 10) (v 15) (v 1) (v 4) (v 2) (v 2)
    (rfl) (Eq.trans (congrArg p (Eq.symm (h2))) (Eq.trans (hp 9) (t0))) (Eq.trans (hq 6) (t3)) (Eq.trans (congrArg p (h1)) (hp 7)) (hq 1) (Eq.trans (hp 1) (t4)) (rfl) (hq 0)

include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch31 (_h0 : v 3 = v 11) (_h1 : v 1 = v 12) (h2 : v 10 = v 2) : False := by
  exact short4 p q G sep e₀ e₁ e₂ no ![1,2,1,2] (by decide)
    (v 0) (v 1) (v 5) (v 2)
    (hp 0) (hq 3) (Eq.trans (hp 4) (h2)) (hq 0)

include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch45 (h0 : v 3 = v 10) (h1 : v 0 = v 15) (h2 : v 7 = v 4) : False := by
  have t0 : v 16 = v 0 := Eq.trans (Eq.symm (hq 6)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
  have t1 : v 13 = v 12 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 8)))) (Eq.trans (congrArg p.symm (Eq.trans (t0) (h1))) (p.symm_apply_eq.mpr (Eq.symm (hp 7))))
  exact short8 p q G sep e₀ e₁ e₂ no ![0,1,0,2,0,2,0,1] (by decide)
    (v 0) (v 0) (v 12) (v 12) (v 4) (v 4) (v 1) (v 1)
    (rfl) (Eq.trans (hp 7) (Eq.symm (h1))) (rfl) (Eq.trans (congrArg q (Eq.symm (h2))) (Eq.trans (hq 4) (t1))) (rfl) (hq 1) (rfl) (hp 0)

include p q v hp hq sep in
private theorem branch50 (_h0 : v 3 = v 10) (h1 : v 0 = v 12) : False := by
  have t0 : v 6 = v 2 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 0))
  exact (sep (v 2)).1 (Eq.trans (hp 1) (t0))

include p q v hq sep in
private theorem branch56 (_h0 : v 3 = v 10) (_h1 : v 1 = v 12) (h2 : v 13 = v 7) : False := by
  exact (sep (v 7)).2.1 (Eq.trans (hq 4) (h2))

include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch58 (_h0 : v 3 = v 10) (_h1 : v 1 = v 12) (h2 : v 7 = v 2) : False := by
  exact short4 p q G sep e₀ e₁ e₂ no ![0,2,1,2] (by decide)
    (v 0) (v 0) (v 3) (v 2)
    (rfl) (hq 2) (Eq.trans (hp 2) (h2)) (hq 0)

include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch8 (h0 : v 3 = v 11) (h1 : v 0 = v 15) : False := by
  have t0 : v 17 = v 0 := Eq.trans (Eq.symm (hq 7)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
  have t1 : v 14 = v 12 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 9)))) (Eq.trans (congrArg p.symm (Eq.trans (t0) (h1))) (p.symm_apply_eq.mpr (Eq.symm (hp 7))))
  have t2 : v 5 = v 7 := Eq.trans (Eq.symm (hp 6)) (Eq.trans (congrArg p (Eq.symm (h0))) (hp 2))
  have t3 : v 13 = v 1 := Eq.trans (Eq.symm (hq 4)) (Eq.trans (congrArg q (Eq.symm (t2))) (hq 3))
  have t4 : v 9 = v 2 := Eq.trans (Eq.symm (hq 9)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 0))
  rcases collision16 (fun h => no (.inr (.inr h)))
    (v 0) (v 0) (v 12) (v 12) (v 8) (v 3) (v 3) (v 5) (v 5) (v 10) (v 10) (v 16) (v 1) (v 4) (v 4) (v 2)
    (e₀ (v 0))
    ((Eq.trans (hp 7) (Eq.symm (h1))) ▸ e₁ (v 12))
    (e₀ (v 12))
    ((Eq.trans (hq 5) (t1)) ▸ e₂ (v 8))
    ((hp 5) ▸ e₁ (v 8))
    (e₀ (v 3))
    ((Eq.trans (hp 2) (Eq.symm (t2))) ▸ e₁ (v 3))
    (e₀ (v 5))
    ((hp 4) ▸ e₁ (v 5))
    (e₀ (v 10))
    ((hq 6) ▸ e₂ (v 10))
    ((Eq.trans (congrArg p (Eq.symm (t3))) (hp 8)) ▸ e₁ (v 1))
    ((hq 1) ▸ e₂ (v 1))
    (e₀ (v 4))
    ((Eq.trans (hp 3) (t4)) ▸ e₁ (v 4))
    ((hq 0) ▸ e₂ (v 0)) with hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit
  · exact branch9 p q v hp sep (h0) (h1) (hit)
  · exact branch10 p q v hp hq sep (h0) (h1) (hit)
  · exact branch11 p q v hq sep (h0) (h1) (hit)
  · have t0 : v 10 = v 1 := Eq.trans (Eq.symm (hp 4)) (Eq.trans (congrArg p (Eq.symm (hit))) (hp 0))
    have t1 : v 16 = v 4 := Eq.trans (Eq.symm (hq 6)) (Eq.trans (congrArg q (t0)) (hq 1))
    have t2 : v 9 = v 2 := Eq.trans (Eq.symm (hq 9)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 0))
    have t3 : v 1 = v 2 := Eq.trans (Eq.symm (hq 3)) (Eq.trans (congrArg q (Eq.symm (hit))) (hq 0))
    have t4 : v 4 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 3)))) (Eq.trans (congrArg p.symm (Eq.trans (t2) (Eq.symm (t3)))) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    have t5 : v 13 = v 11 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 8)))) (Eq.trans (congrArg p.symm (Eq.trans (Eq.trans (t1) (t4)) (hit))) (p.symm_apply_eq.mpr (Eq.symm (hp 6))))
    have t6 : v 5 = v 7 := Eq.trans (Eq.symm (hp 6)) (Eq.trans (congrArg p (Eq.symm (h0))) (hp 2))
    have t7 : v 13 = v 2 := Eq.trans (Eq.symm (hq 4)) (Eq.trans (congrArg q (Eq.trans (Eq.symm (t6)) (Eq.symm (hit)))) (hq 0))
    have t8 : v 8 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 5)))) (Eq.trans (congrArg p.symm (Eq.trans (Eq.trans (Eq.trans (h0) (Eq.symm (t5))) (t7)) (Eq.symm (t3)))) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    exact branch10 p q v hp hq sep (h0) (h1) (Eq.symm (t8))
  · have t0 : v 16 = v 2 := Eq.trans (Eq.symm (hq 6)) (Eq.trans (congrArg q (Eq.symm (hit))) (hq 0))
    have t1 : v 9 = v 2 := Eq.trans (Eq.symm (hq 9)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 0))
    have t2 : v 13 = v 4 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 8)))) (Eq.trans (congrArg p.symm (Eq.trans (t0) (Eq.symm (t1)))) (p.symm_apply_eq.mpr (Eq.symm (hp 3))))
    have t3 : v 5 = v 7 := Eq.trans (Eq.symm (hp 6)) (Eq.trans (congrArg p (Eq.symm (h0))) (hp 2))
    have t4 : v 13 = v 1 := Eq.trans (Eq.symm (hq 4)) (Eq.trans (congrArg q (Eq.symm (t3))) (hq 3))
    have t5 : v 1 = v 5 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 1)))) (Eq.trans (congrArg q.symm (Eq.trans (Eq.symm (t2)) (t4))) (q.symm_apply_eq.mpr (Eq.symm (hq 3))))
    have t6 : v 11 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 6)))) (Eq.trans (congrArg p.symm (Eq.symm (t5))) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    exact branch11 p q v hq sep (h0) (h1) (Eq.trans (Eq.symm (t6)) (Eq.symm (h0)))
  · have t0 : v 4 = v 2 := Eq.trans (Eq.symm (hq 1)) (Eq.trans (congrArg q (Eq.symm (hit))) (hq 0))
    have t1 : v 9 = v 6 := Eq.trans (Eq.symm (hp 3)) (Eq.trans (congrArg p (t0)) (hp 1))
    have t2 : v 15 = v 12 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 9)))) (Eq.trans (congrArg q.symm (t1)) (q.symm_apply_eq.mpr (Eq.symm (hq 8))))
    exact branch9 p q v hp sep (h0) (h1) (Eq.trans (h1) (t2))
  · have t0 : v 1 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 1)))) (Eq.trans (congrArg q.symm (Eq.symm (hit))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    have t1 : v 8 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 5)))) (Eq.trans (congrArg p.symm (Eq.symm (t0))) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    exact branch10 p q v hp hq sep (h0) (h1) (Eq.symm (t1))
  · exact branch9 p q v hp sep (h0) (h1) (hit)
  · exact branch11 p q v hq sep (h0) (h1) (hit)
  · have t0 : v 10 = v 1 := Eq.trans (Eq.symm (hp 4)) (Eq.trans (congrArg p (Eq.symm (hit))) (hp 0))
    have t1 : v 16 = v 4 := Eq.trans (Eq.symm (hq 6)) (Eq.trans (congrArg q (t0)) (hq 1))
    have t2 : v 9 = v 2 := Eq.trans (Eq.symm (hq 9)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 0))
    have t3 : v 1 = v 2 := Eq.trans (Eq.symm (hq 3)) (Eq.trans (congrArg q (Eq.symm (hit))) (hq 0))
    have t4 : v 4 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 3)))) (Eq.trans (congrArg p.symm (Eq.trans (t2) (Eq.symm (t3)))) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    have t5 : v 13 = v 11 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 8)))) (Eq.trans (congrArg p.symm (Eq.trans (Eq.trans (t1) (t4)) (hit))) (p.symm_apply_eq.mpr (Eq.symm (hp 6))))
    have t6 : v 5 = v 7 := Eq.trans (Eq.symm (hp 6)) (Eq.trans (congrArg p (Eq.symm (h0))) (hp 2))
    have t7 : v 13 = v 2 := Eq.trans (Eq.symm (hq 4)) (Eq.trans (congrArg q (Eq.trans (Eq.symm (t6)) (Eq.symm (hit)))) (hq 0))
    have t8 : v 8 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 5)))) (Eq.trans (congrArg p.symm (Eq.trans (Eq.trans (Eq.trans (h0) (Eq.symm (t5))) (t7)) (Eq.symm (t3)))) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    exact branch10 p q v hp hq sep (h0) (h1) (Eq.symm (t8))
  · have t0 : v 16 = v 2 := Eq.trans (Eq.symm (hq 6)) (Eq.trans (congrArg q (Eq.symm (hit))) (hq 0))
    have t1 : v 9 = v 2 := Eq.trans (Eq.symm (hq 9)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 0))
    have t2 : v 13 = v 4 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 8)))) (Eq.trans (congrArg p.symm (Eq.trans (t0) (Eq.symm (t1)))) (p.symm_apply_eq.mpr (Eq.symm (hp 3))))
    have t3 : v 5 = v 7 := Eq.trans (Eq.symm (hp 6)) (Eq.trans (congrArg p (Eq.symm (h0))) (hp 2))
    have t4 : v 13 = v 1 := Eq.trans (Eq.symm (hq 4)) (Eq.trans (congrArg q (Eq.symm (t3))) (hq 3))
    have t5 : v 1 = v 5 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 1)))) (Eq.trans (congrArg q.symm (Eq.trans (Eq.symm (t2)) (t4))) (q.symm_apply_eq.mpr (Eq.symm (hq 3))))
    have t6 : v 11 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 6)))) (Eq.trans (congrArg p.symm (Eq.symm (t5))) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    exact branch11 p q v hq sep (h0) (h1) (Eq.trans (Eq.symm (t6)) (Eq.symm (h0)))
  · exact branch12 p q v hp hq sep G e₀ e₁ e₂ no (h0) (h1) (hit)
  · have t0 : v 1 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 1)))) (Eq.trans (congrArg q.symm (Eq.symm (hit))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    have t1 : v 8 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 5)))) (Eq.trans (congrArg p.symm (Eq.symm (t0))) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    exact branch10 p q v hp hq sep (h0) (h1) (Eq.symm (t1))
  · have t0 : v 0 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 0)))) (Eq.trans (congrArg q.symm (Eq.symm (hit))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    exact branch11 p q v hq sep (h0) (h1) (t0)
  · have t0 : v 15 = v 3 := Eq.trans (Eq.symm (hp 7)) (Eq.trans (congrArg p (hit)) (hp 5))
    exact branch11 p q v hq sep (h0) (h1) (Eq.trans (h1) (t0))
  · have t0 : v 15 = v 7 := Eq.trans (Eq.symm (hp 7)) (Eq.trans (congrArg p (hit)) (hp 2))
    have t1 : v 5 = v 7 := Eq.trans (Eq.symm (hp 6)) (Eq.trans (congrArg p (Eq.symm (h0))) (hp 2))
    have t2 : v 17 = v 0 := Eq.trans (Eq.symm (hq 7)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
    have t3 : v 14 = v 12 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 9)))) (Eq.trans (congrArg p.symm (Eq.trans (t2) (h1))) (p.symm_apply_eq.mpr (Eq.symm (hp 7))))
    have t4 : v 6 = v 0 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (hit)) (hq 2))
    have t5 : v 2 = v 11 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 1)))) (Eq.trans (congrArg p.symm (Eq.trans (Eq.trans (Eq.trans (t4) (h1)) (t0)) (Eq.symm (t1)))) (p.symm_apply_eq.mpr (Eq.symm (hp 6))))
    have t6 : v 1 = v 2 := Eq.trans (Eq.symm (hq 3)) (Eq.trans (congrArg q (Eq.trans (Eq.trans (t1) (Eq.symm (t0))) (Eq.symm (h1)))) (hq 0))
    have t7 : v 8 = v 5 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 5)))) (Eq.trans (congrArg q.symm (Eq.trans (Eq.trans (Eq.trans (Eq.trans (t3) (hit)) (h0)) (Eq.symm (t5))) (Eq.symm (t6)))) (q.symm_apply_eq.mpr (Eq.symm (hq 3))))
    exact branch10 p q v hp hq sep (h0) (h1) (Eq.trans (Eq.trans (Eq.trans (h1) (t0)) (Eq.symm (t1))) (Eq.symm (t7)))
  · have t0 : v 9 = v 2 := Eq.trans (Eq.symm (hq 9)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 0))
    have t1 : v 6 = v 1 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (hit)) (hq 3))
    have t2 : v 2 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 1)))) (Eq.trans (congrArg p.symm (t1)) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    have t3 : v 15 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 9)))) (Eq.trans (congrArg q.symm (Eq.trans (t0) (t2))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    exact branch11 p q v hq sep (h0) (h1) (Eq.trans (h1) (t3))
  · have t0 : v 9 = v 2 := Eq.trans (Eq.symm (hq 9)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 0))
    have t1 : v 6 = v 16 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (hit)) (hq 6))
    have t2 : v 13 = v 2 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 8)))) (Eq.trans (congrArg p.symm (Eq.symm (t1))) (p.symm_apply_eq.mpr (Eq.symm (hp 1))))
    have t3 : v 5 = v 7 := Eq.trans (Eq.symm (hp 6)) (Eq.trans (congrArg p (Eq.symm (h0))) (hp 2))
    have t4 : v 13 = v 1 := Eq.trans (Eq.symm (hq 4)) (Eq.trans (congrArg q (Eq.symm (t3))) (hq 3))
    have t5 : v 15 = v 5 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 9)))) (Eq.trans (congrArg q.symm (Eq.trans (Eq.trans (t0) (Eq.symm (t2))) (t4))) (q.symm_apply_eq.mpr (Eq.symm (hq 3))))
    have t6 : v 17 = v 0 := Eq.trans (Eq.symm (hq 7)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
    have t7 : v 14 = v 12 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 9)))) (Eq.trans (congrArg p.symm (Eq.trans (t6) (h1))) (p.symm_apply_eq.mpr (Eq.symm (hp 7))))
    have t8 : v 10 = v 1 := Eq.trans (Eq.symm (hp 4)) (Eq.trans (congrArg p (Eq.trans (Eq.symm (t5)) (Eq.symm (h1)))) (hp 0))
    have t9 : v 8 = v 5 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 5)))) (Eq.trans (congrArg q.symm (Eq.trans (Eq.trans (t7) (hit)) (t8))) (q.symm_apply_eq.mpr (Eq.symm (hq 3))))
    exact branch10 p q v hp hq sep (h0) (h1) (Eq.trans (Eq.trans (h1) (t5)) (Eq.symm (t9)))
  · have t0 : v 5 = v 7 := Eq.trans (Eq.symm (hp 6)) (Eq.trans (congrArg p (Eq.symm (h0))) (hp 2))
    have t1 : v 13 = v 1 := Eq.trans (Eq.symm (hq 4)) (Eq.trans (congrArg q (Eq.symm (t0))) (hq 3))
    have t2 : v 16 = v 15 := Eq.trans (Eq.symm (hp 8)) (Eq.trans (congrArg p (Eq.trans (t1) (Eq.symm (hit)))) (hp 7))
    exact branch12 p q v hp hq sep G e₀ e₁ e₂ no (h0) (h1) (Eq.trans (h1) (Eq.symm (t2)))
  · have t0 : v 9 = v 2 := Eq.trans (Eq.symm (hq 9)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 0))
    have t1 : v 15 = v 9 := Eq.trans (Eq.symm (hp 7)) (Eq.trans (congrArg p (hit)) (hp 3))
    have t2 : v 0 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 0)))) (Eq.trans (congrArg q.symm (Eq.trans (Eq.trans (Eq.symm (t0)) (Eq.symm (t1))) (Eq.symm (h1)))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    exact branch11 p q v hq sep (h0) (h1) (t2)
  · have t0 : v 15 = v 7 := Eq.trans (Eq.symm (hp 7)) (Eq.trans (congrArg p (hit)) (hp 2))
    have t1 : v 5 = v 7 := Eq.trans (Eq.symm (hp 6)) (Eq.trans (congrArg p (Eq.symm (h0))) (hp 2))
    have t2 : v 17 = v 0 := Eq.trans (Eq.symm (hq 7)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
    have t3 : v 14 = v 12 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 9)))) (Eq.trans (congrArg p.symm (Eq.trans (t2) (h1))) (p.symm_apply_eq.mpr (Eq.symm (hp 7))))
    have t4 : v 6 = v 0 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (hit)) (hq 2))
    have t5 : v 2 = v 11 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 1)))) (Eq.trans (congrArg p.symm (Eq.trans (Eq.trans (Eq.trans (t4) (h1)) (t0)) (Eq.symm (t1)))) (p.symm_apply_eq.mpr (Eq.symm (hp 6))))
    have t6 : v 1 = v 2 := Eq.trans (Eq.symm (hq 3)) (Eq.trans (congrArg q (Eq.trans (Eq.trans (t1) (Eq.symm (t0))) (Eq.symm (h1)))) (hq 0))
    have t7 : v 8 = v 5 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 5)))) (Eq.trans (congrArg q.symm (Eq.trans (Eq.trans (Eq.trans (Eq.trans (t3) (hit)) (h0)) (Eq.symm (t5))) (Eq.symm (t6)))) (q.symm_apply_eq.mpr (Eq.symm (hq 3))))
    exact branch10 p q v hp hq sep (h0) (h1) (Eq.trans (Eq.trans (Eq.trans (h1) (t0)) (Eq.symm (t1))) (Eq.symm (t7)))
  · have t0 : v 9 = v 2 := Eq.trans (Eq.symm (hq 9)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 0))
    have t1 : v 6 = v 1 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (hit)) (hq 3))
    have t2 : v 2 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 1)))) (Eq.trans (congrArg p.symm (t1)) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    have t3 : v 15 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 9)))) (Eq.trans (congrArg q.symm (Eq.trans (t0) (t2))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    exact branch11 p q v hq sep (h0) (h1) (Eq.trans (h1) (t3))
  · have t0 : v 9 = v 2 := Eq.trans (Eq.symm (hq 9)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 0))
    have t1 : v 6 = v 16 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (hit)) (hq 6))
    have t2 : v 13 = v 2 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 8)))) (Eq.trans (congrArg p.symm (Eq.symm (t1))) (p.symm_apply_eq.mpr (Eq.symm (hp 1))))
    have t3 : v 5 = v 7 := Eq.trans (Eq.symm (hp 6)) (Eq.trans (congrArg p (Eq.symm (h0))) (hp 2))
    have t4 : v 13 = v 1 := Eq.trans (Eq.symm (hq 4)) (Eq.trans (congrArg q (Eq.symm (t3))) (hq 3))
    have t5 : v 15 = v 5 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 9)))) (Eq.trans (congrArg q.symm (Eq.trans (Eq.trans (t0) (Eq.symm (t2))) (t4))) (q.symm_apply_eq.mpr (Eq.symm (hq 3))))
    have t6 : v 17 = v 0 := Eq.trans (Eq.symm (hq 7)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
    have t7 : v 14 = v 12 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 9)))) (Eq.trans (congrArg p.symm (Eq.trans (t6) (h1))) (p.symm_apply_eq.mpr (Eq.symm (hp 7))))
    have t8 : v 10 = v 1 := Eq.trans (Eq.symm (hp 4)) (Eq.trans (congrArg p (Eq.trans (Eq.symm (t5)) (Eq.symm (h1)))) (hp 0))
    have t9 : v 8 = v 5 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 5)))) (Eq.trans (congrArg q.symm (Eq.trans (Eq.trans (t7) (hit)) (t8))) (q.symm_apply_eq.mpr (Eq.symm (hq 3))))
    exact branch10 p q v hp hq sep (h0) (h1) (Eq.trans (Eq.trans (h1) (t5)) (Eq.symm (t9)))
  · exact branch13 p q v hp hq sep G e₀ e₁ e₂ no (h0) (h1) (hit)
  · have t0 : v 9 = v 2 := Eq.trans (Eq.symm (hq 9)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 0))
    have t1 : v 15 = v 9 := Eq.trans (Eq.symm (hp 7)) (Eq.trans (congrArg p (hit)) (hp 3))
    have t2 : v 0 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 0)))) (Eq.trans (congrArg q.symm (Eq.trans (Eq.trans (Eq.symm (t0)) (Eq.symm (t1))) (Eq.symm (h1)))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    exact branch11 p q v hq sep (h0) (h1) (t2)
  · have t0 : v 17 = v 0 := Eq.trans (Eq.symm (hq 7)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
    have t1 : v 14 = v 12 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 9)))) (Eq.trans (congrArg p.symm (Eq.trans (t0) (h1))) (p.symm_apply_eq.mpr (Eq.symm (hp 7))))
    have t2 : v 8 = v 0 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 5)))) (Eq.trans (congrArg q.symm (Eq.trans (t1) (hit))) (q.symm_apply_eq.mpr (Eq.symm (hq 0))))
    exact branch10 p q v hp hq sep (h0) (h1) (Eq.symm (t2))
  · have t0 : v 14 = v 0 := Eq.trans (Eq.symm (hq 5)) (Eq.trans (congrArg q (hit)) (hq 2))
    have t1 : v 17 = v 0 := Eq.trans (Eq.symm (hq 7)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
    have t2 : v 14 = v 12 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 9)))) (Eq.trans (congrArg p.symm (Eq.trans (t1) (h1))) (p.symm_apply_eq.mpr (Eq.symm (hp 7))))
    exact branch9 p q v hp sep (h0) (h1) (Eq.trans (Eq.symm (t0)) (t2))
  · have t0 : v 3 = v 10 := Eq.trans (Eq.symm (hp 5)) (Eq.trans (congrArg p (hit)) (hp 4))
    have t1 : v 16 = v 0 := Eq.trans (Eq.symm (hq 6)) (Eq.trans (congrArg q (Eq.symm (t0))) (hq 2))
    exact branch12 p q v hp hq sep G e₀ e₁ e₂ no (h0) (h1) (Eq.symm (t1))
  · have t0 : v 17 = v 0 := Eq.trans (Eq.symm (hq 7)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
    have t1 : v 14 = v 12 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 9)))) (Eq.trans (congrArg p.symm (Eq.trans (t0) (h1))) (p.symm_apply_eq.mpr (Eq.symm (hp 7))))
    have t2 : v 16 = v 14 := Eq.trans (Eq.symm (hq 6)) (Eq.trans (congrArg q (Eq.symm (hit))) (hq 5))
    exact branch13 p q v hp hq sep G e₀ e₁ e₂ no (h0) (h1) (Eq.trans (Eq.symm (t1)) (Eq.symm (t2)))
  · have t0 : v 9 = v 2 := Eq.trans (Eq.symm (hq 9)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 0))
    have t1 : v 14 = v 4 := Eq.trans (Eq.symm (hq 5)) (Eq.trans (congrArg q (hit)) (hq 1))
    have t2 : v 17 = v 9 := Eq.trans (Eq.symm (hp 9)) (Eq.trans (congrArg p (t1)) (hp 3))
    have t3 : v 17 = v 0 := Eq.trans (Eq.symm (hq 7)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
    have t4 : v 0 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 0)))) (Eq.trans (congrArg q.symm (Eq.trans (Eq.trans (Eq.symm (t0)) (Eq.symm (t2))) (t3))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    exact branch11 p q v hq sep (h0) (h1) (t4)
  · exact branch14 p q v hp hq sep G e₀ e₁ e₂ no (h0) (h1) (hit)
  · have t0 : v 11 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 6)))) (Eq.trans (congrArg p.symm (Eq.symm (hit))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t1 : v 14 = v 0 := Eq.trans (Eq.symm (hq 5)) (Eq.trans (congrArg q (Eq.trans (Eq.symm (t0)) (Eq.symm (h0)))) (hq 2))
    have t2 : v 17 = v 0 := Eq.trans (Eq.symm (hq 7)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
    have t3 : v 14 = v 12 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 9)))) (Eq.trans (congrArg p.symm (Eq.trans (t2) (h1))) (p.symm_apply_eq.mpr (Eq.symm (hp 7))))
    exact branch9 p q v hp sep (h0) (h1) (Eq.trans (Eq.symm (t1)) (t3))
  · have t0 : v 16 = v 0 := Eq.trans (Eq.symm (hq 6)) (Eq.trans (congrArg q (Eq.symm (hit))) (hq 2))
    exact branch12 p q v hp hq sep G e₀ e₁ e₂ no (h0) (h1) (Eq.symm (t0))
  · have t0 : v 9 = v 2 := Eq.trans (Eq.symm (hq 9)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 0))
    have t1 : v 17 = v 0 := Eq.trans (Eq.symm (hq 7)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
    have t2 : v 14 = v 12 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 9)))) (Eq.trans (congrArg p.symm (Eq.trans (t1) (h1))) (p.symm_apply_eq.mpr (Eq.symm (hp 7))))
    have t3 : v 13 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 8)))) (Eq.trans (congrArg p.symm (Eq.symm (hit))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t4 : v 5 = v 7 := Eq.trans (Eq.symm (hp 6)) (Eq.trans (congrArg p (Eq.symm (h0))) (hp 2))
    have t5 : v 13 = v 1 := Eq.trans (Eq.symm (hq 4)) (Eq.trans (congrArg q (Eq.symm (t4))) (hq 3))
    have t6 : v 14 = v 4 := Eq.trans (Eq.symm (hq 5)) (Eq.trans (congrArg q (Eq.trans (Eq.symm (t3)) (t5))) (hq 1))
    have t7 : v 15 = v 9 := Eq.trans (Eq.symm (hp 7)) (Eq.trans (congrArg p (Eq.trans (Eq.symm (t2)) (t6))) (hp 3))
    have t8 : v 0 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 0)))) (Eq.trans (congrArg q.symm (Eq.trans (Eq.trans (Eq.symm (t0)) (Eq.symm (t7))) (Eq.symm (h1)))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    exact branch11 p q v hq sep (h0) (h1) (t8)
  · exact branch15 p q v hp hq sep G e₀ e₁ e₂ no (h0) (h1) (hit)
  · have t0 : v 9 = v 2 := Eq.trans (Eq.symm (hq 9)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 0))
    have t1 : v 4 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 3)))) (Eq.trans (congrArg p.symm (Eq.trans (t0) (Eq.symm (hit)))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    exact branch14 p q v hp hq sep G e₀ e₁ e₂ no (h0) (h1) (Eq.symm (t1))
  · have t0 : v 11 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 6)))) (Eq.trans (congrArg p.symm (Eq.symm (hit))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t1 : v 14 = v 0 := Eq.trans (Eq.symm (hq 5)) (Eq.trans (congrArg q (Eq.trans (Eq.symm (t0)) (Eq.symm (h0)))) (hq 2))
    have t2 : v 17 = v 0 := Eq.trans (Eq.symm (hq 7)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
    have t3 : v 14 = v 12 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 9)))) (Eq.trans (congrArg p.symm (Eq.trans (t2) (h1))) (p.symm_apply_eq.mpr (Eq.symm (hp 7))))
    exact branch9 p q v hp sep (h0) (h1) (Eq.trans (Eq.symm (t1)) (t3))
  · have t0 : v 16 = v 0 := Eq.trans (Eq.symm (hq 6)) (Eq.trans (congrArg q (Eq.symm (hit))) (hq 2))
    exact branch12 p q v hp hq sep G e₀ e₁ e₂ no (h0) (h1) (Eq.symm (t0))
  · have t0 : v 8 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 5)))) (Eq.trans (congrArg p.symm (hit)) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    exact branch10 p q v hp hq sep (h0) (h1) (Eq.symm (t0))
  · exact branch15 p q v hp hq sep G e₀ e₁ e₂ no (h0) (h1) (hit)
  · have t0 : v 5 = v 11 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.symm (hit))) (p.symm_apply_eq.mpr (Eq.symm (hp 6))))
    have t1 : v 11 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 6)))) (Eq.trans (congrArg p.symm (Eq.trans (t0) (Eq.symm (h0)))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t2 : v 14 = v 0 := Eq.trans (Eq.symm (hq 5)) (Eq.trans (congrArg q (Eq.trans (Eq.symm (t1)) (Eq.symm (h0)))) (hq 2))
    have t3 : v 17 = v 0 := Eq.trans (Eq.symm (hq 7)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
    have t4 : v 14 = v 12 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 9)))) (Eq.trans (congrArg p.symm (Eq.trans (t3) (h1))) (p.symm_apply_eq.mpr (Eq.symm (hp 7))))
    exact branch9 p q v hp sep (h0) (h1) (Eq.trans (Eq.symm (t2)) (t4))
  · have t0 : v 13 = v 11 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 8)))) (Eq.trans (congrArg p.symm (Eq.symm (hit))) (p.symm_apply_eq.mpr (Eq.symm (hp 6))))
    have t1 : v 5 = v 7 := Eq.trans (Eq.symm (hp 6)) (Eq.trans (congrArg p (Eq.symm (h0))) (hp 2))
    have t2 : v 13 = v 1 := Eq.trans (Eq.symm (hq 4)) (Eq.trans (congrArg q (Eq.symm (t1))) (hq 3))
    have t3 : v 8 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 5)))) (Eq.trans (congrArg p.symm (Eq.trans (Eq.trans (h0) (Eq.symm (t0))) (t2))) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    exact branch10 p q v hp hq sep (h0) (h1) (Eq.symm (t3))
  · exact branch16 p q v hp hq sep G e₀ e₁ e₂ no (h0) (h1) (hit)
  · have t0 : v 9 = v 2 := Eq.trans (Eq.symm (hq 9)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 0))
    have t1 : v 4 = v 11 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 3)))) (Eq.trans (congrArg p.symm (Eq.trans (t0) (Eq.symm (hit)))) (p.symm_apply_eq.mpr (Eq.symm (hp 6))))
    exact branch15 p q v hp hq sep G e₀ e₁ e₂ no (h0) (h1) (Eq.trans (h0) (Eq.symm (t1)))
  · have t0 : v 5 = v 11 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.symm (hit))) (p.symm_apply_eq.mpr (Eq.symm (hp 6))))
    have t1 : v 11 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 6)))) (Eq.trans (congrArg p.symm (Eq.trans (t0) (Eq.symm (h0)))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t2 : v 14 = v 0 := Eq.trans (Eq.symm (hq 5)) (Eq.trans (congrArg q (Eq.trans (Eq.symm (t1)) (Eq.symm (h0)))) (hq 2))
    have t3 : v 17 = v 0 := Eq.trans (Eq.symm (hq 7)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
    have t4 : v 14 = v 12 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 9)))) (Eq.trans (congrArg p.symm (Eq.trans (t3) (h1))) (p.symm_apply_eq.mpr (Eq.symm (hp 7))))
    exact branch9 p q v hp sep (h0) (h1) (Eq.trans (Eq.symm (t2)) (t4))
  · have t0 : v 11 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 6)))) (Eq.trans (congrArg p.symm (hit)) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    exact branch11 p q v hq sep (h0) (h1) (Eq.trans (Eq.symm (t0)) (Eq.symm (h0)))
  · exact branch16 p q v hp hq sep G e₀ e₁ e₂ no (h0) (h1) (hit)
  · have t0 : v 5 = v 7 := Eq.trans (Eq.symm (hp 6)) (Eq.trans (congrArg p (Eq.symm (h0))) (hp 2))
    have t1 : v 13 = v 5 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 8)))) (Eq.trans (congrArg p.symm (Eq.symm (hit))) (p.symm_apply_eq.mpr (Eq.symm (hp 4))))
    have t2 : v 13 = v 1 := Eq.trans (Eq.symm (hq 4)) (Eq.trans (congrArg q (Eq.symm (t0))) (hq 3))
    have t3 : v 3 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 2)))) (Eq.trans (congrArg p.symm (Eq.trans (Eq.trans (Eq.symm (t0)) (Eq.symm (t1))) (t2))) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    exact branch11 p q v hq sep (h0) (h1) (Eq.symm (t3))
  · exact branch17 p q v hp hq sep G e₀ e₁ e₂ no (h0) (h1) (hit)
  · have t0 : v 9 = v 2 := Eq.trans (Eq.symm (hq 9)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 0))
    have t1 : v 5 = v 4 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.trans (hit) (Eq.symm (t0)))) (p.symm_apply_eq.mpr (Eq.symm (hp 3))))
    exact branch16 p q v hp hq sep G e₀ e₁ e₂ no (h0) (h1) (t1)
  · have t0 : v 16 = v 4 := Eq.trans (Eq.symm (hq 6)) (Eq.trans (congrArg q (hit)) (hq 1))
    have t1 : v 9 = v 2 := Eq.trans (Eq.symm (hq 9)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 0))
    have t2 : v 5 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (hit)) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    have t3 : v 1 = v 2 := Eq.trans (Eq.symm (hq 3)) (Eq.trans (congrArg q (t2)) (hq 0))
    have t4 : v 4 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 3)))) (Eq.trans (congrArg p.symm (Eq.trans (t1) (Eq.symm (t3)))) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    have t5 : v 13 = v 11 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 8)))) (Eq.trans (congrArg p.symm (Eq.trans (Eq.trans (t0) (t4)) (Eq.symm (t2)))) (p.symm_apply_eq.mpr (Eq.symm (hp 6))))
    have t6 : v 5 = v 7 := Eq.trans (Eq.symm (hp 6)) (Eq.trans (congrArg p (Eq.symm (h0))) (hp 2))
    have t7 : v 13 = v 2 := Eq.trans (Eq.symm (hq 4)) (Eq.trans (congrArg q (Eq.trans (Eq.symm (t6)) (t2))) (hq 0))
    have t8 : v 8 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 5)))) (Eq.trans (congrArg p.symm (Eq.trans (Eq.trans (Eq.trans (h0) (Eq.symm (t5))) (t7)) (Eq.symm (t3)))) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    exact branch10 p q v hp hq sep (h0) (h1) (Eq.symm (t8))
  · exact branch17 p q v hp hq sep G e₀ e₁ e₂ no (h0) (h1) (hit)
  · have t0 : v 9 = v 2 := Eq.trans (Eq.symm (hq 9)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 0))
    have t1 : v 10 = v 1 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 6)))) (Eq.trans (congrArg q.symm (hit)) (q.symm_apply_eq.mpr (Eq.symm (hq 1))))
    have t2 : v 5 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (t1)) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    have t3 : v 1 = v 2 := Eq.trans (Eq.symm (hq 3)) (Eq.trans (congrArg q (t2)) (hq 0))
    have t4 : v 4 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 3)))) (Eq.trans (congrArg p.symm (Eq.trans (t0) (Eq.symm (t3)))) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    have t5 : v 13 = v 11 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 8)))) (Eq.trans (congrArg p.symm (Eq.trans (Eq.trans (hit) (t4)) (Eq.symm (t2)))) (p.symm_apply_eq.mpr (Eq.symm (hp 6))))
    have t6 : v 5 = v 7 := Eq.trans (Eq.symm (hp 6)) (Eq.trans (congrArg p (Eq.symm (h0))) (hp 2))
    have t7 : v 13 = v 1 := Eq.trans (Eq.symm (hq 4)) (Eq.trans (congrArg q (Eq.symm (t6))) (hq 3))
    have t8 : v 8 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 5)))) (Eq.trans (congrArg p.symm (Eq.trans (Eq.trans (h0) (Eq.symm (t5))) (t7))) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    exact branch10 p q v hp hq sep (h0) (h1) (Eq.symm (t8))
  · have t0 : v 9 = v 2 := Eq.trans (Eq.symm (hq 9)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 0))
    have t1 : v 13 = v 4 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 8)))) (Eq.trans (congrArg p.symm (Eq.trans (hit) (Eq.symm (t0)))) (p.symm_apply_eq.mpr (Eq.symm (hp 3))))
    have t2 : v 5 = v 7 := Eq.trans (Eq.symm (hp 6)) (Eq.trans (congrArg p (Eq.symm (h0))) (hp 2))
    have t3 : v 13 = v 1 := Eq.trans (Eq.symm (hq 4)) (Eq.trans (congrArg q (Eq.symm (t2))) (hq 3))
    have t4 : v 1 = v 5 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 1)))) (Eq.trans (congrArg q.symm (Eq.trans (Eq.symm (t1)) (t3))) (q.symm_apply_eq.mpr (Eq.symm (hq 3))))
    have t5 : v 11 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 6)))) (Eq.trans (congrArg p.symm (Eq.symm (t4))) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    exact branch11 p q v hq sep (h0) (h1) (Eq.trans (Eq.symm (t5)) (Eq.symm (h0)))
  · have t0 : v 1 = v 5 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 1)))) (Eq.trans (congrArg q.symm (Eq.symm (hit))) (q.symm_apply_eq.mpr (Eq.symm (hq 3))))
    have t1 : v 11 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 6)))) (Eq.trans (congrArg p.symm (Eq.symm (t0))) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    exact branch11 p q v hq sep (h0) (h1) (Eq.trans (Eq.symm (t1)) (Eq.symm (h0)))
  · have t0 : v 9 = v 6 := Eq.trans (Eq.symm (hp 3)) (Eq.trans (congrArg p (hit)) (hp 1))
    have t1 : v 15 = v 12 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 9)))) (Eq.trans (congrArg q.symm (t0)) (q.symm_apply_eq.mpr (Eq.symm (hq 8))))
    exact branch9 p q v hp sep (h0) (h1) (Eq.trans (h1) (t1))

include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch24 (h0 : v 3 = v 11) (h1 : v 1 = v 12) : False := by
  have t0 : v 17 = v 0 := Eq.trans (Eq.symm (hq 7)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
  have t1 : v 5 = v 7 := Eq.trans (Eq.symm (hp 6)) (Eq.trans (congrArg p (Eq.symm (h0))) (hp 2))
  have t2 : v 13 = v 1 := Eq.trans (Eq.symm (hq 4)) (Eq.trans (congrArg q (Eq.symm (t1))) (hq 3))
  have t3 : v 16 = v 15 := Eq.trans (Eq.symm (hp 8)) (Eq.trans (congrArg p (Eq.trans (t2) (h1))) (hp 7))
  have t4 : v 6 = v 4 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 1))
  rcases collision16 (fun h => no (.inr (.inr h)))
    (v 0) (v 0) (v 14) (v 14) (v 8) (v 3) (v 3) (v 5) (v 5) (v 10) (v 10) (v 15) (v 1) (v 4) (v 2) (v 2)
    (e₀ (v 0))
    ((Eq.trans (hp 9) (t0)) ▸ e₁ (v 14))
    (e₀ (v 14))
    ((hq 5) ▸ e₂ (v 8))
    ((hp 5) ▸ e₁ (v 8))
    (e₀ (v 3))
    ((Eq.trans (hp 2) (Eq.symm (t1))) ▸ e₁ (v 3))
    (e₀ (v 5))
    ((hp 4) ▸ e₁ (v 5))
    (e₀ (v 10))
    ((Eq.trans (hq 6) (t3)) ▸ e₂ (v 10))
    ((Eq.trans (congrArg p (h1)) (hp 7)) ▸ e₁ (v 1))
    ((hq 1) ▸ e₂ (v 1))
    ((Eq.trans (hp 1) (t4)) ▸ e₁ (v 2))
    (e₀ (v 2))
    ((hq 0) ▸ e₂ (v 0)) with hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit
  · have t0 : v 17 = v 1 := Eq.trans (Eq.symm (hp 9)) (Eq.trans (congrArg p (Eq.symm (hit))) (hp 0))
    have t1 : v 17 = v 0 := Eq.trans (Eq.symm (hq 7)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
    have t2 : v 4 = v 2 := Eq.trans (Eq.symm (hq 1)) (Eq.trans (congrArg q (Eq.trans (Eq.symm (t0)) (t1))) (hq 0))
    have t3 : v 9 = v 6 := Eq.trans (Eq.symm (hp 3)) (Eq.trans (congrArg p (t2)) (hp 1))
    have t4 : v 6 = v 4 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 1))
    have t5 : v 15 = v 0 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 9)))) (Eq.trans (congrArg q.symm (Eq.trans (Eq.trans (t3) (t4)) (t2))) (q.symm_apply_eq.mpr (Eq.symm (hq 0))))
    exact branch9 p q v hp sep (h0) (Eq.symm (t5)) (Eq.trans (Eq.trans (Eq.symm (t1)) (t0)) (h1))
  · have t0 : v 3 = v 1 := Eq.trans (Eq.symm (hp 5)) (Eq.trans (congrArg p (Eq.symm (hit))) (hp 0))
    have t1 : v 0 = v 4 := Eq.trans (Eq.symm (hq 2)) (Eq.trans (congrArg q (t0)) (hq 1))
    exact branch7 p q v hp hq sep G e₀ e₁ e₂ no (h0) (t1)
  · exact branch4 p q v hq sep (h0) (hit)
  · exact branch5 p q v hp hq sep (h0) (hit)
  · exact branch25 p q v hp hq sep G e₀ e₁ e₂ no (h0) (h1) (hit)
  · have t0 : v 4 = v 2 := Eq.trans (Eq.symm (hq 1)) (Eq.trans (congrArg q (Eq.symm (hit))) (hq 0))
    have t1 : v 9 = v 6 := Eq.trans (Eq.symm (hp 3)) (Eq.trans (congrArg p (t0)) (hp 1))
    have t2 : v 15 = v 12 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 9)))) (Eq.trans (congrArg q.symm (t1)) (q.symm_apply_eq.mpr (Eq.symm (hq 8))))
    exact branch9 p q v hp sep (h0) (Eq.trans (Eq.trans (hit) (h1)) (Eq.symm (t2))) (Eq.trans (hit) (h1))
  · have t0 : v 0 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 0)))) (Eq.trans (congrArg q.symm (Eq.symm (hit))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    exact branch4 p q v hq sep (h0) (t0)
  · have t0 : v 17 = v 1 := Eq.trans (Eq.symm (hp 9)) (Eq.trans (congrArg p (Eq.symm (hit))) (hp 0))
    have t1 : v 17 = v 0 := Eq.trans (Eq.symm (hq 7)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
    have t2 : v 4 = v 2 := Eq.trans (Eq.symm (hq 1)) (Eq.trans (congrArg q (Eq.trans (Eq.symm (t0)) (t1))) (hq 0))
    have t3 : v 9 = v 6 := Eq.trans (Eq.symm (hp 3)) (Eq.trans (congrArg p (t2)) (hp 1))
    have t4 : v 6 = v 4 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 1))
    have t5 : v 15 = v 0 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 9)))) (Eq.trans (congrArg q.symm (Eq.trans (Eq.trans (t3) (t4)) (t2))) (q.symm_apply_eq.mpr (Eq.symm (hq 0))))
    exact branch9 p q v hp sep (h0) (Eq.symm (t5)) (Eq.trans (Eq.trans (Eq.symm (t1)) (t0)) (h1))
  · exact branch4 p q v hq sep (h0) (hit)
  · exact branch5 p q v hp hq sep (h0) (hit)
  · exact branch25 p q v hp hq sep G e₀ e₁ e₂ no (h0) (h1) (hit)
  · have t0 : v 5 = v 7 := Eq.trans (Eq.symm (hp 6)) (Eq.trans (congrArg p (Eq.symm (h0))) (hp 2))
    have t1 : v 13 = v 1 := Eq.trans (Eq.symm (hq 4)) (Eq.trans (congrArg q (Eq.symm (t0))) (hq 3))
    have t2 : v 16 = v 15 := Eq.trans (Eq.symm (hp 8)) (Eq.trans (congrArg p (Eq.trans (t1) (h1))) (hp 7))
    exact branch12 p q v hp hq sep G e₀ e₁ e₂ no (h0) (hit) (Eq.trans (hit) (Eq.symm (t2)))
  · exact branch7 p q v hp hq sep G e₀ e₁ e₂ no (h0) (hit)
  · have t0 : v 0 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 0)))) (Eq.trans (congrArg q.symm (Eq.symm (hit))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    exact branch4 p q v hq sep (h0) (t0)
  · have t0 : v 17 = v 0 := Eq.trans (Eq.symm (hq 7)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
    have t1 : v 17 = v 3 := Eq.trans (Eq.symm (hp 9)) (Eq.trans (congrArg p (hit)) (hp 5))
    exact branch4 p q v hq sep (h0) (Eq.trans (Eq.symm (t0)) (t1))
  · have t0 : v 17 = v 0 := Eq.trans (Eq.symm (hq 7)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
    have t1 : v 17 = v 7 := Eq.trans (Eq.symm (hp 9)) (Eq.trans (congrArg p (hit)) (hp 2))
    have t2 : v 5 = v 7 := Eq.trans (Eq.symm (hp 6)) (Eq.trans (congrArg p (Eq.symm (h0))) (hp 2))
    exact branch5 p q v hp hq sep (h0) (Eq.trans (Eq.trans (Eq.symm (t0)) (t1)) (Eq.symm (t2)))
  · have t0 : v 17 = v 0 := Eq.trans (Eq.symm (hq 7)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
    have t1 : v 17 = v 10 := Eq.trans (Eq.symm (hp 9)) (Eq.trans (congrArg p (hit)) (hp 4))
    exact branch25 p q v hp hq sep G e₀ e₁ e₂ no (h0) (h1) (Eq.trans (Eq.symm (t0)) (t1))
  · exact branch26 p q v hp hq sep G e₀ e₁ e₂ no (h0) (h1) (hit)
  · have t0 : v 17 = v 0 := Eq.trans (Eq.symm (hq 7)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
    have t1 : v 17 = v 15 := Eq.trans (Eq.symm (hp 9)) (Eq.trans (congrArg p (Eq.trans (hit) (h1))) (hp 7))
    have t2 : v 8 = v 5 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 5)))) (Eq.trans (congrArg q.symm (hit)) (q.symm_apply_eq.mpr (Eq.symm (hq 3))))
    have t3 : v 3 = v 10 := Eq.trans (Eq.symm (hp 5)) (Eq.trans (congrArg p (t2)) (hp 4))
    have t4 : v 16 = v 0 := Eq.trans (Eq.symm (hq 6)) (Eq.trans (congrArg q (Eq.symm (t3))) (hq 2))
    exact branch12 p q v hp hq sep G e₀ e₁ e₂ no (h0) (Eq.trans (Eq.symm (t0)) (t1)) (Eq.symm (t4))
  · have t0 : v 17 = v 0 := Eq.trans (Eq.symm (hq 7)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
    have t1 : v 17 = v 6 := Eq.trans (Eq.symm (hp 9)) (Eq.trans (congrArg p (hit)) (hp 1))
    have t2 : v 6 = v 4 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 1))
    exact branch7 p q v hp hq sep G e₀ e₁ e₂ no (h0) (Eq.trans (Eq.trans (Eq.symm (t0)) (t1)) (t2))
  · have t0 : v 17 = v 0 := Eq.trans (Eq.symm (hq 7)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
    have t1 : v 17 = v 7 := Eq.trans (Eq.symm (hp 9)) (Eq.trans (congrArg p (hit)) (hp 2))
    have t2 : v 5 = v 7 := Eq.trans (Eq.symm (hp 6)) (Eq.trans (congrArg p (Eq.symm (h0))) (hp 2))
    exact branch5 p q v hp hq sep (h0) (Eq.trans (Eq.trans (Eq.symm (t0)) (t1)) (Eq.symm (t2)))
  · have t0 : v 17 = v 0 := Eq.trans (Eq.symm (hq 7)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
    have t1 : v 17 = v 10 := Eq.trans (Eq.symm (hp 9)) (Eq.trans (congrArg p (hit)) (hp 4))
    exact branch25 p q v hp hq sep G e₀ e₁ e₂ no (h0) (h1) (Eq.trans (Eq.symm (t0)) (t1))
  · exact branch26 p q v hp hq sep G e₀ e₁ e₂ no (h0) (h1) (hit)
  · exact branch27 p q v hp hq sep G e₀ e₁ e₂ no (h0) (h1) (hit)
  · have t0 : v 17 = v 0 := Eq.trans (Eq.symm (hq 7)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
    have t1 : v 17 = v 9 := Eq.trans (Eq.symm (hp 9)) (Eq.trans (congrArg p (hit)) (hp 3))
    exact branch19 p q v hp hq sep G e₀ e₁ e₂ no (h0) (Eq.trans (Eq.symm (t0)) (t1))
  · have t0 : v 17 = v 0 := Eq.trans (Eq.symm (hq 7)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
    have t1 : v 17 = v 6 := Eq.trans (Eq.symm (hp 9)) (Eq.trans (congrArg p (hit)) (hp 1))
    have t2 : v 6 = v 4 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 1))
    exact branch7 p q v hp hq sep G e₀ e₁ e₂ no (h0) (Eq.trans (Eq.trans (Eq.symm (t0)) (t1)) (t2))
  · have t0 : v 14 = v 0 := Eq.trans (Eq.symm (hq 5)) (Eq.trans (congrArg q (hit)) (hq 2))
    have t1 : v 17 = v 1 := Eq.trans (Eq.symm (hp 9)) (Eq.trans (congrArg p (t0)) (hp 0))
    have t2 : v 17 = v 0 := Eq.trans (Eq.symm (hq 7)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
    have t3 : v 4 = v 2 := Eq.trans (Eq.symm (hq 1)) (Eq.trans (congrArg q (Eq.trans (Eq.symm (t1)) (t2))) (hq 0))
    have t4 : v 9 = v 6 := Eq.trans (Eq.symm (hp 3)) (Eq.trans (congrArg p (t3)) (hp 1))
    have t5 : v 6 = v 4 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 1))
    have t6 : v 15 = v 0 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 9)))) (Eq.trans (congrArg q.symm (Eq.trans (Eq.trans (t4) (t5)) (t3))) (q.symm_apply_eq.mpr (Eq.symm (hq 0))))
    exact branch9 p q v hp sep (h0) (Eq.symm (t6)) (Eq.trans (Eq.trans (Eq.symm (t2)) (t1)) (h1))
  · have t0 : v 17 = v 0 := Eq.trans (Eq.symm (hq 7)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
    have t1 : v 14 = v 1 := Eq.trans (Eq.symm (hq 5)) (Eq.trans (congrArg q (hit)) (hq 3))
    have t2 : v 17 = v 15 := Eq.trans (Eq.symm (hp 9)) (Eq.trans (congrArg p (Eq.trans (t1) (h1))) (hp 7))
    have t3 : v 3 = v 10 := Eq.trans (Eq.symm (hp 5)) (Eq.trans (congrArg p (hit)) (hp 4))
    have t4 : v 16 = v 0 := Eq.trans (Eq.symm (hq 6)) (Eq.trans (congrArg q (Eq.symm (t3))) (hq 2))
    exact branch12 p q v hp hq sep G e₀ e₁ e₂ no (h0) (Eq.trans (Eq.symm (t0)) (t2)) (Eq.symm (t4))
  · have t0 : v 16 = v 14 := Eq.trans (Eq.symm (hq 6)) (Eq.trans (congrArg q (Eq.symm (hit))) (hq 5))
    have t1 : v 5 = v 7 := Eq.trans (Eq.symm (hp 6)) (Eq.trans (congrArg p (Eq.symm (h0))) (hp 2))
    have t2 : v 13 = v 1 := Eq.trans (Eq.symm (hq 4)) (Eq.trans (congrArg q (Eq.symm (t1))) (hq 3))
    have t3 : v 16 = v 15 := Eq.trans (Eq.symm (hp 8)) (Eq.trans (congrArg p (Eq.trans (t2) (h1))) (hp 7))
    exact branch27 p q v hp hq sep G e₀ e₁ e₂ no (h0) (h1) (Eq.trans (Eq.symm (t0)) (t3))
  · have t0 : v 17 = v 0 := Eq.trans (Eq.symm (hq 7)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
    have t1 : v 14 = v 4 := Eq.trans (Eq.symm (hq 5)) (Eq.trans (congrArg q (hit)) (hq 1))
    have t2 : v 17 = v 9 := Eq.trans (Eq.symm (hp 9)) (Eq.trans (congrArg p (t1)) (hp 3))
    exact branch19 p q v hp hq sep G e₀ e₁ e₂ no (h0) (Eq.trans (Eq.symm (t0)) (t2))
  · exact branch28 p q v hp hq sep G e₀ e₁ e₂ no (h0) (h1) (hit)
  · have t0 : v 1 = v 0 := Eq.trans (Eq.symm (hq 3)) (Eq.trans (congrArg q (Eq.symm (hit))) (hq 2))
    have t1 : v 15 = v 1 := Eq.trans (Eq.symm (hp 7)) (Eq.trans (congrArg p (Eq.trans (Eq.symm (h1)) (t0))) (hp 0))
    exact branch9 p q v hp sep (h0) (Eq.trans (Eq.symm (t0)) (Eq.symm (t1))) (Eq.trans (Eq.symm (t0)) (h1))
  · have t0 : v 16 = v 0 := Eq.trans (Eq.symm (hq 6)) (Eq.trans (congrArg q (Eq.symm (hit))) (hq 2))
    have t1 : v 5 = v 7 := Eq.trans (Eq.symm (hp 6)) (Eq.trans (congrArg p (Eq.symm (h0))) (hp 2))
    have t2 : v 13 = v 1 := Eq.trans (Eq.symm (hq 4)) (Eq.trans (congrArg q (Eq.symm (t1))) (hq 3))
    have t3 : v 16 = v 15 := Eq.trans (Eq.symm (hp 8)) (Eq.trans (congrArg p (Eq.trans (t2) (h1))) (hp 7))
    exact branch12 p q v hp hq sep G e₀ e₁ e₂ no (h0) (Eq.trans (Eq.symm (t0)) (t3)) (Eq.symm (t0))
  · have t0 : v 9 = v 0 := Eq.trans (Eq.symm (hq 9)) (Eq.trans (congrArg q (Eq.symm (hit))) (hq 2))
    exact branch19 p q v hp hq sep G e₀ e₁ e₂ no (h0) (Eq.symm (t0))
  · have t0 : v 6 = v 4 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 1))
    have t1 : v 2 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 1)))) (Eq.trans (congrArg p.symm (Eq.trans (t0) (Eq.symm (hit)))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    exact branch28 p q v hp hq sep G e₀ e₁ e₂ no (h0) (h1) (Eq.symm (t1))
  · exact branch29 p q v hq sep G e₀ e₁ e₂ no (h0) (h1) (hit)
  · have t0 : v 1 = v 0 := Eq.trans (Eq.symm (hq 3)) (Eq.trans (congrArg q (Eq.symm (hit))) (hq 2))
    have t1 : v 15 = v 1 := Eq.trans (Eq.symm (hp 7)) (Eq.trans (congrArg p (Eq.trans (Eq.symm (h1)) (t0))) (hp 0))
    exact branch9 p q v hp sep (h0) (Eq.trans (Eq.symm (t0)) (Eq.symm (t1))) (Eq.trans (Eq.symm (t0)) (h1))
  · have t0 : v 16 = v 0 := Eq.trans (Eq.symm (hq 6)) (Eq.trans (congrArg q (Eq.symm (hit))) (hq 2))
    have t1 : v 5 = v 7 := Eq.trans (Eq.symm (hp 6)) (Eq.trans (congrArg p (Eq.symm (h0))) (hp 2))
    have t2 : v 13 = v 1 := Eq.trans (Eq.symm (hq 4)) (Eq.trans (congrArg q (Eq.symm (t1))) (hq 3))
    have t3 : v 16 = v 15 := Eq.trans (Eq.symm (hp 8)) (Eq.trans (congrArg p (Eq.trans (t2) (h1))) (hp 7))
    exact branch12 p q v hp hq sep G e₀ e₁ e₂ no (h0) (Eq.trans (Eq.symm (t0)) (t3)) (Eq.symm (t0))
  · have t0 : v 0 = v 4 := Eq.trans (Eq.symm (hq 2)) (Eq.trans (congrArg q (hit)) (hq 1))
    exact branch7 p q v hp hq sep G e₀ e₁ e₂ no (h0) (t0)
  · exact branch29 p q v hq sep G e₀ e₁ e₂ no (h0) (h1) (hit)
  · have t0 : v 5 = v 11 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.symm (hit))) (p.symm_apply_eq.mpr (Eq.symm (hp 6))))
    have t1 : v 1 = v 0 := Eq.trans (Eq.symm (hq 3)) (Eq.trans (congrArg q (Eq.trans (t0) (Eq.symm (h0)))) (hq 2))
    have t2 : v 15 = v 1 := Eq.trans (Eq.symm (hp 7)) (Eq.trans (congrArg p (Eq.trans (Eq.symm (h1)) (t1))) (hp 0))
    exact branch9 p q v hp sep (h0) (Eq.trans (Eq.symm (t1)) (Eq.symm (t2))) (Eq.trans (Eq.symm (t1)) (h1))
  · have t0 : v 12 = v 11 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 7)))) (Eq.trans (congrArg p.symm (Eq.symm (hit))) (p.symm_apply_eq.mpr (Eq.symm (hp 6))))
    have t1 : v 0 = v 4 := Eq.trans (Eq.symm (hq 2)) (Eq.trans (congrArg q (Eq.trans (Eq.trans (h0) (Eq.symm (t0))) (Eq.symm (h1)))) (hq 1))
    exact branch7 p q v hp hq sep G e₀ e₁ e₂ no (h0) (t1)
  · have t0 : v 6 = v 4 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 1))
    have t1 : v 2 = v 11 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 1)))) (Eq.trans (congrArg p.symm (Eq.trans (t0) (Eq.symm (hit)))) (p.symm_apply_eq.mpr (Eq.symm (hp 6))))
    exact branch29 p q v hq sep G e₀ e₁ e₂ no (h0) (h1) (Eq.trans (h0) (Eq.symm (t1)))
  · exact branch30 p q v hp hq sep G e₀ e₁ e₂ no (h0) (h1) (hit)
  · have t0 : v 5 = v 11 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.symm (hit))) (p.symm_apply_eq.mpr (Eq.symm (hp 6))))
    have t1 : v 1 = v 0 := Eq.trans (Eq.symm (hq 3)) (Eq.trans (congrArg q (Eq.trans (t0) (Eq.symm (h0)))) (hq 2))
    have t2 : v 15 = v 1 := Eq.trans (Eq.symm (hp 7)) (Eq.trans (congrArg p (Eq.trans (Eq.symm (h1)) (t1))) (hp 0))
    exact branch9 p q v hp sep (h0) (Eq.trans (Eq.symm (t1)) (Eq.symm (t2))) (Eq.trans (Eq.symm (t1)) (h1))
  · have t0 : v 11 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 6)))) (Eq.trans (congrArg p.symm (hit)) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    exact branch4 p q v hq sep (h0) (Eq.trans (Eq.symm (t0)) (Eq.symm (h0)))
  · exact branch30 p q v hp hq sep G e₀ e₁ e₂ no (h0) (h1) (hit)
  · have t0 : v 12 = v 5 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 7)))) (Eq.trans (congrArg p.symm (Eq.symm (hit))) (p.symm_apply_eq.mpr (Eq.symm (hp 4))))
    have t1 : v 11 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 6)))) (Eq.trans (congrArg p.symm (Eq.trans (Eq.symm (t0)) (Eq.symm (h1)))) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    exact branch4 p q v hq sep (h0) (Eq.trans (Eq.symm (t1)) (Eq.symm (h0)))
  · have t0 : v 6 = v 4 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 1))
    have t1 : v 5 = v 2 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.trans (hit) (Eq.symm (t0)))) (p.symm_apply_eq.mpr (Eq.symm (hp 1))))
    exact branch30 p q v hp hq sep G e₀ e₁ e₂ no (h0) (h1) (t1)
  · exact branch31 p q v hp hq sep G e₀ e₁ e₂ no (h0) (h1) (hit)
  · have t0 : v 5 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (hit)) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    exact branch5 p q v hp hq sep (h0) (Eq.symm (t0))
  · exact branch31 p q v hp hq sep G e₀ e₁ e₂ no (h0) (h1) (hit)
  · have t0 : v 6 = v 4 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 1))
    have t1 : v 12 = v 2 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 7)))) (Eq.trans (congrArg p.symm (Eq.trans (hit) (Eq.symm (t0)))) (p.symm_apply_eq.mpr (Eq.symm (hp 1))))
    have t2 : v 0 = v 5 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 0)))) (Eq.trans (congrArg q.symm (Eq.trans (Eq.symm (t1)) (Eq.symm (h1)))) (q.symm_apply_eq.mpr (Eq.symm (hq 3))))
    exact branch5 p q v hp hq sep (h0) (t2)
  · have t0 : v 5 = v 7 := Eq.trans (Eq.symm (hp 6)) (Eq.trans (congrArg p (Eq.symm (h0))) (hp 2))
    have t1 : v 13 = v 1 := Eq.trans (Eq.symm (hq 4)) (Eq.trans (congrArg q (Eq.symm (t0))) (hq 3))
    have t2 : v 16 = v 15 := Eq.trans (Eq.symm (hp 8)) (Eq.trans (congrArg p (Eq.trans (t1) (h1))) (hp 7))
    have t3 : v 10 = v 0 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 6)))) (Eq.trans (congrArg q.symm (Eq.trans (t2) (hit))) (q.symm_apply_eq.mpr (Eq.symm (hq 0))))
    exact branch25 p q v hp hq sep G e₀ e₁ e₂ no (h0) (h1) (Eq.symm (t3))
  · have t0 : v 0 = v 5 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 0)))) (Eq.trans (congrArg q.symm (Eq.symm (hit))) (q.symm_apply_eq.mpr (Eq.symm (hq 3))))
    exact branch5 p q v hp hq sep (h0) (t0)
  · have t0 : v 1 = v 0 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 1)))) (Eq.trans (congrArg q.symm (hit)) (q.symm_apply_eq.mpr (Eq.symm (hq 0))))
    have t1 : v 9 = v 6 := Eq.trans (Eq.symm (hp 3)) (Eq.trans (congrArg p (hit)) (hp 1))
    have t2 : v 15 = v 12 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 9)))) (Eq.trans (congrArg q.symm (t1)) (q.symm_apply_eq.mpr (Eq.symm (hq 8))))
    exact branch9 p q v hp sep (h0) (Eq.trans (Eq.trans (Eq.symm (t0)) (h1)) (Eq.symm (t2))) (Eq.trans (Eq.symm (t0)) (h1))

include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch40 (h0 : v 3 = v 10) (h1 : v 0 = v 15) : False := by
  have t0 : v 16 = v 0 := Eq.trans (Eq.symm (hq 6)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
  have t1 : v 13 = v 12 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 8)))) (Eq.trans (congrArg p.symm (Eq.trans (t0) (h1))) (p.symm_apply_eq.mpr (Eq.symm (hp 7))))
  have t2 : v 5 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.symm (h0))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
  have t3 : v 14 = v 1 := Eq.trans (Eq.symm (hq 5)) (Eq.trans (congrArg q (Eq.symm (t2))) (hq 3))
  have t4 : v 9 = v 2 := Eq.trans (Eq.symm (hq 9)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 0))
  rcases collision16 (fun h => no (.inr (.inr h)))
    (v 0) (v 0) (v 12) (v 12) (v 7) (v 7) (v 3) (v 3) (v 5) (v 5) (v 11) (v 17) (v 1) (v 4) (v 4) (v 2)
    (e₀ (v 0))
    ((Eq.trans (hp 7) (Eq.symm (h1))) ▸ e₁ (v 12))
    (e₀ (v 12))
    ((Eq.trans (hq 4) (t1)) ▸ e₂ (v 7))
    (e₀ (v 7))
    ((hp 2) ▸ e₁ (v 3))
    (e₀ (v 3))
    ((Eq.trans (hp 4) (Eq.symm (h0))) ▸ e₁ (v 5))
    (e₀ (v 5))
    ((hp 6) ▸ e₁ (v 11))
    ((hq 7) ▸ e₂ (v 11))
    ((Eq.trans (congrArg p (Eq.symm (t3))) (hp 9)) ▸ e₁ (v 1))
    ((hq 1) ▸ e₂ (v 1))
    (e₀ (v 4))
    ((Eq.trans (hp 3) (t4)) ▸ e₁ (v 4))
    ((hq 0) ▸ e₂ (v 0)) with hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit
  · have t0 : v 15 = v 1 := Eq.trans (Eq.symm (hp 7)) (Eq.trans (congrArg p (Eq.symm (hit))) (hp 0))
    have t1 : v 5 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 3)))) (Eq.trans (congrArg q.symm (Eq.trans (Eq.symm (t0)) (Eq.symm (h1)))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    have t2 : v 5 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.symm (h0))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t3 : v 11 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 6)))) (Eq.trans (congrArg p.symm (t1)) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    exact branch9 p q v hp sep (Eq.trans (Eq.trans (Eq.symm (t1)) (t2)) (Eq.symm (t3))) (h1) (hit)
  · exact branch41 p q v hp hq sep (h0) (h1) (hit)
  · exact branch38 p q v hq sep (h0) (hit)
  · exact branch39 p q v hp hq sep (h0) (hit)
  · exact branch42 p q v hp hq sep (h0) (h1) (hit)
  · have t0 : v 5 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 3)))) (Eq.trans (congrArg q.symm (Eq.symm (hit))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    have t1 : v 10 = v 7 := Eq.trans (Eq.symm (hp 4)) (Eq.trans (congrArg p (t0)) (hp 2))
    have t2 : v 3 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 2)))) (Eq.trans (congrArg p.symm (Eq.trans (Eq.symm (t1)) (Eq.symm (h0)))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t3 : v 11 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 6)))) (Eq.trans (congrArg p.symm (t0)) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t4 : v 4 = v 2 := Eq.trans (Eq.symm (hq 1)) (Eq.trans (congrArg q (Eq.symm (hit))) (hq 0))
    have t5 : v 9 = v 6 := Eq.trans (Eq.symm (hp 3)) (Eq.trans (congrArg p (t4)) (hp 1))
    have t6 : v 15 = v 12 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 9)))) (Eq.trans (congrArg q.symm (t5)) (q.symm_apply_eq.mpr (Eq.symm (hq 8))))
    exact branch9 p q v hp sep (Eq.trans (t2) (Eq.symm (t3))) (h1) (Eq.trans (h1) (t6))
  · have t0 : v 9 = v 1 := Eq.trans (Eq.symm (hp 3)) (Eq.trans (congrArg p (Eq.symm (hit))) (hp 0))
    have t1 : v 15 = v 5 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 9)))) (Eq.trans (congrArg q.symm (t0)) (q.symm_apply_eq.mpr (Eq.symm (hq 3))))
    exact branch39 p q v hp hq sep (h0) (Eq.trans (h1) (t1))
  · have t0 : v 15 = v 1 := Eq.trans (Eq.symm (hp 7)) (Eq.trans (congrArg p (Eq.symm (hit))) (hp 0))
    have t1 : v 5 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 3)))) (Eq.trans (congrArg q.symm (Eq.trans (Eq.symm (t0)) (Eq.symm (h1)))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    have t2 : v 5 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.symm (h0))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t3 : v 11 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 6)))) (Eq.trans (congrArg p.symm (t1)) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    exact branch9 p q v hp sep (Eq.trans (Eq.trans (Eq.symm (t1)) (t2)) (Eq.symm (t3))) (h1) (hit)
  · exact branch41 p q v hp hq sep (h0) (h1) (hit)
  · exact branch38 p q v hq sep (h0) (hit)
  · exact branch39 p q v hp hq sep (h0) (hit)
  · have t0 : v 11 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 7)))) (Eq.trans (congrArg q.symm (Eq.symm (hit))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    have t1 : v 16 = v 0 := Eq.trans (Eq.symm (hq 6)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
    exact branch12 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm (t0)) (h1) (Eq.symm (t1))
  · have t0 : v 9 = v 1 := Eq.trans (Eq.symm (hp 3)) (Eq.trans (congrArg p (Eq.symm (hit))) (hp 0))
    have t1 : v 15 = v 5 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 9)))) (Eq.trans (congrArg q.symm (t0)) (q.symm_apply_eq.mpr (Eq.symm (hq 3))))
    exact branch39 p q v hp hq sep (h0) (Eq.trans (h1) (t1))
  · have t0 : v 0 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 0)))) (Eq.trans (congrArg q.symm (Eq.symm (hit))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    exact branch38 p q v hq sep (h0) (t0)
  · exact branch43 p q v hp hq sep (h0) (h1) (hit)
  · have t0 : v 15 = v 7 := Eq.trans (Eq.symm (hp 7)) (Eq.trans (congrArg p (hit)) (hp 2))
    exact branch41 p q v hp hq sep (h0) (h1) (Eq.trans (h1) (t0))
  · have t0 : v 15 = v 10 := Eq.trans (Eq.symm (hp 7)) (Eq.trans (congrArg p (hit)) (hp 4))
    exact branch38 p q v hq sep (h0) (Eq.trans (Eq.trans (h1) (t0)) (Eq.symm (h0)))
  · have t0 : v 15 = v 5 := Eq.trans (Eq.symm (hp 7)) (Eq.trans (congrArg p (hit)) (hp 6))
    exact branch39 p q v hp hq sep (h0) (Eq.trans (h1) (t0))
  · have t0 : v 5 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.symm (h0))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t1 : v 14 = v 1 := Eq.trans (Eq.symm (hq 5)) (Eq.trans (congrArg q (Eq.symm (t0))) (hq 3))
    have t2 : v 17 = v 15 := Eq.trans (Eq.symm (hp 9)) (Eq.trans (congrArg p (Eq.trans (t1) (Eq.symm (hit)))) (hp 7))
    have t3 : v 11 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 7)))) (Eq.trans (congrArg q.symm (Eq.trans (t2) (Eq.symm (h1)))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    have t4 : v 16 = v 0 := Eq.trans (Eq.symm (hq 6)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
    exact branch12 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm (t3)) (h1) (Eq.symm (t4))
  · have t0 : v 9 = v 2 := Eq.trans (Eq.symm (hq 9)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 0))
    have t1 : v 15 = v 9 := Eq.trans (Eq.symm (hp 7)) (Eq.trans (congrArg p (hit)) (hp 3))
    have t2 : v 0 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 0)))) (Eq.trans (congrArg q.symm (Eq.trans (Eq.trans (Eq.symm (t0)) (Eq.symm (t1))) (Eq.symm (h1)))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    exact branch38 p q v hq sep (h0) (t2)
  · exact branch43 p q v hp hq sep (h0) (h1) (hit)
  · have t0 : v 15 = v 7 := Eq.trans (Eq.symm (hp 7)) (Eq.trans (congrArg p (hit)) (hp 2))
    exact branch41 p q v hp hq sep (h0) (h1) (Eq.trans (h1) (t0))
  · have t0 : v 15 = v 10 := Eq.trans (Eq.symm (hp 7)) (Eq.trans (congrArg p (hit)) (hp 4))
    exact branch38 p q v hq sep (h0) (Eq.trans (Eq.trans (h1) (t0)) (Eq.symm (h0)))
  · exact branch44 p q v hp hq sep G e₀ e₁ e₂ no (h0) (h1) (hit)
  · have t0 : v 9 = v 2 := Eq.trans (Eq.symm (hq 9)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 0))
    have t1 : v 15 = v 9 := Eq.trans (Eq.symm (hp 7)) (Eq.trans (congrArg p (hit)) (hp 3))
    have t2 : v 0 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 0)))) (Eq.trans (congrArg q.symm (Eq.trans (Eq.trans (Eq.symm (t0)) (Eq.symm (t1))) (Eq.symm (h1)))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    exact branch38 p q v hq sep (h0) (t2)
  · have t0 : v 16 = v 0 := Eq.trans (Eq.symm (hq 6)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
    have t1 : v 13 = v 12 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 8)))) (Eq.trans (congrArg p.symm (Eq.trans (t0) (h1))) (p.symm_apply_eq.mpr (Eq.symm (hp 7))))
    have t2 : v 7 = v 0 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 4)))) (Eq.trans (congrArg q.symm (Eq.trans (t1) (hit))) (q.symm_apply_eq.mpr (Eq.symm (hq 0))))
    exact branch41 p q v hp hq sep (h0) (h1) (Eq.symm (t2))
  · have t0 : v 3 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 2)))) (Eq.trans (congrArg p.symm (hit)) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t1 : v 14 = v 0 := Eq.trans (Eq.symm (hq 5)) (Eq.trans (congrArg q (Eq.symm (t0))) (hq 2))
    have t2 : v 17 = v 1 := Eq.trans (Eq.symm (hp 9)) (Eq.trans (congrArg p (t1)) (hp 0))
    have t3 : v 13 = v 0 := Eq.trans (Eq.symm (hq 4)) (Eq.trans (congrArg q (hit)) (hq 2))
    have t4 : v 16 = v 1 := Eq.trans (Eq.symm (hp 8)) (Eq.trans (congrArg p (t3)) (hp 0))
    have t5 : v 16 = v 0 := Eq.trans (Eq.symm (hq 6)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
    have t6 : v 11 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 7)))) (Eq.trans (congrArg q.symm (Eq.trans (Eq.trans (t2) (Eq.symm (t4))) (t5))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    have t7 : v 13 = v 12 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 8)))) (Eq.trans (congrArg p.symm (Eq.trans (t5) (h1))) (p.symm_apply_eq.mpr (Eq.symm (hp 7))))
    exact branch9 p q v hp sep (Eq.symm (t6)) (h1) (Eq.trans (Eq.symm (t3)) (t7))
  · have t0 : v 3 = v 11 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 2)))) (Eq.trans (congrArg p.symm (hit)) (p.symm_apply_eq.mpr (Eq.symm (hp 6))))
    have t1 : v 16 = v 0 := Eq.trans (Eq.symm (hq 6)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
    exact branch12 p q v hp hq sep G e₀ e₁ e₂ no (t0) (h1) (Eq.symm (t1))
  · have t0 : v 16 = v 0 := Eq.trans (Eq.symm (hq 6)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
    have t1 : v 13 = v 12 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 8)))) (Eq.trans (congrArg p.symm (Eq.trans (t0) (h1))) (p.symm_apply_eq.mpr (Eq.symm (hp 7))))
    have t2 : v 17 = v 13 := Eq.trans (Eq.symm (hq 7)) (Eq.trans (congrArg q (Eq.symm (hit))) (hq 4))
    exact branch44 p q v hp hq sep G e₀ e₁ e₂ no (h0) (h1) (Eq.trans (Eq.symm (t1)) (Eq.symm (t2)))
  · have t0 : v 3 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 2)))) (Eq.trans (congrArg p.symm (hit)) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    exact branch38 p q v hq sep (h0) (Eq.symm (t0))
  · exact branch45 p q v hp hq sep G e₀ e₁ e₂ no (h0) (h1) (hit)
  · have t0 : v 3 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 2)))) (Eq.trans (congrArg p.symm (hit)) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t1 : v 14 = v 0 := Eq.trans (Eq.symm (hq 5)) (Eq.trans (congrArg q (Eq.symm (t0))) (hq 2))
    have t2 : v 17 = v 1 := Eq.trans (Eq.symm (hp 9)) (Eq.trans (congrArg p (t1)) (hp 0))
    have t3 : v 13 = v 0 := Eq.trans (Eq.symm (hq 4)) (Eq.trans (congrArg q (hit)) (hq 2))
    have t4 : v 16 = v 1 := Eq.trans (Eq.symm (hp 8)) (Eq.trans (congrArg p (t3)) (hp 0))
    have t5 : v 16 = v 0 := Eq.trans (Eq.symm (hq 6)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
    have t6 : v 11 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 7)))) (Eq.trans (congrArg q.symm (Eq.trans (Eq.trans (t2) (Eq.symm (t4))) (t5))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    have t7 : v 13 = v 12 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 8)))) (Eq.trans (congrArg p.symm (Eq.trans (t5) (h1))) (p.symm_apply_eq.mpr (Eq.symm (hp 7))))
    exact branch9 p q v hp sep (Eq.symm (t6)) (h1) (Eq.trans (Eq.symm (t3)) (t7))
  · have t0 : v 3 = v 11 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 2)))) (Eq.trans (congrArg p.symm (hit)) (p.symm_apply_eq.mpr (Eq.symm (hp 6))))
    have t1 : v 16 = v 0 := Eq.trans (Eq.symm (hq 6)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
    exact branch12 p q v hp hq sep G e₀ e₁ e₂ no (t0) (h1) (Eq.symm (t1))
  · have t0 : v 14 = v 3 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 9)))) (Eq.trans (congrArg p.symm (Eq.symm (hit))) (p.symm_apply_eq.mpr (Eq.symm (hp 2))))
    have t1 : v 5 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.symm (h0))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t2 : v 14 = v 1 := Eq.trans (Eq.symm (hq 5)) (Eq.trans (congrArg q (Eq.symm (t1))) (hq 3))
    have t3 : v 5 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.trans (Eq.trans (Eq.symm (h0)) (Eq.symm (t0))) (t2))) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    exact branch39 p q v hp hq sep (h0) (Eq.symm (t3))
  · exact branch45 p q v hp hq sep G e₀ e₁ e₂ no (h0) (h1) (hit)
  · exact branch46 p q v hp hq sep G e₀ e₁ e₂ no (h0) (h1) (hit)
  · have t0 : v 10 = v 7 := Eq.trans (Eq.symm (hp 4)) (Eq.trans (congrArg p (Eq.symm (hit))) (hp 2))
    have t1 : v 3 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 2)))) (Eq.trans (congrArg p.symm (Eq.trans (Eq.symm (t0)) (Eq.symm (h0)))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t2 : v 11 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 6)))) (Eq.trans (congrArg p.symm (Eq.symm (hit))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t3 : v 13 = v 0 := Eq.trans (Eq.symm (hq 4)) (Eq.trans (congrArg q (Eq.trans (Eq.symm (t0)) (Eq.symm (h0)))) (hq 2))
    have t4 : v 16 = v 0 := Eq.trans (Eq.symm (hq 6)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
    have t5 : v 13 = v 12 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 8)))) (Eq.trans (congrArg p.symm (Eq.trans (t4) (h1))) (p.symm_apply_eq.mpr (Eq.symm (hp 7))))
    exact branch9 p q v hp sep (Eq.trans (t1) (Eq.symm (t2))) (h1) (Eq.trans (Eq.symm (t3)) (t5))
  · have t0 : v 16 = v 0 := Eq.trans (Eq.symm (hq 6)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
    exact branch12 p q v hp hq sep G e₀ e₁ e₂ no (hit) (h1) (Eq.symm (t0))
  · have t0 : v 0 = v 4 := Eq.trans (Eq.symm (hq 2)) (Eq.trans (congrArg q (hit)) (hq 1))
    have t1 : v 9 = v 1 := Eq.trans (Eq.symm (hp 3)) (Eq.trans (congrArg p (Eq.symm (t0))) (hp 0))
    have t2 : v 15 = v 5 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 9)))) (Eq.trans (congrArg q.symm (t1)) (q.symm_apply_eq.mpr (Eq.symm (hq 3))))
    exact branch39 p q v hp hq sep (h0) (Eq.trans (h1) (t2))
  · have t0 : v 9 = v 7 := Eq.trans (Eq.symm (hp 3)) (Eq.trans (congrArg p (Eq.symm (hit))) (hp 2))
    have t1 : v 9 = v 2 := Eq.trans (Eq.symm (hq 9)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 0))
    exact branch46 p q v hp hq sep G e₀ e₁ e₂ no (h0) (h1) (Eq.trans (Eq.symm (t0)) (t1))
  · have t0 : v 10 = v 7 := Eq.trans (Eq.symm (hp 4)) (Eq.trans (congrArg p (Eq.symm (hit))) (hp 2))
    have t1 : v 3 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 2)))) (Eq.trans (congrArg p.symm (Eq.trans (Eq.symm (t0)) (Eq.symm (h0)))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t2 : v 11 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 6)))) (Eq.trans (congrArg p.symm (Eq.symm (hit))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t3 : v 13 = v 0 := Eq.trans (Eq.symm (hq 4)) (Eq.trans (congrArg q (Eq.trans (Eq.symm (t0)) (Eq.symm (h0)))) (hq 2))
    have t4 : v 16 = v 0 := Eq.trans (Eq.symm (hq 6)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
    have t5 : v 13 = v 12 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 8)))) (Eq.trans (congrArg p.symm (Eq.trans (t4) (h1))) (p.symm_apply_eq.mpr (Eq.symm (hp 7))))
    exact branch9 p q v hp sep (Eq.trans (t1) (Eq.symm (t2))) (h1) (Eq.trans (Eq.symm (t3)) (t5))
  · have t0 : v 5 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.symm (h0))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t1 : v 14 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 9)))) (Eq.trans (congrArg p.symm (Eq.symm (hit))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t2 : v 14 = v 1 := Eq.trans (Eq.symm (hq 5)) (Eq.trans (congrArg q (Eq.symm (t0))) (hq 3))
    have t3 : v 11 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 6)))) (Eq.trans (congrArg p.symm (Eq.trans (Eq.trans (t0) (Eq.symm (t1))) (t2))) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    exact branch42 p q v hp hq sep (h0) (h1) (Eq.symm (t3))
  · have t0 : v 9 = v 7 := Eq.trans (Eq.symm (hp 3)) (Eq.trans (congrArg p (Eq.symm (hit))) (hp 2))
    have t1 : v 9 = v 2 := Eq.trans (Eq.symm (hq 9)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 0))
    exact branch46 p q v hp hq sep G e₀ e₁ e₂ no (h0) (h1) (Eq.trans (Eq.symm (t0)) (t1))
  · exact branch47 p q v hq sep G e₀ e₁ e₂ no (h0) (h1) (hit)
  · have t0 : v 5 = v 10 := Eq.trans (Eq.symm (hp 6)) (Eq.trans (congrArg p (Eq.symm (hit))) (hp 4))
    have t1 : v 10 = v 7 := Eq.trans (Eq.symm (hp 4)) (Eq.trans (congrArg p (Eq.trans (t0) (Eq.symm (h0)))) (hp 2))
    have t2 : v 13 = v 0 := Eq.trans (Eq.symm (hq 4)) (Eq.trans (congrArg q (Eq.trans (Eq.symm (t1)) (Eq.symm (h0)))) (hq 2))
    have t3 : v 16 = v 0 := Eq.trans (Eq.symm (hq 6)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
    have t4 : v 13 = v 12 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 8)))) (Eq.trans (congrArg p.symm (Eq.trans (t3) (h1))) (p.symm_apply_eq.mpr (Eq.symm (hp 7))))
    exact branch9 p q v hp sep (Eq.trans (Eq.trans (h0) (Eq.symm (t0))) (hit)) (h1) (Eq.trans (Eq.symm (t2)) (t4))
  · have t0 : v 11 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 6)))) (Eq.trans (congrArg p.symm (hit)) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    exact branch42 p q v hp hq sep (h0) (h1) (Eq.symm (t0))
  · have t0 : v 10 = v 9 := Eq.trans (Eq.symm (hp 4)) (Eq.trans (congrArg p (hit)) (hp 3))
    have t1 : v 9 = v 2 := Eq.trans (Eq.symm (hq 9)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 0))
    exact branch47 p q v hq sep G e₀ e₁ e₂ no (h0) (h1) (Eq.trans (Eq.trans (h0) (t0)) (t1))
  · exact branch48 p q v hp hq sep (h0) (h1) (hit)
  · have t0 : v 10 = v 9 := Eq.trans (Eq.symm (hp 4)) (Eq.trans (congrArg p (hit)) (hp 3))
    have t1 : v 9 = v 2 := Eq.trans (Eq.symm (hq 9)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 0))
    exact branch47 p q v hq sep G e₀ e₁ e₂ no (h0) (h1) (Eq.trans (Eq.trans (h0) (t0)) (t1))
  · exact branch49 p q v hp hq sep G e₀ e₁ e₂ no (h0) (h1) (hit)
  · have t0 : v 5 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.symm (h0))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t1 : v 14 = v 1 := Eq.trans (Eq.symm (hq 5)) (Eq.trans (congrArg q (Eq.symm (t0))) (hq 3))
    have t2 : v 17 = v 5 := Eq.trans (Eq.symm (hp 9)) (Eq.trans (congrArg p (Eq.trans (t1) (Eq.symm (hit)))) (hp 6))
    exact branch48 p q v hp hq sep (h0) (h1) (Eq.symm (t2))
  · have t0 : v 5 = v 9 := Eq.trans (Eq.symm (hp 6)) (Eq.trans (congrArg p (hit)) (hp 3))
    have t1 : v 9 = v 2 := Eq.trans (Eq.symm (hq 9)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 0))
    exact branch49 p q v hp hq sep G e₀ e₁ e₂ no (h0) (h1) (Eq.trans (t0) (t1))
  · have t0 : v 5 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.symm (h0))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t1 : v 14 = v 1 := Eq.trans (Eq.symm (hq 5)) (Eq.trans (congrArg q (Eq.symm (t0))) (hq 3))
    have t2 : v 11 = v 1 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 7)))) (Eq.trans (congrArg q.symm (hit)) (q.symm_apply_eq.mpr (Eq.symm (hq 1))))
    have t3 : v 17 = v 5 := Eq.trans (Eq.symm (hp 9)) (Eq.trans (congrArg p (Eq.trans (t1) (Eq.symm (t2)))) (hp 6))
    exact branch48 p q v hp hq sep (h0) (h1) (Eq.symm (t3))
  · have t0 : v 11 = v 0 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 7)))) (Eq.trans (congrArg q.symm (hit)) (q.symm_apply_eq.mpr (Eq.symm (hq 0))))
    exact branch42 p q v hp hq sep (h0) (h1) (Eq.symm (t0))
  · have t0 : v 1 = v 5 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 1)))) (Eq.trans (congrArg q.symm (Eq.symm (hit))) (q.symm_apply_eq.mpr (Eq.symm (hq 3))))
    have t1 : v 11 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 6)))) (Eq.trans (congrArg p.symm (Eq.symm (t0))) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    exact branch42 p q v hp hq sep (h0) (h1) (Eq.symm (t1))
  · have t0 : v 1 = v 0 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 1)))) (Eq.trans (congrArg q.symm (hit)) (q.symm_apply_eq.mpr (Eq.symm (hq 0))))
    have t1 : v 5 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 3)))) (Eq.trans (congrArg q.symm (t0)) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    have t2 : v 5 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.symm (h0))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t3 : v 11 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 6)))) (Eq.trans (congrArg p.symm (t1)) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t4 : v 9 = v 6 := Eq.trans (Eq.symm (hp 3)) (Eq.trans (congrArg p (hit)) (hp 1))
    have t5 : v 15 = v 12 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 9)))) (Eq.trans (congrArg q.symm (t4)) (q.symm_apply_eq.mpr (Eq.symm (hq 8))))
    exact branch9 p q v hp sep (Eq.trans (Eq.trans (Eq.symm (t1)) (t2)) (Eq.symm (t3))) (h1) (Eq.trans (h1) (t5))

include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch55 (h0 : v 3 = v 10) (h1 : v 1 = v 12) : False := by
  have t0 : v 16 = v 0 := Eq.trans (Eq.symm (hq 6)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
  have t1 : v 5 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.symm (h0))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
  have t2 : v 14 = v 1 := Eq.trans (Eq.symm (hq 5)) (Eq.trans (congrArg q (Eq.symm (t1))) (hq 3))
  have t3 : v 17 = v 15 := Eq.trans (Eq.symm (hp 9)) (Eq.trans (congrArg p (Eq.trans (t2) (h1))) (hp 7))
  have t4 : v 6 = v 4 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 1))
  rcases collision16 (fun h => no (.inr (.inr h)))
    (v 0) (v 0) (v 13) (v 13) (v 7) (v 7) (v 3) (v 3) (v 5) (v 5) (v 11) (v 15) (v 1) (v 4) (v 2) (v 2)
    (e₀ (v 0))
    ((Eq.trans (hp 8) (t0)) ▸ e₁ (v 13))
    (e₀ (v 13))
    ((hq 4) ▸ e₂ (v 7))
    (e₀ (v 7))
    ((hp 2) ▸ e₁ (v 3))
    (e₀ (v 3))
    ((Eq.trans (hp 4) (Eq.symm (h0))) ▸ e₁ (v 5))
    (e₀ (v 5))
    ((hp 6) ▸ e₁ (v 11))
    ((Eq.trans (hq 7) (t3)) ▸ e₂ (v 11))
    ((Eq.trans (congrArg p (h1)) (hp 7)) ▸ e₁ (v 1))
    ((hq 1) ▸ e₂ (v 1))
    ((Eq.trans (hp 1) (t4)) ▸ e₁ (v 2))
    (e₀ (v 2))
    ((hq 0) ▸ e₂ (v 0)) with hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit
  · have t0 : v 16 = v 1 := Eq.trans (Eq.symm (hp 8)) (Eq.trans (congrArg p (Eq.symm (hit))) (hp 0))
    have t1 : v 16 = v 0 := Eq.trans (Eq.symm (hq 6)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
    have t2 : v 5 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 3)))) (Eq.trans (congrArg q.symm (Eq.trans (Eq.symm (t0)) (t1))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    have t3 : v 5 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.symm (h0))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t4 : v 11 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 6)))) (Eq.trans (congrArg p.symm (t2)) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t5 : v 4 = v 2 := Eq.trans (Eq.symm (hq 1)) (Eq.trans (congrArg q (Eq.trans (Eq.symm (t0)) (t1))) (hq 0))
    have t6 : v 9 = v 6 := Eq.trans (Eq.symm (hp 3)) (Eq.trans (congrArg p (t5)) (hp 1))
    have t7 : v 6 = v 4 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 1))
    have t8 : v 15 = v 0 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 9)))) (Eq.trans (congrArg q.symm (Eq.trans (Eq.trans (t6) (t7)) (t5))) (q.symm_apply_eq.mpr (Eq.symm (hq 0))))
    exact branch9 p q v hp sep (Eq.trans (Eq.trans (Eq.symm (t2)) (t3)) (Eq.symm (t4))) (Eq.symm (t8)) (Eq.trans (Eq.trans (Eq.symm (t1)) (t0)) (h1))
  · have t0 : v 5 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.symm (h0))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t1 : v 14 = v 1 := Eq.trans (Eq.symm (hq 5)) (Eq.trans (congrArg q (Eq.symm (t0))) (hq 3))
    have t2 : v 17 = v 15 := Eq.trans (Eq.symm (hp 9)) (Eq.trans (congrArg p (Eq.trans (t1) (h1))) (hp 7))
    have t3 : v 6 = v 4 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 1))
    have t4 : v 13 = v 2 := Eq.trans (Eq.symm (hq 4)) (Eq.trans (congrArg q (Eq.symm (hit))) (hq 0))
    have t5 : v 16 = v 6 := Eq.trans (Eq.symm (hp 8)) (Eq.trans (congrArg p (t4)) (hp 1))
    have t6 : v 16 = v 0 := Eq.trans (Eq.symm (hq 6)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
    have t7 : v 9 = v 1 := Eq.trans (Eq.symm (hp 3)) (Eq.trans (congrArg p (Eq.trans (Eq.trans (Eq.symm (t3)) (Eq.symm (t5))) (t6))) (hp 0))
    have t8 : v 15 = v 5 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 9)))) (Eq.trans (congrArg q.symm (t7)) (q.symm_apply_eq.mpr (Eq.symm (hq 3))))
    have t9 : v 1 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 1)))) (Eq.trans (congrArg q.symm (Eq.trans (Eq.trans (Eq.symm (t3)) (Eq.symm (t5))) (t6))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    have t10 : v 5 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.trans (Eq.symm (h0)) (Eq.symm (t9)))) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    have t11 : v 11 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 7)))) (Eq.trans (congrArg q.symm (Eq.trans (Eq.trans (t2) (t8)) (t10))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    exact branch10 p q v hp hq sep (Eq.symm (t11)) (Eq.trans (Eq.symm (t10)) (Eq.symm (t8))) (Eq.trans (Eq.symm (t10)) (t0))
  · have t0 : v 5 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.symm (h0))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t1 : v 16 = v 2 := Eq.trans (Eq.symm (hq 6)) (Eq.trans (congrArg q (Eq.trans (Eq.symm (h0)) (Eq.symm (hit)))) (hq 0))
    have t2 : v 0 = v 2 := Eq.trans (Eq.symm (hq 2)) (Eq.trans (congrArg q (Eq.symm (hit))) (hq 0))
    have t3 : v 13 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 8)))) (Eq.trans (congrArg p.symm (Eq.trans (Eq.trans (t1) (Eq.symm (t2))) (hit))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t4 : v 7 = v 1 := Eq.trans (Eq.symm (hp 2)) (Eq.trans (congrArg p (Eq.symm (hit))) (hp 0))
    have t5 : v 13 = v 4 := Eq.trans (Eq.symm (hq 4)) (Eq.trans (congrArg q (t4)) (hq 1))
    have t6 : v 6 = v 4 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 1))
    have t7 : v 6 = v 1 := Eq.trans (Eq.symm (hp 1)) (Eq.trans (congrArg p (Eq.symm (t2))) (hp 0))
    have t8 : v 11 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 6)))) (Eq.trans (congrArg p.symm (Eq.trans (Eq.trans (Eq.trans (Eq.trans (t0) (Eq.symm (t3))) (t5)) (Eq.symm (t6))) (t7))) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    have t9 : v 16 = v 9 := Eq.trans (Eq.symm (hp 8)) (Eq.trans (congrArg p (t5)) (hp 3))
    have t10 : v 15 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 9)))) (Eq.trans (congrArg q.symm (Eq.trans (Eq.trans (Eq.symm (t9)) (t1)) (Eq.symm (t2)))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    exact branch11 p q v hq sep (Eq.trans (Eq.symm (hit)) (Eq.symm (t8))) (Eq.trans (hit) (Eq.symm (t10))) (hit)
  · have t0 : v 10 = v 1 := Eq.trans (Eq.symm (hp 4)) (Eq.trans (congrArg p (Eq.symm (hit))) (hp 0))
    have t1 : v 1 = v 2 := Eq.trans (Eq.symm (hq 3)) (Eq.trans (congrArg q (Eq.symm (hit))) (hq 0))
    have t2 : v 6 = v 4 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 1))
    have t3 : v 0 = v 4 := Eq.trans (Eq.symm (hq 2)) (Eq.trans (congrArg q (Eq.trans (h0) (t0))) (hq 1))
    have t4 : v 2 = v 11 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 1)))) (Eq.trans (congrArg p.symm (Eq.trans (Eq.trans (t2) (Eq.symm (t3))) (hit))) (p.symm_apply_eq.mpr (Eq.symm (hp 6))))
    have t5 : v 9 = v 1 := Eq.trans (Eq.symm (hp 3)) (Eq.trans (congrArg p (Eq.symm (t3))) (hp 0))
    have t6 : v 15 = v 5 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 9)))) (Eq.trans (congrArg q.symm (t5)) (q.symm_apply_eq.mpr (Eq.symm (hq 3))))
    have t7 : v 8 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 5)))) (Eq.trans (congrArg p.symm (Eq.trans (h0) (t0))) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    exact branch10 p q v hp hq sep (Eq.trans (Eq.trans (Eq.trans (h0) (t0)) (t1)) (t4)) (Eq.trans (hit) (Eq.symm (t6))) (Eq.symm (t7))
  · have t0 : v 5 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.symm (h0))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t1 : v 5 = v 1 := Eq.trans (Eq.symm (hp 6)) (Eq.trans (congrArg p (Eq.symm (hit))) (hp 0))
    have t2 : v 14 = v 4 := Eq.trans (Eq.symm (hq 5)) (Eq.trans (congrArg q (Eq.trans (Eq.symm (t0)) (t1))) (hq 1))
    have t3 : v 1 = v 4 := Eq.trans (Eq.symm (hq 3)) (Eq.trans (congrArg q (t1)) (hq 1))
    have t4 : v 17 = v 10 := Eq.trans (Eq.symm (hp 9)) (Eq.trans (congrArg p (Eq.trans (Eq.trans (t2) (Eq.symm (t3))) (Eq.symm (t1)))) (hp 4))
    have t5 : v 17 = v 2 := Eq.trans (Eq.symm (hq 7)) (Eq.trans (congrArg q (Eq.symm (hit))) (hq 0))
    have t6 : v 6 = v 4 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 1))
    have t7 : v 2 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 1)))) (Eq.trans (congrArg p.symm (Eq.trans (t6) (Eq.symm (t3)))) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    have t8 : v 15 = v 10 := Eq.trans (Eq.symm (hp 7)) (Eq.trans (congrArg p (Eq.trans (Eq.symm (h1)) (Eq.symm (t1)))) (hp 4))
    exact branch11 p q v hq sep (Eq.trans (Eq.trans (Eq.trans (Eq.trans (h0) (Eq.symm (t4))) (t5)) (t7)) (hit)) (Eq.trans (Eq.trans (Eq.trans (Eq.symm (t7)) (Eq.symm (t5))) (t4)) (Eq.symm (t8))) (Eq.trans (Eq.trans (Eq.trans (Eq.symm (t7)) (Eq.symm (t5))) (t4)) (Eq.symm (h0)))
  · have t0 : v 5 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 3)))) (Eq.trans (congrArg q.symm (Eq.symm (hit))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    have t1 : v 10 = v 7 := Eq.trans (Eq.symm (hp 4)) (Eq.trans (congrArg p (t0)) (hp 2))
    have t2 : v 3 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 2)))) (Eq.trans (congrArg p.symm (Eq.trans (Eq.symm (t1)) (Eq.symm (h0)))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t3 : v 11 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 6)))) (Eq.trans (congrArg p.symm (t0)) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t4 : v 4 = v 2 := Eq.trans (Eq.symm (hq 1)) (Eq.trans (congrArg q (Eq.symm (hit))) (hq 0))
    have t5 : v 9 = v 6 := Eq.trans (Eq.symm (hp 3)) (Eq.trans (congrArg p (t4)) (hp 1))
    have t6 : v 15 = v 12 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 9)))) (Eq.trans (congrArg q.symm (t5)) (q.symm_apply_eq.mpr (Eq.symm (hq 8))))
    exact branch9 p q v hp sep (Eq.trans (t2) (Eq.symm (t3))) (Eq.trans (Eq.trans (hit) (h1)) (Eq.symm (t6))) (Eq.trans (hit) (h1))
  · have t0 : v 0 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 0)))) (Eq.trans (congrArg q.symm (Eq.symm (hit))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    have t1 : v 6 = v 1 := Eq.trans (Eq.symm (hp 1)) (Eq.trans (congrArg p (Eq.symm (hit))) (hp 0))
    have t2 : v 12 = v 5 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 8)))) (Eq.trans (congrArg q.symm (t1)) (q.symm_apply_eq.mpr (Eq.symm (hq 3))))
    have t3 : v 11 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 6)))) (Eq.trans (congrArg p.symm (Eq.trans (Eq.symm (t2)) (Eq.symm (h1)))) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    have t4 : v 16 = v 2 := Eq.trans (Eq.symm (hq 6)) (Eq.trans (congrArg q (Eq.trans (Eq.symm (h0)) (Eq.symm (t0)))) (hq 0))
    have t5 : v 7 = v 1 := Eq.trans (Eq.symm (hp 2)) (Eq.trans (congrArg p (Eq.symm (t0))) (hp 0))
    have t6 : v 13 = v 4 := Eq.trans (Eq.symm (hq 4)) (Eq.trans (congrArg q (t5)) (hq 1))
    have t7 : v 6 = v 4 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 1))
    have t8 : v 16 = v 15 := Eq.trans (Eq.symm (hp 8)) (Eq.trans (congrArg p (Eq.trans (Eq.trans (Eq.trans (t6) (Eq.symm (t7))) (t1)) (h1))) (hp 7))
    exact branch11 p q v hq sep (Eq.trans (Eq.symm (t0)) (Eq.symm (t3))) (Eq.trans (Eq.trans (hit) (Eq.symm (t4))) (t8)) (t0)
  · have t0 : v 16 = v 1 := Eq.trans (Eq.symm (hp 8)) (Eq.trans (congrArg p (Eq.symm (hit))) (hp 0))
    have t1 : v 16 = v 0 := Eq.trans (Eq.symm (hq 6)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
    have t2 : v 5 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 3)))) (Eq.trans (congrArg q.symm (Eq.trans (Eq.symm (t0)) (t1))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    have t3 : v 5 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.symm (h0))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t4 : v 11 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 6)))) (Eq.trans (congrArg p.symm (t2)) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t5 : v 4 = v 2 := Eq.trans (Eq.symm (hq 1)) (Eq.trans (congrArg q (Eq.trans (Eq.symm (t0)) (t1))) (hq 0))
    have t6 : v 9 = v 6 := Eq.trans (Eq.symm (hp 3)) (Eq.trans (congrArg p (t5)) (hp 1))
    have t7 : v 6 = v 4 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 1))
    have t8 : v 15 = v 0 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 9)))) (Eq.trans (congrArg q.symm (Eq.trans (Eq.trans (t6) (t7)) (t5))) (q.symm_apply_eq.mpr (Eq.symm (hq 0))))
    exact branch9 p q v hp sep (Eq.trans (Eq.trans (Eq.symm (t2)) (t3)) (Eq.symm (t4))) (Eq.symm (t8)) (Eq.trans (Eq.trans (Eq.symm (t1)) (t0)) (h1))
  · have t0 : v 5 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.symm (h0))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t1 : v 14 = v 1 := Eq.trans (Eq.symm (hq 5)) (Eq.trans (congrArg q (Eq.symm (t0))) (hq 3))
    have t2 : v 17 = v 15 := Eq.trans (Eq.symm (hp 9)) (Eq.trans (congrArg p (Eq.trans (t1) (h1))) (hp 7))
    have t3 : v 6 = v 4 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 1))
    have t4 : v 13 = v 2 := Eq.trans (Eq.symm (hq 4)) (Eq.trans (congrArg q (Eq.symm (hit))) (hq 0))
    have t5 : v 16 = v 6 := Eq.trans (Eq.symm (hp 8)) (Eq.trans (congrArg p (t4)) (hp 1))
    have t6 : v 16 = v 0 := Eq.trans (Eq.symm (hq 6)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
    have t7 : v 9 = v 1 := Eq.trans (Eq.symm (hp 3)) (Eq.trans (congrArg p (Eq.trans (Eq.trans (Eq.symm (t3)) (Eq.symm (t5))) (t6))) (hp 0))
    have t8 : v 15 = v 5 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 9)))) (Eq.trans (congrArg q.symm (t7)) (q.symm_apply_eq.mpr (Eq.symm (hq 3))))
    have t9 : v 1 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 1)))) (Eq.trans (congrArg q.symm (Eq.trans (Eq.trans (Eq.symm (t3)) (Eq.symm (t5))) (t6))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    have t10 : v 5 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.trans (Eq.symm (h0)) (Eq.symm (t9)))) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    have t11 : v 11 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 7)))) (Eq.trans (congrArg q.symm (Eq.trans (Eq.trans (t2) (t8)) (t10))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    exact branch10 p q v hp hq sep (Eq.symm (t11)) (Eq.trans (Eq.symm (t10)) (Eq.symm (t8))) (Eq.trans (Eq.symm (t10)) (t0))
  · have t0 : v 5 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.symm (h0))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t1 : v 16 = v 2 := Eq.trans (Eq.symm (hq 6)) (Eq.trans (congrArg q (Eq.trans (Eq.symm (h0)) (Eq.symm (hit)))) (hq 0))
    have t2 : v 0 = v 2 := Eq.trans (Eq.symm (hq 2)) (Eq.trans (congrArg q (Eq.symm (hit))) (hq 0))
    have t3 : v 13 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 8)))) (Eq.trans (congrArg p.symm (Eq.trans (Eq.trans (t1) (Eq.symm (t2))) (hit))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t4 : v 7 = v 1 := Eq.trans (Eq.symm (hp 2)) (Eq.trans (congrArg p (Eq.symm (hit))) (hp 0))
    have t5 : v 13 = v 4 := Eq.trans (Eq.symm (hq 4)) (Eq.trans (congrArg q (t4)) (hq 1))
    have t6 : v 6 = v 4 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 1))
    have t7 : v 6 = v 1 := Eq.trans (Eq.symm (hp 1)) (Eq.trans (congrArg p (Eq.symm (t2))) (hp 0))
    have t8 : v 11 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 6)))) (Eq.trans (congrArg p.symm (Eq.trans (Eq.trans (Eq.trans (Eq.trans (t0) (Eq.symm (t3))) (t5)) (Eq.symm (t6))) (t7))) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    have t9 : v 16 = v 9 := Eq.trans (Eq.symm (hp 8)) (Eq.trans (congrArg p (t5)) (hp 3))
    have t10 : v 15 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 9)))) (Eq.trans (congrArg q.symm (Eq.trans (Eq.trans (Eq.symm (t9)) (t1)) (Eq.symm (t2)))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    exact branch11 p q v hq sep (Eq.trans (Eq.symm (hit)) (Eq.symm (t8))) (Eq.trans (hit) (Eq.symm (t10))) (hit)
  · have t0 : v 10 = v 1 := Eq.trans (Eq.symm (hp 4)) (Eq.trans (congrArg p (Eq.symm (hit))) (hp 0))
    have t1 : v 1 = v 2 := Eq.trans (Eq.symm (hq 3)) (Eq.trans (congrArg q (Eq.symm (hit))) (hq 0))
    have t2 : v 6 = v 4 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 1))
    have t3 : v 0 = v 4 := Eq.trans (Eq.symm (hq 2)) (Eq.trans (congrArg q (Eq.trans (h0) (t0))) (hq 1))
    have t4 : v 2 = v 11 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 1)))) (Eq.trans (congrArg p.symm (Eq.trans (Eq.trans (t2) (Eq.symm (t3))) (hit))) (p.symm_apply_eq.mpr (Eq.symm (hp 6))))
    have t5 : v 9 = v 1 := Eq.trans (Eq.symm (hp 3)) (Eq.trans (congrArg p (Eq.symm (t3))) (hp 0))
    have t6 : v 15 = v 5 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 9)))) (Eq.trans (congrArg q.symm (t5)) (q.symm_apply_eq.mpr (Eq.symm (hq 3))))
    have t7 : v 8 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 5)))) (Eq.trans (congrArg p.symm (Eq.trans (h0) (t0))) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    exact branch10 p q v hp hq sep (Eq.trans (Eq.trans (Eq.trans (h0) (t0)) (t1)) (t4)) (Eq.trans (hit) (Eq.symm (t6))) (Eq.symm (t7))
  · have t0 : v 5 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.symm (h0))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t1 : v 14 = v 1 := Eq.trans (Eq.symm (hq 5)) (Eq.trans (congrArg q (Eq.symm (t0))) (hq 3))
    have t2 : v 17 = v 15 := Eq.trans (Eq.symm (hp 9)) (Eq.trans (congrArg p (Eq.trans (t1) (h1))) (hp 7))
    have t3 : v 11 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 7)))) (Eq.trans (congrArg q.symm (Eq.trans (t2) (Eq.symm (hit)))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    have t4 : v 16 = v 0 := Eq.trans (Eq.symm (hq 6)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
    exact branch12 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm (t3)) (hit) (Eq.symm (t4))
  · have t0 : v 1 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 1)))) (Eq.trans (congrArg q.symm (Eq.symm (hit))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    have t1 : v 9 = v 1 := Eq.trans (Eq.symm (hp 3)) (Eq.trans (congrArg p (Eq.symm (hit))) (hp 0))
    have t2 : v 15 = v 5 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 9)))) (Eq.trans (congrArg q.symm (t1)) (q.symm_apply_eq.mpr (Eq.symm (hq 3))))
    have t3 : v 5 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.trans (Eq.symm (h0)) (Eq.symm (t0)))) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    have t4 : v 9 = v 2 := Eq.trans (Eq.symm (hq 9)) (Eq.trans (congrArg q (Eq.trans (t2) (t3))) (hq 0))
    have t5 : v 6 = v 4 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 1))
    have t6 : v 2 = v 11 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 1)))) (Eq.trans (congrArg p.symm (Eq.trans (Eq.trans (t5) (Eq.symm (hit))) (Eq.symm (t3)))) (p.symm_apply_eq.mpr (Eq.symm (hp 6))))
    have t7 : v 8 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 5)))) (Eq.trans (congrArg p.symm (Eq.symm (t0))) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    exact branch10 p q v hp hq sep (Eq.trans (Eq.trans (Eq.trans (Eq.symm (t0)) (Eq.symm (t1))) (t4)) (t6)) (Eq.trans (Eq.symm (t3)) (Eq.symm (t2))) (Eq.symm (t7))
  · have t0 : v 0 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 0)))) (Eq.trans (congrArg q.symm (Eq.symm (hit))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    have t1 : v 6 = v 1 := Eq.trans (Eq.symm (hp 1)) (Eq.trans (congrArg p (Eq.symm (hit))) (hp 0))
    have t2 : v 12 = v 5 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 8)))) (Eq.trans (congrArg q.symm (t1)) (q.symm_apply_eq.mpr (Eq.symm (hq 3))))
    have t3 : v 11 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 6)))) (Eq.trans (congrArg p.symm (Eq.trans (Eq.symm (t2)) (Eq.symm (h1)))) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    have t4 : v 16 = v 2 := Eq.trans (Eq.symm (hq 6)) (Eq.trans (congrArg q (Eq.trans (Eq.symm (h0)) (Eq.symm (t0)))) (hq 0))
    have t5 : v 7 = v 1 := Eq.trans (Eq.symm (hp 2)) (Eq.trans (congrArg p (Eq.symm (t0))) (hp 0))
    have t6 : v 13 = v 4 := Eq.trans (Eq.symm (hq 4)) (Eq.trans (congrArg q (t5)) (hq 1))
    have t7 : v 6 = v 4 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 1))
    have t8 : v 16 = v 15 := Eq.trans (Eq.symm (hp 8)) (Eq.trans (congrArg p (Eq.trans (Eq.trans (Eq.trans (t6) (Eq.symm (t7))) (t1)) (h1))) (hp 7))
    exact branch11 p q v hq sep (Eq.trans (Eq.symm (t0)) (Eq.symm (t3))) (Eq.trans (Eq.trans (hit) (Eq.symm (t4))) (t8)) (t0)
  · exact branch56 p q v hq sep (h0) (h1) (hit)
  · have t0 : v 5 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.symm (h0))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t1 : v 14 = v 1 := Eq.trans (Eq.symm (hq 5)) (Eq.trans (congrArg q (Eq.symm (t0))) (hq 3))
    have t2 : v 17 = v 15 := Eq.trans (Eq.symm (hp 9)) (Eq.trans (congrArg p (Eq.trans (t1) (h1))) (hp 7))
    have t3 : v 6 = v 4 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 1))
    have t4 : v 16 = v 7 := Eq.trans (Eq.symm (hp 8)) (Eq.trans (congrArg p (hit)) (hp 2))
    have t5 : v 16 = v 0 := Eq.trans (Eq.symm (hq 6)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
    have t6 : v 13 = v 2 := Eq.trans (Eq.symm (hq 4)) (Eq.trans (congrArg q (Eq.trans (Eq.symm (t4)) (t5))) (hq 0))
    have t7 : v 16 = v 6 := Eq.trans (Eq.symm (hp 8)) (Eq.trans (congrArg p (t6)) (hp 1))
    have t8 : v 9 = v 1 := Eq.trans (Eq.symm (hp 3)) (Eq.trans (congrArg p (Eq.trans (Eq.trans (Eq.symm (t3)) (Eq.symm (t7))) (t5))) (hp 0))
    have t9 : v 15 = v 5 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 9)))) (Eq.trans (congrArg q.symm (t8)) (q.symm_apply_eq.mpr (Eq.symm (hq 3))))
    have t10 : v 1 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 1)))) (Eq.trans (congrArg q.symm (Eq.trans (Eq.trans (Eq.symm (t3)) (Eq.symm (t7))) (t5))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    have t11 : v 5 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.trans (Eq.symm (h0)) (Eq.symm (t10)))) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    have t12 : v 11 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 7)))) (Eq.trans (congrArg q.symm (Eq.trans (Eq.trans (t2) (t9)) (t11))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    exact branch10 p q v hp hq sep (Eq.symm (t12)) (Eq.trans (Eq.symm (t11)) (Eq.symm (t9))) (Eq.trans (Eq.symm (t11)) (t0))
  · have t0 : v 16 = v 10 := Eq.trans (Eq.symm (hp 8)) (Eq.trans (congrArg p (hit)) (hp 4))
    have t1 : v 16 = v 0 := Eq.trans (Eq.symm (hq 6)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
    have t2 : v 5 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.symm (h0))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t3 : v 7 = v 1 := Eq.trans (Eq.symm (hp 2)) (Eq.trans (congrArg p (Eq.trans (Eq.trans (h0) (Eq.symm (t0))) (t1))) (hp 0))
    have t4 : v 13 = v 4 := Eq.trans (Eq.symm (hq 4)) (Eq.trans (congrArg q (t3)) (hq 1))
    have t5 : v 3 = v 9 := Eq.trans (Eq.symm (hp 5)) (Eq.trans (congrArg p (Eq.trans (Eq.trans (Eq.symm (t2)) (Eq.symm (hit))) (t4))) (hp 3))
    have t6 : v 15 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 9)))) (Eq.trans (congrArg q.symm (Eq.trans (Eq.trans (Eq.trans (Eq.symm (t5)) (h0)) (Eq.symm (t0))) (t1))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    have t7 : v 12 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 7)))) (Eq.trans (congrArg p.symm (t6)) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t8 : v 11 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 6)))) (Eq.trans (congrArg p.symm (Eq.trans (Eq.trans (t2) (Eq.symm (t7))) (Eq.symm (h1)))) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    exact branch11 p q v hq sep (Eq.trans (Eq.trans (Eq.trans (h0) (Eq.symm (t0))) (t1)) (Eq.symm (t8))) (Eq.trans (Eq.trans (Eq.trans (Eq.symm (t1)) (t0)) (Eq.symm (h0))) (Eq.symm (t6))) (Eq.trans (Eq.trans (Eq.symm (t1)) (t0)) (Eq.symm (h0)))
  · have t0 : v 16 = v 5 := Eq.trans (Eq.symm (hp 8)) (Eq.trans (congrArg p (hit)) (hp 6))
    have t1 : v 16 = v 0 := Eq.trans (Eq.symm (hq 6)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
    have t2 : v 10 = v 1 := Eq.trans (Eq.symm (hp 4)) (Eq.trans (congrArg p (Eq.trans (Eq.symm (t0)) (t1))) (hp 0))
    have t3 : v 1 = v 2 := Eq.trans (Eq.symm (hq 3)) (Eq.trans (congrArg q (Eq.trans (Eq.symm (t0)) (t1))) (hq 0))
    have t4 : v 6 = v 4 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 1))
    have t5 : v 16 = v 4 := Eq.trans (Eq.symm (hq 6)) (Eq.trans (congrArg q (t2)) (hq 1))
    have t6 : v 2 = v 11 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 1)))) (Eq.trans (congrArg p.symm (Eq.trans (Eq.trans (t4) (Eq.symm (t5))) (t0))) (p.symm_apply_eq.mpr (Eq.symm (hp 6))))
    have t7 : v 9 = v 1 := Eq.trans (Eq.symm (hp 3)) (Eq.trans (congrArg p (Eq.trans (Eq.symm (t5)) (t1))) (hp 0))
    have t8 : v 15 = v 5 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 9)))) (Eq.trans (congrArg q.symm (t7)) (q.symm_apply_eq.mpr (Eq.symm (hq 3))))
    have t9 : v 5 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.symm (h0))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    exact branch10 p q v hp hq sep (Eq.trans (Eq.trans (Eq.trans (h0) (t2)) (t3)) (t6)) (Eq.trans (Eq.trans (Eq.symm (t1)) (t0)) (Eq.symm (t8))) (Eq.trans (Eq.trans (Eq.symm (t1)) (t0)) (t9))
  · have t0 : v 7 = v 5 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 4)))) (Eq.trans (congrArg q.symm (hit)) (q.symm_apply_eq.mpr (Eq.symm (hq 3))))
    have t1 : v 3 = v 11 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 2)))) (Eq.trans (congrArg p.symm (t0)) (p.symm_apply_eq.mpr (Eq.symm (hp 6))))
    have t2 : v 16 = v 0 := Eq.trans (Eq.symm (hq 6)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
    have t3 : v 16 = v 15 := Eq.trans (Eq.symm (hp 8)) (Eq.trans (congrArg p (Eq.trans (hit) (h1))) (hp 7))
    exact branch12 p q v hp hq sep G e₀ e₁ e₂ no (t1) (Eq.trans (Eq.symm (t2)) (t3)) (Eq.symm (t2))
  · have t0 : v 5 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.symm (h0))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t1 : v 14 = v 1 := Eq.trans (Eq.symm (hq 5)) (Eq.trans (congrArg q (Eq.symm (t0))) (hq 3))
    have t2 : v 17 = v 15 := Eq.trans (Eq.symm (hp 9)) (Eq.trans (congrArg p (Eq.trans (t1) (h1))) (hp 7))
    have t3 : v 6 = v 4 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 1))
    have t4 : v 16 = v 6 := Eq.trans (Eq.symm (hp 8)) (Eq.trans (congrArg p (hit)) (hp 1))
    have t5 : v 16 = v 0 := Eq.trans (Eq.symm (hq 6)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
    have t6 : v 9 = v 1 := Eq.trans (Eq.symm (hp 3)) (Eq.trans (congrArg p (Eq.trans (Eq.trans (Eq.symm (t3)) (Eq.symm (t4))) (t5))) (hp 0))
    have t7 : v 15 = v 5 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 9)))) (Eq.trans (congrArg q.symm (t6)) (q.symm_apply_eq.mpr (Eq.symm (hq 3))))
    have t8 : v 1 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 1)))) (Eq.trans (congrArg q.symm (Eq.trans (Eq.trans (Eq.symm (t3)) (Eq.symm (t4))) (t5))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    have t9 : v 5 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.trans (Eq.symm (h0)) (Eq.symm (t8)))) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    have t10 : v 11 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 7)))) (Eq.trans (congrArg q.symm (Eq.trans (Eq.trans (t2) (t7)) (t9))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    exact branch10 p q v hp hq sep (Eq.symm (t10)) (Eq.trans (Eq.symm (t9)) (Eq.symm (t7))) (Eq.trans (Eq.symm (t9)) (t0))
  · exact branch56 p q v hq sep (h0) (h1) (hit)
  · have t0 : v 5 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.symm (h0))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t1 : v 14 = v 1 := Eq.trans (Eq.symm (hq 5)) (Eq.trans (congrArg q (Eq.symm (t0))) (hq 3))
    have t2 : v 17 = v 15 := Eq.trans (Eq.symm (hp 9)) (Eq.trans (congrArg p (Eq.trans (t1) (h1))) (hp 7))
    have t3 : v 6 = v 4 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 1))
    have t4 : v 16 = v 7 := Eq.trans (Eq.symm (hp 8)) (Eq.trans (congrArg p (hit)) (hp 2))
    have t5 : v 16 = v 0 := Eq.trans (Eq.symm (hq 6)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
    have t6 : v 13 = v 2 := Eq.trans (Eq.symm (hq 4)) (Eq.trans (congrArg q (Eq.trans (Eq.symm (t4)) (t5))) (hq 0))
    have t7 : v 16 = v 6 := Eq.trans (Eq.symm (hp 8)) (Eq.trans (congrArg p (t6)) (hp 1))
    have t8 : v 9 = v 1 := Eq.trans (Eq.symm (hp 3)) (Eq.trans (congrArg p (Eq.trans (Eq.trans (Eq.symm (t3)) (Eq.symm (t7))) (t5))) (hp 0))
    have t9 : v 15 = v 5 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 9)))) (Eq.trans (congrArg q.symm (t8)) (q.symm_apply_eq.mpr (Eq.symm (hq 3))))
    have t10 : v 1 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 1)))) (Eq.trans (congrArg q.symm (Eq.trans (Eq.trans (Eq.symm (t3)) (Eq.symm (t7))) (t5))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    have t11 : v 5 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.trans (Eq.symm (h0)) (Eq.symm (t10)))) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    have t12 : v 11 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 7)))) (Eq.trans (congrArg q.symm (Eq.trans (Eq.trans (t2) (t9)) (t11))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    exact branch10 p q v hp hq sep (Eq.symm (t12)) (Eq.trans (Eq.symm (t11)) (Eq.symm (t9))) (Eq.trans (Eq.symm (t11)) (t0))
  · have t0 : v 16 = v 10 := Eq.trans (Eq.symm (hp 8)) (Eq.trans (congrArg p (hit)) (hp 4))
    have t1 : v 16 = v 0 := Eq.trans (Eq.symm (hq 6)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
    have t2 : v 5 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.symm (h0))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t3 : v 7 = v 1 := Eq.trans (Eq.symm (hp 2)) (Eq.trans (congrArg p (Eq.trans (Eq.trans (h0) (Eq.symm (t0))) (t1))) (hp 0))
    have t4 : v 13 = v 4 := Eq.trans (Eq.symm (hq 4)) (Eq.trans (congrArg q (t3)) (hq 1))
    have t5 : v 3 = v 9 := Eq.trans (Eq.symm (hp 5)) (Eq.trans (congrArg p (Eq.trans (Eq.trans (Eq.symm (t2)) (Eq.symm (hit))) (t4))) (hp 3))
    have t6 : v 15 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 9)))) (Eq.trans (congrArg q.symm (Eq.trans (Eq.trans (Eq.trans (Eq.symm (t5)) (h0)) (Eq.symm (t0))) (t1))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    have t7 : v 12 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 7)))) (Eq.trans (congrArg p.symm (t6)) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t8 : v 11 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 6)))) (Eq.trans (congrArg p.symm (Eq.trans (Eq.trans (t2) (Eq.symm (t7))) (Eq.symm (h1)))) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    exact branch11 p q v hq sep (Eq.trans (Eq.trans (Eq.trans (h0) (Eq.symm (t0))) (t1)) (Eq.symm (t8))) (Eq.trans (Eq.trans (Eq.trans (Eq.symm (t1)) (t0)) (Eq.symm (h0))) (Eq.symm (t6))) (Eq.trans (Eq.trans (Eq.symm (t1)) (t0)) (Eq.symm (h0)))
  · exact branch57 p q v hp hq sep G e₀ e₁ e₂ no (h0) (h1) (hit)
  · have t0 : v 5 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.symm (h0))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t1 : v 14 = v 1 := Eq.trans (Eq.symm (hq 5)) (Eq.trans (congrArg q (Eq.symm (t0))) (hq 3))
    have t2 : v 17 = v 15 := Eq.trans (Eq.symm (hp 9)) (Eq.trans (congrArg p (Eq.trans (t1) (h1))) (hp 7))
    have t3 : v 16 = v 9 := Eq.trans (Eq.symm (hp 8)) (Eq.trans (congrArg p (hit)) (hp 3))
    have t4 : v 16 = v 0 := Eq.trans (Eq.symm (hq 6)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
    have t5 : v 15 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 9)))) (Eq.trans (congrArg q.symm (Eq.trans (Eq.symm (t3)) (t4))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    have t6 : v 7 = v 1 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 4)))) (Eq.trans (congrArg q.symm (hit)) (q.symm_apply_eq.mpr (Eq.symm (hq 1))))
    have t7 : v 3 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 2)))) (Eq.trans (congrArg p.symm (t6)) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    have t8 : v 11 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 7)))) (Eq.trans (congrArg q.symm (Eq.trans (Eq.trans (t2) (t5)) (t7))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    exact branch11 p q v hq sep (Eq.symm (t8)) (Eq.trans (Eq.symm (t7)) (Eq.symm (t5))) (Eq.symm (t7))
  · have t0 : v 5 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.symm (h0))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t1 : v 14 = v 1 := Eq.trans (Eq.symm (hq 5)) (Eq.trans (congrArg q (Eq.symm (t0))) (hq 3))
    have t2 : v 17 = v 15 := Eq.trans (Eq.symm (hp 9)) (Eq.trans (congrArg p (Eq.trans (t1) (h1))) (hp 7))
    have t3 : v 6 = v 4 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 1))
    have t4 : v 16 = v 6 := Eq.trans (Eq.symm (hp 8)) (Eq.trans (congrArg p (hit)) (hp 1))
    have t5 : v 16 = v 0 := Eq.trans (Eq.symm (hq 6)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
    have t6 : v 9 = v 1 := Eq.trans (Eq.symm (hp 3)) (Eq.trans (congrArg p (Eq.trans (Eq.trans (Eq.symm (t3)) (Eq.symm (t4))) (t5))) (hp 0))
    have t7 : v 15 = v 5 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 9)))) (Eq.trans (congrArg q.symm (t6)) (q.symm_apply_eq.mpr (Eq.symm (hq 3))))
    have t8 : v 1 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 1)))) (Eq.trans (congrArg q.symm (Eq.trans (Eq.trans (Eq.symm (t3)) (Eq.symm (t4))) (t5))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    have t9 : v 5 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.trans (Eq.symm (h0)) (Eq.symm (t8)))) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    have t10 : v 11 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 7)))) (Eq.trans (congrArg q.symm (Eq.trans (Eq.trans (t2) (t7)) (t9))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    exact branch10 p q v hp hq sep (Eq.symm (t10)) (Eq.trans (Eq.symm (t9)) (Eq.symm (t7))) (Eq.trans (Eq.symm (t9)) (t0))
  · have t0 : v 3 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 2)))) (Eq.trans (congrArg p.symm (hit)) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t1 : v 14 = v 0 := Eq.trans (Eq.symm (hq 5)) (Eq.trans (congrArg q (Eq.symm (t0))) (hq 2))
    have t2 : v 17 = v 1 := Eq.trans (Eq.symm (hp 9)) (Eq.trans (congrArg p (t1)) (hp 0))
    have t3 : v 13 = v 0 := Eq.trans (Eq.symm (hq 4)) (Eq.trans (congrArg q (hit)) (hq 2))
    have t4 : v 16 = v 1 := Eq.trans (Eq.symm (hp 8)) (Eq.trans (congrArg p (t3)) (hp 0))
    have t5 : v 16 = v 0 := Eq.trans (Eq.symm (hq 6)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
    have t6 : v 11 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 7)))) (Eq.trans (congrArg q.symm (Eq.trans (Eq.trans (t2) (Eq.symm (t4))) (t5))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    have t7 : v 4 = v 2 := Eq.trans (Eq.symm (hq 1)) (Eq.trans (congrArg q (Eq.trans (Eq.symm (t4)) (t5))) (hq 0))
    have t8 : v 9 = v 6 := Eq.trans (Eq.symm (hp 3)) (Eq.trans (congrArg p (t7)) (hp 1))
    have t9 : v 6 = v 4 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 1))
    have t10 : v 15 = v 0 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 9)))) (Eq.trans (congrArg q.symm (Eq.trans (Eq.trans (t8) (t9)) (t7))) (q.symm_apply_eq.mpr (Eq.symm (hq 0))))
    exact branch9 p q v hp sep (Eq.symm (t6)) (Eq.symm (t10)) (Eq.trans (Eq.trans (Eq.symm (t5)) (t4)) (h1))
  · have t0 : v 3 = v 11 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 2)))) (Eq.trans (congrArg p.symm (hit)) (p.symm_apply_eq.mpr (Eq.symm (hp 6))))
    have t1 : v 16 = v 0 := Eq.trans (Eq.symm (hq 6)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
    have t2 : v 13 = v 1 := Eq.trans (Eq.symm (hq 4)) (Eq.trans (congrArg q (hit)) (hq 3))
    have t3 : v 16 = v 15 := Eq.trans (Eq.symm (hp 8)) (Eq.trans (congrArg p (Eq.trans (t2) (h1))) (hp 7))
    exact branch12 p q v hp hq sep G e₀ e₁ e₂ no (t0) (Eq.trans (Eq.symm (t1)) (t3)) (Eq.symm (t1))
  · have t0 : v 17 = v 13 := Eq.trans (Eq.symm (hq 7)) (Eq.trans (congrArg q (Eq.symm (hit))) (hq 4))
    have t1 : v 5 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.symm (h0))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t2 : v 14 = v 1 := Eq.trans (Eq.symm (hq 5)) (Eq.trans (congrArg q (Eq.symm (t1))) (hq 3))
    have t3 : v 17 = v 15 := Eq.trans (Eq.symm (hp 9)) (Eq.trans (congrArg p (Eq.trans (t2) (h1))) (hp 7))
    exact branch57 p q v hp hq sep G e₀ e₁ e₂ no (h0) (h1) (Eq.trans (Eq.symm (t0)) (t3))
  · have t0 : v 3 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 2)))) (Eq.trans (congrArg p.symm (hit)) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    have t1 : v 5 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.symm (h0))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t2 : v 13 = v 4 := Eq.trans (Eq.symm (hq 4)) (Eq.trans (congrArg q (hit)) (hq 1))
    have t3 : v 16 = v 9 := Eq.trans (Eq.symm (hp 8)) (Eq.trans (congrArg p (t2)) (hp 3))
    have t4 : v 16 = v 2 := Eq.trans (Eq.symm (hq 6)) (Eq.trans (congrArg q (Eq.trans (Eq.symm (h0)) (t0))) (hq 0))
    have t5 : v 0 = v 2 := Eq.trans (Eq.symm (hq 2)) (Eq.trans (congrArg q (t0)) (hq 0))
    have t6 : v 15 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 9)))) (Eq.trans (congrArg q.symm (Eq.trans (Eq.trans (Eq.symm (t3)) (t4)) (Eq.symm (t5)))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    have t7 : v 12 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 7)))) (Eq.trans (congrArg p.symm (t6)) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t8 : v 11 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 6)))) (Eq.trans (congrArg p.symm (Eq.trans (Eq.trans (t1) (Eq.symm (t7))) (Eq.symm (h1)))) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    exact branch11 p q v hq sep (Eq.trans (t0) (Eq.symm (t8))) (Eq.trans (Eq.symm (t0)) (Eq.symm (t6))) (Eq.symm (t0))
  · exact branch58 p q v hp hq sep G e₀ e₁ e₂ no (h0) (h1) (hit)
  · have t0 : v 3 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 2)))) (Eq.trans (congrArg p.symm (hit)) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t1 : v 14 = v 0 := Eq.trans (Eq.symm (hq 5)) (Eq.trans (congrArg q (Eq.symm (t0))) (hq 2))
    have t2 : v 17 = v 1 := Eq.trans (Eq.symm (hp 9)) (Eq.trans (congrArg p (t1)) (hp 0))
    have t3 : v 13 = v 0 := Eq.trans (Eq.symm (hq 4)) (Eq.trans (congrArg q (hit)) (hq 2))
    have t4 : v 16 = v 1 := Eq.trans (Eq.symm (hp 8)) (Eq.trans (congrArg p (t3)) (hp 0))
    have t5 : v 16 = v 0 := Eq.trans (Eq.symm (hq 6)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
    have t6 : v 11 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 7)))) (Eq.trans (congrArg q.symm (Eq.trans (Eq.trans (t2) (Eq.symm (t4))) (t5))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    have t7 : v 4 = v 2 := Eq.trans (Eq.symm (hq 1)) (Eq.trans (congrArg q (Eq.trans (Eq.symm (t4)) (t5))) (hq 0))
    have t8 : v 9 = v 6 := Eq.trans (Eq.symm (hp 3)) (Eq.trans (congrArg p (t7)) (hp 1))
    have t9 : v 6 = v 4 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 1))
    have t10 : v 15 = v 0 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 9)))) (Eq.trans (congrArg q.symm (Eq.trans (Eq.trans (t8) (t9)) (t7))) (q.symm_apply_eq.mpr (Eq.symm (hq 0))))
    exact branch9 p q v hp sep (Eq.symm (t6)) (Eq.symm (t10)) (Eq.trans (Eq.trans (Eq.symm (t5)) (t4)) (h1))
  · have t0 : v 3 = v 11 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 2)))) (Eq.trans (congrArg p.symm (hit)) (p.symm_apply_eq.mpr (Eq.symm (hp 6))))
    have t1 : v 16 = v 0 := Eq.trans (Eq.symm (hq 6)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
    have t2 : v 13 = v 1 := Eq.trans (Eq.symm (hq 4)) (Eq.trans (congrArg q (hit)) (hq 3))
    have t3 : v 16 = v 15 := Eq.trans (Eq.symm (hp 8)) (Eq.trans (congrArg p (Eq.trans (t2) (h1))) (hp 7))
    exact branch12 p q v hp hq sep G e₀ e₁ e₂ no (t0) (Eq.trans (Eq.symm (t1)) (t3)) (Eq.symm (t1))
  · have t0 : v 12 = v 3 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 7)))) (Eq.trans (congrArg p.symm (Eq.symm (hit))) (p.symm_apply_eq.mpr (Eq.symm (hp 2))))
    have t1 : v 5 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.symm (h0))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t2 : v 8 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 5)))) (Eq.trans (congrArg p.symm (Eq.trans (Eq.symm (t0)) (Eq.symm (h1)))) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    have t3 : v 1 = v 2 := Eq.trans (Eq.symm (hq 3)) (Eq.trans (congrArg q (Eq.trans (t1) (t2))) (hq 0))
    have t4 : v 6 = v 4 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 1))
    have t5 : v 0 = v 4 := Eq.trans (Eq.symm (hq 2)) (Eq.trans (congrArg q (Eq.trans (Eq.symm (t0)) (Eq.symm (h1)))) (hq 1))
    have t6 : v 2 = v 11 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 1)))) (Eq.trans (congrArg p.symm (Eq.trans (Eq.trans (Eq.trans (t4) (Eq.symm (t5))) (Eq.symm (t2))) (Eq.symm (t1)))) (p.symm_apply_eq.mpr (Eq.symm (hp 6))))
    have t7 : v 9 = v 1 := Eq.trans (Eq.symm (hp 3)) (Eq.trans (congrArg p (Eq.symm (t5))) (hp 0))
    have t8 : v 15 = v 5 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 9)))) (Eq.trans (congrArg q.symm (t7)) (q.symm_apply_eq.mpr (Eq.symm (hq 3))))
    exact branch10 p q v hp hq sep (Eq.trans (Eq.trans (Eq.trans (Eq.symm (t0)) (Eq.symm (h1))) (t3)) (t6)) (Eq.trans (Eq.trans (Eq.symm (t2)) (Eq.symm (t1))) (Eq.symm (t8))) (Eq.symm (t2))
  · exact branch59 p q v hp hq sep G e₀ e₁ e₂ no (h0) (h1) (hit)
  · exact branch58 p q v hp hq sep G e₀ e₁ e₂ no (h0) (h1) (hit)
  · have t0 : v 10 = v 7 := Eq.trans (Eq.symm (hp 4)) (Eq.trans (congrArg p (Eq.symm (hit))) (hp 2))
    have t1 : v 3 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 2)))) (Eq.trans (congrArg p.symm (Eq.trans (Eq.symm (t0)) (Eq.symm (h0)))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t2 : v 11 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 6)))) (Eq.trans (congrArg p.symm (Eq.symm (hit))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t3 : v 1 = v 0 := Eq.trans (Eq.symm (hq 3)) (Eq.trans (congrArg q (Eq.symm (hit))) (hq 2))
    have t4 : v 15 = v 1 := Eq.trans (Eq.symm (hp 7)) (Eq.trans (congrArg p (Eq.trans (Eq.symm (h1)) (t3))) (hp 0))
    exact branch9 p q v hp sep (Eq.trans (t1) (Eq.symm (t2))) (Eq.trans (Eq.symm (t3)) (Eq.symm (t4))) (Eq.trans (Eq.symm (t3)) (h1))
  · have t0 : v 16 = v 0 := Eq.trans (Eq.symm (hq 6)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
    have t1 : v 5 = v 7 := Eq.trans (Eq.symm (hp 6)) (Eq.trans (congrArg p (Eq.symm (hit))) (hp 2))
    have t2 : v 13 = v 1 := Eq.trans (Eq.symm (hq 4)) (Eq.trans (congrArg q (Eq.symm (t1))) (hq 3))
    have t3 : v 16 = v 15 := Eq.trans (Eq.symm (hp 8)) (Eq.trans (congrArg p (Eq.trans (t2) (h1))) (hp 7))
    exact branch12 p q v hp hq sep G e₀ e₁ e₂ no (hit) (Eq.trans (Eq.symm (t0)) (t3)) (Eq.symm (t0))
  · have t0 : v 8 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 5)))) (Eq.trans (congrArg p.symm (hit)) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    have t1 : v 14 = v 2 := Eq.trans (Eq.symm (hq 5)) (Eq.trans (congrArg q (t0)) (hq 0))
    have t2 : v 17 = v 6 := Eq.trans (Eq.symm (hp 9)) (Eq.trans (congrArg p (t1)) (hp 1))
    have t3 : v 6 = v 4 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 1))
    have t4 : v 0 = v 4 := Eq.trans (Eq.symm (hq 2)) (Eq.trans (congrArg q (hit)) (hq 1))
    have t5 : v 11 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 7)))) (Eq.trans (congrArg q.symm (Eq.trans (Eq.trans (t2) (t3)) (Eq.symm (t4)))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    have t6 : v 5 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.trans (Eq.symm (h0)) (hit))) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    have t7 : v 9 = v 1 := Eq.trans (Eq.symm (hp 3)) (Eq.trans (congrArg p (Eq.symm (t4))) (hp 0))
    have t8 : v 15 = v 5 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 9)))) (Eq.trans (congrArg q.symm (t7)) (q.symm_apply_eq.mpr (Eq.symm (hq 3))))
    exact branch10 p q v hp hq sep (Eq.symm (t5)) (Eq.trans (Eq.symm (t6)) (Eq.symm (t8))) (Eq.symm (t0))
  · have t0 : v 7 = v 6 := Eq.trans (Eq.symm (hp 2)) (Eq.trans (congrArg p (hit)) (hp 1))
    have t1 : v 6 = v 4 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 1))
    exact branch59 p q v hp hq sep G e₀ e₁ e₂ no (h0) (h1) (Eq.trans (t0) (t1))
  · have t0 : v 10 = v 7 := Eq.trans (Eq.symm (hp 4)) (Eq.trans (congrArg p (Eq.symm (hit))) (hp 2))
    have t1 : v 3 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 2)))) (Eq.trans (congrArg p.symm (Eq.trans (Eq.symm (t0)) (Eq.symm (h0)))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t2 : v 11 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 6)))) (Eq.trans (congrArg p.symm (Eq.symm (hit))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t3 : v 1 = v 0 := Eq.trans (Eq.symm (hq 3)) (Eq.trans (congrArg q (Eq.symm (hit))) (hq 2))
    have t4 : v 15 = v 1 := Eq.trans (Eq.symm (hp 7)) (Eq.trans (congrArg p (Eq.trans (Eq.symm (h1)) (t3))) (hp 0))
    exact branch9 p q v hp sep (Eq.trans (t1) (Eq.symm (t2))) (Eq.trans (Eq.symm (t3)) (Eq.symm (t4))) (Eq.trans (Eq.symm (t3)) (h1))
  · have t0 : v 12 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 7)))) (Eq.trans (congrArg p.symm (Eq.symm (hit))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t1 : v 14 = v 4 := Eq.trans (Eq.symm (hq 5)) (Eq.trans (congrArg q (Eq.trans (Eq.symm (t0)) (Eq.symm (h1)))) (hq 1))
    have t2 : v 5 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.symm (h0))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t3 : v 1 = v 4 := Eq.trans (Eq.symm (hq 3)) (Eq.trans (congrArg q (Eq.trans (Eq.trans (t2) (Eq.symm (t0))) (Eq.symm (h1)))) (hq 1))
    have t4 : v 17 = v 10 := Eq.trans (Eq.symm (hp 9)) (Eq.trans (congrArg p (Eq.trans (Eq.trans (Eq.trans (Eq.trans (t1) (Eq.symm (t3))) (h1)) (t0)) (Eq.symm (t2)))) (hp 4))
    have t5 : v 11 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 6)))) (Eq.trans (congrArg p.symm (Eq.trans (Eq.trans (t2) (Eq.symm (t0))) (Eq.symm (h1)))) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    have t6 : v 17 = v 2 := Eq.trans (Eq.symm (hq 7)) (Eq.trans (congrArg q (t5)) (hq 0))
    have t7 : v 6 = v 4 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 1))
    have t8 : v 2 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 1)))) (Eq.trans (congrArg p.symm (Eq.trans (t7) (Eq.symm (t3)))) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    exact branch11 p q v hq sep (Eq.trans (Eq.trans (Eq.trans (Eq.trans (h0) (Eq.symm (t4))) (t6)) (t8)) (Eq.symm (t5))) (Eq.trans (Eq.trans (Eq.trans (Eq.trans (Eq.symm (t8)) (Eq.symm (t6))) (t4)) (Eq.symm (h0))) (hit)) (Eq.trans (Eq.trans (Eq.trans (Eq.symm (t8)) (Eq.symm (t6))) (t4)) (Eq.symm (h0)))
  · exact branch60 p q v hp hq sep G e₀ e₁ e₂ no (h0) (h1) (hit)
  · have t0 : v 7 = v 6 := Eq.trans (Eq.symm (hp 2)) (Eq.trans (congrArg p (hit)) (hp 1))
    have t1 : v 6 = v 4 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 1))
    exact branch59 p q v hp hq sep G e₀ e₁ e₂ no (h0) (h1) (Eq.trans (t0) (t1))
  · have t0 : v 5 = v 10 := Eq.trans (Eq.symm (hp 6)) (Eq.trans (congrArg p (Eq.symm (hit))) (hp 4))
    have t1 : v 1 = v 0 := Eq.trans (Eq.symm (hq 3)) (Eq.trans (congrArg q (Eq.trans (t0) (Eq.symm (h0)))) (hq 2))
    have t2 : v 15 = v 1 := Eq.trans (Eq.symm (hp 7)) (Eq.trans (congrArg p (Eq.trans (Eq.symm (h1)) (t1))) (hp 0))
    exact branch9 p q v hp sep (Eq.trans (Eq.trans (h0) (Eq.symm (t0))) (hit)) (Eq.trans (Eq.symm (t1)) (Eq.symm (t2))) (Eq.trans (Eq.symm (t1)) (h1))
  · have t0 : v 1 = v 4 := Eq.trans (Eq.symm (hq 3)) (Eq.trans (congrArg q (hit)) (hq 1))
    have t1 : v 10 = v 9 := Eq.trans (Eq.symm (hp 4)) (Eq.trans (congrArg p (Eq.trans (hit) (t0))) (hp 3))
    have t2 : v 15 = v 10 := Eq.trans (Eq.symm (hp 7)) (Eq.trans (congrArg p (Eq.trans (Eq.symm (h1)) (Eq.symm (hit)))) (hp 4))
    have t3 : v 9 = v 0 := Eq.trans (Eq.symm (hq 9)) (Eq.trans (congrArg q (Eq.trans (t2) (Eq.symm (h0)))) (hq 2))
    have t4 : v 11 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 6)))) (Eq.trans (congrArg p.symm (hit)) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    exact branch11 p q v hq sep (Eq.trans (Eq.trans (Eq.trans (h0) (t1)) (t3)) (Eq.symm (t4))) (Eq.trans (Eq.trans (Eq.symm (t3)) (Eq.symm (t1))) (Eq.symm (t2))) (Eq.trans (Eq.trans (Eq.symm (t3)) (Eq.symm (t1))) (Eq.symm (h0)))
  · have t0 : v 10 = v 6 := Eq.trans (Eq.symm (hp 4)) (Eq.trans (congrArg p (hit)) (hp 1))
    have t1 : v 6 = v 4 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 1))
    exact branch60 p q v hp hq sep G e₀ e₁ e₂ no (h0) (h1) (Eq.trans (Eq.trans (h0) (t0)) (t1))
  · have t0 : v 12 = v 11 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 7)))) (Eq.trans (congrArg p.symm (Eq.symm (hit))) (p.symm_apply_eq.mpr (Eq.symm (hp 6))))
    have t1 : v 17 = v 4 := Eq.trans (Eq.symm (hq 7)) (Eq.trans (congrArg q (Eq.trans (Eq.symm (t0)) (Eq.symm (h1)))) (hq 1))
    have t2 : v 9 = v 1 := Eq.trans (Eq.symm (hq 9)) (Eq.trans (congrArg q (Eq.symm (hit))) (hq 3))
    have t3 : v 4 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 3)))) (Eq.trans (congrArg p.symm (t2)) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    have t4 : v 11 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 7)))) (Eq.trans (congrArg q.symm (Eq.trans (t1) (t3))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    have t5 : v 5 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.symm (h0))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t6 : v 14 = v 1 := Eq.trans (Eq.symm (hq 5)) (Eq.trans (congrArg q (Eq.symm (t5))) (hq 3))
    have t7 : v 17 = v 5 := Eq.trans (Eq.symm (hp 9)) (Eq.trans (congrArg p (Eq.trans (Eq.trans (t6) (h1)) (t0))) (hp 6))
    exact branch10 p q v hp hq sep (Eq.symm (t4)) (Eq.trans (Eq.trans (Eq.trans (Eq.symm (t3)) (Eq.symm (t1))) (t7)) (hit)) (Eq.trans (Eq.trans (Eq.trans (Eq.symm (t3)) (Eq.symm (t1))) (t7)) (t5))
  · exact branch61 p q v hq sep G e₀ e₁ e₂ no (h0) (h1) (hit)
  · have t0 : v 10 = v 6 := Eq.trans (Eq.symm (hp 4)) (Eq.trans (congrArg p (hit)) (hp 1))
    have t1 : v 6 = v 4 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 1))
    exact branch60 p q v hp hq sep G e₀ e₁ e₂ no (h0) (h1) (Eq.trans (Eq.trans (h0) (t0)) (t1))
  · have t0 : v 17 = v 4 := Eq.trans (Eq.symm (hq 7)) (Eq.trans (congrArg q (hit)) (hq 1))
    have t1 : v 15 = v 5 := Eq.trans (Eq.symm (hp 7)) (Eq.trans (congrArg p (Eq.trans (Eq.symm (h1)) (Eq.symm (hit)))) (hp 6))
    have t2 : v 9 = v 1 := Eq.trans (Eq.symm (hq 9)) (Eq.trans (congrArg q (t1)) (hq 3))
    have t3 : v 4 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 3)))) (Eq.trans (congrArg p.symm (t2)) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    have t4 : v 11 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 7)))) (Eq.trans (congrArg q.symm (Eq.trans (t0) (t3))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    have t5 : v 5 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.symm (h0))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t6 : v 14 = v 1 := Eq.trans (Eq.symm (hq 5)) (Eq.trans (congrArg q (Eq.symm (t5))) (hq 3))
    have t7 : v 17 = v 5 := Eq.trans (Eq.symm (hp 9)) (Eq.trans (congrArg p (Eq.trans (t6) (Eq.symm (hit)))) (hp 6))
    exact branch10 p q v hp hq sep (Eq.symm (t4)) (Eq.trans (Eq.trans (Eq.trans (Eq.symm (t3)) (Eq.symm (t0))) (t7)) (Eq.symm (t1))) (Eq.trans (Eq.trans (Eq.trans (Eq.symm (t3)) (Eq.symm (t0))) (t7)) (t5))
  · have t0 : v 5 = v 6 := Eq.trans (Eq.symm (hp 6)) (Eq.trans (congrArg p (hit)) (hp 1))
    have t1 : v 6 = v 4 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 1))
    exact branch61 p q v hq sep G e₀ e₁ e₂ no (h0) (h1) (Eq.trans (t0) (t1))
  · have t0 : v 6 = v 4 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 1))
    have t1 : v 12 = v 2 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 7)))) (Eq.trans (congrArg p.symm (Eq.trans (hit) (Eq.symm (t0)))) (p.symm_apply_eq.mpr (Eq.symm (hp 1))))
    have t2 : v 0 = v 5 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 0)))) (Eq.trans (congrArg q.symm (Eq.trans (Eq.symm (t1)) (Eq.symm (h1)))) (q.symm_apply_eq.mpr (Eq.symm (hq 3))))
    have t3 : v 10 = v 1 := Eq.trans (Eq.symm (hp 4)) (Eq.trans (congrArg p (Eq.symm (t2))) (hp 0))
    have t4 : v 5 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.symm (h0))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t5 : v 14 = v 1 := Eq.trans (Eq.symm (hq 5)) (Eq.trans (congrArg q (Eq.symm (t4))) (hq 3))
    have t6 : v 17 = v 15 := Eq.trans (Eq.symm (hp 9)) (Eq.trans (congrArg p (Eq.trans (t5) (h1))) (hp 7))
    have t7 : v 11 = v 1 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 7)))) (Eq.trans (congrArg q.symm (Eq.trans (t6) (hit))) (q.symm_apply_eq.mpr (Eq.symm (hq 1))))
    have t8 : v 16 = v 0 := Eq.trans (Eq.symm (hq 6)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
    have t9 : v 16 = v 4 := Eq.trans (Eq.symm (hq 6)) (Eq.trans (congrArg q (t3)) (hq 1))
    exact branch10 p q v hp hq sep (Eq.trans (Eq.trans (h0) (t3)) (Eq.symm (t7))) (Eq.trans (Eq.trans (Eq.symm (t8)) (t9)) (Eq.symm (hit))) (Eq.trans (t2) (t4))
  · have t0 : v 5 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.symm (h0))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t1 : v 14 = v 1 := Eq.trans (Eq.symm (hq 5)) (Eq.trans (congrArg q (Eq.symm (t0))) (hq 3))
    have t2 : v 17 = v 15 := Eq.trans (Eq.symm (hp 9)) (Eq.trans (congrArg p (Eq.trans (t1) (h1))) (hp 7))
    have t3 : v 11 = v 0 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 7)))) (Eq.trans (congrArg q.symm (Eq.trans (t2) (hit))) (q.symm_apply_eq.mpr (Eq.symm (hq 0))))
    have t4 : v 5 = v 1 := Eq.trans (Eq.symm (hp 6)) (Eq.trans (congrArg p (t3)) (hp 0))
    have t5 : v 15 = v 10 := Eq.trans (Eq.symm (hp 7)) (Eq.trans (congrArg p (Eq.trans (Eq.symm (h1)) (Eq.symm (t4)))) (hp 4))
    have t6 : v 6 = v 4 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 1))
    have t7 : v 1 = v 4 := Eq.trans (Eq.symm (hq 3)) (Eq.trans (congrArg q (t4)) (hq 1))
    have t8 : v 2 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 1)))) (Eq.trans (congrArg p.symm (Eq.trans (t6) (Eq.symm (t7)))) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    exact branch11 p q v hq sep (Eq.trans (Eq.trans (Eq.trans (Eq.trans (h0) (Eq.symm (t5))) (hit)) (t8)) (Eq.symm (t3))) (Eq.trans (Eq.symm (t8)) (Eq.symm (hit))) (Eq.trans (Eq.trans (Eq.trans (Eq.symm (t8)) (Eq.symm (hit))) (t5)) (Eq.symm (h0)))
  · have t0 : v 0 = v 5 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 0)))) (Eq.trans (congrArg q.symm (Eq.symm (hit))) (q.symm_apply_eq.mpr (Eq.symm (hq 3))))
    have t1 : v 10 = v 1 := Eq.trans (Eq.symm (hp 4)) (Eq.trans (congrArg p (Eq.symm (t0))) (hp 0))
    have t2 : v 6 = v 4 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 1))
    have t3 : v 0 = v 4 := Eq.trans (Eq.symm (hq 2)) (Eq.trans (congrArg q (Eq.trans (h0) (t1))) (hq 1))
    have t4 : v 2 = v 11 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 1)))) (Eq.trans (congrArg p.symm (Eq.trans (Eq.trans (t2) (Eq.symm (t3))) (t0))) (p.symm_apply_eq.mpr (Eq.symm (hp 6))))
    have t5 : v 15 = v 6 := Eq.trans (Eq.symm (hp 7)) (Eq.trans (congrArg p (Eq.trans (Eq.symm (h1)) (hit))) (hp 1))
    have t6 : v 8 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 5)))) (Eq.trans (congrArg p.symm (Eq.trans (h0) (t1))) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    exact branch10 p q v hp hq sep (Eq.trans (Eq.trans (Eq.trans (h0) (t1)) (hit)) (t4)) (Eq.trans (Eq.trans (t3) (Eq.symm (t2))) (Eq.symm (t5))) (Eq.symm (t6))
  · have t0 : v 1 = v 0 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 1)))) (Eq.trans (congrArg q.symm (hit)) (q.symm_apply_eq.mpr (Eq.symm (hq 0))))
    have t1 : v 5 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 3)))) (Eq.trans (congrArg q.symm (t0)) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    have t2 : v 5 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.symm (h0))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t3 : v 11 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 6)))) (Eq.trans (congrArg p.symm (t1)) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t4 : v 9 = v 6 := Eq.trans (Eq.symm (hp 3)) (Eq.trans (congrArg p (hit)) (hp 1))
    have t5 : v 15 = v 12 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 9)))) (Eq.trans (congrArg q.symm (t4)) (q.symm_apply_eq.mpr (Eq.symm (hq 8))))
    exact branch9 p q v hp sep (Eq.trans (Eq.trans (Eq.symm (t1)) (t2)) (Eq.symm (t3))) (Eq.trans (Eq.trans (Eq.symm (t0)) (h1)) (Eq.symm (t5))) (Eq.trans (Eq.symm (t0)) (h1))

include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch20 (h0 : v 3 = v 11) (h1 : v 3 = v 4) : False := by
  have t0 : v 17 = v 0 := Eq.trans (Eq.symm (hq 7)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
  exact short8 p q G sep e₀ e₁ e₂ no ![0,1,0,2,1,2,0,1] (by decide)
    (v 0) (v 0) (v 14) (v 14) (v 8) (v 3) (v 1) (v 1)
    (rfl) (Eq.trans (hp 9) (t0)) (rfl) (hq 5) (hp 5) (Eq.trans (hq 1) (Eq.symm (h1))) (rfl) (hp 0)

include p q v hq sep G e₀ e₁ e₂ no in
private theorem branch21 (_h0 : v 3 = v 11) (h1 : v 3 = v 2) : False := by
  exact short4 p q G sep e₀ e₁ e₂ no ![0,2,0,2] (by decide)
    (v 0) (v 0) (v 2) (v 2)
    (rfl) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 2)) (rfl) (hq 0)

include p q v hq sep G e₀ e₁ e₂ no in
private theorem branch22 (_h0 : v 3 = v 11) (h1 : v 5 = v 4) : False := by
  exact short4 p q G sep e₀ e₁ e₂ no ![0,2,0,2] (by decide)
    (v 1) (v 1) (v 4) (v 4)
    (rfl) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 3)) (rfl) (hq 1)

include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch23 (h0 : v 3 = v 11) (h1 : v 5 = v 2) : False := by
  have t0 : v 5 = v 7 := Eq.trans (Eq.symm (hp 6)) (Eq.trans (congrArg p (Eq.symm (h0))) (hp 2))
  exact short4 p q G sep e₀ e₁ e₂ no ![0,2,1,2] (by decide)
    (v 0) (v 0) (v 3) (v 2)
    (rfl) (hq 2) (Eq.trans (hp 2) (Eq.trans (Eq.symm (t0)) (h1))) (hq 0)

include p q v hp hq sep in
private theorem branch33 (_h0 : v 3 = v 11) (h1 : v 4 = v 12) : False := by
  have t0 : v 15 = v 9 := Eq.trans (Eq.symm (hp 7)) (Eq.trans (congrArg p (Eq.symm (h1))) (hp 3))
  exact (sep (v 9)).2.1 (Eq.trans (congrArg q (Eq.symm (t0))) (hq 9))

include p q v hp hq sep in
private theorem branch35 (_h0 : v 3 = v 11) (h1 : v 15 = v 6) : False := by
  have t0 : v 12 = v 2 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 7)))) (Eq.trans (congrArg p.symm (h1)) (p.symm_apply_eq.mpr (Eq.symm (hp 1))))
  exact (sep (v 2)).2.2 (Eq.trans (hp 1) (Eq.symm (Eq.trans (congrArg q (Eq.symm (t0))) (hq 8))))

include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch51 (h0 : v 3 = v 10) (h1 : v 3 = v 4) : False := by
  exact short4 p q G sep e₀ e₁ e₂ no ![0,2,1,2] (by decide)
    (v 1) (v 1) (v 5) (v 3)
    (rfl) (hq 3) (Eq.trans (hp 4) (Eq.symm (h0))) (Eq.trans (hq 1) (Eq.symm (h1)))

include p q v hq sep G e₀ e₁ e₂ no in
private theorem branch52 (_h0 : v 3 = v 10) (h1 : v 3 = v 2) : False := by
  exact short4 p q G sep e₀ e₁ e₂ no ![0,2,0,2] (by decide)
    (v 0) (v 0) (v 2) (v 2)
    (rfl) (Eq.trans (congrArg q (Eq.symm (h1))) (hq 2)) (rfl) (hq 0)

include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch53 (h0 : v 3 = v 10) (h1 : v 3 = v 9) : False := by
  have t0 : v 4 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 3)))) (Eq.trans (congrArg p.symm (Eq.symm (h1))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
  have t1 : v 5 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.symm (h0))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
  exact short4 p q G sep e₀ e₁ e₂ no ![0,2,0,2] (by decide)
    (v 1) (v 1) (v 4) (v 4)
    (rfl) (Eq.trans (congrArg q (Eq.trans (t0) (Eq.symm (t1)))) (hq 3)) (rfl) (hq 1)

include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch54 (h0 : v 3 = v 10) (h1 : v 3 = v 6) : False := by
  have t0 : v 2 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 1)))) (Eq.trans (congrArg p.symm (Eq.symm (h1))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
  have t1 : v 5 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.symm (h0))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
  exact short4 p q G sep e₀ e₁ e₂ no ![1,2,0,2] (by decide)
    (v 0) (v 1) (v 2) (v 2)
    (hp 0) (Eq.trans (congrArg q (Eq.trans (t0) (Eq.symm (t1)))) (hq 3)) (rfl) (hq 0)

include p q v hp hq sep in
private theorem branch63 (_h0 : v 3 = v 10) (h1 : v 4 = v 12) : False := by
  have t0 : v 15 = v 9 := Eq.trans (Eq.symm (hp 7)) (Eq.trans (congrArg p (Eq.symm (h1))) (hp 3))
  exact (sep (v 9)).2.1 (Eq.trans (congrArg q (Eq.symm (t0))) (hq 9))

include p q v hp hq sep in
private theorem branch65 (_h0 : v 3 = v 10) (h1 : v 15 = v 6) : False := by
  have t0 : v 12 = v 2 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 7)))) (Eq.trans (congrArg p.symm (h1)) (p.symm_apply_eq.mpr (Eq.symm (hp 1))))
  exact (sep (v 2)).2.2 (Eq.trans (hp 1) (Eq.symm (Eq.trans (congrArg q (Eq.symm (t0))) (hq 8))))

include p q v hp hq sep in
private theorem branch32 (_h0 : v 3 = v 11) (h1 : v 4 = v 15) : False := by
  exact (sep (v 4)).2.2 (Eq.trans (hp 3) (Eq.symm (Eq.trans (congrArg q (h1)) (hq 9))))

include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch34 (_h0 : v 3 = v 11) (h1 : v 15 = v 2) : False := by
  exact short4 p q G sep e₀ e₁ e₂ no ![0,1,2,1] (by decide)
    (v 2) (v 2) (v 12) (v 6)
    (rfl) (Eq.trans (hp 7) (h1)) (hq 8) (hp 1)

include p q v hp hq sep in
private theorem branch62 (_h0 : v 3 = v 10) (h1 : v 4 = v 15) : False := by
  exact (sep (v 4)).2.2 (Eq.trans (hp 3) (Eq.symm (Eq.trans (congrArg q (h1)) (hq 9))))

include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch64 (_h0 : v 3 = v 10) (h1 : v 15 = v 2) : False := by
  exact short4 p q G sep e₀ e₁ e₂ no ![0,1,2,1] (by decide)
    (v 2) (v 2) (v 12) (v 6)
    (rfl) (Eq.trans (hp 7) (h1)) (hq 8) (hp 1)

include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch3 (h0 : v 3 = v 11) : False := by
  have t0 : v 5 = v 7 := Eq.trans (Eq.symm (hp 6)) (Eq.trans (congrArg p (Eq.symm (h0))) (hp 2))
  rcases collision16 (fun h => no (.inr (.inr h)))
    (v 0) (v 0) (v 3) (v 5) (v 5) (v 1) (v 1) (v 4) (v 4) (v 9) (v 15) (v 15) (v 12) (v 6) (v 2) (v 2)
    (e₀ (v 0))
    ((hq 2) ▸ e₂ (v 3))
    ((Eq.trans (hp 2) (Eq.symm (t0))) ▸ e₁ (v 3))
    (e₀ (v 5))
    ((hq 3) ▸ e₂ (v 5))
    (e₀ (v 1))
    ((hq 1) ▸ e₂ (v 1))
    (e₀ (v 4))
    ((hp 3) ▸ e₁ (v 4))
    ((hq 9) ▸ e₂ (v 15))
    (e₀ (v 15))
    ((hp 7) ▸ e₁ (v 12))
    ((hq 8) ▸ e₂ (v 12))
    ((hp 1) ▸ e₁ (v 2))
    (e₀ (v 2))
    ((hq 0) ▸ e₂ (v 0)) with hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit
  · exact branch4 p q v hq sep (h0) (hit)
  · exact branch5 p q v hp hq sep (h0) (hit)
  · exact branch6 p q v hp sep (h0) (hit)
  · exact branch7 p q v hp hq sep G e₀ e₁ e₂ no (h0) (hit)
  · exact branch8 p q v hp hq sep G e₀ e₁ e₂ no (h0) (hit)
  · exact branch18 p q v hp hq sep (h0) (hit)
  · have t0 : v 0 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 0)))) (Eq.trans (congrArg q.symm (Eq.symm (hit))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    exact branch4 p q v hq sep (h0) (t0)
  · exact branch5 p q v hp hq sep (h0) (hit)
  · exact branch6 p q v hp sep (h0) (hit)
  · exact branch7 p q v hp hq sep G e₀ e₁ e₂ no (h0) (hit)
  · exact branch19 p q v hp hq sep G e₀ e₁ e₂ no (h0) (hit)
  · exact branch8 p q v hp hq sep G e₀ e₁ e₂ no (h0) (hit)
  · have t0 : v 12 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 8)))) (Eq.trans (congrArg q.symm (Eq.symm (hit))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    have t1 : v 15 = v 7 := Eq.trans (Eq.symm (hp 7)) (Eq.trans (congrArg p (t0)) (hp 2))
    have t2 : v 5 = v 7 := Eq.trans (Eq.symm (hp 6)) (Eq.trans (congrArg p (Eq.symm (h0))) (hp 2))
    have t3 : v 9 = v 1 := Eq.trans (Eq.symm (hq 9)) (Eq.trans (congrArg q (Eq.trans (t1) (Eq.symm (t2)))) (hq 3))
    have t4 : v 4 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 3)))) (Eq.trans (congrArg p.symm (t3)) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    exact branch7 p q v hp hq sep G e₀ e₁ e₂ no (h0) (Eq.symm (t4))
  · have t0 : v 0 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 0)))) (Eq.trans (congrArg q.symm (Eq.symm (hit))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    exact branch4 p q v hq sep (h0) (t0)
  · have t0 : v 1 = v 0 := Eq.trans (Eq.symm (hq 3)) (Eq.trans (congrArg q (Eq.symm (hit))) (hq 2))
    exact branch6 p q v hp sep (h0) (Eq.symm (t0))
  · have t0 : v 0 = v 4 := Eq.trans (Eq.symm (hq 2)) (Eq.trans (congrArg q (hit)) (hq 1))
    exact branch7 p q v hp hq sep G e₀ e₁ e₂ no (h0) (t0)
  · exact branch20 p q v hp hq sep G e₀ e₁ e₂ no (h0) (hit)
  · have t0 : v 9 = v 0 := Eq.trans (Eq.symm (hq 9)) (Eq.trans (congrArg q (Eq.symm (hit))) (hq 2))
    exact branch19 p q v hp hq sep G e₀ e₁ e₂ no (h0) (Eq.symm (t0))
  · have t0 : v 15 = v 7 := Eq.trans (Eq.symm (hp 7)) (Eq.trans (congrArg p (Eq.symm (hit))) (hp 2))
    have t1 : v 5 = v 7 := Eq.trans (Eq.symm (hp 6)) (Eq.trans (congrArg p (Eq.symm (h0))) (hp 2))
    have t2 : v 9 = v 1 := Eq.trans (Eq.symm (hq 9)) (Eq.trans (congrArg q (Eq.trans (t0) (Eq.symm (t1)))) (hq 3))
    have t3 : v 4 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 3)))) (Eq.trans (congrArg p.symm (t2)) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    exact branch7 p q v hp hq sep G e₀ e₁ e₂ no (h0) (Eq.symm (t3))
  · exact branch21 p q v hq sep G e₀ e₁ e₂ no (h0) (hit)
  · have t0 : v 11 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 6)))) (Eq.trans (congrArg p.symm (hit)) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    exact branch4 p q v hq sep (h0) (Eq.trans (Eq.symm (t0)) (Eq.symm (h0)))
  · exact branch22 p q v hq sep G e₀ e₁ e₂ no (h0) (hit)
  · have t0 : v 4 = v 11 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 3)))) (Eq.trans (congrArg p.symm (Eq.symm (hit))) (p.symm_apply_eq.mpr (Eq.symm (hp 6))))
    exact branch20 p q v hp hq sep G e₀ e₁ e₂ no (h0) (Eq.trans (h0) (Eq.symm (t0)))
  · have t0 : v 9 = v 1 := Eq.trans (Eq.symm (hq 9)) (Eq.trans (congrArg q (Eq.symm (hit))) (hq 3))
    have t1 : v 4 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 3)))) (Eq.trans (congrArg p.symm (t0)) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    exact branch7 p q v hp hq sep G e₀ e₁ e₂ no (h0) (Eq.symm (t1))
  · have t0 : v 2 = v 11 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 1)))) (Eq.trans (congrArg p.symm (Eq.symm (hit))) (p.symm_apply_eq.mpr (Eq.symm (hp 6))))
    exact branch21 p q v hq sep G e₀ e₁ e₂ no (h0) (Eq.trans (h0) (Eq.symm (t0)))
  · exact branch23 p q v hp hq sep G e₀ e₁ e₂ no (h0) (hit)
  · have t0 : v 11 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 6)))) (Eq.trans (congrArg p.symm (hit)) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    exact branch4 p q v hq sep (h0) (Eq.trans (Eq.symm (t0)) (Eq.symm (h0)))
  · exact branch22 p q v hq sep G e₀ e₁ e₂ no (h0) (hit)
  · have t0 : v 9 = v 1 := Eq.trans (Eq.symm (hq 9)) (Eq.trans (congrArg q (Eq.symm (hit))) (hq 3))
    have t1 : v 4 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 3)))) (Eq.trans (congrArg p.symm (t0)) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    exact branch7 p q v hp hq sep G e₀ e₁ e₂ no (h0) (Eq.symm (t1))
  · have t0 : v 6 = v 1 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (Eq.symm (hit))) (hq 3))
    have t1 : v 2 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 1)))) (Eq.trans (congrArg p.symm (t0)) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    have t2 : v 0 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 0)))) (Eq.trans (congrArg q.symm (t1)) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    exact branch4 p q v hq sep (h0) (t2)
  · exact branch23 p q v hp hq sep G e₀ e₁ e₂ no (h0) (hit)
  · have t0 : v 1 = v 5 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 1)))) (Eq.trans (congrArg q.symm (Eq.symm (hit))) (q.symm_apply_eq.mpr (Eq.symm (hq 3))))
    have t1 : v 11 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 6)))) (Eq.trans (congrArg p.symm (Eq.symm (t0))) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    exact branch4 p q v hq sep (h0) (Eq.trans (Eq.symm (t1)) (Eq.symm (h0)))
  · have t0 : v 4 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 3)))) (Eq.trans (congrArg p.symm (Eq.symm (hit))) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    exact branch7 p q v hp hq sep G e₀ e₁ e₂ no (h0) (Eq.symm (t0))
  · have t0 : v 12 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 7)))) (Eq.trans (congrArg p.symm (Eq.symm (hit))) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    exact branch18 p q v hp hq sep (h0) (Eq.symm (t0))
  · have t0 : v 2 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 1)))) (Eq.trans (congrArg p.symm (Eq.symm (hit))) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    have t1 : v 0 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 0)))) (Eq.trans (congrArg q.symm (t0)) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    exact branch4 p q v hq sep (h0) (t1)
  · have t0 : v 0 = v 5 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 0)))) (Eq.trans (congrArg q.symm (Eq.symm (hit))) (q.symm_apply_eq.mpr (Eq.symm (hq 3))))
    exact branch5 p q v hp hq sep (h0) (t0)
  · have t0 : v 1 = v 5 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 1)))) (Eq.trans (congrArg q.symm (Eq.symm (hit))) (q.symm_apply_eq.mpr (Eq.symm (hq 3))))
    have t1 : v 11 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 6)))) (Eq.trans (congrArg p.symm (Eq.symm (t0))) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    exact branch4 p q v hq sep (h0) (Eq.trans (Eq.symm (t1)) (Eq.symm (h0)))
  · have t0 : v 12 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 7)))) (Eq.trans (congrArg p.symm (Eq.symm (hit))) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    exact branch18 p q v hp hq sep (h0) (Eq.symm (t0))
  · exact branch24 p q v hp hq sep G e₀ e₁ e₂ no (h0) (hit)
  · have t0 : v 0 = v 5 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 0)))) (Eq.trans (congrArg q.symm (Eq.symm (hit))) (q.symm_apply_eq.mpr (Eq.symm (hq 3))))
    exact branch5 p q v hp hq sep (h0) (t0)
  · have t0 : v 15 = v 1 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 9)))) (Eq.trans (congrArg q.symm (Eq.symm (hit))) (q.symm_apply_eq.mpr (Eq.symm (hq 1))))
    have t1 : v 12 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 7)))) (Eq.trans (congrArg p.symm (t0)) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    exact branch18 p q v hp hq sep (h0) (Eq.symm (t1))
  · exact branch32 p q v hp hq sep (h0) (hit)
  · have t0 : v 12 = v 1 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 8)))) (Eq.trans (congrArg q.symm (Eq.symm (hit))) (q.symm_apply_eq.mpr (Eq.symm (hq 1))))
    exact branch24 p q v hp hq sep G e₀ e₁ e₂ no (h0) (Eq.symm (t0))
  · have t0 : v 1 = v 0 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 1)))) (Eq.trans (congrArg q.symm (hit)) (q.symm_apply_eq.mpr (Eq.symm (hq 0))))
    exact branch6 p q v hp sep (h0) (Eq.symm (t0))
  · exact branch32 p q v hp hq sep (h0) (hit)
  · exact branch33 p q v hp hq sep (h0) (hit)
  · have t0 : v 1 = v 0 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 1)))) (Eq.trans (congrArg q.symm (hit)) (q.symm_apply_eq.mpr (Eq.symm (hq 0))))
    exact branch6 p q v hp sep (h0) (Eq.symm (t0))
  · have t0 : v 12 = v 4 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 7)))) (Eq.trans (congrArg p.symm (Eq.symm (hit))) (p.symm_apply_eq.mpr (Eq.symm (hp 3))))
    exact branch33 p q v hp hq sep (h0) (Eq.symm (t0))
  · have t0 : v 4 = v 2 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 3)))) (Eq.trans (congrArg p.symm (hit)) (p.symm_apply_eq.mpr (Eq.symm (hp 1))))
    have t1 : v 1 = v 0 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 1)))) (Eq.trans (congrArg q.symm (t0)) (q.symm_apply_eq.mpr (Eq.symm (hq 0))))
    exact branch6 p q v hp sep (h0) (Eq.symm (t1))
  · have t0 : v 15 = v 0 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 9)))) (Eq.trans (congrArg q.symm (hit)) (q.symm_apply_eq.mpr (Eq.symm (hq 0))))
    exact branch8 p q v hp hq sep G e₀ e₁ e₂ no (h0) (Eq.symm (t0))
  · have t0 : v 9 = v 6 := Eq.trans (Eq.symm (hq 9)) (Eq.trans (congrArg q (hit)) (hq 8))
    have t1 : v 4 = v 2 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 3)))) (Eq.trans (congrArg p.symm (t0)) (p.symm_apply_eq.mpr (Eq.symm (hp 1))))
    have t2 : v 1 = v 0 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 1)))) (Eq.trans (congrArg q.symm (t1)) (q.symm_apply_eq.mpr (Eq.symm (hq 0))))
    exact branch6 p q v hp sep (h0) (Eq.symm (t2))
  · exact branch34 p q v hp hq sep G e₀ e₁ e₂ no (h0) (hit)
  · exact branch35 p q v hp hq sep (h0) (hit)
  · exact branch34 p q v hp hq sep G e₀ e₁ e₂ no (h0) (hit)
  · have t0 : v 15 = v 6 := Eq.trans (Eq.symm (hp 7)) (Eq.trans (congrArg p (hit)) (hp 1))
    exact branch35 p q v hp hq sep (h0) (t0)
  · have t0 : v 12 = v 0 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 8)))) (Eq.trans (congrArg q.symm (hit)) (q.symm_apply_eq.mpr (Eq.symm (hq 0))))
    exact branch18 p q v hp hq sep (h0) (Eq.symm (t0))

include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch37 (h0 : v 3 = v 10) : False := by
  rcases collision16 (fun h => no (.inr (.inr h)))
    (v 0) (v 0) (v 3) (v 3) (v 5) (v 1) (v 1) (v 4) (v 4) (v 9) (v 15) (v 15) (v 12) (v 6) (v 2) (v 2)
    (e₀ (v 0))
    ((hq 2) ▸ e₂ (v 3))
    (e₀ (v 3))
    ((Eq.trans (hp 4) (Eq.symm (h0))) ▸ e₁ (v 5))
    ((hq 3) ▸ e₂ (v 5))
    (e₀ (v 1))
    ((hq 1) ▸ e₂ (v 1))
    (e₀ (v 4))
    ((hp 3) ▸ e₁ (v 4))
    ((hq 9) ▸ e₂ (v 15))
    (e₀ (v 15))
    ((hp 7) ▸ e₁ (v 12))
    ((hq 8) ▸ e₂ (v 12))
    ((hp 1) ▸ e₁ (v 2))
    (e₀ (v 2))
    ((hq 0) ▸ e₂ (v 0)) with hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit
  · exact branch38 p q v hq sep (h0) (hit)
  · exact branch39 p q v hp hq sep (h0) (hit)
  · have t0 : v 5 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 3)))) (Eq.trans (congrArg q.symm (Eq.symm (hit))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    have t1 : v 10 = v 7 := Eq.trans (Eq.symm (hp 4)) (Eq.trans (congrArg p (t0)) (hp 2))
    have t2 : v 3 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 2)))) (Eq.trans (congrArg p.symm (Eq.trans (Eq.symm (t1)) (Eq.symm (h0)))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t3 : v 11 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 6)))) (Eq.trans (congrArg p.symm (t0)) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    exact branch6 p q v hp sep (Eq.trans (t2) (Eq.symm (t3))) (hit)
  · have t0 : v 1 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 1)))) (Eq.trans (congrArg q.symm (Eq.symm (hit))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    have t1 : v 5 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.trans (Eq.symm (h0)) (Eq.symm (t0)))) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    exact branch39 p q v hp hq sep (h0) (Eq.symm (t1))
  · exact branch40 p q v hp hq sep G e₀ e₁ e₂ no (h0) (hit)
  · exact branch50 p q v hp hq sep (h0) (hit)
  · have t0 : v 0 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 0)))) (Eq.trans (congrArg q.symm (Eq.symm (hit))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    exact branch38 p q v hq sep (h0) (t0)
  · exact branch38 p q v hq sep (h0) (hit)
  · have t0 : v 5 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 3)))) (Eq.trans (congrArg q.symm (Eq.symm (hit))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    have t1 : v 10 = v 7 := Eq.trans (Eq.symm (hp 4)) (Eq.trans (congrArg p (t0)) (hp 2))
    have t2 : v 3 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 2)))) (Eq.trans (congrArg p.symm (Eq.trans (Eq.symm (t1)) (Eq.symm (h0)))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t3 : v 11 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 6)))) (Eq.trans (congrArg p.symm (t0)) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    exact branch6 p q v hp sep (Eq.trans (t2) (Eq.symm (t3))) (hit)
  · have t0 : v 1 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 1)))) (Eq.trans (congrArg q.symm (Eq.symm (hit))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    have t1 : v 5 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.trans (Eq.symm (h0)) (Eq.symm (t0)))) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    exact branch39 p q v hp hq sep (h0) (Eq.symm (t1))
  · have t0 : v 16 = v 0 := Eq.trans (Eq.symm (hq 6)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
    have t1 : v 13 = v 4 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 8)))) (Eq.trans (congrArg p.symm (Eq.trans (t0) (hit))) (p.symm_apply_eq.mpr (Eq.symm (hp 3))))
    have t2 : v 7 = v 1 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 4)))) (Eq.trans (congrArg q.symm (t1)) (q.symm_apply_eq.mpr (Eq.symm (hq 1))))
    have t3 : v 3 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 2)))) (Eq.trans (congrArg p.symm (t2)) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    exact branch38 p q v hq sep (h0) (Eq.symm (t3))
  · exact branch40 p q v hp hq sep G e₀ e₁ e₂ no (h0) (hit)
  · have t0 : v 12 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 8)))) (Eq.trans (congrArg q.symm (Eq.symm (hit))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    have t1 : v 15 = v 7 := Eq.trans (Eq.symm (hp 7)) (Eq.trans (congrArg p (t0)) (hp 2))
    have t2 : v 9 = v 13 := Eq.trans (Eq.symm (hq 9)) (Eq.trans (congrArg q (t1)) (hq 4))
    have t3 : v 16 = v 0 := Eq.trans (Eq.symm (hq 6)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
    have t4 : v 13 = v 2 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 8)))) (Eq.trans (congrArg p.symm (Eq.trans (t3) (hit))) (p.symm_apply_eq.mpr (Eq.symm (hp 1))))
    have t5 : v 15 = v 0 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 9)))) (Eq.trans (congrArg q.symm (Eq.trans (t2) (t4))) (q.symm_apply_eq.mpr (Eq.symm (hq 0))))
    exact branch41 p q v hp hq sep (h0) (Eq.symm (t5)) (Eq.trans (Eq.symm (t5)) (t1))
  · have t0 : v 0 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 0)))) (Eq.trans (congrArg q.symm (Eq.symm (hit))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    exact branch38 p q v hq sep (h0) (t0)
  · have t0 : v 10 = v 7 := Eq.trans (Eq.symm (hp 4)) (Eq.trans (congrArg p (Eq.symm (hit))) (hp 2))
    have t1 : v 3 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 2)))) (Eq.trans (congrArg p.symm (Eq.trans (Eq.symm (t0)) (Eq.symm (h0)))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t2 : v 11 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 6)))) (Eq.trans (congrArg p.symm (Eq.symm (hit))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t3 : v 1 = v 0 := Eq.trans (Eq.symm (hq 3)) (Eq.trans (congrArg q (Eq.symm (hit))) (hq 2))
    exact branch6 p q v hp sep (Eq.trans (t1) (Eq.symm (t2))) (Eq.symm (t3))
  · have t0 : v 5 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.trans (Eq.symm (h0)) (hit))) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    exact branch39 p q v hp hq sep (h0) (Eq.symm (t0))
  · exact branch51 p q v hp hq sep G e₀ e₁ e₂ no (h0) (hit)
  · have t0 : v 12 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 7)))) (Eq.trans (congrArg p.symm (Eq.symm (hit))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t1 : v 5 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.symm (h0))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t2 : v 6 = v 1 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (Eq.trans (t0) (Eq.symm (t1)))) (hq 3))
    have t3 : v 2 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 1)))) (Eq.trans (congrArg p.symm (t2)) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    have t4 : v 0 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 0)))) (Eq.trans (congrArg q.symm (t3)) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    exact branch38 p q v hq sep (h0) (t4)
  · have t0 : v 15 = v 7 := Eq.trans (Eq.symm (hp 7)) (Eq.trans (congrArg p (Eq.symm (hit))) (hp 2))
    have t1 : v 9 = v 13 := Eq.trans (Eq.symm (hq 9)) (Eq.trans (congrArg q (t0)) (hq 4))
    have t2 : v 16 = v 0 := Eq.trans (Eq.symm (hq 6)) (Eq.trans (congrArg q (Eq.symm (h0))) (hq 2))
    have t3 : v 6 = v 0 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (Eq.symm (hit))) (hq 2))
    have t4 : v 13 = v 2 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 8)))) (Eq.trans (congrArg p.symm (Eq.trans (t2) (Eq.symm (t3)))) (p.symm_apply_eq.mpr (Eq.symm (hp 1))))
    have t5 : v 15 = v 0 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 9)))) (Eq.trans (congrArg q.symm (Eq.trans (t1) (t4))) (q.symm_apply_eq.mpr (Eq.symm (hq 0))))
    exact branch41 p q v hp hq sep (h0) (Eq.symm (t5)) (Eq.trans (Eq.symm (t5)) (t0))
  · exact branch52 p q v hq sep G e₀ e₁ e₂ no (h0) (hit)
  · have t0 : v 5 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.trans (Eq.symm (h0)) (hit))) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    exact branch39 p q v hp hq sep (h0) (Eq.symm (t0))
  · exact branch51 p q v hp hq sep G e₀ e₁ e₂ no (h0) (hit)
  · exact branch53 p q v hp hq sep G e₀ e₁ e₂ no (h0) (hit)
  · have t0 : v 12 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 7)))) (Eq.trans (congrArg p.symm (Eq.symm (hit))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t1 : v 5 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.symm (h0))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t2 : v 6 = v 1 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (Eq.trans (t0) (Eq.symm (t1)))) (hq 3))
    have t3 : v 2 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 1)))) (Eq.trans (congrArg p.symm (t2)) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    have t4 : v 0 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 0)))) (Eq.trans (congrArg q.symm (t3)) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    exact branch38 p q v hq sep (h0) (t4)
  · exact branch54 p q v hp hq sep G e₀ e₁ e₂ no (h0) (hit)
  · exact branch52 p q v hq sep G e₀ e₁ e₂ no (h0) (hit)
  · have t0 : v 5 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.symm (h0))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t1 : v 14 = v 4 := Eq.trans (Eq.symm (hq 5)) (Eq.trans (congrArg q (Eq.trans (Eq.symm (t0)) (hit))) (hq 1))
    have t2 : v 17 = v 9 := Eq.trans (Eq.symm (hp 9)) (Eq.trans (congrArg p (t1)) (hp 3))
    have t3 : v 11 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 6)))) (Eq.trans (congrArg p.symm (hit)) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    have t4 : v 17 = v 2 := Eq.trans (Eq.symm (hq 7)) (Eq.trans (congrArg q (t3)) (hq 0))
    have t5 : v 15 = v 0 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 9)))) (Eq.trans (congrArg q.symm (Eq.trans (Eq.symm (t2)) (t4))) (q.symm_apply_eq.mpr (Eq.symm (hq 0))))
    exact branch42 p q v hp hq sep (h0) (Eq.symm (t5)) (Eq.symm (t3))
  · have t0 : v 10 = v 9 := Eq.trans (Eq.symm (hp 4)) (Eq.trans (congrArg p (hit)) (hp 3))
    exact branch53 p q v hp hq sep G e₀ e₁ e₂ no (h0) (Eq.trans (h0) (t0))
  · have t0 : v 12 = v 11 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 7)))) (Eq.trans (congrArg p.symm (Eq.symm (hit))) (p.symm_apply_eq.mpr (Eq.symm (hp 6))))
    have t1 : v 6 = v 17 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (t0)) (hq 7))
    have t2 : v 14 = v 2 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 9)))) (Eq.trans (congrArg p.symm (Eq.symm (t1))) (p.symm_apply_eq.mpr (Eq.symm (hp 1))))
    have t3 : v 5 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.symm (h0))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t4 : v 14 = v 1 := Eq.trans (Eq.symm (hq 5)) (Eq.trans (congrArg q (Eq.symm (t3))) (hq 3))
    have t5 : v 0 = v 5 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 0)))) (Eq.trans (congrArg q.symm (Eq.trans (Eq.symm (t2)) (t4))) (q.symm_apply_eq.mpr (Eq.symm (hq 3))))
    exact branch39 p q v hp hq sep (h0) (t5)
  · have t0 : v 6 = v 1 := Eq.trans (Eq.symm (hq 8)) (Eq.trans (congrArg q (Eq.symm (hit))) (hq 3))
    have t1 : v 2 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 1)))) (Eq.trans (congrArg p.symm (t0)) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    have t2 : v 0 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 0)))) (Eq.trans (congrArg q.symm (t1)) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    exact branch38 p q v hq sep (h0) (t2)
  · have t0 : v 10 = v 6 := Eq.trans (Eq.symm (hp 4)) (Eq.trans (congrArg p (hit)) (hp 1))
    exact branch54 p q v hp hq sep G e₀ e₁ e₂ no (h0) (Eq.trans (h0) (t0))
  · have t0 : v 1 = v 5 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 1)))) (Eq.trans (congrArg q.symm (Eq.symm (hit))) (q.symm_apply_eq.mpr (Eq.symm (hq 3))))
    have t1 : v 10 = v 9 := Eq.trans (Eq.symm (hp 4)) (Eq.trans (congrArg p (Eq.trans (Eq.symm (t0)) (hit))) (hp 3))
    have t2 : v 4 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 3)))) (Eq.trans (congrArg p.symm (Eq.trans (Eq.symm (t1)) (Eq.symm (h0)))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t3 : v 14 = v 4 := Eq.trans (Eq.symm (hq 5)) (Eq.trans (congrArg q (Eq.trans (Eq.symm (t2)) (Eq.symm (hit)))) (hq 1))
    have t4 : v 17 = v 9 := Eq.trans (Eq.symm (hp 9)) (Eq.trans (congrArg p (t3)) (hp 3))
    have t5 : v 11 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 6)))) (Eq.trans (congrArg p.symm (Eq.symm (t0))) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    have t6 : v 17 = v 2 := Eq.trans (Eq.symm (hq 7)) (Eq.trans (congrArg q (t5)) (hq 0))
    have t7 : v 15 = v 0 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 9)))) (Eq.trans (congrArg q.symm (Eq.trans (Eq.symm (t4)) (t6))) (q.symm_apply_eq.mpr (Eq.symm (hq 0))))
    exact branch42 p q v hp hq sep (h0) (Eq.symm (t7)) (Eq.symm (t5))
  · have t0 : v 4 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 3)))) (Eq.trans (congrArg p.symm (Eq.symm (hit))) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    have t1 : v 1 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 1)))) (Eq.trans (congrArg q.symm (t0)) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    have t2 : v 5 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.trans (Eq.symm (h0)) (Eq.symm (t1)))) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    exact branch39 p q v hp hq sep (h0) (Eq.symm (t2))
  · have t0 : v 12 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 7)))) (Eq.trans (congrArg p.symm (Eq.symm (hit))) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    exact branch50 p q v hp hq sep (h0) (Eq.symm (t0))
  · have t0 : v 2 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 1)))) (Eq.trans (congrArg p.symm (Eq.symm (hit))) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    have t1 : v 0 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 0)))) (Eq.trans (congrArg q.symm (t0)) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    exact branch38 p q v hq sep (h0) (t1)
  · have t0 : v 0 = v 5 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 0)))) (Eq.trans (congrArg q.symm (Eq.symm (hit))) (q.symm_apply_eq.mpr (Eq.symm (hq 3))))
    exact branch39 p q v hp hq sep (h0) (t0)
  · have t0 : v 1 = v 5 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 1)))) (Eq.trans (congrArg q.symm (Eq.symm (hit))) (q.symm_apply_eq.mpr (Eq.symm (hq 3))))
    have t1 : v 10 = v 9 := Eq.trans (Eq.symm (hp 4)) (Eq.trans (congrArg p (Eq.trans (Eq.symm (t0)) (hit))) (hp 3))
    have t2 : v 4 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 3)))) (Eq.trans (congrArg p.symm (Eq.trans (Eq.symm (t1)) (Eq.symm (h0)))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t3 : v 14 = v 4 := Eq.trans (Eq.symm (hq 5)) (Eq.trans (congrArg q (Eq.trans (Eq.symm (t2)) (Eq.symm (hit)))) (hq 1))
    have t4 : v 17 = v 9 := Eq.trans (Eq.symm (hp 9)) (Eq.trans (congrArg p (t3)) (hp 3))
    have t5 : v 11 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 6)))) (Eq.trans (congrArg p.symm (Eq.symm (t0))) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    have t6 : v 17 = v 2 := Eq.trans (Eq.symm (hq 7)) (Eq.trans (congrArg q (t5)) (hq 0))
    have t7 : v 15 = v 0 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 9)))) (Eq.trans (congrArg q.symm (Eq.trans (Eq.symm (t4)) (t6))) (q.symm_apply_eq.mpr (Eq.symm (hq 0))))
    exact branch42 p q v hp hq sep (h0) (Eq.symm (t7)) (Eq.symm (t5))
  · have t0 : v 12 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 7)))) (Eq.trans (congrArg p.symm (Eq.symm (hit))) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    exact branch50 p q v hp hq sep (h0) (Eq.symm (t0))
  · exact branch55 p q v hp hq sep G e₀ e₁ e₂ no (h0) (hit)
  · have t0 : v 0 = v 5 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 0)))) (Eq.trans (congrArg q.symm (Eq.symm (hit))) (q.symm_apply_eq.mpr (Eq.symm (hq 3))))
    exact branch39 p q v hp hq sep (h0) (t0)
  · have t0 : v 15 = v 1 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 9)))) (Eq.trans (congrArg q.symm (Eq.symm (hit))) (q.symm_apply_eq.mpr (Eq.symm (hq 1))))
    have t1 : v 12 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 7)))) (Eq.trans (congrArg p.symm (t0)) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    exact branch50 p q v hp hq sep (h0) (Eq.symm (t1))
  · exact branch62 p q v hp hq sep (h0) (hit)
  · have t0 : v 12 = v 1 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 8)))) (Eq.trans (congrArg q.symm (Eq.symm (hit))) (q.symm_apply_eq.mpr (Eq.symm (hq 1))))
    exact branch55 p q v hp hq sep G e₀ e₁ e₂ no (h0) (Eq.symm (t0))
  · have t0 : v 1 = v 0 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 1)))) (Eq.trans (congrArg q.symm (hit)) (q.symm_apply_eq.mpr (Eq.symm (hq 0))))
    have t1 : v 5 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 3)))) (Eq.trans (congrArg q.symm (t0)) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    have t2 : v 5 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.symm (h0))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t3 : v 11 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 6)))) (Eq.trans (congrArg p.symm (t1)) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    exact branch6 p q v hp sep (Eq.trans (Eq.trans (Eq.symm (t1)) (t2)) (Eq.symm (t3))) (Eq.symm (t0))
  · exact branch62 p q v hp hq sep (h0) (hit)
  · exact branch63 p q v hp hq sep (h0) (hit)
  · have t0 : v 1 = v 0 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 1)))) (Eq.trans (congrArg q.symm (hit)) (q.symm_apply_eq.mpr (Eq.symm (hq 0))))
    have t1 : v 5 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 3)))) (Eq.trans (congrArg q.symm (t0)) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    have t2 : v 5 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.symm (h0))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t3 : v 11 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 6)))) (Eq.trans (congrArg p.symm (t1)) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    exact branch6 p q v hp sep (Eq.trans (Eq.trans (Eq.symm (t1)) (t2)) (Eq.symm (t3))) (Eq.symm (t0))
  · have t0 : v 12 = v 4 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 7)))) (Eq.trans (congrArg p.symm (Eq.symm (hit))) (p.symm_apply_eq.mpr (Eq.symm (hp 3))))
    exact branch63 p q v hp hq sep (h0) (Eq.symm (t0))
  · have t0 : v 5 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.symm (h0))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t1 : v 14 = v 1 := Eq.trans (Eq.symm (hq 5)) (Eq.trans (congrArg q (Eq.symm (t0))) (hq 3))
    have t2 : v 4 = v 2 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 3)))) (Eq.trans (congrArg p.symm (hit)) (p.symm_apply_eq.mpr (Eq.symm (hp 1))))
    have t3 : v 1 = v 0 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 1)))) (Eq.trans (congrArg q.symm (t2)) (q.symm_apply_eq.mpr (Eq.symm (hq 0))))
    have t4 : v 17 = v 1 := Eq.trans (Eq.symm (hp 9)) (Eq.trans (congrArg p (Eq.trans (t1) (t3))) (hp 0))
    have t5 : v 11 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 7)))) (Eq.trans (congrArg q.symm (Eq.trans (t4) (t3))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    exact branch6 p q v hp sep (Eq.symm (t5)) (Eq.symm (t3))
  · have t0 : v 15 = v 0 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 9)))) (Eq.trans (congrArg q.symm (hit)) (q.symm_apply_eq.mpr (Eq.symm (hq 0))))
    exact branch40 p q v hp hq sep G e₀ e₁ e₂ no (h0) (Eq.symm (t0))
  · have t0 : v 5 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.symm (h0))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    have t1 : v 14 = v 1 := Eq.trans (Eq.symm (hq 5)) (Eq.trans (congrArg q (Eq.symm (t0))) (hq 3))
    have t2 : v 9 = v 6 := Eq.trans (Eq.symm (hq 9)) (Eq.trans (congrArg q (hit)) (hq 8))
    have t3 : v 4 = v 2 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 3)))) (Eq.trans (congrArg p.symm (t2)) (p.symm_apply_eq.mpr (Eq.symm (hp 1))))
    have t4 : v 1 = v 0 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 1)))) (Eq.trans (congrArg q.symm (t3)) (q.symm_apply_eq.mpr (Eq.symm (hq 0))))
    have t5 : v 17 = v 1 := Eq.trans (Eq.symm (hp 9)) (Eq.trans (congrArg p (Eq.trans (t1) (t4))) (hp 0))
    have t6 : v 11 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 7)))) (Eq.trans (congrArg q.symm (Eq.trans (t5) (t4))) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    exact branch6 p q v hp sep (Eq.symm (t6)) (Eq.symm (t4))
  · exact branch64 p q v hp hq sep G e₀ e₁ e₂ no (h0) (hit)
  · exact branch65 p q v hp hq sep (h0) (hit)
  · exact branch64 p q v hp hq sep G e₀ e₁ e₂ no (h0) (hit)
  · have t0 : v 15 = v 6 := Eq.trans (Eq.symm (hp 7)) (Eq.trans (congrArg p (hit)) (hp 1))
    exact branch65 p q v hp hq sep (h0) (t0)
  · have t0 : v 12 = v 0 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 8)))) (Eq.trans (congrArg q.symm (hit)) (q.symm_apply_eq.mpr (Eq.symm (hq 0))))
    exact branch50 p q v hp hq sep (h0) (Eq.symm (t0))

include p q v hp sep G e₀ e₁ e₂ no in
private theorem branch70 (h0 : v 8 = v 7) : False := by
  exact short4 p q G sep e₀ e₁ e₂ no ![0,1,0,1] (by decide)
    (v 3) (v 3) (v 7) (v 7)
    (rfl) (Eq.trans (congrArg p (Eq.symm (h0))) (hp 5)) (rfl) (hp 2)

include p q v hp hq sep in
private theorem branch2 (h0 : v 3 = v 14) : False := by
  exact (sep (v 8)).2.2 (Eq.trans (hp 5) (Eq.symm (Eq.trans (hq 5) (Eq.symm (h0)))))

include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch66 (h0 : v 3 = v 13) : False := by
  exact short4 p q G sep e₀ e₁ e₂ no ![0,2,0,1] (by decide)
    (v 3) (v 3) (v 7) (v 7)
    (rfl) (Eq.trans (hq 4) (Eq.symm (h0))) (rfl) (hp 2)

include p q v hp hq sep in
private theorem branch67 (h0 : v 3 = v 17) : False := by
  have t0 : v 14 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 9)))) (Eq.trans (congrArg p.symm (Eq.symm (h0))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
  exact (sep (v 8)).2.1 (Eq.trans (hq 5) (t0))

include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch68 (h0 : v 3 = v 16) : False := by
  exact short8 p q G sep e₀ e₁ e₂ no ![0,2,0,2,0,1,2,1] (by decide)
    (v 0) (v 0) (v 3) (v 3) (v 10) (v 10) (v 5) (v 1)
    (rfl) (hq 2) (rfl) (Eq.trans (hq 6) (Eq.symm (h0))) (rfl) (hp 4) (hq 3) (hp 0)

include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch69 (h0 : v 8 = v 10) : False := by
  exact short8 p q G sep e₀ e₁ e₂ no ![0,2,0,1,0,1,2,1] (by decide)
    (v 0) (v 0) (v 3) (v 3) (v 8) (v 8) (v 5) (v 1)
    (rfl) (hq 2) (rfl) (hp 5) (rfl) (Eq.trans (hp 4) (Eq.symm (h0))) (hq 3) (hp 0)

include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch71 (h0 : v 14 = v 5) : False := by
  have t0 : v 17 = v 10 := Eq.trans (Eq.symm (hp 9)) (Eq.trans (congrArg p (h0)) (hp 4))
  exact short4 p q G sep e₀ e₁ e₂ no ![0,1,2,1] (by decide)
    (v 5) (v 5) (v 11) (v 10)
    (rfl) (hp 6) (Eq.trans (hq 7) (t0)) (hp 4)

include p q v hp hq sep in
private theorem branch74 (h0 : v 14 = v 11) : False := by
  have t0 : v 17 = v 5 := Eq.trans (Eq.symm (hp 9)) (Eq.trans (congrArg p (h0)) (hp 6))
  exact (sep (v 11)).2.2 (Eq.trans (hp 6) (Eq.symm (Eq.trans (hq 7) (t0))))

include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch75 (h0 : v 17 = v 13) : False := by
  have t0 : v 11 = v 7 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 7)))) (Eq.trans (congrArg q.symm (h0)) (q.symm_apply_eq.mpr (Eq.symm (hq 4))))
  exact short8 p q G sep e₀ e₁ e₂ no ![0,2,1,0,1,0,2,1] (by decide)
    (v 0) (v 0) (v 3) (v 7) (v 7) (v 5) (v 5) (v 1)
    (rfl) (hq 2) (hp 2) (rfl) (Eq.trans (congrArg p (Eq.symm (t0))) (hp 6)) (rfl) (hq 3) (hp 0)

include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch76 (h0 : v 11 = v 13) : False := by
  have t0 : v 16 = v 5 := Eq.trans (Eq.symm (hp 8)) (Eq.trans (congrArg p (Eq.symm (h0))) (hp 6))
  exact short4 p q G sep e₀ e₁ e₂ no ![0,2,0,1] (by decide)
    (v 5) (v 5) (v 10) (v 10)
    (rfl) (Eq.trans (hq 6) (t0)) (rfl) (hp 4)

include p q v hp hq sep in
private theorem branch77 (h0 : v 5 = v 13) : False := by
  have t0 : v 16 = v 10 := Eq.trans (Eq.symm (hp 8)) (Eq.trans (congrArg p (Eq.symm (h0))) (hp 4))
  exact (sep (v 10)).2.1 (Eq.trans (hq 6) (t0))

include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch72 (h0 : v 14 = v 10) : False := by
  exact short8 p q G sep e₀ e₁ e₂ no ![0,2,0,1,2,1,2,1] (by decide)
    (v 0) (v 0) (v 3) (v 3) (v 8) (v 10) (v 5) (v 1)
    (rfl) (hq 2) (rfl) (hp 5) (Eq.trans (hq 5) (h0)) (hp 4) (hq 3) (hp 0)

include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch73 (h0 : v 14 = v 7) : False := by
  exact short4 p q G sep e₀ e₁ e₂ no ![0,1,2,1] (by decide)
    (v 3) (v 3) (v 8) (v 7)
    (rfl) (hp 5) (Eq.trans (hq 5) (h0)) (hp 2)

include p q v hp hq sep in
private theorem branch78 (h0 : v 10 = v 13) : False := by
  exact (sep (v 10)).2.2 (Eq.trans (Eq.trans (congrArg p (h0)) (hp 8)) (Eq.symm (hq 6)))

include p q v hq sep in
private theorem branch79 (h0 : v 13 = v 7) : False := by
  exact (sep (v 7)).2.1 (Eq.trans (hq 4) (h0))

include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch0 : False := by
  rcases collision16 (fun h => no (.inr (.inr h)))
    (v 3) (v 3) (v 8) (v 14) (v 14) (v 17) (v 11) (v 5) (v 5) (v 10) (v 10) (v 16) (v 13) (v 13) (v 7) (v 7)
    (e₀ (v 3))
    ((hp 5) ▸ e₁ (v 8))
    ((hq 5) ▸ e₂ (v 8))
    (e₀ (v 14))
    ((hp 9) ▸ e₁ (v 14))
    ((hq 7) ▸ e₂ (v 11))
    ((hp 6) ▸ e₁ (v 11))
    (e₀ (v 5))
    ((hp 4) ▸ e₁ (v 5))
    (e₀ (v 10))
    ((hq 6) ▸ e₂ (v 10))
    ((hp 8) ▸ e₁ (v 13))
    (e₀ (v 13))
    ((hq 4) ▸ e₂ (v 7))
    (e₀ (v 7))
    ((hp 2) ▸ e₁ (v 3)) with hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit
  · exact branch1 p q v hp sep (hit)
  · exact branch2 p q v hp hq sep (hit)
  · exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (hit)
  · exact branch36 p q v hp hq sep (hit)
  · exact branch37 p q v hp hq sep G e₀ e₁ e₂ no (hit)
  · exact branch66 p q v hp hq sep G e₀ e₁ e₂ no (hit)
  · have t0 : v 3 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 2)))) (Eq.trans (congrArg p.symm (Eq.symm (hit))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    exact branch1 p q v hp sep (t0)
  · exact branch2 p q v hp hq sep (hit)
  · exact branch67 p q v hp hq sep (hit)
  · exact branch36 p q v hp hq sep (hit)
  · exact branch37 p q v hp hq sep G e₀ e₁ e₂ no (hit)
  · exact branch68 p q v hp hq sep G e₀ e₁ e₂ no (hit)
  · exact branch66 p q v hp hq sep G e₀ e₁ e₂ no (hit)
  · have t0 : v 3 = v 8 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 2)))) (Eq.trans (congrArg p.symm (Eq.symm (hit))) (p.symm_apply_eq.mpr (Eq.symm (hp 5))))
    exact branch1 p q v hp sep (t0)
  · have t0 : v 17 = v 3 := Eq.trans (Eq.symm (hp 9)) (Eq.trans (congrArg p (Eq.symm (hit))) (hp 5))
    exact branch67 p q v hp hq sep (Eq.symm (t0))
  · have t0 : v 5 = v 3 := Eq.trans (Eq.symm (hp 6)) (Eq.trans (congrArg p (Eq.symm (hit))) (hp 5))
    exact branch36 p q v hp hq sep (Eq.symm (t0))
  · have t0 : v 3 = v 10 := Eq.trans (Eq.symm (hp 5)) (Eq.trans (congrArg p (hit)) (hp 4))
    exact branch37 p q v hp hq sep G e₀ e₁ e₂ no (t0)
  · exact branch69 p q v hp hq sep G e₀ e₁ e₂ no (hit)
  · have t0 : v 16 = v 3 := Eq.trans (Eq.symm (hp 8)) (Eq.trans (congrArg p (Eq.symm (hit))) (hp 5))
    exact branch68 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm (t0))
  · exact branch70 p q v hp sep G e₀ e₁ e₂ no (hit)
  · have t0 : v 11 = v 8 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 7)))) (Eq.trans (congrArg q.symm (Eq.symm (hit))) (q.symm_apply_eq.mpr (Eq.symm (hq 5))))
    have t1 : v 5 = v 3 := Eq.trans (Eq.symm (hp 6)) (Eq.trans (congrArg p (t0)) (hp 5))
    exact branch36 p q v hp hq sep (Eq.symm (t1))
  · exact branch71 p q v hp hq sep G e₀ e₁ e₂ no (hit)
  · exact branch72 p q v hp hq sep G e₀ e₁ e₂ no (hit)
  · have t0 : v 10 = v 8 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 6)))) (Eq.trans (congrArg q.symm (Eq.symm (hit))) (q.symm_apply_eq.mpr (Eq.symm (hq 5))))
    exact branch69 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm (t0))
  · have t0 : v 8 = v 7 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 5)))) (Eq.trans (congrArg q.symm (hit)) (q.symm_apply_eq.mpr (Eq.symm (hq 4))))
    exact branch70 p q v hp sep G e₀ e₁ e₂ no (t0)
  · exact branch73 p q v hp hq sep G e₀ e₁ e₂ no (hit)
  · exact branch74 p q v hp hq sep (hit)
  · exact branch71 p q v hp hq sep G e₀ e₁ e₂ no (hit)
  · exact branch72 p q v hp hq sep G e₀ e₁ e₂ no (hit)
  · have t0 : v 8 = v 7 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 5)))) (Eq.trans (congrArg q.symm (hit)) (q.symm_apply_eq.mpr (Eq.symm (hq 4))))
    exact branch70 p q v hp sep G e₀ e₁ e₂ no (t0)
  · exact branch73 p q v hp hq sep G e₀ e₁ e₂ no (hit)
  · have t0 : v 14 = v 11 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 9)))) (Eq.trans (congrArg p.symm (hit)) (p.symm_apply_eq.mpr (Eq.symm (hp 6))))
    exact branch74 p q v hp hq sep (t0)
  · have t0 : v 14 = v 5 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 9)))) (Eq.trans (congrArg p.symm (hit)) (p.symm_apply_eq.mpr (Eq.symm (hp 4))))
    exact branch71 p q v hp hq sep G e₀ e₁ e₂ no (t0)
  · have t0 : v 14 = v 13 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 9)))) (Eq.trans (congrArg p.symm (hit)) (p.symm_apply_eq.mpr (Eq.symm (hp 8))))
    have t1 : v 8 = v 7 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 5)))) (Eq.trans (congrArg q.symm (t0)) (q.symm_apply_eq.mpr (Eq.symm (hq 4))))
    exact branch70 p q v hp sep G e₀ e₁ e₂ no (t1)
  · exact branch75 p q v hp hq sep G e₀ e₁ e₂ no (hit)
  · have t0 : v 14 = v 3 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 9)))) (Eq.trans (congrArg p.symm (hit)) (p.symm_apply_eq.mpr (Eq.symm (hp 2))))
    exact branch2 p q v hp hq sep (Eq.symm (t0))
  · have t0 : v 17 = v 1 := Eq.trans (Eq.symm (hq 7)) (Eq.trans (congrArg q (hit)) (hq 3))
    have t1 : v 14 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 9)))) (Eq.trans (congrArg p.symm (t0)) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    have t2 : v 8 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 5)))) (Eq.trans (congrArg q.symm (t1)) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    exact branch1 p q v hp sep (Eq.symm (t2))
  · have t0 : v 17 = v 16 := Eq.trans (Eq.symm (hq 7)) (Eq.trans (congrArg q (hit)) (hq 6))
    have t1 : v 14 = v 13 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 9)))) (Eq.trans (congrArg p.symm (t0)) (p.symm_apply_eq.mpr (Eq.symm (hp 8))))
    have t2 : v 8 = v 7 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 5)))) (Eq.trans (congrArg q.symm (t1)) (q.symm_apply_eq.mpr (Eq.symm (hq 4))))
    exact branch70 p q v hp sep G e₀ e₁ e₂ no (t2)
  · exact branch76 p q v hp hq sep G e₀ e₁ e₂ no (hit)
  · have t0 : v 17 = v 13 := Eq.trans (Eq.symm (hq 7)) (Eq.trans (congrArg q (hit)) (hq 4))
    exact branch75 p q v hp hq sep G e₀ e₁ e₂ no (t0)
  · have t0 : v 5 = v 11 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.symm (hit))) (p.symm_apply_eq.mpr (Eq.symm (hp 6))))
    have t1 : v 17 = v 1 := Eq.trans (Eq.symm (hq 7)) (Eq.trans (congrArg q (Eq.symm (t0))) (hq 3))
    have t2 : v 14 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 9)))) (Eq.trans (congrArg p.symm (t1)) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    have t3 : v 8 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 5)))) (Eq.trans (congrArg q.symm (t2)) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    exact branch1 p q v hp sep (Eq.symm (t3))
  · have t0 : v 13 = v 11 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 8)))) (Eq.trans (congrArg p.symm (Eq.symm (hit))) (p.symm_apply_eq.mpr (Eq.symm (hp 6))))
    exact branch76 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm (t0))
  · exact branch77 p q v hp hq sep (hit)
  · have t0 : v 3 = v 11 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 2)))) (Eq.trans (congrArg p.symm (Eq.symm (hit))) (p.symm_apply_eq.mpr (Eq.symm (hp 6))))
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (t0)
  · have t0 : v 5 = v 11 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (Eq.symm (hit))) (p.symm_apply_eq.mpr (Eq.symm (hp 6))))
    have t1 : v 17 = v 1 := Eq.trans (Eq.symm (hq 7)) (Eq.trans (congrArg q (Eq.symm (t0))) (hq 3))
    have t2 : v 14 = v 0 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 9)))) (Eq.trans (congrArg p.symm (t1)) (p.symm_apply_eq.mpr (Eq.symm (hp 0))))
    have t3 : v 8 = v 3 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 5)))) (Eq.trans (congrArg q.symm (t2)) (q.symm_apply_eq.mpr (Eq.symm (hq 2))))
    exact branch1 p q v hp sep (Eq.symm (t3))
  · exact branch77 p q v hp hq sep (hit)
  · have t0 : v 3 = v 11 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 2)))) (Eq.trans (congrArg p.symm (Eq.symm (hit))) (p.symm_apply_eq.mpr (Eq.symm (hp 6))))
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (t0)
  · have t0 : v 13 = v 5 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 8)))) (Eq.trans (congrArg p.symm (Eq.symm (hit))) (p.symm_apply_eq.mpr (Eq.symm (hp 4))))
    exact branch77 p q v hp hq sep (Eq.symm (t0))
  · exact branch78 p q v hp hq sep (hit)
  · have t0 : v 5 = v 3 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (hit)) (p.symm_apply_eq.mpr (Eq.symm (hp 2))))
    exact branch36 p q v hp hq sep (Eq.symm (t0))
  · exact branch78 p q v hp hq sep (hit)
  · have t0 : v 5 = v 3 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (hit)) (p.symm_apply_eq.mpr (Eq.symm (hp 2))))
    exact branch36 p q v hp hq sep (Eq.symm (t0))
  · have t0 : v 10 = v 7 := Eq.trans (Eq.symm (q.symm_apply_eq.mpr (Eq.symm (hq 6)))) (Eq.trans (congrArg q.symm (hit)) (q.symm_apply_eq.mpr (Eq.symm (hq 4))))
    have t1 : v 5 = v 3 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 4)))) (Eq.trans (congrArg p.symm (t0)) (p.symm_apply_eq.mpr (Eq.symm (hp 2))))
    exact branch36 p q v hp hq sep (Eq.symm (t1))
  · have t0 : v 13 = v 3 := Eq.trans (Eq.symm (p.symm_apply_eq.mpr (Eq.symm (hp 8)))) (Eq.trans (congrArg p.symm (hit)) (p.symm_apply_eq.mpr (Eq.symm (hp 2))))
    exact branch66 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm (t0))
  · exact branch79 p q v hq sep (hit)
  · exact branch79 p q v hq sep (hit)

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 8000 in
/-- Checking the conjugate square at three specified translates of one point suffices. -/
theorem local_matching_cycle (p q : Equiv.Perm X)
    (x : X) (squares : ∀ i : Fin 3, let y := ((![q,(1 : Equiv.Perm X),q*p⁻¹*q⁻¹] : Fin 3 → Equiv.Perm X) i) x;
      (p*(q*p*q⁻¹)) y = ((q*p*q⁻¹)*p) y)
    (sep : ∀ x, p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x)
    (G : SimpleGraph (Bool × X))
    (e₀ : ∀ x, G.Adj (false,x) (true,x))
    (e₁ : ∀ x, G.Adj (false,x) (true,p x))
    (e₂ : ∀ x, G.Adj (false,x) (true,q x)) :
    cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G := by

  classical
  have t0_12 : (p*(q⁻¹*p*q)) x=(q⁻¹*p*q*p) x := by
    have h := congrArg (fun y : X => (q⁻¹ : Equiv.Perm X) y) ((squares 0).symm)
    calc
      _ = ((q⁻¹)*(q*p*q⁻¹*p)*(q)) x := congrArg (fun g : Equiv.Perm X => g x) (by group : _ = _)
      _ = ((q⁻¹)*(p*q*p*q⁻¹)*(q)) x := h
      _ = _ := congrArg (fun g : Equiv.Perm X => g x) (by group : _ = _)
  have t0_13 : (p*(q*p*q⁻¹)) x=(q*p*q⁻¹*p) x := by
    have h := congrArg (fun y : X => ((1 : Equiv.Perm X) : Equiv.Perm X) y) (squares 1)
    calc
      _ = (((1 : Equiv.Perm X))*(p*q*p*q⁻¹)*((1 : Equiv.Perm X))) x := congrArg (fun g : Equiv.Perm X => g x) (by group : _ = _)
      _ = (((1 : Equiv.Perm X))*(q*p*q⁻¹*p)*((1 : Equiv.Perm X))) x := h
      _ = _ := congrArg (fun g : Equiv.Perm X => g x) (by group : _ = _)
  have t0_14 : (p*(q*p⁻¹*q⁻¹)) x=(q*p⁻¹*q⁻¹*p) x := by
    have h := congrArg (fun y : X => (q*p⁻¹*q⁻¹ : Equiv.Perm X) y) ((squares 2).symm)
    calc
      _ = ((q*p⁻¹*q⁻¹)*(q*p*q⁻¹*p)*(q*p⁻¹*q⁻¹)) x := congrArg (fun g : Equiv.Perm X => g x) (by group : _ = _)
      _ = ((q*p⁻¹*q⁻¹)*(p*q*p*q⁻¹)*(q*p⁻¹*q⁻¹)) x := h
      _ = _ := congrArg (fun g : Equiv.Perm X => g x) (by group : _ = _)
  let W : List (Equiv.Perm X) := [
    (1 : Equiv.Perm X),p,q,q⁻¹,q*p,q⁻¹*p,
    p*q,p*q⁻¹,p⁻¹*q⁻¹,p*q*p,p*q⁻¹*p,p⁻¹*q⁻¹*p,
    q⁻¹*p*q,q*p*q⁻¹,q*p⁻¹*q⁻¹,q⁻¹*p*q*p,q*p*q⁻¹*p,q*p⁻¹*q⁻¹*p]
  let v (i : ℕ) := (W.getD i 1) x
  have hp (i : Fin 10) : let e := ([(0,1),(2,6),(3,7),(4,9),(5,10),(8,3),(11,5),(12,15),(13,16),(14,17)] : List (ℕ × ℕ)).get i; p (v e.1)=v e.2 := by
    fin_cases i
    · change (p*((1 : Equiv.Perm X))) x = (p) x
      exact congrArg (fun f : Equiv.Perm X => f x) (by group : _ = _)
    · change (p*(q)) x = (p*q) x
      exact congrArg (fun f : Equiv.Perm X => f x) (by group : _ = _)
    · change (p*(q⁻¹)) x = (p*q⁻¹) x
      exact congrArg (fun f : Equiv.Perm X => f x) (by group : _ = _)
    · change (p*(q*p)) x = (p*q*p) x
      exact congrArg (fun f : Equiv.Perm X => f x) (by group : _ = _)
    · change (p*(q⁻¹*p)) x = (p*q⁻¹*p) x
      exact congrArg (fun f : Equiv.Perm X => f x) (by group : _ = _)
    · change (p*(p⁻¹*q⁻¹)) x = (q⁻¹) x
      exact congrArg (fun f : Equiv.Perm X => f x) (by group : _ = _)
    · change (p*(p⁻¹*q⁻¹*p)) x = (q⁻¹*p) x
      exact congrArg (fun f : Equiv.Perm X => f x) (by group : _ = _)
    · change (p*(q⁻¹*p*q)) x = (q⁻¹*p*q*p) x
      exact t0_12
    · change (p*(q*p*q⁻¹)) x = (q*p*q⁻¹*p) x
      exact t0_13
    · change (p*(q*p⁻¹*q⁻¹)) x = (q*p⁻¹*q⁻¹*p) x
      exact t0_14
  have hq (i : Fin 10) : let e := ([(0,2),(1,4),(3,0),(5,1),(7,13),(8,14),(10,16),(11,17),(12,6),(15,9)] : List (ℕ × ℕ)).get i; q (v e.1)=v e.2 := by
    fin_cases i
    · change (q*((1 : Equiv.Perm X))) x = (q) x
      exact congrArg (fun f : Equiv.Perm X => f x) (by group : _ = _)
    · change (q*(p)) x = (q*p) x
      exact congrArg (fun f : Equiv.Perm X => f x) (by group : _ = _)
    · change (q*(q⁻¹)) x = ((1 : Equiv.Perm X)) x
      exact congrArg (fun f : Equiv.Perm X => f x) (by group : _ = _)
    · change (q*(q⁻¹*p)) x = (p) x
      exact congrArg (fun f : Equiv.Perm X => f x) (by group : _ = _)
    · change (q*(p*q⁻¹)) x = (q*p*q⁻¹) x
      exact congrArg (fun f : Equiv.Perm X => f x) (by group : _ = _)
    · change (q*(p⁻¹*q⁻¹)) x = (q*p⁻¹*q⁻¹) x
      exact congrArg (fun f : Equiv.Perm X => f x) (by group : _ = _)
    · change (q*(p*q⁻¹*p)) x = (q*p*q⁻¹*p) x
      exact congrArg (fun f : Equiv.Perm X => f x) (by group : _ = _)
    · change (q*(p⁻¹*q⁻¹*p)) x = (q*p⁻¹*q⁻¹*p) x
      exact congrArg (fun f : Equiv.Perm X => f x) (by group : _ = _)
    · change (q*(q⁻¹*p*q)) x = (p*q) x
      exact congrArg (fun f : Equiv.Perm X => f x) (by group : _ = _)
    · change (q*(q⁻¹*p*q*p)) x = (p*q*p) x
      exact congrArg (fun f : Equiv.Perm X => f x) (by group : _ = _)
  by_contra no
  exact branch0 p q v hp hq sep G e₀ e₁ e₂ no


/-- On any nonempty action, commutation with the first conjugate suffices
for a simple cycle of length four, eight, or sixteen. -/
theorem conjugate_matching_cycle [Nonempty X] (p q : Equiv.Perm X)
    (comm : Commute p (q*p*q⁻¹))
    (sep : ∀ x, p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x)
    (G : SimpleGraph (Bool × X))
    (e₀ : ∀ x, G.Adj (false,x) (true,x))
    (e₁ : ∀ x, G.Adj (false,x) (true,p x))
    (e₂ : ∀ x, G.Adj (false,x) (true,q x)) :
    cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G := by

  classical
  exact local_matching_cycle p q (Classical.choice inferInstance) (fun i =>
    congrArg (fun g : Equiv.Perm X => g _) comm.eq) sep G e₀ e₁ e₂

theorem conjugate_defect_bound [Fintype X] (p q : Equiv.Perm X)
    (sep : ∀ x, p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x)
    (G : SimpleGraph (Bool × X))
    (e₀ : ∀ x, G.Adj (false,x) (true,x))
    (e₁ : ∀ x, G.Adj (false,x) (true,p x))
    (e₂ : ∀ x, G.Adj (false,x) (true,q x)) :
    ¬ (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) →
    Fintype.card X ≤ 3 * {y : X | (p*(q*p*q⁻¹)) y ≠ ((q*p*q⁻¹)*p) y}.ncard := by

  classical
  intro no
  let move : Fin 3 → Equiv.Perm X := ![q,(1 : Equiv.Perm X),q*p⁻¹*q⁻¹]
  let bad := {y : X | (p*(q*p*q⁻¹)) y ≠ ((q*p*q⁻¹)*p) y}
  let test (i : Fin 3) := (move i) ⁻¹' bad
  have cover : Set.univ ⊆ ⋃ i, test i := by
    intro x _
    by_contra hx
    apply no
    apply local_matching_cycle p q x _ sep G e₀ e₁ e₂
    intro i
    by_contra fail
    exact hx (Set.mem_iUnion.mpr ⟨i,fail⟩)
  have count (i : Fin 3) : (test i).ncard = bad.ncard := by
    have h := Set.encard_preimage_of_bijective (move i).bijective bad
    exact congrArg ENat.toNat h
  calc
    Fintype.card X = (Set.univ : Set X).ncard := by simp [Nat.card_eq_fintype_card]
    _ ≤ (⋃ i, test i).ncard := Set.ncard_le_ncard cover
    _ ≤ ∑ i, (test i).ncard := Set.ncard_iUnion_le_of_fintype test
    _ = 3 * bad.ncard := by simp [count]

/-- Any repeated pair of matching cosets can serve as the first pair. -/
theorem matching_cycle_after_relabel [Nonempty X] (p q : Equiv.Perm X)
    (sep : ∀ x, p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x)
    (ok : Commute p (q*p*q⁻¹) ∨ Commute q (p*q*p⁻¹) ∨
      Commute (p⁻¹*q) (p⁻¹*(p⁻¹*q)*(p⁻¹)⁻¹))
    (G : SimpleGraph (Bool × X))
    (e₀ : ∀ x, G.Adj (false,x) (true,x))
    (e₁ : ∀ x, G.Adj (false,x) (true,p x))
    (e₂ : ∀ x, G.Adj (false,x) (true,q x)) :
    cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G := by

  classical
  rcases ok with h|h|h
  · exact conjugate_matching_cycle p q h sep G e₀ e₁ e₂
  · exact conjugate_matching_cycle q p h (fun x => ⟨(sep x).2.1,(sep x).1,(sep x).2.2.symm⟩) G e₀ e₂ e₁
  let f : Bool × X → Bool × X := fun u => (u.1,if u.1 then p u.2 else u.2)
  have inj : Function.Injective f := by
    rintro ⟨i,x⟩ ⟨j,y⟩ h
    have ij : i=j := congrArg Prod.fst h
    subst j
    cases i <;> simpa [f] using h
  have lift : G.comap f ⊑ G := ⟨⟨⟨f,fun edge => edge⟩,inj⟩⟩
  have separated (x : X) : (p⁻¹*q) x ≠ x ∧ p⁻¹ x ≠ x ∧ (p⁻¹*q) x ≠ p⁻¹ x := by
    change p.symm (q x) ≠ x ∧ p.symm x ≠ x ∧ p.symm (q x) ≠ p.symm x
    exact ⟨fun h => (sep x).2.2 (p.symm_apply_eq.mp h).symm,
      fun h => (sep x).1 (p.symm_apply_eq.mp h).symm,fun h => (sep x).2.1 (p.symm.injective h)⟩
  have short := conjugate_matching_cycle (p⁻¹*q) p⁻¹ h
    separated (G.comap f) (fun x => e₁ x)
    (fun x => by change G.Adj (false,x) (true,p (p.symm (q x))); simpa using e₂ x)
    (fun x => by change G.Adj (false,x) (true,p (p.symm x)); simpa using e₀ x)
  exact short.imp (fun h => h.trans lift) (Or.imp (fun h => h.trans lift) (fun h => h.trans lift))


/-- In the absence of short cycles the conjugate-square defect has density
at least one third for each of the three choices of matching pair. -/
theorem relabel_defect_bounds [Fintype X] (p q : Equiv.Perm X)
    (sep : ∀ x, p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x)
    (G : SimpleGraph (Bool × X))
    (e₀ : ∀ x, G.Adj (false,x) (true,x))
    (e₁ : ∀ x, G.Adj (false,x) (true,p x))
    (e₂ : ∀ x, G.Adj (false,x) (true,q x)) 
    (no : ¬ (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G)) :
     ∀ (a b : Equiv.Perm X), (a=p ∧ b=q) ∨ (a=q ∧ b=p) ∨ (a=p⁻¹*q ∧ b=p⁻¹) →
       Fintype.card X ≤ 3 * {y : X | (a*(b*a*b⁻¹)) y ≠ ((b*a*b⁻¹)*a) y}.ncard := by
  classical
  intro a b choices
  rcases choices with ⟨ha,hb⟩|⟨ha,hb⟩|⟨ha,hb⟩ <;> subst a <;> subst b
  · exact conjugate_defect_bound p q sep G e₀ e₁ e₂ no
  · exact conjugate_defect_bound q p (fun x => ⟨(sep x).2.1,(sep x).1,(sep x).2.2.symm⟩) G e₀ e₂ e₁ no
  let f : Bool × X → Bool × X := fun u => (u.1,if u.1 then p u.2 else u.2)
  have inj : Function.Injective f := by
    rintro ⟨i,x⟩ ⟨j,y⟩ h
    have ij : i=j := congrArg Prod.fst h
    subst j
    cases i <;> simpa [f] using h
  have lift : G.comap f ⊑ G := ⟨⟨⟨f,fun edge => edge⟩,inj⟩⟩
  have separated (x : X) : (p⁻¹*q) x ≠ x ∧ p⁻¹ x ≠ x ∧ (p⁻¹*q) x ≠ p⁻¹ x := by
    change p.symm (q x) ≠ x ∧ p.symm x ≠ x ∧ p.symm (q x) ≠ p.symm x
    exact ⟨fun h => (sep x).2.2 (p.symm_apply_eq.mp h).symm,
      fun h => (sep x).1 (p.symm_apply_eq.mp h).symm,fun h => (sep x).2.1 (p.symm.injective h)⟩
  apply conjugate_defect_bound (p⁻¹*q) p⁻¹ separated (G.comap f) (fun x => e₁ x)
    (fun x => by change G.Adj (false,x) (true,p (p.symm (q x))); simpa using e₂ x)
    (fun x => by change G.Adj (false,x) (true,p (p.symm x)); simpa using e₀ x)
  exact fun h => no (h.imp (fun c => c.trans lift) (Or.imp (fun c => c.trans lift) (fun c => c.trans lift)))

/-- A separated matching graph has a cycle of length four, eight, or sixteen
whenever the relative permutations generate a group with an abelian normal
subgroup of index two. No transitivity or freeness assumption is required. -/
theorem index_two_matching_cycle [Nonempty X] (p q : Equiv.Perm X)
    (sep : ∀ x, p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x)
    (idx : ∃ N : Subgroup (Subgroup.closure ({p,q} : Set (Equiv.Perm X))),
      N.Normal ∧ IsMulCommutative N ∧ N.index=2)
    (G : SimpleGraph (Bool × X))
    (e₀ : ∀ x, G.Adj (false,x) (true,x))
    (e₁ : ∀ x, G.Adj (false,x) (true,p x))
    (e₂ : ∀ x, G.Adj (false,x) (true,q x)) :
    cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G := by
  classical
  let K := Subgroup.closure ({p,q} : Set (Equiv.Perm X))
  let a : K := ⟨p,Subgroup.subset_closure (by simp)⟩
  let b : K := ⟨q,Subgroup.subset_closure (by simp)⟩
  obtain ⟨N,normal,abelian,two⟩ := idx
  have commute {g h : K} (hg : g∈N) (hh : h∈N) : Commute (g : Equiv.Perm X) (h : Equiv.Perm X) :=
    congrArg (fun z : N => ((z:K):Equiv.Perm X))
      (abelian.is_comm.comm (⟨g,hg⟩ : N) (⟨h,hh⟩ : N))

  have rels {g : K} (hg : g ∈ N) (h : K) :
      Commute (g : Equiv.Perm X) ((h:Equiv.Perm X)*g*(h:Equiv.Perm X)⁻¹) :=
    commute hg (normal.conj_mem _ hg h)
  apply matching_cycle_after_relabel p q sep _ G e₀ e₁ e₂
  by_cases ha : a∈N
  · exact .inl (rels ha b)
  by_cases hb : b∈N
  · exact .inr (.inl (rels hb a))
  have hab : a⁻¹*b∈N :=
    (N.mul_mem_iff_of_index_two two).mpr (by simp [ha,hb])
  exact .inr (.inr (rels hab a⁻¹))

end Erdos64.MatchingConjugate

namespace OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R1_H2_R1_H1_R1
open scoped commutatorElement
open SimpleGraph

/-- A nontrivial abelian normal subgroup survives. The three matching labels are
distinct modulo this kernel, and each indicated conjugate square has large defect. -/
def H1 : Prop :=
  ∀ (X : Type) [Fintype X] [Nonempty X] (p q : Equiv.Perm X),
    (∀ x, p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x) →
    Fintype.card X ≤ 3 * {x : X | p (q x) ≠ q (p x)}.ncard →
    ¬ (Commute p ⁅p,q⁆ ∧ Commute q ⁅p,q⁆) →
    (∃ g ∈ Subgroup.closure ({p,q} : Set (Equiv.Perm X)), g ≠ 1 ∧ ∃ x : X, g x=x) →
    (∀ N : Subgroup (Subgroup.closure ({p,q} : Set (Equiv.Perm X))), N.Normal → IsMulCommutative N → N.index ≠ 11) →
    (∀ (a b : Equiv.Perm X), (a=p ∧ b=q) ∨ (a=q ∧ b=p) ∨ (a=p⁻¹*q ∧ b=p⁻¹) →
      Fintype.card X ≤ 3 * {y : X | (a*(b*a*b⁻¹)) y ≠ ((b*a*b⁻¹)*a) y}.ncard) →
    (∃ N : Subgroup (Subgroup.closure ({p,q} : Set (Equiv.Perm X))), N.Normal ∧ IsMulCommutative N ∧ N ≠ ⊥ ∧
      ∀ g : Subgroup.closure ({p,q} : Set (Equiv.Perm X)), g ∈ N → (g : Equiv.Perm X) ≠ p ∧ (g : Equiv.Perm X) ≠ q ∧ (g : Equiv.Perm X) ≠ p⁻¹*q) →
    ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ SimpleGraph.fromRel (fun u v : Bool × X =>
      u.1 = false ∧ v.1 = true ∧ (v.2 = u.2 ∨ v.2 = p u.2 ∨ v.2 = q u.2))

/-- The generated group has no nontrivial abelian normal subgroup. -/
def H2 : Prop :=
  ∀ (X : Type) [Fintype X] [Nonempty X] (p q : Equiv.Perm X),
    (∀ x, p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x) →
    Fintype.card X ≤ 3 * {x : X | p (q x) ≠ q (p x)}.ncard →
    ¬ (Commute p ⁅p,q⁆ ∧ Commute q ⁅p,q⁆) →
    (∃ g ∈ Subgroup.closure ({p,q} : Set (Equiv.Perm X)), g ≠ 1 ∧ ∃ x : X, g x=x) →
    (∀ N : Subgroup (Subgroup.closure ({p,q} : Set (Equiv.Perm X))), N.Normal → IsMulCommutative N → N.index ≠ 11) →
    (∀ (a b : Equiv.Perm X), (a=p ∧ b=q) ∨ (a=q ∧ b=p) ∨ (a=p⁻¹*q ∧ b=p⁻¹) →
      Fintype.card X ≤ 3 * {y : X | (a*(b*a*b⁻¹)) y ≠ ((b*a*b⁻¹)*a) y}.ncard) →
    (∀ N : Subgroup (Subgroup.closure ({p,q} : Set (Equiv.Perm X))), N.Normal → IsMulCommutative N → N = ⊥) →
    ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ SimpleGraph.fromRel (fun u v : Bool × X =>
      u.1 = false ∧ v.1 = true ∧ (v.2 = u.2 ∨ v.2 = p u.2 ∨ v.2 = q u.2))

theorem main : H1 → H2 → OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R1_H2_R1.H1 := by
  classical
  intro withKernel withoutKernel X _ _ p q sep density central fixed noEleven
  let G := SimpleGraph.fromRel (fun u v : Bool × X =>
    u.1=false ∧ v.1=true ∧ (v.2=u.2 ∨ v.2=p u.2 ∨ v.2=q u.2))
  have e₀ (x : X) : G.Adj (false,x) (true,x) := ⟨by simp,Or.inl ⟨rfl,rfl,Or.inl rfl⟩⟩
  have e₁ (x : X) : G.Adj (false,x) (true,p x) := ⟨by simp,Or.inl ⟨rfl,rfl,Or.inr (Or.inl rfl)⟩⟩
  have e₂ (x : X) : G.Adj (false,x) (true,q x) := ⟨by simp,Or.inl ⟨rfl,rfl,Or.inr (Or.inr rfl)⟩⟩
  by_cases short : cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G
  · rcases short with h|h|h
    · exact ⟨2,by decide,h⟩
    · exact ⟨3,by decide,h⟩
    · exact ⟨4,by decide,h⟩
  have bounds := Erdos64.MatchingConjugate.relabel_defect_bounds p q sep G e₀ e₁ e₂ short
  let K := Subgroup.closure ({p,q} : Set (Equiv.Perm X))
  by_cases pos : ∃ N : Subgroup K, N.Normal ∧ IsMulCommutative N ∧ N ≠ ⊥
  · obtain ⟨N,normal,abelian,nt⟩ := pos
    apply withKernel X p q sep density central fixed noEleven bounds
    refine ⟨N,normal,abelian,nt,?_⟩
    intro g hg
    let a : K := ⟨p,Subgroup.subset_closure (by simp)⟩
    let b : K := ⟨q,Subgroup.subset_closure (by simp)⟩
    have localComm (h : K) : Commute (g:Equiv.Perm X) ((h:Equiv.Perm X)*g*(h:Equiv.Perm X)⁻¹) :=
      congrArg (fun z : N => ((z:K):Equiv.Perm X))
        (abelian.is_comm.comm (⟨g,hg⟩ : N) (⟨h*g*h⁻¹,normal.conj_mem _ hg h⟩ : N))
    have impossible := fun ok => short (Erdos64.MatchingConjugate.matching_cycle_after_relabel p q sep ok G e₀ e₁ e₂)
    refine ⟨fun h => impossible (.inl ?_), fun h => impossible (.inr (.inl ?_)),fun h => impossible (.inr (.inr ?_))⟩
    · simpa only [← h] using localComm b
    · simpa only [← h] using localComm a
    · have raw : Commute (g:Equiv.Perm X) (p⁻¹*(g:Equiv.Perm X)*(p⁻¹)⁻¹) := localComm a⁻¹
      exact h ▸ raw
  · apply withoutKernel X p q sep density central fixed noEleven bounds
    intro N normal abelian
    by_contra nt
    exact pos ⟨N,normal,abelian,nt⟩

end OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R1_H2_R1_H1_R1
