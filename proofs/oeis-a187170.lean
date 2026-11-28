import OMAStatements.S_oeis_a187170
import Mathlib.Tactic

/-! At widths at least 8, every translate count is a polynomial of degree
at most 3. Its finite difference of order 4 vanishes. The proof applies
this identity to each actual walk shape and checks the initial coefficients. -/

namespace LatticeWalk170
open OMA.S_oeis_a187170

/-- Merge the weights of walks whose three coordinate spans coincide. -/
def addProfile (p : Profile) : List Profile → List Profile
  | [] => [p]
  | q :: qs =>
    if p.2 = q.2 then (p.1 + q.1, q.2) :: qs else q :: addProfile p qs

def total (n : ℕ) (xs : List Profile) : ℤ := (xs.map (placed n)).sum

@[simp] lemma total_nil (n : ℕ) : total n [] = 0 := rfl
@[simp] lemma total_cons (n : ℕ) (p : Profile) (ps : List Profile) :
    total n (p::ps) = placed n p + total n ps := rfl

lemma addProfile_total (n : ℕ) (p : Profile) (ps : List Profile) :
    total n (addProfile p ps) = placed n p + total n ps := by
  induction ps with
  | nil => simp [addProfile]
  | cons q qs ih =>
    obtain ⟨w, s⟩ := p
    obtain ⟨v, t⟩ := q
    by_cases eq : s = t
    · subst t
      simp [addProfile, placed, Nat.cast_add]
      ring
    · simp [addProfile, eq, ih, add_left_comm]

lemma foldProfiles (n : ℕ) (ps initial : List Profile) :
    total n (ps.foldl (fun acc p => addProfile p acc) initial) = total n ps + total n initial := by
  induction ps generalizing initial with
  | nil => simp
  | cons p qs ih =>
    simp [List.foldl_cons, ih, addProfile_total, add_comm, add_left_comm]

/-- The entries are total multiplicity and the three spans, in first-visit order.
The single kernel computation below certifies every entry from the walk enumerator. -/
def table : List Profile := [
  (6, 8, 0, 0), (168, 7, 1, 0), (408, 6, 1, 0), (504, 6, 2, 0),
  (1008, 6, 1, 1), (456, 5, 1, 0), (1248, 5, 2, 0), (4176, 5, 1, 1),
  (840, 5, 3, 0), (3360, 5, 2, 1), (1680, 5, 1, 2), (264, 4, 1, 0),
  (1800, 4, 2, 0), (7968, 4, 1, 1), (1440, 4, 3, 0), (12240, 4, 2, 1),
  (6960, 4, 1, 2), (840, 4, 4, 0), (5040, 4, 3, 1), (5040, 4, 2, 2),
  (1680, 4, 1, 3), (1440, 3, 2, 0), (9408, 3, 1, 1), (2208, 3, 3, 0),
  (23664, 3, 2, 1), (13872, 3, 1, 2), (1248, 3, 4, 0), (13392, 3, 3, 1),
  (17280, 3, 2, 2), (5808, 3, 1, 3), (504, 3, 5, 0), (4032, 3, 4, 1),
  (6048, 3, 3, 2), (4032, 3, 2, 3), (1008, 3, 1, 4), (120, 2, 2, 0),
  (1176, 2, 3, 0), (23664, 2, 2, 1), (1536, 2, 4, 0), (21168, 2, 3, 1),
  (30720, 2, 2, 2), (3120, 2, 1, 1), (14880, 2, 1, 2), (9840, 2, 1, 3),
  (768, 2, 5, 0), (9024, 2, 4, 1), (15168, 2, 3, 2), (11232, 2, 2, 3),
  (2928, 2, 1, 4), (168, 2, 6, 0), (1680, 2, 5, 1), (3360, 2, 4, 2),
  (3360, 2, 3, 3), (1680, 2, 2, 4), (336, 2, 1, 5), (168, 1, 4, 0),
  (6816, 1, 3, 1), (264, 1, 5, 0), (5136, 1, 4, 1), (10128, 1, 3, 2),
  (2928, 1, 2, 1), (12432, 1, 2, 2), (8112, 1, 2, 3), (144, 1, 6, 0),
  (2016, 1, 5, 1), (4320, 1, 4, 2), (4320, 1, 3, 3), (2496, 1, 2, 4),
  (2448, 1, 1, 2), (3600, 1, 1, 3), (2064, 1, 1, 4), (528, 1, 1, 5),
  (24, 1, 7, 0), (288, 1, 6, 1), (720, 1, 5, 2), (960, 1, 4, 3),
  (720, 1, 3, 4), (288, 1, 2, 5), (48, 1, 1, 6)]

set_option maxRecDepth 60000 in
set_option maxHeartbeats 8000000 in
lemma census : shapes.foldl (fun acc p => addProfile p acc) [] = table := by
  decide +kernel

lemma useTable (n : ℕ) : sequence n = total n table := by
  have h := foldProfiles n shapes []
  rw [census] at h
  change total n shapes = total n table
  simpa only [total_nil, add_zero] using h.symm

abbrev bounded (w : Profile) := w.2.1 ≤ 8 ∧ w.2.2.1 ≤ 8 ∧ w.2.2.2 ≤ 8

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
lemma shapeBound : ∀ w ∈ table, bounded w := by
  have h : table.all (fun w => decide (bounded w)) = true := by decide +kernel
  intro w hw
  exact of_decide_eq_true (List.all_eq_true.mp h w hw)

lemma one (k : ℕ) (w : Profile) (ok : bounded w) : placed (k+12) w - 4*placed (k+11) w + 6*placed (k+10) w - 4*placed (k+9) w + placed (k+8) w = 0 := by
  obtain ⟨h0,h1,h2⟩ := ok
  simp (disch := omega) only [placed,Nat.cast_sub,Nat.cast_add,Nat.cast_ofNat]
  ring

lemma linearSum (k : ℕ) (xs : List Profile) (ok : ∀ w ∈ xs, bounded w) :
    (xs.map (placed (k+12))).sum - 4*(xs.map (placed (k+11))).sum + 6*(xs.map (placed (k+10))).sum - 4*(xs.map (placed (k+9))).sum + (xs.map (placed (k+8))).sum = 0 := by
  induction xs with
  | nil => simp
  | cons w xs ih =>
    have hw := one k w (ok w (by simp))
    have hx := ih (fun v hv => ok v (List.mem_cons_of_mem w hv))
    simp only [List.map_cons,List.sum_cons]
    linear_combination hw + hx

lemma recurrence (k : ℕ) : sequence (k+12) - 4*sequence (k+11) + 6*sequence (k+10) - 4*sequence (k+9) + sequence (k+8) = 0 := by
  simp only [useTable]
  exact linearSum k table shapeBound

def finiteLag (d n : ℕ) : ℤ := if d ≤ n then total (n-d) table else 0

lemma lag_eq (d n : ℕ) : lag d n = finiteLag d n := by
  simp [lag, finiteLag, useTable]

set_option maxRecDepth 26000 in
set_option maxHeartbeats 3000000 in
lemma initial : ∀ n : Fin 12, lag 0 n.val - 4*lag 1 n.val + 6*lag 2 n.val - 4*lag 3 n.val + lag 4 n.val = numerator n.val := by
  simp only [lag_eq]
  decide +kernel

lemma gf (n : ℕ) : lag 0 n - 4*lag 1 n + 6*lag 2 n - 4*lag 3 n + lag 4 n = numerator n := by
  by_cases hn : n < 12
  · exact initial ⟨n,hn⟩
  · obtain ⟨k,rfl⟩ : ∃ k : ℕ, n = k+12 := ⟨n-12,by omega⟩
    change sequence (k+12) - 4*sequence (k+11) + 6*sequence (k+10) - 4*sequence (k+9) + sequence (k+8) = 0
    exact recurrence k

end LatticeWalk170

theorem OMA.solution : type_of% @OMA.S_oeis_a187170.main := by
  refine ⟨LatticeWalk170.gf, ?_⟩
  intro k
  linear_combination LatticeWalk170.recurrence k
