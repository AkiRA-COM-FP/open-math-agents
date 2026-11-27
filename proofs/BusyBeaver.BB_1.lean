import FormalConjectures.Wikipedia.BusyBeaver

open Turing BusyBeaver Machine

namespace OMA

variable {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ]

lemma I : (init [] : Cfg Γ Λ) = ⟨some default, ⟨default, ListBlank.mk [], ListBlank.mk []⟩⟩ := rfl

lemma R (M : Machine Γ Λ) [Subsingleton Λ] (q : Λ) (a : Γ)
    (h : M default default = some (some q, Stmt.write a Dir.right)) (k : ℕ) :
    ∃ L, M.multiStep (init []) k = some ⟨some default, ⟨default, L, ListBlank.mk []⟩⟩ := by
  induction k with
  | zero => exact ⟨_, rfl⟩
  | succ k ih =>
    obtain ⟨L, hL⟩ := ih
    exact ⟨ListBlank.cons a L, by simp [hL, step, h, Subsingleton.elim q default, Tape.write, Tape.move]⟩

lemma L (M : Machine Γ Λ) [Subsingleton Λ] (q : Λ) (a : Γ)
    (h : M default default = some (some q, Stmt.write a Dir.left)) (k : ℕ) :
    ∃ R, M.multiStep (init []) k = some ⟨some default, ⟨default, ListBlank.mk [], R⟩⟩ := by
  induction k with
  | zero => exact ⟨_, rfl⟩
  | succ k ih =>
    obtain ⟨R, hR⟩ := ih
    exact ⟨ListBlank.cons a R, by simp [hR, step, h, Subsingleton.elim q default, Tape.write, Tape.move]⟩

lemma B (M : Machine Γ Λ) [Subsingleton Λ] (N : ℕ) (hN : M.haltingNumber = N) : N ≤ 1 := by
  rcases hM : M default default with _ | ⟨_ | q, a, d⟩
  · rw [haltingNumber_def M 0 ⟨_, rfl⟩ (by simp [I, step, hM])] at hN; norm_cast at hN; omega
  · rw [haltingNumber_def M 1 (by simp [I, step, hM]) (by simp [I, step, hM])] at hN
    norm_cast at hN; omega
  · have : M.haltingNumber = ⊤ := by
      refine sInf_eq_top.2 ?_
      rintro _ ⟨n, hn, rfl⟩
      cases d
      · obtain ⟨_, h⟩ := L M q a hM (n + 1); rw [HaltsAfter, h] at hn; cases hn
      · obtain ⟨_, h⟩ := R M q a hM (n + 1); rw [HaltsAfter, h] at hn; cases hn
    simp [this] at hN

def C : Candidate 1 := ⟨Bool, Unit, inferInstance, rfl, inferInstance, inferInstance, rfl,
  inferInstance, fun _ _ => some (none, Stmt.write default Dir.right),
  (isHalting_iff_exists_haltsAt _).2 ⟨1, rfl⟩⟩

end OMA

theorem OMA.solution : type_of% @BusyBeaver.BB_1 := by
  have b : ∀ N ∈ {N : ℕ | ∃ C : Candidate 1, C.M.haltingNumber = N}, N ≤ 1 := by
    rintro N ⟨C, hC⟩
    have := Fintype.card_le_one_iff_subsingleton.1 C.Λ_card.le
    exact OMA.B C.M N hC
  have m : 1 ∈ {N : ℕ | ∃ C : Candidate 1, C.M.haltingNumber = N} :=
    ⟨OMA.C, haltingNumber_def _ 1 ⟨_, rfl⟩ rfl⟩
  exact le_antisymm (csSup_le ⟨1, m⟩ b) (le_csSup ⟨1, b⟩ m)
