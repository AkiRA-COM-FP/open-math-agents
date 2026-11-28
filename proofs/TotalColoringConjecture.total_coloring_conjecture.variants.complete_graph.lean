import FormalConjectures.Wikipedia.TotalColoringConjecture

/-! Shorter proof of `TotalColoringConjecture.total_coloring_conjecture.variants.complete_graph`. -/

open SimpleGraph

theorem OMA.solution :
    type_of% @TotalColoringConjecture.total_coloring_conjecture.variants.complete_graph := by
  classical
  intro n
  let q := 2 * (n / 2) + 1
  have hn : n ≤ q := by omega
  have : NeZero q := ⟨by omega⟩
  let f (v : Fin n) : ZMod q := v.val
  have hf : Function.Injective f := fun u v h => by
    have hm := (ZMod.natCast_eq_natCast_iff' u.val v.val q).mp h
    rwa [Nat.mod_eq_of_lt (u.isLt.trans_le hn), Nat.mod_eq_of_lt (v.isLt.trans_le hn),
      ← Fin.ext_iff] at hm
  have h2 : IsUnit (2 : ZMod q) :=
    (ZMod.isUnit_iff_coprime 2 q).2 (Nat.prime_two.coprime_iff_not_dvd.2 (by omega))
  let es : Sym2 (Fin n) → ZMod q := Sym2.lift ⟨fun u v => f u + f v, fun _ _ => add_comm _ _⟩
  have heq {v : Fin n} {e : Sym2 (Fin n)} (h : v ∈ e) : es e = f v + f (Sym2.Mem.other h) :=
    congrArg es (Sym2.other_spec h).symm
  let col : ZMod q ≃ Fin q := Fintype.equivFinOfCardEq (ZMod.card q)
  refine (Nat.sInf_le (s := {k | (completeGraph (Fin n)).TotalColorable k})
    ⟨Sum.elim (fun v => col (2 * f v)) (fun e => col (es e.1)),
      fun _ _ huv h => huv.ne (hf (h2.mul_right_inj.mp (col.injective h))),
      fun e d hne ⟨v, he, hd⟩ h => hne <| Subtype.ext <| (Sym2.other_spec he).symm.trans <|
        (congrArg (fun x => s(v, x)) (hf <| add_left_cancel <| by
          have H := col.injective h; rwa [heq he, heq hd] at H)).trans (Sym2.other_spec hd),
      fun v e he h => ?_⟩).trans ?_
  · have H := col.injective h; rw [two_mul, heq he] at H
    exact ((completeGraph (Fin n)).mem_edgeSet.mp (by rw [Sym2.other_spec he]; exact e.2)).ne
      (hf (add_left_cancel H))
  · change q ≤ (⊤ : SimpleGraph (Fin n)).maxDegree + 2
    simp only [maxDegree_top, Fintype.card_fin]; omega
