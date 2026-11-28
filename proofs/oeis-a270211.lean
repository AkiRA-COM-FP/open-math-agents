import OMAStatements.S_oeis_a270211

section Disproof_a270211
open OMA.S_oeis_a270211

def lookupL {α : Type} : List α → ℕ → α → α
  | [], _, d => d
  | b :: _, 0, _ => b
  | _ :: bs, i + 1, d => lookupL bs i d

lemma lookupL_eq_getD {α : Type} (xs : List α) (i : ℕ) (d : α) :
    lookupL xs i d = xs.getD i d := by
  induction xs generalizing i with
  | nil => simp [lookupL, List.getD]
  | cons x xs ih =>
    cases i with
    | zero => simp [lookupL, List.getD]
    | succ i => simp [lookupL, List.getD, ih]

lemma lookupL_map {α β : Type} (f : α → β) (xs : List α) (i : ℕ) (da : α) (db : β)
    (hi : i < xs.length) :
    lookupL (xs.map f) i db = f (lookupL xs i da) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons _ xs ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i (by simp at hi; omega)

lemma lookupL_append {α : Type} (xs ys : List α) (i : ℕ) (d : α) :
    lookupL (xs ++ ys) i d =
      if i < xs.length then lookupL xs i d else lookupL ys (i - xs.length) d := by
  induction xs generalizing i with
  | nil => simp
  | cons _ xs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simp only [List.cons_append, lookupL, List.length_cons,
        Nat.succ_lt_succ_iff, Nat.succ_sub_succ_eq_sub, ih]

lemma lookupL_replicate_same {α : Type} (n i : ℕ) (v : α) :
    lookupL (List.replicate n v) i v = v := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

lemma lookupL_out {α : Type} (xs : List α) (i : ℕ) (d : α) (h : xs.length ≤ i) :
    lookupL xs i d = d := by
  induction xs generalizing i with
  | nil => rfl
  | cons _ xs ih =>
    cases i with
    | zero => simp at h
    | succ i => exact ih i (by simp at h; omega)

lemma lookupL_in_mem {α : Type} (xs : List α) (i : ℕ) (d : α) (hi : i < xs.length) :
    lookupL xs i d ∈ xs := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => simp [lookupL]
    | succ i => exact List.mem_cons_of_mem x (ih i (by simp at hi; omega))

lemma lookupL_congr_default {α : Type} (xs : List α) (i : ℕ) (d1 d2 : α) (hi : i < xs.length) :
    lookupL xs i d1 = lookupL xs i d2 := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons _ xs ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i (by simp at hi; omega)

def pad1 {α : Type} (v : α) (xs : List α) : List α :=
  v :: v :: (xs ++ [v, v])

lemma length_pad1 {α : Type} (v : α) (xs : List α) : (pad1 v xs).length = xs.length + 4 := by
  simp [pad1]

lemma lookupL_pad1 {α : Type} (v : α) (xs : List α) (n i : ℕ) (h : xs.length = n) :
    lookupL (pad1 v xs) i v = if 2 ≤ i ∧ i < n + 2 then lookupL xs (i - 2) v else v := by
  subst h
  cases i with
  | zero => simp [pad1, lookupL]
  | succ i =>
    cases i with
    | zero => simp [pad1, lookupL]
    | succ j =>
      simp only [pad1, lookupL, lookupL_append]
      by_cases hj : j < xs.length
      · have hcond : 2 ≤ j + 1 + 1 ∧ j + 1 + 1 < xs.length + 2 := by omega
        simp [hj, hcond]
      · have hcond : ¬(2 ≤ j + 1 + 1 ∧ j + 1 + 1 < xs.length + 2) := by omega
        simp only [if_neg hj, if_neg hcond]
        rcases (show j - xs.length = 0 ∨ j - xs.length = 1 ∨ 2 ≤ j - xs.length by omega) with
          h0 | h1 | h2
        · rw [h0]; rfl
        · rw [h1]; rfl
        · exact lookupL_out [v, v] (j - xs.length) v (by simp; omega)

def stepRow3 : List Bool → List Bool → List Bool → List Bool
  | _ :: n :: ns, w :: c :: e :: cs, _ :: s :: ss =>
      applyRule 123 c n s w e :: stepRow3 (n :: ns) (c :: e :: cs) (s :: ss)
  | _, _, _ => []

lemma length_stepRow3 (r1 r2 r3 : List Bool) (n : ℕ)
    (h1 : r1.length = n + 2) (h2 : r2.length = n + 2) (h3 : r3.length = n + 2) :
    (stepRow3 r1 r2 r3).length = n := by
  induction n generalizing r1 r2 r3 with
  | zero =>
    match r2 with
    | [_, _] => simp [stepRow3]
    | [] | [_] | _ :: _ :: _ :: _ => simp at h2
  | succ n ih =>
    match r1, r2, r3 with
    | _ :: b1 :: cs1, _ :: b2 :: c2 :: cs2, _ :: b3 :: cs3 =>
      simp only [stepRow3, List.length_cons]
      rw [ih (b1 :: cs1) (b2 :: c2 :: cs2) (b3 :: cs3)
        (by simp at h1 ⊢; omega) (by simp at h2 ⊢; omega) (by simp at h3 ⊢; omega)]
    | [], _, _ | [_], _, _ => simp at h1
    | _, [], _ | _, [_], _ | _, [_, _], _ => simp at h2
    | _, _, [] | _, _, [_] => simp at h3

lemma lookupL_stepRow3 (r1 r2 r3 : List Bool) (n i : ℕ) (d : Bool)
    (h1 : r1.length = n + 2) (h2 : r2.length = n + 2) (h3 : r3.length = n + 2) (hi : i < n) :
    lookupL (stepRow3 r1 r2 r3) i d =
      applyRule 123 (lookupL r2 (i + 1) d) (lookupL r1 (i + 1) d) (lookupL r3 (i + 1) d)
        (lookupL r2 i d) (lookupL r2 (i + 2) d) := by
  induction i generalizing r1 r2 r3 n with
  | zero =>
    rcases n with _ | n
    · omega
    match r1, r2, r3 with
    | _ :: _ :: _, _ :: _ :: _ :: _, _ :: _ :: _ => rfl
    | [], _, _ | [_], _, _ => simp at h1
    | _, [], _ | _, [_], _ | _, [_, _], _ => simp at h2
    | _, _, [] | _, _, [_] => simp at h3
  | succ i ih =>
    rcases n with _ | n
    · omega
    match r1, r2, r3 with
    | _ :: b1 :: cs1, _ :: b2 :: c2 :: cs2, _ :: b3 :: cs3 =>
      simp only [stepRow3, lookupL]
      exact ih (b1 :: cs1) (b2 :: c2 :: cs2) (b3 :: cs3) n
        (by simp at h1 ⊢; omega) (by simp at h2 ⊢; omega) (by simp at h3 ⊢; omega) (by omega)

def stepGrid : List (List Bool) → List (List Bool)
  | r1 :: r2 :: r3 :: rs => stepRow3 r1 r2 r3 :: stepGrid (r2 :: r3 :: rs)
  | _ => []

lemma length_stepGrid (ps : List (List Bool)) (m w : ℕ)
    (hlen : ps.length = m + 2) (hrow : ∀ r ∈ ps, r.length = w + 2) :
    (stepGrid ps).length = m ∧ ∀ r ∈ stepGrid ps, r.length = w := by
  induction m generalizing ps with
  | zero =>
    match ps with
    | [_, _] => simp [stepGrid]
    | [] | [_] | _ :: _ :: _ :: _ => simp at hlen
  | succ m ih =>
    match ps with
    | r1 :: r2 :: r3 :: rs =>
      have hr1 : r1.length = w + 2 := hrow r1 (by simp)
      have hr2 : r2.length = w + 2 := hrow r2 (by simp)
      have hr3 : r3.length = w + 2 := hrow r3 (by simp)
      have hsub := ih (r2 :: r3 :: rs) (by simp at hlen ⊢; omega)
        (fun r hr => hrow r (List.mem_cons_of_mem r1 hr))
      simp only [stepGrid, List.length_cons, hsub.1, true_and, List.mem_cons]
      rintro r (rfl | hr)
      · exact length_stepRow3 r1 r2 r3 w hr1 hr2 hr3
      · exact hsub.2 r hr
    | [] | [_] | [_, _] => simp at hlen

lemma lookupL_stepGrid (ps : List (List Bool)) (m w iy ix : ℕ) (bg : Bool)
    (hlen : ps.length = m + 2) (hrow : ∀ r ∈ ps, r.length = w + 2)
    (hiy : iy < m) (hix : ix < w) :
    lookupL (lookupL (stepGrid ps) iy []) ix bg =
      applyRule 123 (lookupL (lookupL ps (iy + 1) []) (ix + 1) bg)
        (lookupL (lookupL ps iy []) (ix + 1) bg)
        (lookupL (lookupL ps (iy + 2) []) (ix + 1) bg)
        (lookupL (lookupL ps (iy + 1) []) ix bg)
        (lookupL (lookupL ps (iy + 1) []) (ix + 2) bg) := by
  induction iy generalizing ps m with
  | zero =>
    rcases m with _ | m
    · omega
    match ps with
    | r1 :: r2 :: r3 :: rs =>
      simp only [stepGrid, lookupL]
      exact lookupL_stepRow3 r1 r2 r3 w ix bg
        (hrow r1 (by simp)) (hrow r2 (by simp)) (hrow r3 (by simp)) hix
    | [] | [_] | [_, _] => simp at hlen
  | succ iy ih =>
    rcases m with _ | m
    · omega
    match ps with
    | r1 :: r2 :: r3 :: rs =>
      simp only [stepGrid, lookupL]
      exact ih (r2 :: r3 :: rs) m (by simp at hlen ⊢; omega)
        (fun r hr => hrow r (List.mem_cons_of_mem r1 hr)) (by omega)

def nextCfg (t : ℕ) (c : Bool × List (List Bool)) : Bool × List (List Bool) :=
  let bg := c.1
  let bg' := applyRule 123 bg bg bg bg bg
  let blank := List.replicate (2 * t + 5) bg
  let padded := pad1 blank (c.2.map (pad1 bg))
  (bg', stepGrid padded)

def cfg : ℕ → Bool × List (List Bool)
  | 0 => (false, [[true]])
  | t + 1 => nextCfg t (cfg t)

def CfgWf (t : ℕ) (c : Bool × List (List Bool)) : Prop :=
  c.2.length = 2 * t + 1 ∧ ∀ r ∈ c.2, r.length = 2 * t + 1

lemma padded_wf (t : ℕ) (c : Bool × List (List Bool)) (hwf : CfgWf t c) :
    let blank := List.replicate (2 * t + 5) c.1
    let padded := pad1 blank (c.2.map (pad1 c.1))
    padded.length = (2 * (t + 1) + 1) + 2 ∧
      ∀ r ∈ padded, r.length = (2 * (t + 1) + 1) + 2 := by
  dsimp only
  refine ⟨by rw [length_pad1, List.length_map, hwf.1]; omega, ?_⟩
  intro r hr
  simp only [pad1, List.mem_cons, List.mem_append, List.mem_map] at hr
  rcases hr with rfl | rfl | ⟨⟨row, hmem, rfl⟩ | hr2⟩
  · simp; omega
  · simp; omega
  · simp [hwf.2 row hmem]; omega
  · simp only [List.not_mem_nil, or_false] at hr2
    rcases hr2 with rfl | rfl <;> (simp; omega)

lemma cfg_wf (t : ℕ) : CfgWf t (cfg t) := by
  induction t with
  | zero => simp [CfgWf, cfg]
  | succ t ih =>
    unfold CfgWf cfg nextCfg
    dsimp only
    have hp := padded_wf t (cfg t) ih
    exact length_stepGrid _ (2 * (t + 1) + 1) (2 * (t + 1) + 1) hp.1 hp.2

lemma lookupL_padded (t : ℕ) (c : Bool × List (List Bool)) (hwf : CfgWf t c) (ky kx : ℕ) :
    lookupL (lookupL (pad1 (List.replicate (2 * t + 5) c.1) (c.2.map (pad1 c.1))) ky []) kx c.1 =
      getCell t c ((kx : ℤ) - ↑t - 2) ((ky : ℤ) - ↑t - 2) := by
  set blank := List.replicate (2 * t + 5) c.1
  have hmap_len : (c.2.map (pad1 c.1)).length = 2 * t + 1 := by simp [hwf.1]
  have hp_len : (pad1 blank (c.2.map (pad1 c.1))).length = 2 * t + 5 := by
    rw [length_pad1, hmap_len]
  have hswap : lookupL (lookupL (pad1 blank (c.2.map (pad1 c.1))) ky []) kx c.1 =
      lookupL (lookupL (pad1 blank (c.2.map (pad1 c.1))) ky blank) kx c.1 := by
    by_cases hky : ky < 2 * t + 5
    · rw [lookupL_congr_default _ ky [] blank (by omega)]
    · rw [lookupL_out _ ky [] (by omega), lookupL_out _ ky blank (by omega),
          lookupL_replicate_same]
      rfl
  rw [hswap, lookupL_pad1 blank (c.2.map (pad1 c.1)) (2 * t + 1) ky hmap_len]
  by_cases hky : 2 ≤ ky ∧ ky < (2 * t + 1) + 2
  · rw [if_pos hky, lookupL_map (pad1 c.1) c.2 (ky - 2) [] blank (by rw [hwf.1]; omega)]
    have hrow_len : (lookupL c.2 (ky - 2) []).length = 2 * t + 1 :=
      hwf.2 _ (lookupL_in_mem c.2 (ky - 2) [] (by rw [hwf.1]; omega))
    rw [lookupL_pad1 c.1 _ (2 * t + 1) kx hrow_len]
    unfold getCell
    by_cases hkx : 2 ≤ kx ∧ kx < (2 * t + 1) + 2
    · have hbox : -(t : ℤ) ≤ (kx : ℤ) - ↑t - 2 ∧ (kx : ℤ) - ↑t - 2 ≤ ↑t ∧
          -(t : ℤ) ≤ (ky : ℤ) - ↑t - 2 ∧ (ky : ℤ) - ↑t - 2 ≤ ↑t := by omega
      rw [if_pos hkx, if_pos hbox]
      have ey : ((ky : ℤ) - ↑t - 2 + ↑t).toNat = ky - 2 := by omega
      have ex : ((kx : ℤ) - ↑t - 2 + ↑t).toNat = kx - 2 := by omega
      rw [ey, ex, ← lookupL_eq_getD, ← lookupL_eq_getD]
    · have hbox : ¬(-(t : ℤ) ≤ (kx : ℤ) - ↑t - 2 ∧ (kx : ℤ) - ↑t - 2 ≤ ↑t ∧
          -(t : ℤ) ≤ (ky : ℤ) - ↑t - 2 ∧ (ky : ℤ) - ↑t - 2 ≤ ↑t) := by omega
      rw [if_neg hkx, if_neg hbox]
  · rw [if_neg hky, lookupL_replicate_same]
    unfold getCell
    have hbox : ¬(-(t : ℤ) ≤ (kx : ℤ) - ↑t - 2 ∧ (kx : ℤ) - ↑t - 2 ≤ ↑t ∧
        -(t : ℤ) ≤ (ky : ℤ) - ↑t - 2 ∧ (ky : ℤ) - ↑t - 2 ≤ ↑t) := by omega
    rw [if_neg hbox]

lemma list_eq_of_lookupL {α : Type} (xs ys : List α) (d : α)
    (hlen : xs.length = ys.length) (hget : ∀ i < xs.length, lookupL xs i d = lookupL ys i d) :
    xs = ys := by
  induction xs generalizing ys with
  | nil => symm; exact List.length_eq_zero_iff.mp hlen.symm
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      have h0 := hget 0 (by simp)
      simp only [lookupL] at h0
      rw [h0]
      congr 1
      exact ih ys (by simp at hlen; exact hlen) (fun i hi => hget (i + 1) (by simp; omega))

lemma flatMap_pure_map {α β γ : Type} (xs : List α) (c : α → β) (f : β → γ) :
    List.map f (List.flatMap (fun a => [c a]) xs) = List.map (fun a => f (c a)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

lemma stageCfg_eq_cfg (t : ℕ) : stageCfg 123 t = cfg t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [stageCfg, ih]
    change stepCfg 123 t (cfg t) = nextCfg t (cfg t)
    unfold stepCfg nextCfg
    dsimp only
    refine Prod.ext rfl ?_
    simp only [List.bind_eq_flatMap, List.pure_def, flatMap_pure_map]
    have hwf := cfg_wf t
    have hp := padded_wf t (cfg t) hwf
    have hsg := length_stepGrid _ (2 * (t + 1) + 1) (2 * (t + 1) + 1) hp.1 hp.2
    symm
    apply list_eq_of_lookupL _ _ [] (by rw [hsg.1, List.length_map, List.length_range])
    intro iy hiy
    rw [hsg.1] at hiy
    rw [lookupL_eq_getD ((List.range (2 * (t + 1) + 1)).map _),
        List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hiy]
    dsimp only [Option.map_some, Option.getD_some]
    apply list_eq_of_lookupL _ _ (cfg t).1
    · rw [hsg.2 _ (lookupL_in_mem _ iy [] (by rw [hsg.1]; exact hiy)),
          List.length_map, List.length_range]
    · intro ix hix
      have hrow_len : (lookupL (stepGrid (pad1 (List.replicate (2 * t + 5) (cfg t).1)
          ((cfg t).2.map (pad1 (cfg t).1)))) iy []).length = 2 * (t + 1) + 1 :=
        hsg.2 _ (lookupL_in_mem _ iy [] (by rw [hsg.1]; exact hiy))
      rw [hrow_len] at hix
      rw [lookupL_stepGrid _ (2 * (t + 1) + 1) (2 * (t + 1) + 1) iy ix (cfg t).1
        hp.1 hp.2 hiy hix]
      rw [lookupL_padded t (cfg t) hwf (iy + 1) (ix + 1),
          lookupL_padded t (cfg t) hwf iy (ix + 1),
          lookupL_padded t (cfg t) hwf (iy + 2) (ix + 1),
          lookupL_padded t (cfg t) hwf (iy + 1) ix,
          lookupL_padded t (cfg t) hwf (iy + 1) (ix + 2)]
      rw [lookupL_eq_getD ((List.range (2 * (t + 1) + 1)).map _),
          List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hix]
      dsimp only [Option.map_some, Option.getD_some]
      have cx : ((ix + 1 : ℕ) : ℤ) - ↑t - 2 = (ix : ℤ) - ↑(t + 1) := by omega
      have cy : ((iy + 1 : ℕ) : ℤ) - ↑t - 2 = (iy : ℤ) - ↑(t + 1) := by omega
      have ny : (iy : ℤ) - ↑t - 2 = ((iy : ℤ) - ↑(t + 1)) - 1 := by omega
      have sy : ((iy + 2 : ℕ) : ℤ) - ↑t - 2 = ((iy : ℤ) - ↑(t + 1)) + 1 := by omega
      have wx : (ix : ℤ) - ↑t - 2 = ((ix : ℤ) - ↑(t + 1)) - 1 := by omega
      have ex : ((ix + 2 : ℕ) : ℤ) - ↑t - 2 = ((ix : ℤ) - ↑(t + 1)) + 1 := by omega
      rw [cx, cy, ny, sy, wx, ex]

def countRow : List Bool → ℕ
  | [] => 0
  | true :: bs => countRow bs + 1
  | false :: bs => countRow bs

lemma countRow_eq (bs : List Bool) : bs.count true = countRow bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [countRow, ih]

def countGrid : List (List Bool) → ℕ
  | [] => 0
  | r :: rs => countGrid rs + countRow r

lemma countOn_eq_fast (t : ℕ) : countOn 123 t = countGrid (cfg t).2 := by
  unfold countOn
  rw [stageCfg_eq_cfg]
  induction (cfg t).2 with
  | nil => rfl
  | cons r rs ih => rw [List.map_cons, List.sum_cons, ih, countRow_eq, countGrid, Nat.add_comm]

end Disproof_a270211

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 200000 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a270211.main) := by
  intro h
  have h6 := h 6 (by decide)
  have hv6 : OMA.S_oeis_a270211.a 6 = 14809 := by
    change OMA.S_oeis_a270211.countOn 123 63 = 14809
    rw [countOn_eq_fast]
    decide +kernel
  rw [hv6] at h6
  norm_num at h6
