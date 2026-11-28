import OMAReductions.R_Erdos114_erdos_114_variants_large_n_R1
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Mathlib.Algebra.Polynomial.Taylor

/-! The analytic steps are Lemmas 4–6 of Eremenko and Hayman, arXiv:0805.2295.
The translation and rotation in Tao's Proposition 1.2 are proved below. -/

namespace OMA.R_Erdos114_erdos_114_variants_large_n_R1_H1_R1

open Polynomial Erdos114 MeasureTheory

-- Attainment of the maximum over monic polynomials of fixed positive degree.
def H1 : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ p : ℂ[X],
    p.Monic ∧ p.natDegree = n ∧
    (∀ r : ℂ[X], r.Monic → r.natDegree = n →
      lemniscateLength r ≤ lemniscateLength p)

-- Deform an extremizer at constant length until all critical values are on the unit circle.
def H2 : Prop :=
  ∀ p : ℂ[X], p.Monic → 1 ≤ p.natDegree →
    (∀ r : ℂ[X], r.Monic → r.natDegree = p.natDegree →
      lemniscateLength r ≤ lemniscateLength p) →
    ∃ q : ℂ[X], q.Monic ∧ q.natDegree = p.natDegree ∧
      lemniscateLength q = lemniscateLength p ∧
      ∀ z : ℂ, q.derivative.eval z = 0 → z ∈ lemniscate q

-- When all critical values are on the unit circle, the lemniscate is connected.
def H3 : Prop :=
  ∀ p : ℂ[X], 1 ≤ p.natDegree →
    (∀ z : ℂ, p.derivative.eval z = 0 → z ∈ lemniscate p) →
    IsConnected (lemniscate p)

lemma penultimate_taylor {p : ℂ[X]} (hp : p.Monic) (hn : 1 ≤ p.natDegree) (b : ℂ) :
    (p.taylor b).coeff (p.natDegree - 1) =
      p.coeff (p.natDegree - 1) + (p.natDegree : ℂ) * b := by
  let n := p.natDegree - 1
  have hn' : 1 + n = p.natDegree := by dsimp [n]; omega
  have hchoose : p.natDegree.choose n = p.natDegree := by
    rw [← hn', Nat.add_comm 1 n, Nat.choose_succ_self_right]
  have h : hasseDeriv n p = C (p.coeff n) + C (p.natDegree : ℂ) * X := by
    ext i
    rw [hasseDeriv_coeff, coeff_add, coeff_C_mul]
    rcases i with _ | i
    · simp
    rcases i with _ | i
    · rw [hn', hchoose, coeff_natDegree, hp.leadingCoeff]
      simp
    · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_X, if_neg (by omega)]
      simp
  change (p.taylor b).coeff n = p.coeff n + (p.natDegree : ℂ) * b
  rw [taylor_coeff, h]
  simp

lemma taylor_geometry (p : ℂ[X]) (b : ℂ) :
    lemniscateLength (p.taylor b) = lemniscateLength p ∧
    (IsConnected (lemniscate p) → IsConnected (lemniscate (p.taylor b))) ∧
    ((∀ z : ℂ, p.derivative.eval z = 0 → z ∈ lemniscate p) →
      (∀ z : ℂ, (p.taylor b).derivative.eval z = 0 → z ∈ lemniscate (p.taylor b))) := by
  let e := IsometryEquiv.addRight b
  have hset : lemniscate (p.taylor b) = e ⁻¹' lemniscate p := by
    ext z
    simp [lemniscate, taylor_apply, e, eval_comp]
  refine ⟨?_, ?_, ?_⟩
  · rw [lemniscateLength, hset, e.hausdorffMeasure_preimage]
    rfl
  · intro h
    rw [hset]
    exact e.toHomeomorph.isConnected_preimage.mpr h
  · intro h z hz
    have hv : p.derivative.eval (z + b) = 0 := by
      simpa [taylor_apply, derivative_comp, eval_comp] using hz
    rw [hset]
    exact h _ hv

lemma derivative_scale (p : ℂ[X]) (a : ℂ) :
    (p.scaleRoots a).derivative = p.derivative.scaleRoots a := by
  ext i
  rw [coeff_derivative, coeff_scaleRoots, coeff_scaleRoots, coeff_derivative, natDegree_derivative]
  rw [show p.natDegree - (i + 1) = p.natDegree - 1 - i by omega]
  ring

lemma scale_geometry (p : ℂ[X]) (a : ℂ) (ha : ‖a‖ = 1) :
    lemniscateLength (p.scaleRoots a) = lemniscateLength p ∧
    (IsConnected (lemniscate p) → IsConnected (lemniscate (p.scaleRoots a))) ∧
    ((∀ z : ℂ, p.derivative.eval z = 0 → z ∈ lemniscate p) →
      (∀ z : ℂ, (p.scaleRoots a).derivative.eval z = 0 → z ∈ lemniscate (p.scaleRoots a))) := by
  have ha₀ : a ≠ 0 := by
    intro h
    simp [h] at ha
  let e : ℂ ≃ᵢ ℂ :=
    ⟨Equiv.mulLeft₀ a ha₀, Isometry.of_dist_eq fun x y => by
      change dist (a * x) (a * y) = dist x y
      rw [dist_eq_norm, dist_eq_norm, ← mul_sub, norm_mul, ha, one_mul]⟩
  have hset : e ⁻¹' lemniscate (p.scaleRoots a) = lemniscate p := by
    ext z
    change ‖(p.scaleRoots a).eval (a * z)‖ = 1 ↔ ‖p.eval z‖ = 1
    rw [scaleRoots_eval_mul, norm_mul, norm_pow, ha, one_pow, one_mul]
  refine ⟨?_, ?_, ?_⟩
  · have hm := e.hausdorffMeasure_preimage 1 (lemniscate (p.scaleRoots a))
    rw [hset] at hm
    exact hm.symm
  · intro hc
    exact e.toHomeomorph.isConnected_preimage.mp (hset.symm ▸ hc)
  · intro hc z hz
    obtain ⟨w, rfl⟩ := e.surjective z
    change (p.scaleRoots a).derivative.eval (a * w) = 0 at hz
    rw [derivative_scale, scaleRoots_eval_mul] at hz
    have hroot := (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ ha₀)
    have hw : w ∈ e ⁻¹' lemniscate (p.scaleRoots a) := hset.symm ▸ hc _ hroot
    exact hw

lemma unit_root_rotate (z : ℂ) {n : ℕ} (hn : 0 < n) :
    ∃ a : ℂ, ‖a‖ = 1 ∧ a ^ n * z = - (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · exact ⟨1, by simp, by simp [hz]⟩
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (- (‖z‖ : ℂ) / z) hn
  have hpow : ‖a‖ ^ n = (1 : ℝ) ^ n := by
    rw [← norm_pow, ha]
    simp [norm_ne_zero_iff.mpr hz]
  exact ⟨a, (pow_left_inj₀ (norm_nonneg _) zero_le_one hn.ne').mp hpow,
    ((div_eq_iff hz).mp ha.symm).symm⟩

lemma normalize (p : ℂ[X]) (hp : p.Monic) (hn : 1 ≤ p.natDegree) :
    ∃ q : ℂ[X], q.Monic ∧ q.natDegree = p.natDegree ∧ q.coeff (p.natDegree - 1) = 0 ∧
    (q.eval 0).im = 0 ∧ (q.eval 0).re ≤ 0 ∧ lemniscateLength q = lemniscateLength p ∧
    (IsConnected (lemniscate p) → IsConnected (lemniscate q)) ∧
    ((∀ z : ℂ, p.derivative.eval z = 0 → z ∈ lemniscate p) →
      (∀ z : ℂ, q.derivative.eval z = 0 → z ∈ lemniscate q)) := by
  let b : ℂ := -p.coeff (p.natDegree - 1) / (p.natDegree : ℂ)
  let t := p.taylor b
  have htdeg : t.natDegree = p.natDegree := natDegree_taylor p b
  have htmonic : t.Monic := by unfold Monic; simpa [t] using hp.leadingCoeff
  have htc : t.coeff (p.natDegree - 1) = 0 := by
    have hn₀ : (p.natDegree : ℂ) ≠ 0 := by exact_mod_cast (show p.natDegree ≠ 0 by omega)
    dsimp [t]
    rw [penultimate_taylor hp hn]
    dsimp [b]
    field_simp
    ring
  obtain ⟨a, ha, ha0⟩ := unit_root_rotate (t.eval 0) (n := t.natDegree) (htdeg.symm ▸ hn)
  let q := t.scaleRoots a
  have hq0 : q.eval 0 = - (‖t.eval 0‖ : ℂ) := by
    simpa [q] using (scaleRoots_eval_mul t 0 a).trans ha0
  obtain ⟨htlen, htconn, htcrit⟩ := taylor_geometry p b
  obtain ⟨hqlen, hqconn, hqcrit⟩ := scale_geometry t a ha
  exact ⟨q, (monic_scaleRoots_iff _).mpr htmonic, (natDegree_scaleRoots _ _).trans htdeg,
    by simp [q, htc], by simp [hq0], by simp [hq0], hqlen.trans htlen,
    hqconn ∘ htconn, hqcrit ∘ htcrit⟩


theorem main : H1 → H2 → H3 → OMA.R_Erdos114_erdos_114_variants_large_n_R1.H1 := by
  intro hExist hDeform hConnected n hn
  obtain ⟨p, hp, hpdeg, hpmax⟩ := hExist n hn
  obtain ⟨q, hq, hqdeg, hqlen, hqcrit⟩ :=
    hDeform p hp (hpdeg.symm ▸ hn) (fun r hr hd => hpmax r hr (hd.trans hpdeg))
  have hqn : q.natDegree = n := hqdeg.trans hpdeg
  have hqpos : 1 ≤ q.natDegree := hqn.symm ▸ hn
  obtain ⟨r, hr, hrdeg, hcoeff, him, hre, hrlen, hconn, hcrit⟩ :=
    normalize q hq hqpos
  refine ⟨r, hr, hrdeg.trans hqn, hqn ▸ hcoeff, him, hre,
    hconn (hConnected q hqpos hqcrit), hcrit hqcrit, ?_⟩
  rw [hrlen, hqlen]
  exact hpmax

end OMA.R_Erdos114_erdos_114_variants_large_n_R1_H1_R1
