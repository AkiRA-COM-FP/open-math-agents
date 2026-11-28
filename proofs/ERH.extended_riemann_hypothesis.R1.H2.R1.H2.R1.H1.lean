import OMAReductions.R_ERH_extended_riemann_hypothesis_R1_H2_R1_H2_R1
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Factorization.Basic

/-! Coefficients of the squarefree ideal product have subpolynomial growth.
Only the distinct rational prime divisors of the norm affect the count. -/
-- Credit: @STARDUSTLC666
noncomputable section
namespace OMA.SquarefreeCoefficientBound
open Filter Asymptotics NumberField
open scoped NumberField Topology Classical
variable (K : Type*) [Field K] [NumberField K]

abbrev Primes := {I : Ideal (𝓞 K) // I.IsPrime ∧ I ≠ ⊥}
def normProduct (S : Finset (Primes K)) : ℕ := ∏ p ∈ S, Ideal.absNorm p.val
def signedCoeff (n : ℕ) : ℂ := ∑' S : normProduct K ⁻¹' {n}, (-1 : ℂ)^S.val.card

def above (p : ℕ) := IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 K)

theorem card_above {p : ℕ} (hp : p.Prime) : (above K p).card ≤ Module.finrank ℚ K := by
  have : Fact p.Prime := ⟨hp⟩
  let J : Ideal ℤ := Ideal.span {(p : ℤ)}
  have hJ : J ≠ ⊥ := by simpa [J] using (Nat.cast_ne_zero.mpr hp.ne_zero : (p : ℤ) ≠ 0)
  have he : (↑(above K p) : Set (Ideal (𝓞 K))) = J.primesOver (𝓞 K) :=
    IsDedekindDomain.coe_primesOverFinset hJ (𝓞 K)
  let _ : Fintype (J.primesOver (𝓞 K)) := (IsDedekindDomain.primesOver_finite J (𝓞 K)).fintype
  calc
    (above K p).card = Fintype.card (J.primesOver (𝓞 K)) := by
      rw [← Fintype.card_coe]
      exact Fintype.card_congr (Equiv.setCongr he)
    _ = ∑ _q : J.primesOver (𝓞 K), 1 := by simp
    _ ≤ ∑ q : J.primesOver (𝓞 K), q.val.ramificationIdx ℤ * q.val.inertiaDeg ℤ := by
      apply Finset.sum_le_sum
      intro q _
      have : q.val.IsPrime := q.property.1
      exact Nat.mul_pos (q.val.ramificationIdx_pos ℤ) (q.val.inertiaDeg_pos ℤ)
    _ = Module.finrank ℤ (𝓞 K) := Ideal.sum_ramification_inertia_eq_finrank J (𝓞 K)
    _ = _ := NumberField.RingOfIntegers.rank K

theorem support_at_norm {n : ℕ} (hn : 0 < n) (S : Finset (Primes K))
    (hS : normProduct K S = n) {q : Primes K} (hq : q ∈ S) :
    q.val ∈ n.primeFactors.biUnion (above K) := by
  have : q.val.IsMaximal := q.property.1.isMaximal q.property.2
  obtain ⟨p, f, hf, hmem, hp, hnorm⟩ := Ideal.exists_prime_and_absNorm_eq_pow q.val
  have hdiv : p ∣ n := by
    rw [← hS]
    apply dvd_trans _ (Finset.dvd_prod_of_mem (fun q : Primes K => q.val.absNorm) hq)
    rw [hnorm]
    exact dvd_pow_self p hf.ne'
  have : Fact p.Prime := ⟨hp⟩
  have hbot : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    simpa using (Nat.cast_ne_zero.mpr hp.ne_zero : (p : ℤ) ≠ 0)
  refine Finset.mem_biUnion.mpr ⟨p, hp.mem_primeFactors hdiv hn.ne', ?_⟩
  apply (IsDedekindDomain.mem_primesOverFinset_iff hbot (𝓞 K)).mpr
  refine ⟨q.property.1, (Ideal.liesOver_span_iff q.property.1.ne_top
    (Nat.prime_iff_prime_int.mp hp)).mpr ?_⟩
  simpa using hmem

theorem coefficient_count {n : ℕ} (hn : 0 < n) :
    ‖signedCoeff K n‖ ≤ ((2 : ℝ)^(Module.finrank ℚ K))^n.primeFactors.card := by
  let U := n.primeFactors.biUnion (above K)
  have hu : U.card ≤ n.primeFactors.card * Module.finrank ℚ K :=
    Finset.card_biUnion_le_card_mul _ _ _ fun p hp => card_above K (Nat.mem_primeFactors.mp hp).1
  let e : Primes K ↪ Ideal (𝓞 K) := Function.Embedding.subtype _
  let enc (S : normProduct K ⁻¹' {n}) : U.powerset := ⟨S.val.map e, by
    apply Finset.mem_powerset.mpr
    intro I hI
    obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hI
    exact support_at_norm K hn S.val S.property hq⟩
  have hi : Function.Injective enc := fun S T h =>
    Subtype.ext (Finset.map_injective e (congrArg Subtype.val h))
  let _ : Fintype (normProduct K ⁻¹' {n}) := Fintype.ofInjective enc hi
  have hc := Fintype.card_le_of_injective enc hi
  simp only [Fintype.card_coe, Finset.card_powerset] at hc
  calc
    ‖signedCoeff K n‖ ≤ ∑ S : normProduct K ⁻¹' {n}, ‖(-1 : ℂ)^S.val.card‖ := by
      rw [signedCoeff, tsum_fintype]
      exact norm_sum_le _ _
    _ = (Fintype.card (normProduct K ⁻¹' {n}) : ℝ) := by simp
    _ ≤ ((2^U.card : ℕ) : ℝ) := by exact_mod_cast hc
    _ ≤ _ := by
      push_cast
      rw [← pow_mul, Nat.mul_comm (Module.finrank ℚ K)]
      exact pow_le_pow_right₀ (by norm_num) hu

/-- A fixed factor per distinct prime is absorbed by any positive power of the integer. -/
theorem prime_factor_power (D : ℝ) (hD : 1 ≤ D) {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℝ, ∀ n : ℕ, 0 < n → D^n.primeFactors.card ≤ B*(n : ℝ)^ε := by
  have ht := (tendsto_rpow_atTop hε).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨T, hT⟩ := eventually_atTop.mp (ht.eventually_ge_atTop D)
  refine ⟨D^T, ?_⟩
  intro n hn
  let small := n.primeFactors.filter (· < T)
  let large := n.primeFactors \ small
  have hs : small ⊆ n.primeFactors := Finset.filter_subset _ _
  have hl : large ⊆ n.primeFactors := Finset.sdiff_subset
  have hsT : small.card ≤ T := by
    simpa using Finset.card_le_card (show small ⊆ Finset.range T from
      fun p hp => Finset.mem_range.mpr (Finset.mem_filter.mp hp).2)
  have hlarge : D^large.card ≤ (n : ℝ)^ε := by
    calc
      _ = ∏ _p ∈ large, D := by simp
      _ ≤ ∏ p ∈ large, (p : ℝ)^ε := by
        apply Finset.prod_le_prod (fun _ _ => zero_le_one.trans hD)
        intro p hp
        obtain ⟨hp', hsmall⟩ := Finset.mem_sdiff.mp hp
        exact hT p (le_of_not_gt fun h => hsmall (Finset.mem_filter.mpr ⟨hp', h⟩))
      _ = ((∏ p ∈ large, p : ℕ) : ℝ)^ε := by
        rw [Real.finsetProd_rpow large (fun p : ℕ => (p : ℝ)) (fun p _ => Nat.cast_nonneg p)]
        simp
      _ ≤ _ := by
        apply Real.rpow_le_rpow (Nat.cast_nonneg _) _ hε.le
        exact_mod_cast Nat.le_of_dvd hn ((Finset.prod_dvd_prod_of_subset _ _ id hl).trans n.prod_primeFactors_dvd)
  rw [← Finset.card_sdiff_add_card_eq_card hs, pow_add, mul_comm]
  exact mul_le_mul (pow_le_pow_right₀ hD hsT) hlarge (pow_nonneg (zero_le_one.trans hD) _)
    (pow_nonneg (zero_le_one.trans hD) _)

theorem subpolynomial {ε : ℝ} (hε : 0 < ε) :
    signedCoeff K =O[atTop] fun n : ℕ => (n : ℝ)^ε := by
  obtain ⟨B, hB⟩ := prime_factor_power ((2 : ℝ)^(Module.finrank ℚ K))
    (one_le_pow₀ (by norm_num)) hε
  apply IsBigO.of_bound B
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) ε)]
  exact (coefficient_count K hn).trans (hB n hn)

end OMA.SquarefreeCoefficientBound

theorem OMA.solution : OMA.R_ERH_extended_riemann_hypothesis_R1_H2_R1_H2_R1.H1 := by
  intro K _ _ P N a ε hε
  exact OMA.SquarefreeCoefficientBound.subpolynomial K hε
