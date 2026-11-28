import FormalConjectures.ErdosProblems.«145»
import Mathlib

/-!
Convergence of squarefree-gap moments for exponents from zero through three.

The remaining analytic input is a linear upper bound for the order-7/2
moment of completed gaps, as in Chan, arXiv:2310.08448, equation (3).
Bertrand's postulate includes the gap crossing the cutoff by doubling it.
The fixed-gap frequencies have a proof in PR 4209. The Cauchy argument
adapts the truncation proofs in PRs 3976 and 4712.
-/
-- Credit: @Pasx71

namespace OMA.R_Erdos145_erdos_145_variants_le_three_R2

open Filter Finset Erdos145
open scoped Topology BigOperators

/-- Each fixed gap size has a limiting frequency. -/
def H1 : Prop := ∀ k : ℕ, ∃ d : ℝ,
  Tendsto (fun x : ℝ => 1/x * (((A x).filter
    (fun n => s (n+1)-s n = k)).card : ℝ)) atTop (𝓝 d)

/-- An eventual bound for the moment of order seven halves over completed gaps.
The weight is written as the cube of the gap times its square root. -/
def H2 : Prop := ∃ C : ℝ, 0 < C ∧ ∀ᶠ y : ℝ in atTop,
  (∑ n ∈ (A y).filter (fun n => s (n+1) ≤ ⌊y⌋₊),
    ((s (n+1)-s n : ℕ) : ℝ)^3 * Real.sqrt ((s (n+1)-s n : ℕ) : ℝ)) ≤ C*y

/-- Every squarefree gap counted at x is completed by 2x. -/
lemma next_le_double {x : ℝ} (hx : 1 ≤ x) {n : ℕ} (hn : n ∈ A x) :
    s (n+1) ≤ ⌊2*x⌋₊ := by
  have hfloor : 1 ≤ ⌊x⌋₊ := (Nat.one_le_floor_iff x).2 hx
  obtain ⟨p, hp, hgt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul ⌊x⌋₊ (by omega)
  have hleft : s n ≤ ⌊x⌋₊ := (Finset.mem_Icc.mp (Finset.mem_preimage.mp hn)).2
  have hnext : s (n+1) ≤ p := by
    by_contra! h
    have hback : p ≤ s n := Nat.le_nth_of_lt_nth_succ h hp.squarefree
    omega
  apply (Nat.le_floor_iff (by linarith : 0 ≤ 2*x)).2
  have hnat := hnext.trans hle
  have hreal : (s (n+1) : ℝ) ≤ 2*(⌊x⌋₊ : ℝ) := by exact_mod_cast hnat
  linarith [Nat.floor_le (by linarith : 0 ≤ x)]

lemma cubic_tail (moment : H2) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, 0 < K ∧ ∀ᶠ x : ℝ in atTop, 1/x * ∑ n ∈ (A x).filter
      (fun n => ¬ s (n+1)-s n < K), ((s (n+1)-s n : ℕ) : ℝ)^3 ≤ ε := by
  classical
  obtain ⟨C,hC,bounded⟩ := moment
  obtain ⟨L,hL⟩ := exists_nat_gt (2*C/ε)
  have hLpos : (0:ℝ) < L := lt_trans (by positivity) hL
  have hLn : 0 < L := by exact_mod_cast hLpos
  have hscale : 2*C ≤ ε*L := by linarith [(div_lt_iff₀ hε).mp hL]
  obtain ⟨Y,hY⟩ := eventually_atTop.mp bounded
  refine ⟨L^2, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (max Y 1)] with x hx
  have hx1 : 1 ≤ x := (le_max_right _ _).trans hx
  have hxpos : 0 < x := by linarith
  have hbound := hY (2*x) (by linarith [(le_max_left Y 1).trans hx])
  let g (n : ℕ) : ℝ := ((s (n+1)-s n : ℕ) : ℝ)
  let T := (A x).filter (fun n => ¬ s (n+1)-s n < L^2)
  let D := (A (2*x)).filter (fun n => s (n+1) ≤ ⌊2*x⌋₊)
  have hsub : T ⊆ D := by
    intro n hn
    have hleft := (mem_filter.mp hn).1
    apply mem_filter.mpr
    refine ⟨?_, next_le_double hx1 hleft⟩
    apply mem_preimage.mpr
    exact mem_Icc.mpr ⟨Nat.zero_le _, ((mem_Icc.mp (mem_preimage.mp hleft)).2).trans
      (Nat.floor_mono (by linarith : x ≤ 2*x))⟩
  have hscaled : (L:ℝ) * (∑ n ∈ T, g n ^ 3) ≤ C*(2*x) := by
    calc
      _ = ∑ n ∈ T, (L:ℝ) * g n ^ 3 := mul_sum ..
      _ ≤ ∑ n ∈ T, g n ^ 3 * Real.sqrt (g n) := by
        apply sum_le_sum
        intro n hn
        have hn' : L^2 ≤ s (n+1)-s n := not_lt.mp (mem_filter.mp hn).2
        have hr : (L:ℝ)^2 ≤ g n := by dsimp [g]; exact_mod_cast hn'
        have hs := Real.sqrt_le_sqrt hr
        rw [Real.sqrt_sq hLpos.le] at hs
        rw [mul_comm (L:ℝ)]
        exact mul_le_mul_of_nonneg_left hs (by dsimp [g]; positivity)
      _ ≤ ∑ n ∈ D, g n ^ 3 * Real.sqrt (g n) :=
        sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by dsimp [g]; positivity)
      _ ≤ _ := hbound
  change 1/x * (∑ n ∈ T, g n ^ 3) ≤ ε
  rw [one_div, ← div_eq_inv_mul, div_le_iff₀ hxpos]
  apply le_of_mul_le_mul_left _ hLpos
  calc
    _ ≤ C*(2*x) := hscaled
    _ ≤ L*(ε*x) := by nlinarith only [mul_le_mul_of_nonneg_right hscale hxpos.le]

lemma sumByGapSize (D : Finset ℕ) (g : ℕ → ℕ) (a : ℝ) (K : ℕ) :
    (∑ k ∈ range K, ((D.filter fun n => g n=k).card : ℝ) * (k:ℝ)^a) =
    ∑ n ∈ D.filter (fun n => g n < K), (g n:ℝ)^a := by
  calc
    _ = ∑ k ∈ range K, ∑ n ∈ D.filter (fun n => g n=k), (g n:ℝ)^a := by
      apply sum_congr rfl
      intro k _
      rw [← nsmul_eq_mul,← sum_const]
      apply sum_congr rfl
      intro n hn
      rw [(mem_filter.mp hn).2]
    _ = _ := by simpa only [mem_range] using sum_fiberwise_eq_sum_filter D (range K) g (fun n => (g n:ℝ)^a)

theorem main : H1 → H2 → type_of% @Erdos145.erdos_145.variants.le_three := by
  classical
  intro freq moment
  have tail := cubic_tail moment
  intro a ha
  let g (n : ℕ) := s (n+1) - s n
  have hg (n : ℕ) : ((g n : ℕ) : ℝ) = (s (n+1) : ℝ) - s n :=
    Nat.cast_sub ((Nat.nth_strictMono Nat.squarefree_infinite).monotone (Nat.le_succ n))
  let f (x : ℝ) := (1/x) * ∑ n ∈ A x, (g n:ℝ)^a
  suffices h : ∃ β, Tendsto f atTop (𝓝 β) by simpa only [f,hg] using h
  choose d hd using freq
  let T (K : ℕ) (x : ℝ) := ∑ k ∈ range K, (1/x * ((A x).filter fun n => g n=k).card) * (k:ℝ)^a
  have tend (K : ℕ) : Tendsto (T K) atTop (𝓝 (∑ k ∈ range K, d k*(k:ℝ)^a)) :=
    tendsto_finsetSum _ (fun k _ => (hd k).mul_const _)
  have terr (K : ℕ) (ε : ℝ) (hK : 0 < K)
      (hT : ∀ᶠ x : ℝ in atTop, 1/x * ∑ n ∈ (A x).filter (fun n => ¬ s (n+1) - s n < K),
        ((s (n+1) - s n : ℕ) : ℝ)^3 ≤ ε) :
      ∀ᶠ x : ℝ in atTop, |f x - T K x| ≤ ε := by
    filter_upwards [hT, eventually_gt_atTop (0:ℝ)] with x hb hx
    have te : T K x = (1/x) * ∑ n ∈ (A x).filter (fun n => g n < K), (g n:ℝ)^a := by
      unfold T
      rw [← sumByGapSize (A x) g a K, mul_sum]
      exact sum_congr rfl (fun k _ => by ring)
    let D := (A x).filter (fun n => ¬ g n < K)
    have split := sum_filter_add_sum_filter_not (A x) (fun n => g n < K) (fun n => (g n:ℝ)^a)
    have diff : f x - T K x = (1/x) * ∑ n ∈ D, (g n:ℝ)^a := by
      rw [te]
      unfold f
      dsimp [D]
      rw [← split, mul_add]
      ring
    have hKr : (1:ℝ) ≤ K := by exact_mod_cast hK
    have hsum : ∑ n ∈ D, (g n:ℝ)^a ≤ ∑ n ∈ D, (g n:ℝ)^3 := by
      apply sum_le_sum
      intro n hn
      have h1 : (K:ℝ) ≤ g n := by exact_mod_cast (not_lt.mp (mem_filter.mp hn).2)
      have h1' : (1:ℝ) ≤ g n := hKr.trans h1
      calc (g n:ℝ)^a ≤ (g n:ℝ)^(3:ℝ) := Real.rpow_le_rpow_of_exponent_le h1' ha.2
        _ = (g n:ℝ)^3 := Real.rpow_natCast _ 3
    have hnn : 0 ≤ f x - T K x := by
      rw [diff]
      exact mul_nonneg (by positivity) (sum_nonneg (fun n _ => by positivity))
    rw [abs_of_nonneg hnn, diff]
    calc (1/x) * ∑ n ∈ D, (g n:ℝ)^a ≤ (1/x) * ∑ n ∈ D, (g n:ℝ)^3 :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ ε := hb
  apply cauchySeq_tendsto_of_complete
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨K, hK, hTail⟩ := tail (ε/4) (by linarith)
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp (tend K).cauchySeq (ε/2) (by linarith)
  obtain ⟨M, hM⟩ := eventually_atTop.mp (terr K (ε/4) hK hTail)
  refine ⟨max N M, ?_⟩
  intro x hx y hy
  have ht := hN x (le_trans (le_max_left _ _) hx) y (le_trans (le_max_left _ _) hy)
  have h₁ := hM x (le_trans (le_max_right _ _) hx)
  have h₂ := hM y (le_trans (le_max_right _ _) hy)
  rw [Real.dist_eq] at ht ⊢
  rw [abs_le] at h₁ h₂
  rw [abs_lt] at ht ⊢
  constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2, ht.1, ht.2]

end OMA.R_Erdos145_erdos_145_variants_le_three_R2
