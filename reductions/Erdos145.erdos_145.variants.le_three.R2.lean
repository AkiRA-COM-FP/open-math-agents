import FormalConjectures.ErdosProblems.«145»
import Mathlib

/-!
Convergence of squarefree-gap moments up to the cubic endpoint from fixed-gap
frequencies and uniform decay of the cubic tail.
Credit: @Pasx71.

The Cauchy argument is adapted from the accepted proof in PR 4712 of the
project, itself based on the frequency-and-tail reduction in PR 3976.
The cubic tail is an independent hypothesis, not an asserted theorem here.
-/

namespace OMA.R_Erdos145_erdos_145_variants_le_three_R2

open Filter Finset Erdos145
open scoped Topology BigOperators

/-- Each fixed gap size has a limiting frequency. -/
def H1 : Prop := ∀ k : ℕ, ∃ d : ℝ,
  Tendsto (fun x : ℝ => 1/x * (((A x).filter
    (fun n => s (n+1)-s n = k)).card : ℝ)) atTop (𝓝 d)

/-- Contributions of sufficiently large gaps to the cubic moment vanish uniformly. -/
def H2 : Prop := ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, 0 < K ∧
  ∀ᶠ x : ℝ in atTop, 1/x * ∑ n ∈ (A x).filter
    (fun n => ¬ s (n+1)-s n < K), ((s (n+1)-s n : ℕ) : ℝ)^3 ≤ ε

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
  intro freq tail
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
