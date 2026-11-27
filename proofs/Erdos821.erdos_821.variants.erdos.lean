import FormalConjectures.ErdosProblems.«821»
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
A smooth shifted-prime supply and a power lower bound for totient fibers.
The affine sieve is included in full. The problem-specific counting argument
begins in namespace Erdos821Design after the sieve.

The prime-sum and sieve estimates adapt the Erdős 16 Romanoff proof by Devin
Robison (PR 4564) and Steven Enamakel's development (PR 2460). The Euler
product estimate comes from Ian Qvist's Erdős 856 proof (PR 1907), and the
divisor estimate for the singular factor from Marcus Buffett's Erdős 971
proof (PR 3352). The squarefree subset, smooth-box, and collision arguments
generalize zarnab222-dev's first Erdős 821 reduction (PR 1162).
-/

section AffineSieveProof
open scoped Classical

namespace OMALib.Mertens

open Real Finset

theorem log_factorial_eq_sum (N : ℕ) :
    Real.log (N.factorial : ℝ) =
      ∑ p ∈ Nat.primesLE N, ((N.factorial.factorization p : ℕ) : ℝ) * Real.log p := by
  rw [Real.log_nat_eq_sum_factorization]
  apply Finsupp.sum_of_support_subset
  · intro p hp
    rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
    rw [Nat.mem_primesLE]
    exact ⟨(Nat.Prime.dvd_factorial hp.1).1 hp.2.1, hp.1⟩
  · intro p _
    simp

theorem div_le_factorization_factorial {p : ℕ} (hp : p.Prime) (N : ℕ) :
    N / p ≤ N.factorial.factorization p := by
  rcases lt_or_ge N p with h | h
  · simp [Nat.div_eq_of_lt h]
  rw [Nat.factorization_factorial hp (Nat.lt_add_one (Nat.log p N))]
  have h1 : 1 ∈ Ico 1 (Nat.log p N + 1) := by
    simp only [mem_Ico, le_refl, true_and]
    have := Nat.log_pos hp.one_lt h
    omega
  have := Finset.single_le_sum (f := fun i => N / p ^ i) (fun i _ => Nat.zero_le _) h1
  simpa using this

theorem real_div_sub_one_le_nat_div (N p : ℕ) (hp : 0 < p) :
    (N : ℝ) / p - 1 ≤ ((N / p : ℕ) : ℝ) := by
  have h := Nat.lt_div_mul_add (a := N) hp
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have h2 : (N : ℝ) < ((N / p : ℕ) : ℝ) * p + p := by exact_mod_cast h
  rw [div_sub_one hp'.ne', div_le_iff₀ hp']
  linarith

theorem log_factorial_le (N : ℕ) : Real.log (N.factorial : ℝ) ≤ N * Real.log N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  rw [← Real.log_pow]
  apply Real.log_le_log (by exact_mod_cast Nat.factorial_pos N)
  exact_mod_cast Nat.factorial_le_pow N

theorem sum_log_div_le_nat (N : ℕ) :
    ∑ p ∈ Nat.primesLE N, Real.log p / p ≤ Real.log N + Real.log 4 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [Nat.primesLE_zero, Finset.sum_empty, Nat.cast_zero, Real.log_zero, zero_add]
    exact Real.log_nonneg (by norm_num)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have key : ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p - 1) ≤ Real.log (N.factorial : ℝ) := by
    rw [log_factorial_eq_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hpp := (Nat.mem_primesLE.mp hp).2
    have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_right _ hl
    calc (N : ℝ) / p - 1 ≤ ((N / p : ℕ) : ℝ) := real_div_sub_one_le_nat_div N p hpp.pos
      _ ≤ _ := by exact_mod_cast div_le_factorization_factorial hpp N
  have hsplit : ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p - 1) =
      N * ∑ p ∈ Nat.primesLE N, Real.log p / p - Chebyshev.theta N := by
    rw [Chebyshev.theta_eq_sum_primesLE_log, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    ring
  have hth := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hf := log_factorial_le N
  rw [hsplit] at key
  have : (N : ℝ) * ∑ p ∈ Nat.primesLE N, Real.log p / p ≤ N * (Real.log N + Real.log 4) := by
    nlinarith
  exact le_of_mul_le_mul_left this hNr

open Nat

theorem harmonic_real (N : ℕ) :
    (harmonic N : ℝ) = ∑ m ∈ Icc 1 N, (m : ℝ)⁻¹ := by
  simp [harmonic_eq_sum_Icc]

theorem harmonic_le_euler (N : ℕ) :
    (harmonic N : ℝ) ≤ ∏ p ∈ (N+1).primesBelow, (1 - (p : ℝ)⁻¹)⁻¹ := by
  classical
  let f : ℕ → ℝ := fun n => (n : ℝ)⁻¹
  have hf₁ : f 1 = 1 := by simp [f]
  have hmul : ∀ {m n : ℕ}, m.Coprime n → f (m*n) = f m * f n := by
    intro m n _
    simp [f, mul_comm]
  have hp_bound {p : ℕ} (hp : p.Prime) : (p : ℝ)⁻¹ ≤ 1/2 := by
    have h : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    rw [one_div]
    exact inv_anti₀ (by norm_num) h
  have hs {p : ℕ} (hp : p.Prime) : Summable (fun n : ℕ => ‖f (p ^ n)‖) := by
    have hh : (p : ℝ)⁻¹ < 1 := (hp_bound hp).trans_lt (by norm_num)
    simpa [f, mul_inv, inv_pow, Real.norm_eq_abs, abs_of_nonneg] using
      summable_geometric_of_lt_one (show 0 ≤ (p : ℝ)⁻¹ by positivity) hh
  obtain ⟨-, heuler⟩ :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum hf₁ hmul
      (fun hp => hs hp) (N+1)
  have hprod : (∏ p ∈ (N+1).primesBelow, (1 - (p : ℝ)⁻¹)⁻¹) =
      (∏ p ∈ (N+1).primesBelow, ∑' n : ℕ, f (p^n)) := by
    apply prod_congr rfl
    intro p hp
    have hlt : (p : ℝ)⁻¹ < 1 :=
      (hp_bound (prime_of_mem_primesBelow hp)).trans_lt (by norm_num)
    simp only [f, Nat.cast_pow, ← inv_pow]
    exact (tsum_geometric_of_lt_one (by positivity) hlt).symm
  rw [← hprod] at heuler
  let s := Icc 1 N
  let emb : s ↪ (N+1).smoothNumbers :=
    ⟨fun m => ⟨m.val, Nat.mem_smoothNumbers_of_lt
      (by have := (mem_Icc.mp m.prop).1; omega)
      (by have := (mem_Icc.mp m.prop).2; omega)⟩,
      fun m n h => Subtype.ext (congrArg (fun t : (N+1).smoothNumbers => t.val) h)⟩
  rw [harmonic_real, ← sum_attach s]
  change (∑ m ∈ s.attach, f (emb m).val) ≤ _
  rw [← sum_map s.attach emb (fun m => f m.val)]
  rw [← heuler.tsum_eq]
  exact heuler.summable.sum_le_tsum _ (fun m _ => by dsimp [f]; positivity)

theorem log_le_euler (N : ℕ) :
    Real.log N ≤ (∏ p ∈ Nat.primesLE N, (1-1/(p:ℝ)))⁻¹ := by
  have hh := log_le_harmonic_floor (N:ℝ) (by positivity)
  rw [Nat.floor_natCast] at hh
  simpa only [Nat.primesLE, one_div, prod_inv_distrib] using hh.trans (harmonic_le_euler N)

end OMALib.Mertens

open scoped Classical
open Finset

namespace OMALib.Sieve

variable {ι : Type*} [DecidableEq ι]

noncomputable def hFun (g : ι → ℝ) (p : ι) : ℝ := g p / (1 - g p)

noncomputable def selbergG (g : ι → ℝ) (D : Finset (Finset ι)) : ℝ :=
  ∑ S ∈ D, ∏ p ∈ S, hFun g p

noncomputable def omega (C : ℕ → ℕ → Prop) (p : ℕ) : ℕ := ((range p).filter (C p)).card

noncomputable def levelFamily (Q : Finset ℕ) (z : ℕ) : Finset (Finset ℕ) :=
  Q.powerset.filter (fun S => ∏ p ∈ S, p < z)

theorem levelFamily_subset {Q : Finset ℕ} {z : ℕ} : ∀ S ∈ levelFamily Q z, S ⊆ Q :=
  fun S hS => mem_powerset.mp (mem_filter.mp hS).1

theorem empty_mem_levelFamily {Q : Finset ℕ} {z : ℕ} (hz : 2 ≤ z) : ∅ ∈ levelFamily Q z := by
  simp only [levelFamily, mem_filter, empty_mem_powerset, prod_empty, true_and]; omega

theorem card_levelFamily_le {Q : Finset ℕ} (hQ : ∀ p ∈ Q, p.Prime) (z : ℕ) :
    (levelFamily Q z).card ≤ z := by
  have := card_le_card_of_injOn (s := levelFamily Q z) (t := range z) (fun S => ∏ p ∈ S, p)
    (fun S hS => by
      simp only [levelFamily, coe_filter, mem_powerset, Set.mem_ofPred_eq] at hS
      simp only [coe_range, Set.mem_Iio]; exact hS.2)
    (fun S hS T hT h => by
      simp only [levelFamily, coe_filter, mem_powerset, Set.mem_ofPred_eq] at hS hT
      have h1 := Nat.primeFactors_prod (s := S) fun p hp => hQ p (hS.1 hp)
      have h2 := Nat.primeFactors_prod (s := T) fun p hp => hQ p (hT.1 hp)
      simp only at h
      rw [← h1, ← h2, h])
  simpa using this

-- A complete period factors into independent prime residues by CRT.
theorem sum_period_prod (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (f : ℕ → ℕ → ℝ)
    (hf : ∀ p ∈ S, ∀ n, f p n = f p (n%p)) :
    ∑ n ∈ range (∏ p ∈ S,p), ∏ p ∈ S,f p n = ∏ p ∈ S, ∑ r ∈ range p,f p r := by
  let M := ∏ p ∈ S,p
  let r (n : Fin M) (p : S) : Fin p.val := ⟨n.val%p, Nat.mod_lt _ (hS p p.prop).pos⟩
  have hb : Function.Bijective r := by
    apply (Fintype.bijective_iff_surjective_and_card _).mpr
    constructor
    · intro v
      let a (p : ℕ) := if hp : p ∈ S then (v ⟨p,hp⟩).val else 0
      have hnz (p) (hp : p ∈ S) := (hS p hp).ne_zero
      have hcop : Set.Pairwise (↑S) (fun p q : ℕ => p.Coprime q) := fun p hp q hq =>
        (Nat.coprime_primes (hS p hp) (hS q hq)).mpr
      let n := Nat.chineseRemainderOfFinset a id S hnz hcop
      refine ⟨⟨n,Nat.chineseRemainderOfFinset_lt_prod _ _ _ _⟩, funext fun p => Fin.ext ?_⟩
      have e : n.val % p = a p % p := n.prop p p.prop
      simpa [r,a,p.prop,Nat.mod_eq_of_lt (v p).isLt] using e
    · simp only [Fintype.card_fin,Fintype.card_pi]
      exact (Finset.prod_coe_sort S id).symm
  let g (v : ∀ p : S, Fin p.val) := ∏ p : S, f p (v p)
  have he := (Equiv.ofBijective r hb).sum_comp g
  rw [← Fin.sum_univ_eq_sum_range]
  calc _ = ∑ n : Fin M,g (r n) := by
            refine sum_congr rfl fun n _ => ?_
            rw [← Finset.prod_coe_sort S (fun p => f p n)]
            exact prod_congr rfl fun p _ => hf p p.prop n
       _ = ∑ v,g v := he
       _ = _ := by
         dsimp only [g]
         rw [← Fintype.prod_sum (fun (p : S) (r : Fin p.val) => f p r), ← Finset.prod_coe_sort S (fun p => ∑ r ∈ range p,f p r)]
         exact prod_congr rfl fun p _ => Fin.sum_univ_eq_sum_range _ _

theorem sum_period_le (f : ℕ → ℝ) (m N : ℕ) (hm : 0 < m) (A B : ℝ)
    (hper : ∀ n, f n = f (n%m)) (hfull : ∑ n ∈ range m,f n = m*A)
    (ha : 0 ≤ A) (hb : 0 ≤ B) (hf : ∀ n, f n ≤ B) :
    ∑ n ∈ range N,f n ≤ N*A + m*B := by
  have shift (k i : ℕ) : f (m*k+i) = f i := by rw [hper (m*k+i),Nat.mul_add_mod,hper i]
  have blocks (k : ℕ) : ∑ n ∈ range (m*k), f n = (m*k:ℕ)*A := by
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.mul_succ,sum_range_add,ih]; simp_rw [shift]; rw [hfull]; push_cast; ring
  have he := Nat.div_add_mod N m
  conv_lhs => rw [← he]
  rw [sum_range_add,blocks]
  simp_rw [shift]
  have hsmall : ∑ i ∈ range (N%m),f i ≤ (N%m:ℕ)*B :=
    (sum_le_sum fun i _ => hf i).trans_eq (by simp)
  have h1 : (m*(N/m):ℕ) ≤ N := by omega
  gcongr <;> first | exact hsmall.trans (by gcongr; exact (Nat.mod_lt _ hm).le) | exact_mod_cast h1

-- Products of centered local functions have zero cross terms on each period.
theorem orthogonal_pair (S T : Finset ℕ) (hprime : ∀ p ∈ S ∪ T, p.Prime)
    (F : ℕ → ℕ → ℝ) (H : ℕ → ℝ)
    (hper : ∀ p n, F p n = F p (n%p))
    (hmean : ∀ p ∈ S ∪ T, ∑ r ∈ range p, F p r = 0)
    (hvar : ∀ p ∈ S ∪ T, ∑ r ∈ range p, F p r * F p r = p*H p) :
    ∑ n ∈ range (∏ p ∈ S ∪ T,p), (∏ p ∈ S,F p n)*(∏ p ∈ T,F p n) =
      (∏ p ∈ S ∪ T,(p:ℝ))*(if S=T then ∏ p ∈ S,H p else 0) := by
  let f (p n : ℕ) := (if p ∈ S then F p n else 1)*(if p ∈ T then F p n else 1)
  have he (n) : (∏ p ∈ S ∪ T,f p n) = (∏ p ∈ S,F p n)*(∏ p ∈ T,F p n) := by
    dsimp only [f]
    rw [prod_mul_distrib,prod_ite_mem,prod_ite_mem]
    simp
  simp_rw [← he]
  rw [sum_period_prod _ hprime f (fun p _ n => by dsimp [f]; rw [hper p n])]
  split_ifs with eq
  · subst T
    simp only [union_self, ← prod_mul_distrib]
    exact prod_congr rfl fun p hp => by simpa [f,hp] using hvar p (mem_union_left _ hp)
  · rw [mul_zero]
    have ⟨p,hp⟩ := SetLike.ext_iff.not.mp eq |> Classical.not_forall.mp
    push Not at hp
    rcases hp with ⟨hS,hT⟩ | ⟨hT,hS⟩
    · have h := mem_union_left T hS
      exact prod_eq_zero h (by simpa [f,hS,hT] using hmean p h)
    · have h := mem_union_right S hS
      exact prod_eq_zero h (by simpa [f,hS,hT] using hmean p h)
theorem quadratic_sieve (N z : ℕ) (hz : 2 ≤ z) (Q : Finset ℕ) (hq : ∀ p ∈ Q,p.Prime)
    (H : ℕ → ℝ) (F : ℕ → ℕ → ℝ) (hH : ∀ p ∈ Q,0 ≤ H p)
    (hF : ∀ p ∈ Q,∀ n, |F p n| ≤ p) (hper : ∀ p n,F p n = F p (n%p))
    (hmean : ∀ p ∈ Q, ∑ r ∈ range p,F p r = 0)
    (hvar : ∀ p ∈ Q, ∑ r ∈ range p,F p r * F p r = p * H p) :
    let D := levelFamily Q z
    let G := ∑ S ∈ D, ∏ p ∈ S,H p
    (((range N).filter (fun n => ∀ p ∈ Q,F p n = H p)).card:ℝ) ≤ N/G+(z:ℝ)^6 := by
  intro D G
  let w (S : Finset ℕ) (n : ℕ) := ∏ p ∈ S,F p n
  let v (S : Finset ℕ) := ∏ p ∈ S,H p
  have hsub (S) (hS : S ∈ D) : S ⊆ Q := levelFamily_subset _ hS
  have hv (S) (hS : S ∈ D) : 0 ≤ v S := prod_nonneg fun p hp => hH p (hsub S hS hp)
  have bound (S) (hS : S ∈ D) : (∏ p ∈ S,p) ≤ z := (mem_filter.mp hS).2.le
  have hG : 1 ≤ G := by simpa [v] using single_le_sum hv (empty_mem_levelFamily (Q := Q) hz)
  have habs (S) (hS : S ∈ D) (n) : |w S n| ≤ z := by
    dsimp only [w]; rw [abs_prod]
    exact (prod_le_prod (fun _ _ => abs_nonneg _) (fun p hp => hF p (hsub S hS hp) n)).trans
      (by rw [← Nat.cast_prod]; exact_mod_cast bound S hS)
  have pair (S) (hS : S ∈ D) (T) (hT : T ∈ D) :
      ∑ n ∈ range N,w S n*w T n ≤ N*(if S=T then v S else 0)+(z:ℝ)^4 := by
    let m := ∏ p ∈ S ∪ T,p
    have hu : S ∪ T ⊆ Q := union_subset (hsub S hS) (hsub T hT)
    have hm : 0 < m := prod_pos fun p hp => (hq p (hu hp)).pos
    have hmle : m ≤ z*z := calc
      _ ≤ (∏ p ∈ S,p)*(∏ p ∈ T,p) := by
        rw [← prod_union_inter]
        exact Nat.le_mul_of_pos_right _ (prod_pos fun p hp => (hq p (hsub S hS (mem_inter.mp hp).1)).pos)
      _ ≤ _ := Nat.mul_le_mul (bound S hS) (bound T hT)
    have period (U : Finset ℕ) (hU : U ⊆ S ∪ T) (n) : w U n = w U (n%m) :=
      prod_congr rfl fun p hp => by rw [hper p n,hper p (n%m),Nat.mod_mod_of_dvd n (show p ∣ m from dvd_prod_of_mem id (hU hp))]
    have full := orthogonal_pair S T (fun p hp => hq p (hu hp)) F H hper
      (fun p hp => hmean p (hu hp)) (fun p hp => hvar p (hu hp))
    have h := sum_period_le (fun n => w S n*w T n) m N hm (if S=T then v S else 0) ((z:ℝ)^2)
      (fun n => by rw [period S subset_union_left n,period T subset_union_right n])
      (by simpa only [m,Nat.cast_prod] using full)
      (by split_ifs <;> first | exact hv S hS | positivity) (sq_nonneg _)
      (fun n => by rw [sq]; exact (le_abs_self _).trans ((abs_mul ..).trans_le
        (mul_le_mul (habs S hS n) (habs T hT n) (abs_nonneg _) (by positivity))))
    refine h.trans (add_le_add_right ?_ _)
    calc _ ≤ ((z:ℝ)*z)*z^2 := by gcongr; exact_mod_cast hmle
         _ = _ := by ring
  let A := (range N).filter (fun n => ∀ p ∈ Q,F p n = H p)
  have upper : (A.card:ℝ)*G^2 ≤ ∑ n ∈ range N,(∑ S ∈ D,w S n)^2 := by
    calc _ = ∑ n ∈ A,(∑ S ∈ D,w S n)^2 := by
              rw [← nsmul_eq_mul,← sum_const]
              refine sum_congr rfl fun n hn => congrArg (·^2) (sum_congr rfl fun S hS =>
                prod_congr rfl fun p hp => ((mem_filter.mp hn).2 p (hsub S hS hp)).symm)
         _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => sq_nonneg _)
  have exchange : ∑ n ∈ range N,(∑ S ∈ D,w S n)^2 =
      ∑ S ∈ D,∑ T ∈ D,∑ n ∈ range N,w S n*w T n := by
    simp_rw [sq,sum_mul,mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun _ _ => sum_comm
  rw [exchange] at upper
  have est := upper.trans (sum_le_sum fun S hS => sum_le_sum fun T hT => pair S hS T hT)
  simp_rw [sum_add_distrib,← mul_sum] at est
  simp only [sum_ite_eq,ite_true,sum_const,nsmul_eq_mul] at est
  have diag : ∑ S ∈ D, (if S ∈ D then v S else 0) = G := sum_congr rfl fun S hS => if_pos hS
  have hc : (D.card:ℝ) ≤ z := by exact_mod_cast card_levelFamily_le hq z
  change (A.card:ℝ) ≤ _
  have hmain : (A.card:ℝ)*G^2 ≤ N*G + (z:ℝ)^6 := by
    rw [diag] at est
    refine est.trans (add_le_add_right ?_ _)
    have h4 : (0:ℝ) ≤ (z:ℝ)^4 := pow_nonneg (Nat.cast_nonneg _) _
    have he := mul_le_mul hc (mul_le_mul_of_nonneg_right hc h4)
      (mul_nonneg (Nat.cast_nonneg _) h4) (Nat.cast_nonneg _)
    exact he.trans_eq (by ring)
  apply le_of_mul_le_mul_right _ (sq_pos_of_pos (by linarith : 0 < G))
  calc _ ≤ _ := hmain
       _ ≤ (N/G+(z:ℝ)^6)*G^2 := by
         have : (N/G)*G^2 = N*G := by field_simp
         rw [add_mul,this]
         nlinarith only [mul_le_mul_of_nonneg_left (one_le_pow₀ hG (n := 2)) (pow_nonneg (Nat.cast_nonneg (α := ℝ) z) 6)]
def pairCond (d : ℕ) (p n : ℕ) : Prop := p ∣ n * (1 + d * n)

def pairOmega (d p : ℕ) : ℕ := if p ∣ d then 1 else 2

noncomputable def pairG (d z : ℕ) : ℝ :=
  selbergG (fun p => (pairOmega d p : ℝ) / p) (levelFamily (Nat.primesBelow z) z)

theorem pairCond_periodic (d p n : ℕ) : pairCond d p n ↔ pairCond d p (n % p) := by
  unfold pairCond
  simp only [Nat.dvd_iff_mod_eq_zero, Nat.mul_mod, Nat.add_mod, Nat.mod_mod]

theorem omega_pairCond {d p : ℕ} (hp : p.Prime) : omega (pairCond d) p = pairOmega d p := by
  haveI : Fact p.Prime := ⟨hp⟩
  let u := (-(d:ZMod p)⁻¹).val
  have hmem (n : ℕ) (hn : n < p) : pairCond d p n ↔ n = 0 ∨ (¬p ∣ d ∧ n = u) := by
    rw [pairCond, ← ZMod.natCast_eq_zero_iff, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_mul,
        mul_eq_zero]
    have h0 : (n : ZMod p) = 0 ↔ n = 0 := by
      rw [ZMod.natCast_eq_zero_iff]; exact ⟨fun h => Nat.eq_zero_of_dvd_of_lt h hn, by rintro rfl; simp⟩
    rw [h0]; apply or_congr_right
    by_cases h : p ∣ d
    · simp [h,(ZMod.natCast_eq_zero_iff ..).mpr h]
    · have hd : (d:ZMod p) ≠ 0 := fun e => h ((ZMod.natCast_eq_zero_iff ..).mp e)
      simp only [h,not_false_eq_true,true_and]
      have he : (n:ZMod p) = -(d:ZMod p)⁻¹ ↔ n = u := by
        constructor
        · intro h; simpa [u,ZMod.val_natCast_of_lt hn] using congrArg ZMod.val h
        · rintro rfl; simp [u]
      rw [← he]; field_simp; constructor <;> intro h <;> linear_combination h
  have hset : (range p).filter (pairCond d p) = if p ∣ d then {0} else {0,u} := by
    ext n
    have hu : u < p := ZMod.val_lt _
    have hpos := hp.pos
    by_cases hn : n < p
    · simp only [mem_filter,mem_range,hn,true_and,hmem n hn]
      split_ifs <;> simp_all
    · split_ifs <;> simp [hn] <;> omega
  rw [omega,hset,pairOmega]
  split_ifs with h
  · simp
  · have hd : (d:ZMod p) ≠ 0 := fun e => h ((ZMod.natCast_eq_zero_iff ..).mp e)
    have hu : u ≠ 0 := by simpa [u] using hd
    simp [hu,Ne.symm hu]

theorem pairOmega_pos (d p : ℕ) : 0 < pairOmega d p := by
  unfold pairOmega; split_ifs <;> norm_num

theorem pairOmega_lt {d p : ℕ} (hd : Even d) (hp : p.Prime) : pairOmega d p < p := by
  unfold pairOmega
  split_ifs with h
  · exact hp.one_lt
  · have h2 : p ≠ 2 := by rintro rfl; exact h (even_iff_two_dvd.mp hd)
    have := hp.two_le; omega

theorem pair_hFun (d : ℕ) {p : ℕ} (hd : Even d) (hp : p.Prime) :
    hFun (fun p => (pairOmega d p : ℝ) / p) p
      = (pairOmega d p : ℝ) / ((p : ℝ) - pairOmega d p) := by
  have hlt : (pairOmega d p : ℝ) < p := by exact_mod_cast pairOmega_lt hd hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  unfold hFun
  have : (p : ℝ) - pairOmega d p ≠ 0 := by linarith
  field_simp

theorem pair_hFun_nonneg (d : ℕ) {p : ℕ} (hd : Even d) (hp : p.Prime) :
    0 ≤ hFun (fun p => (pairOmega d p : ℝ) / p) p := by
  rw [pair_hFun d hd hp]
  have hlt : (pairOmega d p : ℝ) < p := by exact_mod_cast pairOmega_lt hd hp
  exact div_nonneg (Nat.cast_nonneg _) (by linarith)

theorem sum_local (P : ℕ → Prop) [DecidablePred P] (p : ℕ) (a b : ℝ) :
    ∑ r ∈ range p,(if P r then a else b) =
      ((range p).filter P).card*a + (p-(((range p).filter P).card:ℝ))*b := by
  rw [sum_ite]
  simp only [sum_const,nsmul_eq_mul]
  have h := card_filter_add_card_filter_not (s := range p) P
  rw [card_range] at h
  have e : ((((range p).filter (fun r => ¬ P r)).card:ℝ)) = p-(((range p).filter P).card:ℝ) := by
    exact eq_sub_of_add_eq' (by exact_mod_cast h)
  rw [e]

theorem affine_count_le_sieve (d x z : ℕ) (hd0 : 0 < d) (hd : Even d) (hz : 2 ≤ z) :
    (((range (x+1)).filter (fun p => p.Prime ∧ (1+d*p).Prime)).card:ℝ)
      ≤ z+(x+1)/pairG d z+(z:ℝ)^6 := by
  let Q := Nat.primesBelow z
  have hQ (p) (hp : p ∈ Q) := (Nat.mem_primesBelow.mp hp).2
  let H := hFun (fun p => (pairOmega d p:ℝ)/p)
  let F (p n : ℕ) := if pairCond d p n then (-1:ℝ) else H p
  have hH (p) (hp : p ∈ Q) : 0 ≤ H p := pair_hFun_nonneg d hd (hQ p hp)
  have hlt (p) (hp : p ∈ Q) : (pairOmega d p:ℝ) < p := by exact_mod_cast pairOmega_lt hd (hQ p hp)
  have hgap (p) (hp : p ∈ Q) : (1:ℝ) ≤ (p:ℝ)-pairOmega d p := by
    have := pairOmega_lt hd (hQ p hp)
    exact le_sub_iff_add_le.mpr (by exact_mod_cast (by omega : 1+pairOmega d p ≤ p))
  have hF (p) (hp : p ∈ Q) (n) : |F p n| ≤ p := by
    dsimp only [F]; split_ifs
    · simpa using (show (1:ℝ) ≤ p by exact_mod_cast (hQ p hp).one_le)
    · rw [abs_of_nonneg (hH p hp)]
      change hFun _ _ ≤ _
      rw [pair_hFun d hd (hQ p hp),div_le_iff₀ (by linarith [hgap p hp])]
      nlinarith only [hlt p hp,mul_le_mul_of_nonneg_left (hgap p hp) (Nat.cast_nonneg (α := ℝ) p)]
  have hlocal (p) (hp : p ∈ Q) (a b : ℝ) := sum_local (pairCond d p) p a b
  have moments (p) (hp : p ∈ Q) :
      (∑ r ∈ range p,F p r) = 0 ∧ (∑ r ∈ range p,F p r * F p r) = p*H p := by
    have count : ((range p).filter (pairCond d p)).card = pairOmega d p := omega_pairCond (hQ p hp)
    have e : H p*((p:ℝ)-pairOmega d p) = pairOmega d p := by
      change hFun _ _ * _ = _
      rw [pair_hFun d hd (hQ p hp),div_mul_cancel₀ _ (by linarith [hlt p hp])]
    constructor
    · dsimp only [F]; rw [hlocal p hp,count]; linarith
    · have sq (r) : F p r * F p r = if pairCond d p r then 1 else H p*H p := by
        dsimp only [F]; split_ifs <;> ring
      simp_rw [sq]
      rw [hlocal p hp,count]
      nlinarith only [e,congrArg (· * H p) e]
  have hs := quadratic_sieve (x+1) z hz Q hQ H F hH hF
    (fun p n => by dsimp only [F]; rw [pairCond_periodic]) (fun p hp => (moments p hp).1)
    (fun p hp => (moments p hp).2)
  have hsub : (range (x+1)).filter (fun p => p.Prime ∧ (1+d*p).Prime) ⊆
      range z ∪ (range (x+1)).filter (fun n => ∀ p ∈ Q,F p n = H p) := by
    intro n hn
    obtain ⟨hx,hn,hpartner⟩ := mem_filter.mp hn
    by_cases h : n < z
    · exact mem_union_left _ (mem_range.mpr h)
    refine mem_union_right _ (mem_filter.mpr ⟨hx,fun p hp => if_neg ?_⟩)
    intro hdiv
    have ⟨hpz,hpr⟩ := Nat.mem_primesBelow.mp hp
    rcases hpr.dvd_mul.mp hdiv with h₁ | h₂
    · have := (Nat.prime_dvd_prime_iff_eq hpr hn).mp h₁; omega
    · have := (Nat.prime_dvd_prime_iff_eq hpr hpartner).mp h₂
      have := Nat.le_mul_of_pos_left n hd0; omega
  have h := (card_le_card hsub).trans (card_union_le ..)
  rw [card_range] at h
  push_cast at hs
  have hc := Nat.cast_le (α := ℝ) |>.mpr h
  push_cast at hc
  change _ ≤ ((x:ℝ)+1)/pairG d z + (z:ℝ)^6 at hs
  linarith
noncomputable def pairSingularProduct (d : ℕ) : ℝ :=
  ∏ p ∈ d.primeFactors, (1 + 1 / (p : ℝ))

theorem one_le_pairSingularProduct (d : ℕ) : 1 ≤ pairSingularProduct d :=
  one_le_prod fun p _ => le_add_of_nonneg_right (by positivity)

theorem singular_compensation (d : ℕ) :
    1/2 ≤ (∏ p ∈ d.primeFactors, (1 - 1 / (p : ℝ))) * pairSingularProduct d := by
  let f (p : ℕ) := (1-1/(p:ℝ))*(1+1/(p:ℝ))
  have hf (p : ℕ) (hp : 2 ≤ p) : 0 ≤ f p ∧ f p ≤ 1 := by
    have hp' : (2:ℝ) ≤ p := by exact_mod_cast hp
    dsimp [f]
    constructor
    · apply mul_nonneg _ (by positivity)
      rw [sub_nonneg, div_le_one (by linarith)]; linarith
    · nlinarith [sq_nonneg (1/(p:ℝ))]
  have hprod (n : ℕ) (hn : 1 ≤ n) : ∏ p ∈ Icc 2 n, f p = ((n:ℝ)+1)/(2*n) := by
    induction n, hn using Nat.le_induction with
    | base => norm_num
    | succ n hn ih =>
      rw [prod_Icc_succ_top (by omega), ih]
      dsimp [f]; push_cast
      have : (0:ℝ) < n := by exact_mod_cast hn
      field_simp; ring
  unfold pairSingularProduct
  rw [← prod_mul_distrib]
  change 1/2 ≤ ∏ p ∈ d.primeFactors, f p
  calc _ ≤ ∏ p ∈ Icc 2 (d+1), f p := by
           rw [hprod _ (by omega), le_div_iff₀ (by positivity)]
           linarith
       _ ≤ _ := prod_le_prod_of_subset_of_le_one
          (fun p hp => mem_Icc.mpr ⟨(Nat.prime_of_mem_primeFactors hp).two_le,
             (Nat.le_of_mem_primeFactors hp).trans (Nat.le_succ _)⟩)
          (fun p hp => (hf p (mem_Icc.mp hp).1).1)
          (fun p hp _ => (hf p (mem_Icc.mp hp).1).2)

theorem pair_one_add_hFun_ge (d : ℕ) {p : ℕ} (hd : Even d) (hp : p.Prime) :
    (1 - 1 / (p : ℝ))⁻¹ ^ 2 * (if p ∣ d then 1 - 1 / (p : ℝ) else 1)
      ≤ 1 + hFun (fun p => (pairOmega d p : ℝ) / p) p := by
  rw [pair_hFun d hd hp]
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have e : 1 - 1 / (p : ℝ) = ((p : ℝ) - 1) / p := by field_simp
  rw [e, inv_div]
  unfold pairOmega
  split_ifs with h
  · push_cast
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    rw [div_pow, div_mul_div_comm, div_le_iff₀ (by positivity)]
    have : (p : ℝ) - 1 ≠ 0 := by linarith
    field_simp; nlinarith
  · have h2 : p ≠ 2 := by rintro rfl; exact h (even_iff_two_dvd.mp hd)
    have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (show 3 ≤ p by have := hp.two_le; omega)
    push_cast
    rw [mul_one, div_pow, div_le_iff₀ (by nlinarith)]
    have : (p : ℝ) - 2 ≠ 0 := by linarith
    rw [show (1 : ℝ) + 2 / ((p : ℝ) - 2) = p / ((p : ℝ) - 2) by field_simp; ring]
    rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
    nlinarith

-- First moment of the log of the product of a random subset.
theorem powerset_moment (Q : Finset ℕ) (H g a : ℕ → ℝ)
    (hg : ∀ p ∈ Q, (1+H p)*g p = H p) :
    ∑ T ∈ Q.powerset, (∏ p ∈ T, H p)*(∑ p ∈ T, a p) =
      (∏ p ∈ Q, (1+H p))*(∑ p ∈ Q, g p*a p) := by
  induction Q using Finset.induction_on with
  | empty => simp
  | insert p Q hp ih =>
    rw [sum_powerset_insert hp, prod_insert hp, sum_insert hp]
    have h (T) (hT : T ∈ Q.powerset) : p ∉ T := fun ht => hp (mem_powerset.mp hT ht)
    simp_rw [sum_congr rfl (fun T (hT : T ∈ Q.powerset) => show
      (∏ i ∈ insert p T, H i)*(∑ i ∈ insert p T, a i) =
        H p*a p*(∏ i ∈ T,H i) + H p*((∏ i ∈ T,H i)*(∑ i ∈ T,a i)) by
          rw [prod_insert (h T hT),sum_insert (h T hT)]; ring)]
    rw [sum_add_distrib, ← mul_sum, ← mul_sum, ← prod_one_add,
      ih (fun i hi => hg i (mem_insert_of_mem hi))]
    linear_combination -(a p * ∏ i ∈ Q, (1+H i)) * hg p (mem_insert_self ..)

theorem pair_rankin_half (d Y : ℕ) (hd : Even d) (hY : 4 ≤ Y) :
    (1 / 2) * ∏ p ∈ Nat.primesLE Y, (1 + hFun (fun p => (pairOmega d p : ℝ) / p) p)
      ≤ pairG d (Y^37) := by
  let Q := Nat.primesLE Y
  let z := Y^37
  let g := fun p => (pairOmega d p : ℝ) / p
  let H := hFun g
  let L := Real.log (Y:ℝ)
  have hY' : (4:ℝ) ≤ Y := by exact_mod_cast hY
  have hL : 0 < L := Real.log_pos (by linarith)
  have hQ (p) (hp : p ∈ Q) := (Nat.mem_primesLE.mp hp).2
  have hH (p) (hp : p ∈ Q) : 0 ≤ H p := pair_hFun_nonneg d hd (hQ p hp)
  have hm := powerset_moment Q H g (fun p => Real.log p) (by
    intro p hp
    have hlt : (pairOmega d p:ℝ) < p := by exact_mod_cast pairOmega_lt hd (hQ p hp)
    have hp' : (0:ℝ) < p := by exact_mod_cast (hQ p hp).pos
    have h1 : g p < 1 := (div_lt_one hp').mpr hlt
    dsimp [H,hFun]; field_simp [ne_of_gt (sub_pos.mpr h1)]; ring)
  have hs : ∑ p ∈ Q, g p * Real.log p ≤ 4 * L := calc
    _ ≤ ∑ p ∈ Q, 2*(Real.log p/p) := by
      refine sum_le_sum fun p hp => ?_
      have hlog := Real.log_nonneg (by exact_mod_cast (hQ p hp).one_le : (1:ℝ) ≤ p)
      dsimp [g,pairOmega]
      split_ifs <;> push_cast <;> ring_nf <;> nlinarith [mul_nonneg hlog (inv_nonneg.mpr (Nat.cast_nonneg (α := ℝ) p))]
    _ ≤ _ := by
      rw [← mul_sum]
      have := Real.log_le_log (by norm_num : (0:ℝ)<4) hY'
      linarith [OMALib.Mertens.sum_log_div_le_nat Y]
  let w (T : Finset ℕ) := ∏ p ∈ T,H p
  let D := levelFamily (Nat.primesBelow z) z
  have hmass : (∏ p ∈ Q, (1+H p))*(37*L) ≤
      (∑ T ∈ Q.powerset with T ∈ D, w T)*(37*L) +
      (∏ p ∈ Q, (1+H p))*(4*L) := by
    refine le_trans ?_ (add_le_add_right (mul_le_mul_of_nonneg_left hs
      (prod_nonneg fun p hp => by linarith [hH p hp])) _)
    rw [← hm, prod_one_add, sum_mul, sum_filter, sum_mul, ← sum_add_distrib]
    refine sum_le_sum fun T hT => ?_
    have hTQ := mem_powerset.mp hT
    have hw : 0 ≤ w T := prod_nonneg fun p hp => hH p (hTQ hp)
    have hlog (p) (hp : p ∈ T) := Real.log_nonneg (by exact_mod_cast (hQ p (hTQ hp)).one_le : (1:ℝ) ≤ p)
    split_ifs with h
    · dsimp [w] at *; nlinarith [sum_nonneg hlog]
    · simp only [zero_mul,zero_add]
      apply mul_le_mul_of_nonneg_left _ hw
      rw [← Real.log_prod (fun p hp => by exact_mod_cast (hQ p (hTQ hp)).ne_zero),
        ← Nat.cast_prod]
      have hlt : Y < z := by simpa [z] using pow_lt_pow_right₀ (by omega : 1 < Y) (by decide : 1 < 37)
      have hge : z ≤ ∏ p ∈ T,p := by
        by_contra! hh
        exact h (mem_filter.mpr ⟨mem_powerset.mpr (fun p hp =>
          Nat.mem_primesBelow.mpr ⟨(Nat.mem_primesLE.mp (hTQ hp)).1.trans_lt hlt,hQ p (hTQ hp)⟩),hh⟩)
      have hz : (0:ℝ) < (z:ℕ) := by dsimp [z]; positivity
      simpa [z,L,Real.log_pow] using Real.log_le_log hz (by exact_mod_cast hge : (z:ℝ) ≤ ((∏ p ∈ T,p : ℕ):ℝ))
  have hsub : (∑ T ∈ Q.powerset with T ∈ D,w T) ≤ pairG d z :=
    sum_le_sum_of_subset_of_nonneg (fun T hT => (mem_filter.mp hT).2) (fun T hT _ =>
      prod_nonneg fun p hp => pair_hFun_nonneg d hd (Nat.mem_primesBelow.mp (levelFamily_subset T hT hp)).2)
  apply le_trans _ hsub
  apply le_of_mul_le_mul_right _ hL
  change 1/2*(∏ p ∈ Q,(1+H p))*L ≤ _
  have hprod : 0 ≤ ∏ p ∈ Q,(1+H p) := prod_nonneg fun p hp => by linarith [hH p hp]
  nlinarith

theorem pair_euler_ge (d Y : ℕ) (hd0 : 0 < d) (hd : Even d) :
    ((∏ p ∈ Nat.primesLE Y, (1 - 1 / (p : ℝ)))⁻¹) ^ 2 * ∏ p ∈ d.primeFactors, (1 - 1 / (p : ℝ))
      ≤ ∏ p ∈ Nat.primesLE Y, (1 + hFun (fun p => (pairOmega d p : ℝ) / p) p) := by
  set Q := Nat.primesLE Y
  have hQp : ∀ p ∈ Q, p.Prime := fun p hp => (Nat.mem_primesLE.mp hp).2
  set H : ℕ → ℝ := fun p => hFun (fun p => (pairOmega d p : ℝ) / p) p

  have hE : ((∏ p ∈ Q, (1 - 1 / (p : ℝ)))⁻¹) ^ 2 * ∏ p ∈ d.primeFactors, (1 - 1 / (p : ℝ))
      ≤ ∏ p ∈ Q, (1 + H p) := by
    have hf : ∀ p ∈ Q, 0 ≤ 1 - 1 / (p : ℝ) := fun p hp => by
      have : (1 : ℝ) ≤ p := by exact_mod_cast (hQp p hp).one_lt.le
      rw [sub_nonneg, div_le_one (by linarith)]; exact this
    have step1 : ∏ p ∈ Q, ((1 - 1 / (p : ℝ))⁻¹ ^ 2 * (if p ∣ d then 1 - 1 / (p : ℝ) else 1))
        ≤ ∏ p ∈ Q, (1 + H p) :=
      prod_le_prod (fun p hp => by
        have := hf p hp
        split_ifs <;> positivity) fun p hp => pair_one_add_hFun_ge d hd (hQp p hp)
    rw [prod_mul_distrib, prod_pow, prod_inv_distrib] at step1
    refine le_trans ?_ step1
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [← prod_filter]
    have hsub : Q.filter (fun p => p ∣ d) ⊆ d.primeFactors := fun p hp => by
      simp only [mem_filter] at hp
      exact Nat.mem_primeFactors.mpr ⟨hQp p hp.1, hp.2, hd0.ne'⟩
    rw [← prod_sdiff hsub]
    have h0 : 0 ≤ ∏ p ∈ Q.filter (fun p => p ∣ d), (1 - 1 / (p : ℝ)) :=
      prod_nonneg fun p hp => hf p (mem_filter.mp hp).1
    have h1 : ∏ p ∈ d.primeFactors \ Q.filter (fun p => p ∣ d), (1 - 1 / (p : ℝ)) ≤ 1 := by
      refine prod_le_one (fun p hp => ?_) (fun p hp => ?_)
      · have hp' := Nat.prime_of_mem_primeFactors (mem_sdiff.mp hp).1
        have : (1 : ℝ) ≤ p := by exact_mod_cast hp'.one_lt.le
        rw [sub_nonneg, div_le_one (by linarith)]; exact this
      · have : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
        linarith
    nlinarith
  exact hE

-- The level is shared by every row in the cofactor sum.
theorem affine_upper (Y d x : ℕ) (hY : 4 ≤ Y) (hd0 : 0 < d) (hd : Even d)
    (hx : Y^240 ≤ x) :
    (((range (x+1)).filter (fun p => p.Prime ∧ (1+d*p).Prime)).card : ℝ)
      ≤ 10 * ((x:ℝ) / Real.log Y ^ 2) * pairSingularProduct d := by
  let z := Y^37
  have hYr : (4:ℝ) ≤ Y := by exact_mod_cast hY
  have hL := Real.log_pos (by linarith : 1 < (Y:ℝ))
  have hz : Y < z := by
    change Y < Y^37
    simpa using pow_lt_pow_right₀ (by omega : 1 < Y) (by decide : 1 < 37)
  have hhalf := pair_rankin_half d Y hd hY
  have hEuler := pair_euler_ge d Y hd0 hd
  have hD := singular_compensation d
  have hPP := one_le_pairSingularProduct d
  let P := ∏ p ∈ d.primeFactors, (1-1/(p:ℝ))
  have hP : 0 ≤ P := prod_nonneg fun p hp => by
    have h : (1:ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
    exact sub_nonneg.mpr ((div_le_one (by linarith)).mpr h.le)
  have he := pow_le_pow_left₀ hL.le (OMALib.Mertens.log_le_euler Y) 2
  have hGP : Real.log Y ^ 2 ≤ 4 * (pairG d z * pairSingularProduct d) := by
    nlinarith only [mul_le_mul_of_nonneg_left hD (sq_nonneg (Real.log Y)),
      mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_right he hP).trans hEuler)
        (zero_le_one.trans hPP), mul_le_mul_of_nonneg_right hhalf (zero_le_one.trans hPP)]
  have hG : 0 < pairG d z := by
    by_contra! h
    nlinarith [mul_nonpos_of_nonpos_of_nonneg h (zero_le_one.trans hPP), sq_pos_of_pos hL]
  have hxR : (Y:ℝ)^240 ≤ x := by exact_mod_cast hx
  have hx1 : (1:ℝ) ≤ x := (one_le_pow₀ (by linarith : 1 ≤ (Y:ℝ))).trans hxR
  have hmain : ((x:ℝ)+1)/pairG d z ≤ 8*((x:ℝ)/Real.log Y^2)*pairSingularProduct d := by
    rw [div_le_iff₀ hG]
    field_simp [hL.ne']
    nlinarith only [mul_le_mul_of_nonneg_left hGP (Nat.cast_nonneg x),
      mul_le_mul_of_nonneg_right hx1 (sq_nonneg (Real.log Y))]
  have herr : ((z:ℝ)+(z:ℝ)^6)*Real.log Y^2 ≤ 2*x := by
    have hlog := Real.log_le_sub_one_of_pos (by positivity : 0 < (Y:ℝ))
    have hsq : Real.log Y^2 ≤ (Y:ℝ)^2 := by nlinarith
    have powle (a b : ℕ) (hab : a ≤ b) := pow_le_pow_right₀ (by linarith : 1 ≤ (Y:ℝ)) hab
    dsimp [z]; push_cast
    rw [← pow_mul]
    calc _ ≤ ((Y:ℝ)^222+Y^222)*Y^2 := by gcongr <;> norm_num <;> omega
         _ = 2*(Y:ℝ)^224 := by ring
         _ ≤ _ := by linarith [powle 224 240 (by decide)]
  have hs := affine_count_le_sieve d x z hd0 hd (by omega)
  have hrem : (z:ℝ)+(z:ℝ)^6 ≤ 2*((x:ℝ)/Real.log Y^2) := by
    rw [mul_div_assoc', le_div_iff₀ (by positivity)]; exact herr
  nlinarith only [hs, hmain, hrem, mul_le_mul_of_nonneg_left hPP
    (div_nonneg (Nat.cast_nonneg x) (sq_nonneg (Real.log Y)))]

end OMALib.Sieve

end AffineSieveProof

open Finset Filter Erdos821

namespace Erdos821Design
open OMALib.Sieve

def row (m x : ℕ) : Finset ℕ :=
  (range (x + 1)).filter (fun q => q.Prime ∧ (1 + m * q).Prime)

noncomputable def good (x y : ℕ) : Finset ℕ := by
  classical
  exact (Nat.primesLE x).filter (fun p => ∀ q ∈ (p - 1).primeFactors, q ≤ y)

def slopes (M : ℕ) : Finset ℕ := (Ioc 0 M).filter Even

lemma weight_nonneg (m : ℕ) : 0 ≤ pairSingularProduct m :=
  prod_nonneg fun _ _ => by positivity

lemma weight_le_sum (k : ℕ) (hk : k ≠ 0) :
    pairSingularProduct k ≤ ∑ a ∈ k.divisors, 1/(a:ℝ) := by
  let S := k.primeFactors
  let f (T : Finset ℕ) := ∏ p ∈ T, p
  have divs : S.powerset.image f ⊆ k.divisors := by
    intro a ha
    obtain ⟨T,hT,rfl⟩ := mem_image.mp ha
    exact Nat.mem_divisors.mpr ⟨(Finset.prod_dvd_prod_of_subset _ _ _
      (mem_powerset.mp hT)).trans (Nat.prod_primeFactors_dvd k),hk⟩
  have primes (T : Finset ℕ) (hT : T ∈ S.powerset) : (f T).primeFactors = T :=
    Nat.primeFactors_prod (fun p hp => Nat.prime_of_mem_primeFactors
      (mem_powerset.mp hT hp))
  change (∏ p ∈ S, (1+1/(p:ℝ))) ≤ _
  rw [Finset.prod_one_add]
  calc _ = ∑ a ∈ S.powerset.image f, 1/(a:ℝ) := by
         rw [sum_image (fun T hT U hU he => (primes T hT).symm.trans ((congrArg Nat.primeFactors he).trans (primes U hU)))]
         apply sum_congr rfl
         intro T _
         simp only [f,one_div,Nat.cast_prod,prod_inv_distrib]
       _ ≤ _ := sum_le_sum_of_subset_of_nonneg divs (fun _ _ _ => by positivity)

lemma weight_harmonic :
    ∃ B : ℝ, 0 < B ∧ ∀ M : ℕ,
      (∑ m ∈ Ioc 0 M, pairSingularProduct m / m) ≤ B * (1 + Real.log M) := by
  let f : ArithmeticFunction ℝ := ⟨fun a => 1/(a:ℝ)^2, by simp⟩
  let g : ArithmeticFunction ℝ := ⟨fun b => (b:ℝ)⁻¹, by simp⟩
  have hf : Summable f := Real.summable_one_div_nat_pow.mpr (by decide)
  have hf0 (a) : 0 ≤ f a := by change 0 ≤ 1/(a:ℝ)^2; positivity
  have hg (M : ℕ) : ∑ i ∈ Ioc 0 M, g i ≤ 1+Real.log M := by
    simpa [g,harmonic_eq_sum_Icc,show Ioc 0 M = Icc 1 M by ext i; simp only [mem_Ioc, mem_Icc]; rfl] using harmonic_le_one_add_log M
  refine ⟨(∑' a, f a)+1, add_pos_of_nonneg_of_pos (tsum_nonneg hf0) zero_lt_one, fun M => ?_⟩
  calc _ ≤ ∑ m ∈ Ioc 0 M, (f*g) m := by
         refine sum_le_sum fun m hm => (div_le_div_of_nonneg_right (weight_le_sum m (mem_Ioc.mp hm).1.ne') (Nat.cast_nonneg m)).trans_eq ?_
         rw [sum_div,ArithmeticFunction.mul_apply,Nat.sum_divisorsAntidiagonal (fun a b => f a * g b)]
         refine sum_congr rfl fun a ha => ?_
         have h : (a:ℝ)*((m/a:ℕ):ℝ) = m := by exact_mod_cast Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors ha)
         change 1/(a:ℝ)/(m:ℝ) = 1/(a:ℝ)^2 * ((m/a:ℕ):ℝ)⁻¹
         conv_lhs => rw [← h]
         simp [div_eq_mul_inv,sq,mul_comm,mul_left_comm,mul_assoc]
       _ ≤ (∑ a ∈ Ioc 0 M, f a) * (1+Real.log M) := by
         rw [ArithmeticFunction.sum_Ioc_mul_eq_sum_sum,sum_mul]
         refine sum_le_sum fun a _ => mul_le_mul_of_nonneg_left ((sum_le_sum_of_subset_of_nonneg
           (Ioc_subset_Ioc_right (Nat.div_le_self M a)) (fun i _ _ => by change 0 ≤ (i:ℝ)⁻¹; positivity)).trans (hg M)) (hf0 a)
       _ ≤ _ := by
         exact mul_le_mul_of_nonneg_right ((hf.sum_le_tsum _ fun a _ => hf0 a).trans (le_add_of_nonneg_right zero_le_one)) (by positivity)

-- No uniqueness of the large prime divisor is required.
lemma cover (y M : ℕ) (hy : 2 ≤ y) :
    (Nat.primesLE (y*M)).card ≤ (good (y*M) y).card +
      ∑ m ∈ slopes M, (row m (y*M/m)).card := by
  let bad := (slopes M).biUnion (fun m => (row m (y*M/m)).image (fun q => 1+m*q))
  have hs : Nat.primesLE (y*M) ⊆ good (y*M) y ∪ bad := by
    intro p hp
    obtain ⟨hpx,hpr⟩ := Nat.mem_primesLE.mp hp
    by_cases hg : ∀ q ∈ (p-1).primeFactors, q ≤ y
    · exact mem_union_left _ (by simpa only [good,mem_filter] using And.intro hp hg)
    · push Not at hg
      obtain ⟨q,hq,hqy⟩ := hg
      have hqp := Nat.prime_of_mem_primeFactors hq
      obtain ⟨m, hm⟩ := Nat.dvd_of_mem_primeFactors hq
      have hp1 := hpr.one_lt
      have hm0 : 0 < m := by
        by_contra! hz
        simp [Nat.eq_zero_of_le_zero hz] at hm
        omega
      have heq : 1 + m*q = p := by rw [mul_comm m q, ← hm]; omega
      have hqle := Nat.le_of_dvd (by omega : 0 < p-1) (Nat.dvd_of_mem_primeFactors hq)
      have heven := (hpr.even_sub_one (by omega)).two_dvd
      rw [hm] at heven
      have h2m := (Nat.prime_two.dvd_mul.mp heven).resolve_left
        (fun hd => by have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hqp).mp hd; omega)
      have hmle : m ≤ M := by
        apply le_of_mul_le_mul_left (a := y) _ (by omega)
        exact (Nat.mul_le_mul_right m hqy.le).trans (hm ▸ (by omega : p-1 ≤ y*M))
      have hqbound : q ≤ y*M/m := (Nat.le_div_iff_mul_le hm0).mpr (hm ▸ (by omega : p-1 ≤ y*M))
      exact mem_union_right _ (mem_biUnion.mpr ⟨m,mem_filter.mpr ⟨mem_Ioc.mpr ⟨hm0,hmle⟩,
        even_iff_two_dvd.mpr h2m⟩, mem_image.mpr ⟨q,mem_filter.mpr
          ⟨mem_range.mpr (by omega),hqp,heq ▸ hpr⟩,heq⟩⟩)
  exact (card_le_card hs).trans ((card_union_le _ _).trans (Nat.add_le_add_left
    (card_biUnion_le.trans (sum_le_sum (fun _ _ => card_image_le))) _))

lemma aggregate (y M : ℕ) (hy : 2 ≤ y) (C B : ℝ) (hC : 0 < C)
    (hrow : ∀ m : ℕ, 0 < m → Even m → ∀ X : ℕ, y ≤ X →
      ((row m X).card : ℝ) ≤ C * ((X : ℝ) / Real.log y ^ 2) * pairSingularProduct m)
    (hB : ∑ m ∈ Ioc 0 M, pairSingularProduct m / m ≤ B * (1 + Real.log M)) :
    ((Nat.primesLE (y*M)).card : ℝ) ≤ (good (y*M) y).card +
      (C * ((y*M : ℕ) : ℝ) / Real.log y ^ 2) * (B * (1 + Real.log M)) := by
  have hL : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  have hmrows (m : ℕ) (hm : m ∈ slopes M) :
      ((row m (y*M/m)).card : ℝ) ≤
      (C * ((y*M : ℕ) : ℝ) / Real.log y ^ 2) * (pairSingularProduct m / m) := by
    obtain ⟨hmI, he⟩ := mem_filter.mp hm
    obtain ⟨hm0, hmM⟩ := mem_Ioc.mp hmI
    have hY : y ≤ y*M/m := (Nat.le_div_iff_mul_le hm0).mpr (Nat.mul_le_mul_left y hmM)
    refine (hrow m hm0 he _ hY).trans ?_

    calc C * (((y*M/m : ℕ) : ℝ) / Real.log y ^ 2) * pairSingularProduct m
        ≤ C * ((((y*M : ℕ) : ℝ) / m) / Real.log y ^ 2) * pairSingularProduct m := by
          apply mul_le_mul_of_nonneg_right _ (weight_nonneg m)
          apply mul_le_mul_of_nonneg_left _ hC.le
          exact div_le_div_of_nonneg_right Nat.cast_div_le (sq_nonneg _)

      _ = _ := by ring
  have hsum := sum_le_sum hmrows
  rw [← mul_sum] at hsum
  have hs : (∑ m ∈ slopes M, pairSingularProduct m / m) ≤ B * (1 + Real.log M) :=
    (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      (fun m _ _ => div_nonneg (weight_nonneg m) (Nat.cast_nonneg m))).trans hB
  have hc := cover y M hy
  have hcast : ((Nat.primesLE (y*M)).card : ℝ) ≤
      (good (y*M) y).card + ∑ m ∈ slopes M, ((row m (y*M/m)).card : ℝ) := by
    exact_mod_cast hc
  exact hcast.trans (add_le_add_right (hsum.trans
    (mul_le_mul_of_nonneg_left hs (by positivity))) _)

theorem pi_lower : ∃ y0 : ℕ, ∀ y : ℕ, y0 ≤ y → (y : ℝ) / 3 ≤ (Nat.primesLE y).card * Real.log y := by
  refine ⟨100, fun y hy => ?_⟩
  have h : (100 : ℝ) ≤ y := by exact_mod_cast hy
  have hl := Real.log_le_sub_one_of_pos (show 0 < ((y:ℝ)+1)/4 by positivity)
  rw [Real.log_div (by positivity) (by norm_num)] at hl
  rw [Nat.primesLE_card_eq_primeCounting]
  linarith [Chebyshev.psi_ge y, Chebyshev.psi_le_primeCounting_mul_log y,
    Real.log_le_sub_one_of_pos (show (0:ℝ)<4 by norm_num),
    mul_le_mul_of_nonneg_left Real.log_two_gt_d9.le (Nat.cast_nonneg y)]

-- Choose the exponent gap after both absolute sieve constants are fixed.
lemma parameters (C B : ℝ) (hC : 0 < C) (hB : 0 < B) :
    ∃ D : ℕ, 4 ≤ D ∧ 240 ∣ D ∧ ∀ᶠ t : ℕ in atTop,
      6 * C * B * (1 + Real.log (t^4 : ℕ)) * Real.log (t^(D+4) : ℕ) ≤
        Real.log (t^D : ℕ) ^ 2 ∧ 6 * Real.log (t^(D+4) : ℕ) ≤ t := by
  obtain ⟨j,hj⟩ := exists_nat_ge (60*C*B+4)
  let D := 240*j
  have hD : 60*C*B+4 ≤ D := hj.trans (by dsimp [D]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) j])
  have hCB : 0 < C*B := mul_pos hC hB
  have h4 : (4:ℝ) ≤ D := by nlinarith
  have hD0 : 4 ≤ D := by exact_mod_cast h4
  have hcoeff : (6*C*B) * 5 * ((D:ℝ)+4) ≤ (D:ℝ)^2 := calc
    _ ≤ (6*C*B) * 5 * (2*(D:ℝ)) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right hD (Nat.cast_nonneg D), h4]
  let K : ℝ := 6 * ((D:ℝ)+4)
  have hK : 0 < K := by dsimp [K]; positivity
  have hlim := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (Real.isLittleO_log_id_atTop.bound (c := 1/K) (by positivity))
  have hone := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
    (eventually_ge_atTop 1)
  refine ⟨D,hD0,⟨j,rfl⟩,?_⟩
  filter_upwards [hlim,hone] with t ht hL
  change 1 ≤ Real.log (t:ℝ) at hL
  simp only [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat, Nat.cast_add]
  constructor
  · calc _ ≤ 6*C*B*(5*Real.log t)*(((D:ℝ)+4)*Real.log t) := by
           gcongr <;> linarith
         _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right hcoeff (sq_nonneg (Real.log t))]
  · have h := (Real.le_norm_self _).trans ht
    simp only [id_eq, Real.norm_of_nonneg (Nat.cast_nonneg t), one_div_mul_eq_div] at h
    have := (le_div_iff₀ hK).mp h
    dsimp [K] at this
    linarith

theorem supply : ∃ D : ℕ, 4 ≤ D ∧ ∀ᶠ t : ℕ in atTop,
    t^(D+3) ≤ (good (t^(D+4)) (t^D)).card := by
  let C : ℝ := 10*240^2
  have hC : 0 < C := by norm_num [C]
  obtain ⟨B, hB, hweight⟩ := weight_harmonic
  obtain ⟨D,hD,⟨j,hj⟩,hpar⟩ := parameters C B hC hB
  obtain ⟨x0,hpi⟩ := pi_lower
  refine ⟨D,hD,?_⟩
  filter_upwards [hpar, eventually_ge_atTop 4, eventually_ge_atTop x0] with t ht ht2 ht0
  have hy : 2 ≤ t^D := (by omega : 2 ≤ t).trans (Nat.le_self_pow (by omega) _)
  have hx : t ≤ t^(D+4) := Nat.le_self_pow (by omega) _
  have hπ := hpi _ (ht0.trans hx)
  have hrow (m : ℕ) (hm : 0 < m) (he : Even m) (X : ℕ) (hX : t^D ≤ X) :
      ((row m X).card:ℝ) ≤ C * ((X:ℝ)/Real.log (t^D : ℕ)^2)*pairSingularProduct m := by
    have hjpos : j ≠ 0 := by omega
    have eq : t^D = (t^j)^240 := by rw [← pow_mul, hj, mul_comm]
    rw [eq] at hX ⊢
    have hb := affine_upper (t^j) m X (ht2.trans (Nat.le_self_pow hjpos t)) hm he hX
    rw [Nat.cast_pow (t^j), Real.log_pow]
    convert hb using 1 <;> dsimp [C,row] <;> norm_num <;> ring_nf <;> simp
  have h := aggregate (t^D) (t^4) hy C B hC hrow (hweight _)
  rw [← pow_add] at h
  let X : ℝ := (t^(D+4) : ℕ)
  let L := Real.log X
  let H := Real.log (t^D : ℕ) ^ 2
  let W := B * (1 + Real.log (t^4 : ℕ))
  let N : ℝ := (good (t^(D+4)) (t^D)).card
  have hL : 0 < L := Real.log_pos (by dsimp [X]; exact_mod_cast (by omega : 1 < t^(D+4)))
  have hH : 0 < H := sq_pos_of_pos (Real.log_pos (by exact_mod_cast (by omega : 1 < t^D)))
  have hX : 0 ≤ X := Nat.cast_nonneg _
  change ((Nat.primesLE (t^(D+4))).card : ℝ) ≤ N + (C * X / H) * W at h
  change X / 3 ≤ (Nat.primesLE (t^(D+4))).card * L at hπ
  have h6 : 6 * C * W * L ≤ H := by simpa [W, L, X, H, mul_assoc] using ht.1
  have he : ((C * X / H) * W) * L ≤ X / 6 := by
    rw [show (C*X/H*W)*L = (C*W*L*X)/H by ring, div_le_iff₀ hH]
    nlinarith only [mul_le_mul_of_nonneg_right h6 hX]
  have hN : X ≤ 6 * N * L := by
    nlinarith only [hπ, mul_le_mul_of_nonneg_right h hL.le, he]
  have hsmall : 6 * L ≤ t := ht.2
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hscale : ((t^(D+3) : ℕ) : ℝ) * t ≤ N * t := calc
    _ = X := by dsimp [X]; exact_mod_cast (pow_succ t (D+3)).symm
    _ ≤ 6 * N * L := hN
    _ ≤ N * t := by nlinarith only [mul_le_mul_of_nonneg_left hsmall hN0]
  dsimp [N] at hscale
  exact_mod_cast (le_of_mul_le_mul_right hscale (by positivity : (0 : ℝ) < t))

lemma block_choose (b k : ℕ) (hb : 1 ≤ b) :
    b ^ k ≤ (b * k).choose k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.choose_mul_right (Nat.succ_ne_zero k), Nat.succ_sub_one, pow_succ']
    apply Nat.mul_le_mul_left
    apply ih.trans (Nat.choose_le_choose k ?_)
    rw [Nat.mul_succ]
    omega

-- Recover the subset of primes from the product before counting totients.
lemma many_products (b k x y : ℕ) (hb : 1 ≤ b) (P : Finset ℕ) (hcard : b*k ≤ P.card)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ x ∧ ∀ q ∈ (p-1).primeFactors, q ≤ y) :
    ∃ S : Finset ℕ, b^k ≤ S.card ∧ ∀ m ∈ S,
      0 < m.totient ∧ m.totient ≤ x^k ∧ ∀ q ∈ m.totient.primeFactors, q ≤ y := by
  let S := (P.powersetCard k).image (fun A => ∏ p ∈ A, p)
  have hS : S.card = P.card.choose k := by
    apply (Finset.card_image_of_injOn ?_).trans (Finset.card_powersetCard ..)
    intro A hA B hB hab
    have h := congrArg Nat.primeFactors hab
    rwa [Nat.primeFactors_prod (fun p hp => (hP p ((Finset.mem_powersetCard.mp hA).1 hp)).1),
      Nat.primeFactors_prod (fun p hp => (hP p ((Finset.mem_powersetCard.mp hB).1 hp)).1)] at h
  refine ⟨S, ?_, ?_⟩
  · rw [hS]
    exact (block_choose b k hb).trans (Nat.choose_le_choose _ hcard)
  · intro m hm
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨hsub, hsize⟩ := Finset.mem_powersetCard.mp hA
    have hprime (p) (hp : p ∈ A) : Nat.Prime p := (hP p (hsub hp)).1
    have hpos := Finset.prod_pos (s := A) (f := id) (fun p hp => (hprime p hp).pos)
    refine ⟨Nat.totient_pos.mpr hpos, ?_, ?_⟩
    · calc
        Nat.totient (∏ p ∈ A, p) ≤ ∏ p ∈ A, p := Nat.totient_le _
        _ ≤ x^A.card := Finset.prod_le_pow_card _ _ _ (fun p hp => (hP p (hsub hp)).2.1)
        _ = _ := by rw [hsize]
    · have hphi := Nat.totient_mul_prod_primeFactors (∏ p ∈ A, p)
      rw [Nat.primeFactors_prod hprime, mul_comm (∏ p ∈ A, p)] at hphi
      have he := Nat.mul_right_cancel hpos hphi
      intro q hq
      have hdiv := Nat.dvd_of_mem_primeFactors hq
      rw [he] at hdiv
      obtain ⟨p, hp, hd⟩ := ((Nat.prime_of_mem_primeFactors hq).prime.dvd_finsetProd_iff _).mp hdiv
      exact (hP p (hsub hp)).2.2 q (Nat.mem_primeFactors.mpr
        ⟨Nat.prime_of_mem_primeFactors hq, hd, by have := (hprime p hp).two_le; omega⟩)

lemma fiber_finite (n : ℕ) (hn : 0 < n) : {m : ℕ | Nat.totient m = n}.Finite := by
  obtain ⟨q, hq, hp⟩ := Nat.exists_infinite_primes (n + 2)
  have hpow : 1 < q ^ n := one_lt_pow₀ hp.one_lt hn.ne'
  apply (Set.finite_Iic (q ^ n - 1)).subset
  intro m hm
  change m.totient = n at hm
  have hc : q.Coprime m := hp.coprime_iff_not_dvd.mpr fun h => by
    have hd := Nat.totient_dvd_of_dvd h
    rw [Nat.totient_prime hp, hm] at hd
    have := Nat.le_of_dvd hn hd
    omega
  have he := Nat.ModEq.pow_totient hc
  rw [hm] at he
  exact Nat.le_of_dvd (Nat.sub_pos_of_lt hpow) ((Nat.modEq_iff_dvd' hpow.le).mp he.symm)

def values (x y : ℕ) : Finset ℕ :=
  (Finset.Icc 1 x).filter (fun n => ∀ p ∈ n.primeFactors, p ≤ y)

lemma smooth_box (x U Y : ℕ) (hx : x ≤ 2^U) : (values x Y).card ≤ (U+1)^Y := by
  let S := values x Y
  have hmem (n : ↥S) := mem_filter.mp n.property
  have hpos (n : ↥S) : 0 < n.val := (mem_Icc.mp (hmem n).1).1
  have hexp (n : ↥S) (p : ℕ) : n.val.factorization p < U+1 := by
    by_cases hp : p.Prime
    · have h := (Nat.pow_le_pow_left hp.two_le (n.val.factorization p)).trans <|
        (Nat.ordProj_le p (hpos n).ne').trans ((mem_Icc.mp (hmem n).1).2.trans hx)
      exact Nat.lt_succ_of_le ((pow_le_pow_iff_right₀ (by decide : 1 < (2:ℕ))).mp h)
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  let code (n : ↥S) (p : ↥(Finset.Icc 1 Y)) : Fin (U+1) :=
    ⟨n.val.factorization p.val, hexp n p.val⟩
  have hinj : Function.Injective code := by
    intro m n heq
    apply Subtype.ext
    apply Nat.eq_of_factorization_eq (hpos m).ne' (hpos n).ne'
    intro p
    by_cases hp : p ∈ Finset.Icc 1 Y
    · exact congrArg Fin.val (congrFun heq ⟨p, hp⟩)
    · have hout (k : ↥S) : k.val.factorization p = 0 := by
        apply Finsupp.notMem_support_iff.mp
        exact fun h => hp <| mem_Icc.mpr ⟨(Nat.prime_of_mem_primeFactors h).one_le, (hmem k).2 p h⟩
      rw [hout m, hout n]
  simpa [S] using Fintype.card_le_of_injective code hinj

-- The extra power of t in the subset size absorbs the exponent-code length.
lemma few_values (D : ℕ) : ∀ᶠ t : ℕ in atTop,
    (values ((t^(D+4))^(t^(D+1))) (t^D)).card ≤ t^(t^(D+1)) := by
  filter_upwards [eventually_ge_atTop (D+5)] with t ht
  let k := t^(D+1)
  let U := t * ((D+4)*k)
  have ht2 : 2 ≤ t := by omega
  have hpos : 0 < t := by omega
  have hlarge : (t^(D+4))^k ≤ 2^U := by
    rw [← pow_mul]
    exact (Nat.pow_le_pow_left Nat.lt_two_pow_self.le _).trans_eq (pow_mul 2 t _).symm
  have hU : U+1 ≤ t^(D+4) := by
    have h₁ : U ≤ t^(D+3) := calc
      _ ≤ t * (t*k) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
      _ = _ := by dsimp [k]; rw [pow_succ t (D+2), pow_succ t (D+1)]; ring
    have h₂ : t^(D+3) < t^(D+4) := pow_lt_pow_right₀ (by omega) (by omega)
    omega
  calc _ ≤ (U+1)^(t^D) := smooth_box _ _ _ hlarge
    _ ≤ (t^(D+4))^(t^D) := Nat.pow_le_pow_left hU _
    _ ≤ t^k := by
      rw [← pow_mul]
      apply pow_le_pow_right₀ (by omega : 1 ≤ t)
      dsimp [k]
      rw [pow_succ, mul_comm (t^D)]
      exact Nat.mul_le_mul_right _ (by omega)


lemma collision (t k a : ℕ) (ht : 2 ≤ t) (hk : 0 < k) (S T : Finset ℕ)
    (hmap : ∀ m ∈ S, m.totient ∈ T)
    (hrange : ∀ n ∈ T, 0 < n ∧ n ≤ (t^k)^a)
    (hmany : (t^k)*(t^k) ≤ S.card) (hfew : T.card ≤ t^k) :
    ∃ n : ℕ, (n : ℝ) ^ (1 / ((a : ℝ) + 1)) < (g n : ℝ) ∧ t ≤ g n := by
  let r := t^k
  have htr : t ≤ r := Nat.le_self_pow hk.ne' t
  have hr : 1 < r := by omega
  have hcount : T.card * r ≤ S.card := (Nat.mul_le_mul_right r hfew).trans hmany
  obtain ⟨m, hm⟩ := Finset.card_pos.mp (lt_of_lt_of_le (by positivity) hmany)
  obtain ⟨n, hn, hf⟩ := Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to hmap
    ⟨m.totient, hmap m hm⟩ hcount
  have hsub : (↑(S.filter (fun m => m.totient = n)) : Set ℕ) ⊆ {m : ℕ | m.totient = n} :=
    fun _ hx => (mem_filter.mp hx).2
  have hrg : r ≤ g n := hf.trans (by
    simpa only [Set.ncard_coe_finset, Erdos821.g] using
      Set.ncard_le_ncard hsub (fiber_finite n (hrange n hn).1))
  have hnr : (n : ℝ) ≤ (r : ℝ)^a := by exact_mod_cast (hrange n hn).2
  have hr' : 1 < (r : ℝ) := by exact_mod_cast hr
  refine ⟨n, lt_of_lt_of_le ?_ (by exact_mod_cast hrg : (r : ℝ) ≤ g n), htr.trans hrg⟩
  apply (Real.rpow_lt_rpow_iff (by positivity) (by positivity)
    (by positivity : 0 < (a : ℝ) + 1)).mp
  rw [← Real.rpow_mul (by positivity), one_div_mul_cancel (by positivity : (a : ℝ) + 1 ≠ 0),
    Real.rpow_one, ← Nat.cast_succ, Real.rpow_natCast]
  exact hnr.trans_lt (pow_lt_pow_right₀ hr' (Nat.lt_succ_self a))

theorem conclusion (D : ℕ)
    (hs : ∀ᶠ t : ℕ in atTop, t^(D+3) ≤ (good (t^(D+4)) (t^D)).card) :
    type_of% @Erdos821.erdos_821.variants.erdos := by
  refine ⟨1 / (((D+4 : ℕ) : ℝ) + 1), by positivity, ?_⟩
  by_contra hn
  obtain ⟨B, hB⟩ := ((Set.not_infinite.mp hn).image g).bddAbove
  obtain ⟨t,ht,hB',hP,hfew⟩ := ((eventually_ge_atTop 2).and
    ((eventually_gt_atTop B).and (hs.and (few_values D)))).exists
  let k := t^(D+1)
  let x := t^(D+4)
  let y := t^D
  have hcard : (t^2)*k ≤ (good x y).card := by
    simpa only [k, x, y, ← pow_add, show 2+(D+1) = D+3 by omega] using hP
  have hgood (p : ℕ) (hp : p ∈ good x y) :
      p.Prime ∧ p ≤ x ∧ ∀ q ∈ (p-1).primeFactors, q ≤ y := by
    simp only [good,mem_filter] at hp
    obtain ⟨hp0,hs'⟩ := hp
    exact ⟨(Nat.mem_primesLE.mp hp0).2,(Nat.mem_primesLE.mp hp0).1,hs'⟩
  obtain ⟨S,hmany,hmap⟩ := many_products (t^2) k x y (one_le_pow₀ (by omega : 1 ≤ t)) _ hcard hgood
  obtain ⟨n,hn',htn⟩ := collision t k (D+4) ht (by dsimp [k]; positivity) S (values (x^k) y)
    (fun m hm => by obtain ⟨h1,h2,h3⟩ := hmap m hm; exact mem_filter.mpr ⟨mem_Icc.mpr ⟨h1,h2⟩,h3⟩)
    (fun n hn => by
      obtain ⟨h0,h1⟩ := mem_Icc.mp (mem_filter.mp hn).1
      refine ⟨h0,?_⟩
      simpa only [x, ← pow_mul, Nat.mul_comm (D+4) k] using h1)
    (by simpa only [← pow_add, ← pow_mul, two_mul] using hmany) hfew
  exact hB'.not_ge (htn.trans (hB ⟨n,hn',rfl⟩))

end Erdos821Design

theorem OMA.solution : type_of% @Erdos821.erdos_821.variants.erdos := by
  obtain ⟨D,_,h⟩ := Erdos821Design.supply
  exact Erdos821Design.conclusion D h
