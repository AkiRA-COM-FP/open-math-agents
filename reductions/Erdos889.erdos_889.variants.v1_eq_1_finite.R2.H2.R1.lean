import OMAReductions.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic
import Mathlib.NumberTheory.Pell
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Multiplicity
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

/-! Restrictions on the prime-square branch of Erdős problem 889. -/

namespace OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2_H2_R1

private theorem split_factor_exponent (e : ℕ) :
    ∃ i j : ℕ, e=i+j*2 ∧ i≤3 ∧ (0 < j → 2 ≤ i) := by
  by_cases small : e≤3
  · exact ⟨e,0,by omega,small,by omega⟩
  · exact ⟨2+e%2,(e-2)/2,by omega,by omega,by omega⟩

private theorem smooth_square_decomposition (T n : ℕ) (hn : 0 < n)
    (smooth : ∀ q : ℕ, q.Prime → q∣n → q ≤ T) :
    ∃ D y : ℕ, D≤(T+1).factorial^3 ∧ 0 < D ∧ 0 < y ∧ n=D*y^2 ∧
      ∀ q : ℕ, q.Prime → q∣y → q^2∣D := by
  induction T generalizing n with
  | zero =>
    have unit : n=1 := by
      by_contra ne
      obtain ⟨q,pq,dq⟩ := Nat.exists_prime_and_dvd ne
      have := smooth q pq dq
      have := pq.two_le
      omega
    refine ⟨1,1,by decide,by decide,by decide,by simpa only [one_pow,mul_one] using unit,?_⟩
    intro q pq div
    have := Nat.le_of_dvd (by decide : 0<1) div
    have := pq.two_le
    omega
  | succ t ih =>
    let p := t+1
    let e := n.factorization p
    let m := n/p^e
    have fac : p^e*m=n := Nat.ordProj_mul_ordCompl_eq_self n p
    have dm : m∣n := Nat.ordCompl_dvd n p
    have pos : 0 < m := Nat.ordCompl_pos p hn.ne'
    have smaller (q : ℕ) (pq : q.Prime) (dq : q∣m) : q ≤ t := by
      have upper := smooth q pq (dq.trans dm)
      by_contra! high
      have equal : q=p := by dsimp [p]; omega
      rw [equal] at pq dq
      exact (Nat.not_dvd_ordCompl pq hn.ne') dq
    obtain ⟨D,y,cap,hD,hy,form,divisors⟩ := ih m pos smaller
    obtain ⟨i,j,ei,i3,ji⟩ := split_factor_exponent e
    have small : p^i ≤ (t+2)^3 :=
      (Nat.pow_le_pow_right (show 0 < p by dsimp [p]; omega) i3).trans
        (Nat.pow_le_pow_left (show p ≤ t+2 by dsimp [p]; omega) 3)
    have total : D*p^i ≤ (t+1+1).factorial^3 := by
      have bound := Nat.mul_le_mul cap small
      rw [Nat.factorial_succ (t+1),mul_pow,Nat.mul_comm ((t+1+1)^3)]
      exact bound
    refine ⟨D*p^i,y*p^j,total,Nat.mul_pos hD (pow_pos (by dsimp [p]; omega) _),
      Nat.mul_pos hy (pow_pos (by dsimp [p]; omega) _),?_,?_⟩
    · calc
        n = p^e*m := fac.symm
        _ = _ := by rw [form,ei,pow_add,pow_mul,mul_pow]; ring
    · intro q pq dq
      rcases pq.dvd_mul.mp dq with fromY|fromP
      · exact dvd_mul_of_dvd_left (divisors q pq fromY) _
      · have jp : 0 < j := by
          by_contra! low
          have zero : j=0 := by omega
          rw [zero,pow_zero] at fromP
          have := Nat.le_of_dvd (by decide : 0<1) fromP
          have := pq.two_le
          omega
        have pp : p.Prime := by
          by_contra np
          have zero : e=0 := Nat.factorization_eq_zero_of_not_prime n np
          omega
        have same := (Nat.prime_dvd_prime_iff_eq pq pp).mp (pq.dvd_of_dvd_pow fromP)
        rw [same]
        exact dvd_mul_of_dvd_right (pow_dvd_pow p (ji jp)) _

/-- Every square-plus-one supported on primes at most T gives a negative Pell
equation with D in an explicit finite interval. Each prime dividing its
positive y-coordinate has its square dividing D. -/
theorem quadratic_smooth_decomposition (T x : ℕ)
    (smooth : ∀ q : ℕ, q.Prime → q∣x^2+1 → q ≤ T) :
    ∃ D ∈ Finset.Icc 1 ((T+1).factorial^3), ∃ y : ℕ, 0 < D ∧ 0 < y ∧
      x^2+1=D*y^2 ∧ ∀ q : ℕ, q.Prime → q∣y → q^2∣D := by
  obtain ⟨D,y,cap,hD,hy,form,divisors⟩ := smooth_square_decomposition T (x^2+1) (by omega) smooth
  exact ⟨D,Finset.mem_Icc.mpr ⟨hD,cap⟩,y,hD,hy,form,divisors⟩



-- BEGIN PELL VALUATION
private theorem pell_expansion_remainder {d : ℤ} (z : Pell.Solution₁ d) (n : ℕ) :
    ∃ L K : ℤ, (z^(n+1)).x=z.x^(n+1)+d*L ∧
      (z^(n+1)).y=z.y*((n+1 : ℕ)*(z.x^n)+d*K) := by
  induction n with
  | zero => exact ⟨0,0,by simp,by simp⟩
  | succ n ih =>
    obtain ⟨L,K,hx,hy⟩ := ih
    refine ⟨L*z.x+(z^(n+1)).y*z.y,L+K*z.x,?_,?_⟩
    · change (z^(n+1)*z).x=z.x^(n+1+1)+d*(L*z.x+(z^(n+1)).y*z.y)
      rw [Pell.Solution₁.x_mul,hx,pow_succ z.x (n+1)]
      ring
    · change (z^(n+1)*z).y=z.y*((n+1+1:ℕ)*z.x^(n+1)+d*(L+K*z.x))
      rw [Pell.Solution₁.y_mul,hx,hy,pow_succ z.x n]
      push_cast
      ring

private theorem pell_prime_multiplier {D l q : ℕ} (z : Pell.Solution₁ (D:ℤ))
    (pl : l.Prime) (pq : q.Prime) (dq : q^2∣D) :
    ∃ k : ℕ, (z^l).y.natAbs=z.y.natAbs*k ∧ k≠0 ∧ k.factorization q=l.factorization q := by
  let _ : Fact q.Prime := ⟨pq⟩
  obtain ⟨_,K,_,hy⟩ := pell_expansion_remainder z (l-1)
  rw [Nat.sub_add_cancel pl.one_le] at hy
  obtain ⟨h,dh⟩ := dq
  have dint : (D:ℤ)=(q:ℤ)^2*h := by exact_mod_cast dh
  have zd : (D:ZMod q)=0 := (ZMod.natCast_eq_zero_iff _ _).mpr (dh ▸ dvd_mul_of_dvd_left (dvd_pow_self q (by decide : (2:ℕ)≠0)) h)
  have xz : (z.x:ZMod q)≠0 := by
    intro zero
    have f := congrArg (fun v:ℤ => (v:ZMod q)) z.prop
    push_cast at f
    rw [zd,zero,zero_pow two_ne_zero,zero_mul,sub_zero] at f
    exact zero_ne_one f
  let a := z.x^(l-1)
  have an : (a:ZMod q)≠0 := by dsimp [a]; push_cast; exact pow_ne_zero _ xz
  have no {c : ℤ} (hc : (c:ZMod q)≠0) : ¬q∣c.natAbs :=
    fun dd => hc ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (Int.natCast_dvd.mpr dd))
  by_cases same : l=q
  · subst l
    let c := a+(q:ℤ)*h*K
    have cn : ¬q∣c.natAbs := no (by simpa [c] using an)
    have nc : c.natAbs≠0 := fun e => cn (e ▸ dvd_zero q)
    have yq : (z^q).y=z.y*((q:ℤ)*c) := by
      rw [hy]
      dsimp only [a,c]
      linear_combination z.y*K*dint
    refine ⟨q*c.natAbs,?_,mul_ne_zero pq.ne_zero nc,?_⟩
    · rw [yq]; simp only [Int.natAbs_mul,Int.natAbs_natCast]
    · rw [Nat.factorization_mul pq.ne_zero nc,Finsupp.add_apply,Nat.factorization_eq_zero_of_not_dvd cn,add_zero]
  · have nl : ¬q∣l := fun h => same ((Nat.prime_dvd_prime_iff_eq pq pl).mp h).symm
    have lv : (l:ZMod q)≠0 := fun h => nl ((ZMod.natCast_eq_zero_iff _ _).mp h)
    let c := (l:ℤ)*a+(D:ℤ)*K
    have cn : ¬q∣c.natAbs := no (by
      dsimp only [c]
      push_cast
      rw [zd,zero_mul,add_zero]
      exact mul_ne_zero lv an)
    have nc : c.natAbs≠0 := fun e => cn (e ▸ dvd_zero q)
    refine ⟨c.natAbs,?_,nc,?_⟩
    · rw [hy,Int.natAbs_mul]
    · rw [Nat.factorization_eq_zero_of_not_dvd cn,Nat.factorization_eq_zero_of_not_dvd nl]

/-- At a prime whose square divides D, the imaginary coordinate of a Pell power gains exactly the exponent's valuation. -/
theorem pell_factorization_y_pow {D q n : ℕ} (eps : Pell.Solution₁ (D : ℤ))
    (pq : q.Prime) (dq : q^2∣D) (hn : 0 < n) :
    (eps^n).y.natAbs.factorization q = (n*eps.y.natAbs).factorization q := by
  by_cases hzero : eps.y=0
  · obtain ⟨_,_,_,hy⟩ := pell_expansion_remainder eps (n-1)
    rw [Nat.sub_add_cancel hn,hzero,zero_mul] at hy
    simp [hy,hzero]
  have base : eps.y.natAbs≠0 := fun h => hzero (Int.natAbs_eq_zero.mp h)
  have all : ∀ j : ℕ, j≠0 → (eps^j).y.natAbs≠0 ∧
      (eps^j).y.natAbs.factorization q=(j*eps.y.natAbs).factorization q := by
    apply induction_on_primes
    · simp
    · simp [base]
    · intro l a pl ih nz
      have ap : a≠0 := fun e => nz (by rw [e,mul_zero])
      obtain ⟨nonzero,ihv⟩ := ih ap
      obtain ⟨k,mult,kpos,kv⟩ := pell_prime_multiplier (eps^a) pl pq dq
      have e : eps^(l*a)=(eps^a)^l := by rw [←pow_mul,Nat.mul_comm]
      rw [e,mult]
      refine ⟨mul_ne_zero nonzero kpos,?_⟩
      rw [Nat.factorization_mul nonzero kpos,Finsupp.add_apply,kv,ihv,Nat.mul_assoc,
        Nat.factorization_mul pl.ne_zero (mul_ne_zero ap base),Finsupp.add_apply,Nat.add_comm]
  exact (all n hn.ne').2
-- END PELL VALUATION


private theorem cube_le_two_pow {m : ℕ} (hm : 10 ≤ m) : m^3≤2^m := by
  induction m,hm using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    rw [pow_succ 2 k]
    have step : (k+1)^3≤2*k^3 := by
      have k2 : 5*k ≤ k^2 := by nlinarith [Nat.mul_le_mul_right k (show 5 ≤ k by omega)]
      nlinarith [Nat.mul_le_mul_right (k^2) (show 5 ≤ k by omega)]
    omega

private theorem pell_growth {D : ℤ} (eps : Pell.Solution₁ D) (hx : 1 < eps.x)
    (hy : 0 < eps.y) (n : ℕ) : (2:ℤ)^n*eps.y ≤ (eps^(n+1)).y := by
  induction n with
  | zero => simp
  | succ n ih =>
    have sx := Pell.Solution₁.x_pow_pos (show 0 < eps.x by omega) (n+1)
    have sy := Pell.Solution₁.y_pow_succ_pos (show 0 < eps.x by omega) hy n
    have grow := mul_le_mul_of_nonneg_left (show (2:ℤ) ≤ eps.x by omega) sy.le
    rw [pow_succ, show n+1+1=(n+1)+1 by rfl, pow_succ eps (n+1),Pell.Solution₁.y_mul]
    nlinarith [mul_pos sx hy]

private theorem quadratic_twist_bound (D : ℕ)
    (valuation : ∀ (eps : Pell.Solution₁ (D:ℤ)) (q n : ℕ), q.Prime → q^2∣D →
      0 < n → 1 < eps.x → 0 < eps.y →
      ((eps^n).y.natAbs).factorization q=(n*eps.y.natAbs).factorization q) :
    ∃ B : ℕ, ∀ x y : ℕ, 0 < y → x^2+1=D*y^2 →
      (∀ q : ℕ, q.Prime → q∣y → q^2∣D) → x ≤ B := by
  classical
  by_cases has : ∃ e : Pell.Solution₁ (D:ℤ), Pell.IsFundamental e
  · obtain ⟨eps,he⟩ := has
    let Y := eps.y.natAbs
    refine ⟨D*(10+4*D*Y)*Y,?_⟩
    intro x y hy eq support
    by_cases hx : x=0
    · omega
    have castEq : (x:ℤ)^2+1=(D:ℤ)*(y:ℤ)^2 := by exact_mod_cast eq
    have id : ((2:ℤ)*x^2+1)^2-D*(2*(x:ℤ)*y)^2=1 := by
      linear_combination -4*(x:ℤ)^2*(castEq.symm)
    let sol : Pell.Solution₁ (D:ℤ) := Pell.Solution₁.mk _ _ id
    have sx : sol.x=2*(x:ℤ)^2+1 := rfl
    have sy : sol.y=2*(x:ℤ)*y := rfl
    obtain ⟨n,hn⟩ := he.eq_pow_of_nonneg (a:=sol) (by rw [sx]; positivity) (by rw [sy]; positivity)
    have nz : 0 < n := by
      by_contra! h
      have : n=0 := by omega
      rw [this,pow_zero] at hn
      have eqy := congrArg Pell.Solution₁.y hn
      rw [sy,Pell.Solution₁.y_one] at eqy
      have : 0<(x:ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hx
      have pos : 0<2*(x:ℤ)*y := by positivity
      omega
    have YY : 0 < Y := by dsimp [Y]; exact Int.natAbs_pos.mpr he.2.1.ne'
    have imag : (eps^n).y.natAbs=2*x*y := by
      rw [←hn,sy,Int.natAbs_mul,Int.natAbs_mul]
      rfl
    have ydiv : y∣n*Y := by
      apply (Nat.factorization_le_iff_dvd hy.ne' (Nat.mul_pos nz YY).ne').mp
      intro q
      by_cases pq : q.Prime
      · by_cases dy : q∣y
        · have div : y∣2*x*y := dvd_mul_left _ _
          have nonz : 2*x*y≠0 := by positivity
          have le := (Nat.factorization_le_iff_dvd hy.ne' nonz).mpr div q
          rw [←imag,valuation eps q n pq (support q pq dy) nz he.1 he.2.1] at le
          exact le
        · simp [Nat.factorization_eq_zero_of_not_dvd dy]
      · simp [Nat.factorization_eq_zero_of_not_prime _ pq]
    have ybound := Nat.le_of_dvd (Nat.mul_pos nz YY) ydiv
    have Dx : x ≤ D*y := by
      have hD : 0 < D := by exact_mod_cast he.d_pos
      by_contra! large
      have h := Nat.mul_le_mul (show 1 ≤ D by omega) (Nat.le_refl (D*y^2))
      nlinarith [Nat.mul_self_lt_mul_self large]
    have expBound : 2^n*Y ≤ 4*x*y := by
      obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero nz.ne'
      have low := pell_growth eps he.1 he.2.1 j
      have eqy := congrArg Pell.Solution₁.y hn
      rw [←eqy,sy] at low
      have castY : (Y:ℤ)=eps.y := Int.natAbs_of_nonneg he.2.1.le
      change (2:ℕ)^(j+1)*Y ≤ 4*x*y
      zify
      rw [castY,pow_succ]
      linarith
    have nbound : n≤10+4*D*Y := by
      by_cases big : 10 ≤ n
      · have cube := cube_le_two_pow big
        have upper := Nat.mul_le_mul Dx ybound
        have upper' := Nat.mul_le_mul (Nat.mul_le_mul_left D ybound) (Nat.le_refl (n*Y))
        have all : n^3*Y≤(4*D*Y)*(n^2*Y) := by
          nlinarith [Nat.mul_le_mul_right Y cube]
        have eqN : n^3*Y=n*(n^2*Y) := by ring
        rw [eqN] at all
        have := Nat.le_of_mul_le_mul_right all (by positivity : 0 < n^2*Y)
        omega
      · omega
    exact Dx.trans (by calc
      D*y ≤ D*(n*Y) := Nat.mul_le_mul_left _ ybound
      _ ≤ D*((10+4*D*Y)*Y) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ nbound)
      _ = _ := by ring)
  · refine ⟨0,?_⟩
    intro x y hy eq _
    by_contra! xbig
    have castEq : (x:ℤ)^2+1=(D:ℤ)*(y:ℤ)^2 := by exact_mod_cast eq
    have id : ((2:ℤ)*x^2+1)^2-D*(2*(x:ℤ)*y)^2=1 := by
      linear_combination -4*(x:ℤ)^2*(castEq.symm)
    let sol : Pell.Solution₁ (D:ℤ) := Pell.Solution₁.mk _ _ id
    have sx : 1 < sol.x := by
      change 1<2*(x:ℤ)^2+1
      have hxZ : 0<(x:ℤ) := by exact_mod_cast xbig
      nlinarith [sq_pos_of_pos hxZ]
    exact has (Pell.IsFundamental.exists_of_not_isSquare
      (Pell.Solution₁.d_pos_of_one_lt_x sx) (Pell.Solution₁.d_nonsquare_of_one_lt_x sx))


/-- The greatest prime factor of x²+1 eventually exceeds each fixed bound. -/
theorem large_prime_of_square_add_one (T : ℕ) : ∃ B : ℕ, ∀ x : ℕ, B < x →
    ∃ q : ℕ, q.Prime ∧ T < q ∧ q∣x^2+1 := by
  classical
  have bounds (D : ℕ) := quadratic_twist_bound D (fun eps q n pr dv hn _ _ =>
    pell_factorization_y_pow eps pr dv hn)
  choose bound covers using bounds
  let ds := Finset.Icc 1 ((T+1).factorial^3)
  refine ⟨ds.sup bound,?_⟩
  intro x hx
  by_contra missing
  have smooth (q : ℕ) (pr : q.Prime) (dv : q∣x^2+1) : q ≤ T := by
    by_contra! big
    exact missing ⟨q,pr,big,dv⟩
  obtain ⟨D,hd,y,_,hy,eq,dv⟩ := quadratic_smooth_decomposition T x smooth
  exact (not_lt_of_ge ((covers D x y hy eq dv).trans (Finset.le_sup (f:=bound) hd))) hx

private theorem two_primes {n k p q : ℕ} (hk : 0<k) (pp : p.Prime) (pq : q.Prime)
    (ne : p≠q) (hp : k<p) (hq : k<q) (dp : p∣n+k) (dq : q∣n+k) : (¬∃ k u v : ℕ, 0<k ∧ u.Prime ∧ v.Prime ∧ u≠v ∧ k<u ∧ k<v ∧ u∣n+k ∧ v∣n+k) → False :=
  fun missing => missing ⟨k,p,q,hk,pp,pq,ne,hp,hq,dp,dq⟩

lemma odd_cofactor {x r : ℕ} (ox : Odd x) (hx : 1 < x) (orr : Odd r) (hr : 1 < r) :
    ∃ c : ℕ, Odd c ∧ r < c ∧ x^r+1 = (x+1)*c := by
  obtain ⟨w, hw⟩ := ox
  obtain ⟨j, rfl⟩ := orr
  have wp : 0 < w := by omega
  have hx3 : 3 ≤ x := by omega
  have aux (i : ℕ) : ∃ z : ℕ, 2*i ≤ z ∧ x^(2*i+1)+1 = (x+1)*(2*z+1) := by
    induction i with
    | zero => exact ⟨0, by decide, by simp⟩
    | succ i ih =>
      obtain ⟨z, hz, he⟩ := ih
      refine ⟨x^2*z+w*x, ?_, ?_⟩
      · have mulz : z ≤ x^2*z := by
          simpa using Nat.mul_le_mul_right z (show 1 ≤ x^2 by exact Nat.one_le_pow _ _ (by omega))
        have mulw : 3 ≤ w*x := by simpa using Nat.mul_le_mul wp hx3
        omega
      · rw [show 2*(i+1)+1 = (2*i+1)+2 by omega, pow_add]
        have scaled := congrArg (fun m : ℕ => m*x^2) he
        rw [hw] at scaled ⊢
        nlinarith only [scaled]
  obtain ⟨z, hz, he⟩ := aux j
  exact ⟨2*z+1, ⟨z,rfl⟩, by omega, he⟩

private theorem smooth_fourth_decomposition (T n : ℕ) (hn : 0<n)
    (smooth : ∀ q : ℕ, q.Prime → q∣n → q≤T) :
    ∃ C z : ℕ, C≤T.factorial^3 ∧ 0<C ∧ 0<z ∧ n=C*z^4 := by
  induction T generalizing n with
  | zero =>
    have unit : n=1 := by
      by_contra ne
      obtain ⟨q,pq,dq⟩ := Nat.exists_prime_and_dvd ne
      have := smooth q pq dq
      have := pq.two_le
      omega
    exact ⟨1,1,by decide,by decide,by decide,by simpa only [one_pow,mul_one] using unit⟩
  | succ t ih =>
    let p := t+1
    let e := n.factorization p
    let m := n/p^e
    have fac : p^e*m=n := Nat.ordProj_mul_ordCompl_eq_self n p
    have dm : m∣n := Nat.ordCompl_dvd n p
    have pos : 0 < m := Nat.ordCompl_pos p hn.ne'
    have smaller (q : ℕ) (pq : q.Prime) (dq : q∣m) : q≤t := by
      have upper := smooth q pq (dq.trans dm)
      by_contra! high
      have equal : q=p := by dsimp [p]; omega
      rw [equal] at pq dq
      exact (Nat.not_dvd_ordCompl pq hn.ne') dq
    obtain ⟨C,z,cap,hC,hz,form⟩ := ih m pos smaller
    have ppos : 0<p := by dsimp [p]; omega
    have small : p^(e%4)≤p^3 := Nat.pow_le_pow_right ppos (by omega)
    have total : C*p^(e%4)≤(t+1).factorial^3 := by
      rw [Nat.factorial_succ,mul_pow,Nat.mul_comm ((t+1)^3)]
      exact Nat.mul_le_mul cap small
    refine ⟨C*p^(e%4),z*p^(e/4),total,Nat.mul_pos hC (pow_pos ppos _),
      Nat.mul_pos hz (pow_pos ppos _),?_⟩
    have ei : e=e%4+(e/4)*4 := by rw [Nat.mul_comm (e/4) 4,Nat.mod_add_div]
    calc
      n = p^e*m := fac.symm
      _ = p^(e%4+(e/4)*4)*(C*z^4) := by rw [←ei,form]
      _ = _ := by rw [pow_add,pow_mul,mul_pow]; ring

private theorem two_quadratic_factors {T u : ℕ} (hT : 4≤T)
    (h₁ : ∃ q : ℕ, q.Prime ∧ T<q ∧ q∣u^2+1)
    (h₂ : ∃ q : ℕ, q.Prime ∧ T<q ∧ q∣(u+2)^2+1) :
    ∃ q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ T<q ∧ T<s ∧ q∣(u+1)^4+4 ∧ s∣(u+1)^4+4 := by
  obtain ⟨q,pq,hq,dq⟩ := h₁
  obtain ⟨s,ps,hs,ds⟩ := h₂
  let z := u+1
  let L := u^2+1
  let R := (u+2)^2+1
  change q∣L at dq
  change s∣R at ds
  have fac : (u+1)^4+4=L*R := by dsimp only [L,R]; ring
  refine ⟨q,s,pq,ps,?_,hq,hs,fac ▸ dvd_mul_of_dvd_left dq _,fac ▸ dvd_mul_of_dvd_right ds _⟩
  rintro rfl
  have diff : R=L+4*z := by dsimp only [R,L,z]; ring
  rw [diff] at ds
  have d4 := (Nat.dvd_add_iff_right dq).mpr ds
  have dz : q∣z := (pq.dvd_mul.mp d4).resolve_left (by
    intro dv; have := Nat.le_of_dvd (by decide : 0<4) dv; omega)
  have sum := dvd_add dq (dvd_mul_of_dvd_right dz 2)
  rw [show L+2*z=z^2+2 by dsimp only [L,z]; ring] at sum
  have sq : q∣z^2 := dz.trans (dvd_pow_self z (by decide : 2≠0))
  have bad := (Nat.dvd_add_iff_right sq).mpr sum
  have := Nat.le_of_dvd (by decide : 0<2) bad
  omega

/-- Uniformly over each fixed initial interval of offsets, a sufficiently large
solution has a prime factor above any prescribed threshold at every offset. -/
theorem eventual_large_prime_at_offsets
    (quadratic : ∀ T : ℕ, ∃ B : ℕ, ∀ x : ℕ, B<x → ∃ q : ℕ, q.Prime ∧ T<q ∧ q∣x^2+1)
    (L T : ℕ) :
    ∃ B : ℕ, ∀ n : ℕ, B<n → (¬∃ k u v : ℕ, 0<k ∧ u.Prime ∧ v.Prime ∧ u≠v ∧ k<u ∧ k<v ∧ u∣n+k ∧ v∣n+k) → ∀ k : ℕ, 0<k → k≤L →
      ∃ q : ℕ, q.Prime ∧ T<q ∧ q∣n+k := by
  let M := T.factorial^3
  let bound := L+4*M
  have mp : 0<M := pow_pos T.factorial_pos 3
  have top : 4≤bound := by dsimp only [bound]; omega
  obtain ⟨K,hK⟩ := quadratic bound
  refine ⟨M*(K+2)^4,?_⟩
  intro n hn sol k kp kl
  by_contra! noLarge
  have smooth (q : ℕ) (pq : q.Prime) (dq : q∣n+k) : q≤T := by
    by_contra! large
    exact noLarge q pq large dq
  obtain ⟨C,z,cap,_cp,_zp,form⟩ := smooth_fourth_decomposition T (n+k) (by omega) smooth
  change C≤M at cap
  have large : K+2<z := by
    by_contra! low
    have cmp := Nat.mul_le_mul cap (Nat.pow_le_pow_left low 4)
    omega
  let u := z-1
  have zu : z=u+1 := by dsimp only [u]; omega
  have ku : K<u := by omega
  obtain ⟨a,b,pa,pb,ne,ha,hb,da,db⟩ := two_quadratic_factors top (hK u ku) (hK (u+2) (by omega))
  have fac : n+(k+4*C)=C*((u+1)^4+4) := by
    rw [zu] at form
    calc
      _ = (n+k)+4*C := by omega
      _ = _ := by rw [form]; ring
  have ub : k+4*C≤bound := by dsimp only [bound]; omega
  exact two_primes (k:=k+4*C) (by omega) pa pb ne (by omega) (by omega)
    (fac ▸ dvd_mul_of_dvd_right da C) (fac ▸ dvd_mul_of_dvd_right db C) sol

/-- Every fixed prime divides all sufficiently large lowercase Erdős 889
solutions when the largest prime factor of x²+1 tends to infinity. -/
theorem eventual_prime_divisibility
    (quadratic : ∀ T : ℕ, ∃ B : ℕ, ∀ x : ℕ, B<x → ∃ q : ℕ, q.Prime ∧ T<q ∧ q∣x^2+1)
    (q : ℕ) (pq : q.Prime) :
    ∃ B : ℕ, ∀ n : ℕ, B<n → (¬∃ k u v : ℕ, 0<k ∧ u.Prime ∧ v.Prime ∧ u≠v ∧ k<u ∧ k<v ∧ u∣n+k ∧ v∣n+k) → q∣n := by
  obtain ⟨B,h⟩ := eventual_large_prime_at_offsets quadratic q q
  refine ⟨B,?_⟩
  intro n hn sol
  by_contra avoid
  let k := q-n%q
  have rem := Nat.mod_lt n pq.pos
  have nr : n%q≠0 := fun z => avoid (Nat.dvd_of_mod_eq_zero z)
  have kp : 0<k := by dsimp only [k]; omega
  have kq : k<q := by dsimp only [k]; omega
  have qd : q∣n+k := by
    refine ⟨n/q+1,?_⟩
    have sum := Nat.mod_add_div n q
    rw [Nat.mul_add,mul_one]
    dsimp only [k]
    omega
  obtain ⟨r,pr,hr,dr⟩ := h n hn sol k kp kq.le
  exact two_primes kp pq pr (by omega) kq (by omega) qd dr sol

/-- Over a fixed initial interval of offsets, every prime dividing n+k
eventually divides k itself, with exactly one exception above any fixed threshold. -/
theorem eventual_prime_support
    (quadratic : ∀ T : ℕ, ∃ B : ℕ, ∀ x : ℕ, B<x → ∃ q : ℕ, q.Prime ∧ T<q ∧ q∣x^2+1)
    (K T : ℕ) :
    ∃ B : ℕ, ∀ n : ℕ, B<n → (¬∃ k u v : ℕ, 0<k ∧ u.Prime ∧ v.Prime ∧ u≠v ∧ k<u ∧ k<v ∧ u∣n+k ∧ v∣n+k) → ∀ k : ℕ, 0<k → k≤K →
      ∃ q : ℕ, q.Prime ∧ max K T<q ∧ q∣n+k ∧
        ∀ r : ℕ, r.Prime → (r∣n+k ↔ r∣k ∨ r=q) := by
  have small (L : ℕ) : ∃ B : ℕ, ∀ n : ℕ, B<n → (¬∃ k u v : ℕ, 0<k ∧ u.Prime ∧ v.Prime ∧ u≠v ∧ k<u ∧ k<v ∧ u∣n+k ∧ v∣n+k) →
      ∀ r : ℕ, r≤L → r.Prime → r∣n := by
    induction L with
    | zero =>
      refine ⟨0,?_⟩
      intro n hn sol r low pr
      have := pr.two_le
      omega
    | succ l ih =>
      obtain ⟨A,hA⟩ := ih
      by_cases prime : (l+1).Prime
      · obtain ⟨B,hB⟩ := eventual_prime_divisibility quadratic (l+1) prime
        refine ⟨max A B,?_⟩
        intro n hn sol r le pr
        by_cases e : r=l+1
        · exact e ▸ hB n (lt_of_le_of_lt (Nat.le_max_right _ _) hn) sol
        · exact hA n (lt_of_le_of_lt (Nat.le_max_left _ _) hn) sol r (by omega) pr
      · refine ⟨A,?_⟩
        intro n hn sol r le pr
        have ne : r≠l+1 := by rintro rfl; exact prime pr
        exact hA n hn sol r (by omega) pr
  obtain ⟨A,ha⟩ := small K
  obtain ⟨B,hb⟩ := eventual_large_prime_at_offsets quadratic K (max K T)
  refine ⟨max A B,?_⟩
  intro n hn sol k kp kk
  obtain ⟨q,pq,hq,dq⟩ := hb n (lt_of_le_of_lt (Nat.le_max_right _ _) hn) sol k kp kk
  refine ⟨q,pq,hq,dq,?_⟩
  intro r pr
  constructor
  · intro dr
    by_cases low : r≤K
    · have dn := ha n (lt_of_le_of_lt (Nat.le_max_left _ _) hn) sol r low pr
      exact Or.inl ((Nat.dvd_add_iff_right dn).mpr dr)
    · right
      by_contra different
      have := Nat.le_max_left K T
      exact two_primes kp pr pq different (by omega) (by omega) dr dq sol
  · rintro (dk|rfl)
    · have low := (Nat.le_of_dvd kp dk).trans kk
      exact dvd_add (ha n (lt_of_le_of_lt (Nat.le_max_left _ _) hn) sol r low pr) dk
    · exact dq

private theorem universal_odd_cofactor {x d : ℕ} (hx : 3≤x) (hd : 1<d) (od : Odd d) :
    ∃ c : ℕ, Odd c ∧ d<c ∧ x^d+1=(x+1)*c := by
  rcases Nat.even_or_odd x with ev|ox
  · obtain ⟨c,fac⟩ : x+1∣x^d+1 := by simpa only [one_pow] using od.nat_add_dvd_pow_add_pow x 1
    have oddC : Odd c := by
      have e := ev.pow_of_ne_zero (by omega : d≠0)
      have o : Odd (x^d+1) := by obtain ⟨j,hj⟩ := e; exact ⟨j,by omega⟩
      rw [fac,Nat.odd_mul] at o
      exact o.2
    have growth (j : ℕ) : (j+3)*(x+1)<x^(j+3) := by
      induction j with
      | zero =>
        have xs : 4<x^2 := lt_of_lt_of_le (by decide : 4<9) (Nat.pow_le_pow_left hx 2)
        have mul := Nat.mul_lt_mul_of_pos_right xs (by omega : 0<x)
        change 3*(x+1)<x^3
        rw [pow_succ]
        omega
      | succ j ih =>
        have z := Nat.mul_le_mul_right (x+1) (by omega : 1≤j+3)
        simp only [one_mul] at z
        have lower := Nat.mul_le_mul_left (x^(j+3)) (by omega : 2≤x)
        rw [show j+1+3=j+3+1 by omega,pow_succ,Nat.add_mul,one_mul]
        omega
    have d3 : 3≤d := by obtain ⟨j,hj⟩ := od; omega
    have h := growth (d-3)
    rw [Nat.sub_add_cancel d3] at h
    refine ⟨c,oddC,?_,fac⟩
    by_contra! low
    have := Nat.mul_le_mul_left (x+1) low
    rw [Nat.mul_comm d (x+1)] at h
    omega
  · exact odd_cofactor ox (by omega) od hd

private theorem fresh_prime_for_odd_power {x d : ℕ} (hx : 3≤x) (hd : 1<d) (od : Odd d) :
    ∃ q : ℕ, q.Prime ∧ 3<q ∧ q∣x^d+1 ∧ ¬q∣x+1 := by
  obtain ⟨c,oc,hc,fac⟩ := universal_odd_cofactor hx hd od
  by_contra missing
  have cd : c∣d := by
    apply (Nat.factorization_le_iff_dvd (by omega : c≠0) (by omega : d≠0)).mp
    intro q
    by_cases pq : q.Prime
    · by_cases dq : q∣c
      · have hi : 2<q := by
          have := pq.two_le
          by_contra! low
          have q2 : q=2 := by omega
          rw [q2] at dq
          obtain ⟨j,hj⟩ := oc
          omega
        have df : q∣x^d+1 := fac ▸ dvd_mul_of_dvd_right dq _
        have dx : q∣x+1 := by
          by_contra nx
          by_cases three : q=3
          · subst q
            have nz : x%3≠0 := by
              intro modzero
              have dv := (Nat.dvd_of_mod_eq_zero modzero).trans (dvd_pow_self x (by omega : d≠0))
              omega
            have one : x%3=1 := by omega
            have co := (Nat.mod_modEq x 3).pow d
            change (x%3)^d%3=x^d%3 at co
            rw [one,one_pow] at co
            omega
          · exact missing ⟨q,pq,by omega,df,nx⟩
        let _ : Fact q.Prime := ⟨pq⟩
        have nd : ¬q∣x := by
          intro div
          have one := (Nat.dvd_add_iff_right div).mpr dx
          have := Nat.le_of_dvd Nat.one_pos one
          omega
        have val := padicValNat.pow_add_pow (x:=x) (y:=1) (pq.odd_of_ne_two (by omega)) dx nd od
        rw [one_pow,fac,padicValNat.mul (by omega) (by omega)] at val
        change c.factorization q≤d.factorization q
        rw [Nat.factorization_def _ pq,Nat.factorization_def _ pq]
        omega
      · exact (Nat.factorization_eq_zero_of_not_dvd dq).trans_le (Nat.zero_le _)
    · exact (Nat.factorization_eq_zero_of_not_prime c pq).trans_le (Nat.zero_le _)
  exact (Nat.not_le_of_gt hc) (Nat.le_of_dvd (by omega) cd)

private theorem odd_dvd_pullback {p d x : ℕ} (pp : p.Prime) (od : Odd d) (hd : 1<d)
    (cop : d.Coprime (p-1)) (div : p∣x^d+1) : p∣x+1 := by
  let _ : Fact p.Prime := ⟨pp⟩
  have eq := (ZMod.natCast_eq_zero_iff (x^d+1) p).mpr div
  push_cast at eq
  have odd : (-(x:ZMod p))^d=1 := by
    rw [neg_pow,od.neg_one_pow]
    linear_combination -eq
  have nz : -(x:ZMod p)≠0 := by
    intro z
    rw [z,zero_pow (by omega : d≠0)] at odd
    exact zero_ne_one odd
  have dn := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one odd)
    (orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one nz))
  rw [cop.gcd_eq_one] at dn
  have one := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_one dn)
  apply (ZMod.natCast_eq_zero_iff (x+1) p).mp
  push_cast
  linear_combination -one

/-- For every fixed odd exponent greater than one and fixed positive offset k
whose prime divisors have p−1 coprime to d, sufficiently large solutions cannot have n+k=k z^d. -/
theorem normalized_odd_power_exclusion
    (quadratic : ∀ T : ℕ, ∃ B : ℕ, ∀ x : ℕ, B<x → ∃ q : ℕ, q.Prime ∧ T<q ∧ q∣x^2+1)
    (k d : ℕ) (kp : 0<k) (compatible : ∀ q : ℕ, q.Prime → q∣k → d.Coprime (q-1))
    (hd : 1<d) (od : Odd d) :
    ∃ B : ℕ, ∀ n z : ℕ, B<n → (¬∃ k u v : ℕ, 0<k ∧ u.Prime ∧ v.Prime ∧ u≠v ∧ k<u ∧ k<v ∧ u∣n+k ∧ v∣n+k) → n+k≠k*z^d := by
  let M := (2*k).factorial^3
  let S := 1+4*M
  have mp : 0<M := pow_pos (Nat.factorial_pos _) _
  have s5 : 5≤S := by dsimp only [S]; omega
  let T := k*(1+S^d)
  have t4 : 4≤T := by
    have s : S≤S^d := Nat.le_self_pow (by omega : d≠0) S
    have r := Nat.mul_le_mul_right (1+S^d) kp
    dsimp only [T]
    omega
  obtain ⟨K,hK⟩ := quadratic T
  let Z := M*(K+3)^4+4
  obtain ⟨A,hA⟩ := eventual_prime_support quadratic (2*k) 3
  refine ⟨max A (k*Z^d),?_⟩
  intro n z big sol eq
  have lowA := Nat.le_max_left A (k*Z^d)
  have lowZ := Nat.le_max_right A (k*Z^d)
  have zlarge : Z<z := by
    by_contra! low
    have := Nat.mul_le_mul_left k (Nat.pow_le_pow_left low d)
    omega
  have z3 : 3≤z := by dsimp only [Z] at zlarge; omega
  obtain ⟨q,pq,hq,dq,notOld⟩ := fresh_prime_for_odd_power z3 hd od
  have next : n+2*k=k*(z^d+1) := by
    calc
      _ = (n+k)+k := by omega
      _ = _ := by rw [eq]; ring
  have dqn : q∣n+2*k := next ▸ dvd_mul_of_dvd_right dq _
  obtain ⟨r,pr,hr,dr,all⟩ := hA n (by omega) sol (2*k) (by omega) le_rfl
  have qnk : ¬q∣2*k := by
    intro ds
    rcases pq.dvd_mul.mp ds with d2|dk
    · have := Nat.le_of_dvd (by decide : 0<2) d2; omega
    · exact notOld (odd_dvd_pullback pq od hd (compatible q pq dk) dq)
  have qr : q=r := ((all q pq).mp dqn).resolve_left qnk
  have smoothZ (s : ℕ) (ps : s.Prime) (ds : s∣z+1) : s≤2*k := by
    by_contra! high
    have af : z+1∣z^d+1 := by simpa only [one_pow] using od.nat_add_dvd_pow_add_pow z 1
    have dsn : s∣n+2*k := next ▸ dvd_mul_of_dvd_right (ds.trans af) _
    have sr := ((all s ps).mp dsn).resolve_left (by intro d; have := Nat.le_of_dvd (by omega) d; omega)
    have sq : s=q := sr.trans qr.symm
    exact notOld (sq ▸ ds)
  obtain ⟨C,y,cap,_cp,_yp,form⟩ := smooth_fourth_decomposition (2*k) (z+1) (by omega) smoothZ
  change C≤M at cap
  have ybig : K+3<y := by
    by_contra! low
    have cmp := Nat.mul_le_mul cap (Nat.pow_le_pow_left low 4)
    dsimp only [Z] at zlarge
    omega
  let u := y-1
  have yu : y=u+1 := by dsimp only [u]; omega
  obtain ⟨a,b,pa,pb,ne,ha,hb,da,db⟩ := two_quadratic_factors t4 (hK u (by omega)) (hK (u+2) (by omega))
  let s := 1+4*C
  have sh : z+s=C*((u+1)^4+4) := by
    dsimp only [s]
    rw [yu] at form
    calc
      _ = (z+1)+4*C := by omega
      _ = _ := by rw [form]; ring
  have up : s≤S := by dsimp only [s,S]; omega
  have pos : 0<k*(1+s^d) := Nat.mul_pos kp (by omega)
  have bound : k*(1+s^d)≤T :=
    Nat.mul_le_mul_left k (Nat.add_le_add_left (Nat.pow_le_pow_left up d) 1)
  have offset : n+k*(1+s^d)=k*(z^d+s^d) := by
    calc
      _ = (n+k)+k*s^d := by ring
      _ = _ := by rw [eq]; ring
  have both : z+s∣n+k*(1+s^d) := offset ▸ dvd_mul_of_dvd_right (od.nat_add_dvd_pow_add_pow z s) _
  exact two_primes pos pa pb ne (by omega) (by omega)
    ((sh ▸ dvd_mul_of_dvd_right da C).trans both) ((sh ▸ dvd_mul_of_dvd_right db C).trans both) sol

/-- A prime modulus detects the coefficient exponent modulo a prime l.
The residue x^m has multiplicative order l. -/
private theorem detect_exponent {n x j a t e l Q m : ℕ} (pl : l.Prime) (pQ : Q.Prime)
    (xpos : 0<x) (xQ : x<Q) (qr : Q-1=m*l) (nonres : x^m%Q≠1)
    (dn : Q∣n) (ep : 0<e) (ed : l∣e) (eq : n+x^j=x^a*t^e) : a%l=j%l := by
  let _ : Fact Q.Prime := ⟨pQ⟩
  let X : ZMod Q := x
  let V : ZMod Q := t
  let W := X^m
  have Xnz : X≠0 := by
    intro z
    have := Nat.le_of_dvd xpos ((ZMod.natCast_eq_zero_iff x Q).mp z)
    omega
  have zn := (ZMod.natCast_eq_zero_iff n Q).mpr dn
  have zeq := congrArg (fun y : ℕ => (y:ZMod Q)) eq
  push_cast at zeq
  rw [zn,zero_add] at zeq
  change X^j=X^a*V^e at zeq
  have Vnz : V≠0 := by
    intro z
    rw [z,zero_pow ep.ne',mul_zero] at zeq
    exact (pow_ne_zero j Xnz) zeq
  have Wpow : W^l=1 := by
    dsimp only [W]; rw [←pow_mul,←qr]; exact ZMod.pow_card_sub_one_eq_one Xnz
  have Wne : W≠1 := by
    intro z
    have co : ((x^m:ℕ):ZMod Q)=(1:ℕ) := by simpa only [Nat.cast_pow,Nat.cast_one] using z
    have h := (ZMod.natCast_eq_natCast_iff _ _ _).mp co
    change x^m%Q=1%Q at h
    rw [Nat.mod_eq_of_lt pQ.one_lt] at h
    exact nonres h
  have ord : orderOf W=l := ((Nat.dvd_prime pl).mp (orderOf_dvd_of_pow_eq_one Wpow)).resolve_left
    (fun h => Wne (orderOf_eq_one_iff.mp h))
  obtain ⟨k,hk⟩ := ed
  have vp : (V^e)^m=1 := by
    rw [←pow_mul,hk,show l*k*m=(m*l)*k by ring,←qr,pow_mul,ZMod.pow_card_sub_one_eq_one Vnz,one_pow]
  have h := congrArg (fun v : ZMod Q => v^m) zeq
  change (X^j)^m=(X^a*V^e)^m at h
  rw [mul_pow,vp,mul_one,←pow_mul,←pow_mul,Nat.mul_comm j m,Nat.mul_comm a m,pow_mul,pow_mul] at h
  have finite := isOfFinOrder_iff_pow_eq_one.mpr ⟨l,pl.pos,Wpow⟩
  have ex := finite.pow_inj_mod.mp (show W^a=W^j from h.symm)
  rwa [ord] at ex

/-- A modular certificate excludes the prime exponent divisor l in the factorization
of a fixed shift by a power of x and a power of one variable base t. -/
theorem fixed_prime_exponent_exclusion
    (quadratic : ∀ T : ℕ, ∃ B : ℕ, ∀ x : ℕ, B<x → ∃ q : ℕ, q.Prime ∧ T<q ∧ q∣x^2+1)
    (x j l Q m : ℕ) (xpos : 0<x) (jl : j<l) (pl : l.Prime) (ol : Odd l)
    (compatible : ∀ q : ℕ, q.Prime → q∣x^j → l.Coprime (q-1))
    (pQ : Q.Prime) (xQ : x<Q) (qr : Q-1=m*l) (nonres : x^m%Q≠1) :
    ∃ B : ℕ, ∀ n a t e : ℕ, B<n → (¬∃ k u v : ℕ, 0<k ∧ u.Prime ∧ v.Prime ∧ u≠v ∧ k<u ∧ k<v ∧ u∣n+k ∧ v∣n+k) → 0<e →
      n+x^j=x^a*t^e → ¬l∣e := by
  obtain ⟨A,hA⟩ := normalized_odd_power_exclusion quadratic (x^j) l (pow_pos xpos j) compatible
    pl.one_lt ol
  obtain ⟨F,hF⟩ := eventual_prime_divisibility quadratic Q pQ
  refine ⟨max A F,?_⟩
  intro n a t e hn sol ep eq de
  have dQ := hF n (lt_of_le_of_lt (Nat.le_max_right _ _) hn) sol
  have aligned := detect_exponent pl pQ xpos xQ qr nonres dQ ep de eq
  rw [Nat.mod_eq_of_lt jl] at aligned
  have rem : a=j+a/l*l := by rw [←aligned,Nat.mul_comm (a/l) l,Nat.mod_add_div]
  obtain ⟨v,hv⟩ := de
  apply hA n (x^(a/l)*t^v) (lt_of_le_of_lt (Nat.le_max_left _ _) hn) sol
  calc
    _ = x^(j+a/l*l)*t^(v*l) := by rw [←rem,Nat.mul_comm v l,←hv,eq]
    _ = _ := by rw [pow_add,pow_mul,pow_mul,mul_pow]; ring

/-- Common prime moduli certify the exclusions for each base 2, 3 and 5. -/
theorem initial_odd_exponent_exclusions
    (quadratic : ∀ T : ℕ, ∃ B : ℕ, ∀ x : ℕ, B<x → ∃ q : ℕ, q.Prime ∧ T<q ∧ q∣x^2+1)
    (x j l Q : ℕ) (base : x=2 ∨ x=3 ∨ x=5) (jl : j<l)
    (row : (l,Q) ∈ ([(3,7),(5,11),(7,29),(11,23),(13,53),(17,103),(19,191),(23,47),
      (29,59),(31,311),(37,149),(41,83),(43,173),(47,283),(53,107)] : List (ℕ×ℕ))) :
    ∃ B : ℕ, ∀ n a t e : ℕ, B<n → (¬∃ k u v : ℕ, 0<k ∧ u.Prime ∧ v.Prime ∧ u≠v ∧ k<u ∧ k<v ∧ u∣n+k ∧ v∣n+k) → 0<e → n+x^j=x^a*t^e → ¬l∣e := by
  let rows : List (ℕ×ℕ) := [(3,7),(5,11),(7,29),(11,23),(13,53),(17,103),(19,191),(23,47),
    (29,59),(31,311),(37,149),(41,83),(43,173),(47,283),(53,107)]
  have table : ∀ r ∈ rows, ∀ v ∈ [2,3,5], r.1.Prime ∧ Odd r.1 ∧ r.2.Prime ∧ v<r.2 ∧
      r.2-1=(r.2-1)/r.1*r.1 ∧ v^((r.2-1)/r.1)%r.2≠1 := by decide +kernel
  obtain ⟨pl,ol,pQ,xQ,qr,nonres⟩ := table (l,Q) row x (by simpa using base)
  have px : x.Prime := by rcases base with rfl|rfl|rfl <;> decide
  apply fixed_prime_exponent_exclusion quadratic x j l Q ((Q-1)/l) px.pos jl pl ol _ pQ xQ qr nonres
  intro q pq dq
  have eq := (Nat.prime_dvd_prime_iff_eq pq px).mp (pq.dvd_of_dvd_pow dq)
  rw [eq]
  apply pl.coprime_iff_not_dvd.mpr
  have l3 : 2<l := by obtain ⟨k,hk⟩ := ol; have := pl.two_le; omega
  rcases base with rfl|rfl|rfl
  · intro dv; have := Nat.le_of_dvd (by decide : 0<2-1) dv; omega
  · intro dv; have := Nat.le_of_dvd (by decide : 0<3-1) dv; omega
  · intro dv
    have small := pl.dvd_of_dvd_pow (show l∣(2:ℕ)^2 from dv)
    have := Nat.le_of_dvd (by decide : 0<2) small
    omega


theorem square_middle_pell_exclusion {p t r : ℕ} (op : Odd p) (hp : 5<p)
    (pr : r.Prime) (outer : p^2+3=4*r) (middle : p^2+2=3*t^2) : False := by
  have oddProd : Odd (p^2+2) := (op.pow (n:=2)).add_even (by decide : Even 2)
  rw [middle,Nat.odd_mul,Nat.odd_pow_iff (by decide : 2 ≠ 0)] at oddProd
  obtain ⟨i,hi⟩ := op
  obtain ⟨j,hj⟩ := oddProd.2
  have lower : p<3*t := by
    by_contra! bad
    nlinarith [Nat.mul_le_mul bad bad]
  have upper : 3*t<2*p := by
    by_contra! bad
    nlinarith [Nat.mul_le_mul bad bad,Nat.mul_le_mul hp.le hp.le]
  let L := (3*t-p)/2
  have eqL : 2*L+p=3*t := by dsimp only [L]; omega
  have fact : L*(L+p)=2*r := by
    have sq := congrArg (fun x : ℕ => x^2) eqL
    nlinarith
  have small : L+p<r := by
    nlinarith [Nat.mul_le_mul (show 6≤p by omega) (Nat.le_refl p)]
  have rd : r∣L*(L+p) := fact ▸ dvd_mul_left _ _
  rcases pr.dvd_mul.mp rd with h | h
  · have pos : 0<L := by omega
    have := Nat.le_of_dvd pos h
    omega
  · have := Nat.le_of_dvd (show 0<L+p by omega) h
    omega

private theorem three_power_pell_bound {t w e : ℕ} (hi : 3 < t) (power : t = 3^e)
    (pell : t^2 = 2*w^2+1) : False := by
  have pos : 0 < e := by
    by_contra! h
    have ze : e=0 := by omega
    rw [ze,pow_zero] at power
    omega
  have three : 3 ∣ t := power ▸ dvd_pow_self _ pos.ne'
  have oddt : Odd t := power ▸ (show Odd (3:ℕ) by decide).pow
  obtain ⟨u,tu⟩ := oddt
  let v := u+1
  have uv : u.Coprime v := by simp [v]
  have eq : v*(2*u)=w^2 := by dsimp [v]; nlinarith [pell,tu]
  have extract {x y : ℕ} (h : x.Coprime y) (e' : x*y=w^2) : ∃ s : ℕ, x=s^2 := by
    apply exists_eq_pow_of_mul_eq_pow _ e'
    change IsUnit (Nat.gcd x y)
    rw [show Nat.gcd x y = 1 from h]
    exact isUnit_one
  have sq : ∃ s : ℕ, t+1=s^2 := by
    rcases Nat.even_or_odd v with ev|ov
    · have ou : Odd u := by rw [Nat.odd_iff]; dsimp [v] at ev; obtain ⟨k,hk⟩ := ev; omega
      obtain ⟨s,hs⟩ := extract (ou.coprime_two_left.mul_left uv.symm) (show (2*v)*u=w^2 by nlinarith [eq])
      exact ⟨s,by dsimp [v] at hs; omega⟩
    · obtain ⟨s,hs⟩ := extract (ov.coprime_two_right.mul_right uv.symm) eq
      have mm := congrArg (· % 3) hs
      rw [Nat.pow_mod] at mm
      have modv : v%3=2 := by dsimp [v]; omega
      rw [modv] at mm
      have tab : ∀ i : Fin 3, i.val^2%3≠2 := by decide
      exact False.elim (tab ⟨s%3,Nat.mod_lt _ (by decide)⟩ mm.symm)
  obtain ⟨s,hs⟩ := sq
  have sl : 2 < s := by by_contra! h; interval_cases s <;> norm_num at hs <;> omega
  obtain ⟨j,rfl⟩ : ∃ j : ℕ, s=j+1 := ⟨s-1,by omega⟩
  have prod : j*(j+2)=3^e := by nlinarith [hs,power]
  have both {z : ℕ} (hz : 1 < z) (dz : z ∣ 3^e) : 3 ∣ z := by
    have hit := (Nat.dvd_prime_pow Nat.prime_three).mp dz
    obtain ⟨k,_,rfl⟩ := hit
    cases k with
    | zero => simp at hz
    | succ k => exact dvd_pow_self _ (by omega)
  have da := both (show 1 < j by omega) (prod ▸ dvd_mul_right j (j+2))
  have db := both (show 1 < j+2 by omega) (prod ▸ dvd_mul_left (j+2) j)
  omega

private theorem five_times_square_split {x y z : ℕ} (xy : x.Coprime y) (eq : x*y=5*z^2) :
    (∃ h : ℕ, x=h^2) ∨ ∃ h : ℕ, y=h^2 := by
  have extract {u v : ℕ} (uv : u.Coprime v) (sq : u*v=(5*z)^2) : ∃ h : ℕ, u=h^2 := by
    apply exists_eq_pow_of_mul_eq_pow _ sq
    change IsUnit (Nat.gcd u v)
    rw [show Nat.gcd u v=1 from uv]
    exact isUnit_one
  have pf : Nat.Prime 5 := by decide
  by_cases d : 5∣x
  · have ny : ¬5∣y := by
      intro dd
      have r := Nat.dvd_gcd d dd
      rw [Nat.coprime_iff_gcd_eq_one.mp xy] at r
      omega
    exact Or.inr (extract ((pf.coprime_iff_not_dvd.mpr ny).symm.mul_right xy.symm)
      (show y*(5*x)=(5*z)^2 by nlinarith only [eq]))
  · exact Or.inl (extract ((pf.coprime_iff_not_dvd.mpr d).symm.mul_right xy)
      (show x*(5*y)=(5*z)^2 by nlinarith only [eq]))

private theorem no_square_two_mod_three {x v : ℕ} (rem : v%3=2) (sq : v=x^2) : False := by
  have eq := (Nat.mod_modEq x 3).pow 2
  have t : ∀ i ∈ List.range 3, i^2%3≠2 := by decide +kernel
  apply t (x%3) (List.mem_range.mpr (by omega))
  exact Eq.trans eq (sq ▸ rem)

private theorem pell_four_smooth_bound {T w a : ℕ} (eq : T^2=5*w^2+4)
    (shape : T=3^a ∨ T=2*3^a) : T≤27 := by
  by_contra! large
  have posa : 0<a := by
    by_contra! h
    have z : a=0 := by omega
    rw [z,pow_zero] at shape
    omega
  have da : 3∣3^a := dvd_pow_self 3 posa.ne'
  rcases shape with pow | twice
  · let X := T-2
    have eX : X+2=T := by dsimp only [X]; omega
    have ot : Odd T := pow ▸ (show Odd (3:ℕ) by decide).pow
    have ox : Odd X := by obtain ⟨h,hh⟩ := ot; exact Nat.odd_iff.mpr (by omega)
    have cop : X.Coprime (X+4) := Nat.coprime_self_add_right.mpr ((Nat.coprime_two_right.mpr ox).pow_right 2)
    have fac : X*(X+4)=5*w^2 := by rw [←eX] at eq; nlinarith only [eq]
    rcases five_times_square_split cop fac with ⟨h,eh⟩ | ⟨h,eh⟩
    · have sm := OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2.square_plus_two_three
        (show h^2+2=3^a by omega)
      nlinarith [Nat.mul_le_mul sm sm]
    · exact no_square_two_mod_three (by omega : (X+4)%3=2) eh
  · obtain ⟨x,hx⟩ := (show Odd (3:ℕ) by decide).pow (n:=a)
    have four : 4∣w := by
      have div : 16∣5*w^2 := ⟨x^2+x,by rw [twice,hx] at eq; nlinarith only [eq]⟩
      have dd : 16∣w^2 := (show Nat.Coprime 16 5 by decide).dvd_of_dvd_mul_left div
      exact (Nat.pow_dvd_pow_iff (by decide : 2≠0)).mp dd
    obtain ⟨j,hj⟩ := four
    have fac : x*(x+1)=5*j^2 := by rw [twice,hx,hj] at eq; nlinarith only [eq]
    rcases five_times_square_split (by simp : x.Coprime (x+1)) fac with ⟨v,hv⟩ | ⟨v,hv⟩
    · have ea : Even a := by
        apply Nat.not_odd_iff_even.mp
        rintro ⟨k,hk⟩
        have sq5 : (3^a)^2 ≡ 4 [MOD 5] := by
          calc
            (3^a)^2 = (3^2)^a := by rw [←pow_mul,←pow_mul,Nat.mul_comm a 2]
            _ = ((3^2)^2)^k*(3^2) := by rw [hk,pow_succ,pow_mul]
            _ ≡ 1^k*9 [MOD 5] := ((show (3^2)^2 ≡ 1 [MOD 5] by decide).pow k).mul_right 9
            _ ≡ 4 [MOD 5] := by simp only [one_pow,one_mul]; decide
        have norm : (2*3^a)^2%5=4 := by rw [←twice,eq]; omega
        have bad : (2*3^a)^2 ≡ 16 [MOD 5] := by simpa [mul_pow] using sq5.mul_left 4
        change (2*3^a)^2%5=16%5 at bad
        omega
      obtain ⟨k,hk⟩ := ea
      have shape : 3^a=(3^k)^2 := by rw [hk,pow_add,pow_two]
      have high : 3<3^k := by
        by_contra! low
        nlinarith [Nat.mul_le_mul low low]
      exact three_power_pell_bound high rfl (show (3^k)^2=2*v^2+1 by omega)
    · exact no_square_two_mod_three (by omega : (x+1)%3=2) hv

private theorem pell_four_large_prime {T w : ℕ} (large : 27<T) (eq : T^2=5*w^2+4)
    (no4 : ¬4∣T) : ∃ q : ℕ, q.Prime ∧ 6<q ∧ q∣T := by
  by_contra missing
  have no5 : ¬5∣T := by
    intro d
    have sq := d.trans (dvd_pow_self T (by decide : 2≠0))
    omega
  have pure {v : ℕ} (dv : v∣T) (nz : v≠0) (odd : ¬2∣v) : v=3^v.primeFactorsList.length := by
    apply Nat.eq_prime_pow_of_unique_prime_dvd nz
    intro q pq dq
    have bound : q≤6 := by by_contra! h; exact missing ⟨q,pq,h,dq.trans dv⟩
    have tab : ∀ i ∈ List.range 7, Nat.Prime i → i=2 ∨ i=3 ∨ i=5 := by decide +kernel
    rcases tab q (List.mem_range.mpr (by omega)) pq with rfl | same | rfl
    · exact (odd dq).elim
    · exact same
    · exact (no5 (dq.trans dv)).elim
  by_cases two : 2∣T
  · obtain ⟨v,hv⟩ := two
    have d : v∣T := hv ▸ dvd_mul_left _ _
    have odd : ¬2∣v := by intro hh; exact no4 (hv ▸ Nat.mul_dvd_mul_left 2 hh)
    have pw := pure d (by omega) odd
    exact (not_le_of_gt large) (pell_four_smooth_bound eq (Or.inr (show T=2*3^v.primeFactorsList.length by omega)))
  · exact (not_le_of_gt large) (pell_four_smooth_bound eq (Or.inl (pure (dvd_refl T) (by omega) two)))

theorem square_fourth_even_witness {p u : ℕ} (pp : p.Prime) (op : Odd p)
    (hp : 81<p) (ou : Odd u) (eq : p^2+4=5*u^2) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧ q∣p^2+d ∧ s∣p^2+d := by
  obtain ⟨k,hk⟩ := op
  obtain ⟨j,hj⟩ := ou
  have upper : u<p := by by_contra! bad; nlinarith [Nat.mul_le_mul bad bad,Nat.mul_le_mul hp.le hp.le]
  have lower : p<3*u := by by_contra! bad; nlinarith [Nat.mul_le_mul bad bad]
  have bound : 5*u<3*p := by by_contra! bad; nlinarith [Nat.mul_le_mul bad bad,Nat.mul_le_mul hp.le hp.le]
  let w := (p-u)/2
  let v := u-w
  have uu : u=v+w := by dsimp only [v,w]; omega
  have pu : p=v+3*w := by dsimp only [v,w]; omega
  let A := 2*v+w
  let B := 3*v+4*w
  have pure := eq
  rw [pu,uu] at pure
  have ab : A*B=p^2+5 := by rw [pu]; dsimp only [A,B]; nlinarith only [pure]
  have ae : A^2=5*w^2+4 := by dsimp only [A]; nlinarith only [pure]
  have be : B^2=5*(v+2*w)^2+4 := by dsimp only [B]; nlinarith only [pure]
  have ways : A+p=B ∧ A<p := by dsimp only [A,B]; omega
  have aL : 27<A := by dsimp only [A]; omega
  have bL : 27<B := by omega
  have no4 : ¬4∣p^2+5 := by
    have e : p^2+5=4*(k^2+k+1)+2 := by rw [hk]; ring
    omega
  have dA : A∣p^2+5 := ab ▸ dvd_mul_right _ _
  have dB : B∣p^2+5 := ab ▸ dvd_mul_left _ _
  obtain ⟨q,pq,lq,dq⟩ := pell_four_large_prime aL ae (fun h => no4 (h.trans dA))
  obtain ⟨s,ps,ls,ds⟩ := pell_four_large_prime bL be (fun h => no4 (h.trans dB))
  have ne : q≠s := by
    rintro rfl
    have dp : q∣p := (Nat.dvd_add_right dq).mp (ways.1 ▸ ds)
    have qp := (Nat.prime_dvd_prime_iff_eq pq pp).mp dp
    have lb := Nat.le_of_dvd (show 0<A by omega) dq
    omega
  exact ⟨5,q,s,pq,ps,ne,lq,ls,dq.trans dA,ds.trans dB⟩

private theorem square_fourth_coprime {p r s a b : ℕ} (pr : r.Prime) (hs : 5<s)
    (hb : 0<b) (outer : p^2+3=4*r) (eq : p^2+4=5^a*s^b) : a.Coprime b := by
  by_contra bad
  obtain ⟨d,pd,da,db⟩ := Nat.Prime.not_coprime_iff_dvd.mp bad
  obtain ⟨i,hi⟩ := da
  obtain ⟨j,hj⟩ := db
  have jp : j≠0 := by rintro rfl; simp at hj; omega
  let x := 5^i*s^j
  have xb : 5<x := by
    have sl := Nat.le_self_pow jp s
    have fi : 0<5^i := pow_pos (by decide) _
    have lb := Nat.mul_le_mul_right (s^j) fi
    dsimp only [x]; omega
  have power : p^2+4=x^d := by
    dsimp only [x]
    rw [eq,hi,hj,mul_pow,←pow_mul,←pow_mul,Nat.mul_comm i d,Nat.mul_comm j d]
  have sq : x^2≤x^d := Nat.pow_le_pow_right (by omega) pd.two_le
  let L := x-1
  have lx : L+1=x := by dsimp only [L]; omega
  have lf : L∣4*r := by
    have h : x-1∣x^d-1 := by simpa using (Nat.sub_dvd_pow_sub_pow (x:=x) (y:=1) (n:=d))
    have e : x^d-1=4*r := by omega
    exact e ▸ h
  have small : L<r := by
    have up : x^2≤4*r+1 := by omega
    rw [←lx] at up
    nlinarith [Nat.mul_le_mul (show 4≤L by omega) (Nat.le_refl L)]
  have cop : L.Coprime r := (pr.coprime_iff_not_dvd.mpr (by
    intro dv
    have := Nat.le_of_dvd (show 0<L by omega) dv
    omega)).symm
  have div := cop.dvd_of_dvd_mul_right lf
  have bound := Nat.le_of_dvd (by decide : 0<4) div
  omega

private theorem square_fourth_cofactor {p q r : ℕ} (pp : p.Prime) (op : Odd p)
    (hp : 81<p) (pq : q.Prime) (first : p^2+1=2*q) (pr : r.Prime) (outer : p^2+3=4*r)
    (missing : ¬∃ d a b : ℕ, a.Prime ∧ b.Prime ∧ a≠b ∧ d+1<a ∧ d+1<b ∧
      a∣p^2+d ∧ b∣p^2+d) :
    ∃ s a b : ℕ, s.Prime ∧ 5<s ∧ s%4=1 ∧ 0<a ∧ 0<b ∧ Odd b ∧ a.Coprime b ∧ p^2+4=5^a*s^b := by
  have p5 : p%5≠0 := by
    intro h
    have ds := (Nat.dvd_prime pp).mp (Nat.dvd_of_mod_eq_zero h)
    omega
  have q5 : ¬5∣p^2+1 := by
    intro div
    rw [first] at div
    have ds := (show Nat.Prime 5 by decide).dvd_mul.mp div
    rcases ds with d | d
    · omega
    · have same := (Nat.dvd_prime pq).mp d
      rcases same with impossible | same
      · omega
      · nlinarith [Nat.mul_le_mul hp.le hp.le]
  have div5 : 5∣p^2+4 := by
    have sq := Nat.pow_mod p 2 5
    have rem := Nat.mod_lt p (by decide : 0<5)
    interval_cases h : p%5 <;> norm_num [h] at sq <;> omega
  let n := p^2+4
  let a := n.factorization 5
  let m := n / 5^a
  have nz : n≠0 := by dsimp only [n]; omega
  have fac : 5^a*m=n := Nat.ordProj_mul_ordCompl_eq_self n 5
  have dm : m∣n := Nat.ordCompl_dvd n 5
  have pos : 0 < m := Nat.ordCompl_pos 5 nz
  have no5 : ¬5∣m := Nat.not_dvd_ordCompl (by decide : Nat.Prime 5) nz
  have ha : 0<a := (Nat.Prime.dvd_iff_one_le_factorization (by decide : Nat.Prime 5) nz).mp div5
  have big : 2 ≤ m := by
    by_contra! small
    have one : m=1 := by omega
    have pure : p^2+4=5^a := by simpa only [one,mul_one,n] using fac.symm
    rcases Nat.even_or_odd a with ⟨j,hj⟩ | ⟨j,hj⟩
    · have sq : p^2+4=(5^j)^2 := by rw [pure,hj,pow_add,pow_two]
      by_cases low : 5^j≤p
      · nlinarith [Nat.mul_le_mul low low]
      · nlinarith [Nat.mul_le_mul (show p+1≤5^j by omega) (show p+1≤5^j by omega)]
    · have form : p^2+4=5*(5^j)^2 := by rw [pure,hj,pow_succ,Nat.mul_comm 2 j,pow_mul]; ring
      exact missing (square_fourth_even_witness pp op hp ((by decide : Odd 5).pow) form)
  have no2 : ¬2∣n := by
    intro d
    exact (Nat.not_even_iff_odd.mpr ((op.pow (n:=2)).add_even (by decide : Even 4))) (even_iff_two_dvd.mpr d)
  have no3 : ¬3∣n := by
    have sq := Nat.pow_mod p 2 3
    have rem := Nat.mod_lt p (by decide : 0<3)
    dsimp only [n]
    interval_cases h : p%3 <;> norm_num [h] at sq <;> omega
  have eligible {l : ℕ} (pl : l.Prime) (d : l∣m) : 5<l := by
    by_contra! small
    have tab : ∀ z ∈ List.range 6, Nat.Prime z → z=2 ∨ z=3 ∨ z=5 := by decide +kernel
    rcases tab l (List.mem_range.mpr (by omega)) pl with rfl | rfl | rfl
    · exact no2 (d.trans dm)
    · exact no3 (d.trans dm)
    · exact no5 d
  have pure : IsPrimePow m := by
    by_contra bad
    obtain ⟨x,hx,y,hy,ne⟩ := (Nat.not_isPrimePow_iff_nontrivial_of_two_le big).mp bad
    obtain ⟨px,dx,_⟩ := Nat.mem_primeFactors.mp hx
    obtain ⟨py,dy,_⟩ := Nat.mem_primeFactors.mp hy
    exact missing ⟨4,x,y,px,py,ne,eligible px dx,eligible py dy,dx.trans dm,dy.trans dm⟩
  obtain ⟨s,b,ps,hb,ep⟩ := (isPrimePow_nat_iff _).mp pure
  have ds : s∣m := ep ▸ dvd_pow_self s hb.ne'
  have lb := eligible ps ds
  have smod : s%4=1 := by
    let _ : Fact s.Prime := ⟨ps⟩
    have ns : ¬s∣2 := by intro h; have := Nat.le_of_dvd (by decide : 0<2) h; omega
    have two : (2:ZMod s)≠0 := by simpa using (ZMod.natCast_eq_zero_iff 2 s).not.mpr ns
    have hz := (ZMod.natCast_eq_zero_iff (p^2+4) s).mpr (ds.trans dm)
    push_cast at hz
    have hs : IsSquare (-1 : ZMod s) := by
      refine ⟨(p:ZMod s)/2,?_⟩
      field_simp
      linear_combination -hz
    have n3 := ZMod.exists_sq_eq_neg_one_iff.mp hs
    obtain ⟨j,hj⟩ := ps.odd_of_ne_two (by omega)
    omega
  have eqf : p^2+4=5^a*s^b := by rw [ep]; exact fac.symm
  have ob : Odd b := by
    apply Nat.not_even_iff_odd.mp
    rintro ⟨k,hk⟩
    rcases Nat.even_or_odd a with ⟨j,hj⟩ | ⟨j,hj⟩
    · let w := 5^j*s^k
      have sq : p^2+4=w^2 := by rw [eqf,hj,hk,pow_add,pow_add]; dsimp only [w]; ring
      by_cases low : w≤p
      · nlinarith [Nat.mul_le_mul low low]
      · nlinarith [Nat.mul_le_mul (show p+1≤w by omega) (show p+1≤w by omega)]
    · let u := 5^j*s^k
      have form : p^2+4=5*u^2 := by
        rw [eqf,hj,hk,pow_succ,Nat.mul_comm 2 j,pow_mul,pow_add]; dsimp only [u]; ring
      have ou : Odd u := (show Odd 5 by decide).pow.mul (ps.odd_of_ne_two (by omega)).pow
      exact missing (square_fourth_even_witness pp op hp ou form)
  exact ⟨s,a,b,ps,lb,smod,ha,hb,ob,square_fourth_coprime pr lb hb outer eqf,eqf⟩


private theorem square_exponent_cutoff :
    ∃ C : ℕ, ∀ n x a t e : ℕ, C<n → (¬∃ k u v : ℕ, 0<k ∧ u.Prime ∧ v.Prime ∧ u≠v ∧ k<u ∧ k<v ∧ u∣n+k ∧ v∣n+k) → (x=3 ∨ x=5) → 0<e →
      n+x=x^a*t^e → (∀ l : ℕ, l.Prime → 2<l → l≤53 → ¬l∣e) := by
  let rows : List (ℕ×ℕ) := [(3,7),(5,11),(7,29),(11,23),(13,53),(17,103),(19,191),(23,47),(29,59),(31,311),(37,149),(41,83),(43,173),(47,283),(53,107)]
  have good (x : ℕ) (r : ℕ×ℕ) : ∃ D : ℕ, ∀ n a t e : ℕ,
      (x=3 ∨ x=5) → r∈rows → D<n → (¬∃ k u v : ℕ, 0<k ∧ u.Prime ∧ v.Prime ∧ u≠v ∧ k<u ∧ k<v ∧ u∣n+k ∧ v∣n+k) →
      0<e → n+x=x^a*t^e → ¬r.1∣e := by
    by_cases ok : (x=3 ∨ x=5) ∧ r∈rows
    · have table : ∀ v∈rows, 1<v.1 := by decide +kernel
      obtain ⟨D,hD⟩ := initial_odd_exponent_exclusions large_prime_of_square_add_one
        x 1 r.1 r.2 (Or.inr ok.1) (table _ ok.2) ok.2
      exact ⟨D,fun n a t e _ _ hn hsol he eq => hD n a t e hn hsol he (by simpa using eq)⟩
    · exact ⟨0,fun _ _ _ _ hx hr => (ok ⟨hx,hr⟩).elim⟩
  choose cap hcap using good
  let C := rows.toFinset.sup (fun r => max (cap 3 r) (cap 5 r))
  refine ⟨C,?_⟩
  intro n x a t e hn sol hx he eq l pl l2 l53
  have cover : ∀ i ∈ List.range 54, i.Prime → 2 < i → ∃ r∈rows, r.1=i := by decide +kernel
  obtain ⟨r,hr,rl⟩ := cover l (List.mem_range.mpr (by omega)) pl l2
  have bound : max (cap 3 r) (cap 5 r) ≤ C :=
    Finset.le_sup (f:=fun i => max (cap 3 i) (cap 5 i)) (List.mem_toFinset.mpr hr)
  rw [←rl]
  rcases hx with rfl|rfl
  · exact hcap 3 r n a t e (Or.inl rfl) hr (lt_of_le_of_lt ((Nat.le_max_left _ _).trans bound) hn) sol he eq
  · exact hcap 5 r n a t e (Or.inr rfl) hr (lt_of_le_of_lt ((Nat.le_max_right _ _).trans bound) hn) sol he eq

/-- The middle factor at the third offset contains one copy of its prime above three. -/
def H1 : Prop := ∃ T B : ℕ, ∀ p : ℕ, p.Prime → Odd p → B<p^2 →
    (∀ l : ℕ, l.Prime → l≤T → l∣p^2-1) →
    (∃ q r : ℕ, q.Prime ∧ r.Prime ∧ q≠r ∧ q%4=1 ∧ r%3=1 ∧
      p^2+1=2*q ∧ p^2+3=4*r) →
    (∃ s a b : ℕ, s.Prime ∧ 5<s ∧ s%4=1 ∧ 0<a ∧ 0<b ∧ Odd b ∧ a.Coprime b ∧ (∀ l : ℕ, l.Prime → 2<l → l≤53 → ¬l∣b) ∧ p^2+4=5^a*s^b) →
    (∃ t c : ℕ, t.Prime ∧ 3<t ∧ (t%8=1 ∨ t%8=3) ∧ 0<c ∧ p^2+2=3^c*t) →
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧ q∣p^2+d ∧ s∣p^2+d

/-- The remaining higher middle exponents have all prime factors above 53. -/
def H2 : Prop := ∃ T B : ℕ, ∀ p : ℕ, p.Prime → Odd p → B<p^2 →
    (∀ l : ℕ, l.Prime → l≤T → l∣p^2-1) →
    (∃ q r : ℕ, q.Prime ∧ r.Prime ∧ q≠r ∧ q%4=1 ∧ r%3=1 ∧
      p^2+1=2*q ∧ p^2+3=4*r) →
    (∃ s a b : ℕ, s.Prime ∧ 5<s ∧ s%4=1 ∧ 0<a ∧ 0<b ∧ Odd b ∧ a.Coprime b ∧ (∀ l : ℕ, l.Prime → 2<l → l≤53 → ¬l∣b) ∧ p^2+4=5^a*s^b) →
    (∃ t c e : ℕ, t.Prime ∧ 3<t ∧ (t%8=1 ∨ t%8=3) ∧ 0<c ∧ 53<e ∧ Odd e ∧
      c.Coprime e ∧ (∀ l : ℕ, l.Prime → 2<l → l≤53 → ¬l∣e) ∧ p^2+2=3^c*t^e) →
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧ q∣p^2+d ∧ s∣p^2+d


theorem main : H1 → H2 → OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2.H2 := by
  rintro ⟨X,A,h₁⟩ ⟨Y,B,h₂⟩
  let T := max X Y
  obtain ⟨C,hC⟩ := square_exponent_cutoff
  obtain ⟨D,hD⟩ := eventual_prime_support large_prime_of_square_add_one T T
  refine ⟨A+B+C+D+6562,?_⟩
  intro p pp op bound outer mid
  have large : 81<p := by
    by_contra! bad
    have sq := Nat.mul_le_mul bad bad
    rw [pow_two] at bound
    omega
  let n := p^2-1
  have sqpos : 0<p^2 := pow_pos pp.pos _
  have en : n+1=p^2 := by dsimp only [n]; omega
  by_contra missing
  have sol : (¬∃ k u v : ℕ, 0<k ∧ u.Prime ∧ v.Prime ∧ u≠v ∧ k<u ∧ k<v ∧ u∣n+k ∧ v∣n+k) := by
    rintro ⟨k,u,v,kp,pu,pv,ne,hu,hv,du,dv⟩
    have nk : n+k=p^2+(k-1) := by omega
    exact missing ⟨k-1,u,v,pu,pv,ne,by omega,by omega,nk ▸ du,nk ▸ dv⟩
  have small (l : ℕ) (pl : l.Prime) (lt : l≤T) : l∣p^2-1 := by
    obtain ⟨_,_,_,_,factors⟩ := hD n (by omega) sol l pl.pos lt
    exact (Nat.dvd_add_iff_left (dvd_refl l)).mpr ((factors l pl).mpr (Or.inl dvd_rfl))
  have fourth : ∃ s a b : ℕ, s.Prime ∧ 5<s ∧ s%4=1 ∧ 0<a ∧ 0<b ∧ Odd b ∧
      a.Coprime b ∧ (∀ l : ℕ, l.Prime → 2<l → l≤53 → ¬l∣b) ∧ p^2+4=5^a*s^b := by
    obtain ⟨q,r,pq,pr,_,_,_,first,last⟩ := outer
    obtain ⟨s,a,b,ps,hs,sm,ha,hb,od,cop,eq⟩ := square_fourth_cofactor pp op large pq first pr last missing
    exact ⟨s,a,b,ps,hs,sm,ha,hb,od,cop,hC n 5 a s b (by omega) sol (Or.inr rfl) hb (by omega),eq⟩
  apply missing
  obtain ⟨t,c,e,pt,ht,rt,hc,he,cop,pell,middle⟩ := mid
  by_cases one : e=1
  · apply h₁ p pp op (by omega) (fun l pl low => small l pl (low.trans (Nat.le_max_left X Y))) outer fourth
    exact ⟨t,c,pt,ht,rt,hc,by simpa only [one,pow_one] using middle⟩
  rcases Nat.even_or_odd e with ev | od
  · obtain ⟨ec,ee⟩ := pell ev
    obtain ⟨q,r,_,pr,_,_,_,_,right⟩ := outer
    exact (square_middle_pell_exclusion op (by omega) pr right
      (by simpa only [ec,ee,pow_one] using middle)).elim
  · have high := hC n 3 c t e (by omega) sol (Or.inl rfl) he (by omega)
    obtain ⟨l,pl,dl⟩ := Nat.exists_prime_and_dvd one
    have l2 : 2<l := by
      have := pl.two_le
      by_contra! low
      have el : l=2 := by omega
      rw [el] at dl
      obtain ⟨i,hi⟩ := od
      omega
    have big : 53<l := by by_contra! low; exact high l pl l2 low dl
    exact h₂ p pp op (by omega) (fun l pl low => small l pl (low.trans (Nat.le_max_right X Y))) outer fourth
      ⟨t,c,e,pt,ht,rt,hc,big.trans_le (Nat.le_of_dvd he dl),od,cop,high,middle⟩

end OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2_H2_R1
