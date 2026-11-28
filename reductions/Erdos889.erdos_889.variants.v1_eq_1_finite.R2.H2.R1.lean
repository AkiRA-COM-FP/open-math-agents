import OMAReductions.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2

/-!
The primality of the fourth-offset cofactor excludes every even middle exponent.
A cubic obstruction modulo seven distinguishes the remaining higher odd powers.
The fifth offset has a prime divisor above five. A factorization at offset ten
excludes a pure power of five.
-/

namespace OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2_H2_R1

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

theorem square_middle_cubic_index {p t c e : ℕ} (pp : p.Prime) (hp : 7<p)
    (cop : c.Coprime e) (middle : p^2+2=3^c*t^e) (de : 3∣e) : c%3=1 := by
  have nz : c%3 ≠ 0 := by
    intro z
    have h := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero z) de
    rw [Nat.coprime_iff_gcd_eq_one.mp cop] at h
    omega
  by_contra! notone
  have ec : c/3*3+2=c := by omega
  obtain ⟨m,hm⟩ := de
  let y := 3^(c/3)*t^m
  have eq : p^2+2=9*y^3 := by
    calc
      _ = 3^(c/3*3+2)*t^(m*3) := by rw [ec,Nat.mul_comm m 3,←hm,middle]
      _ = _ := by dsimp only [y]; rw [pow_add,pow_mul,pow_mul,mul_pow]; ring
  have z : p%7 ≠ 0 := by
    intro zz
    have ds := (Nat.dvd_prime pp).mp (Nat.dvd_of_mod_eq_zero zz)
    omega
  have table : ∀ u ∈ List.range 7, u≠0 → ∀ v ∈ List.range 7,
      (u^2+2)%7 ≠ (9*v^3)%7 := by decide +kernel
  apply table (p%7) (List.mem_range.mpr (by omega)) z (y%7) (List.mem_range.mpr (by omega))
  exact (((Nat.mod_modEq p 7).pow 2).add_right 2).trans
    (eq ▸ (((Nat.mod_modEq y 7).pow 3).mul_left 9).symm)

private theorem square_odd_prime_factor {x : ℕ} (large : 2<x) (h4 : ¬4∣x) :
    ∃ s : ℕ, s.Prime ∧ s≠2 ∧ s∣x := by
  by_cases even : 2∣x
  · obtain ⟨v,rfl⟩ := even
    obtain ⟨s,ps,ds⟩ := Nat.exists_prime_and_dvd (show v≠1 by omega)
    refine ⟨s,ps,?_,ds.trans (dvd_mul_left _ _)⟩
    rintro rfl
    exact h4 (Nat.mul_dvd_mul_left 2 ds)
  · obtain ⟨s,ps,ds⟩ := Nat.exists_prime_and_dvd (show x≠1 by omega)
    exact ⟨s,ps,fun eq => even (eq ▸ ds),ds⟩

private theorem square_fourth_pell_witness {p u : ℕ} (pp : p.Prime) (op : Odd p)
    (hp : 11<p) (ou : Odd u) (n5 : ¬5∣u^2+1) (eq : p^2+4=5*u^2) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧ q∣p^2+d ∧ s∣p^2+d := by
  obtain ⟨i,hi⟩ := op
  obtain ⟨j,hj⟩ := ou
  have lower : p+4<3*u := by
    by_contra! bad
    nlinarith [Nat.mul_le_mul bad bad,Nat.mul_le_mul (show 12≤p by omega) (Nat.le_refl p)]
  have upper : u<p := by
    by_contra! bad
    nlinarith [Nat.mul_le_mul bad bad,Nat.mul_le_mul hp.le hp.le]
  let L := (3*u-p)/2
  have eL : 2*L+p=3*u := by dsimp only [L]; omega
  have fac : L*(L+p)=u^2+1 := by
    have sq := congrArg (fun x : ℕ => x^2) eL
    nlinarith
  have four : ¬4∣u^2+1 := by
    have shape : u^2+1=4*(j^2+j)+2 := by rw [hj]; ring
    omega
  have left : L∣u^2+1 := fac ▸ dvd_mul_right _ _
  have right : L+p∣u^2+1 := fac ▸ dvd_mul_left _ _
  obtain ⟨q,pq,q2,dq⟩ := square_odd_prime_factor (by omega : 2<L) (fun h => four (h.trans left))
  obtain ⟨s,ps,s2,ds⟩ := square_odd_prime_factor (by omega : 2<L+p) (fun h => four (h.trans right))
  have big {v : ℕ} (pv : v.Prime) (v2 : v≠2) (dv : v∣u^2+1) : 10<v := by
    by_contra! small
    have tab : ∀ l ∈ List.range 11, l.Prime → l≠2 → ∀ w ∈ List.range l,
        (l=5 → (w^2+1)%5≠0) → (w^2+1)%l ≠ 0 := by decide +kernel
    have res (h : v=5) : ((u%v)^2+1)%5≠0 := by
      subst v
      intro z
      apply n5
      apply Nat.dvd_of_mod_eq_zero
      exact Eq.trans (((Nat.mod_modEq u 5).pow 2).add_right 1).symm z
    apply tab v (List.mem_range.mpr (by omega)) pv v2 (u%v)
      (List.mem_range.mpr (Nat.mod_lt _ pv.pos)) res
    exact (((Nat.mod_modEq u v).pow 2).add_right 1).trans (Nat.modEq_zero_iff_dvd.mpr dv)
  have ne : q≠s := by
    rintro rfl
    have dp : q∣p := (Nat.dvd_add_right dq).mp ds
    have qp := (Nat.prime_dvd_prime_iff_eq pq pp).mp dp
    have lb := Nat.le_of_dvd (show 0<L by omega) dq
    omega
  have w : u^2+1∣p^2+9 := ⟨5,by nlinarith⟩
  exact ⟨9,q,s,pq,ps,ne,big pq q2 (dq.trans left),big ps s2 (ds.trans right),
    dq.trans (left.trans w),ds.trans (right.trans w)⟩

private theorem square_fourth_no_five {x : ℕ} (d : 5∣x) : ¬5∣x^2+1 := by
  have sq : 5∣x^2 := d.trans (dvd_pow_self _ (by decide : 2≠0))
  omega

private theorem square_fourth_even_index {p s a b : ℕ} (pp : p.Prime) (op : Odd p)
    (hp : 11<p) (os : Odd s) (eq : p^2+4=5^a*s^b) (ev : Even b)
    (missing : ¬∃ d q r : ℕ, q.Prime ∧ r.Prime ∧ q≠r ∧ d+1<q ∧ d+1<r ∧
      q∣p^2+d ∧ r∣p^2+d) : a=1 ∧ b%4=2 := by
  obtain ⟨k,hk⟩ := ev
  rcases Nat.even_or_odd a with ⟨j,hj⟩ | ⟨j,hj⟩
  · let w := 5^j*s^k
    have sq : p^2+4=w^2 := by rw [eq,hj,hk,pow_add,pow_add]; dsimp only [w]; ring
    by_cases low : w≤p
    · nlinarith [Nat.mul_le_mul low low]
    · nlinarith [Nat.mul_le_mul (show p+1≤w by omega) (show p+1≤w by omega)]
  · let u := 5^j*s^k
    have form : p^2+4=5*u^2 := by rw [eq,hj,hk,pow_succ,Nat.mul_comm 2 j,pow_mul,pow_add]; dsimp only [u]; ring
    have ou : Odd u := (show Odd 5 by decide).pow.mul os.pow
    have z : j=0 := by
      by_contra jpos
      have ds : 5∣u := dvd_mul_of_dvd_left (dvd_pow_self 5 jpos) _
      exact missing (square_fourth_pell_witness pp op hp ou (square_fourth_no_five ds) form)
    refine ⟨by omega,?_⟩
    by_contra! bad
    have kp : k=k/2*2 := by omega
    have usq : u=(s^(k/2))^2 := by
      dsimp only [u]
      rw [z,pow_zero,one_mul,←pow_mul,←kp]
    have tab : ∀ w ∈ List.range 5, (w^4+1)%5≠0 := by decide +kernel
    have nf : ¬5∣u^2+1 := by
      intro d
      rw [usq,←pow_mul] at d
      exact tab ((s^(k/2))%5) (List.mem_range.mpr (by omega))
        ((((Nat.mod_modEq (s^(k/2)) 5).pow 4).add_right 1).trans (Nat.modEq_zero_iff_dvd.mpr d))
    exact missing (square_fourth_pell_witness pp op hp ou nf form)


private theorem square_fourth_cofactor {p q : ℕ} (pp : p.Prime) (op : Odd p)
    (hp : 11<p) (pq : q.Prime) (first : p^2+1=2*q)
    (missing : ¬∃ d a b : ℕ, a.Prime ∧ b.Prime ∧ a≠b ∧ d+1<a ∧ d+1<b ∧
      a∣p^2+d ∧ b∣p^2+d) :
    ∃ s a b : ℕ, s.Prime ∧ 5<s ∧ s%4=1 ∧ 0<a ∧ 0<b ∧ (Even b → a=1 ∧ b%4=2) ∧ p^2+4=5^a*s^b := by
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
      have jpos : j≠0 := by rintro rfl; norm_num at form; nlinarith [Nat.mul_le_mul hp.le hp.le]
      exact missing (square_fourth_pell_witness pp op hp ((by decide : Odd 5).pow)
        (square_fourth_no_five (dvd_pow_self 5 jpos)) form)
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
  exact ⟨s,a,b,ps,lb,smod,ha,hb,fun ev => square_fourth_even_index pp op hp
    (ps.odd_of_ne_two (by omega)) eqf ev missing,eqf⟩

/-- The middle factor at the third offset contains one copy of its prime above three. -/
def H1 : Prop := ∃ B : ℕ, ∀ p : ℕ, p.Prime → Odd p → B<p^2 →
    (∃ q r : ℕ, q.Prime ∧ r.Prime ∧ q≠r ∧ q%4=1 ∧ r%3=1 ∧
      p^2+1=2*q ∧ p^2+3=4*r) →
    (∃ s a b : ℕ, s.Prime ∧ 5<s ∧ s%4=1 ∧ 0<a ∧ 0<b ∧ (Even b → a=1 ∧ b%4=2) ∧ p^2+4=5^a*s^b) →
    (∃ t c : ℕ, t.Prime ∧ 3<t ∧ (t%8=1 ∨ t%8=3) ∧ 0<c ∧ p^2+2=3^c*t) →
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧ q∣p^2+d ∧ s∣p^2+d

/-- Higher middle exponents are odd, and a multiple of three requires the exponent
of three to equal one modulo three. -/
def H2 : Prop := ∃ B : ℕ, ∀ p : ℕ, p.Prime → Odd p → B<p^2 →
    (∃ q r : ℕ, q.Prime ∧ r.Prime ∧ q≠r ∧ q%4=1 ∧ r%3=1 ∧
      p^2+1=2*q ∧ p^2+3=4*r) →
    (∃ s a b : ℕ, s.Prime ∧ 5<s ∧ s%4=1 ∧ 0<a ∧ 0<b ∧ (Even b → a=1 ∧ b%4=2) ∧ p^2+4=5^a*s^b) →
    (∃ t c e : ℕ, t.Prime ∧ 3<t ∧ (t%8=1 ∨ t%8=3) ∧ 0<c ∧ 3≤e ∧ Odd e ∧
      c.Coprime e ∧ (3∣e → c%3=1) ∧ p^2+2=3^c*t^e) →
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧ q∣p^2+d ∧ s∣p^2+d

theorem main : H1 → H2 → OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2.H2 := by
  rintro ⟨A,h₁⟩ ⟨B,h₂⟩
  refine ⟨max A B+121,?_⟩
  intro p pp op bound outer mid
  have large : 11<p := by
    by_contra! bad
    have sq := Nat.mul_le_mul bad bad
    rw [pow_two] at bound
    omega
  have b₁ : A<p^2 := by have := Nat.le_max_left A B; omega
  have b₂ : B<p^2 := by have := Nat.le_max_right A B; omega
  by_contra missing
  apply missing
  have fourth : ∃ s a b : ℕ, s.Prime ∧ 5<s ∧ s%4=1 ∧ 0<a ∧ 0<b ∧ (Even b → a=1 ∧ b%4=2) ∧ p^2+4=5^a*s^b := by
    obtain ⟨q,r,pq,_,_,_,_,first,_⟩ := outer
    exact square_fourth_cofactor pp op large pq first missing
  obtain ⟨t,c,e,pt,ht,rt,hc,he,cop,pell,middle⟩ := mid
  by_cases one : e=1
  · apply h₁ p pp op b₁ outer fourth
    exact ⟨t,c,pt,ht,rt,hc,by simpa only [one,pow_one] using middle⟩
  rcases Nat.even_or_odd e with ev | od
  · obtain ⟨ec,ee⟩ := pell ev
    obtain ⟨q,r,_,pr,_,_,_,_,right⟩ := outer
    exact (square_middle_pell_exclusion op (by omega) pr right
      (by simpa only [ec,ee,pow_one] using middle)).elim
  · have le : 3≤e := by obtain ⟨k,hk⟩ := od; omega
    exact h₂ p pp op b₂ outer fourth ⟨t,c,e,pt,ht,rt,hc,le,od,cop,
      square_middle_cubic_index pp (by omega) cop middle,middle⟩

end OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2_H2_R1
