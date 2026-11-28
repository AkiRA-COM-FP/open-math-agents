import OMAReductions.R_mo_191889_R1
import Mathlib

/-!
# The large squarefree parameter in the powerful fourth-power census

Write the sum as b³k². Every prime of k is 1 modulo 8. We prove Lucas's
theorem for arbitrary coprime positive x and y by
factoring their fourth-power sum in the Gaussian integers. For the resulting
quartic z² + 3u⁴ = v⁴ a primitive solution splits as v² = a² + 3c²,
u² = 2ac. Reducing (v+a)/c yields a new solution whose positive
fourth-power coordinate is strictly smaller.

For cofactor 17, factoring off a Gaussian square of norm 17 gives a
single pair of binary cubics. Congruences modulo 16 and 9 give eight lattice
classes modulo 48. A strip-wise intersection of square-residue tests at
18 primes certifies the whole signed box |m|,|n| ≤ 469320. Thus k ≥ 41
and b ≤ 122475323887. The two remaining steps distinguish k = 41 from k ≥ 73.
A rational
right triangle with area 2b is constructed directly in both cases.

Chad Mazzola formalized Lucas's theorem using a different descent in Beal
reduction #9630. The reduced-slope proof here also
gives the auxiliary quartic for arbitrary positive u, including imprimitive inputs.
The prime-order and parity arguments below are adapted from ZedingZhang’s parent
reduction in #8603. The cube theorem and congruent-number sieve are used by
Noam D. Elkies and Gaurav Goel, *On powerful integers expressible as sums of
two coprime fourth powers*, sections 2 and 4.
https://antsmath.org/ANTSXV/papers/ANTS-XV_elkies-goel.pdf
-/

namespace OMA.R_mo_191889_R1_H3_R1

/-- After excluding 17, the first possible cofactor is 41. -/
def H1 : Prop :=
  ∀ b x y : ℕ, 10000 < b → b ≤ 122475323887 → Squarefree b →
    (∀ p ∈ b.primeFactors, p % 8 = 1) →
    (∃ a d c : ℚ, 0 < a ∧ 0 < d ∧ 0 < c ∧ a^2+d^2=c^2 ∧ a*d=4*(b:ℚ)) →
    0 < x → x < y → y ≤ 1325648472 → x.Coprime y →
    x^4+y^4=b^3*41^2 → b^3*41^2 < 3088257489493360278725196965477359217 → False

/-- The remaining cofactors are at least 73. -/
def H2 : Prop :=
  ∀ b k x y : ℕ, 10000 < b → b ≤ 83372455837 → Squarefree b →
    (∀ p ∈ b.primeFactors, p % 8 = 1) → 73 ≤ k →
    (∀ p ∈ k.primeFactors, p % 8 = 1) →
    (∃ a d c : ℚ, 0 < a ∧ 0 < d ∧ 0 < c ∧ a^2+d^2=c^2 ∧ a*d=4*(b:ℚ)) →
    0 < x → x < y → y ≤ 1325648472 → x.Coprime y →
    x^4+y^4=b^3*k^2 → b^3*k^2 < 3088257489493360278725196965477359217 → False

section Arithmetic

private theorem not_four {x y : ℕ} (hc : x.Coprime y) : ¬ 4 ∣ x^4+y^4 := by
  intro h
  have tab : ∀ i j : Fin 4, (i.val^4+j.val^4)%4 = 0 →
      i.val%2 = 0 ∧ j.val%2 = 0 := by decide
  have congr := ((Nat.mod_modEq x 4).pow 4).add ((Nat.mod_modEq y 4).pow 4)
  have h0 : ((x%4)^4+(y%4)^4)%4 = 0 := congr.trans h.modEq_zero_nat
  obtain ⟨hx,hy⟩ := tab ⟨x%4, Nat.mod_lt _ (by decide)⟩ ⟨y%4, Nat.mod_lt _ (by decide)⟩ h0
  change (x%4)%2 = 0 at hx
  change (y%4)%2 = 0 at hy
  rw [Nat.mod_mod_of_dvd x (by decide : 2 ∣ 4)] at hx
  rw [Nat.mod_mod_of_dvd y (by decide : 2 ∣ 4)] at hy
  have hd := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero hx) (Nat.dvd_of_mod_eq_zero hy)
  rw [show x.gcd y = 1 from hc] at hd
  norm_num at hd

private theorem prime_residue {x y p : ℕ} (hc : x.Coprime y) (hp : p.Prime)
    (hne : p ≠ 2) (hd : p ∣ x^4+y^4) : p%8 = 1 := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hz := (ZMod.natCast_eq_zero_iff (x^4+y^4) p).mpr hd
  push_cast at hz
  have hy : (y : ZMod p) ≠ 0 := by
    intro hy
    have hx : (x : ZMod p) = 0 := by simpa [hy] using hz
    have gd := Nat.dvd_gcd ((ZMod.natCast_eq_zero_iff x p).mp hx)
      ((ZMod.natCast_eq_zero_iff y p).mp hy)
    rw [show x.gcd y = 1 from hc] at gd
    exact hp.not_dvd_one gd
  let u := (x : ZMod p) / y
  have hu4 : u^4 = -1 := by
    change ((x : ZMod p) / y)^4 = -1
    rw [div_pow,div_eq_iff (pow_ne_zero _ hy)]
    linear_combination hz
  have hu8 : u^8 = 1 := by rw [show 8 = 4*2 by decide,pow_mul,hu4]; norm_num
  have hnot : u^4 ≠ 1 := by
    rw [hu4]
    intro he
    have htwo : (2 : ZMod p) = 0 := by linear_combination -he
    have hle := Nat.le_of_dvd (by decide : 0 < 2) ((ZMod.natCast_eq_zero_iff 2 p).mp htwo)
    have := hp.two_le
    omega
  have hd8 := orderOf_dvd_of_pow_eq_one hu8
  have hd4 : ¬ orderOf u ∣ 4 := fun h => hnot (orderOf_dvd_iff_pow_eq_one.mp h)
  have order : orderOf u = 8 := by
    have le := Nat.le_of_dvd (by decide : 0 < 8) hd8
    generalize hh : orderOf u = m at *
    interval_cases m <;> norm_num at *
  have une : u ≠ 0 := by intro h; simp [h] at hu8
  have div := ZMod.orderOf_dvd_card_sub_one une
  rw [order] at div
  obtain ⟨j,hj⟩ := div
  have := hp.two_le
  omega

/-- The Pythagorean triple for U = x⁴+y⁴ and V = 2x²y² supplies a triangle
of area 2b after division by xyz(y⁴−x⁴). -/
theorem triangle_of_quartic {x y z b : ℚ} (hx : 0<x) (hxy : x<y) (hz : 0<z)
    (he : x^4+y^4=b*z^2) :
    ∃ a d c : ℚ, 0<a ∧ 0<d ∧ 0<c ∧ a^2+d^2=c^2 ∧ a*d=4*b := by
  let u := x^4+y^4
  let v := 2*x^2*y^2
  let w := y^4-x^4
  let t := x*y*z
  have hy := hx.trans hxy
  have hu : 0<u := by dsimp [u]; positivity
  have hv : 0<v := by dsimp [v]; positivity
  have hw : 0<w := sub_pos.mpr (pow_lt_pow_left₀ hxy hx.le (by decide : 4≠0))
  have ht : 0<t := by dsimp [t]; positivity
  have rel : w^2=u^2-v^2 := by dsimp [u,v,w]; ring
  have size : 2*u*v=4*b*t^2 := by dsimp [u,v,t]; rw [he]; ring
  refine ⟨w^2/(t*w), (2*u*v)/(t*w), (u^2+v^2)/(t*w), by positivity,
    by positivity, by positivity, ?_, ?_⟩
  · rw [div_pow,div_pow,div_pow,←add_div]
    apply congrArg (fun q : ℚ => q/(t*w)^2)
    rw [rel]; ring
  · rw [size]
    field_simp [ht.ne',hw.ne']

private theorem gunit_fourth (u : GaussianIntˣ) : (u:GaussianInt)^4=1 := by
  have h := (Zsqrtd.norm_eq_one_iff' (show (-1:ℤ)≤0 by decide) (u:GaussianInt)).mpr u.isUnit
  generalize eq : (u:GaussianInt)=v at h ⊢
  obtain ⟨a,b⟩ := v
  change a*a-(-1)*b*b=1 at h
  have al : -1≤a := by by_contra! e; nlinarith [sq_nonneg b, mul_nonneg (show 0≤ -a-2 by omega) (show 0≤ -a+2 by omega)]
  have ah : a≤1 := by by_contra! e; nlinarith [sq_nonneg b, mul_nonneg (show 0≤ a-2 by omega) (show 0≤ a+2 by omega)]
  have bl : -1≤b := by by_contra! e; nlinarith [sq_nonneg a, mul_nonneg (show 0≤ -b-2 by omega) (show 0≤ -b+2 by omega)]
  have bh : b≤1 := by by_contra! e; nlinarith [sq_nonneg a, mul_nonneg (show 0≤ b-2 by omega) (show 0≤ b+2 by omega)]
  interval_cases a <;> interval_cases b <;> norm_num at h <;> decide

private theorem quartic_coprime {x y b z : ℕ} (hc : x.Coprime y) (hb : Odd b)
    (he : x^4+y^4=b*z^2) :
    let a : GaussianInt := ⟨(x:ℤ)^2,(y:ℤ)^2⟩
    IsCoprime a (star a) := by
  let a : GaussianInt := ⟨(x:ℤ)^2,(y:ℤ)^2⟩
  let i : GaussianInt := ⟨0,1⟩
  change IsCoprime a (star a)
  have hz : Odd z := by
    rcases Nat.even_or_odd z with ev|od
    · have h4 : 2^2 ∣ z^2 := pow_dvd_pow_of_dvd (even_iff_two_dvd.mp ev) 2
      exact (not_four hc (he ▸ dvd_mul_of_dvd_right h4 b)).elim
    · exact od
  have plus : a+star a=2*(x:GaussianInt)^2 := by
    ext <;> simp [a,star,pow_two]
    ring
  have minus : (-i)*(a-star a)=2*(y:GaussianInt)^2 := by
    ext <;> simp [a,i,star,pow_two]
    ring
  have prod : a*star a=((b*z^2:ℕ):GaussianInt) := by
    rw [← he,Zsqrtd.natCast_val]
    ext <;> simp [a,star] <;> ring
  have cps := ((hc.pow_left 2).pow_right 2).isCoprime.map (Int.castRingHom GaussianInt)
  have oddN := Nat.coprime_two_left.mpr (hb.mul (hz.pow (n:=2)))
  have cp2 := oddN.isCoprime.map (Int.castRingHom GaussianInt)
  simp only [Int.coe_castRingHom, Nat.cast_pow, Int.cast_pow, Int.cast_natCast] at cps
  change IsCoprime (2:GaussianInt) ((b*z^2:ℕ):GaussianInt) at cp2
  apply IsRelPrime.isCoprime
  intro d da dc
  have dx := plus ▸ dvd_add da dc
  have dy := minus ▸ dvd_mul_of_dvd_right (dvd_sub da dc) (-i)
  have d2 : d ∣ 2 := by
    obtain ⟨j,k,eq⟩ := cps
    have ds := dvd_add (dvd_mul_of_dvd_left dx j) (dvd_mul_of_dvd_left dy k)
    convert ds using 1
    linear_combination -2*eq
  exact cp2.isRelPrime d2 (prod ▸ dvd_mul_of_dvd_left da _)

private theorem quartic_norm (x y : ℕ) :
    (⟨(x:ℤ)^2,(y:ℤ)^2⟩ : GaussianInt).norm = ((x^4+y^4 : ℕ):ℤ) := by
  simp [Zsqrtd.norm]
  ring

/-- A scalar square in a primitive Gaussian norm can be removed as a Gaussian square. -/
private theorem strip_norm_square {a : GaussianInt} {b z : ℕ}
    (cp : IsCoprime a (star a)) (hz : 0<z) (he : a.norm=(b:ℤ)*(z:ℤ)^2) :
    ∃ B W : GaussianInt, a=B*W^2 ∧ B.norm=b ∧ W.norm=z := by
  have prod : a*star a=(b:GaussianInt)*(z:GaussianInt)^2 := by
    rw [← Zsqrtd.norm_eq_mul_conj, he]
    push_cast
    rfl
  have scalar : (z:GaussianInt)^2 ∣ a*star a := prod ▸ dvd_mul_left _ _
  obtain ⟨d,e,da,ec,hde⟩ := exists_dvd_and_dvd_of_dvd_mul
    ((dvd_pow_self (z:GaussianInt) (by decide : 2≠0)).trans scalar)
  have sd : star d ∣ star a := map_dvd (starRingEnd GaussianInt) da
  have se : star e ∣ a := by
    have h := map_dvd (starRingEnd GaussianInt) ec
    simpa only [starRingEnd_apply,star_star] using h
  have rev : (z:GaussianInt)=star e*star d := by
    simpa only [star_natCast,star_mul] using congrArg star hde
  have cpd := cp.of_isCoprime_of_dvd_left da
  have cpe := cp.of_isCoprime_of_dvd_left se
  have dse : d ∣ star e :=
    (cpd.of_isCoprime_of_dvd_right sd).dvd_of_dvd_mul_right
      (rev ▸ hde.symm ▸ dvd_mul_right d e)
  have sed : star e ∣ d :=
    (cpe.of_isCoprime_of_dvd_right ec).dvd_of_dvd_mul_right
      (hde ▸ rev.symm ▸ dvd_mul_right (star e) (star d))
  have en : d.norm=e.norm := by
    simpa using Zsqrtd.norm_eq_of_associated (by decide : (-1:ℤ)≤0)
      (associated_of_dvd_dvd dse sed)
  have normZ := congrArg Zsqrtd.norm hde
  rw [Zsqrtd.norm_natCast,Zsqrtd.norm_mul,←en] at normZ
  have dn : d.norm=(z:ℤ) := (sq_eq_sq₀ (GaussianInt.norm_nonneg d) (by positivity)).mp
    (by simpa [pow_two] using normZ.symm)
  have d2 : d^2 ∣ a := cpd.pow_left.dvd_of_dvd_mul_right
    ((pow_dvd_pow_of_dvd (hde ▸ dvd_mul_right d e) 2).trans scalar)
  obtain ⟨B,hab⟩ := d2
  have n := congrArg Zsqrtd.norm hab
  simp only [Zsqrtd.norm_mul,pow_two,dn,he] at n
  have bn : B.norm=(b:ℤ) := by
    have zz : (z:ℤ)*(z:ℤ)≠0 := by positivity
    exact mul_right_cancel₀ zz (by linear_combination -n)
  exact ⟨B,d,hab.trans (mul_comm _ _),bn,dn⟩

private theorem cube_of_norm {a : GaussianInt} {b : ℕ} (hc : IsCoprime a (star a))
    (hn : a.norm=(b:ℤ)^3) : ∃ B : GaussianInt, a=B^3 ∧ B.norm=b := by
  have prod : a*star a=(b:GaussianInt)^3 := by
    rw [← Zsqrtd.norm_eq_mul_conj,hn]
    push_cast
    rfl
  obtain ⟨d,⟨u,hu⟩⟩ := exists_associated_pow_of_mul_eq_pow' hc prod
  let B := d*(u:GaussianInt)^3
  have cube : a=B^3 := by
    rw [←hu]
    dsimp [B]
    rw [mul_pow]
    have e := gunit_fourth u
    calc d^3*(u:GaussianInt) = d^3*(((u:GaussianInt)^4)^2*(u:GaussianInt)) := by rw [e]; ring
         _ = d^3*((u:GaussianInt)^3)^3 := by ring
  refine ⟨B,cube,(Odd.strictMono_pow (by decide : Odd 3)).injective ?_⟩
  rw [← hn,cube]
  simp [pow_succ]

/-- The condition b ∣ z gives the stronger factorization with Gaussian exponents 3 and 2. -/
private theorem powerful_descent {b k x y : ℕ} (hb : Odd b) (hk : 0<k) (hc : x.Coprime y)
    (he : x^4+y^4=b^3*k^2) :
    ∃ B W : GaussianInt, (⟨(x:ℤ)^2,(y:ℤ)^2⟩ : GaussianInt)=B^3*W^2 ∧
      B.norm=b ∧ W.norm=k := by
  let a : GaussianInt := ⟨(x:ℤ)^2,(y:ℤ)^2⟩
  have cp : IsCoprime a (star a) :=
    quartic_coprime hc hb (he.trans (by ring : b^3*k^2=b*(b*k)^2))
  have hn : a.norm=((b^3:ℕ):ℤ)*(k:ℤ)^2 := by
    rw [quartic_norm,he]
    push_cast
    rfl
  obtain ⟨D,W,eq,dn,wn⟩ := strip_norm_square cp hk hn
  have da : D ∣ a := eq ▸ dvd_mul_right _ _
  have dc : star D ∣ star a := map_dvd (starRingEnd GaussianInt) da
  obtain ⟨B,cube,bn⟩ := cube_of_norm
    ((cp.of_isCoprime_of_dvd_left da).of_isCoprime_of_dvd_right dc) (by simpa using dn)
  exact ⟨B,W,eq.trans (by rw [cube]),bn,wn⟩

private theorem gaussian_cube {x y b : ℕ} (hc : x.Coprime y) (hodd : Odd b)
    (he : x^4+y^4=b^3) :
    ∃ m n : ℤ, (x:ℤ)^2=m*(m^2-3*n^2) ∧ (y:ℤ)^2=n*(3*m^2-n^2) ∧
      m^2+n^2=(b:ℤ) := by
  obtain ⟨B,fac,hn⟩ := cube_of_norm
    (quartic_coprime (z:=b) hc hodd (he.trans (by ring))) (by rw [quartic_norm,he]; push_cast; rfl)
  obtain ⟨m,n⟩ := B
  have ex := congrArg Zsqrtd.re fac
  have ey := congrArg Zsqrtd.im fac
  simp [pow_succ] at ex ey
  refine ⟨m,n,by linear_combination ex,by linear_combination ey,?_⟩
  simpa [Zsqrtd.norm,pow_two] using hn

private theorem square_class {m c X : ℕ} (hm : 0 < m) (he : m*c=X^2) (hd : m.gcd c ∣ 3) :
    ∃ u : ℕ, m=u^2 ∨ m=3*u^2 := by
  let g := m.gcd c
  have hp : 0 < g := Nat.gcd_pos_of_pos_left c hm
  have dm := Nat.gcd_dvd_left m c
  have dc := Nat.gcd_dvd_right m c
  have mm : m/g*g=m := Nat.div_mul_cancel dm
  have cc : c/g*g=c := Nat.div_mul_cancel dc
  have dvd : g^2 ∣ X^2 := by rw [←he,pow_two]; exact Nat.mul_dvd_mul dm dc
  obtain ⟨v,hv⟩ := (Nat.pow_dvd_pow_iff (by decide : 2≠0)).mp dvd
  have eq : m/g*(c/g)=v^2 := by
    apply Nat.eq_of_mul_eq_mul_right (show 0 < g^2 from pow_pos hp _)
    calc m/g*(c/g)*g^2 = (m/g*g)*(c/g*g) := by ring
         _ = X^2 := by rw [mm,cc,he]
         _ = v^2*g^2 := by rw [hv];ring
  have cp : (m/g).Coprime (c/g) := Nat.coprime_div_gcd_div_gcd hp
  obtain ⟨u,hu⟩ := exists_eq_pow_of_mul_eq_pow
    (show IsUnit (gcd (m/g) (c/g)) by change IsUnit ((m/g).gcd (c/g)); rw [cp]; exact isUnit_one) eq
  have gor : g=1 ∨ g=3 := (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd
  rw [hu] at mm
  exact ⟨u, gor.elim (fun e => Or.inl (by simpa [e] using mm.symm))
    (fun e => Or.inr (by simpa [e,Nat.mul_comm] using mm.symm))⟩

private theorem coefficient {m n : ℤ} (cp : m.natAbs.Coprime n.natAbs) :
    m.natAbs.gcd (m^2-3*n^2).natAbs ∣ 3 := by
  let g := m.natAbs.gcd (m^2-3*n^2).natAbs
  have gm : g ∣ m.natAbs := Nat.gcd_dvd_left _ _
  have gf : g ∣ (m^2-3*n^2).natAbs := Nat.gcd_dvd_right _ _
  have mg : (g:ℤ) ∣ m := Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr gm)
  have fg : (g:ℤ) ∣ m^2-3*n^2 := Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr gf)
  have d : (g:ℤ) ∣ 3*n^2 := by
    have sub := dvd_sub (dvd_pow mg (by decide : 2≠0)) fg
    simpa only [sub_sub_cancel] using sub
  have dn : g ∣ 3*n.natAbs^2 := by
    have h := Int.dvd_natAbs.mpr d
    simpa only [Int.natAbs_mul,Int.natAbs_pow,show (3 : ℤ).natAbs = 3 by decide, Nat.cast_mul,
      Nat.cast_pow,Nat.cast_ofNat] using (Int.natCast_dvd_natCast.mp h)
  have cg : g.Coprime (n.natAbs^2) := (cp.coprime_dvd_left gm).pow_right 2
  exact cg.dvd_of_dvd_mul_right dn

private theorem coordinates_coprime {x y : ℕ} {m n : ℤ} (hc : x.Coprime y)
    (ex : (x:ℤ)^2=m*(m^2-3*n^2)) (ey : (y:ℤ)^2=n*(3*m^2-n^2)) :
    m.natAbs.Coprime n.natAbs := by
  apply Nat.coprime_of_dvd
  intro p pr pm pn
  have hx := congrArg Int.natAbs ex
  have hy := congrArg Int.natAbs ey
  simp only [Int.natAbs_pow,Int.natAbs_mul,Int.natAbs_natCast] at hx hy
  have px := pr.dvd_of_dvd_pow (show p ∣ x^2 by rw [hx]; exact dvd_mul_of_dvd_left pm _)
  have py := pr.dvd_of_dvd_pow (show p ∣ y^2 by rw [hy]; exact dvd_mul_of_dvd_left pn _)
  exact (Nat.not_coprime_of_dvd_of_dvd pr.one_lt px py) hc

/-- Squaring a natural absolute value recovers the original integer square. -/
private theorem absSquare (a : ℤ) : (a.natAbs:ℤ)^2=a^2 := by
  rw [Int.natCast_natAbs,←abs_pow,abs_of_nonneg (sq_nonneg _)]

private theorem smaller_square {A B X : ℕ} (h : A≤B)
    (he : X^2=A*((A:ℤ)^2-3*(B:ℤ)^2).natAbs) :
    X^2=A*(3*B^2-A^2) := by
  have le : A^2≤3*B^2 := by have := Nat.pow_le_pow_left h 2; omega
  have e : (A:ℤ)^2-3*(B:ℤ)^2 = -((3*B^2-A^2 : ℕ):ℤ) := by
    rw [Nat.cast_sub le];push_cast;ring
  simpa only [e,Int.natAbs_neg,Int.natAbs_natCast] using he

/-- The prime 3 has odd valuation in three times a nonzero square. -/
private theorem not_three_square_sum {a b c : ℕ} (hc : 0<c) (h : a^2+b^2=3*c^2) : False := by
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hn : 3*c^2≠0 := by positivity
  have hm : 3 ∈ (3*c^2).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨by decide,dvd_mul_right _ _,hn⟩
  have even := Nat.eq_sq_add_sq_iff.mp ⟨a,b,h.symm⟩ 3 hm (by decide)
  rw [padicValNat.mul (by decide) (by positivity),padicValNat.pow (p:=3) c 2,
    padicValNat_self] at even
  rcases even with ⟨q,hq⟩
  omega

private theorem unscale {X d c : ℕ} (hd : 0<d) (h : X^2=d^2*c) : ∃ w : ℕ, w^2=c := by
  have dvd : d^2 ∣ X^2 := h ▸ dvd_mul_right _ _
  obtain ⟨w,eq⟩ := (Nat.pow_dvd_pow_iff (by decide : 2≠0)).mp dvd
  rw [eq,mul_pow] at h
  exact ⟨w,Nat.eq_of_mul_eq_mul_left (pow_pos hd 2) h⟩

/-- Congruences modulo 16 and 9 control parity and the prime 3. -/
private theorem primitive_residues {u v z : ℕ} (cp : u.Coprime v)
    (he : z^2+3*u^4=v^4) : u%2=0 ∧ v%2=1 ∧ z%2=1 ∧ ¬3∣v := by
  have red (p : ℕ) : ((z%p)^2+3*(u%p)^4)%p=(v%p)^4%p := by
    have h := ((Nat.mod_modEq z p).pow 2).add (((Nat.mod_modEq u p).pow 4).mul_left 3)
    exact h.trans (he ▸ ((Nat.mod_modEq v p).pow 4).symm)
  have tab : ∀ i j k : Fin 16, (i.val^2+3*j.val^4)%16=k.val^4%16 →
      j.val%2=0 ∧ i.val%2=k.val%2 := by decide +kernel
  have h := tab ⟨z%16,Nat.mod_lt _ (by decide)⟩ ⟨u%16,Nat.mod_lt _ (by decide)⟩
    ⟨v%16,Nat.mod_lt _ (by decide)⟩ (red 16)
  change (u%16)%2=0 ∧ (z%16)%2=(v%16)%2 at h
  simp only [Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 16)] at h
  have vo : v%2=1 := by
    by_contra hn
    exact (Nat.not_coprime_of_dvd_of_dvd (by decide : 1<2)
      (Nat.dvd_of_mod_eq_zero h.1) (Nat.dvd_of_mod_eq_zero (by omega))) cp
  refine ⟨h.1,vo,h.2.trans vo,?_⟩
  intro dv
  have t : ∀ i j k : Fin 9, (i.val^2+3*j.val^4)%9=k.val^4%9 →
      k.val%3=0 → j.val%3=0 := by decide +kernel
  have e := t ⟨z%9,Nat.mod_lt _ (by decide)⟩ ⟨u%9,Nat.mod_lt _ (by decide)⟩
    ⟨v%9,Nat.mod_lt _ (by decide)⟩ (red 9)
  change (v%9)%3=0 → (u%9)%3=0 at e
  simp only [Nat.mod_mod_of_dvd _ (by decide : 3 ∣ 9)] at e
  exact (Nat.not_coprime_of_dvd_of_dvd (by decide : 1<3)
    (Nat.dvd_of_mod_eq_zero (e (Nat.mod_eq_zero_of_dvd dv))) dv) cp

private theorem square_pair {a b t : ℕ} (hab : a.Coprime b) (he : a*b=t^2) :
    ∃ m n : ℕ, a=m^2 ∧ b=n^2 := by
  have first {x y : ℕ} (hc : x.Coprime y) (h : x*y=t^2) : ∃ s : ℕ, x=s^2 := by
    exact exists_eq_pow_of_mul_eq_pow
      (show IsUnit (gcd x y) by change IsUnit (x.gcd y); rw [hc]; exact isUnit_one) h
  obtain ⟨m,hm⟩ := first hab he
  obtain ⟨n,hn⟩ := first hab.symm ((mul_comm b a).trans he)
  exact ⟨m,n,hm,hn⟩

/-- Split (v²+z)/2 and (v²-z)/2 into one square and three times a square. -/
private theorem split_quartic {u v z : ℕ} (up : 0<u) (cp : u.Coprime v)
    (he : z^2+3*u^4=v^4) :
    ∃ a c : ℕ, 0<a ∧ 0<c ∧ v^2=a^2+3*c^2 ∧ u^2=2*a*c := by
  obtain ⟨ue,vo,zo,h3⟩ := primitive_residues cp he
  obtain ⟨h,uh⟩ := Nat.dvd_of_mod_eq_zero ue
  have zv : z<v^2 := by
    by_contra! hn
    have le := Nat.pow_le_pow_left hn 2
    rw [show (v^2)^2=v^4 by ring] at le
    have := pow_pos up 4
    omega
  have vodd : v^2%2=1 := by rw [Nat.pow_mod,vo]
  let F := (v^2+z)/2
  let G := (v^2-z)/2
  have sum : F+G=v^2 := by dsimp [F,G]; omega
  have diff : G+z=F := by dsimp [F,G]; omega
  have gp : 0<G := by dsimp [G]; omega
  have fp : 0<F := by omega
  have prod : F*G=3*(2*h^2)^2 := by
    have hq : (F+G)^2=z^2+3*(2*h)^4 := by rw [sum,←uh,he]; ring
    rw [←diff] at hq ⊢
    nlinarith only [hq]
  have cop : F.Coprime G := by
    apply Nat.coprime_of_dvd
    intro p pr df dg
    have dv : p∣v := pr.dvd_of_dvd_pow (sum ▸ dvd_add df dg)
    have dz : p∣z := (Nat.dvd_add_iff_right dg).mpr (diff ▸ df)
    have d3 : p∣3*u^4 := (Nat.dvd_add_iff_right (dvd_pow dz (by decide : 2≠0))).mpr
      (he ▸ dvd_pow dv (by decide : 4≠0))
    rcases pr.dvd_mul.mp d3 with q|q
    · have e := (Nat.prime_dvd_prime_iff_eq pr (by decide : Nat.Prime 3)).mp q
      exact h3 (e ▸ dv)
    · exact (Nat.not_coprime_of_dvd_of_dvd pr.one_lt (pr.dvd_of_dvd_pow q) dv) cp
  have split (A B : ℕ) (ap : 0<A) (bp : 0<B) (ab : A.Coprime B)
      (su : A+B=v^2) (mul : A*B=3*(2*h^2)^2) (d : 3∣B) :
      ∃ a c : ℕ, 0<a ∧ 0<c ∧ v^2=a^2+3*c^2 ∧ u^2=2*a*c := by
    obtain ⟨D,bd⟩ := d
    have ac := ab.coprime_dvd_right (bd ▸ dvd_mul_left D 3)
    have sq : A*D=(2*h^2)^2 := by rw [bd] at mul; nlinarith only [mul]
    obtain ⟨a,c,aa,cc⟩ := square_pair ac sq
    have eq : a*c=2*h^2 := (sq_eq_sq₀ (by positivity) (by positivity)).mp (by
      rw [mul_pow,←aa,←cc]; exact sq)
    refine ⟨a,c,by by_contra! hn; simp [aa,show a=0 by omega] at ap,
      by by_contra! hn; simp [bd,cc,show c=0 by omega] at bp,?_,?_⟩
    · rw [←su,aa,bd,cc]
    · rw [uh,show 2*a*c=2*(a*c) by ring,eq]; ring
  have d : 3∣F*G := prod ▸ dvd_mul_right _ _
  rcases (show Nat.Prime 3 by decide).dvd_mul.mp d with f|g
  · exact split G F gp fp cop.symm ((add_comm G F).trans sum) ((mul_comm G F).trans prod) f
  · exact split F G fp gp cop sum prod g

/-- Reduce the slope (v+a)/c to A/B. Its denominator is a square. The
numerator must also be a square because the other square class would make
three times a nonzero square a sum of two squares. -/
private theorem descend_slope {u v a c : ℕ} (ap : 0<a) (cp : 0<c)
    (vv : v^2=a^2+3*c^2) (uu : u^2=2*a*c) :
    ∃ s t w : ℕ, 0<t ∧ t.Coprime s ∧ s<v ∧ w^2+3*t^4=s^4 := by
  let p := v+a
  let g := p.gcd c
  let A := p/g
  let B := c/g
  have pp : 0<p := by dsimp [p]; omega
  have gp : 0<g := Nat.gcd_pos_of_pos_left c pp
  have dp : g∣p := Nat.gcd_dvd_left p c
  have dc : g∣c := Nat.gcd_dvd_right p c
  have ga : g*A=p := Nat.mul_div_cancel' dp
  have gb : g*B=c := Nat.mul_div_cancel' dc
  have AP : 0<A := Nat.div_pos (Nat.le_of_dvd pp dp) gp
  have BP : 0<B := Nat.div_pos (Nat.le_of_dvd cp dc) gp
  have ab : A.Coprime B := Nat.coprime_div_gcd_div_gcd gp
  have ident : (g*A)^2=3*(g*B)^2+2*a*p := by
    rw [ga,gb]; dsimp only [p]; nlinarith only [vv]
  have ge : 3*B^2 ≤ A^2 := by
    by_contra! lt
    have neg := Nat.mul_lt_mul_of_pos_left lt (pow_pos gp 2)
    nlinarith only [neg,ident,Nat.zero_le (2*a*p)]
  let D := A^2-3*B^2
  have sub : 3*B^2+D=A^2 := Nat.add_sub_of_le ge
  have gd : g^2*D=2*a*p := by
    have eq := congrArg (fun n => g^2*n) sub
    nlinarith only [eq,ident]
  have raw : (u*p)^2=(g^2)^2*(A*B*D) := by
    calc (u*p)^2 = (2*a*p)*(p*c) := by rw [mul_pow,uu]; ring
         _ = (g^2*D)*((g*A)*(g*B)) := by rw [gd,ga,gb]
         _ = _ := by ring
  obtain ⟨w,hw⟩ := unscale (pow_pos gp 2) raw
  have bd : B.Coprime D := by
    apply Nat.coprime_of_dvd
    intro l pr lb ld
    have h : l∣A^2 := sub ▸ dvd_add (dvd_mul_of_dvd_right (dvd_pow lb (by decide : 2≠0)) 3) ld
    exact (Nat.not_coprime_of_dvd_of_dvd pr.one_lt (pr.dvd_of_dvd_pow h) lb) ab
  obtain ⟨t,w',tb,hw'⟩ := square_pair (ab.symm.mul_right bd)
    (show B*(A*D)=w^2 by rw [hw]; ring)
  have tp : 0<t := by by_contra! hn; simp [tb,show t=0 by omega] at BP
  have gcd3 : A.gcd D ∣ 3 := by
    let d := A.gcd D
    have da : d∣A := Nat.gcd_dvd_left _ _
    have dd : d∣D := Nat.gcd_dvd_right _ _
    have d3 : d∣3*B^2 := (Nat.dvd_add_iff_left dd).mpr (sub ▸ dvd_pow da (by decide : 2≠0))
    exact ((ab.coprime_dvd_left da).pow_right 2).dvd_of_dvd_mul_right d3
  obtain ⟨s,hs|hs⟩ := square_class AP hw' gcd3
  · have sp : 0<s := by by_contra! hn; simp [hs,show s=0 by omega] at AP
    obtain ⟨w0,eq⟩ := unscale sp (show w'^2=s^2*D by rw [←hw',hs])
    have av : a<v := by
      by_contra! va
      have bad := Nat.pow_le_pow_left va 2
      have pos := pow_pos cp 2
      omega
    have below : s<v := by
      have bound : A≤p := Nat.div_le_self _ _
      change A≤v+a at bound
      by_contra! vs
      have square := Nat.pow_le_pow_left vs 2
      have tw : 2≤v := by omega
      have two := Nat.mul_le_mul_right v tw
      rw [←pow_two] at two
      omega
    have cop : t.Coprime s := ab.symm.coprime_dvd_left
      (tb ▸ dvd_pow_self t (by decide : 2≠0)) |>.coprime_dvd_right
      (hs ▸ dvd_pow_self s (by decide : 2≠0))
    refine ⟨s,t,w0,tp,cop,below,?_⟩
    rw [hs,tb] at sub
    rw [eq]
    nlinarith only [sub]
  · have sp : 0<s := by by_contra! hn; simp [hs,show s=0 by omega] at AP
    have Dform : D=3*(3*s^4-t^4) := by
      dsimp only [D]; rw [hs,tb,Nat.mul_sub]; congr 1 <;> ring
    obtain ⟨j,eq⟩ := unscale (show 0<3*s by positivity)
      (show w'^2=(3*s)^2*(3*s^4-t^4) by rw [←hw',hs,Dform]; ring)
    have small : t^4 ≤ 3*s^4 := by rw [hs,tb] at ge; nlinarith only [ge]
    have add := Nat.sub_add_cancel small
    exact (not_three_square_sum (pow_pos sp 2)
      (show j^2+(t^2)^2=3*(s^2)^2 by rw [eq]; nlinarith only [add])).elim

private theorem no_primitive_quartic (v : ℕ) :
    ∀ u z : ℕ, 0<u → u.Coprime v → z^2+3*u^4=v^4 → False := by
  induction v using Nat.strong_induction_on with
  | h v ih =>
    intro u z up cp he
    obtain ⟨a,c,ap,cpos,vv,uu⟩ := split_quartic up cp he
    obtain ⟨s,t,w,tp,cop,lt,eq⟩ := descend_slope ap cpos vv uu
    exact ih s lt t w tp cop eq

/-- Infinite descent excludes z² + 3u⁴ = v⁴ for every positive u. -/
theorem quartic_three {u v z : ℕ} (up : 0<u) (he : z^2+3*u^4=v^4) : False := by
  let g := u.gcd v
  let U := u/g
  let V := v/g
  have gp : 0<g := Nat.gcd_pos_of_pos_left _ up
  have du : g∣u := Nat.gcd_dvd_left _ _
  have gu : g*U=u := Nat.mul_div_cancel' du
  have gv : g*V=v := Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
  have eq : z^2+g^4*(3*U^4)=g^4*V^4 := by
    rw [←gu,←gv] at he
    nlinarith only [he]
  have le : 3*U^4≤V^4 := by
    by_contra! h
    have lt := Nat.mul_lt_mul_of_pos_left h (pow_pos gp 4)
    omega
  have sq : z^2=(g^2)^2*(V^4-3*U^4) := by
    rw [show (g^2)^2=g^4 by ring,Nat.mul_sub]; omega
  obtain ⟨w,hw⟩ := unscale (pow_pos gp 2) sq
  exact no_primitive_quartic V U w (Nat.div_pos (Nat.le_of_dvd up du) gp)
    (Nat.coprime_div_gcd_div_gcd gp) (by omega)

/-- If the smaller Gaussian coordinate is a square, the local obstruction at
3 suffices. If it is three times a square, coprimality makes the other
coordinate a square, giving precisely Z² + 3u⁴ = v⁴. -/
private theorem small_magnitude {u v s t X : ℕ} (up : 0<u)
    (vp : 0<v) (ss : s=1 ∨ s=3) (tt : t=1 ∨ t=3)
    (cp : (s*u^2).Coprime (t*v^2)) (le : s*u^2 ≤ t*v^2)
    (h : X^2=(s*u^2)*(3*(t*v^2)^2-(s*u^2)^2)) : False := by
  rcases ss with rfl|rfl
  · simp only [one_mul] at h le
    obtain ⟨w,hw⟩ := unscale up h
    have posT : 0<t := by omega
    have posN : 0<t*v^2 := by positivity
    have ll : (u^2)^2≤3*(t*v^2)^2 := by have := Nat.pow_le_pow_left le 2; omega
    exact not_three_square_sum posN (show w^2+(u^2)^2=3*(t*v^2)^2 by omega)
  · rcases tt with rfl|rfl
    · simp only [one_mul] at h le
      have f : 3*(v^2)^2-(3*u^2)^2 = 3*(v^4-3*u^4) := by
        rw [Nat.mul_sub]
        congr 1 <;> ring
      have hx : X^2=(3*u)^2*(v^4-3*u^4) := by rw [h,f];ring
      obtain ⟨w,hw⟩ := unscale (show 0<3*u by positivity) hx
      have ll := Nat.pow_le_pow_left le 2
      have u4 : (3*u^2)^2 = 9*u^4 := by ring
      have v4 : (v^2)^2=v^4 := by ring
      rw [u4,v4] at ll
      exact quartic_three up (show w^2+3*u^4=v^4 by omega)
    · exact (Nat.not_coprime_of_dvd_of_dvd (by decide : 1<3) (dvd_mul_right _ _) (dvd_mul_right _ _)) cp

/-- The Gaussian cube descent excludes every odd cube. -/
private theorem cube_excluded_odd {b x y : ℕ}
    (hodd : Odd b) (hx : 0<x) (hy : 0<y) (hc : x.Coprime y) (he : x^4+y^4=b^3) : False := by
  obtain ⟨m,n,ex,ey,_⟩ := gaussian_cube hc hodd he
  let A := m.natAbs
  let B := n.natAbs
  have xx : x^2=A*(m^2-3*n^2).natAbs := by
    simpa only [A,Int.natAbs_pow,Int.natAbs_natCast,Int.natAbs_mul] using congrArg Int.natAbs ex
  have yy : y^2=B*(n^2-3*m^2).natAbs := by
    have e : (n^2-3*m^2).natAbs=(3*m^2-n^2).natAbs := by rw [←neg_sub (3*m^2) (n^2),Int.natAbs_neg]
    simpa only [B,e,Int.natAbs_pow,Int.natAbs_natCast,Int.natAbs_mul] using congrArg Int.natAbs ey
  have ap : 0<A := by
    by_contra! h
    have ha : A=0 := by omega
    simp [ha] at xx
    omega
  have bp : 0<B := by
    by_contra! h
    have hn : B=0 := by omega
    simp [hn] at yy
    omega
  have cp := coordinates_coprime hc ex ey
  obtain ⟨u,hu⟩ := square_class ap xx.symm (coefficient cp)
  obtain ⟨v,hv⟩ := square_class bp yy.symm (coefficient cp.symm)
  have pos {M t : ℕ} (h : M=t^2 ∨ M=3*t^2) (hM : 0<M) : 0<t := by
    by_contra! small
    have z : t=0 := by omega
    simp [z] at h
    omega
  have up := pos hu ap
  have vp := pos hv bp
  have repr {M t : ℕ} (h : M=t^2 ∨ M=3*t^2) :
      ∃ s : ℕ, (s=1 ∨ s=3) ∧ M=s*t^2 := by
    rcases h with e|e
    · exact ⟨1,Or.inl rfl,by simpa using e⟩
    · exact ⟨3,Or.inr rfl,e⟩
  obtain ⟨s,ss,es⟩ := repr hu
  obtain ⟨t,tt,et⟩ := repr hv
  rw [←absSquare m,←absSquare n] at xx yy
  rcases le_total A B with le|le
  · have e := smaller_square le xx
    rw [es,et] at e le
    exact small_magnitude up vp ss tt (by rwa [←es,←et]) le e
  · have e := smaller_square le yy
    rw [es,et] at e le
    exact small_magnitude vp up tt ss (by rw [←es,←et]; exact cp.symm) le e

/-- Lucas's theorem. A sum of two coprime positive fourth powers cannot be a cube. -/
theorem lucas_no_cubes {b x y : ℕ} (hx : 0<x) (hy : 0<y)
    (hc : x.Coprime y) (he : x^4+y^4=b^3) : False := by
  rcases Nat.even_or_odd b with even|odd
  · have h2 : 2 ∣ b := even_iff_two_dvd.mp even
    have d4 : 4 ∣ b^3 := (pow_dvd_pow_of_dvd h2 2).trans (pow_dvd_pow b (by decide : 2≤3))
    exact not_four hc (he ▸ d4)
  · exact cube_excluded_odd odd hx hy hc he

/-- The specialization used in the original bounded census. -/
theorem bounded_lucas {b x y : ℕ} (_hb : b≤1456256357804) (hx : 0<x) (hy : 0<y)
    (hc : x.Coprime y) (he : x^4+y^4=b^3) : False :=
  lucas_no_cubes hx hy hc he

/-- There is just one Gaussian cubic chart for cofactor 17 if the two square
coordinates may be interchanged. Its signed parameters have norm b. -/
theorem gaussian_seventeen {b x y : ℕ} (hb : Odd b) (hc : x.Coprime y)
    (he : x^4+y^4=b^3*17^2) :
    ∃ m n X Y : ℤ, m^2+n^2=(b:ℤ) ∧
      ((X=(x:ℤ) ∧ Y=(y:ℤ)) ∨ (X=(y:ℤ) ∧ Y=(x:ℤ))) ∧
      X^2= -15*(m^3-3*m*n^2)-8*(3*m^2*n-n^3) ∧
      Y^2= 8*(m^3-3*m*n^2)-15*(3*m^2*n-n^3) := by
  obtain ⟨⟨m,n⟩,⟨e,f⟩,fac,bn,wn⟩ := powerful_descent hb (by decide : 0<17) hc he
  have ex := congrArg Zsqrtd.re fac
  have ey := congrArg Zsqrtd.im fac
  simp [pow_succ] at ex ey
  have norm : m^2+n^2=(b:ℤ) := by simpa [Zsqrtd.norm,pow_two] using bn
  have qr : e^2+f^2=17 := by simpa [Zsqrtd.norm,pow_two] using wn
  have lim {c d : ℤ} (eq : c^2+d^2=17) : -4≤c ∧ c≤4 := by
    constructor
    · by_contra! h
      nlinarith [sq_nonneg d,mul_nonneg (show 0≤ -c-5 by omega) (show 0≤ -c+5 by omega)]
    · by_contra! h
      nlinarith [sq_nonneg d,mul_nonneg (show 0≤c-5 by omega) (show 0≤c+5 by omega)]
  have ec := lim qr
  have fc := lim (by rw [add_comm]; exact qr : f^2+e^2=17)
  have cases : (e=-4 ∧ f=-1) ∨ (e=-4 ∧ f=1) ∨ (e=-1 ∧ f=-4) ∨ (e=-1 ∧ f=4) ∨ (e=1 ∧ f=-4) ∨ (e=1 ∧ f=4) ∨ (e=4 ∧ f=-1) ∨ (e=4 ∧ f=1) := by
    obtain ⟨_,_⟩ := ec
    obtain ⟨_,_⟩ := fc
    interval_cases e <;> interval_cases f <;> norm_num at *
  rcases cases with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · refine ⟨n,m,y,x,by linear_combination norm,Or.inr ⟨rfl,rfl⟩,?_,?_⟩
    · linear_combination ey
    · linear_combination ex
  · refine ⟨(-m),(-n),x,y,by linear_combination norm,Or.inl ⟨rfl,rfl⟩,?_,?_⟩
    · linear_combination ex
    · linear_combination ey
  · refine ⟨m,n,x,y,by linear_combination norm,Or.inl ⟨rfl,rfl⟩,?_,?_⟩
    · linear_combination ex
    · linear_combination ey
  · refine ⟨(-n),(-m),y,x,by linear_combination norm,Or.inr ⟨rfl,rfl⟩,?_,?_⟩
    · linear_combination ey
    · linear_combination ex
  · refine ⟨(-n),(-m),y,x,by linear_combination norm,Or.inr ⟨rfl,rfl⟩,?_,?_⟩
    · linear_combination ey
    · linear_combination ex
  · refine ⟨m,n,x,y,by linear_combination norm,Or.inl ⟨rfl,rfl⟩,?_,?_⟩
    · linear_combination ex
    · linear_combination ey
  · refine ⟨(-m),(-n),x,y,by linear_combination norm,Or.inl ⟨rfl,rfl⟩,?_,?_⟩
    · linear_combination ex
    · linear_combination ey
  · refine ⟨n,m,y,x,by linear_combination norm,Or.inr ⟨rfl,rfl⟩,?_,?_⟩
    · linear_combination ey
    · linear_combination ex

set_option maxRecDepth 20000 in
/-- A primitive point on the cubic chart lies in eight signed lattice classes
modulo 48, and its norm lies in six classes modulo 3120. -/
private theorem chart_residues {b : ℕ} {m n X Y : ℤ} (odd : b%2=1)
    (d3 : b%3≠0) (d5 : b%5≠0) (d13 : b%13≠0) (bn : m^2+n^2=(b:ℤ))
    (ex : X^2= -15*(m^3-3*m*n^2)-8*(3*m^2*n-n^3))
    (ey : Y^2=8*(m^3-3*m*n^2)-15*(3*m^2*n-n^3)) :
    b%3120 ∈ [17,257,1169,1889,2129,2417] ∧
      (m%48,n%48) ∈ [(8,23),(8,47),(17,8),(17,20),(41,8),(41,20),(44,23),(44,47)] := by
  let chart (p : ℕ) (a c : ZMod p) : Prop :=
    (∃ X : ZMod p, X^2=-15*(a^3-3*a*c^2)-8*(3*a^2*c-c^3)) ∧
    (∃ Y : ZMod p, Y^2=8*(a^3-3*a*c^2)-15*(3*a^2*c-c^3))
  have point (p : ℕ) : chart p m n := by
    refine ⟨⟨(X : ZMod p),?_⟩,⟨(Y : ZMod p),?_⟩⟩
    · simpa using congrArg (fun z : ℤ => (z : ZMod p)) ex
    · simpa using congrArg (fun z : ℤ => (z : ZMod p)) ey
  have hn (p : ℕ) : (m : ZMod p)^2+(n : ZMod p)^2=(b : ZMod p) := by
    simpa using congrArg (fun z : ℤ => (z : ZMod p)) bn
  have t16 : ∀ a c : ZMod 16, chart 16 a c → (a^2+c^2).val%2=1 →
      (a^2+c^2).val=1 ∧ ((a.val:ℤ),(c.val:ℤ)) ∈ [(1,4),(1,8),(8,7),(8,15),(9,4),(9,8),(12,7),(12,15)] := by
    unfold chart
    decide +kernel
  have s16 := t16 _ _ (point 16)
  simp only [hn,ZMod.val_natCast,ZMod.val_intCast] at s16
  obtain ⟨b16,m16⟩ := s16 (by omega)
  have t9 : ∀ a c : ZMod 9, chart 9 a c → (a^2+c^2).val%3≠0 →
      (a^2+c^2).val%3=2 ∧ (a.val:ℤ)%3=2 ∧ (c.val:ℤ)%3=2 := by
    unfold chart
    decide +kernel
  have s9 := t9 _ _ (point 9)
  simp only [hn,ZMod.val_natCast,ZMod.val_intCast] at s9
  obtain ⟨b3,m3,n3⟩ := s9 (by omega)
  have t5 : ∀ a c : ZMod 5, chart 5 a c → (a^2+c^2).val≠0 →
      (a^2+c^2).val ∈ [2,4] := by
    unfold chart
    decide +kernel
  have s5 := t5 _ _ (point 5)
  simp only [hn,ZMod.val_natCast] at s5
  have b5 := s5 d5
  have t13 : ∀ a c : ZMod 13, chart 13 a c → (a^2+c^2).val≠0 →
      (a^2+c^2).val ∈ [4,10,12] := by
    unfold chart
    decide +kernel
  have s13 := t13 _ _ (point 13)
  simp only [hn,ZMod.val_natCast] at s13
  have b13 := s13 d13
  constructor
  · have all : ∀ i : Fin 3120, i.val%16=1 → i.val%3=2 →
        i.val%5 ∈ [2,4] → i.val%13 ∈ [4,10,12] → i.val ∈ [17,257,1169,1889,2129,2417] := by decide +kernel
    apply all ⟨b%3120,Nat.mod_lt _ (by decide)⟩ <;>
      simp only [Nat.mod_mod_of_dvd _ (by decide : 16∣3120),
        Nat.mod_mod_of_dvd _ (by decide : 3∣3120),Nat.mod_mod_of_dvd _ (by decide : 5∣3120),
        Nat.mod_mod_of_dvd _ (by decide : 13∣3120)]
    · exact b16
    · omega
    · exact b5
    · exact b13
  · have tab : ∀ a c : Fin 48, a.val%3=2 → c.val%3=2 →
        (((a.val:ℤ)%16),((c.val:ℤ)%16)) ∈ [(1,4),(1,8),(8,7),(8,15),(9,4),(9,8),(12,7),(12,15)] →
        ((a.val:ℤ),(c.val:ℤ)) ∈ [(8,23),(8,47),(17,8),(17,20),(41,8),(41,20),(44,23),(44,47)] := by decide +kernel
    have lift (t : ℤ) : ((t%48).toNat:ℤ)=t%48 := Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))
    have take (t : ℤ) : (t%48).toNat < 48 := by have := lift t; omega
    have h := tab ⟨_,take m⟩ ⟨_,take n⟩
    simp only [lift] at h
    apply h
    · have := lift m; omega
    · have := lift n; omega
    · simpa only [Nat.cast_ofNat,Int.emod_emod_of_dvd _ (by decide : (16:ℤ)∣48)] using m16

/-- Doubling a bit pattern preserves every residue from the first period. -/
private theorem extend_bits (p : ℕ) (seed : ℕ) (k i : ℕ) (hi : i<p*2^k)
    (hit : seed.testBit (i%p)=true) :
    (Nat.rec (motive:=fun _ => ℕ) seed (fun k w => w ||| (w <<< (p*2^k))) k).testBit i=true := by
  induction k generalizing i with
  | zero => simpa [Nat.mod_eq_of_lt (by simpa using hi : i<p)] using hit
  | succ k ih =>
    simp only [Nat.testBit_or,Bool.or_eq_true]
    by_cases h : i<p*2^k
    · exact Or.inl (ih i h hit)
    · right
      rw [Nat.testBit_shiftLeft,Bool.and_eq_true]
      refine ⟨by simp;omega,ih _ ?_ ?_⟩
      · have eq : p*2^(k+1)=p*2^k+p*2^k := by ring
        omega
      · have eq : (i-p*2^k)%p=i%p := by
          calc (i-p*2^k)%p = (i-p*2^k+p*2^k)%p := (Nat.add_mul_mod_self_left _ _ _).symm
               _ = i%p := by rw [Nat.sub_add_cancel (by omega)]
        rwa [eq]

/-- Pack one full row period. The bit index is width times row plus column. -/
private theorem period_bit (w : ℕ) (f : ℕ → ℕ) (n i j : ℕ) (hi : i<n) (hj : j<w)
    (h : (f i).testBit j=true) :
    (Nat.rec (motive:=fun _ => ℕ) 0 (fun r v => v ||| (((f r) &&& ((1<<<w)-1)) <<< (w*r))) n).testBit
      (w*i+j)=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [Nat.testBit_or,Bool.or_eq_true]
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ hi) with lt|rfl
    · exact Or.inl (ih lt)
    · right
      have clip : ((1<<<w)-1).testBit j=true := by
        simpa only [Nat.shiftLeft_eq,one_mul,Nat.testBit_two_pow_sub_one] using decide_eq_true hj
      rw [Nat.testBit_shiftLeft,Bool.and_eq_true]
      exact ⟨decide_eq_true (by omega),by rw [show w*i+j-w*i=j by omega,Nat.testBit_and,h,clip];rfl⟩

private theorem sheet_bit (w p k : ℕ) (f : ℕ → ℕ) (i j : ℕ) (hi : i<p*2^k) (hj : j<w)
    (h : (f (i%p)).testBit j=true) :
    let base := Nat.rec (motive:=fun _ => ℕ) 0 (fun r v => v ||| (((f r) &&& ((1<<<w)-1)) <<< (w*r))) p
    (Nat.rec (motive:=fun _ => ℕ) base (fun h v => v ||| (v <<< ((w*p)*2^h))) k).testBit (w*i+j)=true := by
  intro base
  have hp : 0<p := by by_contra! e; simp [show p=0 by omega] at hi
  have bound (t N : ℕ) (lt : t<N) : w*t+j<w*N := calc
    w*t+j < w*t+w := Nat.add_lt_add_left hj _
    _ = w*(t+1) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ lt
  have eq : (w*i+j)%(w*p)=w*(i%p)+j := by
    have de : w*i+j = (w*(i%p)+j)+(w*p)*(i/p) := by
      calc w*i+j = w*(i%p+p*(i/p))+j := by rw [Nat.mod_add_div]
           _ = _ := by ring
    rw [de,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (bound _ _ (Nat.mod_lt _ hp))]
  apply extend_bits
  · simpa only [Nat.mul_assoc] using bound _ _ hi
  · rw [eq]; exact period_bit w f p _ j (Nat.mod_lt _ hp) hj h

/-- Check the two cubics modulo each prime. The rectangular certificate intersects
periodic masks in strips of 256 rows and requires each intersection to be zero. -/
private theorem grid_sieve (width origin height : ℕ) (classes : List (ℤ × ℤ))
    (gates : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)) :
    let F (m n : ℤ) := -15*(m^3-3*m*n^2)-8*(3*m^2*n-n^3)
    let G (m n : ℤ) := 8*(m^3-3*m*n^2)-15*(3*m^2*n-n^3)
    let res (a : ℤ) (p : ℕ) := (a%(p:ℤ)).toNat
    let seed (code p i : ℕ) := (code >>> (p*i)) &&& ((1 <<< p)-1)
    let valid (g : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
      let (p,inv,k,v,sq,code) := g
      decide (1<p ∧ width+p≤p*2^k ∧ height+p≤p*2^v ∧ (48*inv)%p=1) &&
      (List.range p).all (fun z => sq.testBit (z^2%p)) &&
      (List.range p).all (fun i => (List.range p).all (fun j =>
        let a := res (F i (48*(j:ℤ))) p
        let b := res (G i (48*(j:ℤ))) p
        !(decide (a≠0 ∨ b≠0) && sq.testBit a && sq.testBit b) || (seed code p i).testBit j))
    let sheets (c : ℤ × ℤ) := gates.map (fun g =>
      let (p,inv,k,v,_,code) := g
      let wave (i : ℕ) :=
        let s := seed code p (res (48*(i:ℤ)+c.1-origin) p)
        (Nat.rec (motive:=fun _ => ℕ) s (fun h t => t ||| (t <<< (p*2^h))) k) >>> res ((c.2-origin)*inv) p
      let base := Nat.rec (motive:=fun _ => ℕ) 0 (fun r t => t ||| ((wave r &&& ((1<<<width)-1)) <<< (width*r))) p
      (p,Nat.rec (motive:=fun _ => ℕ) base (fun h t => t ||| (t <<< ((width*p)*2^h))) v))
    let plane (c : ℤ × ℤ) (lo : ℕ) := (sheets c).foldl (fun bits g =>
      bits &&& (g.2 >>> (width*(lo%g.1)))) ((1 <<< (width*height))-1)
    0<height → gates.all valid=true →
    (∀ c ∈ classes, (List.range (width/height+1)).all (fun t => plane c (height*t) == 0)=true) →
    ∀ m n X Y : ℤ, X.natAbs.Coprime Y.natAbs →
    X^2=F m n → Y^2=G m n → ∀ c ∈ classes, ∀ i j : ℕ, i<width → j<width →
    m=48*(i:ℤ)+c.1-origin → n=48*(j:ℤ)+c.2-origin → False := by
  intro F G res seed valid sheets plane tall good empty m n X Y cop ex ey c cm i j hi hj me ne
  have reduced (a : ℤ) {p : ℕ} (hp : 0<p) : (res a p : ℤ)=a%(p:ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hp.ne'))
  have small (a : ℤ) {p : ℕ} (hp : 0<p) : res a p<p := by
    have := reduced a hp
    have := Int.emod_lt_of_pos a (by exact_mod_cast hp : (0:ℤ)<p)
    omega
  have congr (a : ℤ) {p : ℕ} (hp : 0<p) : (res a p : ℤ) ≡ a [ZMOD (p:ℤ)] := by
    rw [reduced a hp]; exact Int.mod_modEq _ _
  let lo := height*(i/height)
  let r := i%height
  have split : r+lo=i := Nat.mod_add_div _ _
  have rh : r<height := Nat.mod_lt _ tall
  have hit : ∀ g ∈ sheets c, (g.2 >>> (width*(lo%g.1))).testBit (width*r+j)=true := by
    intro g member
    obtain ⟨⟨p,inv,k,v,sq,code⟩,mem,rfl⟩ := List.mem_map.mp member
    have test := List.all_eq_true.mp good _ mem
    change (decide (1<p ∧ width+p≤p*2^k ∧ height+p≤p*2^v ∧ (48*inv)%p=1) && _ && _)=true at test
    simp only [Bool.and_eq_true,decide_eq_true_eq] at test
    obtain ⟨⟨⟨pp,cover,vcover,inverse⟩,quadratic⟩,table⟩ := test
    have hp : 0<p := by omega
    let off := res ((c.2-origin)*inv) p
    let col := (j+off)%p
    have shift : (48:ℤ)*(inv:ℤ) ≡ 1 [ZMOD (p:ℤ)] :=
      Int.natCast_modEq_iff.mpr (show 48*inv ≡ 1 [MOD p] from inverse.trans (Nat.mod_eq_of_lt pp).symm)
    have left : (res m p : ℤ) ≡ m [ZMOD (p:ℤ)] := congr _ hp
    have right : 48*(col:ℤ) ≡ n [ZMOD (p:ℤ)] := by
      have base : (col:ℤ) ≡ (j:ℤ)+(off:ℤ) [ZMOD (p:ℤ)] :=
        Int.natCast_modEq_iff.mpr (Nat.mod_modEq _ _)
      have s := (congr ((c.2-origin)*inv) hp).mul_left 48
      have t := shift.mul_left (c.2-origin)
      have o : (48:ℤ)*off ≡ c.2-origin [ZMOD (p:ℤ)] := by
        calc (48:ℤ)*off ≡ 48*((c.2-origin)*inv) [ZMOD (p:ℤ)] := s
             _ = (c.2-origin)*(48*inv) := by ring
             _ ≡ (c.2-origin)*1 [ZMOD (p:ℤ)] := t
             _ = c.2-origin := by ring
      calc (48:ℤ)*col ≡ 48*((j:ℤ)+off) [ZMOD (p:ℤ)] := base.mul_left 48
           _ = 48*(j:ℤ)+48*off := by ring
           _ ≡ 48*(j:ℤ)+(c.2-origin) [ZMOD (p:ℤ)] := o.add_left _
           _ = n := by rw [ne];ring
    have u := (left.pow 3).sub (((left.mul (right.pow 2)).mul_left 3))
    have vcong := (((left.pow 2).mul right).mul_left 3).sub (right.pow 3)
    have f : F (res m p) (48*(col:ℤ)) ≡ F m n [ZMOD (p:ℤ)] := by
      dsimp only [F]; convert (u.mul_left (-15)).sub (vcong.mul_left 8) using 1 <;> ring
    have g' : G (res m p) (48*(col:ℤ)) ≡ G m n [ZMOD (p:ℤ)] := by
      dsimp only [G]; convert (u.mul_left 8).sub (vcong.mul_left 15) using 1 <;> ring
    have sqhit (Z : ℤ) {a : ℤ} (he : a ≡ Z^2 [ZMOD (p:ℤ)]) : sq.testBit (res a p)=true := by
      have h := List.all_eq_true.mp quadratic (res Z p) (List.mem_range.mpr (small Z hp))
      have eq : (res Z p)^2%p=res a p := by
        have w := ((congr Z hp).pow 2).trans he.symm
        dsimp only [Int.ModEq] at w
        apply Int.natCast_inj.mp
        simpa only [Int.natCast_mod,Nat.cast_pow,reduced a hp] using w
      simpa only [eq] using h
    rw [←ex] at f
    rw [←ey] at g'
    have nonzero : res (F (res m p) (48*(col:ℤ))) p≠0 ∨
        res (G (res m p) (48*(col:ℤ))) p≠0 := by
      by_contra! h
      have div {a Z : ℤ} (hz : res a p=0) (e : a ≡ Z^2 [ZMOD (p:ℤ)]) : p∣Z.natAbs^2 := by
        have z : a%(p:ℤ)=0 := by rw [←reduced a hp,hz];rfl
        have d : (p:ℤ) ∣ Z^2 := Int.dvd_of_emod_eq_zero (Eq.trans (show Z^2%(p:ℤ)=a%(p:ℤ) from e.symm) z)
        have dn := Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr d)
        simpa only [Int.natAbs_pow] using dn
      exact (Nat.not_coprime_of_dvd_of_dvd pp (div h.1 f) (div h.2 g')) ((cop.pow_left 2).pow_right 2)
    have cell := List.all_eq_true.mp (List.all_eq_true.mp table _ (List.mem_range.mpr (small m hp)))
      col (List.mem_range.mpr (Nat.mod_lt _ hp))
    change (!(decide (_≠0 ∨ _≠0) && sq.testBit _ && sq.testBit _) || (seed code p (res m p)).testBit col)=true at cell
    simp only [nonzero,decide_true,sqhit X f,sqhit Y g',Bool.true_and,Bool.not_true,Bool.false_or] at cell
    let wave (t : ℕ) := (Nat.rec (motive:=fun _ => ℕ) (seed code p (res (48*(t:ℤ)+c.1-origin) p))
      (fun h w => w ||| (w <<< (p*2^h))) k) >>> off
    have index : (lo%p+r)%p=i%p := by rw [Nat.mod_add_mod, Nat.add_comm lo r,split]
    have hitrow : (wave ((lo%p+r)%p)).testBit j=true := by
      have cong : (48:ℤ)*(i%p:ℕ)+c.1-origin ≡ m [ZMOD (p:ℤ)] := by
        rw [me]
        exact (((Int.natCast_modEq_iff.mpr (Nat.mod_modEq i p)).mul_left 48).add_right c.1).sub_right _
      have same : res (48*(i%p:ℕ)+c.1-origin) p=res m p := congrArg Int.toNat cong
      dsimp only [wave]
      rw [index,same,Nat.testBit_shiftRight]
      apply extend_bits
      · have := small ((c.2-origin)*inv) hp
        dsimp only [off];omega
      · simpa only [col,Nat.add_comm] using cell
    have lim : lo%p+r < p*2^v := by have := Nat.mod_lt lo hp;omega
    have b := sheet_bit width p v wave (lo%p+r) j lim hj hitrow
    rw [Nat.testBit_shiftRight,show width*(lo%p)+(width*r+j)=width*(lo%p+r)+j by ring]
    exact b
  have all (gs : List (ℕ × ℕ)) (v : ℕ) (hv : v.testBit (width*r+j)=true)
      (h : ∀ g ∈ gs, (g.2 >>> (width*(lo%g.1))).testBit (width*r+j)=true) :
      (gs.foldl (fun bits g => bits &&& (g.2 >>> (width*(lo%g.1)))) v).testBit (width*r+j)=true := by
    induction gs generalizing v with
    | nil => exact hv
    | cons g gs ih =>
      apply ih
      · simp only [Nat.testBit_and,hv,h _ List.mem_cons_self,Bool.true_and]
      · exact fun g hg => h g (List.mem_cons_of_mem _ hg)
  have pos : width*r+j<width*height := calc
    width*r+j < width*r+width := Nat.add_lt_add_left hj _
    _ = width*(r+1) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ rh
  have alive : (plane c lo).testBit (width*r+j)=true := all _ _
    (by simpa only [Nat.shiftLeft_eq,one_mul,Nat.testBit_two_pow_sub_one] using decide_eq_true pos) hit
  have cleared := List.all_eq_true.mp (empty c cm) (i/height)
    (List.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hi.le)))
  rw [beq_iff_eq.mp cleared] at alive
  simp at alive

set_option maxRecDepth 16000 in
private theorem zero_seventeen_grid :
    ∀ m n X Y : ℤ, X.natAbs.Coprime Y.natAbs →
    X^2= -15*(m^3-3*m*n^2)-8*(3*m^2*n-n^3) →
    Y^2= 8*(m^3-3*m*n^2)-15*(3*m^2*n-n^3) →
    ∀ c ∈ ([(8,23),(8,47),(17,8),(17,20),(41,8),(41,20),(44,23),(44,47)] : List (ℤ × ℤ)), ∀ i j : ℕ, i<19556 → j<19556 →
    m=48*(i:ℤ)+c.1-469344 → n=48*(j:ℤ)+c.2-469344 → False := by
  let gates : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
    (5,2,12,6,0x13,0xc08592),
    (7,6,12,6,0x17,0x18a122450368),
    (11,3,11,5,0x23b,0x1254105433c39140800240063404000),
    (13,3,11,5,0x161b,0x1212000d028c300010008004002618a0500064249e4),
    (17,11,11,5,0x1a317,0x1a0b973a0c173a74162e74e82e5ce8105cf9d050b9d3a0b973a14173e74102e74e82e5ce8),
    (19,2,11,4,0x30af3,0x2581130241460440a1905220e804065408b0411809055804a018c030921108401e034900720930408888530af2),
    (23,12,10,4,0x5335f,0x166666b1e1e3707e0e5ab56900000ff003f02004199ce646d9b6100002810081557aa91cf38800c009000096b4b58020404b6db400240110002210008402100800000),
    (29,26,10,4,0x13d122f3,0x20201422e4142180451ad420048308000a2200440702000822830d04662404300a4020d9e84c00e70a21382016204004591c889c4d10410234000e42287380190bcd82012c06101213105861a20800207011002228000860900205ac5100c21413a614020213d122f2),
    (31,11,10,4,0x121d47b7,0x1268911818494e042380220196a104913b206400607400085802978c11c6481d38100310f4d0400c00120d81400152000a6484231caa00860400b5a09215161404005d1054280866301c9805d1048048810c0d20028a4030881400198829508291a0a08204c12821018262701419024044840142280000000),
    (37,27,10,3,0x165e211e9b,0xe4233131c406004e00c27e05690a35c423e801520812019600000c8c0faa51c088c1001113f080c0cba22929c96c3949870a52c9a98512401121023134040020cc02144100ee9a045951814100803201948800800894c02600804140e54d102cba80411420198200101646204244032450cac9a52870c94e1b49ca4a22e9818087c44400418981c52af81098000034c0240825420be211d6284b503f210039003015c646621389a1dee164),
    (41,6,9,3,0x1b382b50737,0xa011a8203031020042d1481280199a014842298084283b22000410a0e1b2028289b102220264b0042018028008f4860310015149c47083002e00e29300188248125c03908112125041ac82485380010d061005400a0d660050202b9815010b506110050089c0d81c880500443056840540cea02050033582801500430584000e509209ac10524244084e01d2409208c0064a3803a00608711c94540046030978800a00c0210069320222046c8a0a026c382841000226e0a1080ca2109402ccc00a40945a100204606020ac40280000000000),
    (43,26,9,3,0x35883a3ee53,0x1b01400687442214a0040905200c8414011a3b46040300004085d225c40841298a26420240100008182092c8d2884263069944710005c15a0a040970060301409847102d808a5213200db10806169a2c11c201cc8198248818150b2d080a0011151e08052200032206002840e20c513001c44640204217210110524738610331c02042c4b1c0640108103d40788248008000180412c11006010524840181003c41004a09835125208204202a81822a20081000311d400114542450b030d0a21581474022043108000817816b4e4910240400581049120ba023b008b45500c29080c000000000000),
    (47,1,9,3,0x4351b2753df,0xc600601402200509c00021041026404a00c0000110241c50694914244481009220414202008320430d080020800a8140e602100009188164918488b8c9080195242010800c904112c0502a5c682040802c00863110858a351204000222402060106006803108054140648411f0100ba4921c0e00920811000ec0400604540f0c99094053722212410042821800140c090a2001881032658ac42504000424034400628100ba882012405c0601ca52303a5022d0950c111010602120920300e897104800e00140a20805544637010088d01884001000128c808be9040900123c162083031c9443a410421d28005400fa9c4006a290108005244a9804598003e803831a10e808ca10b438ac3120211800000000000),
    (53,21,9,3,0x12dd703303aed3,0x51aa2e9084130218180022200c00080aa180810881c06092ec8580202e000824148a06664f0428422e06561300ca000c9000562010a20138619d130a10c64d4488347cc0642240429a000110a0808698860b608850782d480881800002018161d512e130070018b176504442bcc2181640004a070840243201012400421200a088942020011640404800a008849210a004005a800c0010410c931f8408a10888397c12e810080a400070200a28020700012808040ba41f4e0888428810fc64984104001800ad00100284249088028009010134400202148882802421001240402612010870290001340c219ea1110537468c00700643a455c340c0200000c088095a0f05088368308cb080828440002ca1012213019f16089159318428645cc30e40228402350004980029806435303a210a1079333028941208003a0200d09ba48301c0884080c2a80800180222000c0c20641084ba2ac500000000000000),
    (59,16,9,3,0x22b62183e7b92bb,0x1728e12f8000102c204a0400a26980184d12cf0024a09d8113081090a8ba916739420228884203a0804c030c00518142c5302ac9a0a016240805004073301e6a410817041483400084030703100001440cce4138208188358b450058488a0080282204a018011886b038a10cc0c9013961b80420e3202e701d0902888684010a4000b9328060445a0229d64058bc01a8812d1806200471a32b0885c48a41120a286c78000986c21a8800a2c014628000111048b158081d85448168c58bc430208000d6d0ad10d4302069692641b08a1006487c003c6d49084870001042600c4b0204040a445212080c9010820100590000990918200085840e0432480e22d4180b0552cc042511489b82282810342215000154402604082903940061180100141902800100882f07500816143588a683044084889800240512200448046a000911224062114c2998805293204887458404b1a308006806d4002c2099b20346a00520a1185c1d859010c469c030005402100ac81c9812085355010c298504080149449831c10052e040240308030c90010a0ce1808c0012104e2090a0101dc412054044151c5ac03081200820000000000000000),
    (61,14,9,3,0x1713e6940a59f23b,0x1180c8285a2c7254158fc90b071c66119117240a275431163b05600b0b1245130b015f014261c4079417323692d66633673c8194548398862c17f0005f53538510143505d016b4b34e8d5a0126360b2f966480e1038fc00d22951215b5bd0043512040a8baf0222a60188a51030ab5b220d9020407c1b0ce414700688d9a7f00cd1c16289607bb15172068cd38c2dc20421db006204492b2c8de15a58d50984a420e1a6c64184a2561b83ca9c1520c399681202396dfe1051524f230b584100630a28b1d33f91710f04110fb840505ca06ca916c98d4a02322ad7c455d81178e86994446ab6ab1114cb0b8f440dd511f5aa26202958c9b44a9b029d05010ef84410784744fe65c68a286300410d6862792545043fdb4e20240b4ce182541ca9e0ec352290c131b2c3821290c8558d2d43d89a6a491023006dc21021da18e598b0274546ef0348a341c59807f2cd88b0071413986c1f010204d8226d6a86045288c032a2207ae8a81024561005ed6d42454a25801f8e043809334fa683632402d58b96696b405d056140450e5657d0007f41a308ce09514c09e73663335a4b6267414f011c321407d4068645124686803506e3446157228127444c4331c706849f8d415271a2d0a0980c4000000000000000),
    (67,7,9,3,0x359c281ba27ebc653,0x42200401286862ccd001300510b41490410900c5c0024501122250428324436002ad34080805850008626429808030c4022ca10409610a50c8010cb00240640480b0041c20085441003398c002206f01260b310c130680380411428020188001e09ca00605098e20200828310004a010018368314d8922082828360c5032c104090c10124e86c15801000053c215d000581411484a0a1100620939100e87010d1450031c1422000002864339008d014cac00071421310c09b18152802028344c11885502104e032503c360107284c00020c68c0001102533252940000918132116a0034840948c0030c405412e00cad000212502613090028612012019800d92008221251a03a11400408820a2210802ad330014408a42081335400446018e82182100344306201b3600a3808228046206804a69048c494000151581082a2282212800ce3800ba022402e80ce98002402068548d048110040cc518001e0620050a00000c87a0804ab828001603100c8805408806702143001028c04140023016a201747828c04a08201e41000040047700c891b0ac28004035024002848d0a0f500802500038c00083441608981228412011484120510482902308c22a20005865614022828c0805064290785442208074254360220a048004003341b60cc400401008d31811c804401a29124249426900306d0c41022835301422030c01002ca0e280542468008310208361022881268121162a0290042b8282980a00ca40984103002009331614100000000000000000),
    (71,37,9,3,0x1164729716b1d977f,0x4104024881346100001083881a008410404407210150004080482001204805c048014c12624082000950006010001d042100093102001b431ac11041d0a0a80009240010c82810408a0849018081022104348c9000400e000020842360469468a48180000021d38090060904070910b90609c10080814d10ad816650140c048008052100a244408028204324108048205d4090262801b810a0406400c0124307100a00600420140441001805106a5041000109045b16098c2809080e20c81a24271c20014214e41223a83220a9c2a0002080000e0030202806660000203063a0900a1520e901800e0100e0020a9022002268a0408b1a59810810ba040000211441211008d2009040220248c0280818d01516541018128248008460041483e0802a2074188890420e02315110a2e68922100890a050a96001284400920816900140000826311c0808150902004488001c0803138008c0594949c00b22088148009101004854186c80218a68220120e12812314521902082040d62200310024208560e80f84201503040400340082062820312a62112d61201010c15e54186a410404461500444002a0004300c138502108004020f00040004420016928622801088004c76e09c87442a618000e41a5028c0e6104040c180025422218002560011828222815008d998202684b648e4a0108049025410000238014040010245c48818008020c09c00127b922484218108004253040219580a025c200400aeb068d0008cc08a48890995802aa50001c0d421000160090e40041848a01794808604d4222312400fdc00e02022887c008817003018e2c18890848076022e1a60a1042c0e007044b4c063040c812220ca01164729716b1d977e)]
  apply grid_sieve 19556 469344 256 [(8,23),(8,47),(17,8),(17,20),(41,8),(41,20),(44,23),(44,47)] gates (by decide)
  · simp only [gates,List.all_cons,List.all_nil,Bool.and_eq_true]
    repeat' apply And.intro
    all_goals decide +kernel
  · intro c hc
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel


/-- The entire cofactor-17 range below the census cutoff is impossible. -/
theorem no_cofactor_seventeen {b x y : ℕ} (bound : b≤220261480241)
    (cop : x.Coprime y) (he : x^4+y^4=b^3*17^2) : False := by
  have odd : Odd b := by
    rcases Nat.even_or_odd b with h|h
    · have d := even_iff_two_dvd.mp h
      have q : 4∣b^3 := (pow_dvd_pow_of_dvd d 2).trans (pow_dvd_pow b (by decide : 2≤3))
      exact (not_four cop (he ▸ dvd_mul_of_dvd_left q _)).elim
    · exact h
  have unit (p : ℕ) (hp : p.Prime) (two : p≠2) (bad : p%8≠1) : b%p≠0 := by
    intro h
    have d := dvd_pow (Nat.dvd_of_mod_eq_zero h) (by decide : 3≠0)
    exact bad (prime_residue cop hp two (he ▸ dvd_mul_of_dvd_left d _))
  obtain ⟨m,n,X,Y,bn,orient,ex,ey⟩ := gaussian_seventeen odd cop he
  have xy : X.natAbs.Coprime Y.natAbs := by
    rcases orient with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · simpa using cop
    · simpa using cop.symm
  obtain ⟨_,hit⟩ := chart_residues (Nat.odd_iff.mp odd)
    (unit 3 (by decide) (by decide) (by decide)) (unit 5 (by decide) (by decide) (by decide))
    (unit 13 (by decide) (by decide) (by decide)) bn ex ey
  have box {a c : ℤ} (hn : a^2+c^2=(b:ℤ)) :
      -469320≤a ∧ a≤469320 := by
    have bb : (b:ℤ)≤220261480241 := by exact_mod_cast bound
    constructor
    · by_contra! h
      nlinarith [sq_nonneg c,mul_nonneg (show 0≤ -a-469321 by omega) (show 0≤ -a+469321 by omega)]
    · by_contra! h
      nlinarith [sq_nonneg c,mul_nonneg (show 0≤a-469321 by omega) (show 0≤a+469321 by omega)]
  have index (a : ℤ) (h : -469320≤a ∧ a≤469320) :
      ∃ i : ℕ, i<19556 ∧ a=48*(i:ℤ)+a%48-469344 := by
    let i := ((a+469344)/48).toNat
    have e : (i:ℤ)=(a+469344)/48 := Int.toNat_of_nonneg (by omega)
    exact ⟨i,by omega,by omega⟩
  obtain ⟨i,hi,mi⟩ := index m (box bn)
  obtain ⟨j,hj,nj⟩ := index n (box (by rw [add_comm];exact bn : n^2+m^2=(b:ℤ)))
  exact zero_seventeen_grid m n X Y xy ex ey (m%48,n%48) hit i j hi hj mi nj

end Arithmetic

/-- Unconditional bounds on b and the cofactor k, independently of both
remaining census hypotheses. -/
theorem parameter_bounds {b z x y : ℕ} (bhi : b≤1456256357804)
    (hx : 0<x) (hy : 0<y) (hc : x.Coprime y) (hz : b∣z)
    (hsum : x^4+y^4=b*z^2) (hsmall : b*z^2<3088257489493360278725196965477359217) :
    ∃ k, z=b*k ∧ 17≤k ∧ (∀ p ∈ k.primeFactors, p%8=1) ∧ b≤220261480241 ∧
      (k ≠ 17 → 41≤k ∧ b≤122475323887) ∧ (k ≠ 17 → k ≠ 41 → b≤83372455837) := by
  obtain ⟨k,hk⟩ := hz
  have kp : 0<k := by
    by_contra! h
    have k0 : k=0 := by omega
    rw [hk,k0] at hsum
    simp at hsum
    omega
  have rewriteN : b*z^2=b^3*k^2 := by rw [hk];ring
  have eqn := hsum.trans rewriteN
  rw [rewriteN] at hsmall
  have kres (p : ℕ) (hp : p ∈ k.primeFactors) : p%8=1 := by
    obtain ⟨pr,dvd,_⟩ := Nat.mem_primeFactors.mp hp
    have pz : p ∣ z := hk ▸ dvd_mul_of_dvd_right dvd b
    have ps : p ∣ x^4+y^4 := hsum ▸ dvd_mul_of_dvd_right (dvd_pow pz (by decide : 2≠0)) b
    apply prime_residue hc pr _ ps
    rintro rfl
    have four : 2^2 ∣ z^2 := pow_dvd_pow_of_dvd pz 2
    exact not_four hc (hsum ▸ dvd_mul_of_dvd_right four b)
  have tiers : k=1 ∨ k=17 ∨ k=41 ∨ 73≤k := by
    by_cases h : k<73
    · have tab : ∀ i : Fin 73, (0 < (i : ℕ)) → (∀ p ∈ (i : ℕ).primeFactors, p % 8 = 1) →
          (i : ℕ) = 1 ∨ (i : ℕ) = 17 ∨ (i : ℕ) = 41 := by decide +kernel
      have small : k = 1 ∨ k = 17 ∨ k = 41 := tab ⟨k,h⟩ kp kres
      exact small.imp_right (fun h => h.imp_right Or.inl)
    · omega
  have notOne : k ≠ 1 := by
    intro k1
    exact bounded_lucas bhi hx hy hc (by simpa [k1] using eqn)
  have k17 : 17≤k := by omega
  have upper {B K : ℕ} (hK : K≤k) (cut : 3088257489493360278725196965477359217 ≤
      (B+1)^3*K^2) : b≤B := by
    by_contra! h
    have lower := Nat.mul_le_mul (Nat.pow_le_pow_left (show B+1≤b by omega) 3)
      (Nat.pow_le_pow_left hK 2)
    omega
  refine ⟨k,hk,k17,kres,upper k17 (by decide),?_,?_⟩
  · intro ne
    have k41 : 41≤k := by omega
    exact ⟨k41,upper k41 (by decide)⟩
  · intro no17 no41
    have k73 : 73≤k := by omega
    exact upper k73 (by decide)

/-- After the cofactor-17 certificate, 41 is the smallest remaining cofactor.
All higher cofactors give a second, stricter bound on b. -/
theorem parameter_bounds_after_seventeen {b z x y : ℕ} (bhi : b≤1456256357804)
    (hx : 0<x) (hy : 0<y) (hc : x.Coprime y) (hz : b∣z)
    (hsum : x^4+y^4=b*z^2) (hsmall : b*z^2<3088257489493360278725196965477359217) :
    ∃ k, z=b*k ∧ 41≤k ∧ (∀ p ∈ k.primeFactors, p%8=1) ∧ b≤122475323887 ∧
      (k≠41 → 73≤k ∧ b≤83372455837) := by
  obtain ⟨k,hk,_,kres,small,h41,h73⟩ := parameter_bounds bhi hx hy hc hz hsum hsmall
  have no17 : k≠17 := by
    rintro rfl
    apply no_cofactor_seventeen small hc
    rw [hsum,hk];ring
  obtain ⟨k41,upper⟩ := h41 no17
  refine ⟨k,hk,k41,kres,upper,fun d => ⟨?_,h73 no17 d⟩⟩
  by_contra! h
  have tab : ∀ i : Fin 73, (41 ≤ (i : ℕ)) →
      (∀ p ∈ (i : ℕ).primeFactors, p % 8 = 1) → (i : ℕ) = 41 := by decide +kernel
  exact d (tab ⟨k,h⟩ k41 kres)

theorem main : H1 → H2 → OMA.R_mo_191889_R1.H3 := by
  intro first rest b z x y blo bhi sq primes hz hx hxy hy hc he cut
  have zp : 0<z := by
    by_contra! h
    have e : z=0 := by omega
    simp [e] at he
    omega
  have strict : x<y := by
    by_contra! h
    have e : x=y := by omega
    have one : x=1 := by simpa [←e] using hc
    have two : 2=b*z^2 := by simpa [←e,one] using he
    have le : b≤b*z^2 := by simpa using Nat.mul_le_mul_left b (show 1≤z^2 from pow_pos zp _)
    omega
  obtain ⟨k,hk,_,kres,upper,h73⟩ :=
    parameter_bounds_after_seventeen bhi hx (hx.trans strict) hc hz he cut
  have tri := triangle_of_quartic (x := (x:ℚ)) (y := (y:ℚ)) (z := (z:ℚ)) (b := (b:ℚ))
    (by exact_mod_cast hx) (by exact_mod_cast strict) (by exact_mod_cast zp) (by exact_mod_cast he)
  have val : b*z^2=b^3*k^2 := by rw [hk];ring
  rw [val] at he cut
  by_cases d : k=41
  · subst k
    exact first b x y blo upper sq primes tri hx strict hy hc he cut
  · obtain ⟨k73,smaller⟩ := h73 d
    exact rest b k x y blo smaller sq primes k73 kres tri hx strict hy hc he cut

end OMA.R_mo_191889_R1_H3_R1
