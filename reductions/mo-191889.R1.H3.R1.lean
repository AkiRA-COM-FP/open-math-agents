import OMAReductions.R_mo_191889_R1
import Mathlib

/-!
# The large squarefree parameter in the powerful fourth-power census

Write the sum as b³k². Every prime of k is 1 modulo 8. We exclude k = 1
throughout the original range by factoring a primitive cube in the Gaussian
integers. The smaller coordinate leads either to the prime 3 obstruction
for sums of two squares or to Z² + 3u⁴ = v⁴ with u,v ≤ 1098. The latter
equation forces 10 ∣ u, and eleven tables of square residues exclude all
remaining pairs. Thus k is at least 17 and b is at most 220261480241.
The two remaining subproblems distinguish k = 17 from k ≥ 41. A rational
right triangle with area 2b is constructed directly in both cases.

The prime-order and parity arguments below are adapted from ZedingZhang’s parent
reduction in #8603. The cube theorem and congruent-number sieve are used by
Noam D. Elkies and Gaurav Goel, *On powerful integers expressible as sums of
two coprime fourth powers*, sections 2 and 4.
https://antsmath.org/ANTSXV/papers/ANTS-XV_elkies-goel.pdf
-/

namespace OMA.R_mo_191889_R1_H3_R1

/-- The cofactor 17 in the reduced large-parameter census. -/
def H1 : Prop :=
  ∀ b x y : ℕ, 10000 < b → b ≤ 220261480241 → Squarefree b →
    (∀ p ∈ b.primeFactors, p % 8 = 1) →
    (∃ a d c : ℚ, 0 < a ∧ 0 < d ∧ 0 < c ∧ a^2+d^2=c^2 ∧ a*d=4*(b:ℚ)) →
    0 < x → x < y → y ≤ 1325648472 → x.Coprime y →
    x^4+y^4=b^3*17^2 → b^3*17^2 < 3088257489493360278725196965477359217 → False

/-- All larger cofactors have a smaller parameter bound, with a separate
upper stratum in which only 41 is possible. -/
def H2 : Prop :=
  ∀ b k x y : ℕ, 10000 < b → b ≤ 122475323887 → Squarefree b →
    (∀ p ∈ b.primeFactors, p % 8 = 1) → 41 ≤ k →
    (∀ p ∈ k.primeFactors, p % 8 = 1) → (83372455837 < b → k=41) →
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

private theorem gaussian_cube {x y b : ℕ} (hc : x.Coprime y) (hodd : Odd b)
    (he : x^4+y^4=b^3) :
    ∃ m n : ℤ, (x:ℤ)^2=m*(m^2-3*n^2) ∧ (y:ℤ)^2=n*(3*m^2-n^2) ∧
      m^2+n^2=(b:ℤ) := by
  let a : GaussianInt := ⟨(x:ℤ)^2,(y:ℤ)^2⟩
  let c : GaussianInt := ⟨(x:ℤ)^2,-(y:ℤ)^2⟩
  let i : GaussianInt := ⟨0,1⟩
  have plus : a+c=2*(x:GaussianInt)^2 := by
    ext <;> simp [a,c,pow_two]
    ring
  have minus : (-i)*(a-c)=2*(y:GaussianInt)^2 := by
    ext <;> simp [a,c,i,pow_two]
    ring
  have prod : a*c=(b:GaussianInt)^3 := by
    rw [← Nat.cast_pow,← he,Zsqrtd.natCast_val]
    ext <;> simp [a,c] <;> ring
  have cps := ((hc.pow_left 2).pow_right 2).isCoprime.map (Int.castRingHom GaussianInt)
  have oddN : Nat.Coprime 2 (b^3) :=
    (Nat.coprime_two_left.mpr hodd).pow_right 3
  have cp2 := oddN.isCoprime.map (Int.castRingHom GaussianInt)
  simp only [Int.coe_castRingHom,Nat.cast_pow,Int.cast_pow,Int.cast_natCast,Nat.cast_ofNat,Int.cast_ofNat] at cps cp2
  have cp : IsCoprime a c := by
    apply IsRelPrime.isCoprime
    intro d da dc
    have dx := plus ▸ dvd_add da dc
    have dy := minus ▸ dvd_mul_of_dvd_right (dvd_sub da dc) (-i)
    have d2 : d ∣ 2 := by
      obtain ⟨j,k,eq⟩ := cps
      have dsum := dvd_add (dvd_mul_of_dvd_left dx j) (dvd_mul_of_dvd_left dy k)
      convert dsum using 1
      linear_combination -2*eq
    exact cp2.isRelPrime d2 (prod ▸ dvd_mul_of_dvd_left da c)
  obtain ⟨d,⟨u,hu⟩⟩ := exists_associated_pow_of_mul_eq_pow' cp prod
  let w := d*(u:GaussianInt)^3
  have w3 : w^3=a := by
    rw [← hu]; dsimp [w]; rw [mul_pow]
    have ue := gunit_fourth u
    calc d^3*((u:GaussianInt)^3)^3 = d^3*(((u:GaussianInt)^4)^2*(u:GaussianInt)) := by ring
         _ = d^3*(u:GaussianInt) := by rw [ue];ring
  obtain ⟨m,n⟩ := w
  have rx := congrArg Zsqrtd.re w3
  have ry := congrArg Zsqrtd.im w3
  simp [a,pow_succ] at rx ry
  have em : (x:ℤ)^2=m*(m^2-3*n^2) := by linear_combination -rx
  have en : (y:ℤ)^2=n*(3*m^2-n^2) := by linear_combination -ry
  refine ⟨m,n,em,en,?_⟩
  have eq : (m^2+n^2)^3=(b:ℤ)^3 := by
    calc (m^2+n^2)^3 = (m*(m^2-3*n^2))^2 + (n*(3*m^2-n^2))^2 := by ring
         _ = (x:ℤ)^4+(y:ℤ)^4 := by rw [← em,← en];ring
         _ = _ := by exact_mod_cast he
  exact (Odd.strictMono_pow (by decide : Odd 3)).injective eq

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

private theorem magnitude {m u b : ℕ} (h : m=u^2 ∨ m=3*u^2)
    (le : m^2≤b) (hb : b≤1456256357804) : u≤1098 := by
  have sq : u^2 ≤ m := by rcases h with h|h <;> omega
  have sm := Nat.pow_le_pow_left sq 2
  by_contra! big
  have lg := Nat.pow_le_pow_left (show 1099≤u by omega) 4
  have e : (u^2)^2=u^4 := by ring
  have bad : 1456256357804 < 1099^4 := by decide
  omega

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

set_option maxRecDepth 16000 in
/-- For Z² + 3u⁴ = v⁴, reduction modulo 16 and 5 forces 10 ∣ u. Eleven
further quadratic-residue tables cover the bounded values of u and v. -/
private theorem quartic_three {u v Z : ℕ} (up : 0<u) (ub : u≤1098) (vp : 0<v)
    (vb : v≤1098) (eqn : Z^2+3*u^4=v^4) : False := by
  have red (p : ℕ) : ((Z%p)^2+3*(u%p)^4)%p=(v%p)^4%p := by
    have e := ((Nat.mod_modEq Z p).pow 2).add (((Nat.mod_modEq u p).pow 4).mul_left 3)
    exact e.trans (by rw [eqn];exact ((Nat.mod_modEq v p).pow 4).symm)
  have checks16 : ∀ a b c : Fin 16, (a.val^2+3*b.val^4)%16=c.val^4%16 → b.val%2=0 := by decide +kernel
  have checks5 : ∀ a b c : Fin 5, (a.val^2+3*b.val^4)%5=c.val^4%5 → b.val=0 := by decide +kernel
  have d2 := checks16 ⟨Z%16,Nat.mod_lt _ (by decide)⟩ ⟨u%16,Nat.mod_lt _ (by decide)⟩
    ⟨v%16,Nat.mod_lt _ (by decide)⟩ (red 16)
  change (u%16)%2=0 at d2
  rw [Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 16)] at d2
  have d5 : u%5=0 := checks5 ⟨Z%5,Nat.mod_lt _ (by decide)⟩ ⟨u%5,Nat.mod_lt _ (by decide)⟩
    ⟨v%5,Nat.mod_lt _ (by decide)⟩ (red 5)
  obtain ⟨a,ea⟩ : 10 ∣ u := (show Nat.Coprime 2 5 by decide).mul_dvd_of_dvd_of_dvd
    (Nat.dvd_of_mod_eq_zero d2) (Nat.dvd_of_mod_eq_zero d5)
  let ts : List (ℕ × ℕ) := [
    (41, 0x1b382b50737),
    (61, 0x1713e6940a59f23b),
    (13, 0x161b),
    (241, 0x1fba6a35a231798f24257c4cba0e12fd21c174c8fa9093c67a3116b15977f),
    (149, 0x13d036bbd749d181671239a062e4baf75b02f3),
    (281, 0x1b78ba137e65193ceba0f1880b096ad7a23b7117ad5a4340463c175cf26299fb21747b7),
    (233, 0x1a71ec5bf3809e6ae86a11160bb5b336b741a221585d59e4073f68de397),
    (139, 0x30ab7730c190a4be0af82daf67cf3112af3),
    (223, 0x163c0fb010ae9a5413158dbdd3996634424e5737d5a68af7f20fc397),
    (137, 0x1a74fc92abc21827733b90610f5524fcb97),
    (7, 0x17)]
  let pass := fun (a v : ℕ) =>
    a==0 || v==0 || decide (v^4 < 3*(10*a)^4) ||
      !(ts.all (fun t => t.2.testBit ((v^4-3*(10*a)^4)%t.1)))
  have valid : ts.all (fun t => decide (0<t.1) &&
      (List.range t.1).all (fun z => t.2.testBit (z^2%t.1))) = true := by
    dsimp only [ts];decide +kernel
  have tested : (List.range 110).all (fun j => (List.range 1099).all (pass j))=true := by
    dsimp only [pass,ts];decide +kernel
  have yes := List.all_eq_true.mp (List.all_eq_true.mp tested a (List.mem_range.mpr (by omega)))
    v (List.mem_range.mpr (by omega))
  have square : ts.all (fun t => t.2.testBit ((v^4-3*(10*a)^4)%t.1))=true := by
    apply List.all_eq_true.mpr
    intro t ht
    have good := List.all_eq_true.mp valid t ht
    simp only [Bool.and_eq_true,decide_eq_true_eq] at good
    have r := List.all_eq_true.mp good.2 (Z%t.1) (List.mem_range.mpr (Nat.mod_lt _ good.1))
    have ev := (Nat.mod_modEq Z t.1).pow 2
    change (Z%t.1)^2%t.1=Z^2%t.1 at ev
    have w : v^4-3*(10*a)^4=Z^2 := by rw [←ea,←eqn];omega
    simpa only [w,ev] using r
  have a0 : a≠0 := by omega
  have v0 := vp.ne'
  have vge : ¬v^4<3*(10*a)^4 := by rw [←ea,←eqn];omega
  simp [pass,a0,v0,vge,square] at yes

/-- If the smaller Gaussian coordinate is a square, the local obstruction at
3 suffices. If it is three times a square, coprimality makes the other
coordinate a square, giving precisely Z² + 3u⁴ = v⁴. -/
private theorem small_magnitude {u v s t X : ℕ} (up : 0<u) (ub : u≤1098)
    (vp : 0<v) (vb : v≤1098) (ss : s=1 ∨ s=3) (tt : t=1 ∨ t=3)
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
      exact quartic_three up ub vp vb (show w^2+3*u^4=v^4 by omega)
    · exact (Nat.not_coprime_of_dvd_of_dvd (by decide : 1<3) (dvd_mul_right _ _) (dvd_mul_right _ _)) cp

/-- No bounded primitive sum in the census is a cube. -/
private theorem cube_excluded_odd {b x y : ℕ} (hb : b≤1456256357804)
    (hodd : Odd b) (hx : 0<x) (hy : 0<y) (hc : x.Coprime y) (he : x^4+y^4=b^3) : False := by
  obtain ⟨m,n,ex,ey,norm⟩ := gaussian_cube hc hodd he
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
  have sum : A^2+B^2=b := by exact_mod_cast (show (A:ℤ)^2+(B:ℤ)^2=(b:ℤ) by rw [absSquare,absSquare,norm])
  have ub := magnitude hu (by omega : A^2≤b) hb
  have vb := magnitude hv (by omega : B^2≤b) hb
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
    exact small_magnitude up ub vp vb ss tt (by rwa [←es,←et]) le e
  · have e := smaller_square le yy
    rw [es,et] at e le
    exact small_magnitude vp vb up ub tt ss (by rw [←es,←et]; exact cp.symm) le e

/-- Lucas's no-cube theorem throughout the full range of the original census.
The Gaussian argument treats odd cubes. A primitive fourth-power sum is never
divisible by four, which also excludes even cubes. -/
theorem bounded_lucas {b x y : ℕ} (hb : b≤1456256357804) (hx : 0<x) (hy : 0<y)
    (hc : x.Coprime y) (he : x^4+y^4=b^3) : False := by
  rcases Nat.even_or_odd b with even|odd
  · have h2 : 2 ∣ b := even_iff_two_dvd.mp even
    have d4 : 4 ∣ b^3 := (pow_dvd_pow_of_dvd h2 2).trans (pow_dvd_pow b (by decide : 2≤3))
    exact not_four hc (he ▸ d4)
  · exact cube_excluded_odd hb odd hx hy hc he

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
  obtain ⟨k,hk,kpos,kres,small,h41,h73⟩ :=
    parameter_bounds bhi hx (hx.trans strict) hc hz he cut
  have tri := triangle_of_quartic (x := (x:ℚ)) (y := (y:ℚ)) (z := (z:ℚ)) (b := (b:ℚ))
    (by exact_mod_cast hx) (by exact_mod_cast strict) (by exact_mod_cast zp) (by exact_mod_cast he)
  have val : b*z^2=b^3*k^2 := by rw [hk];ring
  rw [val] at he cut
  by_cases d : k=17
  · subst k
    exact first b x y blo small sq primes tri hx strict hy hc he cut
  · obtain ⟨k41,upper⟩ := h41 d
    exact rest b k x y blo upper sq primes k41 kres
      (fun hi => by by_contra ne;exact (Nat.not_lt_of_ge (h73 d ne)) hi)
      tri hx strict hy hc he cut

end OMA.R_mo_191889_R1_H3_R1
