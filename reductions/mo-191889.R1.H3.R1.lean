import OMAReductions.R_mo_191889_R1
import Mathlib

/-!
# The large squarefree parameter in the powerful fourth-power census

Write the sum as b³k². Every prime of k is 1 modulo 8. Thus the first three
possible positive cofactors are 1, 17 and 41. The case k = 1 is the primitive
fourth-powers-to-a-cube theorem attributed to Lucas. In the other cases the
cutoff gives three explicit bounds on b. Each remaining parameter also makes
2b the area of a rational right triangle. We construct its sides directly.

The prime-order and parity arguments below are adapted from ZedingZhang’s parent
reduction in #8603. The cube theorem and congruent-number sieve are used by
Noam D. Elkies and Gaurav Goel, *On powerful integers expressible as sums of
two coprime fourth powers*, sections 2 and 4.
https://antsmath.org/ANTSXV/papers/ANTS-XV_elkies-goel.pdf
-/

namespace OMA.R_mo_191889_R1_H3_R1

/-- The bounded instance of Lucas's primitive cube theorem. -/
def H1 : Prop :=
  ∀ b x y : ℕ, 10000 < b → b ≤ 1456256357804 → Squarefree b →
    (∀ p ∈ b.primeFactors, p % 8 = 1) →
    0 < x → x < y → y ≤ 1325648472 → x.Coprime y → x^4+y^4=b^3 → False

/-- Only these parameters and cofactors can enter the remaining census. -/
def H2 : Prop :=
  ∀ b k x y : ℕ, 10000 < b → b ≤ 220261480241 → Squarefree b →
    (∀ p ∈ b.primeFactors, p % 8 = 1) →
    17 ≤ k → (∀ p ∈ k.primeFactors, p % 8 = 1) →
    (122475323887 < b → k = 17) →
    (83372455837 < b → k = 17 ∨ k = 41) →
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

end Arithmetic

theorem main : H1 → H2 → OMA.R_mo_191889_R1.H3 := by
  intro cube census b z x y blo bhi square primes hz hx hxy hy hc hsum hsmall
  obtain ⟨k,hk⟩ := hz
  have bz : 0<b := by omega
  have kp : 0<k := by
    by_contra! h
    have k0 : k=0 := by omega
    rw [hk,k0] at hsum
    simp at hsum
    omega
  have zp : 0<z := by rw [hk]; positivity
  have xy : x<y := by
    by_contra! h
    have e : x=y := by omega
    have x1 : x=1 := by simpa [← e] using hc
    have two : 2=b*z^2 := by simpa [← e,x1] using hsum
    have le : b ≤ b*z^2 := by simpa using Nat.mul_le_mul_left b (show 1≤z^2 from pow_pos zp _)
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
  by_cases k1 : k=1
  · exact cube b x y blo bhi square primes hx xy hy hc (by simpa [k1] using eqn)
  have k17 : 17≤k := by omega
  have upper {B K : ℕ} (hK : K≤k) (cut : 3088257489493360278725196965477359217 ≤
      (B+1)^3*K^2) : b≤B := by
    by_contra! h
    have lower := Nat.mul_le_mul (Nat.pow_le_pow_left (show B+1≤b by omega) 3)
      (Nat.pow_le_pow_left hK 2)
    omega
  refine census b k x y blo (upper k17 (by decide)) square primes k17 kres ?_ ?_ ?_
    hx xy hy hc eqn hsmall
  · intro h
    by_contra ne
    have k41 : 41≤k := by omega
    have := upper (B:=122475323887) k41 (by decide)
    omega
  · intro h
    by_contra! ne
    have k73 : 73≤k := by omega
    have := upper (B:=83372455837) k73 (by decide)
    omega
  · exact triangle_of_quartic (x := (x : ℚ)) (y := (y : ℚ)) (z := (z : ℚ)) (by exact_mod_cast hx) (by exact_mod_cast xy)
      (by exact_mod_cast zp) (by exact_mod_cast hsum)

end OMA.R_mo_191889_R1_H3_R1
