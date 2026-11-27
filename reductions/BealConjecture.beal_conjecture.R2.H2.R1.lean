import OMAReductions.R_BealConjecture_beal_conjecture_R2

-- Credit: @ubuwaits

/-!
# Power-of-two gaps and the exponents three and twenty-three

Reduce both odd-base exponents to four or an odd prime. In the two mixed
orientations with exponents three and twenty-three, change signs to put
the power of two on the right. The cubic descent bounds its exponent.
-/

namespace OMA.R_BealConjecture_beal_conjecture_R2_H2_R1

open OMA.R_BealConjecture_beal_conjecture_R2

/-- The other normalized pairs. The output and the power of two cannot both be squares. -/
def H1 : Prop :=
  ∀ {b c p r k : ℕ}, b%2=1 → c%2=1 → b.Coprime c → p.Coprime r →
    (p=4 ∨ (p.Prime ∧ 2<p)) → (r=4 ∨ (r.Prime ∧ 2<r)) → 2<k →
    (k%2=1 ∨ r%2=1) → (p≠3 ∨ r≠23) → (p≠23 ∨ r≠3) → 2^k+b^p ≠ c^r

/-- The two generalized Fermat equations with a repeated exponent. -/
def H2 : Prop :=
  ∀ {X Y Z : ℤ}, X≠0 → Y≠0 → Z≠0 → IsCoprime X Y →
    X^3+Y^3 ≠ Z^23 ∧ X^23+Y^23 ≠ Z^3

/-- The residual coefficient-two equation at a positive power of eight. -/
def H3 : Prop :=
  ∀ {Y Z : ℤ} {t : ℕ}, 0<t → Odd Y → Odd Z → 2*((2:ℤ)^(3*t))^23 + Y^23 ≠ Z^3

/-- The common unit exponent in the cubic descent restricts the exponent of two. -/
def H4 : Prop :=
  ∀ {a b : ℤ} {k : ℕ}, IsCoprime a b → a^3+b^23=(2:ℤ)^k →
    3 ∣ k ∨ 23 ∣ k ∨ k%69=1

section

private theorem exponent_factor {n : ℕ} (hn : 2<n) :
    ∃ p u : ℕ, n=u*p ∧ (p=4 ∨ (p.Prime ∧ 2<p)) := by
  by_cases h4 : 4 ∣ n
  · obtain ⟨u,hu⟩ := h4
    exact ⟨4,u,by omega, Or.inl rfl⟩
  let m := if 2 ∣ n then n/2 else n
  have hm : 1 < m := by dsimp [m]; split <;> omega
  have hm2 : ¬2 ∣ m := by dsimp [m]; split <;> omega
  have hmn : m ∣ n := by
    dsimp [m]; split
    · exact ⟨2,by omega⟩
    · exact dvd_refl _
  obtain ⟨p,hp,hd⟩ := Nat.exists_prime_and_dvd hm.ne'
  obtain ⟨u,hu⟩ := hd.trans hmn
  refine ⟨p,u,hu.trans (Nat.mul_comm _ _),Or.inr ⟨hp,?_⟩⟩
  have hp2 : p≠2 := by rintro rfl; exact hm2 hd
  have := hp.two_le
  omega

private theorem bases_coprime {b c p r k : ℕ} (hb : b%2=1) (hp : 0<p) (hr : 0<r)
    (h : 2^k+b^p=c^r) : b.Coprime c := by
  apply Nat.coprime_of_dvd
  intro l hl hb' hc'
  have hx : l ∣ b^p := hb'.trans (dvd_pow_self _ hp.ne')
  have hz : l ∣ c^r := hc'.trans (dvd_pow_self _ hr.ne')
  have h₂ : l ∣ 2^k := (Nat.dvd_add_iff_left hx).mpr (h ▸ hz)
  have hl₂ := (Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp (hl.dvd_of_dvd_pow h₂)
  subst l
  omega

private theorem square_gap {b c p r k : ℕ} (hb : b%2=1) (hc : c%2=1)
    (hp : 2<p) (hk : 2<k) (cop : p.Coprime r) (eqn : 2^k+b^p=c^r) :
    k%2=1 ∨ r%2=1 := by
  by_contra! h
  let v := 2^(k/2)
  let u := c^(r/2)
  have hv : v%2=0 := by
    dsimp [v]; rw [Nat.pow_mod]; simp [Nat.zero_pow (show 0<k/2 by omega)]
  have hu : u%2=1 := BealTwoPower.odd_pow hc _
  have he : v^2+b^p=u^2 := by
    dsimp only [v,u]; rw [←pow_mul,←pow_mul,show k/2*2=k by omega,show r/2*2=r by omega]
    exact eqn
  have hlt : v<u := by
    apply (Nat.pow_lt_pow_iff_left (by decide : 2≠0)).mp
    have := Nat.pow_pos (n:=p) (show 0<b by omega)
    omega
  let d := u-v
  let e := u+v
  have hde : e=d+2^(k/2+1) := by dsimp only [e,d]; rw [pow_succ]; change u+v=u-v+v*2; omega
  have hd : d%2=1 := by dsimp [d]; omega
  have hprod : d*e=b^p := by
    have hu' : u = d+v := by dsimp [d]; omega
    dsimp only [e]; rw [hu'] at he ⊢; nlinarith
  have hcop : d.Coprime e := by
    apply Nat.coprime_of_dvd
    intro l hl hld hle
    have hv' : l ∣ 2^(k/2+1) := (Nat.dvd_add_iff_right hld).mpr (hde ▸ hle)
    have hl₂ := (Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp (hl.dvd_of_dvd_pow hv')
    subst l
    omega
  obtain ⟨s,hs⟩ := exists_eq_pow_of_mul_eq_pow
    (gcd_isUnit_iff_isRelPrime.mpr (Nat.coprime_iff_isRelPrime.mp hcop)) hprod
  obtain ⟨t,ht⟩ := exists_eq_pow_of_mul_eq_pow
    (gcd_isUnit_iff_isRelPrime.mpr (Nat.coprime_iff_isRelPrime.mp hcop.symm)) ((Nat.mul_comm _ _).trans hprod)
  have heodd : e%2=1 := by dsimp [e]; omega
  have hsp : s%2=1 := by rw [hs,BealTwoPower.parity_pow (by omega : 0<p)] at hd; exact hd
  have htp : t%2=1 := by rw [ht,BealTwoPower.parity_pow (by omega : 0<p)] at heodd; exact heodd
  have hodd : p%2=1 := by
    by_contra hne
    have := Nat.dvd_gcd (show 2 ∣ p by omega) (show 2 ∣ r by omega)
    change p.gcd r = 1 at cop
    omega
  have hst : s<t := by
    apply lt_of_not_ge
    intro hle
    have := Nat.pow_le_pow_left hle p
    have := Nat.two_pow_pos (k/2+1)
    omega
  apply BealPartial.odd_power_difference htp hsp hst (by omega) hodd (k/2+1)
  rw [←hs,←ht,hde,Nat.add_sub_cancel_left]

/-- At k = 69t + 1, writing the right side as twice the 23rd power of 2^(3t)
gives the coefficient-two equation. The two divisibility cases give equal exponents. -/
private theorem mixed (repeated : H2) (weighted : H3) (sieve : H4) {a b : ℤ} {k : ℕ}
    (ha : Odd a) (hb : Odd b) (hc : IsCoprime a b) (hk : 2<k) :
    a^3+b^23 ≠ (2:ℤ)^k := by
  intro he
  have cop₂ (x : ℤ) (hx : Odd x) (m : ℕ) : IsCoprime ((2:ℤ)^m) (-x) := by
    apply IsCoprime.pow_left
    apply Int.prime_two.irreducible.coprime_iff_not_dvd.mpr
    exact fun h => (Int.not_even_iff_odd.mpr hx.neg) (even_iff_two_dvd.mpr h)
  have han : a≠0 := by rintro rfl; simp at ha
  have hbn : b≠0 := by rintro rfl; simp at hb
  rcases sieve hc he with h | h | h
  · obtain ⟨m,rfl⟩ := h
    have hh := (repeated (X:=2^m) (Y:=-a) (Z:=b) (by positivity) (neg_ne_zero.mpr han) hbn (cop₂ a ha m)).1
    apply hh
    rw [←pow_mul,Nat.mul_comm m 3]
    linear_combination -he
  · obtain ⟨m,rfl⟩ := h
    have hh := (repeated (X:=2^m) (Y:=-b) (Z:=a) (by positivity) (neg_ne_zero.mpr hbn) han (cop₂ b hb m)).2
    apply hh
    rw [←pow_mul,Nat.mul_comm m 23]
    linear_combination -he
  · let t := k/69
    have ht : 0<t := by dsimp [t]; omega
    apply weighted (t:=t) (Y:=-b) (Z:=a) ht hb.neg ha
    have he' : (2:ℤ)^k = 2*((2:ℤ)^(3*t))^23 := by
      rw [show k = (3*t)*23+1 by dsimp [t]; omega,pow_succ,pow_mul,mul_comm]
    rw [he'] at he
    linear_combination -he

end

theorem main : H1 → H2 → H3 → H4 → OMA.R_BealConjecture_beal_conjecture_R2.H2 := by
  intro rest repeated weighted sieve b c y z k hb hc hy hz hk cop h
  obtain ⟨p,u,hy',hp⟩ := exponent_factor hy
  obtain ⟨r,v,hz',hr⟩ := exponent_factor hz
  have hp' : 2<p := hp.elim (fun e => by omega) And.right
  have hr' : 2<r := hr.elim (fun e => by omega) And.right
  change y.Coprime z at cop
  have hd₁ : p ∣ y := ⟨u,hy'.trans (Nat.mul_comm _ _)⟩
  have hd₂ : r ∣ z := ⟨v,hz'.trans (Nat.mul_comm _ _)⟩
  have hpr := Nat.Coprime.coprime_dvd_right hd₂ (Nat.Coprime.coprime_dvd_left hd₁ cop)
  rw [hy',hz',pow_mul,pow_mul] at h
  have hbo := BealTwoPower.odd_pow hb u
  have hco := BealTwoPower.odd_pow hc v
  have hbase := bases_coprime hbo (by omega : 0<p) (by omega : 0<r) h
  have hor := square_gap hbo hco hp' hk hpr h
  have hbz : Odd ((b^u:ℕ):ℤ) := by exact_mod_cast (Nat.odd_iff.mpr hbo)
  have hcz : Odd ((c^v:ℕ):ℤ) := by exact_mod_cast (Nat.odd_iff.mpr hco)
  let B : ℤ := ((b^u:ℕ):ℤ)
  let C : ℤ := ((c^v:ℕ):ℤ)
  have he : (2:ℤ)^k+B^p=C^r := by dsimp only [B,C]; exact_mod_cast h
  have hBC : IsCoprime B C := hbase.isCoprime
  by_cases h₁ : p=3 ∧ r=23
  · obtain ⟨rfl,rfl⟩ := h₁
    apply mixed repeated weighted sieve hbz.neg hcz (hBC.neg_left) hk (a := -B) (b := C)
    linear_combination -he
  by_cases h₂ : p=23 ∧ r=3
  · obtain ⟨rfl,rfl⟩ := h₂
    apply mixed repeated weighted sieve hcz hbz.neg hBC.symm.neg_right hk (a := C) (b := -B)
    linear_combination -he
  exact rest hbo hco hbase hpr hp hr hk hor (by omega) (by omega) h

end OMA.R_BealConjecture_beal_conjecture_R2_H2_R1

