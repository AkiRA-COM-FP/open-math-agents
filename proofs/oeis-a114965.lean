import OMAStatements.S_oeis_a114965
import Mathlib

-- Problem: A114965: a(n) = n^2 + 34.
-- Upstream: formal-conjectures statements/oeis-a114965.lean:0 (declaration OMA.S_oeis_a114965.main)
-- Credit: @dries (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! `n ^ 2 + 34` is never a perfect power `x ^ k` with `k > 1` (Cohn, Acta Arith. 65 (1993)).

* Even `k`: `n ^ 2 + 34` is `2` or `3` mod 4. Odd `k`: pass to an odd prime `p ∣ k`.
* Descent: `ℤ[√-34]` is a Dedekind domain whose class group has exponent 4 (proved below
  without Minkowski: pigeonhole bound plus explicit primes above 2, 3, 5, 7, 11). Since
  `n + √-34` and `n - √-34` are coprime, `n + √-34 = z ^ p` for some `z`.
* Cohn: no `p`-th power (`p` odd, `p > 1`) has `√-34`-coefficient `1`. Then `z = a ± √-34`
  with `a` odd; for `p ≡ 1 mod 4` a `2`-adic argument, for `p ≡ 3 mod 4` the congruence
  `z ^ 8 ≡ 1 mod 24`. -/

namespace OMA.A114965

abbrev K := QuadraticAlgebra ℚ (-34) 0

instance fact34 : Fact (∀ r : ℚ, r ^ 2 ≠ (-34) + 0 * r) :=
  ⟨fun r h => by nlinarith [sq_nonneg r]⟩

/-- `a + b √-34 ↦ a + b ω`. -/
def φ : ℤ√(-34) →+* K where
  toFun z := ⟨z.re, z.im⟩
  map_one' := by ext <;> rfl
  map_mul' z w := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' z w := by ext <;> simp

instance algK : Algebra (ℤ√(-34)) K := φ.toAlgebra

lemma algebraMap_apply (z : ℤ√(-34)) : algebraMap (ℤ√(-34)) K z = ⟨z.re, z.im⟩ := rfl

lemma am_re (q : ℚ) : (algebraMap ℚ K q).re = q := rfl

lemma am_im (q : ℚ) : (algebraMap ℚ K q).im = 0 := rfl

lemma ratInt {q : ℚ} (h : IsIntegral ℤ q) : ∃ n : ℤ, (n : ℚ) = q :=
  IsIntegrallyClosed.isIntegral_iff.1 h

lemma ratInt_of_sq {q : ℚ} {m : ℤ} (h : q ^ 2 = m) : ∃ n : ℤ, (n : ℚ) = q := by
  apply ratInt
  refine ⟨Polynomial.X ^ 2 - Polynomial.C m, ?_, ?_⟩
  · exact Polynomial.monic_X_pow_sub_C _ (by norm_num)
  · rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]; simp [h]

lemma int_of_integral (x : K) (hx : IsIntegral ℤ x) : ∃ y : ℤ√(-34), algebraMap _ K y = x := by
  have hs : IsIntegral ℤ (star x) := hx.map (starRingEnd K).toIntAlgHom
  have ht : IsIntegral ℤ (x + star x) := hx.add hs
  have hn : IsIntegral ℤ (x * star x) := hx.mul hs
  have ht' : x + star x = algebraMap ℚ K (2 * x.re) := by
    ext <;> simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.re_star,
      QuadraticAlgebra.im_star, am_re, am_im] <;> ring
  have hn' : x * star x = algebraMap ℚ K (x.re ^ 2 + 34 * x.im ^ 2) := by
    ext <;> simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_star,
      QuadraticAlgebra.im_star, am_re, am_im] <;> ring
  rw [ht'] at ht
  rw [hn'] at hn
  obtain ⟨u, hu⟩ := ratInt ((isIntegral_algHom_iff ((Algebra.ofId ℚ K).restrictScalars ℤ)
    (algebraMap ℚ K).injective).1 ht)
  obtain ⟨m, hm⟩ := ratInt ((isIntegral_algHom_iff ((Algebra.ofId ℚ K).restrictScalars ℤ)
    (algebraMap ℚ K).injective).1 hn)
  -- s = 68 x.im = 34 * (2 x.im) satisfies s^2 = 34 * (4 m - u^2)
  obtain ⟨s, hs⟩ := ratInt_of_sq (q := 68 * x.im) (m := 34 * (4 * m - u ^ 2)) (by
    push_cast; rw [hu, hm]; ring)
  have h34 : (34 : ℤ) ∣ s := by
    have hsq : s ^ 2 = 34 * (4 * m - u ^ 2) := by
      have hq : ((s ^ 2 : ℤ) : ℚ) = ((34 * (4 * m - u ^ 2) : ℤ) : ℚ) := by
        push_cast; rw [hs, hu, hm]; ring
      exact_mod_cast hq
    have h2 : (2 : ℤ) ∣ s := Int.Prime.dvd_pow' (p := 2) (by norm_num) (k := 2) ⟨17 * (4 * m - u ^ 2), by rw [hsq]; ring⟩
    have h17 : (17 : ℤ) ∣ s := Int.Prime.dvd_pow' (p := 17) (by norm_num) (k := 2) ⟨2 * (4 * m - u ^ 2), by rw [hsq]; ring⟩
    have : IsCoprime (2 : ℤ) 17 := by rw [Int.isCoprime_iff_gcd_eq_one]; rfl
    simpa using this.mul_dvd h2 h17
  obtain ⟨v, rfl⟩ := h34
  -- now 2 x.re = u, 2 x.im = v, u^2 + 34 v^2 = 4 m
  have hv : (v : ℚ) = 2 * x.im := by push_cast at hs; linarith
  have huv : u ^ 2 + 34 * v ^ 2 = 4 * m := by
    have : ((u ^ 2 + 34 * v ^ 2 : ℤ) : ℚ) = ((4 * m : ℤ) : ℚ) := by
      push_cast; rw [hu, hm]
      rw [hv]; ring
    exact_mod_cast this
  obtain ⟨u', rfl⟩ : (2 : ℤ) ∣ u := by
    rcases Int.even_or_odd u with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · exact ⟨k, by ring⟩
    · exfalso
      rcases Int.even_or_odd v with ⟨l, rfl⟩ | ⟨l, rfl⟩ <;> ring_nf at huv <;> omega
  obtain ⟨v', rfl⟩ : (2 : ℤ) ∣ v := by
    rcases Int.even_or_odd v with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · exact ⟨k, by ring⟩
    · exfalso; ring_nf at huv; omega
  refine ⟨⟨u', v'⟩, ?_⟩
  rw [algebraMap_apply]
  ext
  · simp only; push_cast at hu; linarith
  · simp only; push_cast at hv; linarith

lemma ai_re (n : ℤ) : (algebraMap ℤ K n).re = n := rfl

lemma ai_im (n : ℤ) : (algebraMap ℤ K n).im = 0 := rfl

lemma integral_of_int (y : ℤ√(-34)) : IsIntegral ℤ (algebraMap (ℤ√(-34)) K y) := by
  have hω2 : (⟨0, 1⟩ : K) ^ 2 = algebraMap ℤ K (-34) := by
    ext <;> simp only [sq, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, ai_re, ai_im] <;> norm_num
  have hω : IsIntegral ℤ (⟨0, 1⟩ : K) :=
    IsIntegral.of_pow (by norm_num : 0 < 2) (hω2 ▸ isIntegral_algebraMap)
  have hy : algebraMap (ℤ√(-34)) K y = algebraMap ℤ K y.re + algebraMap ℤ K y.im * ⟨0, 1⟩ := by
    rw [algebraMap_apply]; ext <;> simp
  rw [hy]
  exact isIntegral_algebraMap.add (isIntegral_algebraMap.mul hω)

lemma φ_injective : Function.Injective (algebraMap (ℤ√(-34)) K) := by
  intro z w h
  rw [algebraMap_apply, algebraMap_apply] at h
  have h1 := congrArg QuadraticAlgebra.re h
  have h2 := congrArg QuadraticAlgebra.im h
  simp at h1 h2
  ext <;> assumption

instance : IsIntegralClosure (ℤ√(-34)) ℤ K where
  algebraMap_injective := φ_injective
  isIntegral_iff := fun {x} => ⟨int_of_integral x, fun ⟨y, hy⟩ => hy ▸ integral_of_int y⟩

instance isDom : IsDomain (ℤ√(-34)) := φ_injective.isDomain _

instance isDed : IsDedekindDomain (ℤ√(-34)) :=
  IsIntegralClosure.isDedekindDomain ℤ ℚ K (ℤ√(-34))

/-- `ℤ√(-34) ≃ ℤ²` as a `ℤ`-module. -/
def tup : ℤ√(-34) ≃ₗ[ℤ] (Fin 2 → ℤ) where
  toFun z := ![z.re, z.im]
  invFun v := ⟨v 0, v 1⟩
  map_add' z w := by ext i; fin_cases i <;> simp
  map_smul' n z := by ext i; fin_cases i <;> simp
  left_inv z := by simp
  right_inv v := by ext i; fin_cases i <;> simp

noncomputable def bas : Module.Basis (Fin 2) ℤ (ℤ√(-34)) := Module.Basis.ofEquivFun tup

instance : Module.Free ℤ (ℤ√(-34)) := Module.Free.of_basis bas

instance : Module.Finite ℤ (ℤ√(-34)) := Module.Finite.of_basis bas

lemma bas0 : bas 0 = 1 := by ext <;> simp [bas, tup]

lemma bas1 : bas 1 = ⟨0, 1⟩ := by ext <;> simp [bas, tup]

lemma repr_apply (z : ℤ√(-34)) (i : Fin 2) : bas.repr z i = ![z.re, z.im] i := by
  simp [bas, tup]

lemma algNorm (z : ℤ√(-34)) : Algebra.norm ℤ z = z.re ^ 2 + 34 * z.im ^ 2 := by
  rw [Algebra.norm_eq_matrix_det bas, Matrix.det_fin_two]
  simp only [Algebra.leftMulMatrix_eq_repr_mul, bas0, bas1, repr_apply]
  simp
  ring

lemma absNorm_span (z : ℤ√(-34)) :
    Ideal.absNorm (Ideal.span {z}) = (z.re ^ 2 + 34 * z.im ^ 2).natAbs := by
  rw [Ideal.absNorm_span_singleton, algNorm]

lemma bounds (M : ℕ) (hM : 0 < M) :
    let B := Nat.sqrt (M / 5); let A := M / (B + 1);
    M < (A + 1) * (B + 1) ∧ 5 * (A ^ 2 + 34 * B ^ 2) < 59 * M := by
  intro B A
  have h1 : A * (B + 1) ≤ M := Nat.div_mul_le_self M (B + 1)
  have h2 : M % (B + 1) < B + 1 := Nat.mod_lt _ (by omega)
  have h3 : (B + 1) * A + M % (B + 1) = M := Nat.div_add_mod M (B + 1)
  have h4 : B ^ 2 ≤ M / 5 := Nat.sqrt_le' (M / 5)
  have h5 : M / 5 < (B + 1) ^ 2 := Nat.lt_succ_sqrt' (M / 5)
  have h6 : 5 * (M / 5) ≤ M := Nat.mul_div_le M 5
  have h7 : M < 5 * (M / 5) + 5 := by omega
  have h8 : M < 5 * (B + 1) ^ 2 := by omega
  have h9 : A ^ 2 < 5 * M := by
    have e1 : A ^ 2 * (B + 1) ^ 2 ≤ M ^ 2 := by
      rw [← mul_pow]; exact Nat.pow_le_pow_left h1 2
    have e2 : M ^ 2 < 5 * M * (B + 1) ^ 2 := by
      have := Nat.mul_lt_mul_of_pos_left h8 hM; rw [sq]; linarith
    have : A ^ 2 * (B + 1) ^ 2 < (5 * M) * (B + 1) ^ 2 := by linarith
    exact lt_of_mul_lt_mul_right this (Nat.zero_le _)
  constructor
  · nlinarith
  · omega

lemma exists_small (I : Ideal (ℤ√(-34))) (hI : I ≠ ⊥) :
    ∃ x ∈ I, x ≠ 0 ∧ 5 * (x.re ^ 2 + 34 * x.im ^ 2) < 59 * (Ideal.absNorm I : ℤ) := by
  have hM : 0 < Ideal.absNorm I := Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  obtain ⟨hcard, hb⟩ := bounds _ hM
  set M := Ideal.absNorm I
  set B := Nat.sqrt (M / 5)
  set A := M / (B + 1)
  have : Finite (ℤ√(-34) ⧸ I) := I.finiteQuotientOfFreeOfNeBot hI
  let _ : Fintype (ℤ√(-34) ⧸ I) := Fintype.ofFinite _
  let f : Fin (A + 1) × Fin (B + 1) → ℤ√(-34) ⧸ I :=
    fun ij => Ideal.Quotient.mk I ⟨(ij.1 : ℕ), (ij.2 : ℕ)⟩
  have hc : Fintype.card (ℤ√(-34) ⧸ I) < Fintype.card (Fin (A + 1) × Fin (B + 1)) := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, ← Nat.card_eq_fintype_card]
    have : Nat.card (ℤ√(-34) ⧸ I) = M := rfl
    omega
  obtain ⟨p, q, hne, hpq⟩ := Fintype.exists_ne_map_eq_of_card_lt f hc
  refine ⟨⟨(p.1 : ℕ) - (q.1 : ℕ), (p.2 : ℕ) - (q.2 : ℕ)⟩, ?_, ?_, ?_⟩
  · have := Ideal.Quotient.eq.1 hpq
    convert this using 1
    ext <;> simp
  · intro h
    apply hne
    have h1 := congrArg Zsqrtd.re h
    have h2 := congrArg Zsqrtd.im h
    simp only [Zsqrtd.re_zero, Zsqrtd.im_zero] at h1 h2
    exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
  · simp only
    have ha1 := p.1.isLt; have ha2 := q.1.isLt; have hb1 := p.2.isLt; have hb2 := q.2.isLt
    have eA : (((p.1 : ℕ) : ℤ) - ((q.1 : ℕ) : ℤ)) ^ 2 ≤ (A : ℤ) ^ 2 := by
      apply sq_le_sq' <;> omega
    have eB : (((p.2 : ℕ) : ℤ) - ((q.2 : ℕ) : ℤ)) ^ 2 ≤ (B : ℤ) ^ 2 := by
      apply sq_le_sq' <;> omega
    have : (5 * (A ^ 2 + 34 * B ^ 2) : ℤ) < 59 * M := by exact_mod_cast hb
    linarith

/-! ### Ideal toolkit -/

lemma norm_span (z : ℤ√(-34)) (n : ℕ) (h : z.re ^ 2 + 34 * z.im ^ 2 = n) :
    Ideal.absNorm (Ideal.span {z}) = n := by
  rw [absNorm_span, h]; rfl

lemma cancel_span {I : Ideal (ℤ√(-34))} {y z : ℤ√(-34)} (hz : z ≠ 0)
    (h : I * Ideal.span {y} = Ideal.span {z}) : I.IsPrincipal := by
  have hy : y ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_eq_bot.2 rfl, Ideal.mul_bot, eq_comm, Ideal.span_singleton_eq_bot] at h
    exact hz h
  have hzm : z ∈ Ideal.span {y} := by
    have : z ∈ I * Ideal.span {y} := by rw [h]; exact Ideal.mem_span_singleton_self z
    exact (Ideal.mul_le_right : I * Ideal.span {y} ≤ Ideal.span {y}) this
  obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 hzm
  refine ⟨⟨w, ?_⟩⟩
  rw [← Ideal.span_singleton_mul_span_singleton, mul_comm I] at h
  have := (Ideal.span_singleton_mul_right_inj hy).1 (h.trans (mul_comm _ _))
  rw [Ideal.submodule_span_eq]; exact this

lemma pr_mul {I J : Ideal (ℤ√(-34))} (hI : (I ^ 4).IsPrincipal) (hJ : (J ^ 4).IsPrincipal) :
    ((I * J) ^ 4).IsPrincipal := by
  obtain ⟨a, ha⟩ := hI
  obtain ⟨b, hb⟩ := hJ
  refine ⟨⟨a * b, ?_⟩⟩
  rw [mul_pow, ha, hb, Ideal.submodule_span_eq, Ideal.submodule_span_eq,
    Ideal.span_singleton_mul_span_singleton]

lemma pr_span (z : ℤ√(-34)) : ((Ideal.span {z}) ^ 4).IsPrincipal :=
  ⟨⟨z ^ 4, by rw [Ideal.span_singleton_pow]⟩⟩

lemma pr_cancel {I J : Ideal (ℤ√(-34))} {x : ℤ√(-34)} (hx : x ≠ 0)
    (h : I * J = Ideal.span {x}) (hJ : (J ^ 4).IsPrincipal) : (I ^ 4).IsPrincipal := by
  obtain ⟨y, hy⟩ := hJ
  refine cancel_span (y := y) (z := x ^ 4) (pow_ne_zero 4 hx) ?_
  rw [Ideal.submodule_span_eq] at hy
  rw [← hy, ← mul_pow, h, Ideal.span_singleton_pow]

lemma div_of_mem {Q : Ideal (ℤ√(-34))} {x : ℤ√(-34)} (hx : x ∈ Q) :
    ∃ J, Ideal.span {x} = Q * J :=
  Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hx)

lemma prime_of_norm {P : Ideal (ℤ√(-34))} {p : ℕ} (hp : p.Prime) (h : Ideal.absNorm P = p) :
    P.IsMaximal := by
  have hP : P.IsPrime := Ideal.isPrime_of_irreducible_absNorm (h ▸ hp)
  have hb : P ≠ ⊥ := by
    rintro rfl; rw [Ideal.absNorm_bot] at h; exact hp.ne_zero h.symm
  exact hP.isMaximal hb

lemma natCast_mem {P : Ideal (ℤ√(-34))} {p : ℕ} (h : Ideal.absNorm P = p) : (p : ℤ√(-34)) ∈ P :=
  h ▸ Ideal.absNorm_mem P

/-- A linear invariant modulo `p` of the elements of `span {a, b}`. -/
lemma inv_mem {p k : ℤ} {a b x : ℤ√(-34)} (ha : ∀ u : ℤ√(-34), p ∣ (u * a).re + k * (u * a).im)
    (hb : ∀ u : ℤ√(-34), p ∣ (u * b).re + k * (u * b).im) (hx : x ∈ Ideal.span {a, b}) :
    p ∣ x.re + k * x.im := by
  obtain ⟨u, v, rfl⟩ := Ideal.mem_span_pair.1 hx
  have := dvd_add (ha u) (hb v)
  rw [show (u * a + v * b).re + k * (u * a + v * b).im =
    ((u * a).re + k * (u * a).im) + ((v * b).re + k * (v * b).im) by simp; ring]
  exact this

lemma ne_top_of_inv {p k : ℤ} {a b : ℤ√(-34)} (hp : ¬ p ∣ 1)
    (ha : ∀ u : ℤ√(-34), p ∣ (u * a).re + k * (u * a).im)
    (hb : ∀ u : ℤ√(-34), p ∣ (u * b).re + k * (u * b).im) : Ideal.span {a, b} ≠ ⊤ := by
  intro h
  have := inv_mem ha hb (h ▸ Submodule.mem_top : (1 : ℤ√(-34)) ∈ Ideal.span {a, b})
  simp at this; exact hp this

lemma norm_pair {a b : ℤ√(-34)} {p na nb : ℕ} (hp : p.Prime) (hne : Ideal.span {a, b} ≠ ⊤)
    (hna : a.re ^ 2 + 34 * a.im ^ 2 = na) (hnb : b.re ^ 2 + 34 * b.im ^ 2 = nb)
    (hg : Nat.gcd na nb = p) : Ideal.absNorm (Ideal.span {a, b}) = p := by
  have h1 : Ideal.absNorm (Ideal.span {a, b}) ∣ na := norm_span a na hna ▸
    Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 (Ideal.subset_span (by simp)))
  have h2 : Ideal.absNorm (Ideal.span {a, b}) ∣ nb := norm_span b nb hnb ▸
    Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 (Ideal.subset_span (by simp)))
  have := Nat.dvd_gcd h1 h2
  rw [hg] at this
  rcases (Nat.dvd_prime hp).1 this with h | h
  · exact absurd (Ideal.absNorm_eq_one_iff.1 h) hne
  · exact h

/-! ### The primes above 2, 3, 5, 7, 11 -/

/-- `√-34`. -/
def w0 : ℤ√(-34) := ⟨0, 1⟩

def Q2 : Ideal (ℤ√(-34)) := Ideal.span {2, w0}
def Q5 : Ideal (ℤ√(-34)) := Ideal.span {5, 1 + w0}
def Q5' : Ideal (ℤ√(-34)) := Ideal.span {5, 1 - w0}
def Q7 : Ideal (ℤ√(-34)) := Ideal.span {7, 1 + w0}
def Q7' : Ideal (ℤ√(-34)) := Ideal.span {7, 1 - w0}

lemma i2a (u : ℤ√(-34)) : (2 : ℤ) ∣ (u * 2).re + 0 * (u * 2).im := ⟨u.re, by simp; ring⟩
lemma i2b (u : ℤ√(-34)) : (2 : ℤ) ∣ (u * w0).re + 0 * (u * w0).im := ⟨-17 * u.im, by simp [w0]; ring⟩
lemma i5a (u : ℤ√(-34)) : (5 : ℤ) ∣ (u * 5).re + -1 * (u * 5).im := ⟨u.re - u.im, by simp; ring⟩
lemma i5b (u : ℤ√(-34)) : (5 : ℤ) ∣ (u * (1 + w0)).re + -1 * (u * (1 + w0)).im :=
  ⟨-7 * u.im, by simp [w0]; ring⟩
lemma i5a' (u : ℤ√(-34)) : (5 : ℤ) ∣ (u * 5).re + 1 * (u * 5).im := ⟨u.re + u.im, by simp; ring⟩
lemma i5b' (u : ℤ√(-34)) : (5 : ℤ) ∣ (u * (1 - w0)).re + 1 * (u * (1 - w0)).im :=
  ⟨7 * u.im, by simp [w0]; ring⟩
lemma i7a (u : ℤ√(-34)) : (7 : ℤ) ∣ (u * 7).re + -1 * (u * 7).im := ⟨u.re - u.im, by simp; ring⟩
lemma i7b (u : ℤ√(-34)) : (7 : ℤ) ∣ (u * (1 + w0)).re + -1 * (u * (1 + w0)).im :=
  ⟨-5 * u.im, by simp [w0]; ring⟩
lemma i7a' (u : ℤ√(-34)) : (7 : ℤ) ∣ (u * 7).re + 1 * (u * 7).im := ⟨u.re + u.im, by simp; ring⟩
lemma i7b' (u : ℤ√(-34)) : (7 : ℤ) ∣ (u * (1 - w0)).re + 1 * (u * (1 - w0)).im :=
  ⟨5 * u.im, by simp [w0]; ring⟩

lemma nQ2 : Ideal.absNorm Q2 = 2 :=
  norm_pair (na := 4) (nb := 34) Nat.prime_two (ne_top_of_inv (by norm_num) i2a i2b) (by simp) (by simp [w0]) (by norm_num)
lemma nQ5 : Ideal.absNorm Q5 = 5 :=
  norm_pair (na := 25) (nb := 35) (by norm_num) (ne_top_of_inv (by norm_num) i5a i5b) (by simp) (by simp [w0]) (by norm_num)
lemma nQ5' : Ideal.absNorm Q5' = 5 :=
  norm_pair (na := 25) (nb := 35) (by norm_num) (ne_top_of_inv (by norm_num) i5a' i5b') (by simp) (by simp [w0]) (by norm_num)
lemma nQ7 : Ideal.absNorm Q7 = 7 :=
  norm_pair (na := 49) (nb := 35) (by norm_num) (ne_top_of_inv (by norm_num) i7a i7b) (by simp) (by simp [w0]) (by norm_num)
lemma nQ7' : Ideal.absNorm Q7' = 7 :=
  norm_pair (na := 49) (nb := 35) (by norm_num) (ne_top_of_inv (by norm_num) i7a' i7b') (by simp) (by simp [w0]) (by norm_num)

lemma n4m : (4 - w0) ∉ Q5' := fun h => by
  have := inv_mem i5a' i5b' h; simp [w0] at this
lemma n4p : (4 + w0) ∉ Q5 := fun h => by
  have := inv_mem i5a i5b h; simp [w0] at this
lemma n1p : (1 + w0) ∉ Q7' := fun h => by
  have := inv_mem i7a' i7b' h; simp [w0] at this
lemma n1m : (1 - w0) ∉ Q7 := fun h => by
  have := inv_mem i7a i7b h; simp [w0] at this

lemma pair_le {P : Ideal (ℤ√(-34))} {a b : ℤ√(-34)} (ha : a ∈ P) (hb : b ∈ P) :
    Ideal.span {a, b} ≤ P := by
  rw [Ideal.span_le]; intro z hz
  rcases hz with rfl | rfl
  · exact ha
  · exact hb

lemma cl2 {P : Ideal (ℤ√(-34))} (hP : P.IsPrime) (h : (2 : ℤ√(-34)) ∈ P) : P = Q2 := by
  have e : w0 * w0 = 2 * (-17) := by ext <;> simp [w0]
  have hw : w0 ∈ P := by
    have : w0 * w0 ∈ P := by rw [e]; exact P.mul_mem_right _ h
    rcases hP.mem_or_mem this with h' | h' <;> exact h'
  exact ((prime_of_norm Nat.prime_two nQ2).eq_of_le hP.ne_top (pair_le h hw)).symm

lemma cl57 {P : Ideal (ℤ√(-34))} (hP : P.IsPrime) {q r : ℕ} (hqr : (q : ℤ√(-34)) * r = 35)
    (h : (q : ℤ√(-34)) ∈ P) : 1 + w0 ∈ P ∨ 1 - w0 ∈ P := by
  have e : (1 + w0) * (1 - w0) = (q : ℤ√(-34)) * r := by rw [hqr]; ext <;> simp [w0]
  exact hP.mem_or_mem (by rw [e]; exact P.mul_mem_right _ h)

lemma cl5 {P : Ideal (ℤ√(-34))} (hP : P.IsPrime) (h : (5 : ℤ√(-34)) ∈ P) : P = Q5 ∨ P = Q5' := by
  rcases cl57 hP (q := 5) (r := 7) (by norm_num) (by exact_mod_cast h) with h' | h'
  · exact Or.inl ((prime_of_norm (by norm_num) nQ5).eq_of_le hP.ne_top (pair_le h h')).symm
  · exact Or.inr ((prime_of_norm (by norm_num) nQ5').eq_of_le hP.ne_top (pair_le h h')).symm

lemma cl7 {P : Ideal (ℤ√(-34))} (hP : P.IsPrime) (h : (7 : ℤ√(-34)) ∈ P) : P = Q7 ∨ P = Q7' := by
  rcases cl57 hP (q := 7) (r := 5) (by norm_num) (by exact_mod_cast h) with h' | h'
  · exact Or.inl ((prime_of_norm (by norm_num) nQ7).eq_of_le hP.ne_top (pair_le h h')).symm
  · exact Or.inr ((prime_of_norm (by norm_num) nQ7').eq_of_le hP.ne_top (pair_le h h')).symm

/-- `3` and `11` are inert: `a ^ 2 + 34 b ^ 2 ≡ 0` forces `a ≡ b ≡ 0`. -/
lemma cl_inert {p : ℕ} (hp : p.Prime) (hres : ∀ a b : ZMod p, a ^ 2 + 34 * b ^ 2 = 0 → a = 0 ∧ b = 0)
    {P : Ideal (ℤ√(-34))} (hP : P.IsPrime) (h : (p : ℤ√(-34)) ∈ P) :
    P = Ideal.span {(p : ℤ√(-34))} := by
  have hdN : ∀ x : ℤ√(-34), (p : ℤ) ∣ x.norm → ((p : ℤ) : ℤ√(-34)) ∣ x := by
    intro x hx
    rw [Zsqrtd.norm_def, ← ZMod.intCast_zmod_eq_zero_iff_dvd] at hx
    push_cast at hx
    obtain ⟨h1, h2⟩ := hres x.re x.im (by linear_combination hx)
    rw [Zsqrtd.intCast_dvd]
    exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h1, (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h2⟩
  have hp0 : (p : ℤ√(-34)) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hpr : Prime (p : ℤ√(-34)) := by
    refine ⟨hp0, ?_, ?_⟩
    · intro hu
      rw [Zsqrtd.isUnit_iff_norm_isUnit, Zsqrtd.norm_natCast, Int.isUnit_iff] at hu
      have := hp.two_le
      rcases hu with hu | hu <;> nlinarith
    · intro x y ⟨w, hw⟩
      have hn := congrArg Zsqrtd.norm hw
      rw [Zsqrtd.norm_mul, Zsqrtd.norm_mul, Zsqrtd.norm_natCast] at hn
      have : (p : ℤ) ∣ x.norm * y.norm := ⟨p * w.norm, by rw [hn]; ring⟩
      have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
      rcases hpz.dvd_or_dvd this with h' | h'
      · left; exact_mod_cast hdN x h'
      · right; exact_mod_cast hdN y h'
  have hmax : (Ideal.span {(p : ℤ√(-34))}).IsMaximal :=
    ((Ideal.span_singleton_prime hp0).2 hpr).isMaximal (by simpa using hp0)
  exact (hmax.eq_of_le hP.ne_top ((Ideal.span_singleton_le_iff_mem _).2 h)).symm

/-! ### Fourth powers of the small primes -/

lemma absNorm_mul' (I J : Ideal (ℤ√(-34))) : Ideal.absNorm (I * J) = Ideal.absNorm I * Ideal.absNorm J :=
  map_mul Ideal.absNorm I J

lemma eq_of_cases {J A B : Ideal (ℤ√(-34))} {x : ℤ√(-34)} (h : J = A ∨ J = B) (hx : x ∈ J)
    (hB : x ∉ B) : J = A := by
  rcases h with h | h
  · exact h
  · exact absurd (h ▸ hx) hB

lemma mem_right {Q J : Ideal (ℤ√(-34))} {x : ℤ√(-34)} (h : Ideal.span {x} = Q * J) : x ∈ J :=
  (Ideal.mul_le_right : Q * J ≤ J) (h ▸ Ideal.mem_span_singleton_self x)

lemma Q2sq : Q2 * Q2 = Ideal.span {2} := by
  obtain ⟨J, hJ⟩ := div_of_mem (Q := Q2) (Ideal.subset_span (by simp) : (2 : ℤ√(-34)) ∈ Q2)
  have hn := congrArg Ideal.absNorm hJ
  rw [absNorm_mul', nQ2, norm_span 2 4 (by simp)] at hn
  have hJn : Ideal.absNorm J = 2 := by omega
  have := cl2 (prime_of_norm Nat.prime_two hJn).isPrime (by exact_mod_cast natCast_mem hJn)
  rw [hJ, this]

lemma Q2pow : (Q2 ^ 4).IsPrincipal := by
  rw [show Q2 ^ 4 = (Q2 * Q2) ^ 2 by ring, Q2sq, Ideal.span_singleton_pow]
  exact ⟨⟨_, Ideal.submodule_span_eq.symm⟩⟩

/-- `(4 ∓ √-34) = Q2 Q ^ 2` for `Q` the prime above 5 containing `4 ∓ √-34`. -/
lemma Q5gen {Q Q' : Ideal (ℤ√(-34))} {x : ℤ√(-34)} (hx2 : x ∈ Q2) (hxn : x.re ^ 2 + 34 * x.im ^ 2 = 50)
    (hcl : ∀ P : Ideal (ℤ√(-34)), P.IsPrime → (5 : ℤ√(-34)) ∈ P → P = Q ∨ P = Q') (hx' : x ∉ Q')
    (hx0 : x ≠ 0) (hQn : Ideal.absNorm Q = 5) : (Q ^ 4).IsPrincipal := by
  obtain ⟨J1, h1⟩ := div_of_mem hx2
  have hn1 := congrArg Ideal.absNorm h1
  rw [absNorm_mul', nQ2, norm_span x 50 hxn] at hn1
  have hJ1n : Ideal.absNorm J1 = 25 := by omega
  have hJ1t : J1 ≠ ⊤ := fun h => by rw [h, Ideal.absNorm_top] at hJ1n; omega
  obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal J1 hJ1t
  have h25 : ((5 : ℕ) : ℤ√(-34)) * ((5 : ℕ) : ℤ√(-34)) ∈ M := by
    have := hJM (natCast_mem hJ1n); push_cast at this ⊢; norm_num; exact this
  have h5 : (5 : ℤ√(-34)) ∈ M := by
    rcases hM.isPrime.mem_or_mem h25 with h | h <;> exact_mod_cast h
  have hxJ1 : x ∈ J1 := mem_right h1
  have hMQ : M = Q := eq_of_cases (hcl M hM.isPrime h5) (hJM hxJ1) hx'
  obtain ⟨J2, h2⟩ := Ideal.dvd_iff_le.2 (hMQ ▸ hJM)
  have hn2 := congrArg Ideal.absNorm h2
  rw [absNorm_mul', hQn, hJ1n] at hn2
  have hJ2n : Ideal.absNorm J2 = 5 := by omega
  have hJ2p := (prime_of_norm (by norm_num) hJ2n).isPrime
  have hxJ2 : x ∈ J2 := (Ideal.mul_le_right : Q * J2 ≤ J2) (h2 ▸ hxJ1)
  have hJ2Q : J2 = Q := eq_of_cases (hcl J2 hJ2p (by exact_mod_cast natCast_mem hJ2n)) hxJ2 hx'
  have e : Q ^ 4 * Ideal.span {2} = Ideal.span {x ^ 2} := by
    rw [← Ideal.span_singleton_pow, h1, h2, hJ2Q, ← Q2sq]; ring
  exact cancel_span (pow_ne_zero 2 hx0) e

lemma Q5pow : (Q5 ^ 4).IsPrincipal :=
  Q5gen (x := 4 - w0) (Ideal.mem_span_pair.2 ⟨2, -1, by ext <;> simp [w0]⟩)
    (by simp [w0]) (fun _ hP h => cl5 hP h) n4m
    (fun h => by have := congrArg Zsqrtd.im h; simp [w0] at this) nQ5

lemma Q5'pow : (Q5' ^ 4).IsPrincipal :=
  Q5gen (x := 4 + w0) (Ideal.mem_span_pair.2 ⟨2, 1, by ext <;> simp [w0]⟩)
    (by simp [w0]) (fun _ hP h => (cl5 hP h).symm) n4p
    (fun h => by have := congrArg Zsqrtd.im h; simp [w0] at this) nQ5'

/-- `(1 ± √-34) = Q5 Q7`, so `Q7 ^ 4` is principal with `Q5 ^ 4`. -/
lemma Q7gen {Q5x Q Q' : Ideal (ℤ√(-34))} {x : ℤ√(-34)} (hx5 : x ∈ Q5x) (hQ5n : Ideal.absNorm Q5x = 5)
    (hxn : x.re ^ 2 + 34 * x.im ^ 2 = 35)
    (hcl : ∀ P : Ideal (ℤ√(-34)), P.IsPrime → (7 : ℤ√(-34)) ∈ P → P = Q ∨ P = Q') (hx' : x ∉ Q')
    (hx0 : x ≠ 0) (h5 : (Q5x ^ 4).IsPrincipal) : (Q ^ 4).IsPrincipal := by
  obtain ⟨J, h1⟩ := div_of_mem hx5
  have hn := congrArg Ideal.absNorm h1
  rw [absNorm_mul', hQ5n, norm_span x 35 hxn] at hn
  have hJn : Ideal.absNorm J = 7 := by omega
  have hJQ : J = Q := eq_of_cases (hcl J (prime_of_norm (by norm_num) hJn).isPrime
    (by exact_mod_cast natCast_mem hJn)) (mem_right h1) hx'
  exact pr_cancel hx0 (by rw [h1, hJQ, mul_comm]) h5

lemma Q7pow : (Q7 ^ 4).IsPrincipal :=
  Q7gen (x := 1 + w0) (Ideal.subset_span (by simp)) nQ5 (by simp [w0]) (fun _ hP h => cl7 hP h) n1p
    (fun h => by have := congrArg Zsqrtd.im h; simp [w0] at this) Q5pow

lemma Q7'pow : (Q7' ^ 4).IsPrincipal :=
  Q7gen (x := 1 - w0) (Ideal.subset_span (by simp)) nQ5' (by simp [w0]) (fun _ hP h => (cl7 hP h).symm)
    n1m (fun h => by have := congrArg Zsqrtd.im h; simp [w0] at this) Q5'pow

/-! ### Every prime of norm at most 11, then every ideal -/

lemma prime_mem {P : Ideal (ℤ√(-34))} (hP : P.IsPrime) :
    ∀ m : ℕ, 2 ≤ m → (m : ℤ√(-34)) ∈ P → ∃ q, q.Prime ∧ q ∣ m ∧ (q : ℤ√(-34)) ∈ P := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm hmP
    have hq := Nat.minFac_prime (show m ≠ 1 by omega)
    obtain ⟨k, hk⟩ := Nat.minFac_dvd m
    rw [hk, Nat.cast_mul] at hmP
    rcases hP.mem_or_mem hmP with h | h
    · exact ⟨_, hq, Nat.minFac_dvd m, h⟩
    · have hk1 : k ≠ 1 := by
        rintro rfl; simp at h; exact hP.ne_top ((Ideal.eq_top_iff_one _).2 h)
      have hk0 : k ≠ 0 := by rintro rfl; omega
      have hq2 := hq.two_le
      have hkm : k < m := by
        rw [hk]; nlinarith
      obtain ⟨q, hq', hqk, hqP⟩ := ih k hkm (by omega) h
      exact ⟨q, hq', hqk.trans ⟨_, by rw [hk, mul_comm]⟩, hqP⟩

lemma small_prime {P : Ideal (ℤ√(-34))} (hP : P.IsPrime) (hb : P ≠ ⊥)
    (hn : Ideal.absNorm P ≤ 11) : (P ^ 4).IsPrincipal := by
  have h0 : Ideal.absNorm P ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have h1 : Ideal.absNorm P ≠ 1 := by rw [Ne, Ideal.absNorm_eq_one_iff]; exact hP.ne_top
  obtain ⟨q, hq, hqd, hqP⟩ := prime_mem hP _ (by omega) (Ideal.absNorm_mem P)
  have hq11 : q ≤ 11 := (Nat.le_of_dvd (by omega) hqd).trans hn
  interval_cases q <;> norm_num at hq
  · rw [cl2 hP (by exact_mod_cast hqP)]; exact Q2pow
  · rw [cl_inert (p := 3) (by norm_num) (by decide) hP hqP]; exact pr_span _
  · rcases cl5 hP (by exact_mod_cast hqP) with h | h <;> rw [h]
    · exact Q5pow
    · exact Q5'pow
  · rcases cl7 hP (by exact_mod_cast hqP) with h | h <;> rw [h]
    · exact Q7pow
    · exact Q7'pow
  · rw [cl_inert (p := 11) (by norm_num) (by decide) hP hqP]; exact pr_span _

lemma all_pow4 : ∀ n : ℕ, ∀ I : Ideal (ℤ√(-34)), Ideal.absNorm I = n → I ≠ ⊥ →
    (I ^ 4).IsPrincipal := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro I hIn hI
    have hn0 : n ≠ 0 := by rw [← hIn]; rwa [Ne, Ideal.absNorm_eq_zero_iff]
    by_cases hn1 : n = 1
    · rw [Ideal.absNorm_eq_one_iff.1 (hIn.trans hn1), Ideal.top_pow]
      exact ⟨⟨1, by rw [Ideal.submodule_span_eq, Ideal.span_singleton_one]⟩⟩
    by_cases hsmall : n ≤ 11
    · have hIt : I ≠ ⊤ := fun h => hn1 (by rw [← hIn, h, Ideal.absNorm_top])
      obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hIt
      obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.2 hIM
      have hn := congrArg Ideal.absNorm hJ
      rw [absNorm_mul', hIn] at hn
      have hMb : M ≠ ⊥ := fun h => hI (le_bot_iff.1 (h ▸ hIM))
      have hM0 : Ideal.absNorm M ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
      have hM1 : Ideal.absNorm M ≠ 1 := by rw [Ne, Ideal.absNorm_eq_one_iff]; exact hM.ne_top
      have hJb : J ≠ ⊥ := by rintro rfl; rw [Ideal.absNorm_bot, mul_zero] at hn; omega
      have hJlt : Ideal.absNorm J < n := by
        rw [hn]; have : 2 ≤ Ideal.absNorm M := by omega
        have : Ideal.absNorm J ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
        have := Nat.mul_lt_mul_of_pos_right (show 1 < Ideal.absNorm M by omega)
          (show 0 < Ideal.absNorm J by omega)
        linarith
      have hMn : Ideal.absNorm M ≤ 11 := (Nat.le_of_dvd (by omega) ⟨_, hn⟩).trans hsmall
      rw [hJ]
      exact pr_mul (small_prime hM.isPrime hMb hMn) (ih _ hJlt J rfl hJb)
    · obtain ⟨x, hxI, hx0, hxb⟩ := exists_small I hI
      obtain ⟨J, hJ⟩ := div_of_mem hxI
      have hn := congrArg Ideal.absNorm hJ
      rw [absNorm_mul', hIn, absNorm_span] at hn
      have hJb : J ≠ ⊥ := by
        rintro rfl; rw [Ideal.mul_bot, Ideal.span_singleton_eq_bot] at hJ; exact hx0 hJ
      have hnn : (0 : ℤ) ≤ x.re ^ 2 + 34 * x.im ^ 2 := by positivity
      have hcast : x.re ^ 2 + 34 * x.im ^ 2 = ((n * Ideal.absNorm J : ℕ) : ℤ) := by
        rw [← hn, Int.natCast_natAbs, abs_of_nonneg hnn]
      rw [hcast, hIn] at hxb
      push_cast at hxb
      have hJ11 : Ideal.absNorm J ≤ 11 := by
        by_contra hc
        push Not at hc
        have : (12 : ℤ) ≤ Ideal.absNorm J := by exact_mod_cast hc
        have : (0 : ℤ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
        nlinarith
      exact pr_cancel hx0 hJ.symm (ih _ (by omega) J rfl hJb)

/-! ### Descent -/

lemma not_two_dvd (p : ℕ) (hp : 2 ≤ p) (n x : ℕ) (hx : n ^ 2 + 34 = x ^ p) : ¬ 2 ∣ x := by
  intro h
  have h4 : 2 ^ 2 ∣ x ^ p := (pow_dvd_pow_of_dvd h 2).trans (pow_dvd_pow x hp)
  rw [← hx] at h4
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩ <;> ring_nf at h4 <;> omega

lemma not_17_dvd (p : ℕ) (hp : 2 ≤ p) (n x : ℕ) (hx : n ^ 2 + 34 = x ^ p) : ¬ 17 ∣ x := by
  intro h
  have h4 : 17 ^ 2 ∣ x ^ p := (pow_dvd_pow_of_dvd h 2).trans (pow_dvd_pow x hp)
  rw [← hx] at h4
  have h17 : 17 ∣ n ^ 2 := by omega
  obtain ⟨m, rfl⟩ := (Nat.prime_iff.mp (by norm_num : Nat.Prime 17)).dvd_of_dvd_pow h17
  ring_nf at h4
  omega

lemma coprime136 (p : ℕ) (hp : 2 ≤ p) (n x : ℕ) (hx : n ^ 2 + 34 = x ^ p) :
    Nat.Coprime (x ^ p) 136 := by
  apply Nat.Coprime.pow_left
  have h2 : Nat.Coprime x 2 :=
    (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (not_two_dvd p hp n x hx)))
  have h17 : Nat.Coprime x 17 :=
    (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 (not_17_dvd p hp n x hx)))
  have : (136 : ℕ) = 2 ^ 3 * 17 := by norm_num
  rw [this]
  exact Nat.Coprime.mul_right (h2.pow_right 3) h17

lemma unit_cases (u : (ℤ√(-34))ˣ) : (u : ℤ√(-34)) = 1 ∨ (u : ℤ√(-34)) = -1 := by
  have hn := (Zsqrtd.norm_eq_one_iff' (by norm_num) (u : ℤ√(-34))).2 u.isUnit
  rw [Zsqrtd.norm_def] at hn
  have him : (u : ℤ√(-34)).im = 0 := by nlinarith [sq_nonneg (u : ℤ√(-34)).re, sq_nonneg (u : ℤ√(-34)).im]
  rw [him] at hn
  have hre : (u : ℤ√(-34)).re = 1 ∨ (u : ℤ√(-34)).re = -1 := by
    have : (u : ℤ√(-34)).re * (u : ℤ√(-34)).re = 1 := by linarith
    rcases Int.eq_one_or_neg_one_of_mul_eq_one this with h | h <;> simp [h]
  rcases hre with h | h
  · left; ext <;> simp [h, him]
  · right; ext <;> simp [h, him]

lemma descent (p : ℕ) (hp : p.Prime) (hp2 : 2 < p) (n x : ℕ) (hx : n ^ 2 + 34 = x ^ p) :
    ∃ z : ℤ√(-34), z ^ p = ⟨n, 1⟩ := by
  set w : ℤ√(-34) := ⟨n, 1⟩ with hw
  have hnorm : w.norm = (x : ℤ) ^ p := by
    rw [Zsqrtd.norm_def, hw]
    have := congrArg (Nat.cast : ℕ → ℤ) hx
    push_cast at this
    simp only
    linarith
  have hprod : w * star w = (x : ℤ√(-34)) ^ p := by
    rw [← Zsqrtd.norm_eq_mul_conj, hnorm]; push_cast; rfl
  have hsq : (w - star w) ^ 2 = -136 := by
    ext <;> simp [hw, sq]
  obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.2 (coprime136 p (by omega) n x hx))
  have huv' := congrArg (Int.cast : ℤ → ℤ√(-34)) huv
  push_cast at huv'
  have hcop : IsCoprime w (star w) :=
    ⟨(u : ℤ√(-34)) * star w + (v : ℤ√(-34)) * (-w + 2 * star w), -(v : ℤ√(-34)) * star w, by
      linear_combination (u : ℤ√(-34)) * hprod - (v : ℤ√(-34)) * hsq + huv'⟩
  have hI : Ideal.span {w} * Ideal.span {star w} = Ideal.span {(x : ℤ√(-34))} ^ p := by
    rw [Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_pow, hprod]
  have hg : IsUnit (gcd (Ideal.span {w}) (Ideal.span {star w})) := by
    rw [Ideal.gcd_eq_sup, (Ideal.isCoprime_iff_sup_eq).1 (Ideal.isCoprime_span_singleton_iff _ _ |>.2 hcop)]
    rw [← Ideal.one_eq_top]; exact isUnit_one
  obtain ⟨I, hIw⟩ := exists_eq_pow_of_mul_eq_pow hg hI
  have hw0 : w ≠ 0 := by intro h; have := congrArg Zsqrtd.im h; simp [hw] at this
  have hI0 : I ≠ ⊥ := by
    rintro rfl
    rw [Ideal.bot_pow (by omega), Ideal.span_singleton_eq_bot] at hIw
    exact hw0 hIw
  have hImem : I ∈ nonZeroDivisors (Ideal (ℤ√(-34))) := mem_nonZeroDivisors_of_ne_zero hI0
  have hc4 : (ClassGroup.mk0 ⟨I, hImem⟩) ^ 4 = 1 := by
    rw [← map_pow, ClassGroup.mk0_eq_one_iff]
    exact all_pow4 _ I rfl hI0
  have hcp : (ClassGroup.mk0 ⟨I, hImem⟩) ^ p = 1 := by
    rw [← map_pow, ClassGroup.mk0_eq_one_iff]
    show (I ^ p).IsPrincipal
    rw [← hIw]
    exact ⟨⟨w, rfl⟩⟩
  have hgcd : Nat.gcd p 4 = 1 := by
    have : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).2 (by omega)
    simpa using this.pow_right 2
  have hc : ClassGroup.mk0 ⟨I, hImem⟩ = 1 := by
    simpa [hgcd] using (pow_gcd_eq_one.2 ⟨hcp, hc4⟩ : (ClassGroup.mk0 ⟨I, hImem⟩) ^ Nat.gcd p 4 = 1)
  obtain ⟨z0, hz0⟩ := ((ClassGroup.mk0_eq_one_iff hImem).1 hc)
  rw [hz0, Ideal.submodule_span_eq, Ideal.span_singleton_pow,
    Ideal.span_singleton_eq_span_singleton] at hIw
  obtain ⟨e, he⟩ := hIw
  rcases unit_cases e with h | h
  · exact ⟨z0, by rw [← he, h, mul_one]⟩
  · refine ⟨-z0, ?_⟩
    rw [Odd.neg_pow (hp.odd_of_ne_two (by omega)), ← he, h]
    ring
lemma pow_two_pow (a : ℤ) (ha : Odd a) : ∀ k : ℕ, ∃ α u : ℤ, Odd α ∧ Odd u ∧
    (⟨a, 1⟩ : ℤ√(-34)) ^ (2 ^ k) = ⟨α, 2 ^ k * u⟩ := by
  intro k
  induction k with
  | zero => exact ⟨a, 1, ha, odd_one, by simp⟩
  | succ k ih =>
    obtain ⟨α, u, hα, hu, h⟩ := ih
    refine ⟨α ^ 2 - 34 * (2 ^ k * u) ^ 2, α * u, ?_, hα.mul hu, ?_⟩
    · have he : Even (34 * (2 ^ k * u) ^ 2) := ⟨17 * (2 ^ k * u) ^ 2, by ring⟩
      exact hα.pow.sub_even he
    · rw [pow_succ, pow_mul, h]
      ext <;> simp [sq] <;> ring

lemma pow_mul_odd (ρ : ℕ) (α u : ℤ) (hα : Odd α) (hu : Odd u) : ∀ n : ℕ, ∃ A c : ℤ,
    Odd A ∧ 2 ∣ c - n ∧ (⟨α, 2 ^ ρ * u⟩ : ℤ√(-34)) ^ n = ⟨A, 2 ^ ρ * c⟩ := by
  intro n
  induction n with
  | zero => exact ⟨1, 0, odd_one, by simp, by ext <;> simp⟩
  | succ n ih =>
    obtain ⟨A, c, hA, hc, h⟩ := ih
    refine ⟨A * α - 34 * (2 ^ ρ * c) * (2 ^ ρ * u), A * u + c * α, ?_, ?_, ?_⟩
    · have he : Even (34 * (2 ^ ρ * c) * (2 ^ ρ * u)) :=
        ⟨17 * (2 ^ ρ * c) * (2 ^ ρ * u), by ring⟩
      exact (hA.mul hα).sub_even he
    · obtain ⟨s, hs⟩ := hA.mul hu
      obtain ⟨t, ht⟩ := hα
      obtain ⟨r, hr⟩ := hc
      exact ⟨s + c * t + r, by push_cast; linear_combination hs + c * ht + hr⟩
    · rw [pow_succ, h]
      ext <;> simp <;> ring

lemma two_pow_dvd (N : ℤ) (hN : Odd N) : ∀ k : ℕ, (2 : ℤ) ^ (k + 3) ∣ N ^ (2 ^ (k + 1)) - 1 := by
  intro k
  induction k with
  | zero =>
    obtain ⟨t, rfl⟩ := hN
    obtain ⟨s, hs⟩ := Int.even_mul_succ_self t
    exact ⟨s, by norm_num; linear_combination 4 * hs⟩
  | succ k ih =>
    obtain ⟨q, hq⟩ := ih
    refine ⟨q * (2 ^ (k + 2) * q + 1), ?_⟩
    rw [pow_succ 2 (k + 1), pow_mul]
    linear_combination (N ^ 2 ^ (k + 1) + 1 + 2 ^ (k + 3) * q) * hq

/-- The case `p ≡ 1 (mod 4)`: a `2`-adic argument. -/
lemma case_one_mod_four (a : ℤ) (ha : Odd a) (p : ℕ) (hp1 : 1 < p) (hp : p % 4 = 1) (ε : ℤ)
    (hε : ε = 1 ∨ ε = -1) : ((⟨a, 1⟩ : ℤ√(-34)) ^ p).im ≠ ε := by
  intro him
  obtain ⟨ρ, m, hm, hpm⟩ := Nat.exists_eq_two_pow_mul_odd (n := p - 1) (by omega)
  have hρ : 2 ≤ ρ := by
    rcases ρ with _ | _ | ρ
    · obtain ⟨j, rfl⟩ := hm; simp at hpm; omega
    · obtain ⟨j, rfl⟩ := hm; simp at hpm; omega
    · omega
  obtain ⟨α, u, hα, hu, h2⟩ := pow_two_pow a ha ρ
  obtain ⟨A, c, hA, hc, hw⟩ := pow_mul_odd ρ α u hα hu m
  have hzp : (⟨a, 1⟩ : ℤ√(-34)) ^ (p - 1) = ⟨A, 2 ^ ρ * c⟩ := by
    rw [hpm, pow_mul, h2, hw]
  have hz : (⟨a, 1⟩ : ℤ√(-34)) ^ p = ⟨A, 2 ^ ρ * c⟩ * ⟨a, 1⟩ := by
    rw [← hzp, ← pow_succ]; congr 1; omega
  have hcodd : Odd c := by
    obtain ⟨j, hj⟩ := hm
    obtain ⟨r, hr⟩ := hc
    exact ⟨r + j, by rw [hj] at hr; push_cast at hr; linarith⟩
  have hn : Zsqrtd.norm ((⟨a, 1⟩ : ℤ√(-34)) ^ (p - 1)) =
      (Zsqrtd.norm (⟨a, 1⟩ : ℤ√(-34))) ^ (p - 1) :=
    map_pow (Zsqrtd.normMonoidHom (d := -34)) _ _
  rw [hzp] at hn
  simp only [Zsqrtd.norm_def] at hn
  rw [hz] at him
  simp at him
  -- `K = 2 ^ ρ = 4 L`
  obtain ⟨L, hL⟩ : ∃ L : ℤ, (2 : ℤ) ^ ρ = 4 * L :=
    ⟨2 ^ (ρ - 2), by rw [show ρ = (ρ - 2) + 2 by omega, pow_add]; norm_num; ring⟩
  have hdiv : (2 : ℤ) ^ (ρ + 2) ∣ (a * a - -34 * 1 * 1) ^ (p - 1) - 1 := by
    have h1 := two_pow_dvd (a * a - -34 * 1 * 1) (by
      have : Odd (a * a) := ha.mul ha
      exact this.sub_even ⟨-17, by ring⟩) (ρ - 1)
    rw [show ρ - 1 + 3 = ρ + 2 by omega, show ρ - 1 + 1 = ρ by omega] at h1
    refine h1.trans ?_
    rw [hpm, pow_mul]
    have := sub_dvd_pow_sub_pow ((a * a - -34 * 1 * 1) ^ 2 ^ ρ) 1 m
    rwa [one_pow] at this
  obtain ⟨q, hq⟩ := hdiv
  set K : ℤ := 2 ^ ρ with hK
  set P : ℤ := (a * a - -34 * 1 * 1) ^ (p - 1) with hP
  have hε2 : ε ^ 2 = 1 := by rcases hε with rfl | rfl <;> norm_num
  have h4K : (2 : ℤ) ^ (ρ + 2) = 4 * K := by rw [hK, pow_add]; ring
  rw [h4K] at hq
  have key : 2 * K * (ε * c * a) = 2 * K * (2 * (L * (c ^ 2 * a ^ 2 + 34 * c ^ 2) - q)) := by
    linear_combination hε2 + K * (c ^ 2 * a ^ 2 + 34 * c ^ 2) * hL
      + (A + ε - K * c * a) * him - hn - hq
  have hKne : (2 : ℤ) * K ≠ 0 := by rw [hK]; positivity
  have key2 := mul_left_cancel₀ hKne key
  have hodd : Odd (ε * c * a) := by
    have : Odd ε := by rcases hε with rfl | rfl <;> decide
    exact (this.mul hcodd).mul ha
  exact (Int.not_even_iff_odd.2 hodd) ⟨L * (c ^ 2 * a ^ 2 + 34 * c ^ 2) - q, by rw [key2]; ring⟩

lemma pow8 (a : ℤ) : (⟨a, 1⟩ : ℤ√(-34)) ^ 8 =
    ⟨a ^ 8 - 952 * a ^ 6 + 80920 * a ^ 4 - 1100512 * a ^ 2 + 1336336,
      8 * a ^ 7 - 1904 * a ^ 5 + 64736 * a ^ 3 - 314432 * a⟩ := by
  ext <;> simp [pow_succ] <;> ring

lemma pow3_im (a : ℤ) : ((⟨a, 1⟩ : ℤ√(-34)) ^ 3).im = 3 * a ^ 2 - 34 := by
  simp [pow_succ]; ring

lemma pow7_im (a : ℤ) : ((⟨a, 1⟩ : ℤ√(-34)) ^ 7).im =
    7 * a ^ 6 - 1190 * a ^ 4 + 24276 * a ^ 2 - 39304 := by
  simp [pow_succ]; ring

lemma dvd24_pow8 (a : ℤ) (ha : Odd a) : (24 : ℤ√(-34)) ∣ (⟨a, 1⟩ : ℤ√(-34)) ^ 8 - 1 := by
  have h := (Zsqrtd.intCast_dvd (d := -34) 24 ((⟨a, 1⟩ : ℤ√(-34)) ^ 8 - 1)).2
  push_cast at h
  apply h
  rw [pow8]
  simp only [Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_one, Zsqrtd.im_one]
  obtain ⟨b, rfl⟩ := ha
  constructor
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 24).1; push_cast
    generalize (b : ZMod 24) = x; revert x; decide
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 24).1; push_cast
    generalize (b : ZMod 24) = x; revert x; decide

lemma dvd24_im (a : ℤ) (ha : Odd a) (p : ℕ) :
    (24 : ℤ) ∣ ((⟨a, 1⟩ : ℤ√(-34)) ^ p).im - ((⟨a, 1⟩ : ℤ√(-34)) ^ (p % 8)).im := by
  have hd : (24 : ℤ√(-34)) ∣ (⟨a, 1⟩ : ℤ√(-34)) ^ p - (⟨a, 1⟩ : ℤ√(-34)) ^ (p % 8) := by
    have e : (⟨a, 1⟩ : ℤ√(-34)) ^ p - (⟨a, 1⟩ : ℤ√(-34)) ^ (p % 8) =
        (((⟨a, 1⟩ : ℤ√(-34)) ^ 8) ^ (p / 8) - 1 ^ (p / 8)) * (⟨a, 1⟩ : ℤ√(-34)) ^ (p % 8) := by
      rw [one_pow, sub_mul, one_mul, ← pow_mul, ← pow_add, Nat.div_add_mod]
    rw [e]
    exact Dvd.dvd.mul_right ((dvd24_pow8 a ha).trans (sub_dvd_pow_sub_pow _ _ _)) _
  have := ((Zsqrtd.intCast_dvd (d := -34) 24 _).1 (by exact_mod_cast hd)).2
  simpa using this

/-- The case `p ≡ 3 (mod 4)`: a congruence modulo `24`. -/
lemma case_three_mod_four (a : ℤ) (ha : Odd a) (p : ℕ) (hp : p % 4 = 3) (ε : ℤ)
    (hε : ε = 1 ∨ ε = -1) : ((⟨a, 1⟩ : ℤ√(-34)) ^ p).im ≠ ε := by
  intro him
  have h := dvd24_im a ha p
  rw [him] at h
  obtain ⟨b, rfl⟩ := ha
  have h8 : p % 8 = 3 ∨ p % 8 = 7 := by omega
  rcases h8 with h8 | h8 <;> rw [h8] at h
  · rw [pow3_im] at h
    replace h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 24).2 (by exact_mod_cast h)
    push_cast at h
    rcases hε with rfl | rfl <;> push_cast at h <;> revert h <;>
      generalize (b : ZMod 24) = x <;> revert x <;> decide
  · rw [pow7_im] at h
    replace h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 24).2 (by exact_mod_cast h)
    push_cast at h
    rcases hε with rfl | rfl <;> push_cast at h <;> revert h <;>
      generalize (b : ZMod 24) = x <;> revert x <;> decide


/-! ### Cohn's elementary argument -/

lemma im_dvd (z : ℤ√(-34)) : ∀ n : ℕ, z.im ∣ (z ^ (n + 1)).im := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Zsqrtd.im_mul]
    exact dvd_add (dvd_mul_left _ _) (dvd_mul_of_dvd_left ih _)

lemma im_eq_unit (z : ℤ√(-34)) {n : ℕ} (hn : 1 ≤ n) (h : (z ^ n).im = 1) :
    z.im = 1 ∨ z.im = -1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hd := im_dvd z k
  rw [h] at hd
  rcases Int.isUnit_iff.1 (isUnit_of_dvd_one hd) with h' | h' <;> simp [h']

lemma two_dvd_im_pow (z : ℤ√(-34)) (ha : (2 : ℤ) ∣ z.re) (n : ℕ) (hn : 2 ≤ n) :
    (2 : ℤ) ∣ (z ^ n).im := by
  have h2 : (2 : ℤ√(-34)) ∣ z ^ 2 := by
    have := (Zsqrtd.intCast_dvd (d := -34) 2 (z ^ 2)).2
    push_cast at this
    apply this
    obtain ⟨c, hc⟩ := ha
    refine ⟨⟨2 * c ^ 2 - 17 * z.im ^ 2, by simp [sq, hc]; ring⟩, ⟨2 * c * z.im, by simp [sq, hc]; ring⟩⟩
  have hd : (2 : ℤ√(-34)) ∣ z ^ n := h2.trans (pow_dvd_pow z hn)
  exact ((Zsqrtd.intCast_dvd (d := -34) 2 _).1 (by exact_mod_cast hd)).2

/-- No odd power `p > 1` in `ℤ[√-34]` has `√-34`-coefficient `1`. -/
lemma im_pow_ne_one (p : ℕ) (hp : p % 2 = 1) (hp1 : 1 < p) (z : ℤ√(-34)) : (z ^ p).im ≠ 1 := by
  intro h
  have ha : Odd z.re := by
    refine Int.not_even_iff_odd.1 (fun he => ?_)
    have := two_dvd_im_pow z he.two_dvd p (by omega)
    rw [h] at this
    omega
  have key : ∀ ε : ℤ, (ε = 1 ∨ ε = -1) → ((⟨z.re, 1⟩ : ℤ√(-34)) ^ p).im ≠ ε := by
    intro ε hε
    rcases (by omega : p % 4 = 1 ∨ p % 4 = 3) with h4 | h4
    · exact case_one_mod_four z.re ha p hp1 h4 ε hε
    · exact case_three_mod_four z.re ha p h4 ε hε
  rcases im_eq_unit z (by omega) h with hb | hb
  · have hz : z = ⟨z.re, 1⟩ := by ext <;> simp [hb]
    rw [hz] at h
    exact key 1 (Or.inl rfl) h
  · have hz : star z = ⟨z.re, 1⟩ := by ext <;> simp [hb]
    have hs : ((star z) ^ p).im = -1 := by
      rw [← star_pow, Zsqrtd.im_star, h]
    rw [hz] at hs
    exact key (-1) (Or.inr rfl) hs

/-- Squares are `0` or `1` mod 4, `n ^ 2 + 34` is `2` or `3` mod 4. -/
lemma sq_add_34_ne_sq (n y : ℕ) : n ^ 2 + 34 ≠ y ^ 2 := by
  intro h
  have h4 : ((n ^ 2 + 34 : ℕ) : ZMod 4) = ((y ^ 2 : ℕ) : ZMod 4) := by rw [h]
  push_cast at h4
  generalize (n : ZMod 4) = u at h4
  generalize (y : ZMod 4) = v at h4
  revert u v
  decide

end OMA.A114965

open OMA.A114965 in
theorem OMA.solution : type_of% @OMA.S_oeis_a114965.main := by
  intro n x k hk hx
  simp only [OMA.S_oeis_a114965.a] at hx
  rcases Nat.even_or_odd k with ⟨m, rfl⟩ | hodd
  · exact sq_add_34_ne_sq n (x ^ m) (by rw [hx]; ring)
  · have hp : k.minFac.Prime := Nat.minFac_prime (by omega)
    have hp2 : 2 < k.minFac := by
      rcases hp.two_le.lt_or_eq with h | h
      · exact h
      · exfalso
        have h2k : 2 ∣ k := h ▸ Nat.minFac_dvd k
        exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2k)
    obtain ⟨m, hm⟩ := Nat.minFac_dvd k
    have hx' : n ^ 2 + 34 = (x ^ m) ^ k.minFac := by
      rw [hx, ← pow_mul, mul_comm, ← hm]
    obtain ⟨z, hz⟩ := descent _ hp hp2 n (x ^ m) hx'
    have hpo : k.minFac % 2 = 1 := Nat.odd_iff.1 (hp.odd_of_ne_two (by omega))
    exact im_pow_ne_one _ hpo (by omega) z (by rw [hz])
