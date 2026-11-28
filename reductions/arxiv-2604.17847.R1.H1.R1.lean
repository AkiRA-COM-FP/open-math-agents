import OMAReductions.R_arxiv_2604_17847_R1

-- Reduction of the finite-cover step from PR 20911 and board note 93655.
-- Credit: @wispiANt

namespace OMA.R_arxiv_2604_17847_R1_H1_R1

open OMA.S_arxiv_2604_17847
open OMA.R_arxiv_2604_17847_R1 (finite_prime_cover_iff fixed_rank_family totient_fib_witness)

-- When the common Fibonacci factor is prime to q, the quotient must avoid q².
def H1 : Prop :=
  ∀ q r : ℕ, q.Prime → 53 < q → r < pisano q → ¬ q ∣ (Nat.fib (pisano q)).totient →
    let g := r.gcd (pisano q)
    ¬ q ∣ Nat.fib g → ∃ t : ℕ, 0 < t ∧ g * t ≡ r [MOD pisano q] ∧
      let c := Nat.fib (g * t) / Nat.fib g
      ¬ q ^ 2 ∣ c ∧ ∀ p : ℕ, p.Prime → p ≡ 1 [MOD q] → ¬ p ∣ c

-- When the common factor supplies one copy of q, the multiplier must avoid q.
def H2 : Prop :=
  ∀ q r : ℕ, q.Prime → 53 < q → r < pisano q → ¬ q ∣ (Nat.fib (pisano q)).totient →
    let g := r.gcd (pisano q)
    q ∣ Nat.fib g → ∃ t : ℕ, 0 < t ∧ g * t ≡ r [MOD pisano q] ∧
      let c := Nat.fib (g * t) / Nat.fib g
      ¬ q ∣ t ∧ ∀ p : ℕ, p.Prime → p ≡ 1 [MOD q] → ¬ p ∣ c

lemma gcd_dvd_class {r P m : ℕ} (hm : m ≡ r [MOD P]) : r.gcd P ∣ m :=
  Nat.modEq_zero_iff_dvd.mp ((hm.of_dvd (Nat.gcd_dvd_right _ _)).trans
    (Nat.gcd_dvd_left _ _).modEq_zero_nat)

lemma fib_quotient_product (g t : ℕ) :
    Nat.fib g * (Nat.fib (g * t) / Nat.fib g) = Nat.fib (g * t) :=
  Nat.mul_div_cancel' (Nat.fib_dvd _ _ (dvd_mul_right g t))

-- Dividing out the common factor preserves strong divisibility in the multiplier.
lemma gcd_fib_quotients {g : ℕ} (hg : 0 < g) (a b : ℕ) :
    (Nat.fib (g * a) / Nat.fib g).gcd (Nat.fib (g * b) / Nat.fib g) =
      Nat.fib (g * a.gcd b) / Nat.fib g := by
  apply Nat.eq_of_mul_eq_mul_left (Nat.fib_pos.mpr hg)
  rw [← Nat.gcd_mul_left, fib_quotient_product, fib_quotient_product, ← Nat.fib_gcd,
    Nat.gcd_mul_left, fib_quotient_product]

lemma coprime_fib_quotients {g a b : ℕ} (hg : 0 < g) (hab : a.Coprime b) :
    (Nat.fib (g * a) / Nat.fib g).Coprime (Nat.fib (g * b) / Nat.fib g) := by
  change _ = 1
  rw [gcd_fib_quotients hg, hab.gcd_eq_one, Nat.mul_one, Nat.div_self (Nat.fib_pos.mpr hg)]

-- At a zero index modulo q, the common factor has been removed exactly once
-- in forming the quotient. The remaining divisibility by q is read from t.
lemma prime_dvd_quotient_iff {q g : ℕ} (hq : q.Prime) (hg : 0 < g)
    (hz : q ∣ Nat.fib g) (t : ℕ) : q ∣ Nat.fib (g * t) / Nat.fib g ↔ q ∣ t := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hg.ne'
  let g := k + 1
  change q ∣ Nat.fib g at hz
  let u : ZMod q := Nat.fib (g + 1)
  let : Fact q.Prime := ⟨hq⟩
  have zero : (Nat.fib g : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff ..).mpr hz
  have unit : u ≠ 0 := by
    intro h
    have hd := (ZMod.natCast_eq_zero_iff (Nat.fib (g + 1)) q).mp h
    exact hq.not_dvd_one (by simpa only [(Nat.fib_coprime_fib_succ g).gcd_eq_one] using Nat.dvd_gcd hz hd)
  have prev : (Nat.fib k : ZMod q) = u := by
    change _ = (Nat.fib (k + 2) : ZMod q)
    rw [Nat.fib_add_two, Nat.cast_add, zero, add_zero]
  have neighbor (s : ℕ) : (Nat.fib (g * s + 1) : ZMod q) = u ^ s := by
    induction s with
    | zero => simp
    | succ s ih =>
      rw [Nat.mul_succ, Nat.fib_add, Nat.cast_add, Nat.cast_mul, Nat.cast_mul, zero, ih, pow_succ]
      simp [u]
  let c := fun s => Nat.fib (g * s) / Nat.fib g
  have step (s : ℕ) : c (s + 1) = c s * Nat.fib k + Nat.fib (g * s + 1) := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.fib_pos.mpr hg)
    change Nat.fib g * (Nat.fib (g * (s + 1)) / Nat.fib g) = _
    rw [fib_quotient_product, Nat.mul_succ, Nat.mul_add, ← Nat.mul_assoc]
    change Nat.fib (g * s + (k + 1)) = Nat.fib g * (Nat.fib (g * s) / Nat.fib g) * _ + _
    rw [fib_quotient_product, ← Nat.add_assoc, Nat.fib_add]
    simp only [g, Nat.mul_comm]
  have coefficient (s : ℕ) : (c s : ZMod q) * u = (s : ZMod q) * u ^ s := by
    induction s with
    | zero => simp [c]
    | succ s ih =>
      rw [step, Nat.cast_add, Nat.cast_mul, prev, neighbor, Nat.cast_succ, pow_succ]
      linear_combination u * ih
  rw [← ZMod.natCast_eq_zero_iff, ← ZMod.natCast_eq_zero_iff]
  change (c t : ZMod q) = 0 ↔ (t : ZMod q) = 0
  have eq := coefficient t
  constructor
  · intro h
    rw [h, zero_mul] at eq
    exact (mul_eq_zero.mp eq.symm).resolve_right (pow_ne_zero _ unit)
  · intro h
    rw [h, zero_mul] at eq
    exact (mul_eq_zero.mp eq).resolve_right unit

lemma totient_witness_iff {q n : ℕ} (hq : q.Prime) (hn : 0 < n) :
    q ∣ (Nat.fib n).totient ↔ q ^ 2 ∣ Nat.fib n ∨
      ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD q] ∧ p ∣ Nat.fib n := by
  constructor
  · intro h
    rcases totient_fib_witness hq h with hs | ⟨p, hp, hc, hd⟩
    · exact Or.inl hs
    · have pos := Nat.pos_of_dvd_of_pos hd hn
      have ex := Nat.nonempty_of_pos_sInf (s := {k : ℕ | 0 < k ∧ p ∣ Nat.fib k}) pos
      have first : 0 < rankOfApparition p ∧ p ∣ Nat.fib (rankOfApparition p) := Nat.sInf_mem ex
      exact Or.inr ⟨p, hp, hc, first.2.trans (Nat.fib_dvd _ _ hd)⟩
  · rintro (hs | ⟨p, hp, hc, hd⟩)
    · have h : q ∣ (q ^ 2).totient := by
        rw [Nat.totient_prime_pow_succ hq 1, pow_one]
        exact dvd_mul_right _ _
      exact h.trans (Nat.totient_dvd_of_dvd hs)
    · have h : q ∣ p.totient := by rw [Nat.totient_prime hp]; exact hc.symm.dvd'
      exact h.trans (Nat.totient_dvd_of_dvd hd)

lemma square_in_product {q a c : ℕ} (hq : q.Prime) (hs : ¬ q ^ 2 ∣ a) :
    q ^ 2 ∣ a * c ↔ (if q ∣ a then q else q ^ 2) ∣ c := by
  split_ifs with ha
  · obtain ⟨b, rfl⟩ := ha
    have hb : ¬ q ∣ b := fun h => hs (by simpa [pow_two] using Nat.mul_dvd_mul_left q h)
    rw [pow_two, Nat.mul_assoc]
    constructor
    · intro h
      exact (hq.coprime_iff_not_dvd.mpr hb).dvd_of_dvd_mul_left (Nat.dvd_of_mul_dvd_mul_left hq.pos h)
    · intro h
      exact Nat.mul_dvd_mul_left _ (dvd_mul_of_dvd_right h _)
  · exact ⟨((hq.coprime_iff_not_dvd.mpr ha).pow_left 2).dvd_of_dvd_mul_left,
      fun h => dvd_mul_of_dvd_right h _⟩

lemma quotient_exception_iff {q g P t : ℕ} (hq : q.Prime) (hP : 0 < P)
    (hgP : g ∣ P) (ht : 0 < t) (hbad : ¬ q ∣ (Nat.fib P).totient) :
    let c := Nat.fib (g * t) / Nat.fib g
    (¬ q ∣ (Nat.fib (g * t)).totient) ↔
      (¬ (if q ∣ Nat.fib g then q else q ^ 2) ∣ c) ∧
        ∀ p : ℕ, p.Prime → p ≡ 1 [MOD q] → ¬ p ∣ c := by
  dsimp only
  have hg := Nat.pos_of_dvd_of_pos hgP hP
  have common := Nat.fib_dvd _ _ hgP
  have badg : ¬ q ∣ (Nat.fib g).totient :=
    fun h => hbad (h.trans (Nat.totient_dvd_of_dvd common))
  rw [totient_witness_iff hq hg, not_or] at badg
  rw [totient_witness_iff hq (Nat.mul_pos hg ht), ← fib_quotient_product g t,
    not_or, square_in_product hq badg.1, Nat.mul_div_cancel_left _ (Nat.fib_pos.mpr hg)]
  constructor
  · rintro ⟨hs, hp⟩
    exact ⟨hs, fun p hpr hc hd => hp ⟨p, hpr, hc, dvd_mul_of_dvd_right hd _⟩⟩
  · rintro ⟨hs, hp⟩
    refine ⟨hs, ?_⟩
    rintro ⟨p, hpr, hc, hd⟩
    rcases hpr.dvd_mul.mp hd with ha | hb
    · exact badg.2 ⟨p, hpr, hc, ha⟩
    · exact hp p hpr hc hb

-- An exception has positive index since the totient at index zero is zero.
lemma exception_multiplier {q r P : ℕ}
    (h : ¬ ∀ m : ℕ, m ≡ r [MOD P] → q ∣ (Nat.fib m).totient) :
    ∃ t : ℕ, 0 < t ∧ r.gcd P * t ≡ r [MOD P] ∧ ¬ q ∣ (Nat.fib (r.gcd P * t)).totient := by
  push Not at h
  obtain ⟨m, hm, hbad⟩ := h
  obtain ⟨t, rfl⟩ := gcd_dvd_class hm
  refine ⟨t, Nat.pos_of_ne_zero ?_, hm, hbad⟩
  rintro rfl
  simp at hbad

theorem main : H1 → H2 → OMA.R_arxiv_2604_17847_R1.H1 := by
  intro first second q r hq hlarge hr _
  have hP := Nat.zero_lt_of_lt hr.1
  apply (finite_prime_cover_iff hq hP).mpr
  by_contra hbad
  let g := r.gcd (pisano q)
  have fail (t : ℕ) (ht : 0 < t) (hc : g * t ≡ r [MOD pisano q]) :=
    mt (quotient_exception_iff hq hP (Nat.gcd_dvd_right r _) ht hbad).mpr
      (not_not_intro (hr.2 _ hc))
  by_cases hd : q ∣ Nat.fib (r.gcd (pisano q))
  · obtain ⟨t, ht, hc, hs, hp⟩ := second q r hq hlarge hr.1 hbad hd
    have hg := Nat.gcd_pos_of_pos_right r hP
    have no := mt (prime_dvd_quotient_iff hq hg hd t).mp hs
    exact fail t ht hc ⟨by simpa only [if_pos hd] using no, hp⟩
  · obtain ⟨t, ht, hc, hs, hp⟩ := first q r hq hlarge hr.1 hbad hd
    exact fail t ht hc ⟨by simpa only [if_neg hd] using hs, hp⟩

-- Conversely, failure of descent supplies the recurring rank family used by the parent.
lemma quotient_problems_of_cover (cover : OMA.R_arxiv_2604_17847_R1.H1) : H1 ∧ H2 := by
  have pick (q r : ℕ) (hq : q.Prime) (hl : 53 < q) (hr : r < pisano q)
      (hbad : ¬ q ∣ (Nat.fib (pisano q)).totient) :
      let g := r.gcd (pisano q)
      ∃ t : ℕ, 0 < t ∧ g * t ≡ r [MOD pisano q] ∧
        (¬ (if q ∣ Nat.fib g then q else q ^ 2) ∣ (Nat.fib (g * t) / Nat.fib g)) ∧
        ∀ p : ℕ, p.Prime → p ≡ 1 [MOD q] → ¬ p ∣ (Nat.fib (g * t) / Nat.fib g) := by
    have hP := Nat.zero_lt_of_lt hr
    have missing : ¬ ∀ m : ℕ, m ≡ r [MOD pisano q] → q ∣ (Nat.fib m).totient := by
      intro hall
      have good : r ∈ S q := ⟨hr, hall⟩
      exact hbad ((finite_prime_cover_iff hq hP).mp (cover q r hq hl good (fixed_rank_family hq good hbad)))
    obtain ⟨t, ht, hc, he⟩ := exception_multiplier missing
    exact ⟨t, ht, hc, (quotient_exception_iff hq hP (Nat.gcd_dvd_right r _) ht hbad).mp he⟩
  constructor
  · intro q r hq hl hr hbad
    dsimp only
    intro hd
    simpa only [if_neg hd] using pick q r hq hl hr hbad
  · intro q r hq hl hr hbad
    dsimp only
    intro hd
    obtain ⟨t, ht, hc, hs, hp⟩ := pick q r hq hl hr hbad
    rw [if_pos hd, prime_dvd_quotient_iff hq (Nat.gcd_pos_of_pos_right r (Nat.zero_lt_of_lt hr)) hd] at hs
    exact ⟨t, ht, hc, hs, hp⟩

end OMA.R_arxiv_2604_17847_R1_H1_R1
