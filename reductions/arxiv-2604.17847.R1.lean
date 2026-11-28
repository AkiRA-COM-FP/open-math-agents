import OMAStatements.S_arxiv_2604_17847
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Tactic.NormNum.Prime

namespace OMA.R_arxiv_2604_17847_R1

open OMA.S_arxiv_2604_17847

-- It suffices to find a finite cover in the case of a recurring prime-index rank family.
def H1 : Prop :=
  ∀ q r : ℕ, q.Prime → 31 < q → r ∈ S q →
    (∃ e : ℕ, e ∣ r.gcd (pisano q) ∧ ∀ B : ℕ, ∃ l > B, ∃ p > B,
      l.Prime ∧ r.gcd (pisano q) * l ≡ r [MOD pisano q] ∧
      p.Prime ∧ p ≡ 1 [MOD q] ∧ rankOfApparition p = e * l) →
    ∃ (r : ℕ) (W : Finset ℕ), r < pisano q ∧
      ∀ m : ℕ, 0 < m → m ≡ r [MOD pisano q] → q ^ 2 ∣ Nat.fib m ∨
        ∃ p ∈ W, p.Prime ∧ p ≡ 1 [MOD q] ∧ p ∣ Nat.fib m

-- Isolate the exceptional square-divisibility case at the period.
def H2 : Prop :=
  ∀ q : ℕ, q.Prime → 31 < q → q ^ 2 ∣ Nat.fib (pisano q) →
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD q] ∧ rankOfApparition p ∣ pisano q

-- The gcd argument follows the proof for OEIS A000032 (project PR 9447).
lemma rank_dvd_index {p n : ℕ} (hn : 0 < n) (hpn : p ∣ Nat.fib n) :
    rankOfApparition p ∣ n := by
  let indices : Set ℕ := {k | 0 < k ∧ p ∣ Nat.fib k}
  have hr : sInf indices ∈ indices := Nat.sInf_mem ⟨n, hn, hpn⟩
  obtain ⟨hrpos, hpr⟩ : 0 < sInf indices ∧ p ∣ Nat.fib (sInf indices) := hr
  have hg : Nat.gcd (sInf indices) n ∈ indices := by
    refine ⟨Nat.gcd_pos_of_pos_left _ hrpos, ?_⟩
    rw [Nat.fib_gcd]
    exact Nat.dvd_gcd hpr hpn
  have heq := le_antisymm (Nat.gcd_le_left n hrpos) (Nat.sInf_le hg)
  change sInf indices ∣ n
  simpa only [heq] using Nat.gcd_dvd_right (sInf indices) n

-- Adapt the totient factorization argument of the Erdős 1003 proof (project PR 6554).
lemma totient_fib_witness {q n : ℕ} (hq : q.Prime) (hd : q ∣ Nat.totient (Nat.fib n)) :
    q ^ 2 ∣ Nat.fib n ∨
      ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD q] ∧ rankOfApparition p ∣ n := by
  by_cases hz : Nat.fib n = 0
  · left
    rw [hz]
    exact dvd_zero _
  have hn : 0 < n := Nat.fib_pos.mp (Nat.pos_of_ne_zero hz)
  rw [Nat.totient_eq_prod_factorization hz, Finsupp.prod, Nat.support_factorization] at hd
  obtain ⟨p, hp, hfactor⟩ := (hq.prime.dvd_finsetProd_iff _).mp hd
  have hpPrime := Nat.prime_of_mem_primeFactors hp
  have hpFib := Nat.dvd_of_mem_primeFactors hp
  obtain ⟨a, ha⟩ := Nat.exists_eq_succ_of_ne_zero
    (hpPrime.factorization_pos_of_dvd hz hpFib).ne'
  rw [ha, Nat.succ_sub_one] at hfactor
  rcases hq.dvd_mul.mp hfactor with hpower | hpred
  · have heq := (Nat.prime_dvd_prime_iff_eq hq hpPrime).mp (hq.dvd_of_dvd_pow hpower)
    subst p
    have hapos : a ≠ 0 := by
      intro he
      simp [he, hq.not_dvd_one] at hpower
    exact Or.inl ((pow_dvd_pow q (by omega : 2 ≤ (Nat.fib n).factorization q)).trans
      (Nat.ordProj_dvd (Nat.fib n) q))
  · exact Or.inr ⟨p, hpPrime, ((Nat.modEq_iff_dvd' hpPrime.one_lt.le).2 hpred).symm,
      rank_dvd_index hn hpFib⟩

-- The product contains precisely the primes dividing L that do not divide a.
lemma coprime_representative {a b L : ℕ} (hab : a.Coprime b) (hb : 0 < b) (hL : 0 < L) :
    ∃ t : ℕ, 0 < t ∧ t ≡ a [MOD b] ∧ L.Coprime t := by
  let primes := L.primeFactors.filter fun p => ¬ p ∣ a
  let k := primes.prod id
  have hk : 0 < k := Finset.prod_pos fun p hp =>
    (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos
  refine ⟨a + k * b, Nat.add_pos_right _ (Nat.mul_pos hk hb), Nat.add_mul_modulus_modEq_iff.mpr rfl, ?_⟩
  apply Nat.coprime_of_dvd
  intro p hp hpL hpt
  by_cases hpa : p ∣ a
  · have hpkb := (Nat.dvd_add_iff_right hpa).mpr hpt
    rcases hp.dvd_mul.mp hpkb with hpk | hpb
    · obtain ⟨s, hs, hps⟩ := (hp.prime.dvd_finsetProd_iff id).mp hpk
      have hsPrime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hs).1
      have heq := (Nat.prime_dvd_prime_iff_eq hp hsPrime).mp hps
      exact (Finset.mem_filter.mp hs).2 (heq ▸ hpa)
    · exact hp.ne_one (Nat.eq_one_of_dvd_coprimes hab hpa hpb)
  · have hmem : p ∈ primes := Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp, hpL, hL.ne'⟩, hpa⟩
    have hpk : p ∣ k := Finset.dvd_prod_of_mem id hmem
    exact hpa ((Nat.dvd_add_iff_left (dvd_mul_of_dvd_left hpk b)).mpr hpt)

-- Normalize by the gcd as in the OEIS A070548 proof (project PR 13027).
lemma finite_divisor_representative (D : Finset ℕ) (r P : ℕ) (hP : 0 < P) :
    ∃ m : ℕ, 0 < m ∧ m ≡ r [MOD P] ∧ ∀ d ∈ D, d ∣ m → d ∣ r.gcd P := by
  let positive := D.filter fun d => 0 < d
  let L := positive.prod id
  have hL : 0 < L := Finset.prod_pos fun d hd => (Finset.mem_filter.mp hd).2
  obtain ⟨a, b, hab, ha, hb⟩ := Nat.exists_coprime r P
  have hbpos : 0 < b := by
    by_contra! hz
    have he := Nat.eq_zero_of_le_zero hz
    rw [he, Nat.zero_mul] at hb
    omega
  obtain ⟨t, ht, hmod, hcop⟩ := coprime_representative hab hbpos hL
  have hg := Nat.gcd_pos_of_pos_right r hP
  refine ⟨t * r.gcd P, Nat.mul_pos ht hg, ?_, ?_⟩
  · simpa only [← ha, ← hb] using hmod.mul_right' (r.gcd P)
  · intro d hd hdm
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdm (Nat.mul_pos ht hg)
    have hdL : d ∣ L := Finset.dvd_prod_of_mem id (Finset.mem_filter.mpr ⟨hd, hdpos⟩)
    exact (Nat.Coprime.of_dvd_left hdL hcop).dvd_of_dvd_mul_left hdm

lemma finite_divisor_cover (D : Finset ℕ) {r P : ℕ} (hP : 0 < P)
    (cover : ∀ m : ℕ, 0 < m → m ≡ r [MOD P] → ∃ d ∈ D, d ∣ m) :
    ∃ d ∈ D, d ∣ r.gcd P := by
  obtain ⟨m, hm, hmod, restrict⟩ := finite_divisor_representative D r P hP
  obtain ⟨d, hd, hdm⟩ := cover m hm hmod
  exact ⟨d, hd, restrict d hd hdm⟩

-- A finite pool supplies a single witness already at the gcd of the residue and period.
lemma finite_fib_witness_at_gcd (W : Finset ℕ) {q r P : ℕ} (hP : 0 < P)
    (cover : ∀ m : ℕ, 0 < m → m ≡ r [MOD P] →
      ∃ b ∈ W, q ∣ Nat.totient b ∧ b ∣ Nat.fib m) :
    ∃ b ∈ W, q ∣ Nat.totient b ∧ b ∣ Nat.fib (r.gcd P) := by
  classical
  obtain ⟨m, hm, hmod, restrict⟩ := finite_divisor_representative (W.image rankOfApparition) r P hP
  obtain ⟨b, hb, htot, hbm⟩ := cover m hm hmod
  have halign := restrict (rankOfApparition b) (Finset.mem_image_of_mem _ hb) (rank_dvd_index hm hbm)
  have hrank : 0 < rankOfApparition b ∧ b ∣ Nat.fib (rankOfApparition b) :=
    Nat.sInf_mem (s := {k : ℕ | 0 < k ∧ b ∣ Nat.fib k}) ⟨m, hm, hbm⟩
  exact ⟨b, hb, htot, hrank.2.trans (Nat.fib_dvd _ _ halign)⟩

lemma finite_prime_witness_descent (W : Finset ℕ) {q r P : ℕ} (hq : q.Prime) (hP : 0 < P)
    (cover : ∀ m : ℕ, 0 < m → m ≡ r [MOD P] → q ^ 2 ∣ Nat.fib m ∨
      ∃ p ∈ W, p.Prime ∧ p ≡ 1 [MOD q] ∧ p ∣ Nat.fib m) :
    q ∣ Nat.totient (Nat.fib P) := by
  have square : q ∣ Nat.totient (q ^ 2) := by
    rw [Nat.totient_prime_pow_succ hq 1, pow_one]
    exact dvd_mul_right _ _
  obtain ⟨b, _, hqt, hbg⟩ := finite_fib_witness_at_gcd (insert (q ^ 2) W) hP (q := q) (r := r) (by
    intro m hm hmod
    rcases cover m hm hmod with hs | ⟨p, hpW, hp, hpmod, hpm⟩
    · exact ⟨_, Finset.mem_insert_self _ _, square, hs⟩
    · refine ⟨p, Finset.mem_insert_of_mem hpW, ?_, hpm⟩
      rw [Nat.totient_prime hp]
      exact hpmod.symm.dvd')
  exact hqt.trans (Nat.totient_dvd_of_dvd (hbg.trans (Nat.fib_dvd _ _ (Nat.gcd_dvd_right r P))))

-- Conversely a witness at the period covers the zero residue class.
lemma finite_prime_cover_iff {q P : ℕ} (hq : q.Prime) (hP : 0 < P) :
    (∃ (r : ℕ) (W : Finset ℕ), r < P ∧
      ∀ m : ℕ, 0 < m → m ≡ r [MOD P] → q ^ 2 ∣ Nat.fib m ∨
        ∃ p ∈ W, p.Prime ∧ p ≡ 1 [MOD q] ∧ p ∣ Nat.fib m) ↔
      q ∣ Nat.totient (Nat.fib P) := by
  constructor
  · rintro ⟨r, W, _, cover⟩
    exact finite_prime_witness_descent W hq hP cover
  · intro htot
    rcases totient_fib_witness hq htot with hsquare | ⟨p, hp, hpmod, hrP⟩
    · refine ⟨0, ∅, hP, ?_⟩
      intro m _ hm
      exact Or.inl (hsquare.trans (Nat.fib_dvd _ _ (Nat.modEq_zero_iff_dvd.mp hm)))
    · have hrpos := Nat.pos_of_dvd_of_pos hrP hP
      have hindices := Nat.nonempty_of_pos_sInf (s := {k : ℕ | 0 < k ∧ p ∣ Nat.fib k}) hrpos
      have hrank : 0 < rankOfApparition p ∧ p ∣ Nat.fib (rankOfApparition p) := Nat.sInf_mem hindices
      refine ⟨0, {p}, hP, ?_⟩
      intro m _ hm
      exact Or.inr ⟨p, Finset.mem_singleton_self p, hp, hpmod,
        hrank.2.trans (Nat.fib_dvd _ _ (hrP.trans (Nat.modEq_zero_iff_dvd.mp hm)))⟩

lemma factor_rank_at_prime_index {k g l : ℕ} (hl : l.Prime) (hk : k ∣ g * l) (hkg : ¬ k ∣ g) :
    ∃ e : ℕ, e ∣ g ∧ k = e * l := by
  by_cases h : l ∣ k
  · obtain ⟨e, he⟩ := h
    have hke : k = e * l := he.trans (Nat.mul_comm _ _)
    exact ⟨e, Nat.dvd_of_mul_dvd_mul_right hl.pos (hke ▸ hk), hke⟩
  · exact False.elim (hkg ((hl.coprime_iff_not_dvd.mpr h).symm.dvd_of_dvd_mul_right hk))

lemma witness_totient_at_period {w q P : ℕ} (hP : 0 < P)
    (hrP : rankOfApparition w ∣ P) (hqw : q ∣ Nat.totient w) :
    q ∣ Nat.totient (Nat.fib P) := by
  have hindices := Nat.nonempty_of_pos_sInf (s := {k : ℕ | 0 < k ∧ w ∣ Nat.fib k})
    (Nat.pos_of_dvd_of_pos hrP hP)
  have hr : 0 < rankOfApparition w ∧ w ∣ Nat.fib (rankOfApparition w) := Nat.sInf_mem hindices
  exact hqw.trans (Nat.totient_dvd_of_dvd (hr.2.trans (Nat.fib_dvd _ _ hrP)))

-- At every sufficiently large prime index in the normalized class the square witness drops out.
lemma prime_index_rank {q r l : ℕ} (hq : q.Prime) (hr : r ∈ S q)
    (hbad : ¬ q ∣ Nat.totient (Nat.fib (pisano q))) (hl : l.Prime)
    (hlarge : rankOfApparition (q ^ 2) < l)
    (hmod : r.gcd (pisano q) * l ≡ r [MOD pisano q]) :
    ∃ e : ℕ, e ∣ r.gcd (pisano q) ∧ ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD q] ∧ rankOfApparition p = e * l := by
  let g := r.gcd (pisano q)
  have hP := Nat.zero_lt_of_lt hr.1
  have hg : 0 < g := Nat.gcd_pos_of_pos_right _ hP
  have indexpos := Nat.mul_pos hg hl.pos
  have unaligned (w : ℕ) (hw : q ∣ Nat.totient w) : ¬ rankOfApparition w ∣ g :=
    fun hd => hbad (witness_totient_at_period hP (hd.trans (Nat.gcd_dvd_right _ _)) hw)
  rcases totient_fib_witness hq (hr.2 _ hmod) with hs | ⟨p, hp, hpmod, hrank⟩
  · have hsq : q ∣ Nat.totient (q ^ 2) := by
      rw [Nat.totient_prime_pow_succ hq 1, pow_one]
      exact dvd_mul_right _ _
    have hd := rank_dvd_index indexpos hs
    obtain ⟨e, he, heq⟩ := factor_rank_at_prime_index hl hd (unaligned _ hsq)
    have hepos := Nat.pos_of_dvd_of_pos he hg
    have hle : l ≤ e * l := by simpa using Nat.mul_le_mul_right l hepos
    omega
  · have hqt : q ∣ Nat.totient p := by rw [Nat.totient_prime hp]; exact hpmod.symm.dvd'
    obtain ⟨e, he, heq⟩ := factor_rank_at_prime_index hl hrank (unaligned _ hqt)
    exact ⟨e, he, p, hp, hpmod, heq⟩

-- Normalize before applying Dirichlet's theorem, as in project PR 5789.
lemma normalized_prime_indices {r P : ℕ} (hP : 0 < P) :
    ∀ B : ℕ, ∃ l > B, l.Prime ∧ r.gcd P * l ≡ r [MOD P] := by
  obtain ⟨a, b, hab, ha, hb⟩ := Nat.exists_coprime r P
  have hb0 : b ≠ 0 := by
    intro hz
    rw [hz, Nat.zero_mul] at hb
    omega
  intro B
  obtain ⟨l, hlarge, hl, hmod⟩ := Nat.forall_exists_prime_gt_and_modEq B hb0 hab
  refine ⟨l, hlarge, hl, ?_⟩
  simpa only [Nat.mul_comm (r.gcd P) l, ← ha, ← hb] using hmod.mul_right' (r.gcd P)

-- Select an infinite fiber of the divisor choice, as in project PR 8141.
lemma fixed_rank_family {q r : ℕ} (hq : q.Prime) (hr : r ∈ S q)
    (hbad : ¬ q ∣ Nat.totient (Nat.fib (pisano q))) :
    ∃ e : ℕ, e ∣ r.gcd (pisano q) ∧ ∀ B : ℕ, ∃ l > B, ∃ p > B,
      l.Prime ∧ r.gcd (pisano q) * l ≡ r [MOD pisano q] ∧
      p.Prime ∧ p ≡ 1 [MOD q] ∧ rankOfApparition p = e * l := by
  classical
  let g := r.gcd (pisano q)
  have hg : 0 < g := Nat.gcd_pos_of_pos_right _ (Nat.zero_lt_of_lt hr.1)
  have pick (B : ℕ) : ∃ e : ↥g.divisors, ∃ l > B, ∃ p > B,
      l.Prime ∧ g * l ≡ r [MOD pisano q] ∧ p.Prime ∧ p ≡ 1 [MOD q] ∧
      rankOfApparition p = e.val * l := by
    let cap := (Finset.range (B + 1)).sup rankOfApparition
    obtain ⟨l, hbound, hl, hmod⟩ := normalized_prime_indices (r := r)
      (Nat.zero_lt_of_lt hr.1) (max B (max cap (rankOfApparition (q ^ 2))))
    have hlB : B < l := lt_of_le_of_lt (le_max_left ..) hbound
    have hother := lt_of_le_of_lt (le_max_right ..) hbound
    obtain ⟨e, he, p, hp, hpmod, heq⟩ := prime_index_rank hq hr hbad hl
      (lt_of_le_of_lt (le_max_right ..) hother) hmod
    have hepos := Nat.pos_of_dvd_of_pos he hg
    have hle : l ≤ e * l := by simpa using Nat.mul_le_mul_right l hepos
    have hpB : B < p := by
      by_contra! hsmall
      have hcap : rankOfApparition p ≤ cap := Finset.le_sup (Finset.mem_range_succ_iff.mpr hsmall)
      have := lt_of_le_of_lt (le_max_left ..) hother
      omega
    exact ⟨⟨e, Nat.mem_divisors.mpr ⟨he, hg.ne'⟩⟩, l, hlB, p, hpB, hl, hmod, hp, hpmod, heq⟩
  choose color hcolor using pick
  obtain ⟨v, hv⟩ := Finite.exists_infinite_fiber color
  refine ⟨v.val, (Nat.mem_divisors.mp v.property).1, ?_⟩
  intro B
  obtain ⟨i, hi, hBi⟩ := (Set.infinite_coe_iff.mp hv).exists_gt B
  change color i = v at hi
  obtain ⟨l, hil, p, hip, rest⟩ := hcolor i
  exact ⟨l, hBi.trans hil, p, hBi.trans hip, hi ▸ rest⟩

-- One eligible prime with no possible rank witness excludes the residue.
lemma not_mem_of_missing_rank {q r l : ℕ} (hq : q.Prime)
    (hbad : ¬ q ∣ Nat.totient (Nat.fib (pisano q))) (hl : l.Prime)
    (hlarge : rankOfApparition (q ^ 2) < l)
    (hmod : r.gcd (pisano q) * l ≡ r [MOD pisano q])
    (hmiss : ∀ e : ℕ, e ∣ r.gcd (pisano q) → ∀ p : ℕ, p.Prime → p ≡ 1 [MOD q] →
      rankOfApparition p ≠ e * l) : r ∉ S q := by
  intro hr
  obtain ⟨e, he, p, hp, hc, hrank⟩ := prime_index_rank hq hr hbad hl hlarge hmod
  exact hmiss e he p hp hc hrank

-- Test a period using two consecutive values, as in project PRs 8383 and 9447.
lemma pisano_eq_of_certificate {q P : ℕ} (hP : 0 < P)
    (hstart : Nat.fib P ≡ 0 [MOD q] ∧ Nat.fib (P + 1) ≡ 1 [MOD q])
    (hmin : ∀ k : Fin P, 0 < k.val →
      ¬ (Nat.fib k.val ≡ 0 [MOD q] ∧ Nat.fib (k.val + 1) ≡ 1 [MOD q])) :
    pisano q = P := by
  have hper (n : ℕ) : Nat.fib (n + P) ≡ Nat.fib n [MOD q] := by
    induction n using Nat.twoStepInduction with
    | zero => simpa using hstart.1
    | one => simpa [Nat.add_comm] using hstart.2
    | more n h0 h1 =>
      rw [show n + 2 + P = (n + P) + 2 by omega, Nat.fib_add_two, Nat.fib_add_two]
      simpa only [show n + 1 + P = n + P + 1 by omega] using h0.add h1
  let periods := {k : ℕ | 0 < k ∧ ∀ n : ℕ, Nat.fib (n + k) ≡ Nat.fib n [MOD q]}
  have hmem : P ∈ periods := ⟨hP, hper⟩
  change sInf periods = P
  apply le_antisymm (Nat.sInf_le hmem)
  by_contra! hlt
  obtain ⟨hpos, hperiod⟩ : sInf periods ∈ periods := Nat.sInf_mem ⟨P, hmem⟩
  apply hmin ⟨sInf periods, hlt⟩ hpos
  exact ⟨by simpa using hperiod 0, by simpa [Nat.add_comm] using hperiod 1⟩

lemma prime_mem_of_dvd_product {p : ℕ} (hp : p.Prime) (factors : List ℕ)
    (hpr : ∀ a ∈ factors, Nat.Prime a) (hd : p ∣ factors.prod) : p ∈ factors := by
  induction factors with
  | nil => exact (hp.not_dvd_one hd).elim
  | cons a tail ih =>
    rcases hp.dvd_mul.mp hd with ha | ht
    · exact List.mem_cons.mpr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (hpr a (by simp))).mp ha))
    · exact List.mem_cons_of_mem a (ih (fun b hb => hpr b (List.mem_cons_of_mem _ hb)) ht)

-- An upper multiple with certified prime factors suffices, even when F_n is large.
lemma totient_exception_of_factors {q n k : ℕ} (hq : q.Prime) (hn : 0 < n)
    (safe : List ℕ) (hpr : ∀ a ∈ safe, Nat.Prime a ∧ ¬ a ≡ 1 [MOD q])
    (hsquare : ¬ q ^ 2 ∣ Nat.fib n) (hdiv : Nat.fib n ∣ safe.prod ^ k) :
    ¬ q ∣ Nat.totient (Nat.fib n) := by
  intro htot
  rcases totient_fib_witness hq htot with hs | ⟨p, hp, hmod, hr⟩
  · exact hsquare hs
  · have hpos := Nat.pos_of_dvd_of_pos hr hn
    have hindices := Nat.nonempty_of_pos_sInf (s := {j : ℕ | 0 < j ∧ p ∣ Nat.fib j}) hpos
    have hleast : 0 < rankOfApparition p ∧ p ∣ Nat.fib (rankOfApparition p) := Nat.sInf_mem hindices
    have hd := hp.dvd_of_dvd_pow ((hleast.2.trans (Nat.fib_dvd _ _ hr)).trans hdiv)
    have hm := prime_mem_of_dvd_product hp safe (fun a ha => (hpr a ha).1) hd
    exact (hpr p hm).2 hmod

-- A single totient exception rules out the residue of every divisor of its index.
lemma not_mem_of_divisor_exception {q r n d : ℕ} (hbad : ¬ q ∣ Nat.totient (Nat.fib n))
    (hd : d ∣ n) (hmod : d ≡ r [MOD pisano q]) : r ∉ S q := by
  intro hr
  exact hbad ((hr.2 d hmod).trans (Nat.totient_dvd_of_dvd (Nat.fib_dvd _ _ hd)))

lemma empty_of_exception_table {q P k shifts : ℕ} (hq : q.Prime) (hperiod : pisano q = P)
    (safe : List ℕ) (hpr : ∀ a ∈ safe, Nat.Prime a ∧ ¬ a ≡ 1 [MOD q])
    (table : ∀ r : Fin P, ∃ t : Fin shifts, let n := r.val + t.val * P
      0 < n ∧ ¬ q ^ 2 ∣ Nat.fib n ∧ Nat.fib n ∣ safe.prod ^ k) : S q = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro r hr
  have hlt : r < P := hperiod ▸ hr.1
  obtain ⟨t, hn, hs, hd⟩ := table ⟨r, hlt⟩
  have bad := totient_exception_of_factors hq hn safe hpr hs hd
  have hm : r + t.val * P ≡ r [MOD pisano q] := by
    rw [hperiod]
    exact Nat.add_mul_modulus_modEq_iff.mpr rfl
  exact not_mem_of_divisor_exception bad (dvd_refl _) hm hr

-- At q = 7, the prime 67 is in residue 3 and exceeds the square-witness threshold.
lemma prime_index_exception_seven :
    rankOfApparition (7 ^ 2) < 67 ∧ (67 : ℕ).Prime ∧
      67 ≡ 3 [MOD pisano 7] ∧ ¬ 7 ∣ Nat.totient (Nat.fib 67) := by
  have hP : pisano 7 = 16 := pisano_eq_of_certificate (by decide) (by decide) (by decide)
  have h49 : rankOfApparition (7 ^ 2) ≤ 56 :=
    Nat.sInf_le (s := {k : ℕ | 0 < k ∧ 7 ^ 2 ∣ Nat.fib k}) (m := 56) (by decide +revert)
  refine ⟨by omega, by decide, hP ▸ (by decide), ?_⟩
  apply totient_exception_of_factors (k := 1) (by decide) (by decide) [269, 116849, 1429913]
  · norm_num [List.forall_mem_cons, Nat.ModEq]
  · decide
  · decide

-- The same list of certified primes serves every row. Removing primes congruent
-- to one gives the allowed factors for that modulus. Up to three additional
-- periods suffice to find an exception for each residue.
set_option maxRecDepth 4000 in
set_option maxHeartbeats 3000000 in
lemma small_empty_classes {q : ℕ} (hq : q.Prime)
    (hcase : q ∈ ([7, 11, 13, 17, 19, 29, 31] : List ℕ)) : S q = ∅ := by
  let primes : List ℕ :=
    [2, 3, 5, 7, 11, 13, 17, 19, 23, 29,
      31, 37, 41, 47, 53, 61, 71, 89, 107, 109,
      113, 199, 233, 281, 331, 353, 421, 521, 557, 661,
      911, 1597, 2207, 2417, 3001, 19801, 28657, 39161, 141961, 474541,
      514229, 2710260697]
  have prime_entries : ∀ a ∈ primes, Nat.Prime a := by
    norm_num [primes, List.forall_mem_cons]
  let rows : List (ℕ × ℕ) := [(7, 16), (11, 10), (13, 28), (17, 36), (19, 18), (29, 14), (31, 30)]
  have data : ∀ row ∈ rows, let Q := row.1
      let P := row.2
      let safe := primes.filter (fun a => decide (¬ a ≡ 1 [MOD Q]))
      (0 < P ∧ Nat.fib P ≡ 0 [MOD Q] ∧ Nat.fib (P + 1) ≡ 1 [MOD Q]) ∧
      (∀ j : Fin P, 0 < j.val → ¬ (Nat.fib j.val ≡ 0 [MOD Q] ∧ Nat.fib (j.val + 1) ≡ 1 [MOD Q])) ∧
      ∀ r : Fin P, ∃ t : Fin 4, let n := r.val + t.val * P
        0 < n ∧ ¬ Q ^ 2 ∣ Nat.fib n ∧ Nat.fib n ∣ safe.prod ^ 5 := by decide
  have hrow : q ∈ rows.map Prod.fst := hcase
  obtain ⟨⟨Q, P⟩, hmem, rfl⟩ := List.mem_map.mp hrow
  obtain ⟨⟨hP, h0, h1⟩, hmin, htable⟩ := data _ hmem
  exact empty_of_exception_table hq (pisano_eq_of_certificate hP ⟨h0, h1⟩ hmin) _
    (fun a ha => ⟨prime_entries a (List.mem_filter.mp ha).1, of_decide_eq_true (List.mem_filter.mp ha).2⟩)
    htable

-- A prime factor at the period witnesses the entire zero class, including index zero.
lemma zero_class_of_period_factor {q P p : ℕ} (hperiod : pisano q = P) (hP : 0 < P)
    (hp : p.Prime) (hmod : p ≡ 1 [MOD q]) (hdiv : p ∣ Nat.fib P) : 0 ∈ S q := by
  refine ⟨hperiod ▸ hP, ?_⟩
  intro m hm
  rw [hperiod] at hm
  have hqm : q ∣ Nat.totient p := by rw [Nat.totient_prime hp]; exact hmod.symm.dvd'
  exact hqm.trans (Nat.totient_dvd_of_dvd (hdiv.trans (Nat.fib_dvd _ _ (Nat.modEq_zero_iff_dvd.mp hm))))

lemma aligned_witness_of_checked_period {q P p : ℕ} (hP : 0 < P)
    (hstart : Nat.fib P ≡ 0 [MOD q] ∧ Nat.fib (P + 1) ≡ 1 [MOD q])
    (hmin : ∀ k : Fin P, 0 < k.val →
      ¬ (Nat.fib k.val ≡ 0 [MOD q] ∧ Nat.fib (k.val + 1) ≡ 1 [MOD q]))
    (hp : p.Prime) (hc : p ≡ 1 [MOD q]) (hd : p ∣ Nat.fib P) :
    0 ∈ S q ∧ ∃ w : ℕ, w.Prime ∧ w ≡ 1 [MOD q] ∧ rankOfApparition w ∣ pisano q := by
  have period := pisano_eq_of_certificate hP hstart hmin
  refine ⟨zero_class_of_period_factor period hP hp hc hd, p, hp, hc, ?_⟩
  rw [period]
  exact rank_dvd_index hP hd

lemma small_positive_classes {q : ℕ} (h : q = 3 ∨ q = 5 ∨ q = 23) :
    0 ∈ S q ∧ ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD q] ∧ rankOfApparition p ∣ pisano q := by
  rcases h with rfl | rfl | rfl
  · apply aligned_witness_of_checked_period (P := 8) (p := 7) <;> decide
  · apply aligned_witness_of_checked_period (P := 20) (p := 11) <;> decide
  · apply aligned_witness_of_checked_period (P := 48) (p := 47) <;> decide

lemma nonempty_through_31 {q : ℕ} (hq : q.Prime) (hodd : q ≠ 2) (hbound : q ≤ 31) :
    (S q).Nonempty ↔ q = 3 ∨ q = 5 ∨ q = 23 := by
  constructor
  · intro hS
    by_contra h
    have classify : ∀ t : Fin 32, t.val.Prime → t.val ≠ 2 →
        ¬ (t.val = 3 ∨ t.val = 5 ∨ t.val = 23) →
        t.val ∈ ([7, 11, 13, 17, 19, 29, 31] : List ℕ) := by decide
    rw [small_empty_classes hq (classify ⟨q, by omega⟩ hq hodd h)] at hS
    exact hS.elim fun _ he => he.elim
  · exact fun h => ⟨0, (small_positive_classes h).1⟩

lemma converse_through_31 {q : ℕ} (hq : q.Prime) (hodd : q ≠ 2) (hbound : q ≤ 31)
    (hS : (S q).Nonempty) :
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD q] ∧ rankOfApparition p ∣ pisano q := by
  exact (small_positive_classes ((nonempty_through_31 hq hodd hbound).mp hS)).2

theorem main : H1 → H2 → type_of% @OMA.S_arxiv_2604_17847.main := by
  intro finiteCover exceptional q hq hodd hS
  by_cases hsmall : q ≤ 31
  · exact converse_through_31 hq hodd hsmall hS
  have hlarge : 31 < q := by omega
  obtain ⟨r, hr⟩ := hS
  have hP : 0 < pisano q := Nat.zero_lt_of_lt hr.1
  have descend : q ∣ Nat.totient (Nat.fib (pisano q)) := by
    by_contra hbad
    exact hbad ((finite_prime_cover_iff hq hP).mp
      (finiteCover q r hq hlarge hr (fixed_rank_family hq hr hbad)))
  rcases totient_fib_witness hq descend with hsquare | hwitness
  · exact exceptional q hq hlarge hsquare
  · exact hwitness

end OMA.R_arxiv_2604_17847_R1
