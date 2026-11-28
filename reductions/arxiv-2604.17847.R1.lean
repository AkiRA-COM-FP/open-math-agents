import OMAStatements.S_arxiv_2604_17847

namespace OMA.R_arxiv_2604_17847_R1

open OMA.S_arxiv_2604_17847

-- The open finite-witness question: can one good class be covered by a finite pool?
def H1 : Prop :=
  ∀ q : ℕ, q.Prime → q ≠ 2 → (S q).Nonempty →
    ∃ (r : ℕ) (W : Finset ℕ), r < pisano q ∧
      ∀ m : ℕ, 0 < m → m ≡ r [MOD pisano q] → q ^ 2 ∣ Nat.fib m ∨
        ∃ p ∈ W, p.Prime ∧ p ≡ 1 [MOD q] ∧ p ∣ Nat.fib m

-- Isolate the exceptional square-divisibility case at the period.
def H2 : Prop :=
  ∀ q : ℕ, q.Prime → q ≠ 2 → q ^ 2 ∣ Nat.fib (pisano q) →
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

theorem main : H1 → H2 → type_of% @OMA.S_arxiv_2604_17847.main := by
  intro finiteCover exceptional q hq hodd hS
  obtain ⟨r, hr⟩ := hS
  have hP : 0 < pisano q := Nat.zero_lt_of_lt hr.1
  have descend := (finite_prime_cover_iff hq hP).mp (finiteCover q hq hodd ⟨r, hr⟩)
  rcases totient_fib_witness hq descend with hsquare | hwitness
  · exact exceptional q hq hodd hsquare
  · exact hwitness

end OMA.R_arxiv_2604_17847_R1
