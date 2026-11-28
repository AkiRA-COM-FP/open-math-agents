import OMAStatements.S_arxiv_2604_17847

namespace OMA.R_arxiv_2604_17847_R1

open OMA.S_arxiv_2604_17847

-- Descend from an entire residue class to the single index given by the period.
def H1 : Prop :=
  ∀ q : ℕ, q.Prime → q ≠ 2 → (S q).Nonempty →
    q ∣ Nat.totient (Nat.fib (pisano q))

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

theorem main : H1 → H2 → type_of% @OMA.S_arxiv_2604_17847.main := by
  intro descend exceptional q hq hodd hS
  rcases totient_fib_witness hq (descend q hq hodd hS) with hsquare | hwitness
  · exact exceptional q hq hodd hsquare
  · exact hwitness

end OMA.R_arxiv_2604_17847_R1
