import OMAStatements.S_arxiv_2604_17847

namespace OMA.R_arxiv_2604_17847_R1

open OMA.S_arxiv_2604_17847

-- Descend from an entire residue class to the single index given by the period.
def H1 : Prop :=
  ∀ q : ℕ, q.Prime → q ≠ 2 → (S q).Nonempty →
    q ∣ Nat.totient (Nat.fib (pisano q))

-- The totient product formula and the Fibonacci rank divisibility law.
def H2 : Prop :=
  ∀ q n : ℕ, q.Prime → q ∣ Nat.totient (Nat.fib n) →
    q ^ 2 ∣ Nat.fib n ∨
      ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD q] ∧ rankOfApparition p ∣ n

-- Isolate the exceptional square-divisibility case at the period.
def H3 : Prop :=
  ∀ q : ℕ, q.Prime → q ≠ 2 → q ^ 2 ∣ Nat.fib (pisano q) →
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD q] ∧ rankOfApparition p ∣ pisano q

theorem main : H1 → H2 → H3 → type_of% @OMA.S_arxiv_2604_17847.main := by
  intro descend totient exceptional q hq hodd hS
  rcases totient q (pisano q) hq (descend q hq hodd hS) with hsquare | hwitness
  · exact exceptional q hq hodd hsquare
  · exact hwitness

end OMA.R_arxiv_2604_17847_R1
