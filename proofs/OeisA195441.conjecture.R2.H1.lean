import OMAReductions.R_OeisA195441_conjecture_R2


/-
Credit: @VestigeClub.
If an odd n has no prime witness, every deficient base-p digit sum is at most p-2.
The recursion certifies those small digit sums in the residue class n = -1 modulo
previous primes. This forces the product of primes through31 to divide n+1,
leaving nine possible positive multiples below10^12, checked directly.
-/

namespace VestigeBernoulliDigit

def enough : ℕ → ℕ → ℕ → ℕ → Bool
  | 0, _, _, _ => false
  | f+1, p, n, need =>
    if need ≤ n%p then true else enough f p (n/p) (need-n%p)

def test (n : ℕ) : Bool :=
  if n ≤ 100000000 ∨ 1000000000000 ≤ n ∨ n % 2 = 0 then true
  else [3,5,7,11,13,17,19,23,29,31,37].any fun p =>
    if (n+1)%p=0 then false else enough 30 p n p

def check : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Bool
  | 0, _, _, _, _, _, _, _ => false
  | f+1, p, m, a, b, off, scale, upper =>
    if upper < m then
      if a ≤ upper ∧ (Nat.digits p a).sum ≤ b then test (off + scale*a) else true
    else (List.range p).all fun t =>
      let z := a+m*t
      if z%p ≤ b then check f p m (z/p) (b-z%p)
        (off+scale*(z%p)) (scale*p) (upper/p) else true


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sum_digits_step (p n : ℕ) (hp : 1 < p) :
    (Nat.digits p n).sum = n%p + (Nat.digits p (n/p)).sum := by
  by_cases hn : n=0
  · simp [hn]
  · rw [Nat.digits_def' hp (Nat.pos_of_ne_zero hn)]
    rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem enough_sound (f p n need : ℕ) (hp : 1 < p)
    (h : enough f p n need = true) : need ≤ (Nat.digits p n).sum := by
  induction f generalizing n need with
  | zero => simp [enough] at h
  | succ f ih =>
    simp only [enough] at h
    have hd := sum_digits_step p n hp
    split at h
    · omega
    · have hi := ih (n/p) (need-n%p) h
      omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check_sound (f p m a b off scale upper : ℕ)
    (hp : 1 < p) (hm : 0 < m) (ha : a < m)
    (hc : check f p m a b off scale upper = true) :
    ∀ n : ℕ, n ≤ upper → n%m=a → (Nat.digits p n).sum ≤ b →
      test (off+scale*n) = true := by
  induction f generalizing a b off scale upper with
  | zero => simp [check] at hc
  | succ f ih =>
    intro n hn hna hnb
    simp only [check] at hc
    split at hc
    next hsmall =>
      have hnm : n < m := lt_of_le_of_lt hn hsmall
      have eq : n=a := by simpa [Nat.mod_eq_of_lt hnm] using hna
      have haU : a ≤ upper := by omega
      have haB : (Nat.digits p a).sum ≤ b := by simpa [eq] using hnb
      have hcond : a ≤ upper ∧ (Nat.digits p a).sum ≤ b := ⟨haU,haB⟩
      rw [if_pos hcond] at hc
      simpa only [eq] using hc
    next hlarge =>
      have hmod : n = a+m*(n/m) := by
        simpa only [hna] using (Nat.mod_add_div n m).symm
      let k := n/m
      let t := k%p
      let z := a+m*t
      have ht : t < p := Nat.mod_lt _ (by omega)
      have hz : z < m*p := by dsimp [z,t]; nlinarith [Nat.mod_lt k (by omega : 0<p)]
      have hzq : z/p < m := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by simpa [Nat.mul_comm] using hz)
      have expand : n = z+p*(m*(k/p)) := by
        dsimp [z,t,k]
        have kk := Nat.mod_add_div (n/m) p
        nlinarith
      have nq : n/p = z/p+m*(k/p) := by
        rw [expand, Nat.add_mul_div_left _ _ (by omega)]
      have nr : n%p = z%p := by rw [expand]; simp
      have hnq : (n/p)%m=z/p := by rw [nq]; simp [Nat.mod_eq_of_lt hzq]
      have digit := sum_digits_step p n hp
      have hzb : z%p ≤ b := by omega
      have rest : (Nat.digits p (n/p)).sum ≤ b-z%p := by omega
      have one := List.all_eq_true.mp hc t (List.mem_range.mpr ht)
      have child : check f p m (z/p) (b-z%p) (off+scale*(z%p)) (scale*p) (upper/p) = true := by
        simpa only [show a+m*t=z from rfl, if_pos hzb] using one
      have got := ih (z/p) (b-z%p) (off+scale*(z%p)) (scale*p) (upper/p) hzq child
        (n/p) (Nat.div_le_div_right hn) hnq rest
      have ident : off+scale*(z%p)+scale*p*(n/p)=off+scale*n := by
        have eq := Nat.mod_add_div n p
        nlinarith
      simpa only [ident] using got

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem enough_complete (f p n need : ℕ) (hp : 1 < p) (hn : n < p^f)
    (hne : 0 < need) (h : need ≤ (Nat.digits p n).sum) :
    enough f p n need = true := by
  induction f generalizing n need with
  | zero =>
    simp only [pow_zero] at hn
    have hn0 : n=0 := by omega
    have hz : (Nat.digits p n).sum=0 := by simp [hn0]
    omega
  | succ f ih =>
    rw [enough]
    split
    · rfl
    · rename_i small
      apply ih (n/p) (need-n%p)
      · exact (Nat.div_lt_iff_lt_mul (by omega)).mpr (by simpa [pow_succ] using hn)
      · omega
      · have hd := sum_digits_step p n hp
        omega

def primes : List ℕ := [3,5,7,11,13,17,19,23,29,31,37]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem primes_prime (p : ℕ) (h : p ∈ primes) : p.Prime := by
  simp only [primes, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem test_of_witness (p n : ℕ) (hp : p ∈ primes) (hn : n < 3^30)
    (hd : ¬ p ∣ n+1) (hs : p ≤ (Nat.digits p n).sum) : test n = true := by
  unfold test
  split
  · rfl
  · apply List.any_eq_true.mpr
    refine ⟨p, hp, ?_⟩
    have hp3 : 3 ≤ p := by
      simp only [primes, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    rw [if_neg (fun h => hd (Nat.dvd_of_mod_eq_zero h))]
    exact enough_complete 30 p n p (by omega) (hn.trans_le (Nat.pow_le_pow_left hp3 30)) (by omega) hs

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem test_witness (n : ℕ) (hlo : 100000000 < n) (hhi : n < 1000000000000)
    (ho : n%2=1) (ht : test n=true) :
    ∃ p : ℕ, p.Prime ∧ ¬ p ∣ n+1 ∧ p ≤ (Nat.digits p n).sum := by
  unfold test at ht
  rw [if_neg (by omega)] at ht
  obtain ⟨p,hp,ht⟩ := List.any_eq_true.mp ht
  have hprime := primes_prime p hp
  split at ht
  · contradiction
  · rename_i hd
    exact ⟨p,hprime, (fun h => hd (Nat.mod_eq_zero_of_dvd h)), enough_sound 30 p n p hprime.one_lt ht⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem force_divisor (p m n : ℕ) (hp : p ∈ primes) (hm : 0 < m)
    (hbound : n ≤ 999999999999) (hodd : n%2=1) (hnm : m ∣ n+1)
    (hcheck : check 30 p m (m-1) (p-2) 0 1 999999999999 = true)
    (hbad : test n ≠ true) : p ∣ n+1 := by
  have hprime := primes_prime p hp
  have hp3 : 3 ≤ p := by
    simp only [primes, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  by_contra hdiv
  have hs : (Nat.digits p n).sum < p := by
    by_contra! h
    exact hbad (test_of_witness p n hp (hbound.trans_lt (by norm_num)) hdiv h)
  have hpodd : p%2=1 := hprime.eq_two_or_odd.resolve_left (by omega)
  have hpar := Nat.modEq_digits_sum 2 p hpodd (n := n)
  have hpar' : (Nat.digits p n).sum % 2 = 1 := by
    change n%2 = (Nat.digits p n).sum%2 at hpar
    omega
  have sumle : (Nat.digits p n).sum ≤ p-2 := by omega
  have nmod : n%m=m-1 := by
    have h := Nat.mod_eq_zero_of_dvd hnm
    have hrem : (n%m+1)%m=0 := by simpa [Nat.add_mod] using h
    have hd : m ∣ n%m+1 := Nat.dvd_of_mod_eq_zero hrem
    have hlo := Nat.le_of_dvd (by omega : 0<n%m+1) hd
    have hlt := Nat.mod_lt n hm
    omega
  have ht := check_sound 30 p m (m-1) (p-2) 0 1 999999999999 hprime.one_lt hm (by omega) hcheck n hbound nmod sumle
  exact hbad (by simpa using ht)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check_step (f p m a b off scale upper : ℕ) (hu : ¬ upper < m)
    (h : ∀ t : ℕ, t < p → (a+m*t)%p ≤ b →
      check f p m ((a+m*t)/p) (b-(a+m*t)%p)
        (off+scale*((a+m*t)%p)) (scale*p) (upper/p) = true) :
    check (f+1) p m a b off scale upper = true := by
  simp only [check, if_neg hu, List.all_eq_true, List.mem_range]
  intro t ht
  split
  · exact h t ht ‹_›
  · rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem force_cert (p m a budget n : ℕ) (ha : a = m-1) (hb : budget = p-2)
    (hp : p ∈ primes) (hm : 0 < m) (hbound : n≤999999999999) (ho : n%2=1)
    (hd : m ∣ n+1) (hc : check 30 p m a budget 0 1 999999999999 = true)
    (hbad : test n ≠ true) : p ∣ n+1 := by
  apply force_divisor p m n hp hm hbound ho hd _ hbad
  simpa only [ha,hb] using hc

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem tail_check : ∀ k : Fin 10, test (100280245065*k.val-1)=true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem all_cases
    (c3 : check 30 3 1 0 1 0 1 999999999999 = true)
    (c5 : check 30 5 3 2 3 0 1 999999999999 = true)
    (c7 : check 30 7 15 14 5 0 1 999999999999 = true)
    (c11 : check 30 11 105 104 9 0 1 999999999999 = true)
    (c13 : check 30 13 1155 1154 11 0 1 999999999999 = true)
    (c17 : check 30 17 15015 15014 15 0 1 999999999999 = true)
    (c19 : check 30 19 255255 255254 17 0 1 999999999999 = true)
    (c23 : check 30 23 4849845 4849844 21 0 1 999999999999 = true)
    (c29 : check 30 29 111546435 111546434 27 0 1 999999999999 = true)
    (c31 : check 30 31 3234846615 3234846614 29 0 1 999999999999 = true)
    (n : ℕ) (hlo : 100000000 < n) (hhi : n < 1000000000000) (ho : n%2=1) :
    ∃ p : ℕ, p.Prime ∧ ¬ p ∣ n+1 ∧ p ≤ (Nat.digits p n).sum := by
  by_contra hn
  have hbad : test n ≠ true := fun ht => hn (test_witness n hlo hhi ho ht)
  have hbound : n ≤ 999999999999 := by omega
  have d1 : 1 ∣ n+1 := one_dvd _
  have p3 := force_cert 3 1 0 1 n (by norm_num) (by norm_num) (by simp [primes]) (by norm_num) hbound ho d1 c3 hbad
  have d3 : 3 ∣ n+1 := by
    simpa only [Nat.reduceMul] using (show Nat.Coprime 1 3 by norm_num).mul_dvd_of_dvd_of_dvd d1 p3
  have p5 := force_cert 5 3 2 3 n (by norm_num) (by norm_num) (by simp [primes]) (by norm_num) hbound ho d3 c5 hbad
  have d15 : 15 ∣ n+1 := by
    simpa only [Nat.reduceMul] using (show Nat.Coprime 3 5 by norm_num).mul_dvd_of_dvd_of_dvd d3 p5
  have p7 := force_cert 7 15 14 5 n (by norm_num) (by norm_num) (by simp [primes]) (by norm_num) hbound ho d15 c7 hbad
  have d105 : 105 ∣ n+1 := by
    simpa only [Nat.reduceMul] using (show Nat.Coprime 15 7 by norm_num).mul_dvd_of_dvd_of_dvd d15 p7
  have p11 := force_cert 11 105 104 9 n (by norm_num) (by norm_num) (by simp [primes]) (by norm_num) hbound ho d105 c11 hbad
  have d1155 : 1155 ∣ n+1 := by
    simpa only [Nat.reduceMul] using (show Nat.Coprime 105 11 by norm_num).mul_dvd_of_dvd_of_dvd d105 p11
  have p13 := force_cert 13 1155 1154 11 n (by norm_num) (by norm_num) (by simp [primes]) (by norm_num) hbound ho d1155 c13 hbad
  have d15015 : 15015 ∣ n+1 := by
    simpa only [Nat.reduceMul] using (show Nat.Coprime 1155 13 by norm_num).mul_dvd_of_dvd_of_dvd d1155 p13
  have p17 := force_cert 17 15015 15014 15 n (by norm_num) (by norm_num) (by simp [primes]) (by norm_num) hbound ho d15015 c17 hbad
  have d255255 : 255255 ∣ n+1 := by
    simpa only [Nat.reduceMul] using (show Nat.Coprime 15015 17 by norm_num).mul_dvd_of_dvd_of_dvd d15015 p17
  have p19 := force_cert 19 255255 255254 17 n (by norm_num) (by norm_num) (by simp [primes]) (by norm_num) hbound ho d255255 c19 hbad
  have d4849845 : 4849845 ∣ n+1 := by
    simpa only [Nat.reduceMul] using (show Nat.Coprime 255255 19 by norm_num).mul_dvd_of_dvd_of_dvd d255255 p19
  have p23 := force_cert 23 4849845 4849844 21 n (by norm_num) (by norm_num) (by simp [primes]) (by norm_num) hbound ho d4849845 c23 hbad
  have d111546435 : 111546435 ∣ n+1 := by
    simpa only [Nat.reduceMul] using (show Nat.Coprime 4849845 23 by norm_num).mul_dvd_of_dvd_of_dvd d4849845 p23
  have p29 := force_cert 29 111546435 111546434 27 n (by norm_num) (by norm_num) (by simp [primes]) (by norm_num) hbound ho d111546435 c29 hbad
  have d3234846615 : 3234846615 ∣ n+1 := by
    simpa only [Nat.reduceMul] using (show Nat.Coprime 111546435 29 by norm_num).mul_dvd_of_dvd_of_dvd d111546435 p29
  have p31 := force_cert 31 3234846615 3234846614 29 n (by norm_num) (by norm_num) (by simp [primes]) (by norm_num) hbound ho d3234846615 c31 hbad
  have d100280245065 : 100280245065 ∣ n+1 := by
    simpa only [Nat.reduceMul] using (show Nat.Coprime 3234846615 31 by norm_num).mul_dvd_of_dvd_of_dvd d3234846615 p31
  have ht : (n+1)/100280245065 < 10 := by
    apply (Nat.div_lt_iff_lt_mul (by norm_num : 0<100280245065)).mpr
    have small : n+1 ≤ 1000000000000 := Nat.succ_le_of_lt hhi
    exact small.trans_lt (by norm_num)
  have heq : 100280245065*((n+1)/100280245065)=n+1 := Nat.mul_div_cancel' d100280245065
  have hnrep : n=100280245065*((n+1)/100280245065)-1 := by simp only [heq, Nat.add_sub_cancel]
  apply hbad
  rw [hnrep]
  exact tail_check ⟨(n+1)/100280245065,ht⟩

end VestigeBernoulliDigit

namespace VestigeBernoulliDigit
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check3 : check 30 3 1 0 1 0 1 999999999999 = true := by decide +kernel
end VestigeBernoulliDigit

namespace VestigeBernoulliDigit
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check5 : check 30 5 3 2 3 0 1 999999999999 = true := by decide +kernel
end VestigeBernoulliDigit

namespace VestigeBernoulliDigit
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check7_x0x0 : check 28 7 15 0 3 14 49 20408163265 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check7_x0x1 : check 28 7 15 2 2 21 49 20408163265 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check7_x0x2 : check 28 7 15 4 1 28 49 20408163265 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check7_x0x3 : check 28 7 15 6 0 35 49 20408163265 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check7_x0x5x0 : check 27 7 15 1 1 196 343 2915451895 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check7_x0x5x1 : check 27 7 15 3 0 245 343 2915451895 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check7_x0x5x3x0 : check 26 7 15 1 4 343 2401 416493127 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check7_x0x5x3x1 : check 26 7 15 3 3 686 2401 416493127 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check7_x0x5x3x2 : check 26 7 15 5 2 1029 2401 416493127 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check7_x0x5x3x3 : check 26 7 15 7 1 1372 2401 416493127 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check7_x0x5x3x4 : check 26 7 15 9 0 1715 2401 416493127 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check7_x0x5x3x6 : check 26 7 15 14 5 0 2401 416493127 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check7_x0x5x3 : check 27 7 15 8 5 0 343 2915451895 = true := by
  apply check_step 26 7 15 8 5 0 343 2915451895 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check7_x0x5x3x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check7_x0x5x3x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check7_x0x5x3x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check7_x0x5x3x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check7_x0x5x3x4
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check7_x0x5x3x6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check7_x0x5x4 : check 27 7 15 10 4 49 343 2915451895 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check7_x0x5x5 : check 27 7 15 12 3 98 343 2915451895 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check7_x0x5x6 : check 27 7 15 14 2 147 343 2915451895 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check7_x0x5 : check 28 7 15 11 5 0 49 20408163265 = true := by
  apply check_step 27 7 15 11 5 0 49 20408163265 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check7_x0x5x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check7_x0x5x1
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check7_x0x5x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check7_x0x5x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check7_x0x5x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check7_x0x5x6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check7_x0x6 : check 28 7 15 13 4 7 49 20408163265 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check7_x0 : check 29 7 15 2 5 0 7 142857142857 = true := by
  apply check_step 28 7 15 2 5 0 7 142857142857 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check7_x0x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check7_x0x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check7_x0x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check7_x0x3
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check7_x0x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check7_x0x6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check7_x1 : check 29 7 15 4 4 1 7 142857142857 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check7_x2 : check 29 7 15 6 3 2 7 142857142857 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check7_x3 : check 29 7 15 8 2 3 7 142857142857 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check7_x4 : check 29 7 15 10 1 4 7 142857142857 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check7_x5 : check 29 7 15 12 0 5 7 142857142857 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check7 : check 30 7 15 14 5 0 1 999999999999 = true := by
  apply check_step 29 7 15 14 5 0 1 999999999999 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check7_x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check7_x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check7_x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check7_x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check7_x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check7_x5
  · norm_num at hb
end VestigeBernoulliDigit

namespace VestigeBernoulliDigit
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x0 : check 29 11 105 9 4 5 11 90909090909 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x0 : check 28 11 105 1 1 88 121 8264462809 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x1x0 : check 27 11 105 1 6 33 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x1x1 : check 27 11 105 10 0 759 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x1x2 : check 27 11 105 20 5 154 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x1x4 : check 27 11 105 39 4 275 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x1x6 : check 27 11 105 58 3 396 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x1x8 : check 27 11 105 77 2 517 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x1x10 : check 27 11 105 96 1 638 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x1 : check 28 11 105 11 6 33 121 8264462809 = true := by
  apply check_step 27 11 105 11 6 33 121 8264462809 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x1x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x1x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x1x2
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x1x4
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x1x6
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x1x8
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x1x10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x2 : check 28 11 105 20 0 99 121 8264462809 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x3 : check 28 11 105 30 5 44 121 8264462809 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x5 : check 28 11 105 49 4 55 121 8264462809 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x0 : check 27 11 105 5 5 484 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x2 : check 27 11 105 24 4 605 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x3x0x0 : check 25 11 105 0 5 45254 161051 6209213 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x3x0x2 : check 25 11 105 19 4 59895 161051 6209213 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x3x0x4 : check 25 11 105 38 3 74536 161051 6209213 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x3x0x5 : check 25 11 105 48 8 1331 161051 6209213 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x3x0x6 : check 25 11 105 57 2 89177 161051 6209213 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x3x0x7 : check 25 11 105 67 7 15972 161051 6209213 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x3x0x8 : check 25 11 105 76 1 103818 161051 6209213 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x3x0x9 : check 25 11 105 86 6 30613 161051 6209213 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x3x0x10 : check 25 11 105 95 0 118459 161051 6209213 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x3x0 : check 26 11 105 3 8 1331 14641 68301345 = true := by
  apply check_step 25 11 105 3 8 1331 14641 68301345 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x3x0x0
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x3x0x2
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x3x0x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x3x0x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x3x0x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x3x0x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x3x0x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x3x0x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x3x0x10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x3x1 : check 26 11 105 12 2 9317 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x3x2 : check 26 11 105 22 7 2662 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x3x3 : check 26 11 105 31 1 10648 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x3x4 : check 26 11 105 41 6 3993 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x3x5 : check 26 11 105 50 0 11979 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x3x6 : check 26 11 105 60 5 5324 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x3x8 : check 26 11 105 79 4 6655 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x3x9x0 : check 25 11 105 8 8 14641 161051 6209213 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x3x9x1 : check 25 11 105 17 2 102487 161051 6209213 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x3x9x2 : check 25 11 105 27 7 29282 161051 6209213 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x3x9x3 : check 25 11 105 36 1 117128 161051 6209213 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x3x9x4 : check 25 11 105 46 6 43923 161051 6209213 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x3x9x5 : check 25 11 105 55 0 131769 161051 6209213 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x3x9x6 : check 25 11 105 65 5 58564 161051 6209213 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x3x9x8 : check 25 11 105 84 4 73205 161051 6209213 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x3x9x9 : check 25 11 105 94 9 0 161051 6209213 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x3x9x10 : check 25 11 105 103 3 87846 161051 6209213 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x3x9 : check 26 11 105 89 9 0 14641 68301345 = true := by
  apply check_step 25 11 105 89 9 0 14641 68301345 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x3x9x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x3x9x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x3x9x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x3x9x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x3x9x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x3x9x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x3x9x6
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x3x9x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x3x9x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x3x9x10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x3x10 : check 26 11 105 98 3 7986 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x3 : check 27 11 105 34 9 0 1331 751314800 = true := by
  apply check_step 26 11 105 34 9 0 1331 751314800 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x3x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x3x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x3x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x3x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x3x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x3x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x3x6
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x3x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x3x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x3x10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x4 : check 27 11 105 43 3 726 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x5x1 : check 26 11 105 14 4 5445 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x5x3 : check 26 11 105 33 3 6776 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x5x4x1 : check 25 11 105 13 3 73326 161051 6209213 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x5x4x2 : check 25 11 105 23 8 121 161051 6209213 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x5x4x3 : check 25 11 105 32 2 87967 161051 6209213 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x5x4x4 : check 25 11 105 42 7 14762 161051 6209213 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x5x4x5 : check 25 11 105 51 1 102608 161051 6209213 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x5x4x6 : check 25 11 105 61 6 29403 161051 6209213 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x5x4x7 : check 25 11 105 70 0 117249 161051 6209213 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x5x4x8 : check 25 11 105 80 5 44044 161051 6209213 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x5x4x10 : check 25 11 105 99 4 58685 161051 6209213 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x5x4 : check 26 11 105 43 8 121 14641 68301345 = true := by
  apply check_step 25 11 105 43 8 121 14641 68301345 (by norm_num)
  intro t ht hb
  interval_cases t
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x5x4x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x5x4x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x5x4x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x5x4x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x5x4x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x5x4x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x5x4x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x5x4x8
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x5x4x10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x5x5 : check 26 11 105 52 2 8107 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x5x6 : check 26 11 105 62 7 1452 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x5x7 : check 26 11 105 71 1 9438 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x5x8 : check 26 11 105 81 6 2783 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x5x9 : check 26 11 105 90 0 10769 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x5x10 : check 26 11 105 100 5 4114 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x5 : check 27 11 105 53 8 121 1331 751314800 = true := by
  apply check_step 26 11 105 53 8 121 1331 751314800 (by norm_num)
  intro t ht hb
  interval_cases t
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x5x1
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x5x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x5x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x5x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x5x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x5x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x5x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x5x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x5x10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x6 : check 27 11 105 62 2 847 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x7x0 : check 26 11 105 6 1 8228 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x7x1 : check 26 11 105 16 6 1573 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x7x2 : check 26 11 105 25 0 9559 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x7x3 : check 26 11 105 35 5 2904 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x7x5 : check 26 11 105 54 4 4235 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x7x7 : check 26 11 105 73 3 5566 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x7x9 : check 26 11 105 92 2 6897 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x7x10 : check 26 11 105 102 7 242 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x7 : check 27 11 105 72 7 242 1331 751314800 = true := by
  apply check_step 26 11 105 72 7 242 1331 751314800 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x7x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x7x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x7x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x7x3
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x7x5
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x7x7
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x7x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x7x10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x8 : check 27 11 105 81 1 968 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x9 : check 27 11 105 91 6 363 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6x10 : check 27 11 105 100 0 1089 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x6 : check 28 11 105 59 9 0 121 8264462809 = true := by
  apply check_step 27 11 105 59 9 0 121 8264462809 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x0
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x7 : check 28 11 105 68 3 66 121 8264462809 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x8x0x0 : check 26 11 105 0 0 9449 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x8x0x1 : check 26 11 105 10 5 2794 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x8x0x3 : check 26 11 105 29 4 4125 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x8x0x5 : check 26 11 105 48 3 5456 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x8x0x7 : check 26 11 105 67 2 6787 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x8x0x8 : check 26 11 105 77 7 132 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x8x0x9 : check 26 11 105 86 1 8118 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x8x0x10 : check 26 11 105 96 6 1463 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x8x0 : check 27 11 105 7 7 132 1331 751314800 = true := by
  apply check_step 26 11 105 7 7 132 1331 751314800 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x8x0x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x8x0x1
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x8x0x3
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x8x0x5
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x8x0x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x8x0x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x8x0x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x8x0x10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x8x1 : check 27 11 105 16 1 858 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x8x2 : check 27 11 105 26 6 253 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x8x3 : check 27 11 105 35 0 979 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x8x4 : check 27 11 105 45 5 374 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x8x6 : check 27 11 105 64 4 495 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x8x8 : check 27 11 105 83 3 616 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x8x9x0 : check 26 11 105 8 3 6666 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x8x9x1x0 : check 25 11 105 1 1 102498 161051 6209213 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x8x9x1x1 : check 25 11 105 11 6 29293 161051 6209213 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x8x9x1x2 : check 25 11 105 20 0 117139 161051 6209213 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x8x9x1x3 : check 25 11 105 30 5 43934 161051 6209213 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x8x9x1x5 : check 25 11 105 49 4 58575 161051 6209213 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x8x9x1x7 : check 25 11 105 68 3 73216 161051 6209213 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x8x9x1x8 : check 25 11 105 78 8 11 161051 6209213 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x8x9x1x9 : check 25 11 105 87 2 87857 161051 6209213 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x8x9x1x10 : check 25 11 105 97 7 14652 161051 6209213 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x8x9x1 : check 26 11 105 18 8 11 14641 68301345 = true := by
  apply check_step 25 11 105 18 8 11 14641 68301345 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x8x9x1x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x8x9x1x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x8x9x1x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x8x9x1x3
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x8x9x1x5
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x8x9x1x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x8x9x1x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x8x9x1x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x8x9x1x10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x8x9x2 : check 26 11 105 27 2 7997 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x8x9x3 : check 26 11 105 37 7 1342 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x8x9x4 : check 26 11 105 46 1 9328 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x8x9x5 : check 26 11 105 56 6 2673 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x8x9x6 : check 26 11 105 65 0 10659 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x8x9x7 : check 26 11 105 75 5 4004 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x8x9x9 : check 26 11 105 94 4 5335 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x8x9 : check 27 11 105 93 8 11 1331 751314800 = true := by
  apply check_step 26 11 105 93 8 11 1331 751314800 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x8x9x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x8x9x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x8x9x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x8x9x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x8x9x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x8x9x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x8x9x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x8x9x7
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x8x9x9
  · norm_num at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x8x10 : check 27 11 105 102 2 737 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x8 : check 28 11 105 78 8 11 121 8264462809 = true := by
  apply check_step 27 11 105 78 8 11 121 8264462809 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x8x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x8x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x8x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x8x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x8x4
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x8x6
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x8x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x8x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x8x10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x9 : check 28 11 105 87 2 77 121 8264462809 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x10x1 : check 27 11 105 18 3 506 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x10x3 : check 27 11 105 37 2 627 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x10x4x0 : check 26 11 105 4 4 4015 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x10x4x2 : check 26 11 105 23 3 5346 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x10x4x4 : check 26 11 105 42 2 6677 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x10x4x5 : check 26 11 105 52 7 22 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x10x4x6 : check 26 11 105 61 1 8008 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x10x4x7 : check 26 11 105 71 6 1353 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x10x4x8 : check 26 11 105 80 0 9339 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x10x4x9 : check 26 11 105 90 5 2684 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x10x4 : check 27 11 105 47 7 22 1331 751314800 = true := by
  apply check_step 26 11 105 47 7 22 1331 751314800 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x10x4x0
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x10x4x2
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x10x4x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x10x4x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x10x4x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x10x4x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x10x4x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x10x4x9
  · norm_num at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x10x5 : check 27 11 105 56 1 748 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x10x6 : check 27 11 105 66 6 143 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x10x7 : check 27 11 105 75 0 869 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x10x8 : check 27 11 105 85 5 264 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x10x10 : check 27 11 105 104 4 385 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1x10 : check 28 11 105 97 7 22 121 8264462809 = true := by
  apply check_step 27 11 105 97 7 22 121 8264462809 (by norm_num)
  intro t ht hb
  interval_cases t
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x10x1
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x10x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x10x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x10x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x10x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x10x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x10x8
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x10x10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x1 : check 29 11 105 19 9 0 11 90909090909 = true := by
  apply check_step 28 11 105 19 9 0 11 90909090909 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x3
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x2 : check 29 11 105 28 3 6 11 90909090909 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x0 : check 28 11 105 3 3 56 121 8264462809 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x1x0 : check 27 11 105 1 6 243 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x1x1 : check 27 11 105 10 0 969 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x1x2 : check 27 11 105 20 5 364 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x1x4 : check 27 11 105 39 4 485 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x1x6 : check 27 11 105 58 3 606 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x1x7x0 : check 26 11 105 6 6 2663 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x1x7x1 : check 26 11 105 15 0 10649 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x1x7x2 : check 26 11 105 25 5 3994 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x1x7x4 : check 26 11 105 44 4 5325 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x1x7x6 : check 26 11 105 63 3 6656 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x1x7x7x0 : check 25 11 105 6 1 102488 161051 6209213 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x1x7x7x1 : check 25 11 105 16 6 29283 161051 6209213 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x1x7x7x2 : check 25 11 105 25 0 117129 161051 6209213 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x1x7x7x3 : check 25 11 105 35 5 43924 161051 6209213 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x1x7x7x5 : check 25 11 105 54 4 58565 161051 6209213 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x1x7x7x7 : check 25 11 105 73 3 73206 161051 6209213 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x1x7x7x8 : check 25 11 105 83 8 1 161051 6209213 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x1x7x7x9 : check 25 11 105 92 2 87847 161051 6209213 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x1x7x7x10 : check 25 11 105 102 7 14642 161051 6209213 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x1x7x7 : check 26 11 105 73 8 1 14641 68301345 = true := by
  apply check_step 25 11 105 73 8 1 14641 68301345 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x1x7x7x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x1x7x7x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x1x7x7x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x1x7x7x3
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x1x7x7x5
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x1x7x7x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x1x7x7x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x1x7x7x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x1x7x7x10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x1x7x8 : check 26 11 105 82 2 7987 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x1x7x9 : check 26 11 105 92 7 1332 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x1x7x10 : check 26 11 105 101 1 9318 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x1x7 : check 27 11 105 68 8 1 1331 751314800 = true := by
  apply check_step 26 11 105 68 8 1 1331 751314800 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x1x7x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x1x7x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x1x7x2
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x1x7x4
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x1x7x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x1x7x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x1x7x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x1x7x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x1x7x10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x1x8 : check 27 11 105 77 2 727 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x1x9x1 : check 26 11 105 17 2 6777 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x1x9x2 : check 26 11 105 27 7 122 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x1x9x3 : check 26 11 105 36 1 8108 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x1x9x4 : check 26 11 105 46 6 1453 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x1x9x5 : check 26 11 105 55 0 9439 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x1x9x6 : check 26 11 105 65 5 2784 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x1x9x8 : check 26 11 105 84 4 4115 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x1x9x10 : check 26 11 105 103 3 5446 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x1x9 : check 27 11 105 87 7 122 1331 751314800 = true := by
  apply check_step 26 11 105 87 7 122 1331 751314800 (by norm_num)
  intro t ht hb
  interval_cases t
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x1x9x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x1x9x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x1x9x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x1x9x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x1x9x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x1x9x6
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x1x9x8
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x1x9x10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x1x10 : check 27 11 105 96 1 848 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x1 : check 28 11 105 13 8 1 121 8264462809 = true := by
  apply check_step 27 11 105 13 8 1 121 8264462809 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x1x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x1x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x1x2
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x1x4
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x1x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x1x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x1x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x1x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x1x10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x2 : check 28 11 105 22 2 67 121 8264462809 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x3x1 : check 27 11 105 12 2 617 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x3x2x0 : check 26 11 105 2 7 12 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x3x2x1 : check 26 11 105 11 1 7998 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x3x2x2 : check 26 11 105 21 6 1343 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x3x2x3 : check 26 11 105 30 0 9329 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x3x2x4 : check 26 11 105 40 5 2674 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x3x2x6 : check 26 11 105 59 4 4005 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x3x2x8 : check 26 11 105 78 3 5336 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x3x2x10 : check 26 11 105 97 2 6667 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x3x2 : check 27 11 105 22 7 12 1331 751314800 = true := by
  apply check_step 26 11 105 22 7 12 1331 751314800 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x3x2x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x3x2x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x3x2x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x3x2x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x3x2x4
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x3x2x6
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x3x2x8
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x3x2x10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x3x3 : check 27 11 105 31 1 738 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x3x4 : check 27 11 105 41 6 133 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x3x5 : check 27 11 105 50 0 859 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x3x6 : check 27 11 105 60 5 254 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x3x8 : check 27 11 105 79 4 375 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x3x10 : check 27 11 105 98 3 496 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x3 : check 28 11 105 32 7 12 121 8264462809 = true := by
  apply check_step 27 11 105 32 7 12 121 8264462809 (by norm_num)
  intro t ht hb
  interval_cases t
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x3x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x3x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x3x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x3x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x3x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x3x6
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x3x8
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x3x10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x4 : check 28 11 105 41 1 78 121 8264462809 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x5x1 : check 27 11 105 14 4 265 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x5x3 : check 27 11 105 33 3 386 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x5x5 : check 27 11 105 52 2 507 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x5x7 : check 27 11 105 71 1 628 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x5x8 : check 27 11 105 81 6 23 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x5x9 : check 27 11 105 90 0 749 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x5x10 : check 27 11 105 100 5 144 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x5 : check 28 11 105 51 6 23 121 8264462809 = true := by
  apply check_step 27 11 105 51 6 23 121 8264462809 (by norm_num)
  intro t ht hb
  interval_cases t
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x5x1
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x5x3
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x5x5
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x5x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x5x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x5x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x5x10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x6 : check 28 11 105 60 0 89 121 8264462809 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x7 : check 28 11 105 70 5 34 121 8264462809 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3x9 : check 28 11 105 89 4 45 121 8264462809 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x3 : check 29 11 105 38 8 1 11 90909090909 = true := by
  apply check_step 28 11 105 38 8 1 11 90909090909 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x7
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x9
  · norm_num at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x4 : check 29 11 105 47 2 7 11 90909090909 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x5x0 : check 28 11 105 5 5 24 121 8264462809 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x5x2 : check 28 11 105 24 4 35 121 8264462809 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x5x4 : check 28 11 105 43 3 46 121 8264462809 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x5x6 : check 28 11 105 62 2 57 121 8264462809 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x5x7x0 : check 27 11 105 6 1 728 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x5x7x1 : check 27 11 105 16 6 123 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x5x7x2 : check 27 11 105 25 0 849 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x5x7x3 : check 27 11 105 35 5 244 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x5x7x5 : check 27 11 105 54 4 365 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x5x7x7 : check 27 11 105 73 3 486 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x5x7x9 : check 27 11 105 92 2 607 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x5x7x10x0 : check 26 11 105 9 4 3995 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x5x7x10x2 : check 26 11 105 28 3 5326 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x5x7x10x4 : check 26 11 105 47 2 6657 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x5x7x10x5 : check 26 11 105 57 7 2 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x5x7x10x6 : check 26 11 105 66 1 7988 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x5x7x10x7 : check 26 11 105 76 6 1333 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x5x7x10x8 : check 26 11 105 85 0 9319 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x5x7x10x9 : check 26 11 105 95 5 2664 14641 68301345 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x5x7x10 : check 27 11 105 102 7 2 1331 751314800 = true := by
  apply check_step 26 11 105 102 7 2 1331 751314800 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x5x7x10x0
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x5x7x10x2
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x5x7x10x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x5x7x10x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x5x7x10x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x5x7x10x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x5x7x10x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x5x7x10x9
  · norm_num at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x5x7 : check 28 11 105 72 7 2 121 8264462809 = true := by
  apply check_step 27 11 105 72 7 2 121 8264462809 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x5x7x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x5x7x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x5x7x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x5x7x3
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x5x7x5
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x5x7x7
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x5x7x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x5x7x10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x5x8 : check 28 11 105 81 1 68 121 8264462809 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x5x9x0 : check 27 11 105 8 3 376 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x5x9x2 : check 27 11 105 27 2 497 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x5x9x4 : check 27 11 105 46 1 618 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x5x9x5 : check 27 11 105 56 6 13 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x5x9x6 : check 27 11 105 65 0 739 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x5x9x7 : check 27 11 105 75 5 134 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x5x9x9 : check 27 11 105 94 4 255 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x5x9 : check 28 11 105 91 6 13 121 8264462809 = true := by
  apply check_step 27 11 105 91 6 13 121 8264462809 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x5x9x0
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x5x9x2
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x5x9x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x5x9x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x5x9x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x5x9x7
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x5x9x9
  · norm_num at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x5x10 : check 28 11 105 100 0 79 121 8264462809 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x5 : check 29 11 105 57 7 2 11 90909090909 = true := by
  apply check_step 28 11 105 57 7 2 11 90909090909 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x5x0
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x5x2
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x5x4
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x5x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x5x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x5x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x5x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x5x10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x6 : check 29 11 105 66 1 8 11 90909090909 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x7x1 : check 28 11 105 16 1 58 121 8264462809 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x7x2x0 : check 27 11 105 2 2 487 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x7x2x2 : check 27 11 105 21 1 608 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x7x2x3 : check 27 11 105 31 6 3 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x7x2x4 : check 27 11 105 40 0 729 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x7x2x5 : check 27 11 105 50 5 124 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x7x2x7 : check 27 11 105 69 4 245 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x7x2x9 : check 27 11 105 88 3 366 1331 751314800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x7x2 : check 28 11 105 26 6 3 121 8264462809 = true := by
  apply check_step 27 11 105 26 6 3 121 8264462809 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x7x2x0
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x7x2x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x7x2x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x7x2x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x7x2x5
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x7x2x7
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x7x2x9
  · norm_num at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x7x3 : check 28 11 105 35 0 69 121 8264462809 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x7x4 : check 28 11 105 45 5 14 121 8264462809 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x7x6 : check 28 11 105 64 4 25 121 8264462809 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x7x8 : check 28 11 105 83 3 36 121 8264462809 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x7x10 : check 28 11 105 102 2 47 121 8264462809 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x7 : check 29 11 105 76 6 3 11 90909090909 = true := by
  apply check_step 28 11 105 76 6 3 11 90909090909 (by norm_num)
  intro t ht hb
  interval_cases t
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x7x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x7x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x7x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x7x4
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x7x6
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x7x8
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x7x10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x8 : check 29 11 105 85 0 9 11 90909090909 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11_x9 : check 29 11 105 95 5 4 11 90909090909 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11 : check 30 11 105 104 9 0 1 999999999999 = true := by
  apply check_step 29 11 105 104 9 0 1 999999999999 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x9
  · norm_num at hb
end VestigeBernoulliDigit

namespace VestigeBernoulliDigit
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x0 : check 29 13 1155 88 1 10 13 76923076923 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x1 : check 29 13 1155 177 3 8 13 76923076923 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x2 : check 29 13 1155 266 5 6 13 76923076923 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x3x0 : check 28 13 1155 27 3 56 169 5917159763 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x3x1 : check 28 13 1155 116 5 30 169 5917159763 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x3x2x2 : check 27 13 1155 193 1 1018 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x3x2x3 : check 27 13 1155 282 3 680 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x3x2x4 : check 27 13 1155 371 5 342 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x3x2x5 : check 27 13 1155 460 7 4 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x3x2x8 : check 27 13 1155 726 0 1187 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x3x2x9 : check 27 13 1155 815 2 849 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x3x2x10 : check 27 13 1155 904 4 511 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x3x2x11 : check 27 13 1155 993 6 173 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x3x2 : check 28 13 1155 205 7 4 169 5917159763 = true := by
  apply check_step 27 13 1155 205 7 4 169 5917159763 (by norm_num)
  intro t ht hb
  interval_cases t
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x3x2x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x3x2x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x3x2x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x3x2x5
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x3x2x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x3x2x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x3x2x10
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x3x2x11
  · norm_num at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x3x5 : check 28 13 1155 471 0 95 169 5917159763 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x3x6 : check 28 13 1155 560 2 69 169 5917159763 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x3x7 : check 28 13 1155 649 4 43 169 5917159763 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x3x8 : check 28 13 1155 738 6 17 169 5917159763 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x3x12 : check 28 13 1155 1093 1 82 169 5917159763 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x3 : check 29 13 1155 355 7 4 13 76923076923 = true := by
  apply check_step 28 13 1155 355 7 4 13 76923076923 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x3x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x3x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x3x2
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x3x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x3x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x3x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x3x8
  · norm_num at hb
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x3x12
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x0x1 : check 27 13 1155 91 1 1042 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x0x2 : check 27 13 1155 180 3 704 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x0x3 : check 27 13 1155 269 5 366 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x0x4 : check 27 13 1155 358 7 28 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x0x7 : check 27 13 1155 624 0 1211 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x0x8 : check 27 13 1155 713 2 873 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x0x9 : check 27 13 1155 802 4 535 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x0x10 : check 27 13 1155 891 6 197 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x0 : check 28 13 1155 34 7 28 169 5917159763 = true := by
  apply check_step 27 13 1155 34 7 28 169 5917159763 (by norm_num)
  intro t ht hb
  interval_cases t
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x0x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x0x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x0x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x0x4
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x0x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x0x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x0x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x0x10
  · norm_num at hb
  · norm_num at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x1x0 : check 27 13 1155 9 3 1016 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x1x1 : check 27 13 1155 98 5 678 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x1x2 : check 27 13 1155 187 7 340 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x1x3x0 : check 26 13 1155 21 6 6593 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x1x3x1 : check 26 13 1155 110 8 2199 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x1x3x4 : check 26 13 1155 376 1 17578 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x1x3x5 : check 26 13 1155 465 3 13184 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x1x3x6 : check 26 13 1155 554 5 8790 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x1x3x7 : check 26 13 1155 643 7 4396 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x1x3x8 : check 26 13 1155 732 9 2 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x1x3x10 : check 26 13 1155 909 0 19775 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x1x3x11 : check 26 13 1155 998 2 15381 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x1x3x12 : check 26 13 1155 1087 4 10987 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x1x3 : check 27 13 1155 276 9 2 2197 455166135 = true := by
  apply check_step 26 13 1155 276 9 2 2197 455166135 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x1x3x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x1x3x1
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x1x3x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x1x3x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x1x3x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x1x3x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x1x3x8
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x1x3x10
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x1x3x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x1x3x12
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x1x5 : check 27 13 1155 453 0 1523 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x1x6 : check 27 13 1155 542 2 1185 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x1x7 : check 27 13 1155 631 4 847 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x1x8 : check 27 13 1155 720 6 509 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x1x9x0 : check 26 13 1155 62 5 6762 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x1x9x1 : check 26 13 1155 151 7 2368 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x1x9x4 : check 26 13 1155 417 0 17747 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x1x9x5 : check 26 13 1155 506 2 13353 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x1x9x6 : check 26 13 1155 595 4 8959 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x1x9x7 : check 26 13 1155 684 6 4565 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x1x9x8 : check 26 13 1155 773 8 171 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x1x9x11 : check 26 13 1155 1039 1 15550 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x1x9x12 : check 26 13 1155 1128 3 11156 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x1x9 : check 27 13 1155 809 8 171 2197 455166135 = true := by
  apply check_step 26 13 1155 809 8 171 2197 455166135 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x1x9x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x1x9x1
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x1x9x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x1x9x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x1x9x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x1x9x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x1x9x8
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x1x9x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x1x9x12
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x1x12 : check 27 13 1155 1075 1 1354 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x1 : check 28 13 1155 123 9 2 169 5917159763 = true := by
  apply check_step 27 13 1155 123 9 2 169 5917159763 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x1x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x1x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x1x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x1x3
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x1x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x1x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x1x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x1x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x1x9
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x1x12
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x3 : check 28 13 1155 300 0 119 169 5917159763 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x4 : check 28 13 1155 389 2 93 169 5917159763 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x5 : check 28 13 1155 478 4 67 169 5917159763 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x6 : check 28 13 1155 567 6 41 169 5917159763 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x7x0 : check 27 13 1155 50 2 1029 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x7x1 : check 27 13 1155 139 4 691 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x7x2 : check 27 13 1155 228 6 353 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x7x3x0 : check 26 13 1155 24 3 11000 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x7x3x1 : check 26 13 1155 113 5 6606 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x7x3x2 : check 26 13 1155 202 7 2212 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x7x3x5 : check 26 13 1155 468 0 17591 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x7x3x6 : check 26 13 1155 557 2 13197 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x7x3x7 : check 26 13 1155 646 4 8803 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x7x3x8 : check 26 13 1155 735 6 4409 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x7x3x9 : check 26 13 1155 824 8 15 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x7x3x12 : check 26 13 1155 1090 1 15394 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x7x3 : check 27 13 1155 317 8 15 2197 455166135 = true := by
  apply check_step 26 13 1155 317 8 15 2197 455166135 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x7x3x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x7x3x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x7x3x2
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x7x3x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x7x3x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x7x3x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x7x3x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x7x3x9
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x7x3x12
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x7x6 : check 27 13 1155 583 1 1198 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x7x7 : check 27 13 1155 672 3 860 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x7x8 : check 27 13 1155 761 5 522 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x7x9 : check 27 13 1155 850 7 184 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x7x12 : check 27 13 1155 1116 0 1367 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x7 : check 28 13 1155 656 8 15 169 5917159763 = true := by
  apply check_step 27 13 1155 656 8 15 169 5917159763 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x7x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x7x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x7x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x7x3
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x7x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x7x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x7x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x7x9
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x7x12
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x10 : check 28 13 1155 922 1 106 169 5917159763 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x11 : check 28 13 1155 1011 3 80 169 5917159763 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4x12 : check 28 13 1155 1100 5 54 169 5917159763 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x4 : check 29 13 1155 444 9 2 13 76923076923 = true := by
  apply check_step 28 13 1155 444 9 2 13 76923076923 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x1
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x7
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x10
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4x12
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x0x0 : check 26 13 1155 0 6 6929 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x0x1 : check 26 13 1155 89 8 2535 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x0x4 : check 26 13 1155 355 1 17914 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x0x5 : check 26 13 1155 444 3 13520 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x0x6 : check 26 13 1155 533 5 9126 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x0x7 : check 26 13 1155 622 7 4732 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x0x8 : check 26 13 1155 711 9 338 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x0x10 : check 26 13 1155 888 0 20111 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x0x11 : check 26 13 1155 977 2 15717 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x0x12 : check 26 13 1155 1066 4 11323 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x0 : check 27 13 1155 3 9 338 2197 455166135 = true := by
  apply check_step 26 13 1155 3 9 338 2197 455166135 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x0x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x0x1
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x0x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x0x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x0x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x0x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x0x8
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x0x10
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x0x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x0x12
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x1x0x0 : check 25 13 1155 0 3 202124 371293 2693290 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x1x0x1 : check 25 13 1155 89 5 145002 371293 2693290 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x1x0x2 : check 25 13 1155 178 7 87880 371293 2693290 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x1x0x3 : check 25 13 1155 267 9 30758 371293 2693290 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x1x0x5 : check 25 13 1155 444 0 287807 371293 2693290 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x1x0x6 : check 25 13 1155 533 2 230685 371293 2693290 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x1x0x7 : check 25 13 1155 622 4 173563 371293 2693290 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x1x0x8 : check 25 13 1155 711 6 116441 371293 2693290 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x1x0x9 : check 25 13 1155 800 8 59319 371293 2693290 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x1x0x10 : check 25 13 1155 889 10 2197 371293 2693290 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x1x0x12 : check 25 13 1155 1066 1 259246 371293 2693290 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x1x0 : check 26 13 1155 7 10 2197 28561 35012779 = true := by
  apply check_step 25 13 1155 7 10 2197 28561 35012779 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x1x0x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x1x0x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x1x0x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x1x0x3
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x1x0x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x1x0x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x1x0x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x1x0x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x1x0x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x1x0x10
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x1x0x12
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x1x2 : check 26 13 1155 184 1 21970 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x1x3 : check 26 13 1155 273 3 17576 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x1x4 : check 26 13 1155 362 5 13182 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x1x5 : check 26 13 1155 451 7 8788 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x1x6 : check 26 13 1155 540 9 4394 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x1x7x0 : check 25 13 1155 48 6 142805 371293 2693290 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x1x7x1 : check 25 13 1155 137 8 85683 371293 2693290 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x1x7x2 : check 25 13 1155 226 10 28561 371293 2693290 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x1x7x4 : check 25 13 1155 403 1 285610 371293 2693290 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x1x7x5 : check 25 13 1155 492 3 228488 371293 2693290 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x1x7x6 : check 25 13 1155 581 5 171366 371293 2693290 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x1x7x7 : check 25 13 1155 670 7 114244 371293 2693290 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x1x7x8 : check 25 13 1155 759 9 57122 371293 2693290 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x1x7x9 : check 25 13 1155 848 11 0 371293 2693290 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x1x7x10 : check 25 13 1155 936 0 314171 371293 2693290 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x1x7x11 : check 25 13 1155 1025 2 257049 371293 2693290 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x1x7x12 : check 25 13 1155 1114 4 199927 371293 2693290 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x1x7 : check 26 13 1155 629 11 0 28561 35012779 = true := by
  apply check_step 25 13 1155 629 11 0 28561 35012779 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x1x7x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x1x7x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x1x7x2
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x1x7x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x1x7x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x1x7x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x1x7x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x1x7x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x1x7x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x1x7x10
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x1x7x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x1x7x12
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x1x8 : check 26 13 1155 717 0 24167 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x1x9 : check 26 13 1155 806 2 19773 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x1x10 : check 26 13 1155 895 4 15379 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x1x11 : check 26 13 1155 984 6 10985 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x1x12 : check 26 13 1155 1073 8 6591 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x1 : check 27 13 1155 92 11 0 2197 455166135 = true := by
  apply check_step 26 13 1155 92 11 0 2197 455166135 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x1x0
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x1x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x1x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x1x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x1x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x1x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x1x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x1x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x1x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x1x10
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x1x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x1x12
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x2 : check 27 13 1155 180 0 1859 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x3 : check 27 13 1155 269 2 1521 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x4 : check 27 13 1155 358 4 1183 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x5 : check 27 13 1155 447 6 845 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x6x0 : check 26 13 1155 41 5 7098 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x6x1 : check 26 13 1155 130 7 2704 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x6x4 : check 26 13 1155 396 0 18083 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x6x5 : check 26 13 1155 485 2 13689 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x6x6 : check 26 13 1155 574 4 9295 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x6x7 : check 26 13 1155 663 6 4901 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x6x8 : check 26 13 1155 752 8 507 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x6x11 : check 26 13 1155 1018 1 15886 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x6x12 : check 26 13 1155 1107 3 11492 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x6 : check 27 13 1155 536 8 507 2197 455166135 = true := by
  apply check_step 26 13 1155 536 8 507 2197 455166135 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x6x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x6x1
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x6x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x6x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x6x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x6x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x6x8
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x6x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x6x12
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x7x0 : check 26 13 1155 48 9 2366 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x7x2 : check 26 13 1155 225 0 22139 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x7x3 : check 26 13 1155 314 2 17745 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x7x4 : check 26 13 1155 403 4 13351 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x7x5 : check 26 13 1155 492 6 8957 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x7x6 : check 26 13 1155 581 8 4563 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x7x7x0 : check 25 13 1155 51 3 200096 371293 2693290 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x7x7x1 : check 25 13 1155 140 5 142974 371293 2693290 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x7x7x2 : check 25 13 1155 229 7 85852 371293 2693290 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x7x7x3 : check 25 13 1155 318 9 28730 371293 2693290 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x7x7x5 : check 25 13 1155 495 0 285779 371293 2693290 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x7x7x6 : check 25 13 1155 584 2 228657 371293 2693290 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x7x7x7 : check 25 13 1155 673 4 171535 371293 2693290 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x7x7x8 : check 25 13 1155 762 6 114413 371293 2693290 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x7x7x9 : check 25 13 1155 851 8 57291 371293 2693290 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x7x7x10 : check 25 13 1155 940 10 169 371293 2693290 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x7x7x12 : check 25 13 1155 1117 1 257218 371293 2693290 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x7x7 : check 26 13 1155 670 10 169 28561 35012779 = true := by
  apply check_step 25 13 1155 670 10 169 28561 35012779 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x7x7x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x7x7x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x7x7x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x7x7x3
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x7x7x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x7x7x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x7x7x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x7x7x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x7x7x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x7x7x10
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x7x7x12
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x7x9 : check 26 13 1155 847 1 19942 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x7x10 : check 26 13 1155 936 3 15548 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x7x11 : check 26 13 1155 1025 5 11154 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x7x12 : check 26 13 1155 1114 7 6760 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x7 : check 27 13 1155 625 10 169 2197 455166135 = true := by
  apply check_step 26 13 1155 625 10 169 2197 455166135 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x7x0
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x7x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x7x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x7x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x7x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x7x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x7x7
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x7x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x7x10
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x7x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x7x12
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x9 : check 27 13 1155 802 1 1690 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x10 : check 27 13 1155 891 3 1352 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x11 : check 27 13 1155 980 5 1014 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0x12 : check 27 13 1155 1069 7 676 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x0 : check 28 13 1155 41 11 0 169 5917159763 = true := by
  apply check_step 27 13 1155 41 11 0 169 5917159763 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x7
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x10
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x12
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x1 : check 28 13 1155 129 0 143 169 5917159763 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x2 : check 28 13 1155 218 2 117 169 5917159763 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x3 : check 28 13 1155 307 4 91 169 5917159763 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x4 : check 28 13 1155 396 6 65 169 5917159763 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x5x0 : check 27 13 1155 37 4 715 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x5x1 : check 27 13 1155 126 6 377 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x5x2x0 : check 26 13 1155 16 1 15418 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x5x2x1 : check 26 13 1155 105 3 11024 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x5x2x2 : check 26 13 1155 194 5 6630 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x5x2x3 : check 26 13 1155 283 7 2236 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x5x2x6 : check 26 13 1155 549 0 17615 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x5x2x7 : check 26 13 1155 638 2 13221 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x5x2x8 : check 26 13 1155 727 4 8827 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x5x2x9 : check 26 13 1155 816 6 4433 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x5x2x10 : check 26 13 1155 905 8 39 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x5x2 : check 27 13 1155 215 8 39 2197 455166135 = true := by
  apply check_step 26 13 1155 215 8 39 2197 455166135 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x5x2x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x5x2x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x5x2x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x5x2x3
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x5x2x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x5x2x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x5x2x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x5x2x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x5x2x10
  · norm_num at hb
  · norm_num at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x5x5 : check 27 13 1155 481 1 1222 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x5x6 : check 27 13 1155 570 3 884 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x5x7 : check 27 13 1155 659 5 546 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x5x8 : check 27 13 1155 748 7 208 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x5x11 : check 27 13 1155 1014 0 1391 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x5x12 : check 27 13 1155 1103 2 1053 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x5 : check 28 13 1155 485 8 39 169 5917159763 = true := by
  apply check_step 27 13 1155 485 8 39 169 5917159763 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x5x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x5x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x5x2
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x5x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x5x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x5x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x5x8
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x5x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x5x12
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x6x0x0 : check 26 13 1155 3 3 11336 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x6x0x1 : check 26 13 1155 92 5 6942 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x6x0x2 : check 26 13 1155 181 7 2548 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x6x0x5 : check 26 13 1155 447 0 17927 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x6x0x6 : check 26 13 1155 536 2 13533 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x6x0x7 : check 26 13 1155 625 4 9139 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x6x0x8 : check 26 13 1155 714 6 4745 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x6x0x9 : check 26 13 1155 803 8 351 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x6x0x12 : check 26 13 1155 1069 1 15730 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x6x0 : check 27 13 1155 44 8 351 2197 455166135 = true := by
  apply check_step 26 13 1155 44 8 351 2197 455166135 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x6x0x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x6x0x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x6x0x2
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x6x0x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x6x0x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x6x0x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x6x0x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x6x0x9
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x6x0x12
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x6x1x0 : check 26 13 1155 10 7 6604 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x6x1x1 : check 26 13 1155 99 9 2210 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x6x1x3 : check 26 13 1155 276 0 21983 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x6x1x4 : check 26 13 1155 365 2 17589 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x6x1x5 : check 26 13 1155 454 4 13195 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x6x1x6 : check 26 13 1155 543 6 8801 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x6x1x7 : check 26 13 1155 632 8 4407 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x6x1x8x0 : check 25 13 1155 55 4 171379 371293 2693290 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x6x1x8x1 : check 25 13 1155 144 6 114257 371293 2693290 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x6x1x8x2 : check 25 13 1155 233 8 57135 371293 2693290 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x6x1x8x3 : check 25 13 1155 322 10 13 371293 2693290 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x6x1x8x5 : check 25 13 1155 499 1 257062 371293 2693290 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x6x1x8x6 : check 25 13 1155 588 3 199940 371293 2693290 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x6x1x8x7 : check 25 13 1155 677 5 142818 371293 2693290 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x6x1x8x8 : check 25 13 1155 766 7 85696 371293 2693290 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x6x1x8x9 : check 25 13 1155 855 9 28574 371293 2693290 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x6x1x8x11 : check 25 13 1155 1032 0 285623 371293 2693290 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x6x1x8x12 : check 25 13 1155 1121 2 228501 371293 2693290 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x6x1x8 : check 26 13 1155 721 10 13 28561 35012779 = true := by
  apply check_step 25 13 1155 721 10 13 28561 35012779 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x6x1x8x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x6x1x8x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x6x1x8x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x6x1x8x3
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x6x1x8x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x6x1x8x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x6x1x8x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x6x1x8x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x6x1x8x9
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x6x1x8x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x6x1x8x12
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x6x1x10 : check 26 13 1155 898 1 19786 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x6x1x11 : check 26 13 1155 987 3 15392 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x6x1x12 : check 26 13 1155 1076 5 10998 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x6x1 : check 27 13 1155 133 10 13 2197 455166135 = true := by
  apply check_step 26 13 1155 133 10 13 2197 455166135 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x6x1x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x6x1x1
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x6x1x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x6x1x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x6x1x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x6x1x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x6x1x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x6x1x8
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x6x1x10
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x6x1x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x6x1x12
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x6x3 : check 27 13 1155 310 1 1534 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x6x4 : check 27 13 1155 399 3 1196 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x6x5 : check 27 13 1155 488 5 858 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x6x6 : check 27 13 1155 577 7 520 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x6x7x0 : check 26 13 1155 51 6 6773 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x6x7x1 : check 26 13 1155 140 8 2379 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x6x7x4 : check 26 13 1155 406 1 17758 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x6x7x5 : check 26 13 1155 495 3 13364 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x6x7x6 : check 26 13 1155 584 5 8970 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x6x7x7 : check 26 13 1155 673 7 4576 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x6x7x8 : check 26 13 1155 762 9 182 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x6x7x10 : check 26 13 1155 939 0 19955 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x6x7x11 : check 26 13 1155 1028 2 15561 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x6x7x12 : check 26 13 1155 1117 4 11167 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x6x7 : check 27 13 1155 666 9 182 2197 455166135 = true := by
  apply check_step 26 13 1155 666 9 182 2197 455166135 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x6x7x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x6x7x1
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x6x7x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x6x7x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x6x7x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x6x7x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x6x7x8
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x6x7x10
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x6x7x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x6x7x12
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x6x9 : check 27 13 1155 843 0 1703 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x6x10 : check 27 13 1155 932 2 1365 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x6x11 : check 27 13 1155 1021 4 1027 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x6x12 : check 27 13 1155 1110 6 689 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x6 : check 28 13 1155 574 10 13 169 5917159763 = true := by
  apply check_step 27 13 1155 574 10 13 169 5917159763 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x6x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x6x1
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x6x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x6x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x6x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x6x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x6x7
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x6x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x6x10
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x6x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x6x12
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x8 : check 28 13 1155 751 1 130 169 5917159763 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x9 : check 28 13 1155 840 3 104 169 5917159763 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x10 : check 28 13 1155 929 5 78 169 5917159763 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x11x0 : check 27 13 1155 78 3 728 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x11x1 : check 27 13 1155 167 5 390 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x11x2 : check 27 13 1155 256 7 52 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x11x5 : check 27 13 1155 522 0 1235 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x11x6 : check 27 13 1155 611 2 897 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x11x7 : check 27 13 1155 700 4 559 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x11x8 : check 27 13 1155 789 6 221 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x11x12 : check 27 13 1155 1144 1 1066 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x11 : check 28 13 1155 1018 7 52 169 5917159763 = true := by
  apply check_step 27 13 1155 1018 7 52 169 5917159763 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x11x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x11x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x11x2
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x11x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x11x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x11x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x11x8
  · norm_num at hb
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x11x12
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x12x0 : check 27 13 1155 85 7 364 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x12x1x0 : check 26 13 1155 13 4 11011 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x12x1x1 : check 26 13 1155 102 6 6617 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x12x1x2 : check 26 13 1155 191 8 2223 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x12x1x5 : check 26 13 1155 457 1 17602 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x12x1x6 : check 26 13 1155 546 3 13208 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x12x1x7 : check 26 13 1155 635 5 8814 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x12x1x8 : check 26 13 1155 724 7 4420 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x12x1x9 : check 26 13 1155 813 9 26 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x12x1x11 : check 26 13 1155 990 0 19799 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x12x1x12 : check 26 13 1155 1079 2 15405 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x12x1 : check 27 13 1155 174 9 26 2197 455166135 = true := by
  apply check_step 26 13 1155 174 9 26 2197 455166135 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x12x1x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x12x1x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x12x1x2
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x12x1x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x12x1x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x12x1x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x12x1x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x12x1x9
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x12x1x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x12x1x12
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x12x3 : check 27 13 1155 351 0 1547 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x12x4 : check 27 13 1155 440 2 1209 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x12x5 : check 27 13 1155 529 4 871 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x12x6 : check 27 13 1155 618 6 533 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x12x7x0 : check 26 13 1155 54 3 11180 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x12x7x1 : check 26 13 1155 143 5 6786 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x12x7x2 : check 26 13 1155 232 7 2392 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x12x7x5 : check 26 13 1155 498 0 17771 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x12x7x6 : check 26 13 1155 587 2 13377 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x12x7x7 : check 26 13 1155 676 4 8983 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x12x7x8 : check 26 13 1155 765 6 4589 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x12x7x9 : check 26 13 1155 854 8 195 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x12x7x12 : check 26 13 1155 1120 1 15574 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x12x7 : check 27 13 1155 707 8 195 2197 455166135 = true := by
  apply check_step 26 13 1155 707 8 195 2197 455166135 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x12x7x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x12x7x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x12x7x2
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x12x7x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x12x7x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x12x7x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x12x7x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x12x7x9
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x12x7x12
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x12x10 : check 27 13 1155 973 1 1378 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x12x11 : check 27 13 1155 1062 3 1040 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x12x12 : check 27 13 1155 1151 5 702 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5x12 : check 28 13 1155 1107 9 26 169 5917159763 = true := by
  apply check_step 27 13 1155 1107 9 26 169 5917159763 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x12x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x12x1
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x12x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x12x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x12x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x12x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x12x7
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x12x10
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x12x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x12x12
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x5 : check 29 13 1155 533 11 0 13 76923076923 = true := by
  apply check_step 28 13 1155 533 11 0 13 76923076923 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x6
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x10
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x12
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x6 : check 29 13 1155 621 0 11 13 76923076923 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x7 : check 29 13 1155 710 2 9 13 76923076923 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x8 : check 29 13 1155 799 4 7 13 76923076923 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x9x0 : check 28 13 1155 68 2 57 169 5917159763 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x9x1 : check 28 13 1155 157 4 31 169 5917159763 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x9x2 : check 28 13 1155 246 6 5 169 5917159763 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x9x6 : check 28 13 1155 601 1 70 169 5917159763 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x9x7 : check 28 13 1155 690 3 44 169 5917159763 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x9x8 : check 28 13 1155 779 5 18 169 5917159763 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x9x12 : check 28 13 1155 1134 0 83 169 5917159763 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x9 : check 29 13 1155 888 6 5 13 76923076923 = true := by
  apply check_step 28 13 1155 888 6 5 13 76923076923 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x9x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x9x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x9x2
  · norm_num at hb
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x9x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x9x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x9x8
  · norm_num at hb
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x9x12
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x10x0 : check 28 13 1155 75 6 29 169 5917159763 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x10x1x0 : check 27 13 1155 12 0 1355 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x10x1x1 : check 27 13 1155 101 2 1017 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x10x1x2 : check 27 13 1155 190 4 679 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x10x1x3 : check 27 13 1155 279 6 341 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x10x1x4x0 : check 26 13 1155 28 4 8791 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x10x1x4x1 : check 26 13 1155 117 6 4397 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x10x1x4x2 : check 26 13 1155 206 8 3 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x10x1x4x5 : check 26 13 1155 472 1 15382 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x10x1x4x6 : check 26 13 1155 561 3 10988 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x10x1x4x7 : check 26 13 1155 650 5 6594 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x10x1x4x8 : check 26 13 1155 739 7 2200 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x10x1x4x11 : check 26 13 1155 1005 0 17579 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x10x1x4x12 : check 26 13 1155 1094 2 13185 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x10x1x4 : check 27 13 1155 368 8 3 2197 455166135 = true := by
  apply check_step 26 13 1155 368 8 3 2197 455166135 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x10x1x4x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x10x1x4x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x10x1x4x2
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x10x1x4x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x10x1x4x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x10x1x4x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x10x1x4x8
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x10x1x4x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x10x1x4x12
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x10x1x7 : check 27 13 1155 634 1 1186 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x10x1x8 : check 27 13 1155 723 3 848 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x10x1x9 : check 27 13 1155 812 5 510 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x10x1x10 : check 27 13 1155 901 7 172 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x10x1 : check 28 13 1155 164 8 3 169 5917159763 = true := by
  apply check_step 27 13 1155 164 8 3 169 5917159763 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x10x1x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x10x1x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x10x1x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x10x1x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x10x1x4
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x10x1x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x10x1x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x10x1x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x10x1x10
  · norm_num at hb
  · norm_num at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x10x4 : check 28 13 1155 430 1 94 169 5917159763 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x10x5 : check 28 13 1155 519 3 68 169 5917159763 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x10x6 : check 28 13 1155 608 5 42 169 5917159763 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x10x7x1 : check 27 13 1155 142 1 1030 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x10x7x2 : check 27 13 1155 231 3 692 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x10x7x3 : check 27 13 1155 320 5 354 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x10x7x4 : check 27 13 1155 409 7 16 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x10x7x7 : check 27 13 1155 675 0 1199 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x10x7x8 : check 27 13 1155 764 2 861 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x10x7x9 : check 27 13 1155 853 4 523 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x10x7x10 : check 27 13 1155 942 6 185 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x10x7 : check 28 13 1155 697 7 16 169 5917159763 = true := by
  apply check_step 27 13 1155 697 7 16 169 5917159763 (by norm_num)
  intro t ht hb
  interval_cases t
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x10x7x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x10x7x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x10x7x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x10x7x4
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x10x7x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x10x7x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x10x7x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x10x7x10
  · norm_num at hb
  · norm_num at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x10x10 : check 28 13 1155 963 0 107 169 5917159763 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x10x11 : check 28 13 1155 1052 2 81 169 5917159763 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x10x12 : check 28 13 1155 1141 4 55 169 5917159763 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x10 : check 29 13 1155 977 8 3 13 76923076923 = true := by
  apply check_step 28 13 1155 977 8 3 13 76923076923 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x10x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x10x1
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x10x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x10x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x10x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x10x7
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x10x10
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x10x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x10x12
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x0x0 : check 27 13 1155 6 6 677 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x0x1x0 : check 26 13 1155 7 4 9127 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x0x1x1 : check 26 13 1155 96 6 4733 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x0x1x2 : check 26 13 1155 185 8 339 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x0x1x5 : check 26 13 1155 451 1 15718 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x0x1x6 : check 26 13 1155 540 3 11324 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x0x1x7 : check 26 13 1155 629 5 6930 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x0x1x8 : check 26 13 1155 718 7 2536 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x0x1x11 : check 26 13 1155 984 0 17915 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x0x1x12 : check 26 13 1155 1073 2 13521 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x0x1 : check 27 13 1155 95 8 339 2197 455166135 = true := by
  apply check_step 26 13 1155 95 8 339 2197 455166135 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x0x1x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x0x1x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x0x1x2
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x0x1x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x0x1x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x0x1x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x0x1x8
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x0x1x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x0x1x12
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x0x2x0 : check 26 13 1155 14 8 4395 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x0x2x1x1 : check 25 13 1155 96 0 285611 371293 2693290 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x0x2x1x2 : check 25 13 1155 185 2 228489 371293 2693290 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x0x2x1x3 : check 25 13 1155 274 4 171367 371293 2693290 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x0x2x1x4 : check 25 13 1155 363 6 114245 371293 2693290 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x0x2x1x5 : check 25 13 1155 452 8 57123 371293 2693290 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x0x2x1x6 : check 25 13 1155 541 10 1 371293 2693290 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x0x2x1x8 : check 25 13 1155 718 1 257050 371293 2693290 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x0x2x1x9 : check 25 13 1155 807 3 199928 371293 2693290 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x0x2x1x10 : check 25 13 1155 896 5 142806 371293 2693290 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x0x2x1x11 : check 25 13 1155 985 7 85684 371293 2693290 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x0x2x1x12 : check 25 13 1155 1074 9 28562 371293 2693290 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x0x2x1 : check 26 13 1155 103 10 1 28561 35012779 = true := by
  apply check_step 25 13 1155 103 10 1 28561 35012779 (by norm_num)
  intro t ht hb
  interval_cases t
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x0x2x1x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x0x2x1x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x0x2x1x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x0x2x1x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x0x2x1x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x0x2x1x6
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x0x2x1x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x0x2x1x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x0x2x1x10
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x0x2x1x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x0x2x1x12
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x0x2x3 : check 26 13 1155 280 1 19774 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x0x2x4 : check 26 13 1155 369 3 15380 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x0x2x5 : check 26 13 1155 458 5 10986 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x0x2x6 : check 26 13 1155 547 7 6592 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x0x2x7 : check 26 13 1155 636 9 2198 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x0x2x9 : check 26 13 1155 813 0 21971 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x0x2x10 : check 26 13 1155 902 2 17577 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x0x2x11 : check 26 13 1155 991 4 13183 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x0x2x12 : check 26 13 1155 1080 6 8789 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x0x2 : check 27 13 1155 184 10 1 2197 455166135 = true := by
  apply check_step 26 13 1155 184 10 1 2197 455166135 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x0x2x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x0x2x1
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x0x2x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x0x2x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x0x2x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x0x2x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x0x2x7
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x0x2x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x0x2x10
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x0x2x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x0x2x12
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x0x4 : check 27 13 1155 361 1 1522 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x0x5 : check 27 13 1155 450 3 1184 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x0x6 : check 27 13 1155 539 5 846 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x0x7 : check 27 13 1155 628 7 508 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x0x8x0 : check 26 13 1155 55 7 4564 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x0x8x1 : check 26 13 1155 144 9 170 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x0x8x3 : check 26 13 1155 321 0 19943 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x0x8x4 : check 26 13 1155 410 2 15549 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x0x8x5 : check 26 13 1155 499 4 11155 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x0x8x6 : check 26 13 1155 588 6 6761 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x0x8x7 : check 26 13 1155 677 8 2367 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x0x8x10 : check 26 13 1155 943 1 17746 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x0x8x11 : check 26 13 1155 1032 3 13352 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x0x8x12 : check 26 13 1155 1121 5 8958 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x0x8 : check 27 13 1155 717 9 170 2197 455166135 = true := by
  apply check_step 26 13 1155 717 9 170 2197 455166135 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x0x8x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x0x8x1
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x0x8x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x0x8x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x0x8x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x0x8x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x0x8x7
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x0x8x10
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x0x8x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x0x8x12
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x0x10 : check 27 13 1155 894 0 1691 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x0x11 : check 27 13 1155 983 2 1353 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x0x12 : check 27 13 1155 1072 4 1015 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x0 : check 28 13 1155 82 10 1 169 5917159763 = true := by
  apply check_step 27 13 1155 82 10 1 169 5917159763 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x0x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x0x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x0x2
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x0x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x0x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x0x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x0x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x0x8
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x0x10
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x0x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x0x12
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x2 : check 28 13 1155 259 1 118 169 5917159763 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x3 : check 28 13 1155 348 3 92 169 5917159763 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x4 : check 28 13 1155 437 5 66 169 5917159763 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x5x0 : check 27 13 1155 40 1 1054 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x5x1 : check 27 13 1155 129 3 716 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x5x2 : check 27 13 1155 218 5 378 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x5x3 : check 27 13 1155 307 7 40 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x5x6 : check 27 13 1155 573 0 1223 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x5x7 : check 27 13 1155 662 2 885 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x5x8 : check 27 13 1155 751 4 547 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x5x9 : check 27 13 1155 840 6 209 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x5 : check 28 13 1155 526 7 40 169 5917159763 = true := by
  apply check_step 27 13 1155 526 7 40 169 5917159763 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x5x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x5x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x5x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x5x3
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x5x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x5x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x5x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x5x9
  · norm_num at hb
  · norm_num at hb
  · norm_num at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x6x0 : check 27 13 1155 47 5 690 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x6x1 : check 27 13 1155 136 7 352 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x6x2x0 : check 26 13 1155 17 5 8802 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x6x2x1 : check 26 13 1155 106 7 4408 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x6x2x2 : check 26 13 1155 195 9 14 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x6x2x4 : check 26 13 1155 372 0 19787 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x6x2x5 : check 26 13 1155 461 2 15393 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x6x2x6 : check 26 13 1155 550 4 10999 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x6x2x7 : check 26 13 1155 639 6 6605 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x6x2x8 : check 26 13 1155 728 8 2211 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x6x2x11 : check 26 13 1155 994 1 17590 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x6x2x12 : check 26 13 1155 1083 3 13196 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x6x2 : check 27 13 1155 225 9 14 2197 455166135 = true := by
  apply check_step 26 13 1155 225 9 14 2197 455166135 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x6x2x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x6x2x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x6x2x2
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x6x2x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x6x2x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x6x2x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x6x2x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x6x2x8
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x6x2x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x6x2x12
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x6x4 : check 27 13 1155 402 0 1535 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x6x5 : check 27 13 1155 491 2 1197 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x6x6 : check 27 13 1155 580 4 859 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x6x7 : check 27 13 1155 669 6 521 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x6x8x0 : check 26 13 1155 58 4 8971 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x6x8x1 : check 26 13 1155 147 6 4577 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x6x8x2 : check 26 13 1155 236 8 183 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x6x8x5 : check 26 13 1155 502 1 15562 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x6x8x6 : check 26 13 1155 591 3 11168 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x6x8x7 : check 26 13 1155 680 5 6774 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x6x8x8 : check 26 13 1155 769 7 2380 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x6x8x11 : check 26 13 1155 1035 0 17759 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x6x8x12 : check 26 13 1155 1124 2 13365 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x6x8 : check 27 13 1155 758 8 183 2197 455166135 = true := by
  apply check_step 26 13 1155 758 8 183 2197 455166135 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x6x8x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x6x8x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x6x8x2
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x6x8x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x6x8x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x6x8x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x6x8x8
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x6x8x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x6x8x12
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x6x11 : check 27 13 1155 1024 1 1366 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x6x12 : check 27 13 1155 1113 3 1028 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x6 : check 28 13 1155 615 9 14 169 5917159763 = true := by
  apply check_step 27 13 1155 615 9 14 169 5917159763 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x6x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x6x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x6x2
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x6x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x6x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x6x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x6x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x6x8
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x6x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x6x12
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x8 : check 28 13 1155 792 0 131 169 5917159763 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x9 : check 28 13 1155 881 2 105 169 5917159763 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x10 : check 28 13 1155 970 4 79 169 5917159763 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x11 : check 28 13 1155 1059 6 53 169 5917159763 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x12x0 : check 27 13 1155 88 4 703 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x12x1 : check 27 13 1155 177 6 365 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x12x2x0 : check 26 13 1155 20 2 13209 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x12x2x1 : check 26 13 1155 109 4 8815 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x12x2x2 : check 26 13 1155 198 6 4421 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x12x2x3 : check 26 13 1155 287 8 27 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x12x2x6 : check 26 13 1155 553 1 15406 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x12x2x7 : check 26 13 1155 642 3 11012 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x12x2x8 : check 26 13 1155 731 5 6618 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x12x2x9 : check 26 13 1155 820 7 2224 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x12x2x12 : check 26 13 1155 1086 0 17603 28561 35012779 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x12x2 : check 27 13 1155 266 8 27 2197 455166135 = true := by
  apply check_step 26 13 1155 266 8 27 2197 455166135 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x12x2x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x12x2x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x12x2x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x12x2x3
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x12x2x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x12x2x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x12x2x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x12x2x9
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x12x2x12
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x12x5 : check 27 13 1155 532 1 1210 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x12x6 : check 27 13 1155 621 3 872 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x12x7 : check 27 13 1155 710 5 534 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x12x8 : check 27 13 1155 799 7 196 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x12x11 : check 27 13 1155 1065 0 1379 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x12x12 : check 27 13 1155 1154 2 1041 2197 455166135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11x12 : check 28 13 1155 1148 8 27 169 5917159763 = true := by
  apply check_step 27 13 1155 1148 8 27 169 5917159763 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x12x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x12x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x12x2
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x12x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x12x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x12x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x12x8
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x12x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x12x12
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13_x11 : check 29 13 1155 1066 10 1 13 76923076923 = true := by
  apply check_step 28 13 1155 1066 10 1 13 76923076923 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x0
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x6
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x10
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x12
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13 : check 30 13 1155 1154 11 0 1 999999999999 = true := by
  apply check_step 29 13 1155 1154 11 0 1 999999999999 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x10
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11
  · norm_num at hb
end VestigeBernoulliDigit

namespace VestigeBernoulliDigit
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x0x1 : check 28 17 15015 935 9 54 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x0x2 : check 28 17 15015 1818 5 122 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x0x3 : check 28 17 15015 2701 1 190 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x0x5x1 : check 27 17 15015 1146 9 326 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x0x5x2 : check 27 17 15015 2029 5 1482 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x0x5x3 : check 27 17 15015 2912 1 2638 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x0x5x5 : check 27 17 15015 4679 10 37 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x0x5x6 : check 27 17 15015 5562 6 1193 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x0x5x7 : check 27 17 15015 6445 2 2349 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x0x5x10 : check 27 17 15015 9095 7 904 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x0x5x11 : check 27 17 15015 9978 3 2060 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x0x5x14 : check 27 17 15015 12628 8 615 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x0x5x15 : check 27 17 15015 13511 4 1771 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x0x5x16 : check 27 17 15015 14394 0 2927 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x0x5 : check 28 17 15015 4468 10 37 289 3460207612 = true := by
  apply check_step 27 17 15015 4468 10 37 289 3460207612 (by norm_num)
  intro t ht hb
  interval_cases t
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x0x5x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x0x5x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x0x5x3
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x0x5x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x0x5x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x0x5x7
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x0x5x10
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x0x5x11
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x0x5x14
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x0x5x15
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x0x5x16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x0x6 : check 28 17 15015 5351 6 105 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x0x7 : check 28 17 15015 6234 2 173 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x0x9x0 : check 27 17 15015 470 0 3199 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x0x9x2 : check 27 17 15015 2237 9 598 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x0x9x3 : check 27 17 15015 3120 5 1754 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x0x9x4 : check 27 17 15015 4003 1 2910 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x0x9x6 : check 27 17 15015 5770 10 309 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x0x9x7 : check 27 17 15015 6653 6 1465 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x0x9x8 : check 27 17 15015 7536 2 2621 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x0x9x10 : check 27 17 15015 9303 11 20 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x0x9x11 : check 27 17 15015 10186 7 1176 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x0x9x12 : check 27 17 15015 11069 3 2332 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x0x9x15 : check 27 17 15015 13719 8 887 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x0x9x16 : check 27 17 15015 14602 4 2043 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x0x9 : check 28 17 15015 8001 11 20 289 3460207612 = true := by
  apply check_step 27 17 15015 8001 11 20 289 3460207612 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x0x9x0
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x0x9x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x0x9x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x0x9x4
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x0x9x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x0x9x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x0x9x8
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x0x9x10
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x0x9x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x0x9x12
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x0x9x15
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x0x9x16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x0x10 : check 28 17 15015 8884 7 88 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x0x11 : check 28 17 15015 9767 3 156 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x0x13x0 : check 27 17 15015 678 4 2315 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x0x13x1 : check 27 17 15015 1561 0 3471 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x0x13x3 : check 27 17 15015 3328 9 870 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x0x13x4 : check 27 17 15015 4211 5 2026 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x0x13x5 : check 27 17 15015 5094 1 3182 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x0x13x7 : check 27 17 15015 6861 10 581 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x0x13x8 : check 27 17 15015 7744 6 1737 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x0x13x9 : check 27 17 15015 8627 2 2893 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x0x13x11 : check 27 17 15015 10394 11 292 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x0x13x12 : check 27 17 15015 11277 7 1448 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x0x13x13 : check 27 17 15015 12160 3 2604 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x0x13x15 : check 27 17 15015 13927 12 3 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x0x13x16 : check 27 17 15015 14810 8 1159 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x0x13 : check 28 17 15015 11534 12 3 289 3460207612 = true := by
  apply check_step 27 17 15015 11534 12 3 289 3460207612 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x0x13x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x0x13x1
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x0x13x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x0x13x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x0x13x5
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x0x13x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x0x13x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x0x13x9
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x0x13x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x0x13x12
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x0x13x13
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x0x13x15
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x0x13x16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x0x14 : check 28 17 15015 12417 8 71 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x0x15 : check 28 17 15015 13300 4 139 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x0x16 : check 28 17 15015 14183 0 207 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x0 : check 29 17 15015 883 12 3 17 58823529411 = true := by
  apply check_step 28 17 15015 883 12 3 17 58823529411 (by norm_num)
  intro t ht hb
  interval_cases t
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x0x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x0x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x0x3
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x0x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x0x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x0x7
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x0x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x0x10
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x0x11
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x0x13
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x0x14
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x0x15
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x0x16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x1x1 : check 28 17 15015 987 6 41 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x1x2 : check 28 17 15015 1870 2 109 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x1x5 : check 28 17 15015 4520 7 24 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x1x6 : check 28 17 15015 5403 3 92 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x1x9 : check 28 17 15015 8053 8 7 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x1x10 : check 28 17 15015 8936 4 75 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x1x11 : check 28 17 15015 9819 0 143 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x1x14 : check 28 17 15015 12469 5 58 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x1x15 : check 28 17 15015 13352 1 126 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x1 : check 29 17 15015 1766 8 7 17 58823529411 = true := by
  apply check_step 28 17 15015 1766 8 7 17 58823529411 (by norm_num)
  intro t ht hb
  interval_cases t
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x1x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x1x2
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x1x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x1x6
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x1x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x1x10
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x1x11
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x1x14
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x1x15
  · norm_num at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x2 : check 29 17 15015 2649 4 11 17 58823529411 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x3 : check 29 17 15015 3532 0 15 17 58823529411 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x0 : check 28 17 15015 259 0 223 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x1x0 : check 27 17 15015 67 9 1158 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x1x1 : check 27 17 15015 950 5 2314 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x1x2 : check 27 17 15015 1833 1 3470 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x1x4 : check 27 17 15015 3600 10 869 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x1x5 : check 27 17 15015 4483 6 2025 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x1x6 : check 27 17 15015 5366 2 3181 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x1x8 : check 27 17 15015 7133 11 580 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x1x9 : check 27 17 15015 8016 7 1736 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x1x10 : check 27 17 15015 8899 3 2892 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x1x12 : check 27 17 15015 10666 12 291 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x1x13 : check 27 17 15015 11549 8 1447 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x1x14 : check 27 17 15015 12432 4 2603 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x1x15 : check 27 17 15015 13315 0 3759 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x1x16 : check 27 17 15015 14199 13 2 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x1 : check 28 17 15015 1143 13 2 289 3460207612 = true := by
  apply check_step 27 17 15015 1143 13 2 289 3460207612 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x1x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x1x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x1x2
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x1x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x1x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x1x6
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x1x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x1x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x1x10
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x1x12
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x1x13
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x1x14
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x1x15
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x1x16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x2 : check 28 17 15015 2026 9 70 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x3 : check 28 17 15015 2909 5 138 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x4 : check 28 17 15015 3792 1 206 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x6x0 : check 27 17 15015 327 10 53 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x6x1 : check 27 17 15015 1210 6 1209 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x6x2 : check 27 17 15015 2093 2 2365 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x6x5 : check 27 17 15015 4743 7 920 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x6x6 : check 27 17 15015 5626 3 2076 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x6x9 : check 27 17 15015 8276 8 631 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x6x10 : check 27 17 15015 9159 4 1787 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x6x11 : check 27 17 15015 10042 0 2943 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x6x13 : check 27 17 15015 11809 9 342 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x6x14 : check 27 17 15015 12692 5 1498 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x6x15 : check 27 17 15015 13575 1 2654 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x6 : check 28 17 15015 5559 10 53 289 3460207612 = true := by
  apply check_step 27 17 15015 5559 10 53 289 3460207612 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x6x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x6x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x6x2
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x6x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x6x6
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x6x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x6x10
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x6x11
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x6x13
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x6x14
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x6x15
  · norm_num at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x7 : check 28 17 15015 6442 6 121 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x8 : check 28 17 15015 7325 2 189 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x10x1 : check 27 17 15015 1418 10 325 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x10x2 : check 27 17 15015 2301 6 1481 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x10x3 : check 27 17 15015 3184 2 2637 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x10x5 : check 27 17 15015 4951 11 36 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x10x6 : check 27 17 15015 5834 7 1192 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x10x7 : check 27 17 15015 6717 3 2348 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x10x10 : check 27 17 15015 9367 8 903 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x10x11 : check 27 17 15015 10250 4 2059 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x10x12 : check 27 17 15015 11133 0 3215 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x10x14 : check 27 17 15015 12900 9 614 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x10x15 : check 27 17 15015 13783 5 1770 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x10x16 : check 27 17 15015 14666 1 2926 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x10 : check 28 17 15015 9092 11 36 289 3460207612 = true := by
  apply check_step 27 17 15015 9092 11 36 289 3460207612 (by norm_num)
  intro t ht hb
  interval_cases t
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x10x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x10x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x10x3
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x10x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x10x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x10x7
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x10x10
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x10x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x10x12
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x10x14
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x10x15
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x10x16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x11 : check 28 17 15015 9975 7 104 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x12 : check 28 17 15015 10858 3 172 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x14x0 : check 27 17 15015 742 1 3198 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x14x2 : check 27 17 15015 2509 10 597 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x14x3 : check 27 17 15015 3392 6 1753 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x14x4 : check 27 17 15015 4275 2 2909 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x14x6 : check 27 17 15015 6042 11 308 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x14x7 : check 27 17 15015 6925 7 1464 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x14x8 : check 27 17 15015 7808 3 2620 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x14x10 : check 27 17 15015 9575 12 19 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x14x11 : check 27 17 15015 10458 8 1175 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x14x12 : check 27 17 15015 11341 4 2331 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x14x13 : check 27 17 15015 12224 0 3487 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x14x15 : check 27 17 15015 13991 9 886 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x14x16 : check 27 17 15015 14874 5 2042 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x14 : check 28 17 15015 12625 12 19 289 3460207612 = true := by
  apply check_step 27 17 15015 12625 12 19 289 3460207612 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x14x0
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x14x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x14x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x14x4
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x14x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x14x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x14x8
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x14x10
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x14x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x14x12
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x14x13
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x14x15
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x14x16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x15 : check 28 17 15015 13508 8 87 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4x16 : check 28 17 15015 14391 4 155 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x4 : check 29 17 15015 4416 13 2 17 58823529411 = true := by
  apply check_step 28 17 15015 4416 13 2 17 58823529411 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x4
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x8
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x10
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x12
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x14
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x15
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x5x2 : check 28 17 15015 2078 6 57 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x5x3 : check 28 17 15015 2961 2 125 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x5x6 : check 28 17 15015 5611 7 40 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x5x7 : check 28 17 15015 6494 3 108 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x5x10 : check 28 17 15015 9144 8 23 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x5x11 : check 28 17 15015 10027 4 91 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x5x12 : check 28 17 15015 10910 0 159 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x5x14 : check 28 17 15015 12677 9 6 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x5x15 : check 28 17 15015 13560 5 74 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x5x16 : check 28 17 15015 14443 1 142 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x5 : check 29 17 15015 5299 9 6 17 58823529411 = true := by
  apply check_step 28 17 15015 5299 9 6 17 58823529411 (by norm_num)
  intro t ht hb
  interval_cases t
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x5x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x5x3
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x5x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x5x7
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x5x10
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x5x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x5x12
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x5x14
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x5x15
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x5x16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x6 : check 29 17 15015 6182 5 10 17 58823529411 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x7 : check 29 17 15015 7065 1 14 17 58823529411 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x0 : check 28 17 15015 467 4 171 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x1 : check 28 17 15015 1350 0 239 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x2x0 : check 27 17 15015 131 6 2041 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x2x1 : check 27 17 15015 1014 2 3197 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x2x3 : check 27 17 15015 2781 11 596 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x2x4 : check 27 17 15015 3664 7 1752 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x2x5 : check 27 17 15015 4547 3 2908 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x2x7 : check 27 17 15015 6314 12 307 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x2x8 : check 27 17 15015 7197 8 1463 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x2x9 : check 27 17 15015 8080 4 2619 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x2x10 : check 27 17 15015 8963 0 3775 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x2x11 : check 27 17 15015 9847 13 18 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x2x12 : check 27 17 15015 10730 9 1174 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x2x13 : check 27 17 15015 11613 5 2330 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x2x14 : check 27 17 15015 12496 1 3486 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x2x16 : check 27 17 15015 14263 10 885 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x2 : check 28 17 15015 2234 13 18 289 3460207612 = true := by
  apply check_step 27 17 15015 2234 13 18 289 3460207612 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x2x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x2x1
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x2x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x2x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x2x5
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x2x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x2x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x2x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x2x10
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x2x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x2x12
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x2x13
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x2x14
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x2x16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x3 : check 28 17 15015 3117 9 86 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x4 : check 28 17 15015 4000 5 154 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x5 : check 28 17 15015 4883 1 222 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x6x0 : check 27 17 15015 339 10 1157 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x6x1 : check 27 17 15015 1222 6 2313 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x6x2 : check 27 17 15015 2105 2 3469 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x6x4 : check 27 17 15015 3872 11 868 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x6x5 : check 27 17 15015 4755 7 2024 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x6x6 : check 27 17 15015 5638 3 3180 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x6x8 : check 27 17 15015 7405 12 579 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x6x9 : check 27 17 15015 8288 8 1735 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x6x10 : check 27 17 15015 9171 4 2891 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x6x11 : check 27 17 15015 10054 0 4047 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x6x12 : check 27 17 15015 10938 13 290 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x6x13 : check 27 17 15015 11821 9 1446 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x6x14 : check 27 17 15015 12704 5 2602 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x6x15 : check 27 17 15015 13587 1 3758 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x6x16x0 : check 26 17 15015 851 10 19653 83521 11973036 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x6x16x1 : check 26 17 15015 1734 6 39305 83521 11973036 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x6x16x2 : check 26 17 15015 2617 2 58957 83521 11973036 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x6x16x4 : check 26 17 15015 4384 11 14740 83521 11973036 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x6x16x5 : check 26 17 15015 5267 7 34392 83521 11973036 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x6x16x6 : check 26 17 15015 6150 3 54044 83521 11973036 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x6x16x8 : check 26 17 15015 7917 12 9827 83521 11973036 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x6x16x9 : check 26 17 15015 8800 8 29479 83521 11973036 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x6x16x10 : check 26 17 15015 9683 4 49131 83521 11973036 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x6x16x11 : check 26 17 15015 10566 0 68783 83521 11973036 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x6x16x12 : check 26 17 15015 11450 13 4914 83521 11973036 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x6x16x13 : check 26 17 15015 12333 9 24566 83521 11973036 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x6x16x14 : check 26 17 15015 13216 5 44218 83521 11973036 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x6x16x15 : check 26 17 15015 14099 1 63870 83521 11973036 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x6x16x16 : check 26 17 15015 14983 14 1 83521 11973036 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x6x16 : check 27 17 15015 14471 14 1 4913 203541624 = true := by
  apply check_step 26 17 15015 14471 14 1 4913 203541624 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x6x16x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x6x16x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x6x16x2
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x6x16x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x6x16x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x6x16x6
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x6x16x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x6x16x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x6x16x10
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x6x16x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x6x16x12
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x6x16x13
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x6x16x14
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x6x16x15
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x6x16x16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x6 : check 28 17 15015 5767 14 1 289 3460207612 = true := by
  apply check_step 27 17 15015 5767 14 1 289 3460207612 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x6x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x6x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x6x2
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x6x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x6x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x6x6
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x6x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x6x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x6x10
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x6x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x6x12
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x6x13
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x6x14
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x6x15
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x6x16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x7x0 : check 27 17 15015 391 7 936 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x7x1 : check 27 17 15015 1274 3 2092 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x7x4 : check 27 17 15015 3924 8 647 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x7x5 : check 27 17 15015 4807 4 1803 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x7x6 : check 27 17 15015 5690 0 2959 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x7x8 : check 27 17 15015 7457 9 358 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x7x9 : check 27 17 15015 8340 5 1514 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x7x10 : check 27 17 15015 9223 1 2670 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x7x12 : check 27 17 15015 10990 10 69 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x7x13 : check 27 17 15015 11873 6 1225 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x7x14 : check 27 17 15015 12756 2 2381 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x7 : check 28 17 15015 6650 10 69 289 3460207612 = true := by
  apply check_step 27 17 15015 6650 10 69 289 3460207612 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x7x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x7x1
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x7x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x7x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x7x6
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x7x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x7x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x7x10
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x7x12
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x7x13
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x7x14
  · norm_num at hb
  · norm_num at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x8 : check 28 17 15015 7533 6 137 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x9 : check 28 17 15015 8416 2 205 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x11x0 : check 27 17 15015 599 11 52 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x11x1 : check 27 17 15015 1482 7 1208 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x11x2 : check 27 17 15015 2365 3 2364 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x11x5 : check 27 17 15015 5015 8 919 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x11x6 : check 27 17 15015 5898 4 2075 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x11x7 : check 27 17 15015 6781 0 3231 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x11x9 : check 27 17 15015 8548 9 630 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x11x10 : check 27 17 15015 9431 5 1786 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x11x11 : check 27 17 15015 10314 1 2942 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x11x13 : check 27 17 15015 12081 10 341 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x11x14 : check 27 17 15015 12964 6 1497 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x11x15 : check 27 17 15015 13847 2 2653 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x11 : check 28 17 15015 10183 11 52 289 3460207612 = true := by
  apply check_step 27 17 15015 10183 11 52 289 3460207612 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x11x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x11x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x11x2
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x11x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x11x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x11x7
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x11x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x11x10
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x11x11
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x11x13
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x11x14
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x11x15
  · norm_num at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x12 : check 28 17 15015 11066 7 120 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x13 : check 28 17 15015 11949 3 188 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x15x1 : check 27 17 15015 1690 11 324 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x15x2 : check 27 17 15015 2573 7 1480 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x15x3 : check 27 17 15015 3456 3 2636 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x15x5 : check 27 17 15015 5223 12 35 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x15x6 : check 27 17 15015 6106 8 1191 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x15x7 : check 27 17 15015 6989 4 2347 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x15x8 : check 27 17 15015 7872 0 3503 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x15x10 : check 27 17 15015 9639 9 902 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x15x11 : check 27 17 15015 10522 5 2058 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x15x12 : check 27 17 15015 11405 1 3214 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x15x14 : check 27 17 15015 13172 10 613 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x15x15 : check 27 17 15015 14055 6 1769 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x15x16 : check 27 17 15015 14938 2 2925 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x15 : check 28 17 15015 13716 12 35 289 3460207612 = true := by
  apply check_step 27 17 15015 13716 12 35 289 3460207612 (by norm_num)
  intro t ht hb
  interval_cases t
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x15x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x15x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x15x3
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x15x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x15x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x15x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x15x8
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x15x10
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x15x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x15x12
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x15x14
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x15x15
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x15x16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8x16 : check 28 17 15015 14599 8 103 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x8 : check 29 17 15015 7949 14 1 17 58823529411 = true := by
  apply check_step 28 17 15015 7949 14 1 17 58823529411 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x9
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x12
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x13
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x15
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x9x0 : check 28 17 15015 519 1 158 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x9x2x0 : check 27 17 15015 134 2 2317 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x9x2x3 : check 27 17 15015 2784 7 872 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x9x2x4 : check 27 17 15015 3667 3 2028 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x9x2x7 : check 27 17 15015 6317 8 583 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x9x2x8 : check 27 17 15015 7200 4 1739 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x9x2x9 : check 27 17 15015 8083 0 2895 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x9x2x11 : check 27 17 15015 9850 9 294 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x9x2x12 : check 27 17 15015 10733 5 1450 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x9x2x13 : check 27 17 15015 11616 1 2606 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x9x2x15 : check 27 17 15015 13383 10 5 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x9x2x16 : check 27 17 15015 14266 6 1161 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x9x2 : check 28 17 15015 2286 10 5 289 3460207612 = true := by
  apply check_step 27 17 15015 2286 10 5 289 3460207612 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x9x2x0
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x9x2x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x9x2x4
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x9x2x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x9x2x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x9x2x9
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x9x2x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x9x2x12
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x9x2x13
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x9x2x15
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x9x2x16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x9x3 : check 28 17 15015 3169 6 73 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x9x4 : check 28 17 15015 4052 2 141 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x9x7 : check 28 17 15015 6702 7 56 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x9x8 : check 28 17 15015 7585 3 124 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x9x11 : check 28 17 15015 10235 8 39 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x9x12 : check 28 17 15015 11118 4 107 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x9x13 : check 28 17 15015 12001 0 175 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x9x15 : check 28 17 15015 13768 9 22 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x9x16 : check 28 17 15015 14651 5 90 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x9 : check 29 17 15015 8832 10 5 17 58823529411 = true := by
  apply check_step 28 17 15015 8832 10 5 17 58823529411 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x9x0
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x9x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x9x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x9x4
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x9x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x9x8
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x9x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x9x12
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x9x13
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x9x15
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x9x16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x10 : check 29 17 15015 9715 6 9 17 58823529411 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x11 : check 29 17 15015 10598 2 13 17 58823529411 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x0 : check 28 17 15015 675 8 119 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x1 : check 28 17 15015 1558 4 187 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x2 : check 28 17 15015 2441 0 255 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x3x0 : check 27 17 15015 195 3 2924 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x3x2 : check 27 17 15015 1962 12 323 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x3x3 : check 27 17 15015 2845 8 1479 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x3x4 : check 27 17 15015 3728 4 2635 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x3x5 : check 27 17 15015 4611 0 3791 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x3x6 : check 27 17 15015 5495 13 34 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x3x7 : check 27 17 15015 6378 9 1190 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x3x8 : check 27 17 15015 7261 5 2346 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x3x9 : check 27 17 15015 8144 1 3502 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x3x11 : check 27 17 15015 9911 10 901 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x3x12 : check 27 17 15015 10794 6 2057 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x3x13 : check 27 17 15015 11677 2 3213 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x3x15 : check 27 17 15015 13444 11 612 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x3x16 : check 27 17 15015 14327 7 1768 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x3 : check 28 17 15015 3325 13 34 289 3460207612 = true := by
  apply check_step 27 17 15015 3325 13 34 289 3460207612 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x3x0
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x3x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x3x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x3x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x3x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x3x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x3x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x3x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x3x9
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x3x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x3x12
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x3x13
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x3x15
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x3x16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x4 : check 28 17 15015 4208 9 102 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x5 : check 28 17 15015 5091 5 170 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x6 : check 28 17 15015 5974 1 238 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x7x0 : check 27 17 15015 403 7 2040 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x7x1 : check 27 17 15015 1286 3 3196 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x7x3 : check 27 17 15015 3053 12 595 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x7x4 : check 27 17 15015 3936 8 1751 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x7x5 : check 27 17 15015 4819 4 2907 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x7x6 : check 27 17 15015 5702 0 4063 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x7x7 : check 27 17 15015 6586 13 306 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x7x8 : check 27 17 15015 7469 9 1462 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x7x9 : check 27 17 15015 8352 5 2618 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x7x10 : check 27 17 15015 9235 1 3774 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x7x11x0 : check 26 17 15015 595 10 19669 83521 11973036 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x7x11x1 : check 26 17 15015 1478 6 39321 83521 11973036 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x7x11x2 : check 26 17 15015 2361 2 58973 83521 11973036 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x7x11x4 : check 26 17 15015 4128 11 14756 83521 11973036 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x7x11x5 : check 26 17 15015 5011 7 34408 83521 11973036 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x7x11x6 : check 26 17 15015 5894 3 54060 83521 11973036 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x7x11x8 : check 26 17 15015 7661 12 9843 83521 11973036 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x7x11x9 : check 26 17 15015 8544 8 29495 83521 11973036 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x7x11x10 : check 26 17 15015 9427 4 49147 83521 11973036 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x7x11x11 : check 26 17 15015 10310 0 68799 83521 11973036 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x7x11x12 : check 26 17 15015 11194 13 4930 83521 11973036 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x7x11x13 : check 26 17 15015 12077 9 24582 83521 11973036 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x7x11x14 : check 26 17 15015 12960 5 44234 83521 11973036 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x7x11x15 : check 26 17 15015 13843 1 63886 83521 11973036 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x7x11x16 : check 26 17 15015 14727 14 17 83521 11973036 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x7x11 : check 27 17 15015 10119 14 17 4913 203541624 = true := by
  apply check_step 26 17 15015 10119 14 17 4913 203541624 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x7x11x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x7x11x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x7x11x2
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x7x11x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x7x11x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x7x11x6
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x7x11x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x7x11x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x7x11x10
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x7x11x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x7x11x12
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x7x11x13
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x7x11x14
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x7x11x15
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x7x11x16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x7x12 : check 27 17 15015 11002 10 1173 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x7x13 : check 27 17 15015 11885 6 2329 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x7x14 : check 27 17 15015 12768 2 3485 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x7x16 : check 27 17 15015 14535 11 884 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x7 : check 28 17 15015 6858 14 17 289 3460207612 = true := by
  apply check_step 27 17 15015 6858 14 17 289 3460207612 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x7x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x7x1
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x7x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x7x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x7x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x7x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x7x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x7x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x7x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x7x10
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x7x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x7x12
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x7x13
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x7x14
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x7x16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x8x0 : check 27 17 15015 455 4 1819 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x8x1 : check 27 17 15015 1338 0 2975 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x8x3 : check 27 17 15015 3105 9 374 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x8x4 : check 27 17 15015 3988 5 1530 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x8x5 : check 27 17 15015 4871 1 2686 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x8x7 : check 27 17 15015 6638 10 85 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x8x8 : check 27 17 15015 7521 6 1241 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x8x9 : check 27 17 15015 8404 2 2397 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x8x12 : check 27 17 15015 11054 7 952 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x8x13 : check 27 17 15015 11937 3 2108 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x8x16 : check 27 17 15015 14587 8 663 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x8 : check 28 17 15015 7741 10 85 289 3460207612 = true := by
  apply check_step 27 17 15015 7741 10 85 289 3460207612 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x8x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x8x1
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x8x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x8x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x8x5
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x8x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x8x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x8x9
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x8x12
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x8x13
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x8x16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x9 : check 28 17 15015 8624 6 153 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x10 : check 28 17 15015 9507 2 221 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x11x0 : check 27 17 15015 611 11 1156 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x11x1 : check 27 17 15015 1494 7 2312 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x11x2 : check 27 17 15015 2377 3 3468 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x11x4 : check 27 17 15015 4144 12 867 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x11x5 : check 27 17 15015 5027 8 2023 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x11x6 : check 27 17 15015 5910 4 3179 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x11x7 : check 27 17 15015 6793 0 4335 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x11x8 : check 27 17 15015 7677 13 578 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x11x9 : check 27 17 15015 8560 9 1734 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x11x10 : check 27 17 15015 9443 5 2890 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x11x11 : check 27 17 15015 10326 1 4046 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x11x12x0 : check 26 17 15015 659 7 34680 83521 11973036 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x11x12x1 : check 26 17 15015 1542 3 54332 83521 11973036 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x11x12x3 : check 26 17 15015 3309 12 10115 83521 11973036 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x11x12x4 : check 26 17 15015 4192 8 29767 83521 11973036 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x11x12x5 : check 26 17 15015 5075 4 49419 83521 11973036 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x11x12x6 : check 26 17 15015 5958 0 69071 83521 11973036 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x11x12x7 : check 26 17 15015 6842 13 5202 83521 11973036 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x11x12x8 : check 26 17 15015 7725 9 24854 83521 11973036 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x11x12x9 : check 26 17 15015 8608 5 44506 83521 11973036 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x11x12x10 : check 26 17 15015 9491 1 64158 83521 11973036 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x11x12x11 : check 26 17 15015 10375 14 289 83521 11973036 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x11x12x12 : check 26 17 15015 11258 10 19941 83521 11973036 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x11x12x13 : check 26 17 15015 12141 6 39593 83521 11973036 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x11x12x14 : check 26 17 15015 13024 2 59245 83521 11973036 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x11x12x16 : check 26 17 15015 14791 11 15028 83521 11973036 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x11x12 : check 27 17 15015 11210 14 289 4913 203541624 = true := by
  apply check_step 26 17 15015 11210 14 289 4913 203541624 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x12x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x12x1
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x12x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x12x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x12x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x12x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x12x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x12x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x12x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x12x10
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x12x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x12x12
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x12x13
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x12x14
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x12x16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x11x13 : check 27 17 15015 12093 10 1445 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x11x14 : check 27 17 15015 12976 6 2601 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x11x15 : check 27 17 15015 13859 2 3757 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x11x16x0 : check 26 17 15015 867 11 19652 83521 11973036 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x11x16x1 : check 26 17 15015 1750 7 39304 83521 11973036 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x11x16x2 : check 26 17 15015 2633 3 58956 83521 11973036 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x11x16x4 : check 26 17 15015 4400 12 14739 83521 11973036 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x11x16x5 : check 26 17 15015 5283 8 34391 83521 11973036 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x11x16x6 : check 26 17 15015 6166 4 54043 83521 11973036 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x11x16x7 : check 26 17 15015 7049 0 73695 83521 11973036 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x11x16x8 : check 26 17 15015 7933 13 9826 83521 11973036 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x11x16x9 : check 26 17 15015 8816 9 29478 83521 11973036 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x11x16x10 : check 26 17 15015 9699 5 49130 83521 11973036 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x11x16x11 : check 26 17 15015 10582 1 68782 83521 11973036 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x11x16x12 : check 26 17 15015 11466 14 4913 83521 11973036 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x11x16x13 : check 26 17 15015 12349 10 24565 83521 11973036 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x11x16x14 : check 26 17 15015 13232 6 44217 83521 11973036 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x11x16x15 : check 26 17 15015 14115 2 63869 83521 11973036 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x11x16x16 : check 26 17 15015 14999 15 0 83521 11973036 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x11x16 : check 27 17 15015 14743 15 0 4913 203541624 = true := by
  apply check_step 26 17 15015 14743 15 0 4913 203541624 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x16x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x16x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x16x2
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x16x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x16x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x16x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x16x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x16x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x16x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x16x10
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x16x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x16x12
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x16x13
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x16x14
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x16x15
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x16x16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x11 : check 28 17 15015 10391 15 0 289 3460207612 = true := by
  apply check_step 27 17 15015 10391 15 0 289 3460207612 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x2
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x10
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x12
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x13
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x14
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x15
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x12x0 : check 27 17 15015 663 8 935 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x12x1 : check 27 17 15015 1546 4 2091 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x12x2 : check 27 17 15015 2429 0 3247 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x12x4 : check 27 17 15015 4196 9 646 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x12x5 : check 27 17 15015 5079 5 1802 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x12x6 : check 27 17 15015 5962 1 2958 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x12x8 : check 27 17 15015 7729 10 357 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x12x9 : check 27 17 15015 8612 6 1513 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x12x10 : check 27 17 15015 9495 2 2669 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x12x12 : check 27 17 15015 11262 11 68 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x12x13 : check 27 17 15015 12145 7 1224 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x12x14 : check 27 17 15015 13028 3 2380 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x12 : check 28 17 15015 11274 11 68 289 3460207612 = true := by
  apply check_step 27 17 15015 11274 11 68 289 3460207612 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x12x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x12x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x12x2
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x12x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x12x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x12x6
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x12x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x12x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x12x10
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x12x12
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x12x13
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x12x14
  · norm_num at hb
  · norm_num at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x13 : check 28 17 15015 12157 7 136 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x14 : check 28 17 15015 13040 3 204 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x16x0 : check 27 17 15015 871 12 51 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x16x1 : check 27 17 15015 1754 8 1207 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x16x2 : check 27 17 15015 2637 4 2363 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x16x3 : check 27 17 15015 3520 0 3519 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x16x5 : check 27 17 15015 5287 9 918 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x16x6 : check 27 17 15015 6170 5 2074 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x16x7 : check 27 17 15015 7053 1 3230 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x16x9 : check 27 17 15015 8820 10 629 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x16x10 : check 27 17 15015 9703 6 1785 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x16x11 : check 27 17 15015 10586 2 2941 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x16x13 : check 27 17 15015 12353 11 340 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x16x14 : check 27 17 15015 13236 7 1496 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x16x15 : check 27 17 15015 14119 3 2652 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12x16 : check 28 17 15015 14807 12 51 289 3460207612 = true := by
  apply check_step 27 17 15015 14807 12 51 289 3460207612 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x16x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x16x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x16x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x16x3
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x16x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x16x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x16x7
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x16x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x16x10
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x16x11
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x16x13
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x16x14
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x16x15
  · norm_num at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x12 : check 29 17 15015 11482 15 0 17 58823529411 = true := by
  apply check_step 28 17 15015 11482 15 0 17 58823529411 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x10
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x12
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x13
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x14
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x13x0 : check 28 17 15015 727 5 106 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x13x1 : check 28 17 15015 1610 1 174 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x13x3x2 : check 27 17 15015 1965 8 599 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x13x3x3 : check 27 17 15015 2848 4 1755 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x13x3x4 : check 27 17 15015 3731 0 2911 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x13x3x6 : check 27 17 15015 5498 9 310 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x13x3x7 : check 27 17 15015 6381 5 1466 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x13x3x8 : check 27 17 15015 7264 1 2622 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x13x3x10 : check 27 17 15015 9031 10 21 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x13x3x11 : check 27 17 15015 9914 6 1177 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x13x3x12 : check 27 17 15015 10797 2 2333 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x13x3x15 : check 27 17 15015 13447 7 888 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x13x3x16 : check 27 17 15015 14330 3 2044 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x13x3 : check 28 17 15015 3377 10 21 289 3460207612 = true := by
  apply check_step 27 17 15015 3377 10 21 289 3460207612 (by norm_num)
  intro t ht hb
  interval_cases t
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x13x3x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x13x3x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x13x3x4
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x13x3x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x13x3x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x13x3x8
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x13x3x10
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x13x3x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x13x3x12
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x13x3x15
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x13x3x16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x13x4 : check 28 17 15015 4260 6 89 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x13x5 : check 28 17 15015 5143 2 157 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x13x7x0 : check 27 17 15015 406 3 2316 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x13x7x3 : check 27 17 15015 3056 8 871 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x13x7x4 : check 27 17 15015 3939 4 2027 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x13x7x5 : check 27 17 15015 4822 0 3183 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x13x7x7 : check 27 17 15015 6589 9 582 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x13x7x8 : check 27 17 15015 7472 5 1738 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x13x7x9 : check 27 17 15015 8355 1 2894 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x13x7x11 : check 27 17 15015 10122 10 293 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x13x7x12 : check 27 17 15015 11005 6 1449 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x13x7x13 : check 27 17 15015 11888 2 2605 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x13x7x15 : check 27 17 15015 13655 11 4 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x13x7x16 : check 27 17 15015 14538 7 1160 4913 203541624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x13x7 : check 28 17 15015 6910 11 4 289 3460207612 = true := by
  apply check_step 27 17 15015 6910 11 4 289 3460207612 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x13x7x0
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x13x7x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x13x7x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x13x7x5
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x13x7x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x13x7x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x13x7x9
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x13x7x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x13x7x12
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x13x7x13
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x13x7x15
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x13x7x16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x13x8 : check 28 17 15015 7793 7 72 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x13x9 : check 28 17 15015 8676 3 140 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x13x12 : check 28 17 15015 11326 8 55 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x13x13 : check 28 17 15015 12209 4 123 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x13x14 : check 28 17 15015 13092 0 191 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x13x16 : check 28 17 15015 14859 9 38 289 3460207612 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x13 : check 29 17 15015 12365 11 4 17 58823529411 = true := by
  apply check_step 28 17 15015 12365 11 4 17 58823529411 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x13x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x13x1
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x13x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x13x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x13x5
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x13x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x13x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x13x9
  · norm_num at hb
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x13x12
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x13x13
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x13x14
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x13x16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x14 : check 29 17 15015 13248 7 8 17 58823529411 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17_x15 : check 29 17 15015 14131 3 12 17 58823529411 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17 : check 30 17 15015 15014 15 0 1 999999999999 = true := by
  apply check_step 29 17 15015 15014 15 0 1 999999999999 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x13
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x15
  · norm_num at hb
end VestigeBernoulliDigit

namespace VestigeBernoulliDigit
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x0 : check 29 19 255255 13434 9 8 19 52631578947 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x1 : check 29 19 255255 26868 0 17 19 52631578947 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x2x0 : check 28 19 255255 2121 6 83 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x2x2 : check 28 19 255255 28990 7 64 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x2x4 : check 28 19 255255 55859 8 45 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x2x6 : check 28 19 255255 82728 9 26 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x2x7 : check 28 19 255255 96162 0 197 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x2x8 : check 28 19 255255 109597 10 7 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x2x9 : check 28 19 255255 123031 1 178 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x2x11 : check 28 19 255255 149900 2 159 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x2x13 : check 28 19 255255 176769 3 140 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x2x15 : check 28 19 255255 203638 4 121 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x2x17 : check 28 19 255255 230507 5 102 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x2 : check 29 19 255255 40303 10 7 19 52631578947 = true := by
  apply check_step 28 19 255255 40303 10 7 19 52631578947 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x2x0
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x2x2
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x2x4
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x2x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x2x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x2x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x2x9
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x2x11
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x2x13
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x2x15
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x2x17
  · norm_num at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x3 : check 29 19 255255 53737 1 16 19 52631578947 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x4x0 : check 28 19 255255 3535 4 139 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x4x2 : check 28 19 255255 30404 5 120 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x4x4 : check 28 19 255255 57273 6 101 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x4x6 : check 28 19 255255 84142 7 82 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x4x8 : check 28 19 255255 111011 8 63 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x4x10 : check 28 19 255255 137880 9 44 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x4x11 : check 28 19 255255 151314 0 215 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x4x12 : check 28 19 255255 164749 10 25 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x4x13 : check 28 19 255255 178183 1 196 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x4x14 : check 28 19 255255 191618 11 6 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x4x15 : check 28 19 255255 205052 2 177 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x4x17 : check 28 19 255255 231921 3 158 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x4 : check 29 19 255255 67172 11 6 19 52631578947 = true := by
  apply check_step 28 19 255255 67172 11 6 19 52631578947 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x4x0
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x4x2
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x4x4
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x4x6
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x4x8
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x4x10
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x4x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x4x12
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x4x13
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x4x14
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x4x15
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x4x17
  · norm_num at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x5 : check 29 19 255255 80606 2 15 19 52631578947 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x6x0 : check 28 19 255255 4949 2 195 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x6x1 : check 28 19 255255 18384 12 5 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x6x2 : check 28 19 255255 31818 3 176 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x6x4 : check 28 19 255255 58687 4 157 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x6x6 : check 28 19 255255 85556 5 138 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x6x8 : check 28 19 255255 112425 6 119 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x6x10 : check 28 19 255255 139294 7 100 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x6x12 : check 28 19 255255 166163 8 81 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x6x14 : check 28 19 255255 193032 9 62 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x6x15 : check 28 19 255255 206466 0 233 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x6x16 : check 28 19 255255 219901 10 43 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x6x17 : check 28 19 255255 233335 1 214 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x6x18 : check 28 19 255255 246770 11 24 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x6 : check 29 19 255255 94041 12 5 19 52631578947 = true := by
  apply check_step 28 19 255255 94041 12 5 19 52631578947 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x6x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x6x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x6x2
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x6x4
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x6x6
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x6x8
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x6x10
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x6x12
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x6x14
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x6x15
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x6x16
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x6x17
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x6x18
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x7 : check 29 19 255255 107475 3 14 19 52631578947 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x8x0 : check 28 19 255255 6363 0 251 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x8x1 : check 28 19 255255 19798 10 61 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x8x2 : check 28 19 255255 33232 1 232 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x8x3 : check 28 19 255255 46667 11 42 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x8x4 : check 28 19 255255 60101 2 213 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x8x5 : check 28 19 255255 73536 12 23 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x8x6 : check 28 19 255255 86970 3 194 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x8x7 : check 28 19 255255 100405 13 4 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x8x8 : check 28 19 255255 113839 4 175 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x8x10 : check 28 19 255255 140708 5 156 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x8x12 : check 28 19 255255 167577 6 137 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x8x14 : check 28 19 255255 194446 7 118 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x8x16 : check 28 19 255255 221315 8 99 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x8x18 : check 28 19 255255 248184 9 80 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x8 : check 29 19 255255 120910 13 4 19 52631578947 = true := by
  apply check_step 28 19 255255 120910 13 4 19 52631578947 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x8x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x8x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x8x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x8x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x8x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x8x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x8x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x8x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x8x8
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x8x10
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x8x12
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x8x14
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x8x16
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x8x18
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x9 : check 29 19 255255 134344 4 13 19 52631578947 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x10x1 : check 28 19 255255 21212 8 117 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x10x3 : check 28 19 255255 48081 9 98 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x10x4 : check 28 19 255255 61515 0 269 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x10x5 : check 28 19 255255 74950 10 79 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x10x6 : check 28 19 255255 88384 1 250 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x10x7 : check 28 19 255255 101819 11 60 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x10x8 : check 28 19 255255 115253 2 231 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x10x9 : check 28 19 255255 128688 12 41 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x10x10 : check 28 19 255255 142122 3 212 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x10x11 : check 28 19 255255 155557 13 22 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x10x12 : check 28 19 255255 168991 4 193 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x10x13x0 : check 27 19 255255 9601 7 2530 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x10x13x2 : check 27 19 255255 36470 8 2169 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x10x13x4 : check 27 19 255255 63339 9 1808 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x10x13x5 : check 27 19 255255 76773 0 5057 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x10x13x6 : check 27 19 255255 90208 10 1447 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x10x13x7 : check 27 19 255255 103642 1 4696 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x10x13x8 : check 27 19 255255 117077 11 1086 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x10x13x9 : check 27 19 255255 130511 2 4335 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x10x13x10 : check 27 19 255255 143946 12 725 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x10x13x11 : check 27 19 255255 157380 3 3974 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x10x13x12 : check 27 19 255255 170815 13 364 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x10x13x13 : check 27 19 255255 184249 4 3613 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x10x13x14 : check 27 19 255255 197684 14 3 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x10x13x15 : check 27 19 255255 211118 5 3252 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x10x13x17 : check 27 19 255255 237987 6 2891 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x10x13 : check 28 19 255255 182426 14 3 361 2770083102 = true := by
  apply check_step 27 19 255255 182426 14 3 361 2770083102 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x10x13x0
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x10x13x2
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x10x13x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x10x13x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x10x13x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x10x13x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x10x13x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x10x13x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x10x13x10
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x10x13x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x10x13x12
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x10x13x13
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x10x13x14
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x10x13x15
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x10x13x17
  · norm_num at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x10x14 : check 28 19 255255 195860 5 174 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x10x16 : check 28 19 255255 222729 6 155 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x10x18 : check 28 19 255255 249598 7 136 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x10 : check 29 19 255255 147779 14 3 19 52631578947 = true := by
  apply check_step 28 19 255255 147779 14 3 19 52631578947 (by norm_num)
  intro t ht hb
  interval_cases t
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x10x1
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x10x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x10x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x10x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x10x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x10x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x10x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x10x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x10x10
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x10x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x10x12
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x10x13
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x10x14
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x10x16
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x10x18
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x11 : check 29 19 255255 161213 5 12 19 52631578947 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x12x0x0 : check 27 19 255255 483 0 5417 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x12x0x1 : check 27 19 255255 13918 10 1807 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x12x0x2 : check 27 19 255255 27352 1 5056 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x12x0x3 : check 27 19 255255 40787 11 1446 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x12x0x4 : check 27 19 255255 54221 2 4695 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x12x0x5 : check 27 19 255255 67656 12 1085 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x12x0x6 : check 27 19 255255 81090 3 4334 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x12x0x7 : check 27 19 255255 94525 13 724 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x12x0x8 : check 27 19 255255 107959 4 3973 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x12x0x9 : check 27 19 255255 121394 14 363 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x12x0x10 : check 27 19 255255 134828 5 3612 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x12x0x11 : check 27 19 255255 148263 15 2 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x12x0x12 : check 27 19 255255 161697 6 3251 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x12x0x14 : check 27 19 255255 188566 7 2890 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x12x0x16 : check 27 19 255255 215435 8 2529 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x12x0x18 : check 27 19 255255 242304 9 2168 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x12x0 : check 28 19 255255 9192 15 2 361 2770083102 = true := by
  apply check_step 27 19 255255 9192 15 2 361 2770083102 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x12x0x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x12x0x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x12x0x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x12x0x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x12x0x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x12x0x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x12x0x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x12x0x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x12x0x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x12x0x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x12x0x10
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x12x0x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x12x0x12
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x12x0x14
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x12x0x16
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x12x0x18
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x12x1 : check 28 19 255255 22626 6 173 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x12x3 : check 28 19 255255 49495 7 154 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x12x5 : check 28 19 255255 76364 8 135 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x12x7 : check 28 19 255255 103233 9 116 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x12x8 : check 28 19 255255 116667 0 287 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x12x9 : check 28 19 255255 130102 10 97 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x12x10 : check 28 19 255255 143536 1 268 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x12x11 : check 28 19 255255 156971 11 78 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x12x12 : check 28 19 255255 170405 2 249 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x12x13 : check 28 19 255255 183840 12 59 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x12x14 : check 28 19 255255 197274 3 230 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x12x15 : check 28 19 255255 210709 13 40 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x12x16 : check 28 19 255255 224143 4 211 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x12x17x0 : check 27 19 255255 12504 12 743 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x12x17x1 : check 27 19 255255 25938 3 3992 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x12x17x2 : check 27 19 255255 39373 13 382 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x12x17x3 : check 27 19 255255 52807 4 3631 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x12x17x4 : check 27 19 255255 66242 14 21 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x12x17x5 : check 27 19 255255 79676 5 3270 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x12x17x7 : check 27 19 255255 106545 6 2909 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x12x17x9 : check 27 19 255255 133414 7 2548 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x12x17x11 : check 27 19 255255 160283 8 2187 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x12x17x13 : check 27 19 255255 187152 9 1826 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x12x17x14 : check 27 19 255255 200586 0 5075 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x12x17x15 : check 27 19 255255 214021 10 1465 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x12x17x16 : check 27 19 255255 227455 1 4714 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x12x17x17 : check 27 19 255255 240890 11 1104 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x12x17x18 : check 27 19 255255 254324 2 4353 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x12x17 : check 28 19 255255 237578 14 21 361 2770083102 = true := by
  apply check_step 27 19 255255 237578 14 21 361 2770083102 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x12x17x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x12x17x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x12x17x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x12x17x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x12x17x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x12x17x5
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x12x17x7
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x12x17x9
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x12x17x11
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x12x17x13
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x12x17x14
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x12x17x15
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x12x17x16
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x12x17x17
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x12x17x18
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x12x18 : check 28 19 255255 251012 5 192 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x12 : check 29 19 255255 174648 15 2 19 52631578947 = true := by
  apply check_step 28 19 255255 174648 15 2 19 52631578947 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x12x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x12x1
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x12x3
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x12x5
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x12x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x12x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x12x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x12x10
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x12x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x12x12
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x12x13
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x12x14
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x12x15
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x12x16
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x12x17
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x12x18
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x13 : check 29 19 255255 188082 6 11 19 52631578947 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x0 : check 28 19 255255 10606 13 58 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x1 : check 28 19 255255 24040 4 229 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x2x0 : check 27 19 255255 1972 7 2566 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x2x2 : check 27 19 255255 28841 8 2205 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x2x4 : check 27 19 255255 55710 9 1844 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x2x5 : check 27 19 255255 69144 0 5093 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x2x6 : check 27 19 255255 82579 10 1483 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x2x7 : check 27 19 255255 96013 1 4732 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x2x8 : check 27 19 255255 109448 11 1122 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x2x9 : check 27 19 255255 122882 2 4371 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x2x10 : check 27 19 255255 136317 12 761 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x2x11 : check 27 19 255255 149751 3 4010 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x2x12 : check 27 19 255255 163186 13 400 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x2x13 : check 27 19 255255 176620 4 3649 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x2x14 : check 27 19 255255 190055 14 39 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x2x15 : check 27 19 255255 203489 5 3288 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x2x17 : check 27 19 255255 230358 6 2927 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x2 : check 28 19 255255 37475 14 39 361 2770083102 = true := by
  apply check_step 27 19 255255 37475 14 39 361 2770083102 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x2x0
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x2x2
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x2x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x2x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x2x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x2x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x2x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x2x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x2x10
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x2x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x2x12
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x2x13
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x2x14
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x2x15
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x2x17
  · norm_num at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x3 : check 28 19 255255 50909 5 210 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x4x0 : check 27 19 255255 3386 5 3630 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x4x1 : check 27 19 255255 16821 15 20 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x4x2 : check 27 19 255255 30255 6 3269 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x4x4 : check 27 19 255255 57124 7 2908 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x4x6 : check 27 19 255255 83993 8 2547 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x4x8 : check 27 19 255255 110862 9 2186 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x4x9 : check 27 19 255255 124296 0 5435 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x4x10 : check 27 19 255255 137731 10 1825 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x4x11 : check 27 19 255255 151165 1 5074 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x4x12 : check 27 19 255255 164600 11 1464 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x4x13 : check 27 19 255255 178034 2 4713 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x4x14 : check 27 19 255255 191469 12 1103 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x4x15 : check 27 19 255255 204903 3 4352 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x4x16 : check 27 19 255255 218338 13 742 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x4x17 : check 27 19 255255 231772 4 3991 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x4x18 : check 27 19 255255 245207 14 381 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x4 : check 28 19 255255 64344 15 20 361 2770083102 = true := by
  apply check_step 27 19 255255 64344 15 20 361 2770083102 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x4x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x4x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x4x2
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x4x4
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x4x6
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x4x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x4x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x4x10
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x4x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x4x12
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x4x13
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x4x14
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x4x15
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x4x16
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x4x17
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x4x18
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x5 : check 28 19 255255 77778 6 191 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x6x0 : check 27 19 255255 4800 3 4694 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x6x1 : check 27 19 255255 18235 13 1084 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x6x2 : check 27 19 255255 31669 4 4333 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x6x3 : check 27 19 255255 45104 14 723 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x6x4 : check 27 19 255255 58538 5 3972 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x6x5 : check 27 19 255255 71973 15 362 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x6x6 : check 27 19 255255 85407 6 3611 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x6x7 : check 27 19 255255 98842 16 1 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x6x8 : check 27 19 255255 112276 7 3250 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x6x10 : check 27 19 255255 139145 8 2889 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x6x12 : check 27 19 255255 166014 9 2528 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x6x13 : check 27 19 255255 179448 0 5777 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x6x14 : check 27 19 255255 192883 10 2167 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x6x15 : check 27 19 255255 206317 1 5416 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x6x16 : check 27 19 255255 219752 11 1806 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x6x17 : check 27 19 255255 233186 2 5055 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x6x18 : check 27 19 255255 246621 12 1445 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x6 : check 28 19 255255 91213 16 1 361 2770083102 = true := by
  apply check_step 27 19 255255 91213 16 1 361 2770083102 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x6x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x6x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x6x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x6x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x6x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x6x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x6x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x6x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x6x8
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x6x10
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x6x12
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x6x13
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x6x14
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x6x15
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x6x16
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x6x17
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x6x18
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x7 : check 28 19 255255 104647 7 172 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x9 : check 28 19 255255 131516 8 153 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x11 : check 28 19 255255 158385 9 134 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x12 : check 28 19 255255 171819 0 305 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x13 : check 28 19 255255 185254 10 115 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x14 : check 28 19 255255 198688 1 286 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x15 : check 28 19 255255 212123 11 96 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x16 : check 28 19 255255 225557 2 267 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x17 : check 28 19 255255 238992 12 77 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14x18 : check 28 19 255255 252426 3 248 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x14 : check 29 19 255255 201517 16 1 19 52631578947 = true := by
  apply check_step 28 19 255255 201517 16 1 19 52631578947 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x7
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x9
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x12
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x13
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x14
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x15
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x16
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x17
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x18
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x15 : check 29 19 255255 214951 7 10 19 52631578947 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x0 : check 28 19 255255 12020 11 114 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x1 : check 28 19 255255 25454 2 285 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x2 : check 28 19 255255 38889 12 95 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x3 : check 28 19 255255 52323 3 266 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x4 : check 28 19 255255 65758 13 76 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x5 : check 28 19 255255 79192 4 247 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x6x0 : check 27 19 255255 4875 12 779 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x6x1 : check 27 19 255255 18309 3 4028 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x6x2 : check 27 19 255255 31744 13 418 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x6x3 : check 27 19 255255 45178 4 3667 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x6x4 : check 27 19 255255 58613 14 57 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x6x5 : check 27 19 255255 72047 5 3306 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x6x7 : check 27 19 255255 98916 6 2945 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x6x9 : check 27 19 255255 125785 7 2584 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x6x11 : check 27 19 255255 152654 8 2223 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x6x13 : check 27 19 255255 179523 9 1862 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x6x14 : check 27 19 255255 192957 0 5111 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x6x15 : check 27 19 255255 206392 10 1501 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x6x16 : check 27 19 255255 219826 1 4750 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x6x17 : check 27 19 255255 233261 11 1140 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x6x18 : check 27 19 255255 246695 2 4389 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x6 : check 28 19 255255 92627 14 57 361 2770083102 = true := by
  apply check_step 27 19 255255 92627 14 57 361 2770083102 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x6x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x6x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x6x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x6x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x6x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x6x5
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x6x7
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x6x9
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x6x11
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x6x13
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x6x14
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x6x15
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x6x16
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x6x17
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x6x18
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x7 : check 28 19 255255 106061 5 228 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x8x0 : check 27 19 255255 6289 10 1843 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x8x1 : check 27 19 255255 19723 1 5092 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x8x2 : check 27 19 255255 33158 11 1482 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x8x3 : check 27 19 255255 46592 2 4731 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x8x4 : check 27 19 255255 60027 12 1121 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x8x5 : check 27 19 255255 73461 3 4370 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x8x6 : check 27 19 255255 86896 13 760 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x8x7 : check 27 19 255255 100330 4 4009 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x8x8 : check 27 19 255255 113765 14 399 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x8x9 : check 27 19 255255 127199 5 3648 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x8x10 : check 27 19 255255 140634 15 38 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x8x11 : check 27 19 255255 154068 6 3287 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x8x13 : check 27 19 255255 180937 7 2926 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x8x15 : check 27 19 255255 207806 8 2565 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x8x17 : check 27 19 255255 234675 9 2204 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x8x18 : check 27 19 255255 248109 0 5453 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x8 : check 28 19 255255 119496 15 38 361 2770083102 = true := by
  apply check_step 27 19 255255 119496 15 38 361 2770083102 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x8x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x8x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x8x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x8x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x8x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x8x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x8x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x8x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x8x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x8x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x8x10
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x8x11
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x8x13
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x8x15
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x8x17
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x8x18
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x9 : check 28 19 255255 132930 6 209 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x10x0 : check 27 19 255255 7703 8 2907 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x10x2 : check 27 19 255255 34572 9 2546 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x10x3 : check 27 19 255255 48006 0 5795 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x10x4 : check 27 19 255255 61441 10 2185 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x10x5 : check 27 19 255255 74875 1 5434 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x10x6 : check 27 19 255255 88310 11 1824 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x10x7 : check 27 19 255255 101744 2 5073 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x10x8 : check 27 19 255255 115179 12 1463 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x10x9 : check 27 19 255255 128613 3 4712 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x10x10 : check 27 19 255255 142048 13 1102 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x10x11 : check 27 19 255255 155482 4 4351 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x10x12 : check 27 19 255255 168917 14 741 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x10x13 : check 27 19 255255 182351 5 3990 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x10x14 : check 27 19 255255 195786 15 380 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x10x15 : check 27 19 255255 209220 6 3629 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x10x16 : check 27 19 255255 222655 16 19 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x10x17 : check 27 19 255255 236089 7 3268 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x10 : check 28 19 255255 146365 16 19 361 2770083102 = true := by
  apply check_step 27 19 255255 146365 16 19 361 2770083102 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x10x0
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x10x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x10x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x10x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x10x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x10x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x10x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x10x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x10x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x10x10
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x10x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x10x12
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x10x13
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x10x14
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x10x15
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x10x16
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x10x17
  · norm_num at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x11 : check 28 19 255255 159799 7 190 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x12x0 : check 27 19 255255 9117 6 3971 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x12x1 : check 27 19 255255 22552 16 361 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x12x2 : check 27 19 255255 35986 7 3610 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x12x3 : check 27 19 255255 49421 17 0 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x12x4 : check 27 19 255255 62855 8 3249 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x12x6 : check 27 19 255255 89724 9 2888 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x12x7 : check 27 19 255255 103158 0 6137 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x12x8 : check 27 19 255255 116593 10 2527 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x12x9 : check 27 19 255255 130027 1 5776 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x12x10 : check 27 19 255255 143462 11 2166 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x12x11 : check 27 19 255255 156896 2 5415 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x12x12 : check 27 19 255255 170331 12 1805 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x12x13 : check 27 19 255255 183765 3 5054 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x12x14 : check 27 19 255255 197200 13 1444 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x12x15 : check 27 19 255255 210634 4 4693 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x12x16 : check 27 19 255255 224069 14 1083 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x12x17 : check 27 19 255255 237503 5 4332 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x12x18 : check 27 19 255255 250938 15 722 6859 145793847 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x12 : check 28 19 255255 173234 17 0 361 2770083102 = true := by
  apply check_step 27 19 255255 173234 17 0 361 2770083102 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x12x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x12x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x12x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x12x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x12x4
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x12x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x12x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x12x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x12x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x12x10
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x12x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x12x12
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x12x13
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x12x14
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x12x15
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x12x16
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x12x17
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x12x18
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x13 : check 28 19 255255 186668 8 171 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x15 : check 28 19 255255 213537 9 152 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x16 : check 28 19 255255 226971 0 323 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x17 : check 28 19 255255 240406 10 133 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16x18 : check 28 19 255255 253840 1 304 361 2770083102 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x16 : check 29 19 255255 228386 17 0 19 52631578947 = true := by
  apply check_step 28 19 255255 228386 17 0 19 52631578947 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x10
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x12
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x13
  · norm_num at hb
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x15
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x16
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x17
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x18
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19_x17 : check 29 19 255255 241820 8 9 19 52631578947 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19 : check 30 19 255255 255254 17 0 1 999999999999 = true := by
  apply check_step 29 19 255255 255254 17 0 1 999999999999 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x10
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x12
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x13
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x15
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x17
  · norm_num at hb
end VestigeBernoulliDigit

namespace VestigeBernoulliDigit
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check23_x0 : check 29 23 4849845 210862 3 18 23 43478260869 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check23_x1 : check 29 23 4849845 421725 7 14 23 43478260869 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check23_x2 : check 29 23 4849845 632588 11 10 23 43478260869 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check23_x3 : check 29 23 4849845 843451 15 6 23 43478260869 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check23_x4 : check 29 23 4849845 1054314 19 2 23 43478260869 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check23_x5 : check 29 23 4849845 1265176 0 21 23 43478260869 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check23_x6 : check 29 23 4849845 1476039 4 17 23 43478260869 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check23_x7 : check 29 23 4849845 1686902 8 13 23 43478260869 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check23_x8 : check 29 23 4849845 1897765 12 9 23 43478260869 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check23_x9 : check 29 23 4849845 2108628 16 5 23 43478260869 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check23_x10 : check 29 23 4849845 2319491 20 1 23 43478260869 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check23_x11 : check 29 23 4849845 2530353 1 20 23 43478260869 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check23_x12 : check 29 23 4849845 2741216 5 16 23 43478260869 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check23_x13 : check 29 23 4849845 2952079 9 12 23 43478260869 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check23_x14 : check 29 23 4849845 3162942 13 8 23 43478260869 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check23_x15 : check 29 23 4849845 3373805 17 4 23 43478260869 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check23_x16 : check 29 23 4849845 3584668 21 0 23 43478260869 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check23_x17 : check 29 23 4849845 3795530 2 19 23 43478260869 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check23_x18 : check 29 23 4849845 4006393 6 15 23 43478260869 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check23_x19 : check 29 23 4849845 4217256 10 11 23 43478260869 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check23_x20 : check 29 23 4849845 4428119 14 7 23 43478260869 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check23_x21 : check 29 23 4849845 4638982 18 3 23 43478260869 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check23 : check 30 23 4849845 4849844 21 0 1 999999999999 = true := by
  apply check_step 29 23 4849845 4849844 21 0 1 999999999999 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check23_x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check23_x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check23_x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check23_x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check23_x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check23_x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check23_x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check23_x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check23_x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check23_x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check23_x10
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check23_x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check23_x12
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check23_x13
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check23_x14
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check23_x15
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check23_x16
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check23_x17
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check23_x18
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check23_x19
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check23_x20
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check23_x21
  · norm_num at hb
end VestigeBernoulliDigit

namespace VestigeBernoulliDigit
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check29_x0 : check 29 29 111546435 3846428 5 22 29 34482758620 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check29_x1 : check 29 29 111546435 7692857 11 16 29 34482758620 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check29_x2 : check 29 29 111546435 11539286 17 10 29 34482758620 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check29_x3 : check 29 29 111546435 15385715 23 4 29 34482758620 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check29_x4 : check 29 29 111546435 19232143 0 27 29 34482758620 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check29_x5 : check 29 29 111546435 23078572 6 21 29 34482758620 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check29_x6 : check 29 29 111546435 26925001 12 15 29 34482758620 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check29_x7 : check 29 29 111546435 30771430 18 9 29 34482758620 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check29_x8 : check 29 29 111546435 34617859 24 3 29 34482758620 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check29_x9 : check 29 29 111546435 38464287 1 26 29 34482758620 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check29_x10 : check 29 29 111546435 42310716 7 20 29 34482758620 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check29_x11 : check 29 29 111546435 46157145 13 14 29 34482758620 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check29_x12 : check 29 29 111546435 50003574 19 8 29 34482758620 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check29_x13 : check 29 29 111546435 53850003 25 2 29 34482758620 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check29_x14 : check 29 29 111546435 57696431 2 25 29 34482758620 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check29_x15 : check 29 29 111546435 61542860 8 19 29 34482758620 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check29_x16 : check 29 29 111546435 65389289 14 13 29 34482758620 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check29_x17 : check 29 29 111546435 69235718 20 7 29 34482758620 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check29_x18 : check 29 29 111546435 73082147 26 1 29 34482758620 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check29_x19 : check 29 29 111546435 76928575 3 24 29 34482758620 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check29_x20 : check 29 29 111546435 80775004 9 18 29 34482758620 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check29_x21 : check 29 29 111546435 84621433 15 12 29 34482758620 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check29_x22 : check 29 29 111546435 88467862 21 6 29 34482758620 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check29_x23 : check 29 29 111546435 92314291 27 0 29 34482758620 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check29_x24 : check 29 29 111546435 96160719 4 23 29 34482758620 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check29_x25 : check 29 29 111546435 100007148 10 17 29 34482758620 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check29_x26 : check 29 29 111546435 103853577 16 11 29 34482758620 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check29_x27 : check 29 29 111546435 107700006 22 5 29 34482758620 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check29 : check 30 29 111546435 111546434 27 0 1 999999999999 = true := by
  apply check_step 29 29 111546435 111546434 27 0 1 999999999999 (by norm_num)
  intro t ht hb
  interval_cases t
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check29_x0
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check29_x1
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check29_x2
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check29_x3
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check29_x4
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check29_x5
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check29_x6
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check29_x7
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check29_x8
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check29_x9
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check29_x10
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check29_x11
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check29_x12
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check29_x13
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check29_x14
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check29_x15
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check29_x16
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check29_x17
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check29_x18
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check29_x19
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check29_x20
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check29_x21
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check29_x22
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check29_x23
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check29_x24
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check29_x25
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check29_x26
  · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check29_x27
  · norm_num at hb
end VestigeBernoulliDigit

namespace VestigeBernoulliDigit
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check31 : check 30 31 3234846615 3234846614 29 0 1 999999999999 = true := by decide +kernel
end VestigeBernoulliDigit

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem OMA.solution : OMA.R_OeisA195441_conjecture_R2.H1 := by
  intro n hlo hhi hodd
  apply VestigeBernoulliDigit.all_cases VestigeBernoulliDigit.check3 VestigeBernoulliDigit.check5 VestigeBernoulliDigit.check7
    VestigeBernoulliDigit.check11 VestigeBernoulliDigit.check13 VestigeBernoulliDigit.check17 VestigeBernoulliDigit.check19
    VestigeBernoulliDigit.check23 VestigeBernoulliDigit.check29 VestigeBernoulliDigit.check31 n hlo _ hodd
  simpa only [show 10000^3 = 1000000000000 by norm_num] using hhi
