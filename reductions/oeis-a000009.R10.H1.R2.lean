import OMAReductions.R_oeis_a000009_R10

/-!
# A sparse pair criterion for the R10 representation step

Gordon and Ono's divisibility theorem (DOI 10.1023/A:1009711020492) implies
that indices with 2048 ∤ q(n) have density zero. Since q(45) = 2048, these
include all sufficiently large small-divisor sieve survivors. A fixed pair of
candidates per window is compatible with zero density in the index. Each
cofactor-exception pair is tested only at its first possible common window.
Both arithmetic hypotheses below remain open.
-/
namespace OMA.R_oeis_a000009_R10_H1_R2
open OMA.S_oeis_a000009 Finset

/-- Usable arrivals occur arbitrarily late. Immediately before each such arrival
above the starting endpoint, two previously arrived values still survive. -/
def H1 : Prop :=
  let Q := fun a : ℕ => ∃ m : ℕ, 0 < m ∧ a = strictPartitionCount m
  let start : ℕ := 30020900773769688559070113208459541809716021698140392739697
  let birth := fun a : ℕ => (2*a+2)/3
  let live := fun x a : ℕ => Q a ∧ x ≤ a ∧ 2*a ≤ 3*x ∧
    ∀ s, 1000 ≤ s → Q s → s*s ≤ x → ¬ s ∣ a
  (∀ x, start ≤ x → ∃ c, x < birth c ∧ live (birth c) c) ∧
    ∀ c, start < birth c → live (birth c) c →
      ∃ a b, live (birth c-1) a ∧ live (birth c-1) b ∧ a < b

/-- If two cofactor exceptions can occur together in a window, at least one
has a small divisor already at the earliest possible lower endpoint. -/
def H2 : Prop :=
  let Q := fun a : ℕ => ∃ m : ℕ, 0 < m ∧ a = strictPartitionCount m
  let exceptional := fun a : ℕ =>
    ∃ k : ℕ, 2 ≤ k ∧ 2*k*k < 3*a ∧ k ∣ a ∧ 1000 ≤ a/k ∧ Q (a/k)
  ∀ a b : ℕ, Q a → Q b → a < b → exceptional a → exceptional b →
    let e := max 30020900773769688559070113208459541809716021698140392739697 ((2*b+2)/3)
    e ≤ a → ∃ s, 1000 ≤ s ∧ Q s ∧ s*s ≤ e ∧ (s ∣ a ∨ s ∣ b)

/-- Every value lives on one interval of integer window endpoints. A number d
that divides a and is least among its eligible divisors causes the first
sieve loss at d². The geometric upper endpoint a can occur earlier. -/
theorem lifetime_of_least_divisor (Q : ℕ → Prop) {a d : ℕ}
    (big : 1000 ≤ d) (qd : Q d) (divides : d ∣ a)
    (least : ∀ s, 1000 ≤ s → Q s → s ∣ a → d ≤ s) (x : ℕ) :
    (x ≤ a ∧ 2*a ≤ 3*x ∧ ∀ s, 1000 ≤ s → Q s → s*s ≤ x → ¬ s ∣ a) ↔
    ((2*a+2)/3 ≤ x ∧ x ≤ a ∧ x < d*d) := by
  constructor
  · rintro ⟨lo,hi,clean⟩
    exact ⟨by omega,lo,lt_of_not_ge (fun sq => clean d big qd sq divides)⟩
  · rintro ⟨lo,hi,small⟩
    refine ⟨hi,by omega,?_⟩
    intro s hs qs sq dv
    have le := least s hs qs dv
    exact (Nat.not_le_of_lt small) ((Nat.mul_le_mul le le).trans sq)

/-- For a finite range of windows the final endpoint takes the place of a
future arrival. Tests just before usable arrivals include simultaneous arrivals
once and use the old witnesses before any new value can be used. -/
theorem pair_on_segment_iff (Q : ℕ → Prop) (start last : ℕ) (order : start ≤ last) :
    let birth := fun a : ℕ => (2*a+2)/3
    let live := fun x a : ℕ => Q a ∧ x ≤ a ∧ 2*a ≤ 3*x ∧
      ∀ s, 1000 ≤ s → Q s → s*s ≤ x → ¬ s ∣ a
    let pair := fun x : ℕ => ∃ a b, live x a ∧ live x b ∧ a < b
    (∀ x, start ≤ x → x ≤ last → pair x) ↔
      pair last ∧ (∀ c, start < birth c → birth c ≤ last → live (birth c) c → pair (birth c-1)) := by
  intro birth live pair
  constructor
  · intro cover
    exact ⟨cover last order le_rfl,fun c lo hi _ => cover _ (by omega) (by omega)⟩
  · rintro ⟨final,checks⟩ x lo hi
    classical
    have next : ∃ e : ℕ, x < e ∧
        (e = last+1 ∨ ∃ c, birth c = e ∧ live e c) :=
      ⟨last+1,by omega,Or.inl rfl⟩
    let e := Nat.find next
    obtain ⟨after,why⟩ := Nat.find_spec next
    change x < e at after
    have limit : e ≤ last+1 := Nat.find_min' next ⟨by omega,Or.inl rfl⟩
    have atEnd : pair (e-1) := by
      rcases why with h | ⟨c,h,hc⟩
      · change e = last+1 at h
        simpa [h] using final
      · change birth c = e at h
        by_cases eq : e = last+1
        · simpa [eq] using final
        · rw [← h]
          exact checks c (by omega) (by omega) (h.symm ▸ hc)
    obtain ⟨a,b,ha,hb,ab⟩ := atEnd
    have back (z : ℕ) (hz : live (e-1) z) : live x z := by
      obtain ⟨qz,left,right,clean⟩ := hz
      have br : birth z ≤ e-1 := by dsimp [birth]; omega
      have born : birth z ≤ x := by
        by_contra! late
        have usable : live (birth z) z :=
          ⟨qz,by omega,by dsimp [birth]; omega,fun s hs qs sq => clean s hs qs (sq.trans br)⟩
        have least := Nat.find_min' next (show x < birth z ∧
          (birth z = last+1 ∨ ∃ c, birth c = birth z ∧ live (birth z) c) from
          ⟨late,Or.inr ⟨z,rfl,usable⟩⟩)
        change e ≤ birth z at least
        omega
      exact ⟨qz,by omega,by dsimp [birth] at born; omega,
        fun s hs qs sq => clean s hs qs (by omega)⟩
    exact ⟨a,b,back a ha,back b hb,ab⟩

/-- It suffices to check pairs just before each usable arrival, provided such
arrivals are cofinal. The two pre-arrival witnesses survive throughout the gap. -/
theorem pair_supply_iff_arrivals (Q : ℕ → Prop) (start : ℕ) :
    let birth := fun a : ℕ => (2*a+2)/3
    let live := fun x a : ℕ => Q a ∧ x ≤ a ∧ 2*a ≤ 3*x ∧
      ∀ s, 1000 ≤ s → Q s → s*s ≤ x → ¬ s ∣ a
    let pair := fun x : ℕ => ∃ a b, live x a ∧ live x b ∧ a < b
    (∀ x, start ≤ x → pair x) ↔
      (∀ x, start ≤ x → ∃ c, x < birth c ∧ live (birth c) c) ∧
      (∀ c, start < birth c → live (birth c) c → pair (birth c-1)) := by
  intro birth live pair
  have retreat {x y a : ℕ} (h : live y a) (born : birth a ≤ x) (le : x ≤ y) : live x a := by
    obtain ⟨qa,lo,hi,clean⟩ := h
    dsimp [birth] at born
    exact ⟨qa,le.trans lo,by omega,fun s hs qs sq => clean s hs qs (sq.trans le)⟩
  have atBirth {x a : ℕ} (h : live x a) : live (birth a) a := by
    apply retreat h le_rfl
    have hi := h.2.2.1
    dsimp [birth]; omega
  constructor
  · intro supply
    constructor
    · intro x hx
      obtain ⟨a,_,ha,_,_⟩ := supply (3*(x+1)) (by omega)
      have lo := ha.2.1
      exact ⟨a,by dsimp [birth]; omega,atBirth ha⟩
    · intro c bound _
      exact supply _ (by omega)
  · rintro ⟨cofinal,checks⟩ x hx
    obtain ⟨c,after,usable⟩ := cofinal x hx
    have last := checks c (by omega) usable
    exact (pair_on_segment_iff Q start (birth c-1) (by omega)).mpr
      ⟨last,fun z lower _ hz => checks z lower hz⟩ x hx (by omega)

/-- For a strictly increasing enumeration whose first value reaches start,
two values lie in every window exactly when the initial pair fits and the
value two positions ahead fits the first window after the old value leaves. -/
theorem two_values_iff_spacing (v : ℕ → ℕ) (inc : StrictMono v) (start : ℕ)
    (first : start ≤ v 0) :
    (∀ x, start ≤ x → ∃ i j : ℕ, i < j ∧ x ≤ v i ∧ 2*v j ≤ 3*x) ↔
    (2*v 1 ≤ 3*start ∧ ∀ i, 2*v (i+2) ≤ 3*(v i+1)) := by
  constructor
  · intro cover
    constructor
    · obtain ⟨i,j,ij,_,hi⟩ := cover start le_rfl
      have := inc.monotone (show 1 ≤ j by omega)
      omega
    · intro i
      have h := inc.monotone (Nat.zero_le i)
      obtain ⟨j,k,jk,lo,hi⟩ := cover (v i+1) (by omega)
      have ij : i < j := by
        by_contra! inv
        have := inc.monotone inv
        omega
      have := inc.monotone (show i+2 ≤ k by omega)
      omega
  · rintro ⟨initial,spacing⟩ x hx
    have reaches : ∃ i, x ≤ v i := ⟨x,inc.id_le x⟩
    let j := Nat.find reaches
    have lo : x ≤ v j := Nat.find_spec reaches
    refine ⟨j,j+1,by omega,lo,?_⟩
    cases eq : j with
    | zero => simpa using initial.trans (Nat.mul_le_mul_left 3 hx)
    | succ i =>
      have early : i < Nat.find reaches := by change i < j; omega
      have prev := Nat.find_min reaches early
      have := spacing i
      change 2*v (i+2) ≤ 3*x
      omega

/-- The arrival formulation recovers exactly the original sparse-pair supply. -/
theorem H1_iff_pair_supply : H1 ↔
  let Q := fun a : ℕ => ∃ m : ℕ, 0 < m ∧ a = strictPartitionCount m
  ∀ x : ℕ, 30020900773769688559070113208459541809716021698140392739697 ≤ x →
    ∃ a b : ℕ, Q a ∧ Q b ∧ x ≤ a ∧ a < b ∧ 2*b ≤ 3*x ∧
      ∀ s, 1000 ≤ s → Q s → s*s ≤ x → ¬ s ∣ a ∧ ¬ s ∣ b := by
  let Q := fun a : ℕ => ∃ m : ℕ, 0 < m ∧ a = strictPartitionCount m
  have windows := pair_supply_iff_arrivals Q 30020900773769688559070113208459541809716021698140392739697
  constructor
  · intro h q x hx
    obtain ⟨a,b,ha,hb,ab⟩ := windows.mpr h x hx
    exact ⟨a,b,ha.1,hb.1,ha.2.1,ab,hb.2.2.1,
      fun s hs qs sq => ⟨ha.2.2.2 s hs qs sq,hb.2.2.2 s hs qs sq⟩⟩
  · intro h
    apply windows.mp
    intro x hx
    obtain ⟨a,b,qa,qb,lo,ab,hi,clean⟩ := h x hx
    exact ⟨a,b,⟨qa,lo,by omega,fun s hs qs sq => (clean s hs qs sq).1⟩,
      ⟨qb,by omega,hi,fun s hs qs sq => (clean s hs qs sq).2⟩,ab⟩

/-- For values that pass the sieve until they leave the window, estimating the
spacing of every second value suffices; intermediate integer windows need no tests. -/
theorem H1_of_clean_spacing (v : ℕ → ℕ) (inc : StrictMono v)
    (first : 30020900773769688559070113208459541809716021698140392739697 ≤ v 0) (initial : 2*v 1 ≤ 3*30020900773769688559070113208459541809716021698140392739697)
    (spacing : ∀ i, 2*v (i+2) ≤ 3*(v i+1))
    (terms : ∀ i, (∃ m : ℕ, 0 < m ∧ v i = strictPartitionCount m) ∧
      ∀ s, 1000 ≤ s → (∃ m : ℕ, 0 < m ∧ s = strictPartitionCount m) →
        s*s ≤ v i → ¬ s ∣ v i) : H1 := by
  apply H1_iff_pair_supply.mpr
  intro q x hx
  obtain ⟨i,j,ij,lo,hi⟩ := (two_values_iff_spacing v inc _ first).mpr ⟨initial,spacing⟩ x hx
  have lt := inc ij
  exact ⟨v i,v j,(terms i).1,(terms j).1,lo,lt,hi,
    fun s hs qs sq => ⟨(terms i).2 s hs qs (sq.trans lo),
      (terms j).2 s hs qs (sq.trans (lo.trans lt.le))⟩⟩

/-- Every subset of {1,...,k} extends to a distinct partition of n by adding
a unique part greater than k. -/
theorem pow_le_strictCount (k n : ℕ) (hn : k*(k+1)/2 + k < n) :
    2^k ≤ strictPartitionCount n := by
  let base := Icc 1 k
  have hc : base.card = k := by simp [base, Nat.card_Icc]
  have weight {s : Finset ℕ} (h : s ∈ base.powerset) : ∑ i ∈ s, i ≤ k*(k+1)/2 := by
    calc ∑ i ∈ s, i ≤ ∑ i ∈ base, i :=
           sum_le_sum_of_subset_of_nonneg (mem_powerset.mp h) (by intros; omega)
         _ = k*(k+1)/2 := by
           have eq : insert 0 base = range (k+1) := by ext i; simp [base]; omega
           have total := Finset.sum_range_id (k+1)
           rw [← eq,sum_insert (by simp [base])] at total
           simpa [Nat.mul_comm] using total
  let pad (s : Finset ℕ) := n - ∑ i ∈ s, i
  have large {s : Finset ℕ} (h : s ∈ base.powerset) : k < pad s := by
    have := weight h
    dsimp [pad]
    omega
  rw [OMA.R_oeis_a000009_R10.strictPartitionCount_eq_subsetCount, ← hc, ← card_powerset]
  apply card_le_card_of_injOn (fun s => insert (pad s) s)
  · intro s hs
    have hl := large hs
    have hf : pad s ∉ s := fun h => (Nat.not_lt_of_ge (mem_Icc.mp (mem_powerset.mp hs h)).2) hl
    refine mem_filter.mpr ⟨mem_powerset.mpr ?_, ?_⟩
    · intro i hi
      rcases mem_insert.mp hi with rfl | h
      · exact mem_Icc.mpr ⟨by omega, Nat.sub_le ..⟩
      · have := mem_Icc.mp (mem_powerset.mp hs h)
        exact mem_Icc.mpr ⟨this.1, by omega⟩
    · rw [sum_insert hf]
      have := weight hs
      dsimp [pad]
      omega
  · intro s hs t ht he
    have recover {u : Finset ℕ} (hu : u ∈ base.powerset) :
        (insert (pad u) u).filter (· ≤ k) = u := by
      ext i
      have := large hu
      simp only [mem_filter, mem_insert]
      exact ⟨fun ⟨h, hk⟩ => h.resolve_left (by omega),
        fun h => ⟨Or.inr h, (mem_Icc.mp (mem_powerset.mp hu h)).2⟩⟩
    exact (recover hs).symm.trans ((congrArg (fun u : Finset ℕ => u.filter (· ≤ k)) he).trans (recover ht))

/-- All strict partition values below 2^k occur among these first indices. -/
theorem index_bound {n k : ℕ} (h : strictPartitionCount n < 2^k) : n ≤ k*(k+1)/2+k := by
  by_contra hn
  exact (Nat.not_lt_of_ge (pow_le_strictCount k n (by omega))) h

theorem disjoint_band_count (q : ℕ → ℕ) (K r : ℕ) (pool : Finset ℕ)
    (A : ℕ → Finset ℕ)
    (size : ∀ j ∈ Ico K (2*K), r ≤ (A j).card)
    (band : ∀ j ∈ Ico K (2*K), ∀ a ∈ A j, 2^j ≤ a ∧ a < 2^(j+1) ∧ a ∈ pool.image q) :
    K*r ≤ pool.card := by
  let J := Ico K (2*K)
  have dis : (J : Set ℕ).PairwiseDisjoint A := by
    intro i hi j hj ne
    apply Finset.disjoint_left.mpr
    intro a hai haj
    obtain ⟨li,ui,_⟩ := band i hi a hai
    obtain ⟨lj,uj,_⟩ := band j hj a haj
    rcases lt_or_gt_of_ne ne with lt | gt
    · have e := Nat.pow_le_pow_right (by decide : 0 < 2) (show i+1 ≤ j by omega)
      omega
    · have e := Nat.pow_le_pow_right (by decide : 0 < 2) (show j+1 ≤ i by omega)
      omega
  have sub : J.biUnion A ⊆ pool.image q := by
    intro a ha
    obtain ⟨j,hj,h⟩ := mem_biUnion.mp ha
    exact (band j hj a h).2.2
  calc
    K*r = ∑ _j ∈ J, r := by simp [J,Nat.card_Ico]; omega
    _ ≤ ∑ j ∈ J, (A j).card := sum_le_sum size
    _ = (J.biUnion A).card := (card_biUnion dis).symm
    _ ≤ (pool.image q).card := card_le_card sub
    _ ≤ _ := card_image_le

/-- The logarithmic survivor quota forces quadratically many indices missing
the fixed divisor q(45). Gordon--Ono's density-one theorem contradicts this
bound as K tends to infinity. The density theorem itself is external. -/
theorem logarithmic_quota_obstruction (K : ℕ)
    (start : 30020900773769688559070113208459541809716021698140392739697 ≤ 2^K)
    (supply : ∀ x : ℕ, 2^K ≤ x → ∃ A : Finset ℕ, x.log2/32 < A.card ∧
      ∀ a ∈ A, (∃ m : ℕ, 0 < m ∧ a = strictPartitionCount m) ∧ x ≤ a ∧ 2*a ≤ 3*x ∧
        ∀ s, 1000 ≤ s → (∃ m : ℕ, 0 < m ∧ s = strictPartitionCount m) → s*s ≤ x → ¬ s ∣ a) :
    let k := 2*K
    K*(K/32+1) ≤ ((range (k*(k+1)/2+k+1)).filter
      (fun m => strictPartitionCount m % 2048 ≠ 0)).card := by
  classical
  let J := Ico K (2*K)
  have witness (j : ℕ) (hj : j ∈ J) := supply (2^j)
    (Nat.pow_le_pow_right (by decide) (mem_Ico.mp hj).1)
  let A (j : ℕ) : Finset ℕ := if h : j ∈ J then (witness j h).choose else ∅
  have spec (j : ℕ) (hj : j ∈ J) := (witness j hj).choose_spec
  apply disjoint_band_count strictPartitionCount K (K/32+1) _ A
  · intro j hj
    have count := (spec j hj).1
    have logeq : (2^j).log2 = j := Nat.log2_two_pow
    have le := (mem_Ico.mp hj).1
    change j ∈ J at hj
    simp only [A,dif_pos hj]
    omega
  · intro j hj a ha
    change j ∈ J at hj
    simp only [A,dif_pos hj] at ha
    obtain ⟨⟨m,_,rfl⟩,lo,hi,clean⟩ := (spec j hj).2 a ha
    have powPos : 0 < 2^j := by positivity
    have upper : strictPartitionCount m < 2^(j+1) := by rw [pow_succ]; omega
    have q45 : strictPartitionCount 45 = 2048 := by
      rw [OMA.R_oeis_a000009_R10.strictPartitionCount_eq_rec 45 45 le_rfl]; decide +kernel
    have lowPow := Nat.pow_le_pow_right (by decide : 0 < 2) (mem_Ico.mp hj).1
    have avoid := clean 2048 (by decide) ⟨45,by decide,q45.symm⟩ (by omega)
    have index := index_bound (upper.trans_le (Nat.pow_le_pow_right (by decide)
      (show j+1 ≤ 2*K from (mem_Ico.mp hj).2)))
    exact ⟨lo,upper,mem_image.mpr ⟨m,mem_filter.mpr ⟨mem_range.mpr (by omega),
      fun eq => avoid (Nat.dvd_of_mod_eq_zero eq)⟩,rfl⟩⟩

/-- The density-zero consequence needed from Gordon--Ono is a single eventual
bound of one index in 128. Under it, the logarithmic quota is impossible. -/
theorem not_logarithmic_quota
    (sparse : ∃ M : ℕ, ∀ N : ℕ, M ≤ N →
      128*((range N).filter (fun m => strictPartitionCount m % 2048 ≠ 0)).card < N) :
    ¬ (∀ x : ℕ, 30020900773769688559070113208459541809716021698140392739697 ≤ x →
      ∃ A : Finset ℕ, x.log2/32 < A.card ∧ ∀ a ∈ A,
        (∃ m : ℕ, 0 < m ∧ a = strictPartitionCount m) ∧ x ≤ a ∧ 2*a ≤ 3*x ∧
        ∀ s, 1000 ≤ s → (∃ m : ℕ, 0 < m ∧ s = strictPartitionCount m) → s*s ≤ x → ¬ s ∣ a) := by
  rintro allWindows
  obtain ⟨M,upper⟩ := sparse
  let h := M+200
  let K := 32*h
  have Kbig : 200 ≤ K := by dsimp [K,h]; omega
  have base : 30020900773769688559070113208459541809716021698140392739697 ≤ 2^K :=
    (by decide : 30020900773769688559070113208459541809716021698140392739697 ≤ 2^200).trans
      (Nat.pow_le_pow_right (by decide) Kbig)
  have lower := logarithmic_quota_obstruction K base (fun x hx => allWindows x (base.trans hx))
  let N := 2*K*(2*K+1)/2 + 2*K + 1
  have reach : M ≤ N := by dsimp [N,K,h]; omega
  have ub := upper N reach
  change K*(K/32+1) ≤ ((range N).filter _).card at lower
  have bound : N ≤ 128*(K*(K/32+1)) := by
    dsimp only [N,K]
    rw [Nat.mul_div_cancel_left _ (by decide : 0 < 32)]
    have hh : 1 ≤ h := by dsimp [h]; omega
    have frac := Nat.div_mul_le_self (2*(32*h)*(2*(32*h)+1)) 2
    nlinarith [Nat.mul_le_mul_right h hh]
  omega

/-- Earliest common window equals max(start, ceil(2*b/3)). Testing the
small divisors there is equivalent to excluding the pair at every common window. -/
theorem first_common_window_iff (Q : ℕ → Prop) (start a b : ℕ) :
    (∀ x, start ≤ x → x ≤ a → 2*b ≤ 3*x →
      ∃ s, 1000 ≤ s ∧ Q s ∧ s*s ≤ x ∧ (s ∣ a ∨ s ∣ b)) ↔
    (let e := max start ((2*b+2)/3)
     e ≤ a → ∃ s, 1000 ≤ s ∧ Q s ∧ s*s ≤ e ∧ (s ∣ a ∨ s ∣ b)) := by
  constructor
  · intro h e he
    exact h e (le_max_left ..) he (by dsimp [e]; have := le_max_right start ((2*b+2)/3); omega)
  · intro h x hx ha hb
    have le : max start ((2*b+2)/3) ≤ x := max_le hx (by omega)
    obtain ⟨s,hs,qs,sq,div⟩ := h (le.trans ha)
    exact ⟨s,hs,qs,sq.trans le,div⟩

/-- An actual pair of exceptions shares an early window. The geometric and
small-divisor tests by themselves cannot exclude all pairs down to x = 1. -/
theorem early_exception_pair :
    let Q := fun a : ℕ => ∃ m : ℕ, 0 < m ∧ a = strictPartitionCount m
    let exc := fun a : ℕ => ∃ k : ℕ, 2 ≤ k ∧ 2*k*k < 3*a ∧ k ∣ a ∧ 1000 ≤ a/k ∧ Q (a/k)
    let a := strictPartitionCount 110
    let b := strictPartitionCount 114
    let e := (2*b+2)/3
    a < b ∧ e = 918870 ∧ e ≤ a ∧ exc a ∧ exc b ∧
      ∀ s : ℕ, 1000 ≤ s → e < s*s := by
  intro Q exc a b e
  have q45 : strictPartitionCount 45 = 2048 := by
    rw [OMA.R_oeis_a000009_R10.strictPartitionCount_eq_rec 45 45 le_rfl]; decide +kernel
  have q46 : strictPartitionCount 46 = 2304 := by
    rw [OMA.R_oeis_a000009_R10.strictPartitionCount_eq_rec 46 46 le_rfl]; decide +kernel
  have va : a = 1004544 := by
    dsimp only [a]; rw [OMA.R_oeis_a000009_R10.strictPartitionCount_eq_rec 110 110 le_rfl]; decide +kernel
  have vb : b = 1378304 := by
    dsimp only [b]; rw [OMA.R_oeis_a000009_R10.strictPartitionCount_eq_rec 114 114 le_rfl]; decide +kernel
  have endpoint : e = 918870 := by dsimp only [e]; omega
  refine ⟨by omega,endpoint,by omega,?_,?_,?_⟩
  · rw [va]; exact ⟨436,by decide,by decide,by decide,by decide,46,by decide,q46.symm⟩
  · rw [vb]; exact ⟨673,by decide,by decide,by decide,by decide,45,by decide,q45.symm⟩
  · intro s hs
    have lower := Nat.mul_le_mul hs hs
    omega

/-- After sieving, a proper partition divisor exists exactly when a short
cofactor gives one. Multiple factorizations of the same value cost one exception. -/
theorem short_cofactor_iff (Q : ℕ → Prop) (x a : ℕ) (hi : 2*a ≤ 3*x)
    (clean : ∀ s, 1000 ≤ s → Q s → s*s ≤ x → ¬ s ∣ a) :
    (∃ s, 1000 ≤ s ∧ Q s ∧ 2*s ≤ a ∧ s ∣ a) ↔
      ∃ k : ℕ, 2 ≤ k ∧ 2*k*k < 3*a ∧ k ∣ a ∧ 1000 ≤ a/k ∧ Q (a/k) := by
  constructor
  · rintro ⟨s,hs,qs,low,d⟩
    have large : x < s*s := by
      by_contra! small
      exact clean s hs qs small d
    obtain ⟨k,rfl⟩ := d
    have hk : 2 ≤ k := by
      by_contra! h
      have h' : k = 0 ∨ k = 1 := by omega
      rcases h' with rfl | rfl <;> simp at low <;> omega
    have prod : s*(2*k) < s*(3*s) := by nlinarith
    have short := Nat.lt_of_mul_lt_mul_left prod
    have sq := Nat.mul_lt_mul_of_pos_right short (by omega : 0 < k)
    have div : s*k/k = s := Nat.mul_div_cancel _ (by omega)
    exact ⟨k,hk,by nlinarith only [sq],dvd_mul_left _ _,by rwa [div],by rwa [div]⟩
  · rintro ⟨k,hk,_,dvd,big,qs⟩
    have h := Nat.div_mul_cancel dvd
    exact ⟨a/k,big,qs,by nlinarith [Nat.mul_le_mul_left (a/k) hk],⟨k,h.symm⟩⟩

theorem main : H1 → H2 → OMA.R_oeis_a000009_R10.H1 := by
  intro supply pairs
  apply OMA.R_oeis_a000009_R10.H1_of_intervals
  intro n hn
  let x := n/2+1
  let start := 30020900773769688559070113208459541809716021698140392739697
  have hx : start ≤ x := by dsimp [x,start]; omega
  obtain ⟨a,b,qa,qb,lo,ab,hi,clean⟩ := H1_iff_pair_supply.mp supply x hx
  by_contra! missing
  have fail (c : ℕ) (qc : ∃ m : ℕ, 0 < m ∧ c = strictPartitionCount m)
      (lc : x ≤ c) (hc : 2*c ≤ 3*x)
      (safe : ∀ s, 1000 ≤ s → (∃ m : ℕ, 0 < m ∧ s = strictPartitionCount m) →
        s*s ≤ x → ¬ s ∣ c) :=
    (short_cofactor_iff _ x c hc safe).mp (missing c qc
      (by dsimp [start] at hx; omega) (by dsimp [x] at hc; omega)
      (by dsimp [x] at lc; omega) (by dsimp [x] at lc; omega))
  have ea := fail a qa lo (by omega) (fun s hs qs sq => (clean s hs qs sq).1)
  have eb := fail b qb (by omega) hi (fun s hs qs sq => (clean s hs qs sq).2)
  obtain ⟨s,hs,qs,sq,div⟩ := (first_common_window_iff _ start a b).mpr
    (pairs a b qa qb ab ea eb) x hx lo hi
  exact div.elim (clean s hs qs sq).1 (clean s hs qs sq).2

end OMA.R_oeis_a000009_R10_H1_R2
