import OMAReductions.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1_H2_R1_H3_R2
import Mathlib.GroupTheory.Rank
import Mathlib.GroupTheory.SpecificGroups.ZGroup
import Mathlib.CategoryTheory.IsomorphismClasses
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

/- Credit: @wispiANt. Count the groups with cyclic Sylow subgroups explicitly.
The Z-group approach was suggested by @hiattco in desk note 69164.
The cyclic-complement bound combines the nilpotent count of @gertjanvdgoot
(PR #7292) with the cyclic-action method discussed by @hiattco (desk note 69414).
The remaining estimates concern nonnilpotent soluble groups of mixed order,
separating abelian from nonabelian Sylow subgroups. -/

open CategoryTheory Erdos1160

namespace OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1_H2_R1_H3_R2_H2_R1

def H1 : Prop :=
  ∃ E : ℕ, ∀ q r : ℕ, Odd q → q < 2^r → ¬ IsPrimePow q →
    ¬ (∃ p l a : ℕ, p.Prime ∧ l.Prime ∧ p ≠ l ∧ 0 < a ∧ q = p^a*l) →
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = q ∧ Group.IsSolvable G ∧ ¬ (((∃ N P : Subgroup G, (N.Normal ∨ P.Normal) ∧ N.IsComplement' P ∧ IsCyclic P ∧ Group.IsNilpotent N ∧ (Nat.card N).Coprime (Nat.card P)) ∨ (∃ c t : ℕ, 0 < t ∧ ∃ H : FiniteGrp.{0}, Group.IsSolvable H ∧ Group.IsNilpotent H ∧
        (Nat.card H).Coprime ((c+2)^t) ∧
        ∃ (χ : Fin t → H →* MulAut (Multiplicative (ZMod (c+2))))
          (a : H →* MulAut (Fin t → Multiplicative (ZMod (c+2)))),
          (∀ h v i, a h v i = χ i h (v i)) ∧ Nonempty (G ≃* SemidirectProduct _ H a))) ∨
        (∃ N P : Subgroup G, N.Normal ∧ N.IsComplement' P ∧ Group.IsNilpotent N ∧ Group.IsNilpotent P ∧ Nat.card N ^ (Group.rank N * Group.rank P) ≤ 2^(r*r*2) ∧ (Nat.card N).Coprime (Nat.card P))) ∧ ¬ IsZGroup G ∧
        (∀ p : ℕ, p.Prime → ∀ P : Sylow p G, IsMulCommutative P)}).ncard ≤
      2^(E*(r+1)^2) * ∏ p ∈ q.primeFactors, g (p^q.factorization p)

def H2 : Prop :=
  ∃ E : ℕ, ∀ q r : ℕ, Odd q → q < 2^r → ¬ IsPrimePow q →
    ¬ (∃ p l a : ℕ, p.Prime ∧ l.Prime ∧ p ≠ l ∧ (¬ p ∣ l-1 ∨ ∀ i, 0 < i → i < a → ¬ Nat.ModEq l (p^i) 1) ∧ 0 < a ∧ q = p^a*l) →
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = q ∧ Group.IsSolvable G ∧ ¬ ((∃ p l a : ℕ, p.Prime ∧ l.Prime ∧ p ≠ l ∧ 0 < a ∧ q = p^a*l) ∧
        ∀ p l a : ℕ, (p.Prime ∧ l.Prime ∧ p ≠ l ∧ 0 < a ∧ q = p^a*l) →
          ((∃ N : Subgroup G, N.Normal ∧ Nat.card N = p^a) ∨ Nat.card (Sylow l G) = 1)) ∧ ¬ (((∃ N P : Subgroup G, (N.Normal ∨ P.Normal) ∧ N.IsComplement' P ∧ IsCyclic P ∧ Group.IsNilpotent N ∧ (Nat.card N).Coprime (Nat.card P)) ∨ (∃ c t : ℕ, 0 < t ∧ ∃ H : FiniteGrp.{0}, Group.IsSolvable H ∧ Group.IsNilpotent H ∧
        (Nat.card H).Coprime ((c+2)^t) ∧
        ∃ (χ : Fin t → H →* MulAut (Multiplicative (ZMod (c+2))))
          (a : H →* MulAut (Fin t → Multiplicative (ZMod (c+2)))),
          (∀ h v i, a h v i = χ i h (v i)) ∧ Nonempty (G ≃* SemidirectProduct _ H a))) ∨
        (∃ N P : Subgroup G, N.Normal ∧ N.IsComplement' P ∧ Group.IsNilpotent N ∧ Group.IsNilpotent P ∧ Nat.card N ^ (Group.rank N * Group.rank P) ≤ 2^(r*r*2) ∧ (Nat.card N).Coprime (Nat.card P))) ∧ (∃ p : ℕ, p.Prime ∧ ∃ P : Sylow p G, ¬ IsMulCommutative P)}).ncard ≤
      2^(E*(r+1)^2) * ∏ p ∈ q.primeFactors, g (p^q.factorization p)

/-- Label each group by a multiplication table on Fin n. -/
lemma finite_classes (n : ℕ) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = n}).Finite := by
  classical
  let T := {m : Fin n → Fin n → Fin n // ∃ s : Group (Fin n), s.mul = m}
  let _ : Finite T := inferInstanceAs (Finite (Subtype _))
  let model (t : T) := @FiniteGrp.of (Fin n) t.property.choose inferInstance
  let c (t : T) := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (model t)
  have cover : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = n} ⊆ Set.range c := by
    rintro _ ⟨G, hG, rfl⟩
    let e : Fin n ≃ G := ((Nat.equivFinOfCardPos (α := G) Nat.card_pos.ne').trans
      (finCongr hG)).symm
    let law : Group (Fin n) := e.group
    let t : T := ⟨law.mul, law, rfl⟩
    refine ⟨t, Quotient.sound ?_⟩
    let f : model t ≃* G := { e with
      map_mul' := fun a b =>
        (congrArg e (congrFun (congrFun t.property.choose_spec a) b)).trans
          (e.apply_symm_apply (e a * e b)) }
    exact ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp) f.toGrpIso⟩
  exact (Set.finite_range c).subset cover

lemma positive_count {n : ℕ} (hn : 0 < n) : 0 < g n := by
  apply (Set.ncard_pos (finite_classes n)).mpr
  let _ : NeZero n := ⟨hn.ne'⟩
  exact ⟨_, FiniteGrp.of (Multiplicative (ZMod n)), Nat.card_zmod _, rfl⟩

lemma cyclic_actions (H K : Type*) [Group H] [Group K] [Finite K]
    [IsCyclic H] [IsCyclic K] : Nat.card (H →* MulAut K) ≤ (Nat.card K).totient := by
  let _ : Finite (MulAut K) := Finite.of_injective (fun a : MulAut K => (a : K → K))
    (fun _ _ h => DFunLike.ext' h)
  obtain ⟨x, hx⟩ := IsCyclic.exists_generator (α := H)
  have inj : Function.Injective (fun f : H →* MulAut K => f x) := by
    intro f g h
    apply MonoidHom.ext
    intro y
    obtain ⟨z, rfl⟩ := hx y
    simpa only [map_zpow] using congrArg (fun a : MulAut K => a ^ z) h
  exact (Nat.card_le_card_of_injective _ inj).trans
    (IsCyclic.card_mulAut K).le

lemma cyclic_sylows_bound (q : ℕ) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = q ∧ Group.IsSolvable G ∧ IsZGroup G}).ncard ≤ q := by
  classical
  let C (i : ℕ) := Multiplicative (ZMod (i+1))
  let A (i : q.divisors) := C (q / (i : ℕ) - 1) →* MulAut (C ((i : ℕ)-1))
  have ccard (i : ℕ) : Nat.card (C i) = i+1 := Nat.card_zmod _
  let (i : q.divisors) : Finite (A i) := by
    let _ : Finite (MulAut (C ((i : ℕ)-1))) := Finite.of_injective
      (fun a : MulAut (C ((i : ℕ)-1)) => (a : C ((i : ℕ)-1) → C ((i : ℕ)-1))) (fun _ _ h => DFunLike.ext' h)
    exact Finite.of_injective (fun a : A i => (a : C _ → MulAut (C ((i : ℕ)-1))))
      (fun _ _ h => DFunLike.ext' h)
  let decode (x : (i : q.divisors) × A i) : Quotient (isIsomorphicSetoid FiniteGrp.{0}) := by
    let K := C ((x.1 : ℕ)-1)
    let H := C (q / (x.1 : ℕ) - 1)
    letI : Finite (SemidirectProduct K H x.2) :=
      Finite.of_equiv (K × H) SemidirectProduct.equivProd.symm
    exact Quotient.mk _ (FiniteGrp.of (SemidirectProduct K H x.2))
  have cover : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = q ∧ Group.IsSolvable G ∧ IsZGroup G} ⊆
      Set.range decode := by
    rintro _ ⟨G, ⟨hG, _, hz⟩, rfl⟩
    obtain ⟨N, H, a, e, hH, hN, _⟩ := isZGroup_iff_exists_mulEquiv.mp hz
    have hp : 0 < Nat.card N := Nat.card_pos
    have hh : 0 < Nat.card H := Nat.card_pos
    let i : q.divisors := ⟨Nat.card N, Nat.mem_divisors.mpr
      ⟨hG ▸ N.card_subgroup_dvd_card, hG ▸ Nat.card_pos.ne'⟩⟩
    have hi : (i : ℕ) = Nat.card N := rfl
    have size := Nat.card_congr e.toEquiv
    rw [SemidirectProduct.card, hG] at size
    have hj : q / (i : ℕ) = Nat.card H := by rw [hi, size, Nat.mul_div_cancel_left _ hp]
    let fn : N ≃* C ((i : ℕ)-1) := mulEquivOfCyclicCardEq (by rw [ccard, hi]; omega)
    let fh : H ≃* C (q / (i : ℕ) - 1) :=
      mulEquivOfCyclicCardEq (by rw [ccard, hj]; omega)
    let f := e.trans (SemidirectProduct.congr' (φ₁ := a) fn fh)
    refine ⟨⟨i, MonoidHom.comp (MulAut.congr fn) (a.comp fh.symm)⟩, Quotient.sound ?_⟩
    exact ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp) f.symm.toGrpIso⟩
  calc
    _ ≤ (Set.range decode).ncard := Set.ncard_le_ncard cover (Set.finite_range _)
    _ ≤ Nat.card ((i : q.divisors) × A i) :=
      Nat.card_le_card_of_surjective _ (Set.rangeFactorization_surjective (f := decode))
    _ = ∑ i : q.divisors, Nat.card (A i) := Nat.card_sigma
    _ ≤ ∑ i : q.divisors, (i : ℕ).totient := by
      apply Finset.sum_le_sum
      intro i _
      have hi := Nat.pos_of_mem_divisors i.property
      have hn : (i : ℕ)-1+1 = (i : ℕ) := by omega
      simpa only [ccard, hn] using
        cyclic_actions (C (q / (i : ℕ) - 1)) (C ((i : ℕ)-1))
    _ = q := (Finset.sum_finset_coe Nat.totient q.divisors).trans (Nat.sum_totient q)

/-- In particular all groups of squarefree order are included in the explicit bound. -/
lemma squarefree_count {q : ℕ} (hs : Squarefree q) : g q ≤ q := by
  have eq : {G : FiniteGrp.{0} | Nat.card G = q} =
      {G : FiniteGrp.{0} | Nat.card G = q ∧ Group.IsSolvable G ∧ IsZGroup G} := by
    ext G
    constructor
    · intro hG
      let _ : IsZGroup G := IsZGroup.of_squarefree (hG.symm ▸ hs)
      exact ⟨hG, inferInstance, inferInstance⟩
    · exact fun h => h.1
  simpa only [g, eq] using cyclic_sylows_bound q

/-- Adapted from nilpotent_ncard_le in the merged R2.H2.R1.H2.R1.H2 proof.
The Sylow profile of a nilpotent group determines it up to isomorphism. -/
lemma nilpotent_bound (q : ℕ) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = q ∧ Group.IsSolvable G ∧ Group.IsNilpotent G}).ncard ≤
      ∏ p ∈ q.primeFactors, g (p^q.factorization p) := by
  classical
  let O (n : ℕ) := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | Nat.card G = n}
  let Profile (n : ℕ) := (p : n.primeFactors) → O ((p : ℕ)^n.factorization p)
  let rep {k : ℕ} (x : O k) : FiniteGrp.{0} := Classical.choose x.property
  have rep_class {k : ℕ} (x : O k) :
      Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (rep x) = x.val :=
    (Classical.choose_spec x.property).2
  let realize {n : ℕ} (x : Profile n) :=
    Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (FiniteGrp.of (∀ p, rep (x p)))
  let (p : q.primeFactors) : Finite (O ((p : ℕ)^q.factorization p)) :=
    (finite_classes _).to_subtype
  let _ : Finite (Profile q) := inferInstanceAs (Finite (∀ p : q.primeFactors, O _))
  have cover : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = q ∧ Group.IsSolvable G ∧ Group.IsNilpotent G} ⊆
      Set.range (realize (n := q)) := by
    rintro _ ⟨G, ⟨rfl, _, hn⟩, rfl⟩
    let _ := hn
    let t : Profile (Nat.card G) := fun p => by
      let _ : Fact (p : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors p.property⟩
      let P : Sylow (p : ℕ) G := default
      exact ⟨Quotient.mk _ (FiniteGrp.of P), FiniteGrp.of P, P.card_eq_multiplicity, rfl⟩
    refine ⟨t, Quotient.sound ?_⟩
    let E := Sylow.directProductOfNormal (G := G) fun _ => inferInstance
    let L (p : (Nat.card G).primeFactors) : (∀ P : Sylow (p : ℕ) G, P) ≃* rep (t p) := by
      let _ : Fact (p : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors p.property⟩
      let P : Sylow (p : ℕ) G := default
      have he : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (rep (t p)) =
          Quotient.mk _ (FiniteGrp.of P) := rep_class _
      let iso := Classical.choice (Quotient.exact he)
      let e := ((inducedFunctor FiniteGrp.toGrp).mapIso iso).groupIsoToMulEquiv
      let _ : Unique (Sylow (p : ℕ) G) := Sylow.unique_of_normal P inferInstance
      exact (MulEquiv.piUnique (fun Q : Sylow (p : ℕ) G => Q)).trans e.symm
    let e := (MulEquiv.piCongrRight L).symm.trans E
    exact ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp) e.toGrpIso⟩
  calc
    _ ≤ (Set.range (realize (n := q))).ncard := Set.ncard_le_ncard cover (Set.finite_range _)
    _ ≤ Nat.card (Profile q) := Nat.card_le_card_of_surjective _ Set.rangeFactorization_surjective
    _ = ∏ p : q.primeFactors, g (p ^ q.factorization p) := by rw [Nat.card_pi]; rfl
    _ = _ := Finset.prod_finset_coe (fun p => g (p ^ q.factorization p)) q.primeFactors

lemma prime_power_count {q : ℕ} (hpp : IsPrimePow q) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = q ∧ Group.IsSolvable G}).ncard ≤
      ∏ p ∈ q.primeFactors, g (p^q.factorization p) := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff q).mp hpp
  rw [Nat.primeFactors_prime_pow hk.ne' hp, Finset.prod_singleton, Nat.factorization_pow_self hp]
  have sub : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = p^k ∧ Group.IsSolvable G} ⊆
      Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = p^k} := by
    rintro _ ⟨G, ⟨hG, _⟩, rfl⟩
    exact ⟨G, hG, rfl⟩
  exact Set.ncard_le_ncard sub (finite_classes _)

/-- Thin a finite generating set, recording the doubling of subgroup order at each step. -/
theorem thin_generators {G : Type*} [Group G] [Finite G] (s : Finset G) :
    ∃ t : Finset G, t ⊆ s ∧ Subgroup.closure (t : Set G) = Subgroup.closure (s : Set G) ∧
      2 ^ t.card ≤ Nat.card (Subgroup.closure (s : Set G)) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨∅, by simp, rfl, by simp⟩
  | @insert x s hx ih =>
    obtain ⟨t, hts, ht, hpow⟩ := ih
    let H := Subgroup.closure (s : Set G)
    let J := Subgroup.closure ((insert x s : Finset G) : Set G)
    have hle : H ≤ J := Subgroup.closure_mono (by simp)
    have hxJ : x ∈ J := Subgroup.subset_closure (by simp)
    by_cases hxH : x ∈ H
    · have heq : J = H := by
        apply le_antisymm _ hle
        apply (Subgroup.closure_le _).2
        rw [Finset.coe_insert, Set.insert_subset_iff]
        exact ⟨hxH, fun _ hy => Subgroup.subset_closure hy⟩
      refine ⟨t, hts.trans (Finset.subset_insert _ _), ht.trans heq.symm, ?_⟩
      change 2 ^ t.card ≤ Nat.card J
      rw [heq]
      exact hpow
    · have hlt : Nat.card H < Nat.card J := by
        apply lt_of_not_ge
        intro h
        exact hxH ((Subgroup.eq_of_le_of_card_ge hle h).symm ▸ hxJ)
      obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hle
      have hk2 : 2 ≤ k := by
        by_contra! h
        interval_cases k <;> simp_all
      have hxT : x ∉ t := fun h => hx (hts h)
      refine ⟨insert x t, Finset.insert_subset_insert _ hts, ?_, ?_⟩
      · simp only [Finset.coe_insert, Set.insert_eq, Subgroup.closure_union, ht]
      · change 2 ^ (insert x t).card ≤ Nat.card J
        rw [Finset.card_insert_of_notMem hxT, pow_succ, hk]
        exact Nat.mul_le_mul hpow hk2

theorem hom_count (G A : Type*) [Group G] [Group A] [Finite G] [Finite A] :
    Nat.card (G →* A) ≤ Nat.card A ^ Nat.log 2 (Nat.card G) := by
  classical
  let _ := Fintype.ofFinite G
  obtain ⟨t, _, ht, hsize⟩ := thin_generators (Finset.univ : Finset G)
  rw [Finset.coe_univ, Subgroup.closure_univ] at ht hsize
  rw [Subgroup.card_top] at hsize
  let restrict (f : G →* A) (x : t) := f x
  have inj : Function.Injective restrict := by
    intro f g h
    apply MonoidHom.eq_of_eqOn_dense ht
    intro x hx
    exact congrFun h ⟨x, hx⟩
  calc
    Nat.card (G →* A) ≤ Nat.card (t → A) := Nat.card_le_card_of_injective restrict inj
    _ = Nat.card A ^ t.card := by simp [Nat.card_fun]
    _ ≤ _ := Nat.pow_le_pow_right Nat.card_pos (Nat.le_log_of_pow_le (by decide) hsize)

theorem cyclic_action_count (H K : FiniteGrp.{0}) [IsCyclic H] :
    Nat.card (H →* MulAut K) ≤ Nat.card K ^ Nat.log 2 (Nat.card K) := by
  let _ : Finite (MulAut K) := Finite.of_injective (fun a : MulAut K => (a : K → K))
    (fun _ _ h => DFunLike.ext' h)
  obtain ⟨x, hx⟩ := IsCyclic.exists_generator (α := H)
  have inj : Function.Injective (fun f : H →* MulAut K => f x) := by
    intro f g h
    apply MonoidHom.ext
    intro y
    obtain ⟨z, rfl⟩ := hx y
    simpa only [map_zpow] using congrArg (fun a : MulAut K => a ^ z) h
  let _ : Finite (K →* K) := Finite.of_injective (fun f : K →* K => (f : K → K))
    (fun _ _ h => DFunLike.ext' h)
  have injAut : Function.Injective (fun e : MulAut K => e.toMonoidHom) := by
    intro e f h
    exact DFunLike.ext' (congrArg (fun a : K →* K => (a : K → K)) h)
  exact (Nat.card_le_card_of_injective _ inj).trans
    ((Nat.card_le_card_of_injective _ injAut).trans (hom_count K K))

lemma normal_hall_of_sylow_count {k l : ℕ} (hk : 0 < k) (hl : l.Prime)
    (hcop : ¬ l ∣ k) (G : FiniteGrp.{0}) (hG : Nat.card G = k*l)
    (hcase : Nat.card (Sylow l G) = k ∨ k.Coprime (l-1)) :
    ∃ N : Subgroup G, N.Normal ∧ Nat.card N = k := by
    classical
    let _ : Fact l.Prime := ⟨hl⟩
    let P : Sylow l G := default
    have hP : Nat.card P = l := by
      rw [P.card_eq_multiplicity, hG, Nat.factorization_mul hk.ne' hl.ne_zero]
      simp [Nat.factorization_eq_zero_of_not_dvd hcop, hl.factorization]
    have hc : IsCyclic P := isCyclic_of_prime_card hP
    have central : Subgroup.normalizer (P : Set G) ≤ Subgroup.centralizer (P : Set G) := by
      rcases hcase with hfull | haut
      · have hind := P.card_eq_index_normalizer.symm.trans hfull
        have hsize := (Subgroup.normalizer (P : Set G)).index_mul_card
        rw [hind, hG] at hsize
        have eq := Subgroup.eq_of_le_of_card_ge P.le_normalizer
          ((Nat.eq_of_mul_eq_mul_left hk hsize).le.trans hP.ge)
        exact eq.ge.trans P.le_centralizer
      · have key := Subgroup.card_dvd_of_injective _ (QuotientGroup.kerLift_injective P.normalizerMonoidHom)
        rw [Subgroup.normalizerMonoidHom_ker, ← Subgroup.index, ← Subgroup.relIndex] at key
        apply Subgroup.relIndex_eq_one.mp
        apply Nat.eq_one_of_dvd_coprimes _ dvd_rfl key
        rw [hc.card_mulAut, hP, Nat.totient_prime hl]
        apply Nat.Coprime.coprime_dvd_left (Subgroup.relIndex_dvd_card ..)
        apply Nat.Coprime.coprime_dvd_left (Subgroup.card_subgroup_dvd_card _)
        rw [hG]
        exact haut.mul_left ((Nat.coprime_self_sub_right hl.one_le).mpr (Nat.coprime_one_right _))
    let N := (MonoidHom.transferSylow P central).ker
    have comp : N.IsComplement' (P : Subgroup G) := MonoidHom.ker_transferSylow_isComplement' P central
    have hn : Nat.card N = k := by
      have h := comp.card_mul_card
      change Nat.card N * Nat.card P = Nat.card G at h
      rw [hP, hG] at h
      exact Nat.eq_of_mul_eq_mul_right hl.pos h
    exact ⟨N, inferInstance, hn⟩

/-- Count split extensions by a cyclic complement, restricting the allowed kernels. -/
theorem cyclic_split_count {k l : ℕ} (hl : 0 < l) (W : FiniteGrp.{0} → Prop) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | ∃ N P : Subgroup G, N.Normal ∧ N.IsComplement' P ∧ IsCyclic P ∧ Nat.card N = k ∧ Nat.card P = l ∧ W (FiniteGrp.of N)}).ncard ≤
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = k ∧ W G}).ncard * k^(Nat.log 2 k) := by
  classical
  let orderClasses (n : ℕ) := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | Nat.card G = n ∧ W G}
  let _ : NeZero l := ⟨hl.ne'⟩
  let H := FiniteGrp.of (Multiplicative (ZMod l))
  let _ : IsCyclic H := inferInstanceAs (IsCyclic (Multiplicative (ZMod l)))
  let K (x : orderClasses k) : FiniteGrp.{0} := x.property.choose
  have rep (x : orderClasses k) : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (K x) = x.val :=
    x.property.choose_spec.2
  have order (x : orderClasses k) : Nat.card (K x) = k := x.property.choose_spec.1.1
  let _ : Finite (orderClasses k) := ((finite_classes k).subset (Set.image_mono (fun _ h => h.1))).to_subtype
  let _ := Fintype.ofFinite (orderClasses k)
  let A (x : orderClasses k) := H →* MulAut (K x)
  let (x : orderClasses k) : Finite (A x) := by
    let _ : Finite (MulAut (K x)) := Finite.of_injective (fun a : MulAut (K x) => (a : K x → K x))
      (fun _ _ h => DFunLike.ext' h)
    exact Finite.of_injective (fun a : A x => (a : H → MulAut (K x))) (fun _ _ h => DFunLike.ext' h)
  let decode (z : (x : orderClasses k) × A x) : Quotient (isIsomorphicSetoid FiniteGrp.{0}) := by
    letI : Finite (SemidirectProduct (K z.1) H z.2) :=
      Finite.of_equiv (K z.1 × H) SemidirectProduct.equivProd.symm
    exact Quotient.mk _ (FiniteGrp.of (SemidirectProduct (K z.1) H z.2))
  have cover : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | ∃ N P : Subgroup G, N.Normal ∧ N.IsComplement' P ∧ IsCyclic P ∧ Nat.card N = k ∧ Nat.card P = l ∧ W (FiniteGrp.of N)} ⊆ Set.range decode := by
    rintro _ ⟨G, ⟨N, P, hN, comp, hc, hn, hP, hw⟩, rfl⟩
    let x : orderClasses k := ⟨Quotient.mk _ (FiniteGrp.of N), FiniteGrp.of N, ⟨hn, hw⟩, rfl⟩
    let i := Classical.choice (Quotient.exact (rep x))
    let fn : N ≃* K x := ((inducedFunctor FiniteGrp.toGrp).mapIso i).groupIsoToMulEquiv.symm
    let fh : P ≃* H := mulEquivOfCyclicCardEq (hP.trans (Nat.card_zmod _).symm)
    let e := SemidirectProduct.mulEquivSubgroup comp
    let f := e.symm.trans (SemidirectProduct.congr' fn fh)
    let a : P →* MulAut N := N.normalizerMonoidHom.comp (Subgroup.inclusion (N.normalizer_eq_top ▸ le_top))
    refine ⟨⟨x, MonoidHom.comp (MulAut.congr fn) (a.comp fh.symm)⟩, Quotient.sound ?_⟩
    exact ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp) f.symm.toGrpIso⟩
  calc
    _ ≤ (Set.range decode).ncard := Set.ncard_le_ncard cover (Set.finite_range _)
    _ ≤ Nat.card ((x : orderClasses k) × A x) :=
      Nat.card_le_card_of_surjective _ (Set.rangeFactorization_surjective (f := decode))
    _ = ∑ x : orderClasses k, Nat.card (A x) := Nat.card_sigma
    _ ≤ ∑ _x : orderClasses k, k^(Nat.log 2 k) := Finset.sum_le_sum fun x _ => by
      simpa only [order] using cyclic_action_count H (K x)
    _ = _ := by simp [← Nat.card_eq_fintype_card, orderClasses]

/-- Count groups having a normal Hall subgroup of prime index. -/
theorem peel {k l : ℕ} (hk : 0 < k) (hl : l.Prime)
    (hcop : ¬ l ∣ k) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = k*l ∧ (∃ N : Subgroup G, N.Normal ∧ Nat.card N = k)}).ncard ≤ g k * k^(Nat.log 2 k) := by
  classical
  let _ : Fact l.Prime := ⟨hl⟩
  have bound := cyclic_split_count (k := k) hl.pos (fun _ => True)
  simp only [and_true] at bound
  apply le_trans _ bound
  apply Set.ncard_le_ncard _ ((finite_classes (k*l)).subset (Set.image_mono ?_))
  · rintro _ ⟨G, ⟨hG, hcase⟩, rfl⟩
    obtain ⟨N, hN, hn⟩ := hcase
    let _ : N.Normal := hN
    have hind : N.index = l := by
      have h := N.index_mul_card
      rw [hn, hG, Nat.mul_comm k l] at h
      exact Nat.eq_of_mul_eq_mul_right hk h
    have cop : (Nat.card N).Coprime N.index := by
      rw [hn, hind]
      exact (hl.coprime_iff_not_dvd.mpr hcop).symm
    obtain ⟨P, comp⟩ := Subgroup.exists_right_complement'_of_coprime cop
    have hP : Nat.card P = l := comp.symm.index_eq_card.symm.trans hind
    have hc : IsCyclic P := isCyclic_of_prime_card hP
    exact ⟨G, ⟨N, P, hN, comp, hc, hn, hP⟩, rfl⟩
  · rintro G ⟨N, P, _, comp, _, hn, hP⟩
    exact comp.card_mul_card.symm.trans (congrArg₂ (· * ·) hn hP)

/-- Count actions of the allowed complements on a cyclic normal subgroup. -/
theorem cyclic_kernel_count {k l : ℕ} (hl : 0 < l) (W : FiniteGrp.{0} → Prop) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | ∃ N P : Subgroup G, P.Normal ∧ N.IsComplement' P ∧ IsCyclic P ∧ Nat.card N = k ∧ Nat.card P = l ∧ W (FiniteGrp.of N)}).ncard ≤
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = k ∧ W G}).ncard * l^(Nat.log 2 k) := by
  classical
  let orderClasses (n : ℕ) := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | Nat.card G = n ∧ W G}
  let _ : NeZero l := ⟨hl.ne'⟩
  let H := FiniteGrp.of (Multiplicative (ZMod l))
  let _ : IsCyclic H := inferInstanceAs (IsCyclic (Multiplicative (ZMod l)))
  let K (x : orderClasses k) : FiniteGrp.{0} := x.property.choose
  have rep (x : orderClasses k) : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (K x) = x.val :=
    x.property.choose_spec.2
  have order (x : orderClasses k) : Nat.card (K x) = k := x.property.choose_spec.1.1
  let _ : Finite (orderClasses k) := ((finite_classes k).subset (Set.image_mono (fun _ h => h.1))).to_subtype
  let _ := Fintype.ofFinite (orderClasses k)
  let A (x : orderClasses k) := K x →* MulAut H
  let (x : orderClasses k) : Finite (A x) := by
    let _ : Finite (MulAut H) := Finite.of_injective (fun a : MulAut H => (a : H → H))
      (fun _ _ h => DFunLike.ext' h)
    exact Finite.of_injective (fun a : A x => (a : K x → MulAut H)) (fun _ _ h => DFunLike.ext' h)
  let decode (z : (x : orderClasses k) × A x) : Quotient (isIsomorphicSetoid FiniteGrp.{0}) := by
    letI : Finite (SemidirectProduct H (K z.1) z.2) :=
      Finite.of_equiv (H × K z.1) SemidirectProduct.equivProd.symm
    exact Quotient.mk _ (FiniteGrp.of (SemidirectProduct H (K z.1) z.2))
  have cover : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | ∃ N P : Subgroup G, P.Normal ∧ N.IsComplement' P ∧ IsCyclic P ∧ Nat.card N = k ∧ Nat.card P = l ∧ W (FiniteGrp.of N)} ⊆ Set.range decode := by
    rintro _ ⟨G, ⟨N, P, hPnorm, comp, hc, hn, hP, hw⟩, rfl⟩
    let x : orderClasses k := ⟨Quotient.mk _ (FiniteGrp.of N), FiniteGrp.of N, ⟨hn, hw⟩, rfl⟩
    let i := Classical.choice (Quotient.exact (rep x))
    let fn : N ≃* K x := ((inducedFunctor FiniteGrp.toGrp).mapIso i).groupIsoToMulEquiv.symm
    let fh : P ≃* H := mulEquivOfCyclicCardEq (hP.trans (Nat.card_zmod _).symm)
    let e := SemidirectProduct.mulEquivSubgroup comp.symm
    let f := e.symm.trans (SemidirectProduct.congr' fh fn)
    let a : N →* MulAut P := (P : Subgroup G).normalizerMonoidHom.comp
      (Subgroup.inclusion ((P : Subgroup G).normalizer_eq_top ▸ le_top))
    refine ⟨⟨x, MonoidHom.comp (MulAut.congr fh) (a.comp fn.symm)⟩, Quotient.sound ?_⟩
    exact ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp) f.symm.toGrpIso⟩
  calc
    _ ≤ (Set.range decode).ncard := Set.ncard_le_ncard cover (Set.finite_range _)
    _ ≤ Nat.card ((x : orderClasses k) × A x) :=
      Nat.card_le_card_of_surjective _ (Set.rangeFactorization_surjective (f := decode))
    _ = ∑ x : orderClasses k, Nat.card (A x) := Nat.card_sigma
    _ ≤ ∑ _x : orderClasses k, l^(Nat.log 2 k) := Finset.sum_le_sum fun x _ => by
      let _ : Finite (MulAut H) := Finite.of_injective (fun a : MulAut H => (a : H → H))
        (fun _ _ h => DFunLike.ext' h)
      have bound := hom_count (K x) (MulAut H)
      have cardH : Nat.card H = l := Nat.card_zmod _
      rw [IsCyclic.card_mulAut H, cardH, order] at bound
      exact bound.trans (Nat.pow_le_pow_left (Nat.totient_le _) _)
    _ = _ := by simp [← Nat.card_eq_fintype_card, orderClasses]

/-- Count the cyclic normal Sylow kernel by actions of a complement of order k. -/
theorem normal_prime_count {k l : ℕ} (hk : 0 < k) (hl : l.Prime)
    (hcop : ¬ l ∣ k) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = k*l ∧ Nat.card (Sylow l G) = 1}).ncard ≤ g k * l^(Nat.log 2 k) := by
  classical
  let _ : Fact l.Prime := ⟨hl⟩
  have bound := cyclic_kernel_count (k := k) hl.pos (fun _ => True)
  simp only [and_true] at bound
  apply le_trans _ bound
  apply Set.ncard_le_ncard _ ((finite_classes (k*l)).subset (Set.image_mono ?_))
  · rintro _ ⟨G, ⟨hG, count_one⟩, rfl⟩
    let P : Sylow l G := default
    have hP : Nat.card P = l := by
      rw [P.card_eq_multiplicity, hG, Nat.factorization_mul hk.ne' hl.ne_zero]
      simp [Nat.factorization_eq_zero_of_not_dvd hcop, hl.factorization]
    have hc : IsCyclic P := isCyclic_of_prime_card hP
    have hindex : P.index = k := by
      have h := (P : Subgroup G).index_mul_card
      change P.index * Nat.card P = Nat.card G at h
      rw [hP, hG] at h
      exact Nat.eq_of_mul_eq_mul_right hl.pos h
    let _ : Subsingleton (Sylow l G) := (Nat.card_eq_one_iff_unique.mp count_one).1
    let _ : (P : Subgroup G).Normal := Sylow.normal_of_subsingleton P
    have cop : (Nat.card P).Coprime P.index := by
      rw [hP, hindex]
      exact hl.coprime_iff_not_dvd.mpr hcop
    obtain ⟨N, comp⟩ := Subgroup.exists_right_complement'_of_coprime cop
    have hn : Nat.card N = k := comp.symm.index_eq_card.symm.trans hindex
    exact ⟨G, ⟨N, P, inferInstance, comp.symm, hc, hn, hP⟩, rfl⟩
  · rintro G ⟨N, P, _, comp, _, hn, hP⟩
    exact comp.card_mul_card.symm.trans (congrArg₂ (· * ·) hn hP)

/-- Bound the classes with a normal Sylow subgroup in either characteristic. -/
theorem normal_hall_bound {p l a r : ℕ} (hp : p.Prime) (hl : l.Prime) (hne : p ≠ l)
    (ha : 0 < a) (hr : p^a*l < 2^r) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = p^a*l ∧ ((∃ N : Subgroup G, N.Normal ∧ Nat.card N = p^a) ∨ Nat.card (Sylow l G) = 1)}).ncard ≤ 2^((r+1)^2) *
      ∏ b ∈ (p^a*l).primeFactors, g (b^(p^a*l).factorization b) := by
  have hk : 0 < p^a := pow_pos hp.pos _
  have hcop : ¬ l ∣ p^a := fun h =>
    hne.symm ((Nat.prime_dvd_prime_iff_eq hl hp).mp (hl.dvd_of_dvd_pow h))
  have hkr := (Nat.le_mul_of_pos_right (p^a) hl.pos).trans_lt hr
  have overhead (b : ℕ) (hb : b ≤ 2^r) : b^(Nat.log 2 (p^a)) ≤ 2^(r*r) := by
    calc
      _ ≤ (2^r)^(Nat.log 2 (p^a)) := Nat.pow_le_pow_left hb _
      _ ≤ (2^r)^r := Nat.pow_le_pow_right (by positivity) (Nat.log_lt_of_lt_pow hk.ne' hkr).le
      _ = 2^(r*r) := (pow_mul ..).symm
  have hv : (p^a*l).factorization p = a := by
    rw [Nat.factorization_mul hk.ne' hl.ne_zero, Finsupp.add_apply, Nat.factorization_pow_self hp,
      Nat.factorization_eq_zero_of_not_dvd (fun h => hne ((Nat.prime_dvd_prime_iff_eq hp hl).mp h)), add_zero]
  have hmem : p ∈ (p^a*l).primeFactors := Nat.mem_primeFactors.mpr
    ⟨hp, dvd_mul_of_dvd_left (dvd_pow_self p ha.ne') _, (Nat.mul_pos hk hl.pos).ne'⟩
  have positive (b : ℕ) (hb : b ∈ (p^a*l).primeFactors) :
      1 ≤ g (b^(p^a*l).factorization b) := by
    exact positive_count (pow_pos (Nat.prime_of_mem_primeFactors hb).pos _)
  have component := Finset.single_le_prod' positive hmem
  rw [hv] at component
  let S (t : FiniteGrp.{0} → Prop) := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | Nat.card G = p^a*l ∧ t G}
  let A (G : FiniteGrp.{0}) := ∃ N : Subgroup G, N.Normal ∧ Nat.card N = p^a
  let B (G : FiniteGrp.{0}) := Nat.card (Sylow l G) = 1
  have cover : S (fun G => A G ∨ B G) = S A ∪ S B := by
    ext c
    constructor
    · rintro ⟨G, ⟨hg, h | h⟩, rfl⟩
      · exact Or.inl ⟨G, ⟨hg, h⟩, rfl⟩
      · exact Or.inr ⟨G, ⟨hg, h⟩, rfl⟩
    · rintro (⟨G, ⟨hg, h⟩, rfl⟩ | ⟨G, ⟨hg, h⟩, rfl⟩)
      · exact ⟨G, ⟨hg, Or.inl h⟩, rfl⟩
      · exact ⟨G, ⟨hg, Or.inr h⟩, rfl⟩
  let L := ∏ b ∈ (p^a*l).primeFactors, g (b^(p^a*l).factorization b)
  have major (b : ℕ) (hb : b ≤ 2^r) :
      g (p^a)*b^(Nat.log 2 (p^a)) ≤ 2^(r*r)*L :=
    (Nat.mul_comm ..).le.trans (Nat.mul_le_mul (overhead _ hb) component)
  have boundA := (peel hk hl hcop).trans (major _ hkr.le)
  have boundB := (normal_prime_count hk hl hcop).trans
    (major _ ((Nat.le_mul_of_pos_left l hk).trans hr.le))
  change (S (fun G => A G ∨ B G)).ncard ≤ _
  rw [cover]
  calc
    _ ≤ (S A).ncard + (S B).ncard := Set.ncard_union_le _ _
    _ ≤ 2^(r*r)*L + 2^(r*r)*L := Nat.add_le_add boundA boundB
    _ = 2^(r*r+1)*L := by rw [pow_succ]; ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (by nlinarith : r*r+1 ≤ (r+1)^2))

/-- The requested estimate with E = 1 for orders p^a l, under either normal-complement or normal-Sylow criterion. -/
theorem two_prime_bound {p l a r : ℕ} (hp : p.Prime) (hl : l.Prime) (hne : p ≠ l) (criterion : ¬ p ∣ l-1 ∨ ∀ i, 0 < i → i < a → ¬ Nat.ModEq l (p^i) 1)
    (ha : 0 < a) (hr : p^a*l < 2^r) :
    g (p^a*l) ≤ 2^((r+1)^2) *
      ∏ b ∈ (p^a*l).primeFactors, g (b^(p^a*l).factorization b) := by
  have hk : 0 < p^a := pow_pos hp.pos _
  have hcop : ¬ l ∣ p^a := fun h =>
    hne.symm ((Nat.prime_dvd_prime_iff_eq hl hp).mp (hl.dvd_of_dvd_pow h))
  apply le_trans _ (normal_hall_bound hp hl hne ha hr)
  classical
  apply le_of_eq
  unfold g
  congr 1
  apply congrArg
  ext G
  constructor
  · intro hG
    refine ⟨hG, ?_⟩
    have transfer := normal_hall_of_sylow_count hk hl hcop G hG
    rcases criterion with haut | hres
    · exact Or.inl (transfer (Or.inr ((hp.coprime_iff_not_dvd.mpr haut).pow_left a)))
    let _ : Fact l.Prime := ⟨hl⟩
    let P : Sylow l G := default
    have hP : Nat.card P = l := by
      rw [P.card_eq_multiplicity, hG, Nat.factorization_mul hk.ne' hl.ne_zero]
      simp [Nat.factorization_eq_zero_of_not_dvd (show ¬ l ∣ p from fun h =>
        hne.symm ((Nat.prime_dvd_prime_iff_eq hl hp).mp h)), hl.factorization]
    have ind := (P : Subgroup G).index_mul_card
    change P.index * Nat.card P = Nat.card G at ind
    rw [hP, hG] at ind
    have hdiv := (Nat.eq_of_mul_eq_mul_right hl.pos ind) ▸ P.card_dvd_index
    obtain ⟨i, hi, he⟩ := (Nat.dvd_prime_pow hp).mp hdiv
    by_cases hz : i = 0
    · exact Or.inr (by simpa [hz] using he)
    by_cases heq : i = a
    · exact Or.inl (transfer (Or.inl (heq ▸ he)))
    exact (hres i (Nat.pos_of_ne_zero hz) (lt_of_le_of_ne hi heq)
      (he ▸ card_sylow_modEq_one l G)).elim
  · exact fun h => h.1

/-- Every odd order p^a l with a at most three satisfies the desired estimate. -/
theorem small_exponent_bound {p l r a : ℕ} (hp : p.Prime) (hl : l.Prime) (hne : p ≠ l)
    (hop : Odd p) (hol : Odd l) (ha : 0 < a) (ha3 : a ≤ 3) (hr : p^a*l < 2^r) :
    g (p^a*l) ≤ 2^((r+1)^2) *
      ∏ b ∈ (p^a*l).primeFactors, g (b^(p^a*l).factorization b) := by
  apply two_prime_bound hp hl hne _ ha hr
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · right
    obtain ⟨u, hu⟩ := hop
    obtain ⟨v, hv⟩ := hol
    have gap : p+1 < l := by omega
    have ppos := hp.one_lt
    have small₁ : ¬ l ∣ p-1 := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
    have small₂ : ¬ l ∣ p+1 := Nat.not_dvd_of_pos_of_lt (by omega) gap
    intro i hi hle he
    have hdvd := (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hp.pos)).mp he.symm
    have hi2 : i ≤ 2 := by omega
    interval_cases i
    · exact small₁ (by simpa using hdvd)
    · have factor : p^2-1 = (p-1)*(p+1) := by
        have h := Nat.sub_add_cancel (show 1 ≤ p by omega)
        have h' := Nat.sub_add_cancel (show 1 ≤ p^2 from Nat.pow_pos hp.pos)
        nlinarith [congrArg (fun x : ℕ => x * (p+1)) h]
      exact (hl.dvd_mul.mp (factor ▸ hdvd)).elim small₁ small₂
  · left
    exact Nat.not_dvd_of_pos_of_lt (Nat.sub_pos_of_lt hl.one_lt) (by omega)

/-- Specialization to odd orders p² l. -/
theorem square_prime_bound {p l r : ℕ} (hp : p.Prime) (hl : l.Prime) (hne : p ≠ l)
    (hop : Odd p) (hol : Odd l) (hr : p^2*l < 2^r) :
    g (p^2*l) ≤ 2^((r+1)^2) *
      ∏ b ∈ (p^2*l).primeFactors, g (b^(p^2*l).factorization b) :=
  small_exponent_bound hp hl hne hop hol (by decide) (by decide) hr

/-- An abelian Sylow subgroup of prime index is normal or has a normal complement. -/
theorem normal_hall_of_abelian {p l a : ℕ} (hp : p.Prime) (hl : l.Prime) (hne : p ≠ l)
    (G : FiniteGrp.{0}) (hg : Nat.card G = p^a*l) (P : Sylow p G) [IsMulCommutative P] :
    (∃ N : Subgroup G, N.Normal ∧ Nat.card N = p^a) ∨ Nat.card (Sylow l G) = 1 := by
  classical
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : Fact l.Prime := ⟨hl⟩
  have hk := pow_pos hp.pos a
  have hP : Nat.card P = p^a := by
    rw [P.card_eq_multiplicity, hg, Nat.factorization_mul hk.ne' hl.ne_zero,
      Finsupp.add_apply, Nat.factorization_pow_self hp, Nat.factorization_eq_zero_of_not_dvd
        (fun h => hne ((Nat.prime_dvd_prime_iff_eq hp hl).mp h)), add_zero]
  have ind := (P : Subgroup G).index_mul_card
  change P.index * Nat.card P = Nat.card G at ind
  rw [hP, hg, Nat.mul_comm (p^a) l] at ind
  have index := Nat.eq_of_mul_eq_mul_right hk ind
  rcases (Nat.dvd_prime hl).mp (index ▸ P.card_dvd_index) with one | full
  · let _ : Subsingleton (Sylow p G) := (Nat.card_eq_one_iff_unique.mp one).1
    exact Or.inl ⟨P, Sylow.normal_of_subsingleton P, hP⟩
  · have size := (Subgroup.normalizer (P : Set G)).index_mul_card
    rw [← P.card_eq_index_normalizer, full, hg, Nat.mul_comm (p^a) l] at size
    have eq := Subgroup.eq_of_le_of_card_ge P.le_normalizer
      ((Nat.eq_of_mul_eq_mul_left hl.pos size).le.trans hP.ge)
    have central : Subgroup.normalizer (P : Set G) ≤ Subgroup.centralizer (P : Set G) :=
      eq.ge.trans P.le_centralizer
    let N := (MonoidHom.transferSylow P central).ker
    have comp : N.IsComplement' (P : Subgroup G) :=
      MonoidHom.ker_transferSylow_isComplement' P central
    have hn : Nat.card N = l := comp.index_eq_card.symm.trans index
    let Q := Sylow.ofCard (p := l) N (by
      rw [hn, hg, Nat.factorization_mul hk.ne' hl.ne_zero]
      simp [Nat.factorization_eq_zero_of_not_dvd (show ¬ l ∣ p from fun h =>
        hne.symm ((Nat.prime_dvd_prime_iff_eq hl hp).mp h)), hl.factorization])
    let _ := Q.unique_of_normal (by change N.Normal; infer_instance)
    exact Or.inr (Nat.card_unique)

/-- At prime index, the abelian Sylow case satisfies the estimate with E = 1. -/
theorem abelian_sylow_bound {p l a r : ℕ} (hp : p.Prime) (hl : l.Prime) (hne : p ≠ l)
    (ha : 0 < a) (hr : p^a*l < 2^r) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = p^a*l ∧ ∃ P : Sylow p G, IsMulCommutative P}).ncard ≤
      2^((r+1)^2) * ∏ b ∈ (p^a*l).primeFactors, g (b^(p^a*l).factorization b) := by
  apply le_trans _ (normal_hall_bound hp hl hne ha hr)
  apply Set.ncard_le_ncard _ ((finite_classes _).subset (Set.image_mono (fun _ h => h.1)))
  rintro _ ⟨G, ⟨hg, P, hc⟩, rfl⟩
  exact ⟨G, ⟨hg, normal_hall_of_abelian hp hl hne G hg P⟩, rfl⟩

/-- Count complementary cyclic and nilpotent Hall factors when either factor is normal. -/
theorem cyclic_nilpotent_hall_bound {q r : ℕ} (hr : q < 2^r) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = q ∧ Group.IsSolvable G ∧ (∃ N P : Subgroup G, (N.Normal ∨ P.Normal) ∧ N.IsComplement' P ∧ IsCyclic P ∧ Group.IsNilpotent N ∧ (Nat.card N).Coprime (Nat.card P))}).ncard ≤
      2^((r+1)^2) * ∏ p ∈ q.primeFactors, g (p^q.factorization p) := by
  classical
  let W (G : FiniteGrp.{0}) := Group.IsSolvable G ∧ Group.IsNilpotent G
  let L := ∏ p ∈ q.primeFactors, g (p^q.factorization p)
  let S (normalNilpotent : Bool) (k : Fin (q+1)) := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | ∃ N P : Subgroup G, (if normalNilpotent then N.Normal else P.Normal) ∧ N.IsComplement' P ∧ IsCyclic P ∧
      Nat.card N = k.val ∧ Nat.card P = q/k.val ∧ W (FiniteGrp.of N)}
  let I := {k : Fin (q+1) // 0 < k.val ∧ 0 < q/k.val ∧ k.val*(q/k.val) = q ∧ k.val.Coprime (q/k.val)}
  have bound (b : Bool) (i : I) : (S b i.val).ncard ≤ 2^(r*r)*L := by
    obtain ⟨k, hk, hb, eq, cop⟩ := i
    have parts : (∏ p ∈ k.val.primeFactors, g (p^k.val.factorization p)) ≤ L := by
      have sub : k.val.primeFactors ⊆ q.primeFactors := by
        rw [← congrArg Nat.primeFactors eq, Nat.primeFactors_mul hk.ne' hb.ne']
        exact Finset.subset_union_left
      calc
        _ = ∏ p ∈ k.val.primeFactors, g (p^q.factorization p) := by
          apply Finset.prod_congr rfl
          intro p hp
          have notdvd : ¬ p ∣ q/k.val := fun h => (Nat.prime_of_mem_primeFactors hp).not_dvd_one
            (cop ▸ Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hp) h)
          rw [← congrArg Nat.factorization eq, Nat.factorization_mul hk.ne' hb.ne', Finsupp.add_apply,
            Nat.factorization_eq_zero_of_not_dvd notdvd, add_zero]
        _ ≤ _ := Finset.prod_le_prod_of_subset_of_one_le' sub fun p hp _ =>
          positive_count (pow_pos (Nat.prime_of_mem_primeFactors hp).pos _)
    have hkr : k.val < 2^r := (Nat.le_of_lt_succ k.isLt).trans_lt hr
    have overhead (u : ℕ) (hu : u ≤ 2^r) : u^(Nat.log 2 k.val) ≤ 2^(r*r) := by
      calc
        _ ≤ (2^r)^(Nat.log 2 k.val) := Nat.pow_le_pow_left hu _
        _ ≤ (2^r)^r := Nat.pow_le_pow_right (by positivity) (Nat.log_lt_of_lt_pow hk.ne' hkr).le
        _ = _ := (pow_mul ..).symm
    have cost (u : ℕ) (hu : u ≤ 2^r) := (Nat.mul_le_mul ((nilpotent_bound k.val).trans parts)
      (overhead u hu)).trans (Nat.mul_comm ..).le
    cases b
    · exact (cyclic_kernel_count hb W).trans (cost _ ((Nat.div_le_self ..).trans hr.le))
    · exact (cyclic_split_count hb W).trans (cost _ hkr.le)
  have cover : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = q ∧ Group.IsSolvable G ∧ (∃ N P : Subgroup G, (N.Normal ∨ P.Normal) ∧ N.IsComplement' P ∧ IsCyclic P ∧ Group.IsNilpotent N ∧ (Nat.card N).Coprime (Nat.card P))} ⊆
      ⋃ z : Bool × I, S z.1 z.2.val := by
    rintro _ ⟨G, ⟨hg, hs, N, P, hn, comp, hc, hnil, cop⟩, rfl⟩
    have eq := comp.card_mul_card.trans hg
    have hk : 0 < Nat.card N := Nat.card_pos
    have hb : 0 < Nat.card P := Nat.card_pos
    have div : q / Nat.card N = Nat.card P := by rw [← eq, Nat.mul_div_cancel_left _ hk]
    let k : Fin (q+1) := ⟨Nat.card N, by have := (Nat.le_mul_of_pos_right (Nat.card N) hb).trans eq.le; omega⟩
    let i : I := ⟨k, hk, div.symm ▸ hb, div.symm ▸ eq, div.symm ▸ cop⟩
    rcases hn with hn | hp
    · refine Set.mem_iUnion.mpr ⟨(true, i), G, ⟨N, P, hn, comp, hc, rfl, div.symm, inferInstanceAs (Group.IsSolvable N), hnil⟩, rfl⟩
    · refine Set.mem_iUnion.mpr ⟨(false, i), G, ⟨N, P, hp, comp, hc, rfl, div.symm, inferInstanceAs (Group.IsSolvable N), hnil⟩, rfl⟩
  have finite (z : Bool × I) : (S z.1 z.2.val).Finite := (finite_classes q).subset (Set.image_mono (by
    rintro G ⟨N, P, _, comp, _, hn, hp, _⟩
    exact comp.card_mul_card.symm.trans ((congrArg₂ (· * ·) hn hp).trans z.2.property.2.2.1)))
  calc
    _ ≤ (⋃ z : Bool × I, S z.1 z.2.val).ncard := Set.ncard_le_ncard cover (Set.finite_iUnion finite)
    _ ≤ ∑ z : Bool × I, (S z.1 z.2.val).ncard := Set.ncard_iUnion_le_of_fintype _
    _ ≤ ∑ _ : Bool × I, 2^(r*r)*L := Finset.sum_le_sum fun z _ => bound z.1 z.2
    _ = (2 * Fintype.card I) * (2^(r*r)*L) := by simp
    _ ≤ (2 * 2^r) * (2^(r*r)*L) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 (by
      have h := Fintype.card_subtype_le (fun k : Fin (q+1) => 0 < k.val ∧ 0 < q/k.val ∧ k.val*(q/k.val) = q ∧ k.val.Coprime (q/k.val))
      simpa [I] using h.trans (by simpa using hr : Fintype.card (Fin (q+1)) ≤ 2^r)))
    _ = 2^(r+r*r+1)*L := by rw [pow_succ, pow_add]; ac_rfl
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (by nlinarith : r+r*r+1 ≤ (r+1)^2))

/-- Count homomorphisms by evaluating on a generating set of minimum size. -/
lemma rank_hom_count (G A : Type*) [Group G] [Group A] [Finite G] [Finite A] :
    Nat.card (G →* A) ≤ Nat.card A ^ Group.rank G := by
  classical
  obtain ⟨t, size, gen⟩ := Group.rank_spec G
  let restrict (f : G →* A) (x : t) := f x
  have inj : Function.Injective restrict := by
    intro f g h
    apply MonoidHom.eq_of_eqOn_dense gen
    exact fun x hx => congrFun h ⟨x, hx⟩
  simpa [Nat.card_fun, size] using Nat.card_le_card_of_injective restrict inj

/-- Count nilpotent Hall extensions whose generator images fit the quadratic exponent. -/
theorem hall_action_bound {q r d : ℕ} (hd : 0 < d) (hr : q < 2^r) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = q ∧ Group.IsSolvable G ∧ (∃ N P : Subgroup G, N.Normal ∧ N.IsComplement' P ∧ Group.IsNilpotent N ∧ Group.IsNilpotent P ∧ Nat.card N ^ (Group.rank N * Group.rank P) ≤ 2^(r*r*d) ∧ (Nat.card N).Coprime (Nat.card P))}).ncard ≤
      2^(d*(r+1)^2) * ∏ p ∈ q.primeFactors, g (p^q.factorization p) := by
  classical
  let W (G : FiniteGrp.{0}) := Group.IsSolvable G ∧ Group.IsNilpotent G
  let O (n : ℕ) := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | Nat.card G = n ∧ W G}
  let K {n : ℕ} (x : O n) : FiniteGrp.{0} := x.property.choose
  have rep {n : ℕ} (x : O n) : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (K x) = x.val :=
    x.property.choose_spec.2
  have order {n : ℕ} (x : O n) : Nat.card (K x) = n := x.property.choose_spec.1.1
  let (n : ℕ) : Finite (O n) := ((finite_classes n).subset (Set.image_mono (fun _ h => h.1))).to_subtype
  let L (n : ℕ) := ∏ p ∈ n.primeFactors, g (p^n.factorization p)
  have factor {k l : ℕ} (hk : 0 < k) (hl : 0 < l) (cop : k.Coprime l) :
      L (k*l) = L k * L l := by
    have part {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (h : a.Coprime b) (p : ℕ) (hp : p ∈ a.primeFactors) :
        (a*b).factorization p = a.factorization p := by
      have nd : ¬ p ∣ b := fun hh => (Nat.prime_of_mem_primeFactors hp).not_dvd_one
        (h ▸ Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hp) hh)
      simp [Nat.factorization_mul ha.ne' hb.ne', Nat.factorization_eq_zero_of_not_dvd nd]
    unfold L
    rw [Nat.primeFactors_mul hk.ne' hl.ne', Finset.prod_union cop.disjoint_primeFactors]
    congr 1
    · exact Finset.prod_congr rfl fun p hp => by rw [part hk hl cop p hp]
    · exact Finset.prod_congr rfl fun p hp => by rw [Nat.mul_comm k l, part hl hk cop.symm p hp]
  let I := {k : Fin (q+1) // 0 < k.val ∧ 0 < q/k.val ∧ k.val*(q/k.val) = q ∧ k.val.Coprime (q/k.val)}
  let T (i : I) := (x : O i.val.val × O (q/i.val.val)) ×
    {a : K x.2 →* MulAut (K x.1) // Nat.card (K x.1) ^ (Group.rank (K x.1) * Group.rank (K x.2)) ≤ 2^(r*r*d)}
  let autFin (H : FiniteGrp.{0}) : Finite (MulAut H) :=
    Finite.of_injective (fun a : MulAut H => (a : H → H)) (fun _ _ h => DFunLike.ext' h)
  let actFin (H J : FiniteGrp.{0}) : Finite (H →* MulAut J) :=
    Finite.of_injective (fun a : H →* MulAut J => (a : H → MulAut J)) (fun _ _ h => DFunLike.ext' h)
  let (i : I) : Finite (T i) := inferInstanceAs (Finite (Sigma _))
  let decode (z : (i : I) × T i) : Quotient (isIsomorphicSetoid FiniteGrp.{0}) := by
    let x := z.2.1
    let a := z.2.2.val
    let _ : Finite (SemidirectProduct (K x.1) (K x.2) a) :=
      Finite.of_equiv (K x.1 × K x.2) SemidirectProduct.equivProd.symm
    exact Quotient.mk _ (FiniteGrp.of (SemidirectProduct (K x.1) (K x.2) a))
  have cover : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = q ∧ Group.IsSolvable G ∧ (∃ N P : Subgroup G, N.Normal ∧ N.IsComplement' P ∧ Group.IsNilpotent N ∧ Group.IsNilpotent P ∧ Nat.card N ^ (Group.rank N * Group.rank P) ≤ 2^(r*r*d) ∧ (Nat.card N).Coprime (Nat.card P))} ⊆ Set.range decode := by
    rintro _ ⟨G, ⟨hg, hs, N, P, hn, comp, hnil, hpnil, rank, cop⟩, rfl⟩
    have eq := comp.card_mul_card.trans hg
    have hk : 0 < Nat.card N := Nat.card_pos
    have hb : 0 < Nat.card P := Nat.card_pos
    have div : q / Nat.card N = Nat.card P := by rw [← eq, Nat.mul_div_cancel_left _ hk]
    let k : Fin (q+1) := ⟨Nat.card N, by have := (Nat.le_mul_of_pos_right (Nat.card N) hb).trans eq.le; omega⟩
    let i : I := ⟨k, hk, div.symm ▸ hb, div.symm ▸ eq, div.symm ▸ cop⟩
    let x : O k.val := ⟨Quotient.mk _ (FiniteGrp.of N), FiniteGrp.of N, ⟨rfl, inferInstanceAs (Group.IsSolvable N), hnil⟩, rfl⟩
    let y : O (q/k.val) := ⟨Quotient.mk _ (FiniteGrp.of P), FiniteGrp.of P, ⟨div.symm, inferInstanceAs (Group.IsSolvable P), hpnil⟩, rfl⟩
    let fn : N ≃* K x := ((inducedFunctor FiniteGrp.toGrp).mapIso (Classical.choice (Quotient.exact (rep x)))).groupIsoToMulEquiv.symm
    let fp : P ≃* K y := ((inducedFunctor FiniteGrp.toGrp).mapIso (Classical.choice (Quotient.exact (rep y)))).groupIsoToMulEquiv.symm
    let a : P →* MulAut N := N.normalizerMonoidHom.comp (Subgroup.inclusion (N.normalizer_eq_top ▸ le_top))
    let e := (SemidirectProduct.mulEquivSubgroup comp).symm.trans (SemidirectProduct.congr' fn fp)
    refine ⟨⟨i, ⟨x,y⟩, ⟨MonoidHom.comp (MulAut.congr fn) (a.comp fp.symm), by simpa only [← Group.rank_congr fn, ← Group.rank_congr fp, ← Nat.card_congr fn.toEquiv] using rank⟩⟩, Quotient.sound ?_⟩
    exact ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp) e.symm.toGrpIso⟩
  have bound (i : I) : Nat.card (T i) ≤ L q * 2^(r*r*d) := by
    let k := i.val.val
    let l := q/k
    have hk : 0 < k := i.property.1
    have hl : 0 < l := i.property.2.1
    have eq : k*l = q := i.property.2.2.1
    let _ := Fintype.ofFinite (O k × O l)
    have cnt (x : O k × O l) : Nat.card {a : K x.2 →* MulAut (K x.1) // Nat.card (K x.1) ^ (Group.rank (K x.1) * Group.rank (K x.2)) ≤ 2^(r*r*d)} ≤ 2^(r*r*d) := by
      by_cases hd : Nat.card (K x.1) ^ (Group.rank (K x.1) * Group.rank (K x.2)) ≤ 2^(r*r*d)
      · apply (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans
        apply (rank_hom_count (K x.2) (MulAut (K x.1))).trans
        have inj : Function.Injective (fun a : MulAut (K x.1) => a.toMonoidHom) := by
          intro a b h
          exact DFunLike.ext' (congrArg (fun f : K x.1 →* K x.1 => (f : K x.1 → K x.1)) h)
        let _ : Finite (K x.1 →* K x.1) := Finite.of_injective (fun f : K x.1 →* K x.1 => (f : K x.1 → K x.1)) (fun _ _ h => DFunLike.ext' h)
        have ba := (Nat.card_le_card_of_injective _ inj).trans (rank_hom_count (K x.1) (K x.1))
        exact (Nat.pow_le_pow_left ba _).trans ((pow_mul ..).symm.le.trans hd)
      · let _ : IsEmpty {a : K x.2 →* MulAut (K x.1) // Nat.card (K x.1) ^ (Group.rank (K x.1) * Group.rank (K x.2)) ≤ 2^(r*r*d)} := ⟨fun a => hd a.property⟩
        simp
    calc
      _ = ∑ x : O k × O l, Nat.card {a : K x.2 →* MulAut (K x.1) // Nat.card (K x.1) ^ (Group.rank (K x.1) * Group.rank (K x.2)) ≤ 2^(r*r*d)} := Nat.card_sigma
      _ ≤ ∑ _ : O k × O l, 2^(r*r*d) := Finset.sum_le_sum fun x _ => cnt x
      _ = (Nat.card (O k) * Nat.card (O l)) * 2^(r*r*d) := by simp [← Nat.card_eq_fintype_card, Nat.card_prod]
      _ ≤ _ := Nat.mul_le_mul_right _ (by rw [← eq, factor hk hl i.property.2.2.2]; exact Nat.mul_le_mul (nilpotent_bound k) (nilpotent_bound l))
  let _ := Fintype.ofFinite I
  have ni : Nat.card I ≤ 2^r := (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans (by simpa using hr : Nat.card (Fin (q+1)) ≤ 2^r)
  calc
    _ ≤ (Set.range decode).ncard := Set.ncard_le_ncard cover (Set.finite_range _)
    _ ≤ Nat.card ((i : I) × T i) := Nat.card_le_card_of_surjective _ (Set.rangeFactorization_surjective (f := decode))
    _ = ∑ i : I, Nat.card (T i) := Nat.card_sigma
    _ ≤ ∑ _ : I, L q * 2^(r*r*d) := Finset.sum_le_sum fun i _ => bound i
    _ = Nat.card I * (L q * 2^(r*r*d)) := by simp [Nat.card_eq_fintype_card]
    _ ≤ 2^r * (L q * 2^(r*r*d)) := Nat.mul_le_mul_right _ ni
    _ = 2^(r+r*r*d) * L q := by rw [pow_add]; ac_rfl
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (by nlinarith [Nat.mul_le_mul_left r hd, Nat.zero_le (r*d)] : r+r*r*d ≤ d*(r+1)^2))

/-- A rank bound on either factor controls split extensions of two nilpotent Hall factors. -/
theorem bounded_rank_hall_bound {q r d : ℕ} (hd : 0 < d) (hr : q < 2^r) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = q ∧ Group.IsSolvable G ∧ (∃ N P : Subgroup G, N.Normal ∧ N.IsComplement' P ∧ Group.IsNilpotent N ∧ Group.IsNilpotent P ∧ min (Group.rank N) (Group.rank P) ≤ d ∧ (Nat.card N).Coprime (Nat.card P))}).ncard ≤
      2^(d*(r+1)^2) * ∏ p ∈ q.primeFactors, g (p^q.factorization p) := by
  classical
  apply le_trans _ (hall_action_bound hd hr)
  apply Set.ncard_le_ncard _ ((finite_classes q).subset (Set.image_mono (fun _ h => h.1)))
  rintro _ ⟨G, ⟨hg, hs, N, P, hn, comp, hnil, hpnil, hmin, cop⟩, rfl⟩
  refine ⟨G, ⟨hg, hs, N, P, hn, comp, hnil, hpnil, ?_, cop⟩, rfl⟩
  have rank_le (H : Subgroup G) : Group.rank H ≤ r := by
    let _ := Fintype.ofFinite H
    obtain ⟨t, _, ht, size⟩ := thin_generators (Finset.univ : Finset H)
    rw [Finset.coe_univ, Subgroup.closure_univ] at ht size
    rw [Subgroup.card_top] at size
    have hcard : Nat.card H ≤ Nat.card G := Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    exact (Group.rank_le ht).trans ((Nat.le_log_of_pow_le (by decide) size).trans
      (Nat.log_lt_of_lt_pow Nat.card_pos.ne' (hcard.trans_lt (hg ▸ hr))).le)
  have prod : Group.rank N * Group.rank P ≤ r*d := by
    rcases min_le_iff.mp hmin with h | h
    · exact (Nat.mul_le_mul h (rank_le P)).trans (Nat.mul_comm ..).le
    · exact Nat.mul_le_mul (rank_le N) h
  have nk : Nat.card N ≤ 2^r :=
    (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective : Nat.card N ≤ Nat.card G).trans (hg ▸ hr.le)
  calc
    _ ≤ (2^r)^(Group.rank N * Group.rank P) := Nat.pow_le_pow_left nk _
    _ ≤ (2^r)^(r*d) := Nat.pow_le_pow_right (by positivity) prod
    _ = _ := by rw [← pow_mul, Nat.mul_assoc]

/-- For a split diagonal action, multiplicities of the one-dimensional actions
determine the middle group up to isomorphism. Both bounds count fixed factors. -/
theorem diagonal_class_bound (C H : FiniteGrp.{0}) (t : ℕ) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | ∃ (χ : Fin t → H →* MulAut C) (a : H →* MulAut (Fin t → C)),
        (∀ h v i, a h v i = χ i h (v i)) ∧
        Nonempty (G ≃* SemidirectProduct (Fin t → C) H a)}).ncard ≤
      min ((Nat.card (H →* MulAut C))^t) ((t+1)^(Nat.card (H →* MulAut C))) := by
  classical
  let A := H →* MulAut C
  let _ : Finite (MulAut C) := Finite.of_injective (fun a : MulAut C => (a : C → C))
    (fun _ _ h => DFunLike.ext' h)
  let _ : Finite A := Finite.of_injective (fun f : A => (f : H → MulAut C))
    (fun _ _ h => DFunLike.ext' h)
  let S := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | ∃ (χ : Fin t → A) (a : H →* MulAut (Fin t → C)),
      (∀ h v i, a h v i = χ i h (v i)) ∧ Nonempty (G ≃* SemidirectProduct (Fin t → C) H a)}
  let G (x : S) : FiniteGrp.{0} := x.property.choose
  have rep (x : S) : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (G x) = x.val := x.property.choose_spec.2
  choose χ a diag iso using fun x : S => x.property.choose_spec.1
  have same (x y : S) (e : Fin t ≃ Fin t) (matchChar : ∀ i, χ y (e i) = χ x i) : x = y := by
    let perm : (Fin t → C) ≃* (Fin t → C) :=
      { Equiv.arrowCongr e (Equiv.refl C) with map_mul' := fun _ _ => rfl }
    have commute (h : H) : (a x h).trans perm = perm.trans (a y h) := by
      ext v j
      change a x h v (e.symm j) = a y h (perm v) j
      rw [diag x, diag y, ← matchChar (e.symm j), e.apply_symm_apply]
      rfl
    let mid := SemidirectProduct.congr perm (MulEquiv.refl H) commute
    let giso := (iso x).some.trans (mid.trans (iso y).some.symm)
    apply Subtype.ext
    rw [← rep x, ← rep y]
    exact Quotient.sound ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp) giso.toGrpIso⟩
  let count (x : S) (b : A) : Fin (t+1) :=
    ⟨Nat.card {i // χ x i = b}, Nat.lt_succ_of_le (by
      simpa using Nat.card_le_card_of_injective (fun i : {i // χ x i = b} => i.val) Subtype.val_injective)⟩
  have inj : Function.Injective count := by
    intro x y h
    have eq (b : A) : Nat.card {i // χ x i = b} = Nat.card {i // χ y i = b} :=
      congrArg Fin.val (congrFun h b)
    let fibers (b : A) : {i // χ x i = b} ≃ {i // χ y i = b} :=
      (Finite.equivFinOfCardEq (eq b)).trans (Finite.equivFinOfCardEq rfl).symm
    exact same x y (Equiv.ofFiberEquiv fibers) (Equiv.ofFiberEquiv_map fibers)
  change Nat.card S ≤ _
  apply le_min
  · have hi : Function.Injective χ := fun {x y} h => same x y (Equiv.refl _) (fun i => congrFun h.symm i)
    simpa [Nat.card_fun, A] using Nat.card_le_card_of_injective χ hi
  · simpa [Nat.card_fun, A] using Nat.card_le_card_of_injective count inj

/-- With a fixed cyclic coordinate group and dimension, sum the diagonal bound
over all nilpotent complements of the specified coprime order. -/
theorem diagonal_hall_bound (C : FiniteGrp.{0}) [IsCyclic C] (t l r : ℕ)
    (hl : 0 < l) (cop : l.Coprime (Nat.card C^t)) (hr : Nat.card C^t*l < 2^r) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | ∃ H : FiniteGrp.{0}, Nat.card H = l ∧ Group.IsSolvable H ∧ Group.IsNilpotent H ∧
        ∃ (χ : Fin t → H →* MulAut C) (a : H →* MulAut (Fin t → C)),
          (∀ h v i, a h v i = χ i h (v i)) ∧ Nonempty (G ≃* SemidirectProduct (Fin t → C) H a)}).ncard ≤
      2^(r*r) * ∏ b ∈ (Nat.card C^t*l).primeFactors, g (b^(Nat.card C^t*l).factorization b) := by
  classical
  let k := Nat.card C^t
  have hk : 0 < k := pow_pos Nat.card_pos _
  let O := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {H : FiniteGrp.{0} | Nat.card H = l ∧ Group.IsSolvable H ∧ Group.IsNilpotent H}
  let K (x : O) : FiniteGrp.{0} := x.property.choose
  have rep (x : O) : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (K x) = x.val :=
    x.property.choose_spec.2
  have order (x : O) : Nat.card (K x) = l := x.property.choose_spec.1.1
  let _ : Finite O := ((finite_classes l).subset (Set.image_mono (fun _ h => h.1))).to_subtype
  let _ := Fintype.ofFinite O
  let S (H : FiniteGrp.{0}) := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | ∃ (χ : Fin t → H →* MulAut C) (a : H →* MulAut (Fin t → C)),
      (∀ h v i, a h v i = χ i h (v i)) ∧ Nonempty (G ≃* SemidirectProduct (Fin t → C) H a)}
  have finite (x : O) : (S (K x)).Finite := (finite_classes (k*l)).subset (Set.image_mono (by
    rintro G ⟨χ,a,_,⟨e⟩⟩
    exact (Nat.card_congr e.toEquiv).trans (by simp [SemidirectProduct.card, Nat.card_fun, k, order])))
  have bound (x : O) : (S (K x)).ncard ≤ 2^(r*r) := by
    apply (diagonal_class_bound C (K x) t).trans
    apply (min_le_left ..).trans
    let _ : Finite (MulAut C) := Finite.of_injective (fun a : MulAut C => (a : C → C))
      (fun _ _ h => DFunLike.ext' h)
    have h := hom_count (K x) (MulAut C)
    rw [IsCyclic.card_mulAut C, order] at h
    have hlr : l < 2^r := (Nat.le_mul_of_pos_left l hk).trans_lt hr
    calc
      _ ≤ ((Nat.card C)^(Nat.log 2 l))^t :=
        Nat.pow_le_pow_left (h.trans (Nat.pow_le_pow_left (Nat.totient_le _) _)) _
      _ = k^(Nat.log 2 l) := by dsimp [k]; rw [← pow_mul, Nat.mul_comm, pow_mul]
      _ ≤ (2^r)^(Nat.log 2 l) := Nat.pow_le_pow_left ((Nat.le_mul_of_pos_right k hl).trans hr.le) _
      _ ≤ (2^r)^r := Nat.pow_le_pow_right (by positivity) (Nat.log_lt_of_lt_pow hl.ne' hlr).le
      _ = _ := (pow_mul ..).symm
  have sub : l.primeFactors ⊆ (k*l).primeFactors := by
    rw [Nat.primeFactors_mul hk.ne' hl.ne']
    exact Finset.subset_union_right
  have parts : O.ncard ≤ ∏ b ∈ (k*l).primeFactors, g (b^(k*l).factorization b) := by
    apply (nilpotent_bound l).trans
    calc
      _ = ∏ b ∈ l.primeFactors, g (b^(k*l).factorization b) := by
        apply Finset.prod_congr rfl
        intro b hb
        have nd : ¬ b ∣ k := fun hh => (Nat.prime_of_mem_primeFactors hb).not_dvd_one
          (cop ▸ Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hb) hh)
        rw [Nat.factorization_mul hk.ne' hl.ne', Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd nd, zero_add]
      _ ≤ _ := Finset.prod_le_prod_of_subset_of_one_le' sub fun b hb _ =>
        positive_count (pow_pos (Nat.prime_of_mem_primeFactors hb).pos _)
  apply le_trans (Set.ncard_le_ncard (t := ⋃ x : O, S (K x)) ?_ (Set.finite_iUnion finite)) ?_
  · rintro _ ⟨G, ⟨H, hH, hs, hn, χ, a, diag, ⟨e⟩⟩, rfl⟩
    let x : O := ⟨Quotient.mk _ H, H, ⟨hH, hs, hn⟩, rfl⟩
    let u : K x ≃* H := ((inducedFunctor FiniteGrp.toGrp).mapIso (Classical.choice (Quotient.exact (rep x)))).groupIsoToMulEquiv
    let mid := SemidirectProduct.congr (φ₁ := a) (φ₂ := a.comp u.toMonoidHom) (MulEquiv.refl _) u.symm
      (fun h => by ext v; simp)
    exact Set.mem_iUnion.mpr ⟨x, G, ⟨fun j => (χ j).comp u.toMonoidHom, a.comp u.toMonoidHom,
      fun h v j => diag (u h) v j, ⟨e.trans mid⟩⟩, rfl⟩
  · calc
      _ ≤ ∑ x : O, (S (K x)).ncard := Set.ncard_iUnion_le_of_fintype _
      _ ≤ ∑ _ : O, 2^(r*r) := Finset.sum_le_sum fun x _ => bound x
      _ = 2^(r*r)*O.ncard := by simp [← Nat.card_eq_fintype_card, Nat.mul_comm]
      _ ≤ _ := Nat.mul_le_mul_left _ parts

/-- Sum the diagonal estimate over all nontrivial cyclic coordinate groups and positive dimensions. -/
theorem diagonal_hall_union {q r : ℕ} (hr : q < 2^r) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = q ∧ (∃ c t : ℕ, 0 < t ∧ ∃ H : FiniteGrp.{0}, Group.IsSolvable H ∧ Group.IsNilpotent H ∧
        (Nat.card H).Coprime ((c+2)^t) ∧
        ∃ (χ : Fin t → H →* MulAut (Multiplicative (ZMod (c+2))))
          (a : H →* MulAut (Fin t → Multiplicative (ZMod (c+2)))),
          (∀ h v i, a h v i = χ i h (v i)) ∧ Nonempty (G ≃* SemidirectProduct _ H a))}).ncard ≤
      2^((r+1)^2) * ∏ b ∈ q.primeFactors, g (b^q.factorization b) := by
  classical
  let J := Fin (q+1) × Fin (q+1)
  let k (j : J) := (j.1.val+2)^j.2.val
  let I := {j : J // 0 < q/k j ∧ (q/k j).Coprime (k j) ∧ k j*(q/k j) = q}
  let C (j : J) := FiniteGrp.of (Multiplicative (ZMod (j.1.val+2)))
  let (j : J) : IsCyclic (C j) := inferInstanceAs (IsCyclic (Multiplicative (ZMod (j.1.val+2))))
  have card (j : J) : Nat.card (C j) = j.1.val+2 := by
    change Nat.card (ZMod (j.1.val+2)) = _
    exact Nat.card_zmod _
  let S (i : I) := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | ∃ H : FiniteGrp.{0}, Nat.card H = q/k i.val ∧ Group.IsSolvable H ∧ Group.IsNilpotent H ∧
      ∃ (χ : Fin i.val.2.val → H →* MulAut (C i.val)) (a : H →* MulAut (Fin i.val.2.val → C i.val)),
        (∀ h v j, a h v j = χ j h (v j)) ∧ Nonempty (G ≃* SemidirectProduct _ H a)}
  let L := ∏ b ∈ q.primeFactors, g (b^q.factorization b)
  have cardpow (i : I) : Nat.card (C i.val)^i.val.2.val = k i.val := by rw [card]
  have bound (i : I) : (S i).ncard ≤ 2^(r*r)*L := by
    have eq := (congrArg (· * (q/k i.val)) (cardpow i)).trans i.property.2.2
    have h := diagonal_hall_bound (C i.val) i.val.2.val (q/k i.val) r i.property.1
      ((cardpow i).symm ▸ i.property.2.1) (eq.trans_lt hr)
    simpa only [eq] using h
  have finite (i : I) : (S i).Finite := (finite_classes q).subset (Set.image_mono (by
    rintro G ⟨H,hH,_,_,_,a,_,⟨e⟩⟩
    exact (Nat.card_congr e.toEquiv).trans (by
      rw [SemidirectProduct.card, Nat.card_fun, Nat.card_fin, cardpow, hH]; exact i.property.2.2)))
  apply le_trans (Set.ncard_le_ncard (t := ⋃ i : I, S i) ?_ (Set.finite_iUnion finite)) ?_
  · rintro _ ⟨G, ⟨hg,c,t,ht,H,hs,hn,cop,χ,a,diag,⟨e⟩⟩, rfl⟩
    have eq : (c+2)^t * Nat.card H = q := by
      have h := (Nat.card_congr e.toEquiv).symm.trans hg
      simpa [SemidirectProduct.card, Nat.card_fun, Nat.card_zmod] using h
    have hpow : 0 < (c+2)^t := by positivity
    have leq := (Nat.le_mul_of_pos_right ((c+2)^t) Nat.card_pos).trans eq.le
    have ct : c+2 ≤ (c+2)^t := by simpa using Nat.pow_le_pow_right (by omega : 0 < c+2) ht
    have tt : t < (c+2)^t := Nat.lt_pow_self (by omega)
    let j : J := (⟨c, by omega⟩, ⟨t, by omega⟩)
    have div : q/k j = Nat.card H := by change q/(c+2)^t = _; rw [← eq, Nat.mul_div_cancel_left _ hpow]
    let i : I := ⟨j, div.symm ▸ Nat.card_pos, div.symm ▸ cop, div.symm ▸ eq⟩
    exact Set.mem_iUnion.mpr ⟨i, G, ⟨H,div.symm,hs,hn,χ,a,diag,⟨e⟩⟩,rfl⟩
  · let _ := Fintype.ofFinite I
    have ni : Nat.card I ≤ 2^(r+r) := by
      apply (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans
      simpa [J, Nat.card_prod, pow_add] using Nat.mul_le_mul (show q+1 ≤ 2^r from hr) hr
    calc
      _ ≤ ∑ i : I, (S i).ncard := Set.ncard_iUnion_le_of_fintype _
      _ ≤ ∑ _ : I, 2^(r*r)*L := Finset.sum_le_sum fun i _ => bound i
      _ = Nat.card I * (2^(r*r)*L) := by simp [Nat.card_eq_fintype_card]
      _ ≤ 2^(r+r) * (2^(r*r)*L) := Nat.mul_le_mul_right _ ni
      _ = 2^((r+r)+r*r)*L := by rw [pow_add (2:ℕ) (r+r) (r*r)]; ac_rfl
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (by nlinarith : (r+r)+r*r ≤ (r+1)^2))

theorem main : H1 → H2 → OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1_H2_R1_H3_R2.H2 := by
  classical
  rintro ⟨A, hA⟩ ⟨B, hB⟩
  let D := max 3 (max A B)
  have h3 : 3 ≤ D := le_max_left ..
  have h1 : 1 ≤ D := by omega
  refine ⟨D+3, fun q r odd hr => ?_⟩
  by_cases hpp : IsPrimePow q
  · exact (prime_power_count hpp).trans (Nat.le_mul_of_pos_left _ (Nat.pow_pos (by decide)))
  by_cases htwo : ∃ p l a : ℕ, p.Prime ∧ l.Prime ∧ p ≠ l ∧ (¬ p ∣ l-1 ∨ ∀ i, 0 < i → i < a → ¬ Nat.ModEq l (p^i) 1) ∧ 0 < a ∧ q = p^a*l
  · obtain ⟨p, l, a, hp, hl, hne, haut, ha, rfl⟩ := htwo
    have sub : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
        {G : FiniteGrp.{0} | Nat.card G = p^a*l ∧ Group.IsSolvable G} ⊆
        Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
        {G : FiniteGrp.{0} | Nat.card G = p^a*l} := by
      rintro _ ⟨G, ⟨hG, _⟩, rfl⟩
      exact ⟨G, hG, rfl⟩
    apply (Set.ncard_le_ncard sub (finite_classes _)).trans
    apply (two_prime_bound hp hl hne haut ha hr).trans
    apply Nat.mul_le_mul_right
    apply Nat.pow_le_pow_right (by decide)
    exact Nat.le_mul_of_pos_left _ (by omega)
  let S (P : FiniteGrp.{0} → Prop) := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | Nat.card G = q ∧ Group.IsSolvable G ∧ P G}
  let U₁ (G : FiniteGrp.{0}) := (∃ N P : Subgroup G, (N.Normal ∨ P.Normal) ∧ N.IsComplement' P ∧ IsCyclic P ∧ Group.IsNilpotent N ∧ (Nat.card N).Coprime (Nat.card P))
  let U₂ (G : FiniteGrp.{0}) := (∃ c t : ℕ, 0 < t ∧ ∃ H : FiniteGrp.{0}, Group.IsSolvable H ∧ Group.IsNilpotent H ∧
        (Nat.card H).Coprime ((c+2)^t) ∧
        ∃ (χ : Fin t → H →* MulAut (Multiplicative (ZMod (c+2))))
          (a : H →* MulAut (Fin t → Multiplicative (ZMod (c+2)))),
          (∀ h v i, a h v i = χ i h (v i)) ∧ Nonempty (G ≃* SemidirectProduct _ H a))
  let U (G : FiniteGrp.{0}) := U₁ G ∨ U₂ G
  let V (G : FiniteGrp.{0}) := (∃ N P : Subgroup G, N.Normal ∧ N.IsComplement' P ∧ Group.IsNilpotent N ∧ Group.IsNilpotent P ∧ Nat.card N ^ (Group.rank N * Group.rank P) ≤ 2^(r*r*2) ∧ (Nat.card N).Coprime (Nat.card P))
  let N (G : FiniteGrp.{0}) := U G ∨ V G
  let Z (G : FiniteGrp.{0}) := IsZGroup G
  let C (G : FiniteGrp.{0}) := ∀ p : ℕ, p.Prime → ∀ P : Sylow p G, IsMulCommutative P
  let T (G : FiniteGrp.{0}) := ∃ p : ℕ, p.Prime ∧ ∃ P : Sylow p G, ¬ IsMulCommutative P
  let F (G : FiniteGrp.{0}) := ((∃ p l a : ℕ, p.Prime ∧ l.Prime ∧ p ≠ l ∧ 0 < a ∧ q = p^a*l) ∧
        ∀ p l a : ℕ, (p.Prime ∧ l.Prime ∧ p ≠ l ∧ 0 < a ∧ q = p^a*l) →
          ((∃ N : Subgroup G, N.Normal ∧ Nat.card N = p^a) ∨ Nat.card (Sylow l G) = 1))
  let X (G : FiniteGrp.{0}) := ¬ F G ∧ ¬ N G ∧ ¬ Z G ∧ C G
  let Y (G : FiniteGrp.{0}) := ¬ F G ∧ ¬ N G ∧ T G
  have union_eq : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = q ∧ Group.IsSolvable G} =
      S F ∪ ((S N ∪ S Z) ∪ (S X ∪ S Y)) := by
    ext c
    constructor
    · rintro ⟨G, ⟨hq, hs⟩, rfl⟩
      by_cases hf : F G
      · exact Or.inl ⟨G, ⟨hq, hs, hf⟩, rfl⟩
      right
      by_cases hn : N G
      · exact Or.inl (Or.inl ⟨G, ⟨hq, hs, hn⟩, rfl⟩)
      by_cases hz : Z G
      · exact Or.inl (Or.inr ⟨G, ⟨hq, hs, hz⟩, rfl⟩)
      by_cases hc : C G
      · exact Or.inr (Or.inl ⟨G, ⟨hq, hs, hf, hn, hz, hc⟩, rfl⟩)
      · have ht : T G := by simpa [C, T] using hc
        exact Or.inr (Or.inr ⟨G, ⟨hq, hs, hf, hn, ht⟩, rfl⟩)
    · rintro (⟨G, ⟨hq, hs, _⟩, rfl⟩ | ((⟨G, ⟨hq, hs, _⟩, rfl⟩ | ⟨G, ⟨hq, hs, _⟩, rfl⟩) | (⟨G, ⟨hq, hs, _⟩, rfl⟩ | ⟨G, ⟨hq, hs, _⟩, rfl⟩))) <;>
        exact ⟨G, ⟨hq, hs⟩, rfl⟩
  let m := (r+1)^2
  let L := ∏ p ∈ q.primeFactors, g (p^q.factorization p)
  have posL : 0 < L := Finset.prod_pos fun p hp =>
    positive_count (pow_pos (Nat.prime_of_mem_primeFactors hp).pos _)
  have mono (a b : ℕ) (hab : a ≤ b) : 2^(a*m)*L ≤ 2^(b*m)*L :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ hab))
  have za : (S Z).ncard ≤ 2^(D*m)*L := by
    calc
      _ ≤ q := cyclic_sylows_bound q
      _ ≤ 2^r := hr.le
      _ ≤ 2^(1*m) := Nat.pow_le_pow_right (by decide) (by dsimp [m]; nlinarith [Nat.zero_le (r^2)])
      _ ≤ 2^(1*m)*L := Nat.le_mul_of_pos_right _ posL
      _ ≤ _ := mono 1 D h1
  have aa : (S X).ncard ≤ 2^(D*m)*L := by
    by_cases h : ∃ p l a : ℕ, p.Prime ∧ l.Prime ∧ p ≠ l ∧ 0 < a ∧ q = p^a*l
    · have empty : S X = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro _ ⟨G, ⟨hg, _, hf, _, _, hc⟩, _⟩
        apply hf
        refine ⟨h, ?_⟩
        rintro p l a ⟨hp, hl, hne, _, hq⟩
        let _ : Fact p.Prime := ⟨hp⟩
        let P : Sylow p G := default
        let _ := hc p hp P
        exact normal_hall_of_abelian hp hl hne G (hg.trans hq) P
      simp [empty]
    · apply le_trans _ (mono _ D ((le_max_left A B).trans (le_max_right ..)))
      apply le_trans _ (hA q r odd hr hpp h)
      apply Set.ncard_le_ncard _ ((finite_classes q).subset (Set.image_mono (fun _ h => h.1)))
      rintro _ ⟨G, ⟨hg, hs, _, hn, hz, hc⟩, rfl⟩
      exact ⟨G, ⟨hg, hs, hn, hz, hc⟩, rfl⟩
  have bb := (hB q r odd hr hpp htwo).trans (mono _ D ((le_max_right A B).trans (le_max_right ..)))
  have nn : (S N).ncard ≤ 2^(D*m)*L := by
    have cover : S N = S U ∪ S V := by
      ext c
      constructor
      · rintro ⟨G, ⟨hg, hs, hu | hv⟩, rfl⟩
        · exact Or.inl ⟨G, ⟨hg, hs, hu⟩, rfl⟩
        · exact Or.inr ⟨G, ⟨hg, hs, hv⟩, rfl⟩
      · rintro (⟨G, ⟨hg, hs, hu⟩, rfl⟩ | ⟨G, ⟨hg, hs, hv⟩, rfl⟩)
        · exact ⟨G, ⟨hg, hs, Or.inl hu⟩, rfl⟩
        · exact ⟨G, ⟨hg, hs, Or.inr hv⟩, rfl⟩
    have hu : (S U).ncard ≤ 2^(2*m)*L := by
      have sub : S U ⊆ S U₁ ∪ S U₂ := by
        rintro _ ⟨G, ⟨hg,hs,h | h⟩,rfl⟩
        · exact Or.inl ⟨G,⟨hg,hs,h⟩,rfl⟩
        · exact Or.inr ⟨G,⟨hg,hs,h⟩,rfl⟩
      have fin (F : FiniteGrp.{0} → Prop) : (S F).Finite :=
        (finite_classes q).subset (Set.image_mono (fun _ h => h.1))
      have h₂ : (S U₂).ncard ≤ 2^m*L := by
        apply le_trans _ (diagonal_hall_union hr)
        apply Set.ncard_le_ncard _ ((finite_classes q).subset (Set.image_mono (fun _ h => h.1)))
        rintro _ ⟨G, ⟨hg,_,h⟩,rfl⟩
        exact ⟨G,⟨hg,h⟩,rfl⟩
      calc
        _ ≤ (S U₁ ∪ S U₂).ncard := Set.ncard_le_ncard sub ((fin _).union (fin _))
        _ ≤ (S U₁).ncard + (S U₂).ncard := Set.ncard_union_le _ _
        _ ≤ 2^m*L + 2^m*L := Nat.add_le_add (cyclic_nilpotent_hall_bound hr) h₂
        _ = 2^(m+1)*L := by rw [pow_succ]; ring
        _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide)
          (by have hm : 0 < m := Nat.pow_pos (Nat.succ_pos r); omega : m+1 ≤ 2*m))
    have hv : (S V).ncard ≤ 2^(2*m)*L := hall_action_bound (by decide) hr
    have hm : 0 < m := Nat.pow_pos (Nat.succ_pos r)
    rw [cover]
    calc
      _ ≤ (S U).ncard + (S V).ncard := Set.ncard_union_le _ _
      _ ≤ 2^(2*m)*L + 2^(2*m)*L := Nat.add_le_add hu hv
      _ = 2^(2*m+1)*L := by rw [pow_succ]; ring
      _ ≤ 2^(3*m)*L := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (by omega))
      _ ≤ _ := mono _ _ h3
  have ff : (S F).ncard ≤ 2^(D*m)*L := by
    by_cases h : ∃ p l a : ℕ, p.Prime ∧ l.Prime ∧ p ≠ l ∧ 0 < a ∧ q = p^a*l
    · obtain ⟨p, l, a, hshape⟩ := h
      obtain ⟨hp, hl, hne, ha, hq⟩ := hshape
      have sub : S F ⊆ Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
          {G : FiniteGrp.{0} | Nat.card G = q ∧ ((∃ N : Subgroup G, N.Normal ∧ Nat.card N = p^a) ∨ Nat.card (Sylow l G) = 1)} := by
        rintro _ ⟨G, ⟨hc, _, hf⟩, rfl⟩
        exact ⟨G, ⟨hc, hf.2 p l a ⟨hp, hl, hne, ha, hq⟩⟩, rfl⟩
      apply (Set.ncard_le_ncard sub ((finite_classes q).subset
        (Set.image_mono (fun _ h => h.1)))).trans
      apply le_trans _ (mono 1 D h1)
      subst q
      simpa [m, L] using normal_hall_bound hp hl hne ha hr
    · have he : S F = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro _ ⟨G, ⟨_, _, hf⟩, _⟩
        exact h hf.1
      simp [he]
  have cost : 5 ≤ 2^(3*m) := by
    have hm : 1 ≤ m := Nat.pow_pos (Nat.succ_pos r)
    exact (by decide : 5 ≤ 2^3).trans (Nat.pow_le_pow_right (by decide) (by omega))
  rw [union_eq]
  calc
    _ ≤ (S F).ncard + ((S N ∪ S Z) ∪ (S X ∪ S Y)).ncard := Set.ncard_union_le _ _
    _ ≤ (S F).ncard + ((S N ∪ S Z).ncard + (S X ∪ S Y).ncard) := Nat.add_le_add_left (Set.ncard_union_le _ _) _
    _ ≤ (S F).ncard + (((S N).ncard + (S Z).ncard) + ((S X).ncard + (S Y).ncard)) :=
      Nat.add_le_add_left (Nat.add_le_add (Set.ncard_union_le _ _) (Set.ncard_union_le _ _)) _
    _ ≤ 2^(D*m)*L + ((2^(D*m)*L + 2^(D*m)*L) + (2^(D*m)*L + 2^(D*m)*L)) :=
      Nat.add_le_add ff (Nat.add_le_add (Nat.add_le_add nn za) (Nat.add_le_add aa bb))
    _ = 2^(D*m)*L*5 := by omega
    _ ≤ 2^(D*m)*L*2^(3*m) := Nat.mul_le_mul_left _ cost
    _ = 2^((D+3)*m)*L := by rw [add_mul, pow_add]; ac_rfl

end OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1_H2_R1_H3_R2_H2_R1
