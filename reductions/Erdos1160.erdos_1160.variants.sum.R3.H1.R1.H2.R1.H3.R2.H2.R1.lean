import OMAReductions.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1_H2_R1_H3_R2
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.MonoidAlgebra.Module

import Mathlib.Algebra.Module.ZMod
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
      {G : FiniteGrp.{0} | Nat.card G = q ∧ Group.IsSolvable G ∧ ¬ ((((∃ N P : Subgroup G, (N.Normal ∨ P.Normal) ∧ N.IsComplement' P ∧ IsCyclic P ∧ Group.IsNilpotent N ∧ (Nat.card N).Coprime (Nat.card P)) ∨ (∃ c t : ℕ, 0 < t ∧ ∃ H : FiniteGrp.{0}, Group.IsSolvable H ∧ Group.IsNilpotent H ∧
        (Nat.card H).Coprime ((c+2)^t) ∧
        ∃ (χ : Fin t → H →* MulAut (Multiplicative (ZMod (c+2))))
          (a : H →* MulAut (Fin t → Multiplicative (ZMod (c+2)))),
          ((IsPrimePow (c+2) ∧ (c+2).Coprime (Nat.card H)) ∨ (∀ h v i, a h v i = χ i h (v i))) ∧ Nonempty (G ≃* SemidirectProduct _ H a))) ∨
        (∃ N P : Subgroup G, N.Normal ∧ N.IsComplement' P ∧ Group.IsNilpotent N ∧ Group.IsNilpotent P ∧ Nat.card N ^ (Group.rank N * Group.rank P) ≤ 2^(r*r*2) ∧ (Nat.card N).Coprime (Nat.card P))) ∨
        (∃ p k a b : ℕ, p.Prime ∧ 0 < b ∧ ∃ H : FiniteGrp.{0}, Group.IsSolvable H ∧ Group.IsNilpotent H ∧ ¬ p ∣ Nat.card H ∧ ∃ f : H →* MulAut (Multiplicative ((Fin a → ZMod p) × (Fin b → ZMod (p^(k+2))))), Nonempty (G ≃* SemidirectProduct _ H f))) ∧ ¬ IsZGroup G ∧
        (∀ p : ℕ, p.Prime → ∀ P : Sylow p G, IsMulCommutative P)}).ncard ≤
      2^(E*(r+1)^2) * ∏ p ∈ q.primeFactors, g (p^q.factorization p)

def H2 : Prop :=
  ∃ E : ℕ, ∀ q r : ℕ, Odd q → q < 2^r → ¬ IsPrimePow q →
    ¬ (∃ p l a : ℕ, p.Prime ∧ l.Prime ∧ p ≠ l ∧ (¬ p ∣ l-1 ∨ ∀ i, 0 < i → i < a → ¬ Nat.ModEq l (p^i) 1) ∧ 0 < a ∧ q = p^a*l) →
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = q ∧ Group.IsSolvable G ∧ ¬ ((∃ p l a : ℕ, p.Prime ∧ l.Prime ∧ p ≠ l ∧ 0 < a ∧ q = p^a*l) ∧
        ∀ p l a : ℕ, (p.Prime ∧ l.Prime ∧ p ≠ l ∧ 0 < a ∧ q = p^a*l) →
          ((∃ N : Subgroup G, N.Normal ∧ Nat.card N = p^a) ∨ Nat.card (Sylow l G) = 1)) ∧ ¬ ((((∃ N P : Subgroup G, (N.Normal ∨ P.Normal) ∧ N.IsComplement' P ∧ IsCyclic P ∧ Group.IsNilpotent N ∧ (Nat.card N).Coprime (Nat.card P)) ∨ (∃ c t : ℕ, 0 < t ∧ ∃ H : FiniteGrp.{0}, Group.IsSolvable H ∧ Group.IsNilpotent H ∧
        (Nat.card H).Coprime ((c+2)^t) ∧
        ∃ (χ : Fin t → H →* MulAut (Multiplicative (ZMod (c+2))))
          (a : H →* MulAut (Fin t → Multiplicative (ZMod (c+2)))),
          ((IsPrimePow (c+2) ∧ (c+2).Coprime (Nat.card H)) ∨ (∀ h v i, a h v i = χ i h (v i))) ∧ Nonempty (G ≃* SemidirectProduct _ H a))) ∨
        (∃ N P : Subgroup G, N.Normal ∧ N.IsComplement' P ∧ Group.IsNilpotent N ∧ Group.IsNilpotent P ∧ Nat.card N ^ (Group.rank N * Group.rank P) ≤ 2^(r*r*2) ∧ (Nat.card N).Coprime (Nat.card P))) ∨
        (∃ p k a b : ℕ, p.Prime ∧ 0 < b ∧ ∃ H : FiniteGrp.{0}, Group.IsSolvable H ∧ Group.IsNilpotent H ∧ ¬ p ∣ Nat.card H ∧ ∃ f : H →* MulAut (Multiplicative ((Fin a → ZMod p) × (Fin b → ZMod (p^(k+2))))), Nonempty (G ≃* SemidirectProduct _ H f))) ∧ (∃ p : ℕ, p.Prime ∧ ∃ P : Sylow p G, ¬ IsMulCommutative P)}).ncard ≤
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

/-- Restriction to the ground field bounds the length of an independent family of simple summands. -/
lemma simple_summand_count (F A M : Type*) [Field F] [Ring A] [Algebra F A]
    [AddCommGroup M] [Module A M] [Module F M] [IsScalarTower F A M] [Module.Finite F M]
    (s : Set (Submodule A M)) (ind : sSupIndep s) (simple : ∀ m ∈ s, IsSimpleModule A m) :
    s.Finite ∧ Nat.card s ≤ Module.finrank F M := by
  classical
  have nz (m : s) : ∃ v : M, v ∈ m.val ∧ v ≠ 0 := by
    let _ := simple m.val m.property
    let _ := IsSimpleModule.nontrivial A m.val
    obtain ⟨v, hv⟩ := exists_ne (0 : m.val)
    exact ⟨v, v.property, fun h => hv (Subtype.ext h)⟩
  choose v hv hn using nz
  have hind : iSupIndep (fun m : s => m.val.restrictScalars F) := by
    apply iSupIndep_def.mpr
    intro i
    simpa only [← Submodule.restrictScalars_iSup, Submodule.disjoint_restrictScalars_iff] using
      (iSupIndep_def.mp ((sSupIndep_iff s).mp ind) i)
  have lin := hind.linearIndependent _ hv hn
  let _ : Finite s := lin.finite
  let _ := Fintype.ofFinite s
  exact ⟨Set.toFinite _, by simpa [Nat.card_eq_fintype_card] using lin.fintype_card_le_finrank⟩

/-- A catalogue of simple group-algebra modules, valid over a nonsplitting field. -/
theorem simple_group_algebra_catalogue (F H : Type) [Field F] [Group H] [Finite H]
    [NeZero (Nat.card H : F)] :
    ∃ s : Finset (Ideal (MonoidAlgebra F H)), s.card ≤ Nat.card H ∧
      (∀ I ∈ s, IsSimpleModule (MonoidAlgebra F H) I) ∧
      ∀ (V : Type) [AddCommGroup V] [Module (MonoidAlgebra F H) V] [IsSimpleModule (MonoidAlgebra F H) V],
        ∃ I ∈ s, Nonempty (V ≃ₗ[MonoidAlgebra F H] I) := by
  classical
  let A := MonoidAlgebra F H
  let _ := Fintype.ofFinite H
  let basis := MonoidAlgebra.basis H F
  let _ : Module.Finite F A := Module.Finite.of_basis basis
  obtain ⟨s, ind, top, simple⟩ := IsSemisimpleModule.exists_sSupIndep_sSup_simples_eq_top A A
  obtain ⟨hs, size⟩ := simple_summand_count F A A s ind simple
  refine ⟨hs.toFinset, ?_, fun I h => simple I (hs.mem_toFinset.mp h), ?_⟩
  · have dim : Module.finrank F A = Fintype.card H := Module.finrank_eq_card_basis basis
    simpa [← Set.ncard_eq_toFinset_card s hs, Set.ncard_def, dim,
      Nat.card_eq_fintype_card] using size
  · intro V _ _ _
    obtain ⟨I, ⟨e⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule A V
    let _ : IsSimpleModule A I := e.isSimpleModule_iff.mp inferInstance
    let _ (m : s) : IsSimpleModule A m := simple m.val m.property
    obtain ⟨J, hJ, ⟨f⟩⟩ := I.linearEquiv_of_sSup_eq_top s top
    exact ⟨J, hs.mem_toFinset.mpr hJ, ⟨e.trans f⟩⟩

/-- Write a finite-dimensional module as a list of catalogue entries of length at most its dimension. -/
lemma module_catalogue_code (F A V : Type) [Field F] [Ring A] [Algebra F A]
    [AddCommGroup V] [Module A V] [Module F V] [IsScalarTower F A V] [Module.Finite F V]
    [IsSemisimpleModule A V] (c : Finset (Ideal A))
    (cover : ∀ (M : Type) [AddCommGroup M] [Module A M] [IsSimpleModule A M],
      ∃ I ∈ c, Nonempty (M ≃ₗ[A] I)) :
    ∃ n ≤ Module.finrank F V, ∃ f : Fin n → c, Nonempty (V ≃ₗ[A] ((i : Fin n) → (f i).val)) := by
  classical
  obtain ⟨s, e, ind, simple⟩ := IsSemisimpleModule.exists_linearEquiv_dfinsupp A V
  obtain ⟨finite, bound⟩ := simple_summand_count F A V s ind (fun m hm => simple ⟨m,hm⟩)
  let _ := finite.fintype
  let _ (m : s) : IsSimpleModule A m.val := simple m
  choose ideal mem iso using fun m : s => cover m.val
  let b := Finite.equivFin s
  let f (i : Fin (Nat.card s)) : c := ⟨ideal (b.symm i), mem _⟩
  let u := (e.trans DFinsupp.linearEquivFunOnFintype).trans (LinearEquiv.piCongrRight fun m => (iso m).some)
  exact ⟨_, bound, f, ⟨u.trans (LinearEquiv.piCongrLeft' A _ b)⟩⟩

/-- Count pairwise nonisomorphic group-algebra modules of dimension at most t. -/
theorem coprime_module_family_bound (F H : Type) [Field F] [Group H] [Finite H]
    [NeZero (Nat.card H : F)] {ι : Type*} (V : ι → Type)
    [∀ i, AddCommGroup (V i)] [∀ i, Module (MonoidAlgebra F H) (V i)]
    [∀ i, Module F (V i)] [∀ i, IsScalarTower F (MonoidAlgebra F H) (V i)]
    [∀ i, Module.Finite F (V i)] (t : ℕ) (dim : ∀ i, Module.finrank F (V i) ≤ t)
    (distinct : ∀ i j, Nonempty (V i ≃ₗ[MonoidAlgebra F H] V j) → i = j) :
    Finite ι ∧ Nat.card ι ≤ (Nat.card H + 1)^t := by
  classical
  let A := MonoidAlgebra F H
  obtain ⟨c, size, _, cover⟩ := simple_group_algebra_catalogue F H
  choose n hn f iso using fun i => module_catalogue_code F A (V i) c cover
  let code (i : ι) : (k : Fin (t+1)) × (Fin k.val → c) :=
    ⟨⟨n i, Nat.lt_succ_of_le ((hn i).trans (dim i))⟩, f i⟩
  let model (z : (k : Fin (t+1)) × (Fin k.val → c)) := (j : Fin z.1.val) → z.2 j |>.val
  have inj : Function.Injective code := by
    intro i j h
    have transport (z w : (k : Fin (t+1)) × (Fin k.val → c)) (hzw : z = w) :
        Nonempty (model z ≃ₗ[A] model w) := by
      subst w
      exact ⟨LinearEquiv.refl A _⟩
    have bridge := transport _ _ h
    exact distinct i j ⟨(iso i).some.trans (bridge.some.trans (iso j).some.symm)⟩
  have sum_bound (m : ℕ) : (∑ k : Fin (m+1), c.card^k.val) ≤ (c.card+1)^m := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Fin.sum_univ_succ, pow_succ]
      simp only [Fin.val_zero, pow_zero, Fin.val_succ, pow_succ, ← Finset.sum_mul]
      have one : 1 ≤ (c.card+1)^m := Nat.pow_pos (by omega)
      nlinarith [Nat.mul_le_mul_right c.card ih]
  refine ⟨Finite.of_injective code inj, (Nat.card_le_card_of_injective code inj).trans ?_⟩
  rw [Nat.card_sigma]
  simpa only [Nat.card_fun, Nat.card_fin, Nat.card_eq_fintype_card (α := ↥c), Fintype.card_coe] using
    (sum_bound t).trans (Nat.pow_le_pow_left (Nat.add_le_add_right size 1) t)

/-- Summing translates of a map produces an intertwiner. -/
lemma average_intertwines {R H : Type*} [Ring R] [Group H] [Fintype H]
    (a b : H →* R) (T : R) (g : H) :
    b g * (∑ h : H, b h * T * a h⁻¹) = (∑ h : H, b h * T * a h⁻¹) * a g := by
  let f (h : H) := b h * T * a h⁻¹ * a g
  calc
    _ = ∑ h : H, f (g*h) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _
      have cancel : a ((g*h)⁻¹) * a g = a h⁻¹ := by rw [← a.map_mul]; simp
      simp only [f, mul_assoc, cancel, map_mul]
    _ = ∑ h : H, f h := Equiv.sum_comp (Equiv.mulLeft g) f
    _ = _ := (Finset.sum_mul ..).symm

/-- Lift a specified invertible intertwiner modulo p by averaging a normalized entrywise lift. -/
theorem prime_power_intertwiner {p n : ℕ} [Fact p.Prime] (hn : 0 < n)
    {I H : Type*} [Fintype I] [DecidableEq I] [Group H] [Fintype H]
    (cop : ¬ p ∣ Fintype.card H)
    (a b : H →* Matrix I I (ZMod (p^n)))
    (T : Matrix I I (ZMod p)) (unitT : IsUnit T)
    (inter : ∀ h, (b h).map (ZMod.castHom (dvd_pow_self p hn.ne') (ZMod p)) * T =
      T * (a h).map (ZMod.castHom (dvd_pow_self p hn.ne') (ZMod p))) :
    ∃ U : Matrix I I (ZMod (p^n)), IsUnit U ∧
      U.map (ZMod.castHom (dvd_pow_self p hn.ne') (ZMod p)) = T ∧ ∀ g, b g * U = U * a g := by
  classical
  let φ := ZMod.castHom (dvd_pow_self p hn.ne') (ZMod p)
  let ψ : Matrix I I (ZMod (p^n)) →+* Matrix I I (ZMod p) := φ.mapMatrix
  let c : ZMod p := Fintype.card H
  have hc : c ≠ 0 := fun h => cop ((ZMod.natCast_eq_zero_iff ..).mp h)
  let V : Matrix I I (ZMod (p^n)) := fun i j => (ZMod.castHom_surjective (dvd_pow_self p hn.ne') (c⁻¹ * T i j)).choose
  have hv : ψ V = c⁻¹ • T := by
    ext i j
    exact (ZMod.castHom_surjective (dvd_pow_self p hn.ne') (c⁻¹ * T i j)).choose_spec
  let U := ∑ h : H, b h * V * a h⁻¹
  have red : ψ U = T := by
    have term (h : H) : ψ (b h * V * a h⁻¹) = c⁻¹ • T := by
      simp only [map_mul, hv, Matrix.mul_smul, Matrix.smul_mul]
      change c⁻¹ • (((b h).map φ * T) * ψ (a h⁻¹)) = _
      rw [inter, mul_assoc]
      change c⁻¹ • (T * (ψ (a h) * ψ (a h⁻¹))) = _
      rw [← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one, mul_one]
    simp only [U, map_sum, term, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul (ZMod p), smul_smul]
    change (c*c⁻¹) • T = T
    rw [mul_inv_cancel₀ hc, one_smul]
  refine ⟨U, (Matrix.isUnit_iff_isUnit_det U).mpr ?_, red, average_intertwines a b V⟩
  let _ : NeZero (p^n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have hd : φ U.det ≠ 0 := by
    rw [φ.map_det]
    exact ((Matrix.isUnit_iff_isUnit_det (ψ U)).mp (red.symm ▸ unitT)).ne_zero
  rw [← ZMod.natCast_zmod_val U.det]
  apply (ZMod.isUnit_natCast_iff_not_dvd_pow Fact.out hn).mpr
  intro h
  apply hd
  rw [← ZMod.natCast_zmod_val U.det, map_natCast, ZMod.natCast_eq_zero_iff]
  exact h

/-- Fixed complement and homocyclic kernel, including higher-dimensional irreducible representations. -/
theorem homocyclic_kernel_classes (p n t : ℕ) (hn : 0 < n) [Fact p.Prime] (H : FiniteGrp.{0})
    [NeZero (Nat.card H : ZMod p)] :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | ∃ a : H →* MulAut (Multiplicative (Fin t → ZMod (p^n))),
        Nonempty (G ≃* SemidirectProduct _ H a)}).ncard ≤ (Nat.card H + 1)^t := by
  classical
  let _ := Fintype.ofFinite H
  let V := Fin t → ZMod (p^n)
  let K := Multiplicative V
  let S := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | ∃ a : H →* MulAut K, Nonempty (G ≃* SemidirectProduct K H a)}
  let G (x : S) : FiniteGrp.{0} := x.property.choose
  have rep (x : S) : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (G x) = x.val := x.property.choose_spec.2
  choose a iso using fun x : S => x.property.choose_spec.1
  let integral (x : S) : Representation (ZMod (p^n)) H V :=
    { toFun := fun h => (AddMonoidHom.toMultiplicative.symm ((a x h).toMonoidHom)).toZModLinearMap (p^n)
      map_one' := by apply LinearMap.ext; intro v; change (a x 1) v = v; rw [map_one]; rfl
      map_mul' := by intro h j; apply LinearMap.ext; intro v; change (a x (h*j)) v = (a x h) ((a x j) v); rw [map_mul]; rfl }
  let φ := ZMod.castHom (dvd_pow_self p hn.ne') (ZMod p)
  let M (x : S) := LinearMap.toMatrixAlgEquiv'.toMonoidHom.comp (integral x)
  let red (x : S) := φ.mapMatrix.toMonoidHom.comp (M x)
  let ρ (x : S) : Representation (ZMod p) H (Fin t → ZMod p) :=
    Matrix.toLinAlgEquiv'.toMonoidHom.comp (red x)
  change Nat.card S ≤ _
  apply (coprime_module_family_bound (ZMod p) H (fun x : S => (ρ x).asModule) t ?_ ?_).2
  · intro x
    rw [(ρ x).asModuleEquiv.finrank_eq]
    simp
  · rintro x y ⟨e⟩
    let v := (ρ x).asModuleEquiv.symm.trans ((e.restrictScalars (ZMod p)).trans (ρ y).asModuleEquiv)
    have comm (h : H) (z : Fin t → ZMod p) : v (ρ x h z) = ρ y h (v z) := by
      apply (ρ y).asModuleEquiv.symm.injective
      rw [(ρ y).asModuleEquiv_symm_map_rho]
      exact (congrArg e ((ρ x).asModuleEquiv_symm_map_rho h z)).trans (e.map_smul _ _)
    let T := LinearMap.toMatrixAlgEquiv' v.toLinearMap
    have isT : IsUnit T := LinearMap.isUnit_toMatrix'_iff.mpr ((Module.End.isUnit_iff _).mpr v.bijective)
    have intertwines (h : H) : (red y h)*T = T*(red x h) := by
      apply Matrix.toLinAlgEquiv'.injective
      rw [map_mul, map_mul, Matrix.toLinAlgEquiv'_toMatrixAlgEquiv']
      exact LinearMap.ext fun z => (comm h z).symm
    have cop : ¬ p ∣ Fintype.card H := by
      rw [Fintype.card_eq_nat_card]
      exact fun h => (NeZero.ne (Nat.card H : ZMod p)) ((ZMod.natCast_eq_zero_iff ..).mpr h)
    obtain ⟨U, hU, _, lift⟩ := prime_power_intertwiner hn cop (M x) (M y) T isT intertwines
    let L := Matrix.toLinAlgEquiv' U
    let f := (LinearEquiv.ofBijective L ((Module.End.isUnit_iff _).mp
      (Matrix.isUnit_toLin'_iff.mpr hU))).toAddEquiv.toMultiplicative
    have equivariant (h : H) : (a x h).trans f = f.trans (a y h) := by
      have eq := congrArg Matrix.toLinAlgEquiv' (lift h)
      rw [map_mul, map_mul] at eq
      change Matrix.toLinAlgEquiv' (LinearMap.toMatrixAlgEquiv' (integral y h)) * L =
        L * Matrix.toLinAlgEquiv' (LinearMap.toMatrixAlgEquiv' (integral x h)) at eq
      rw [Matrix.toLinAlgEquiv'_toMatrixAlgEquiv', Matrix.toLinAlgEquiv'_toMatrixAlgEquiv'] at eq
      apply DFunLike.ext'
      funext z
      exact (DFunLike.congr_fun eq (z : V)).symm
    let mid := SemidirectProduct.congr f (MulEquiv.refl H) equivariant
    apply Subtype.ext
    rw [← rep x, ← rep y]
    exact Quotient.sound ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp)
      (((iso x).some.trans (mid.trans (iso y).some.symm)).toGrpIso)⟩

/-- For a prime-power coordinate group every coprime action is allowed.
For other coordinate orders we count actions admitting diagonal coordinates. -/
theorem homocyclic_or_diagonal_hall_bound (C : FiniteGrp.{0}) [IsCyclic C] (t l r : ℕ)
    (hl : 0 < l) (cop : l.Coprime (Nat.card C^t)) (hr : Nat.card C^t*l < 2^r) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | ∃ H : FiniteGrp.{0}, Nat.card H = l ∧ Group.IsSolvable H ∧ Group.IsNilpotent H ∧
        ∃ (χ : Fin t → H →* MulAut C) (a : H →* MulAut (Fin t → C)),
          ((IsPrimePow (Nat.card C) ∧ (Nat.card C).Coprime (Nat.card H)) ∨ (∀ h v i, a h v i = χ i h (v i))) ∧ Nonempty (G ≃* SemidirectProduct (Fin t → C) H a)}).ncard ≤
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
      ((IsPrimePow (Nat.card C) ∧ (Nat.card C).Coprime (Nat.card H)) ∨ (∀ h v i, a h v i = χ i h (v i))) ∧ Nonempty (G ≃* SemidirectProduct (Fin t → C) H a)}
  have finite (x : O) : (S (K x)).Finite := (finite_classes (k*l)).subset (Set.image_mono (by
    rintro G ⟨χ,a,_,⟨e⟩⟩
    exact (Nat.card_congr e.toEquiv).trans (by simp [SemidirectProduct.card, Nat.card_fun, k, order])))
  have bound (x : O) : (S (K x)).ncard ≤ 2^(r*r) := by
    by_cases hp : IsPrimePow (Nat.card C) ∧ (Nat.card C).Coprime (Nat.card (K x))
    · obtain ⟨p,n,hpprime,hn,heq⟩ := (isPrimePow_nat_iff _).mp hp.1
      let _ : Fact p.Prime := ⟨hpprime⟩
      let _ : NeZero (p^n) := ⟨pow_ne_zero _ hpprime.ne_zero⟩
      have copP := hp.2.coprime_dvd_left (heq ▸ dvd_pow_self p hn.ne')
      let _ : NeZero (Nat.card (K x) : ZMod p) := ⟨fun h =>
        (hpprime.coprime_iff_not_dvd.mp copP) ((ZMod.natCast_eq_zero_iff ..).mp h)⟩
      let u : C ≃* Multiplicative (ZMod (p^n)) := mulEquivOfCyclicCardEq (heq.symm.trans (Nat.card_zmod _).symm)
      let tag : (Fin t → Multiplicative (ZMod (p^n))) ≃* Multiplicative (Fin t → ZMod (p^n)) :=
        { Equiv.refl _ with map_mul' := fun _ _ => rfl }
      let f := (MulEquiv.piCongrRight fun _ : Fin t => u).trans tag
      apply le_trans _ (le_trans (homocyclic_kernel_classes p n t hn (K x)) ?_)
      · apply Set.ncard_le_ncard _ ((finite_classes (k*l)).subset (Set.image_mono (by
          rintro G ⟨a,⟨e⟩⟩
          exact (Nat.card_congr e.toEquiv).trans (by
            rw [SemidirectProduct.card, ← Nat.card_congr f.toEquiv, Nat.card_fun, Nat.card_fin, order]))))
        rintro _ ⟨G, ⟨_,a,_,⟨e⟩⟩,rfl⟩
        exact ⟨G, ⟨_, ⟨e.trans (SemidirectProduct.congr' f (MulEquiv.refl (K x)))⟩⟩, rfl⟩
      · have ht : t ≤ r := by
          have hpow : 2^t < 2^r := (Nat.pow_le_pow_left (by rw [← heq]; exact hpprime.two_le.trans (by simpa using Nat.pow_le_pow_right hpprime.pos hn)) t).trans_lt
            ((Nat.le_mul_of_pos_right k hl).trans_lt hr)
          by_contra! bad
          exact hpow.not_ge (Nat.pow_le_pow_right (by decide) bad.le)
        have hlr := (Nat.le_mul_of_pos_left l hk).trans_lt hr
        rw [order, pow_mul]
        exact (Nat.pow_le_pow_left (show l+1 ≤ 2^r from hlr) _).trans
          (Nat.pow_le_pow_right (by positivity) ht)
    apply le_trans _ (le_trans (diagonal_class_bound C (K x) t) ?_)
    · apply Set.ncard_le_ncard _ ((finite_classes (k*l)).subset (Set.image_mono (by
        rintro G ⟨_,a,_,⟨e⟩⟩
        exact (Nat.card_congr e.toEquiv).trans (by simp [SemidirectProduct.card, Nat.card_fun, k, order]))))
      rintro _ ⟨G, ⟨χ,a,alt,e⟩,rfl⟩
      exact ⟨G, ⟨χ,a,alt.resolve_left hp,e⟩,rfl⟩
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
      diag.imp (fun h => ⟨h.1, by simpa [order, hH] using h.2⟩) (fun hdiag h v j => hdiag (u h) v j), ⟨e.trans mid⟩⟩, rfl⟩
  · calc
      _ ≤ ∑ x : O, (S (K x)).ncard := Set.ncard_iUnion_le_of_fintype _
      _ ≤ ∑ _ : O, 2^(r*r) := Finset.sum_le_sum fun x _ => bound x
      _ = 2^(r*r)*O.ncard := by simp [← Nat.card_eq_fintype_card, Nat.mul_comm]
      _ ≤ _ := Nat.mul_le_mul_left _ parts

/-- Count all homocyclic prime-power Hall kernels with nilpotent complement together with the diagonal family. -/
theorem homocyclic_or_diagonal_hall_union {q r : ℕ} (hr : q < 2^r) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = q ∧ (∃ c t : ℕ, 0 < t ∧ ∃ H : FiniteGrp.{0}, Group.IsSolvable H ∧ Group.IsNilpotent H ∧
        (Nat.card H).Coprime ((c+2)^t) ∧
        ∃ (χ : Fin t → H →* MulAut (Multiplicative (ZMod (c+2))))
          (a : H →* MulAut (Fin t → Multiplicative (ZMod (c+2)))),
          ((IsPrimePow (c+2) ∧ (c+2).Coprime (Nat.card H)) ∨ (∀ h v i, a h v i = χ i h (v i))) ∧ Nonempty (G ≃* SemidirectProduct _ H a))}).ncard ≤
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
        ((IsPrimePow (i.val.1.val+2) ∧ (i.val.1.val+2).Coprime (Nat.card H)) ∨ (∀ h v j, a h v j = χ j h (v j))) ∧ Nonempty (G ≃* SemidirectProduct _ H a)}
  let L := ∏ b ∈ q.primeFactors, g (b^q.factorization b)
  have cardpow (i : I) : Nat.card (C i.val)^i.val.2.val = k i.val := by rw [card]
  have bound (i : I) : (S i).ncard ≤ 2^(r*r)*L := by
    have eq := (congrArg (· * (q/k i.val)) (cardpow i)).trans i.property.2.2
    have h := homocyclic_or_diagonal_hall_bound (C i.val) i.val.2.val (q/k i.val) r i.property.1
      ((cardpow i).symm ▸ i.property.2.1) (eq.trans_lt hr)
    rw [eq] at h
    simpa only [card] using h
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

lemma surjective_of_surjective_mod_p {A : Type*} [AddCommGroup A] {p n : ℕ}
    (f : A →+ A) (tors : ∀ x : A, (p^n) • x = 0)
    (red : ∀ x : A, ∃ y z : A, x = f y + p • z) : Function.Surjective f := by
  have step (k : ℕ) (x : A) : ∃ y z : A, x = f y + (p^k) • z := by
    induction k with
    | zero => exact ⟨0, x, by simp⟩
    | succ k ih =>
      obtain ⟨y,z,h⟩ := ih
      obtain ⟨u,v,hz⟩ := red z
      exact ⟨y + (p^k) • u, v, by rw [h, hz, smul_add, map_add, map_nsmul,
        pow_succ, mul_smul, add_assoc]⟩
  intro x
  obtain ⟨y,z,h⟩ := step n x
  exact ⟨y, by simpa [tors] using h.symm⟩

universe u
/-- Bound the possible representations on one diagonal block. -/
lemma block_repcode {p : ℕ} [Fact p.Prime] {H : Type} [Group H] [Finite H] [NeZero (Nat.card H : ZMod p)] {S : Type u}
    {t : ℕ} (a : S → H →* AddMonoid.End ((Fin t → ZMod p))) :
    ∃ (C : Type u) (_ : Finite C) (code : S → C), Nat.card C ≤ (Nat.card H+1)^t ∧
      ∀ i j, code i = code j → ∃ T : AddMonoid.End ((Fin t → ZMod p)), Function.Surjective T ∧
        ∀ h, a j h * T = T * a i h := by
  classical
  let ρ (i : S) : Representation (ZMod p) H ((Fin t → ZMod p)) :=
    { toFun := fun h => (a i h).toZModLinearMap p
      map_one' := by apply LinearMap.ext; intro x; change a i 1 x = x; rw [map_one]; rfl
      map_mul' := by intro g h; apply LinearMap.ext; intro x; change a i (g*h) x = a i g (a i h x); rw [map_mul]; rfl }
  let R := MonoidAlgebra (ZMod p) H
  let s : Setoid S := ⟨fun i j => Nonempty ((ρ i).asModule ≃ₗ[R] (ρ j).asModule),
    ⟨fun _ => ⟨LinearEquiv.refl _ _⟩,fun e => ⟨e.some.symm⟩,fun e f => ⟨e.some.trans f.some⟩⟩⟩
  let C := Quotient s
  have bound := coprime_module_family_bound (ZMod p) H (fun c : C => (ρ c.out).asModule) t
    (fun c => by rw [(ρ c.out).asModuleEquiv.finrank_eq]; simp) (fun i j h => by
      rw [← Quotient.out_eq i, ← Quotient.out_eq j]; exact Quotient.sound h)
  refine ⟨C,bound.1,Quotient.mk s,bound.2,?_⟩
  intro i j eq
  obtain ⟨e⟩ := Quotient.exact eq
  let v := (ρ i).asModuleEquiv.symm.trans ((e.restrictScalars (ZMod p)).trans (ρ j).asModuleEquiv)
  refine ⟨v.toAddEquiv.toAddMonoidHom,v.surjective,?_⟩
  intro h
  apply AddMonoidHom.ext
  intro x
  change ρ j h (v x) = v (ρ i h x)
  apply (ρ j).asModuleEquiv.symm.injective
  rw [(ρ j).asModuleEquiv_symm_map_rho]
  exact ((congrArg e ((ρ i).asModuleEquiv_symm_map_rho h x)).trans (e.map_smul _ _)).symm

/-- The two diagonal representations determine a coprime action up to conjugacy. -/
theorem block_family_bound {p k : ℕ} [Fact p.Prime] {H : Type} {S : Type u} [Group H] [Fintype H] (cop : ¬ p ∣ Fintype.card H)
    {m n : ℕ} (a : S → H →* AddMonoid.End (((Fin m → ZMod p) × (Fin n → ZMod (p^(k+2))))))
    (sep : ∀ i j, (∃ U : _ ≃+ _, ∀ h x, a j h (U x) = U (a i h x)) → i = j) :
    Finite S ∧ Nat.card S ≤ (Nat.card H + 1)^(m+n) := by
  classical
  let I := Fin m
  let J := Fin n
  let X := I → ZMod p
  let Y := J → ZMod p
  let Z := J → ZMod (p^(k+2))
  let B := X × Z
  let E (T : Type) [AddCommGroup T] := T →+ T
  let π := ZMod.castHom (dvd_pow_self p (by omega : k+2 ≠ 0)) (ZMod p)
  let red (y : Z) : Y := fun j => π (y j)
  have red_zero : red (0 : Z) = 0 := funext fun _ => π.map_zero
  let lift (y : Y) : Z := fun j => (y j).val
  have red_lift (y : Y) : red (lift y) = y := by ext; simp [red,lift]
  have p_low {S : Type} (x : S → ZMod p) : p • x = 0 := by ext; simp [nsmul_eq_mul]
  have ker_red (y : Z) (h : red y = 0) : ∃ z, y = p • z := by
    let _ : NeZero (p^(k+2)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
    have dvd (j : J) : p ∣ (y j).val := by
      have e : π (y j) = 0 := congrFun h j
      rw [← ZMod.natCast_zmod_val (y j), map_natCast, ZMod.natCast_eq_zero_iff] at e
      exact e
    choose z hz using dvd
    exact ⟨fun j => (z j : ZMod _), funext fun j => by
      change y j = p • (z j : ZMod _)
      rw [nsmul_eq_mul, ← Nat.cast_mul, ← hz, ZMod.natCast_zmod_val]⟩
  have kills_low (f : E B) (x : X) : red (f (x,0)).2 = 0 := by
    have e : p • (x,(0 : Z)) = 0 := Prod.ext (p_low x) (by change p • (0 : Z) = 0; simp)
    have h := f.map_nsmul p (x,0)
    rw [e, f.map_zero] at h
    funext j
    let y := (f (x,0)).2 j
    have hy : 0 = p • y := congrArg (fun v : B => v.2 j) h
    let _ : NeZero (p^(k+2)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
    have hv := ZMod.natCast_zmod_val y
    rw [nsmul_eq_mul, ← hv, ← Nat.cast_mul, eq_comm, ZMod.natCast_eq_zero_iff] at hy
    conv at hy => lhs; rw [pow_succ, Nat.mul_comm]
    change π y = 0
    rw [← hv, map_natCast, ZMod.natCast_eq_zero_iff]
    exact dvd_trans (dvd_pow_self p (by omega : k+1 ≠ 0)) (Nat.dvd_of_mul_dvd_mul_left (Fact.out : p.Prime).pos hy)
  let proj : B →+ (X × Y) :=
      { toFun x := (x.1,red x.2)
        map_zero' := Prod.ext rfl red_zero
        map_add' x y := Prod.ext rfl (funext fun j => π.map_add _ _) }
  have proj_p (x : B) : proj (p • x) = 0 := by
    rw [map_nsmul]
    exact Prod.ext (p_low _) (p_low _)
  have congr_proj (f : E B) {x y : B} (h : proj x = proj y) :
      proj (f x) = proj (f y) := by
    have h0 : proj (x-y) = 0 := by rw [map_sub,h,sub_self]
    obtain ⟨z,hz⟩ := ker_red (x-y).2 (congrArg Prod.snd h0)
    have eq : x-y = p • ((0,z) : B) := Prod.ext (by change (x-y).1 = p • (0 : X); rw [smul_zero]; exact congrArg Prod.fst h0) hz
    apply sub_eq_zero.mp
    rw [← map_sub, ← f.map_sub, eq, f.map_nsmul, proj_p]
  let low (f : E B) : E X :=
      { toFun x := (f (x,0)).1
        map_zero' := by change (f 0).1 = 0; rw [f.map_zero]; rfl
        map_add' x y := by simpa [B,X,Z] using congrArg Prod.fst (f.map_add (x,0) (y,0)) }
  let highFun (f : E B) (v : Y) := red (f (0,lift v)).2
  have high_spec (f : E B) (x : B) : red (f x).2 = highFun f (red x.2) := by
    have e := f.map_add (x.1,0) (0,x.2)
    have e' : x = (x.1,0) + (0,x.2) := by simp [B,X,Z]
    conv_lhs => rw [e',e]
    change (proj (_ + _)).2 = _
    rw [map_add]
    change red (f (x.1,0)).2 + red (f (0,x.2)).2 = _
    rw [kills_low, zero_add]
    apply congrArg Prod.snd (congr_proj f _)
    exact Prod.ext rfl (red_lift _).symm
  let high (f : E B) : E Y :=
      { toFun := highFun f
        map_zero' := by
          have h := high_spec f 0
          simpa [red_zero] using h.symm
        map_add' x y := by
          let u : B := (0,lift x)
          let v : B := (0,lift y)
          have hu : red u.2 = x := red_lift _
          have hv : red v.2 = y := red_lift _
          have ha : red (u+v).2 = x+y := (congrArg Prod.snd (proj.map_add u v)).trans (congrArg₂ (·+·) hu hv)
          rw [← ha, ← high_spec, f.map_add, ← hu, ← hv, ← high_spec f u, ← high_spec f v]
          exact congrArg Prod.snd (proj.map_add _ _) }
  let diag : AddMonoid.End (B) →+*
      AddMonoid.End (X) × AddMonoid.End (Y) :=
      { toFun f := (low f,high f)
        map_one' := by
          apply Prod.ext
          · rfl
          · apply AddMonoidHom.ext; exact red_lift
        map_zero' := by
          apply Prod.ext
          · rfl
          · apply AddMonoidHom.ext; intro x; funext j; exact (π).map_zero
        map_add' f g := by
          apply Prod.ext
          · rfl
          · apply AddMonoidHom.ext; intro x; exact congrArg Prod.snd (proj.map_add _ _)
        map_mul' f g := by
          apply Prod.ext
          · apply AddMonoidHom.ext; intro x
            have e := (congr_proj f (x := g (x,0)) (y := ((g (x,0)).1,0))
              (Prod.ext rfl ((kills_low g x).trans red_zero.symm)))
            exact congrArg (fun t : X × Y => t.1) e
          · apply AddMonoidHom.ext; intro x
            exact high_spec f (g (0,lift x)) }
  have diag_onto (f : E B) (hl : Function.Surjective (low f))
      (hh : Function.Surjective (high f)) : Function.Surjective f := by
    apply surjective_of_surjective_mod_p (p := p) (n := k+2) f
    · intro x
      apply Prod.ext
      · funext i; change (p^(k+2)) • x.1 i = 0; simp [nsmul_eq_mul]
      · funext j; change (p^(k+2)) • x.2 j = 0; rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    intro x
    obtain ⟨w,hw⟩ := hh (red x.2)
    let v : B := (0,lift w)
    obtain ⟨u,hu⟩ := hl (x.1 - (f v).1)
    let y : B := (u,0) + v
    have h₁ : (f y).1 = x.1 := by
      change (f ((u,0)+v)).1 = _
      rw [map_add]; change low f u + (f v).1 = _; rw [hu,sub_add_cancel]
    have h₂ : red (f y).2 = red x.2 := by
      rw [high_spec]
      change highFun f (red (0 + lift w)) = _
      rw [zero_add,red_lift]; exact hw
    have he : proj (x-f y) = 0 := by
      rw [map_sub, sub_eq_zero]; exact Prod.ext h₁.symm h₂.symm
    obtain ⟨z,hz⟩ := ker_red (x-f y).2 (congrArg Prod.snd he)
    refine ⟨y,(0,z), Prod.ext ?_ ?_⟩
    · change x.1 = (f y).1 + p • 0; simp [h₁]
    · change x.2 = (f y).2 + p • z
      change x.2 - (f y).2 = _ at hz
      rw [← hz]; abel
  have diag_surjective : Function.Surjective diag := by
    classical
    rintro ⟨blockMap,D⟩
    let c (i j : J) : ZMod (p^(k+2)) := (D (Pi.single j 1) i).val
    let T : E B :=
      { toFun := fun x => (blockMap x.1, fun i => ∑ j, c i j * x.2 j)
        map_zero' := by ext <;> simp [B,X,Z]
        map_add' x y := by apply Prod.ext (blockMap.map_add _ _); funext i; simp [B,X,Z,mul_add,Finset.sum_add_distrib] }
    refine ⟨T,Prod.ext rfl ?_⟩
    apply AddMonoidHom.ext
    intro v
    have decomp : ∑ j, (v j).val • (Pi.single j 1 : Y) = v := by
      funext i
      rw [Finset.sum_apply]
      change ∑ j, (v j).val • ((Pi.single j 1 : Y) i) = _
      simp [J,Pi.single_apply,nsmul_eq_mul]
    have e := congrArg D decomp
    rw [map_sum] at e
    simp only [map_nsmul] at e
    funext i
    change π (∑ j, c i j * lift v j) = D v i
    rw [map_sum, ← e]
    rw [Finset.sum_apply]
    apply Finset.sum_congr rfl; intro j _
    rw [map_mul]; change π (↑(D (Pi.single j 1) i).val) * π (↑(v j).val) = _
    rw [map_natCast,map_natCast,ZMod.natCast_zmod_val,ZMod.natCast_zmod_val,mul_comm]
    change _ = (v j).val • (D (Pi.single j 1) i)
    rw [nsmul_eq_mul,ZMod.natCast_zmod_val]
  have conjugate
      (cop : ¬ p ∣ Fintype.card H) (a b : H →* AddMonoid.End (B))
      (T : AddMonoid.End (X) × AddMonoid.End (Y))
      (hl : Function.Surjective T.1) (hh : Function.Surjective T.2)
      (inter : ∀ h, diag (b h) * T = T * diag (a h)) :
      ∃ U : B ≃+ B, ∀ h x, b h (U x) = U (a h x) := by
    classical
    obtain ⟨L,hL⟩ := diag_surjective T
    let U := ∑ h : H, b h * L * a h⁻¹
    have term (h : H) : diag (b h * L * a h⁻¹) = T := by
      rw [map_mul,map_mul,hL,inter,mul_assoc,← map_mul,← map_mul,mul_inv_cancel,map_one,map_one,mul_one]
    have du : diag U = Fintype.card H • T := by simp only [U,map_sum,term,Finset.sum_const,Finset.card_univ]
    have onto {S : Type} (D : E ((S → ZMod p))) (sur : Function.Surjective D) :
        Function.Surjective (Fintype.card H • D) := by
      intro x
      let v : (S → ZMod p) := fun i => x i / (Fintype.card H : ZMod p)
      obtain ⟨y,hy⟩ := sur v
      refine ⟨y,?_⟩; funext i
      change Fintype.card H • D y i = x i
      rw [hy,nsmul_eq_mul,mul_comm]
      exact div_mul_cancel₀ _ (fun h => cop ((ZMod.natCast_eq_zero_iff ..).mp h))
    have sur := diag_onto U (by change Function.Surjective (diag U).1; rw [du]; exact onto _ hl)
      (by change Function.Surjective (diag U).2; rw [du]; exact onto _ hh)
    refine ⟨AddEquiv.ofBijective U ⟨Finite.injective_iff_surjective.mpr sur,sur⟩,?_⟩
    exact fun h x => DFunLike.congr_fun (average_intertwines a b L h) x
  let _ : NeZero (Nat.card H : ZMod p) := ⟨by rw [← Fintype.card_eq_nat_card]; exact fun h => cop ((ZMod.natCast_eq_zero_iff ..).mp h)⟩
  let l i := (MonoidHom.fst _ _).comp (diag.toMonoidHom.comp (a i))
  let r i := (MonoidHom.snd _ _).comp (diag.toMonoidHom.comp (a i))
  obtain ⟨C,fc,c,hc,lc⟩ := block_repcode l
  obtain ⟨D,fd,d,hd,rd⟩ := block_repcode r
  have inj : Function.Injective (fun i => (c i,d i)) := by
    intro i j eq
    obtain ⟨L,hL,eL⟩ := lc i j (congrArg Prod.fst eq)
    obtain ⟨R,hR,eR⟩ := rd i j (congrArg Prod.snd eq)
    exact sep i j (conjugate cop _ _ (L,R) hL hR (fun h => Prod.ext (eL h) (eR h)))
  refine ⟨Finite.of_injective _ inj,(Nat.card_le_card_of_injective _ inj).trans ?_⟩
  rw [Nat.card_prod,pow_add]; exact Nat.mul_le_mul hc hd
theorem mixed_blocks_kernel_classes (p k m n : ℕ) [Fact p.Prime] (H : FiniteGrp.{0})
    (cop : ¬ p ∣ Nat.card H) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | ∃ a : H →* MulAut (Multiplicative (((Fin m → ZMod p) × (Fin n → ZMod (p^(k+2)))))),
        Nonempty (G ≃* SemidirectProduct _ H a)}).ncard ≤ (Nat.card H+1)^(m+n) := by
  classical
  let _ := Fintype.ofFinite H
  let K := Multiplicative (((Fin m → ZMod p) × (Fin n → ZMod (p^(k+2)))))
  let S := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | ∃ a : H →* MulAut K, Nonempty (G ≃* SemidirectProduct K H a)}
  let G (x : S) : FiniteGrp.{0} := x.property.choose
  have rep (x : S) : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (G x) = x.val := x.property.choose_spec.2
  choose a iso using fun x : S => x.property.choose_spec.1
  let act (x : S) : H →* AddMonoid.End (((Fin m → ZMod p) × (Fin n → ZMod (p^(k+2))))) :=
    { toFun := fun h => AddMonoidHom.toMultiplicative.symm ((a x h).toMonoidHom)
      map_one' := by apply DFunLike.ext'; funext z; change (a x 1) z = z; rw [map_one]; rfl
      map_mul' := by intro h j; apply DFunLike.ext'; funext z; change (a x (h*j)) z = (a x h) ((a x j) z); rw [map_mul]; rfl }
  change Nat.card S ≤ _
  rw [← Fintype.card_eq_nat_card (α := H)] at cop
  apply (block_family_bound cop act ?_).2
  rintro x y ⟨U,hU⟩
  let f := U.toMultiplicative
  have comm (h : H) : (a x h).trans f = f.trans (a y h) := by
    apply DFunLike.ext'
    funext z
    exact (hU h z).symm
  let mid := SemidirectProduct.congr f (MulEquiv.refl H) comm
  apply Subtype.ext
  rw [← rep x, ← rep y]
  exact Quotient.sound ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp)
    (((iso x).some.trans (mid.trans (iso y).some.symm)).toGrpIso)⟩

lemma mixed_card (p k a b : ℕ) : Nat.card (Multiplicative ((Fin a → ZMod p) × (Fin b → ZMod (p^(k+2))))) = p^(a+(k+2)*b) := by
  change Nat.card ((Fin a → ZMod p) × (Fin b → ZMod (p^(k+2)))) = _
  simp [Nat.card_prod,Nat.card_fun,Nat.card_zmod,pow_add,pow_mul]



lemma mixed_fixed_bound (p k a b l : ℕ) [Fact p.Prime] (hl : 0 < l) (hp : ¬ p ∣ l) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
  {G : FiniteGrp.{0} | ∃ H : FiniteGrp.{0}, Nat.card H = l ∧ Group.IsSolvable H ∧ Group.IsNilpotent H ∧
    ∃ a : H →* MulAut (Multiplicative ((Fin a → ZMod p) × (Fin b → ZMod (p^(k+2))))), Nonempty (G ≃* SemidirectProduct _ H a)}).ncard ≤ (l+1)^(a+b) * ∏ z ∈ (p^(a+(k+2)*b)*l).primeFactors, g (z^(p^(a+(k+2)*b)*l).factorization z) := by
  classical
  let m := p^(a+(k+2)*b)
  have hm : 0 < m := pow_pos (Fact.out : p.Prime).pos _
  have cop : l.Coprime m := ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hp).symm.pow_right _
  let O := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {H : FiniteGrp.{0} | Nat.card H = l ∧ Group.IsSolvable H ∧ Group.IsNilpotent H}
  let C (x : O) : FiniteGrp.{0} := x.property.choose
  have rep (x : O) : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (C x) = x.val := x.property.choose_spec.2
  have order (x : O) : Nat.card (C x) = l := x.property.choose_spec.1.1
  let _ : Finite O := ((finite_classes l).subset (Set.image_mono (fun _ h => h.1))).to_subtype
  let _ := Fintype.ofFinite O
  let S (H : FiniteGrp.{0}) := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | ∃ a : H →* MulAut (Multiplicative ((Fin a → ZMod p) × (Fin b → ZMod (p^(k+2))))), Nonempty (G ≃* SemidirectProduct _ H a)}
  have finite (x : O) : (S (C x)).Finite := (finite_classes (m*l)).subset (Set.image_mono (by
    rintro G ⟨a,⟨e⟩⟩
    exact (Nat.card_congr e.toEquiv).trans (by rw [SemidirectProduct.card, mixed_card, order])))
  have bound (x : O) : (S (C x)).ncard ≤ (l+1)^(a+b) := by
    simpa only [order] using mixed_blocks_kernel_classes p k a b (C x) (by rwa [order])
  have sub : l.primeFactors ⊆ (m*l).primeFactors := by
    rw [Nat.primeFactors_mul hm.ne' hl.ne']
    exact Finset.subset_union_right
  have parts : O.ncard ≤ ∏ b ∈ (m*l).primeFactors, g (b^(m*l).factorization b) := by
    apply (nilpotent_bound l).trans
    calc
      _ = ∏ b ∈ l.primeFactors, g (b^(m*l).factorization b) := by
        apply Finset.prod_congr rfl
        intro b hb
        have nd : ¬ b ∣ m := fun hh => (Nat.prime_of_mem_primeFactors hb).not_dvd_one
          (cop ▸ Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hb) hh)
        rw [Nat.factorization_mul hm.ne' hl.ne', Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd nd, zero_add]
      _ ≤ _ := Finset.prod_le_prod_of_subset_of_one_le' sub fun b hb _ =>
        positive_count (pow_pos (Nat.prime_of_mem_primeFactors hb).pos _)
  apply le_trans (Set.ncard_le_ncard (t := ⋃ x : O, S (C x)) ?_ (Set.finite_iUnion finite)) ?_
  · rintro _ ⟨G, ⟨H,hH,hs,hn,a,⟨e⟩⟩,rfl⟩
    let x : O := ⟨Quotient.mk _ H,H,⟨hH,hs,hn⟩,rfl⟩
    let u : C x ≃* H := ((inducedFunctor FiniteGrp.toGrp).mapIso (Classical.choice (Quotient.exact (rep x)))).groupIsoToMulEquiv
    let mid := SemidirectProduct.congr (φ₁ := a) (φ₂ := a.comp u.toMonoidHom) (MulEquiv.refl _) u.symm
      (fun h => by apply DFunLike.ext'; funext v; change a h v = a (u (u.symm h)) v; rw [u.apply_symm_apply])
    exact Set.mem_iUnion.mpr ⟨x,G,⟨a.comp u.toMonoidHom,⟨e.trans mid⟩⟩,rfl⟩
  · calc
      _ ≤ ∑ x : O, (S (C x)).ncard := Set.ncard_iUnion_le_of_fintype _
      _ ≤ ∑ _ : O, (l+1)^(a+b) := Finset.sum_le_sum fun x _ => bound x
      _ = (l+1)^(a+b) * O.ncard := by simp [← Nat.card_eq_fintype_card, Nat.mul_comm]
      _ ≤ _ := Nat.mul_le_mul_left _ parts

/-- Sum the two-block Hall families of a fixed order over all profiles and nilpotent complements. -/
theorem mixed_union_bound {q r : ℕ} (hr : q < 2^r) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = q ∧ ∃ p k a b : ℕ, p.Prime ∧ 0 < b ∧ ∃ H : FiniteGrp.{0},
        Group.IsSolvable H ∧ Group.IsNilpotent H ∧ ¬ p ∣ Nat.card H ∧
        ∃ f : H →* MulAut (Multiplicative ((Fin a → ZMod p) × (Fin b → ZMod (p^(k+2))))), Nonempty (G ≃* SemidirectProduct _ H f)}).ncard ≤
      2^((r+1)^2) * ∏ z ∈ q.primeFactors, g (z^q.factorization z) := by
  classical
  let fixed (p k a b l : ℕ) := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | ∃ H : FiniteGrp.{0}, Nat.card H = l ∧ Group.IsSolvable H ∧ Group.IsNilpotent H ∧
      ∃ a : H →* MulAut (Multiplicative ((Fin a → ZMod p) × (Fin b → ZMod (p^(k+2))))), Nonempty (G ≃* SemidirectProduct _ H a)}
  let J := Fin (q+1) × Fin (q+1) × Fin (q+1) × Fin (q+1)
  let m (i : J) := i.1.val^(i.2.2.1.val+(i.2.1.val+2)*i.2.2.2.val)
  let l (i : J) := q / m i
  let I := {i : J // i.1.val.Prime ∧ 0 < l i ∧ ¬ i.1.val ∣ l i ∧ m i*l i = q ∧ i.2.2.1.val+i.2.2.2.val < r ∧ 2*l i ≤ q}
  let S (i : I) := fixed i.val.1.val i.val.2.1.val i.val.2.2.1.val i.val.2.2.2.val (l i.val)
  let L := ∏ z ∈ q.primeFactors, g (z^q.factorization z)
  have finite (i : I) : (S i).Finite := (finite_classes q).subset (Set.image_mono (by
    rintro G ⟨H,hH,_,_,f,⟨e⟩⟩
    exact (Nat.card_congr e.toEquiv).trans (by rw [SemidirectProduct.card, mixed_card, hH]; exact i.property.2.2.2.1)))
  have bound (i : I) : (S i).ncard ≤ 2^((r-1)*(r-1))*L := by
    let _ : Fact i.val.1.val.Prime := ⟨i.property.1⟩
    have h := mixed_fixed_bound i.val.1.val i.val.2.1.val i.val.2.2.1.val i.val.2.2.2.val _ i.property.2.1 i.property.2.2.1
    change _ ≤ (l i.val+1)^_ * ∏ z ∈ (m i.val*l i.val).primeFactors, g (z^(m i.val*l i.val).factorization z) at h
    rw [i.property.2.2.2.1] at h
    apply h.trans
    apply Nat.mul_le_mul_right
    have ⟨rank,twice⟩ := i.property.2.2.2.2
    have hpos : 0 < r := by omega
    have half : l i.val < 2^(r-1) := by
      have hlt := twice.trans_lt hr
      conv at hlt => rhs; rw [show r = (r-1)+1 by omega, pow_succ]
      omega
    rw [pow_mul]
    exact (Nat.pow_le_pow_left (Nat.succ_le_of_lt half) _).trans
      (Nat.pow_le_pow_right (by positivity) (by omega))
  apply le_trans (Set.ncard_le_ncard (t := ⋃ i : I, S i) ?_ (Set.finite_iUnion finite)) ?_
  · rintro _ ⟨G,⟨hg,p,k,a,b,hp,hb,H,hs,hn,nd,f,⟨e⟩⟩,rfl⟩
    let t := a+(k+2)*b
    have eq : p^t*Nat.card H = q := by
      exact ((by rw [SemidirectProduct.card,mixed_card] : Nat.card (SemidirectProduct _ H f) = p^t*Nat.card H).symm.trans (Nat.card_congr e.toEquiv).symm).trans hg
    have ht : 0 < t := by dsimp [t]; positivity
    have pq := (Nat.le_mul_of_pos_right (p^t) Nat.card_pos).trans eq.le
    have tq := (Nat.lt_pow_self hp.one_lt : t < p^t).trans_le pq
    have pp : p ≤ q := (by simpa using Nat.pow_le_pow_right hp.pos ht : p ≤ p^t).trans pq
    have ab : a+b ≤ t := by dsimp [t]; nlinarith
    have kk : k ≤ t := by dsimp [t]; nlinarith [Nat.le_mul_of_pos_right (k+2) hb]
    have tr : t < r := by
      have powlt := ((Nat.pow_le_pow_left hp.two_le t).trans pq).trans_lt hr
      by_contra! bad
      exact powlt.not_ge (Nat.pow_le_pow_right (by decide) bad)
    let j : J := (⟨p,by omega⟩,⟨k,by omega⟩,⟨a,by omega⟩,⟨b,by omega⟩)
    have div : l j = Nat.card H := by change q / p^t = _; rw [← eq,Nat.mul_div_cancel_left _ (pow_pos hp.pos _)]
    let i : I := ⟨j,hp,div.symm ▸ Nat.card_pos,div.symm ▸ nd,div.symm ▸ eq,ab.trans_lt tr,by rw [div,← eq]; exact Nat.mul_le_mul_right _ (hp.two_le.trans (by simpa using Nat.pow_le_pow_right hp.pos ht))⟩
    exact Set.mem_iUnion.mpr ⟨i,G,⟨H,div.symm,hs,hn,f,⟨e⟩⟩,rfl⟩
  · let _ := Fintype.ofFinite I
    have ni : Nat.card I ≤ (2^r)^4 := by
      apply (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans
      simpa [J,Nat.card_prod,pow_succ,mul_assoc] using Nat.pow_le_pow_left (show q+1 ≤ 2^r from hr) 4
    calc
      _ ≤ ∑ i : I, (S i).ncard := Set.ncard_iUnion_le_of_fintype _
      _ ≤ ∑ _ : I, 2^((r-1)*(r-1))*L := Finset.sum_le_sum fun i _ => bound i
      _ = Nat.card I * (2^((r-1)*(r-1))*L) := by simp [Nat.card_eq_fintype_card]
      _ ≤ (2^r)^4 * (2^((r-1)*(r-1))*L) := Nat.mul_le_mul_right _ ni
      _ ≤ _ := by
        rw [← mul_assoc,← pow_mul,← pow_add]
        apply Nat.mul_le_mul_right
        apply Nat.pow_le_pow_right (by decide)
        cases r <;> simp; nlinarith

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
          ((IsPrimePow (c+2) ∧ (c+2).Coprime (Nat.card H)) ∨ (∀ h v i, a h v i = χ i h (v i))) ∧ Nonempty (G ≃* SemidirectProduct _ H a))
  let U (G : FiniteGrp.{0}) := U₁ G ∨ U₂ G
  let V (G : FiniteGrp.{0}) := (∃ N P : Subgroup G, N.Normal ∧ N.IsComplement' P ∧ Group.IsNilpotent N ∧ Group.IsNilpotent P ∧ Nat.card N ^ (Group.rank N * Group.rank P) ≤ 2^(r*r*2) ∧ (Nat.card N).Coprime (Nat.card P))
  let W (G : FiniteGrp.{0}) := (∃ p k a b : ℕ, p.Prime ∧ 0 < b ∧ ∃ H : FiniteGrp.{0}, Group.IsSolvable H ∧ Group.IsNilpotent H ∧ ¬ p ∣ Nat.card H ∧ ∃ f : H →* MulAut (Multiplicative ((Fin a → ZMod p) × (Fin b → ZMod (p^(k+2))))), Nonempty (G ≃* SemidirectProduct _ H f))
  let N₀ (G : FiniteGrp.{0}) := U G ∨ V G
  let N (G : FiniteGrp.{0}) := N₀ G ∨ W G
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
  have nn₀ : (S N₀).ncard ≤ 2^(2*m+1)*L := by
    have cover : S N₀ = S U ∪ S V := by
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
        apply le_trans _ (homocyclic_or_diagonal_hall_union hr)
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
    rw [cover]
    calc
      _ ≤ (S U).ncard + (S V).ncard := Set.ncard_union_le _ _
      _ ≤ 2^(2*m)*L + 2^(2*m)*L := Nat.add_le_add hu hv
      _ = 2^(2*m+1)*L := by rw [pow_succ]; ring
  have nn : (S N).ncard ≤ 2^(D*m)*L := by
    have fin (F : FiniteGrp.{0} → Prop) : (S F).Finite :=
      (finite_classes q).subset (Set.image_mono (fun _ h => h.1))
    have sub : S N ⊆ S N₀ ∪ S W := by
      rintro _ ⟨G,⟨hg,hs,h | h⟩,rfl⟩
      · exact Or.inl ⟨G,⟨hg,hs,h⟩,rfl⟩
      · exact Or.inr ⟨G,⟨hg,hs,h⟩,rfl⟩
    have w : (S W).ncard ≤ 2^m*L := by
      apply le_trans _ (mixed_union_bound hr)
      apply Set.ncard_le_ncard _ ((finite_classes q).subset (Set.image_mono (fun _ h => h.1)))
      rintro _ ⟨G,⟨hg,_,h⟩,rfl⟩
      exact ⟨G,⟨hg,h⟩,rfl⟩
    calc
      _ ≤ (S N₀ ∪ S W).ncard := Set.ncard_le_ncard sub ((fin _).union (fin _))
      _ ≤ (S N₀).ncard + (S W).ncard := Set.ncard_union_le _ _
      _ ≤ 2^(2*m+1)*L + 2^(2*m+1)*L := Nat.add_le_add nn₀ (w.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (by omega))))
      _ = 2^((2*m+1)+1)*L := by rw [pow_succ _ (2*m+1)]; ring
      _ ≤ 2^(3*m)*L := by
        have hrpos : 0 < r := by
          by_contra! hz
          have := odd.pos
          simp [Nat.eq_zero_of_le_zero hz] at hr
          omega
        apply Nat.mul_le_mul_right
        apply Nat.pow_le_pow_right (by decide)
        dsimp [m]
        nlinarith [Nat.zero_le (r*r)]
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
