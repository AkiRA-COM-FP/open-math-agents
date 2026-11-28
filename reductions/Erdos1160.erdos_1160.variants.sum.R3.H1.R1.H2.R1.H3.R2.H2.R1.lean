import OMAReductions.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1_H2_R1_H3_R2
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
The remaining estimates concern nonnilpotent soluble groups of mixed order,
separating abelian from nonabelian Sylow subgroups. -/

open CategoryTheory Erdos1160

namespace OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1_H2_R1_H3_R2_H2_R1

def H1 : Prop :=
  ∃ E : ℕ, ∀ q r : ℕ, Odd q → q < 2^r → ¬ IsPrimePow q →
    ¬ (∃ p l a : ℕ, p.Prime ∧ l.Prime ∧ p ≠ l ∧ (¬ p ∣ l-1 ∨ ∀ i, 0 < i → i < a → ¬ Nat.ModEq l (p^i) 1) ∧ 0 < a ∧ q = p^a*l) →
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = q ∧ Group.IsSolvable G ∧ ¬ Group.IsNilpotent G ∧ ¬ IsZGroup G ∧
        (∀ p : ℕ, p.Prime → ∀ P : Sylow p G, IsMulCommutative P)}).ncard ≤
      2^(E*(r+1)^2) * ∏ p ∈ q.primeFactors, g (p^q.factorization p)

def H2 : Prop :=
  ∃ E : ℕ, ∀ q r : ℕ, Odd q → q < 2^r → ¬ IsPrimePow q →
    ¬ (∃ p l a : ℕ, p.Prime ∧ l.Prime ∧ p ≠ l ∧ (¬ p ∣ l-1 ∨ ∀ i, 0 < i → i < a → ¬ Nat.ModEq l (p^i) 1) ∧ 0 < a ∧ q = p^a*l) →
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = q ∧ Group.IsSolvable G ∧ ¬ Group.IsNilpotent G ∧ (∃ p : ℕ, p.Prime ∧ ∃ P : Sylow p G, ¬ IsMulCommutative P)}).ncard ≤
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

/-- Count groups with a self-normalizing Sylow subgroup of order l or with k coprime to l−1. -/
theorem peel {k l : ℕ} (hk : 0 < k) (hl : l.Prime)
    (hcop : ¬ l ∣ k) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = k*l ∧ (Nat.card (Sylow l G) = k ∨ k.Coprime (l-1))}).ncard ≤ g k * k^(Nat.log 2 k) := by
  classical
  let orderClasses (n : ℕ) := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | Nat.card G = n}
  let _ : NeZero l := ⟨hl.ne_zero⟩
  let _ : Fact l.Prime := ⟨hl⟩
  let H := FiniteGrp.of (Multiplicative (ZMod l))
  let _ : IsCyclic H := inferInstanceAs (IsCyclic (Multiplicative (ZMod l)))
  let K (x : orderClasses k) : FiniteGrp.{0} := x.property.choose
  have rep (x : orderClasses k) : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (K x) = x.val :=
    x.property.choose_spec.2
  have order (x : orderClasses k) : Nat.card (K x) = k := x.property.choose_spec.1
  let _ : Finite (orderClasses k) := (finite_classes _).to_subtype
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
      {G : FiniteGrp.{0} | Nat.card G = k*l ∧ (Nat.card (Sylow l G) = k ∨ k.Coprime (l-1))} ⊆ Set.range decode := by
    rintro _ ⟨G, ⟨hG, hcase⟩, rfl⟩
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
    let x : orderClasses k := ⟨Quotient.mk _ (FiniteGrp.of N), FiniteGrp.of N, hn, rfl⟩
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
    _ = _ := by simp [← Nat.card_eq_fintype_card, g, orderClasses]

/-- Count the cyclic normal Sylow kernel by actions of a complement of order k. -/
theorem normal_prime_count {k l : ℕ} (hk : 0 < k) (hl : l.Prime)
    (hcop : ¬ l ∣ k) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = k*l ∧ Nat.card (Sylow l G) = 1}).ncard ≤ g k * l^(Nat.log 2 k) := by
  classical
  let orderClasses (n : ℕ) := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | Nat.card G = n}
  let _ : NeZero l := ⟨hl.ne_zero⟩
  let _ : Fact l.Prime := ⟨hl⟩
  let H := FiniteGrp.of (Multiplicative (ZMod l))
  let _ : IsCyclic H := inferInstanceAs (IsCyclic (Multiplicative (ZMod l)))
  let K (x : orderClasses k) : FiniteGrp.{0} := x.property.choose
  have rep (x : orderClasses k) : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (K x) = x.val :=
    x.property.choose_spec.2
  have order (x : orderClasses k) : Nat.card (K x) = k := x.property.choose_spec.1
  let _ : Finite (orderClasses k) := (finite_classes _).to_subtype
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
      {G : FiniteGrp.{0} | Nat.card G = k*l ∧ Nat.card (Sylow l G) = 1} ⊆ Set.range decode := by
    rintro _ ⟨G, ⟨hG, count_one⟩, rfl⟩
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
    let x : orderClasses k := ⟨Quotient.mk _ (FiniteGrp.of N), FiniteGrp.of N, hn, rfl⟩
    let i := Classical.choice (Quotient.exact (rep x))
    let fn : N ≃* K x := ((inducedFunctor FiniteGrp.toGrp).mapIso i).groupIsoToMulEquiv.symm
    let fh : P ≃* H := mulEquivOfCyclicCardEq (hP.trans (Nat.card_zmod _).symm)
    let e := SemidirectProduct.mulEquivSubgroup comp
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
    _ = _ := by simp [← Nat.card_eq_fintype_card, g, orderClasses]

/-- The requested estimate with E = 1 for orders p^a l, under either normal-complement or normal-Sylow criterion. -/
theorem two_prime_bound {p l a r : ℕ} (hp : p.Prime) (hl : l.Prime) (hne : p ≠ l) (criterion : ¬ p ∣ l-1 ∨ ∀ i, 0 < i → i < a → ¬ Nat.ModEq l (p^i) 1)
    (ha : 0 < a) (hr : p^a*l < 2^r) :
    g (p^a*l) ≤ 2^((r+1)^2) *
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
  let A (G : FiniteGrp.{0}) := Nat.card (Sylow l G) = p^a ∨ (p^a).Coprime (l-1)
  let B (G : FiniteGrp.{0}) := Nat.card (Sylow l G) = 1
  have cover : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = p^a*l} = S A ∪ S B := by
    ext c
    constructor
    · rintro ⟨G, hG, rfl⟩
      rcases criterion with haut | hres
      · exact Or.inl ⟨G, ⟨hG, Or.inr ((hp.coprime_iff_not_dvd.mpr haut).pow_left a)⟩, rfl⟩
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
      · exact Or.inr ⟨G, ⟨hG, by simpa [B, hz] using he⟩, rfl⟩
      by_cases heq : i = a
      · exact Or.inl ⟨G, ⟨hG, Or.inl (heq ▸ he)⟩, rfl⟩
      exact (hres i (Nat.pos_of_ne_zero hz) (lt_of_le_of_ne hi heq)
        (he ▸ card_sylow_modEq_one l G)).elim
    · rintro (⟨G, ⟨hG, _⟩, rfl⟩ | ⟨G, ⟨hG, _⟩, rfl⟩) <;> exact ⟨G, hG, rfl⟩
  let L := ∏ b ∈ (p^a*l).primeFactors, g (b^(p^a*l).factorization b)
  have major (b : ℕ) (hb : b ≤ 2^r) :
      g (p^a)*b^(Nat.log 2 (p^a)) ≤ 2^(r*r)*L :=
    (Nat.mul_comm ..).le.trans (Nat.mul_le_mul (overhead _ hb) component)
  have boundA := (peel hk hl hcop).trans (major _ hkr.le)
  have boundB := (normal_prime_count hk hl hcop).trans
    (major _ ((Nat.le_mul_of_pos_left l hk).trans hr.le))
  unfold g at ⊢
  rw [cover]
  calc
    _ ≤ (S A).ncard + (S B).ncard := Set.ncard_union_le _ _
    _ ≤ 2^(r*r)*L + 2^(r*r)*L := Nat.add_le_add boundA boundB
    _ = 2^(r*r+1)*L := by rw [pow_succ]; ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (by nlinarith : r*r+1 ≤ (r+1)^2))

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

theorem main : H1 → H2 → OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1_H2_R1_H3_R2.H2 := by
  classical
  rintro ⟨A, hA⟩ ⟨B, hB⟩
  let D := max 1 (max A B)
  refine ⟨D+2, fun q r odd hr => ?_⟩
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
  let N (G : FiniteGrp.{0}) := Group.IsNilpotent G
  let Z (G : FiniteGrp.{0}) := IsZGroup G
  let C (G : FiniteGrp.{0}) := ∀ p : ℕ, p.Prime → ∀ P : Sylow p G, IsMulCommutative P
  let T (G : FiniteGrp.{0}) := ∃ p : ℕ, p.Prime ∧ ∃ P : Sylow p G, ¬ IsMulCommutative P
  let X (G : FiniteGrp.{0}) := ¬ N G ∧ ¬ Z G ∧ C G
  let Y (G : FiniteGrp.{0}) := ¬ N G ∧ T G
  have union_eq : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = q ∧ Group.IsSolvable G} =
      (S N ∪ S Z) ∪ (S X ∪ S Y) := by
    ext c
    constructor
    · rintro ⟨G, ⟨hq, hs⟩, rfl⟩
      by_cases hn : N G
      · exact Or.inl (Or.inl ⟨G, ⟨hq, hs, hn⟩, rfl⟩)
      by_cases hz : Z G
      · exact Or.inl (Or.inr ⟨G, ⟨hq, hs, hz⟩, rfl⟩)
      by_cases hc : C G
      · exact Or.inr (Or.inl ⟨G, ⟨hq, hs, hn, hz, hc⟩, rfl⟩)
      · have ht : T G := by simpa [C, T] using hc
        exact Or.inr (Or.inr ⟨G, ⟨hq, hs, hn, ht⟩, rfl⟩)
    · rintro ((⟨G, ⟨hq, hs, _⟩, rfl⟩ | ⟨G, ⟨hq, hs, _⟩, rfl⟩) | (⟨G, ⟨hq, hs, _⟩, rfl⟩ | ⟨G, ⟨hq, hs, _⟩, rfl⟩)) <;>
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
      _ ≤ _ := mono _ _ (le_max_left ..)
  have aa := (hA q r odd hr hpp htwo).trans (mono _ D ((le_max_left A B).trans (le_max_right ..)))
  have bb := (hB q r odd hr hpp htwo).trans (mono _ D ((le_max_right A B).trans (le_max_right ..)))
  have nn : (S N).ncard ≤ 2^(D*m)*L := (nilpotent_bound q).trans
    (Nat.le_mul_of_pos_left _ (Nat.pow_pos (by decide)))
  have cost : 4 ≤ 2^(2*m) := by
    have hm : 1 ≤ m := Nat.pow_pos (Nat.succ_pos r)
    exact (by decide : 4 ≤ 2^2).trans (Nat.pow_le_pow_right (by decide) (by omega))
  rw [union_eq]
  calc
    _ ≤ (S N ∪ S Z).ncard + (S X ∪ S Y).ncard := Set.ncard_union_le _ _
    _ ≤ ((S N).ncard + (S Z).ncard) + ((S X).ncard + (S Y).ncard) :=
      Nat.add_le_add (Set.ncard_union_le _ _) (Set.ncard_union_le _ _)
    _ ≤ (2^(D*m)*L + 2^(D*m)*L) + (2^(D*m)*L + 2^(D*m)*L) :=
      Nat.add_le_add (Nat.add_le_add nn za) (Nat.add_le_add aa bb)
    _ = 2^(D*m)*L*4 := by omega
    _ ≤ 2^(D*m)*L*2^(2*m) := Nat.mul_le_mul_left _ cost
    _ = 2^((D+2)*m)*L := by rw [add_mul, pow_add]; ac_rfl

end OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1_H2_R1_H3_R2_H2_R1
