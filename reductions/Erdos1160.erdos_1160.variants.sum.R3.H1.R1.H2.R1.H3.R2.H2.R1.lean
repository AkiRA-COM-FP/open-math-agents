import OMAReductions.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1_H2_R1_H3_R2
import Mathlib.GroupTheory.SpecificGroups.ZGroup
import Mathlib.CategoryTheory.IsomorphismClasses
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Set.Finite.Range
import Mathlib.Tactic.Linarith

/- Credit: @wispiANt. Count the groups with cyclic Sylow subgroups explicitly.
The Z-group approach was suggested by @hiattco in desk note 69164.
The remaining estimates concern nonnilpotent soluble groups of mixed order,
separating abelian from nonabelian Sylow subgroups. -/

open CategoryTheory Erdos1160

namespace OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1_H2_R1_H3_R2_H2_R1

def H1 : Prop :=
  ∃ E : ℕ, ∀ q r : ℕ, Odd q → q < 2^r → ¬ IsPrimePow q →
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = q ∧ Group.IsSolvable G ∧ ¬ Group.IsNilpotent G ∧ ¬ IsZGroup G ∧
        (∀ p : ℕ, p.Prime → ∀ P : Sylow p G, IsMulCommutative P)}).ncard ≤
      2^(E*(r+1)^2) * ∏ p ∈ q.primeFactors, g (p^q.factorization p)

def H2 : Prop :=
  ∃ E : ℕ, ∀ q r : ℕ, Odd q → q < 2^r → ¬ IsPrimePow q →
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

theorem main : H1 → H2 → OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1_H2_R1_H3_R2.H2 := by
  classical
  rintro ⟨A, hA⟩ ⟨B, hB⟩
  let D := max 1 (max A B)
  refine ⟨D+2, fun q r odd hr => ?_⟩
  by_cases hpp : IsPrimePow q
  · exact (prime_power_count hpp).trans (Nat.le_mul_of_pos_left _ (Nat.pow_pos (by decide)))
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
  have aa := (hA q r odd hr hpp).trans (mono _ D ((le_max_left A B).trans (le_max_right ..)))
  have bb := (hB q r odd hr hpp).trans (mono _ D ((le_max_right A B).trans (le_max_right ..)))
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
