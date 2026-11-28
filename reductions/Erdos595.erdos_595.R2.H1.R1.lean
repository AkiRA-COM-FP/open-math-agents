import OMAReductions.R_Erdos595_erdos_595_R2
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Filter.Ultrafilter.Defs

-- Credit: @wispiANt
namespace OMA.R_Erdos595_erdos_595_R2_H1_R1

open SimpleGraph Filter

/-- In a product of finite edge sets, call a triple a triangle if it is a
triangle at every coordinate beyond some finite set. Seek a product in
which every countable colouring makes one of these triangles monochromatic. -/
def H1 : Prop :=
  ∃ (I : Type) (n : Finset I → ℕ) (G : (s : Finset I) → SimpleGraph (Fin (n s))),
    (∀ s, (G s).CliqueFree 4) ∧
    ∀ d : ((s : Finset I) → (G s).edgeSet) → ℕ,
      ∃ a b c, d a = d b ∧ d a = d c ∧ ∀ᶠ s in (atTop : Filter (Finset I)),
        ∃ x y z : Fin (n s), (a s : Sym2 _) = s(x,y) ∧
          (b s : Sym2 _) = s(y,z) ∧ (c s : Sym2 _) = s(z,x)

/-- Every finite family of eventual triangle constraints in a product
admits a single evaluation preserving all the constraints at once. -/
def H2 : Prop :=
  ∀ (I X : Type) (P : Finset I → X → X → X → Prop) (S : Finset X),
    ∃ s : Finset I, ∀ a b c : S,
      (∀ᶠ t in (atTop : Filter (Finset I)), P t a b c) → P s a b c

theorem common_coordinate : H2 := by
  classical
  intro I X P S
  apply Filter.Eventually.exists (f := (atTop : Filter (Finset I)))
  apply eventually_all.mpr
  intro a
  apply eventually_all.mpr
  intro b
  apply eventually_all.mpr
  intro c
  by_cases h : ∀ᶠ t in (atTop : Filter (Finset I)), P t a b c
  · exact h.mono fun _ hp _ => hp
  · exact .of_forall fun _ hf => (h hf).elim

theorem main : H1 → H2 → OMA.R_Erdos595_erdos_595_R2.H1 := by
  classical
  rintro ⟨I,n,G,free,hard⟩ simultaneous
  let X := (s : Finset I) → (G s).edgeSet
  let P := fun (s : Finset I) (a b c : X) =>
    ∃ x y z : Fin (n s), (a s : Sym2 _) = s(x,y) ∧ (b s : Sym2 _) = s(y,z) ∧
      (c s : Sym2 _) = s(z,x)
  let T := fun a b c => ∀ᶠ s in (atTop : Filter (Finset I)), P s a b c
  refine ⟨X,T,?_,?_⟩
  · intro d
    obtain ⟨a,b,c,e,f,t⟩ := hard d
    exact ⟨a,b,c,t,e,f⟩
  · intro S
    obtain ⟨s,hs⟩ := simultaneous I X P S
    exact ⟨n s,G s,free s,fun a => a.val s,hs⟩

/-- Anchor every finite realization at one label to obtain a default edge.
Each label is eventually present, so all its triangle constraints survive. -/
theorem from_finite_realizations : OMA.R_Erdos595_erdos_595_R2.H1 → H1 := by
  classical
  rintro ⟨X,T,hard,localize⟩
  obtain ⟨anchor,_,_,_⟩ := hard (fun _ => 0)
  choose n G free e realizes using fun s : Finset X => localize (insert anchor s)
  let label (a : X) (s : Finset X) : (G s).edgeSet :=
    e s (if h : a ∈ insert anchor s then ⟨a,h⟩ else ⟨anchor,Finset.mem_insert_self _ _⟩)
  refine ⟨X,n,G,free,?_⟩
  intro d
  obtain ⟨a,b,c,t,ab,ac⟩ := hard fun x => d (label x)
  refine ⟨label a,label b,label c,ab,ac,?_⟩
  filter_upwards [Filter.eventually_finset_mem_atTop a, Filter.eventually_finset_mem_atTop b,
    Filter.eventually_finset_mem_atTop c] with s ha hb hc
  have ua := Finset.mem_insert_of_mem (b := anchor) ha
  have ub := Finset.mem_insert_of_mem (b := anchor) hb
  have uc := Finset.mem_insert_of_mem (b := anchor) hc
  simpa only [label,dif_pos ua,dif_pos ub,dif_pos uc] using
    realizes s ⟨a,ua⟩ ⟨b,ub⟩ ⟨c,uc⟩ t

/-- Uniformly bounded palettes on even a cofinal selection of factors colour
the eventual product. Consequently, in a hard product, for every fixed k
all sufficiently late factors already force a monochromatic k-colour test. -/
theorem bounded_palette {I : Type} {A : Finset I → Type}
    (R : (s : Finset I) → A s → A s → A s → Prop) (k : ℕ)
    (cofinal : ∀ t : Finset I, ∃ s, t ⊆ s ∧ ∃ p : A s → Fin k,
      ∀ a b c, R s a b c → p a = p b → p a = p c → False) :
    ∃ d : ((s : Finset I) → A s) → Fin k, ∀ a b c,
      (∀ᶠ s in (atTop : Filter (Finset I)), R s (a s) (b s) (c s)) →
      d a = d b → d a = d c → False := by
  classical
  choose next ext p good using cofinal
  let U := Ultrafilter.of (atTop : Filter (Finset I))
  have pick (a : (s : Finset I) → A s) :
      ∃ i : Fin k, ∀ᶠ t : Finset I in U, p t (a (next t)) = i := by
    by_contra! h
    obtain ⟨t,miss⟩ := (eventually_all.mpr h).exists
    exact miss _ rfl
  choose d selected using pick
  refine ⟨d,?_⟩
  intro a b c tri ab ac
  obtain ⟨base,tail⟩ := Filter.eventually_atTop.mp tri
  have late : ∀ᶠ t : Finset I in U, base ≤ t :=
    Ultrafilter.of_le _ (Filter.eventually_ge_atTop base)
  obtain ⟨t,ht,ha,hb,hc⟩ := (late.and ((selected a).and ((selected b).and (selected c)))).exists
  exact good t _ _ _ (tail _ (ht.trans (ext t)))
    (ha.trans (ab.trans hb.symm)) (ha.trans (ac.trans hc.symm))


private theorem free_of_top_hom {V : Type} {G : SimpleGraph V} (free : G.CliqueFree 4)
    (f : Fin 4 → V) (edges : ∀ i j, i ≠ j → G.Adj (f i) (f j)) : False := by
  let hom : completeGraph (Fin 4) →g G := ⟨f,fun {i j} h => edges i j h⟩
  have inj : Function.Injective f := fun i j eq => by
    by_contra ne
    exact (edges i j ne).ne eq
  exact (cliqueFree_iff.mp free).false (hom.toCopy inj)

/-- One finite universal host for each size: take the disjoint union of
all four-clique-free graphs on the prescribed number of vertices. -/
theorem universal_factors :
    ∃ (u : ℕ → ℕ) (U : (m : ℕ) → SimpleGraph (Fin (u m))),
      (∀ m, (U m).CliqueFree 4) ∧ ∀ m (K : SimpleGraph (Fin (2*(m+1)))),
        K.CliqueFree 4 → Nonempty (K ↪g U m) := by
  classical
  suffices h : ∀ m : ℕ, ∃ (n : ℕ) (G : SimpleGraph (Fin n)), G.CliqueFree 4 ∧
      ∀ K : SimpleGraph (Fin (2*(m+1))), K.CliqueFree 4 → Nonempty (K ↪g G) by
    choose u U free inc using h
    exact ⟨u,U,free,inc⟩
  intro m
  let B := Fin (2*(m+1))
  let W := {K : SimpleGraph B // K.CliqueFree 4} × B
  let num := Fintype.equivFin W
  let G : SimpleGraph W := {
    Adj := fun a b => a.1 = b.1 ∧ a.1.val.Adj a.2 b.2
    symm := ⟨fun {a b} e => ⟨e.1.symm,e.1 ▸ e.2.symm⟩⟩
    loopless := ⟨fun _ e => e.2.ne rfl⟩ }
  refine ⟨_, G.comap num.symm,?_,?_⟩
  · rw [cliqueFree_iff,isEmpty_iff]
    intro copy
    let v (i : Fin 4) : W := num.symm (copy i)
    have adj (i j : Fin 4) (ne : i ≠ j) : G.Adj (v i) (v j) := copy.toHom.map_adj ne
    have tag (i : Fin 4) : (v 0).1 = (v i).1 := by
      by_cases eq : 0 = i
      · rw [eq]
      · exact (adj _ _ eq).1
    apply free_of_top_hom (v 0).1.property (fun i => (v i).2)
    intro i j ne
    rw [tag i]
    exact (adj i j ne).2
  · intro K free
    let add (i : B) : W := (⟨K,free⟩,i)
    refine ⟨{ toFun := fun i => num (add i)
              inj' := fun i j eq => congrArg Prod.snd (num.injective eq)
              map_rel_iff' := ?_ }⟩
    intro i j
    change G.Adj (num.symm (num (add i))) (num.symm (num (add j))) ↔ K.Adj i j
    simp [G,add]

/-- Any such fixed family works if the finite-realization step holds.
Only the index set varies. At a coordinate of size m at most m+1 labels
(including a default edge) contribute endpoints. -/
theorem fixed_factors_iff (u : ℕ → ℕ) (U : (m : ℕ) → SimpleGraph (Fin (u m)))
    (free : ∀ m, (U m).CliqueFree 4)
    (inc : ∀ m (K : SimpleGraph (Fin (2*(m+1)))), K.CliqueFree 4 → Nonempty (K ↪g U m)) :
    OMA.R_Erdos595_erdos_595_R2.H1 ↔
      ∃ I : Type, ∀ d : ((s : Finset I) → (U s.card).edgeSet) → ℕ,
        ∃ a b c, d a = d b ∧ d a = d c ∧ ∀ᶠ s in (atTop : Filter (Finset I)),
          ∃ x y z : Fin (u s.card), (a s : Sym2 _) = s(x,y) ∧
            (b s : Sym2 _) = s(y,z) ∧ (c s : Sym2 _) = s(z,x) := by
  classical
  constructor
  · rintro ⟨X,T,hard,localize⟩
    obtain ⟨anchor,_,_,_⟩ := hard (fun _ => 0)
    have atSize (s : Finset X) :
        ∃ e : ↥(insert anchor s : Finset X) → (U s.card).edgeSet,
          ∀ a b c, T a.val b.val c.val →
            ∃ x y z : Fin (u s.card), (e a : Sym2 (Fin (u s.card))) = s(x,y) ∧ (e b : Sym2 (Fin (u s.card))) = s(y,z) ∧ (e c : Sym2 (Fin (u s.card))) = s(z,x) := by
      let L := insert anchor s
      obtain ⟨n,G,legal,e,test⟩ := localize L
      let B := Fin (2*(s.card+1))
      have size : Fintype.card (↥L × Bool) ≤ Fintype.card B := by
        simp only [Fintype.card_prod,Fintype.card_bool,Fintype.card_coe,Fintype.card_fin,B]
        have := Finset.card_insert_le anchor s
        dsimp [L]
        omega
      obtain ⟨slot⟩ := Function.Embedding.nonempty_of_card_le size
      let endpoint (p : ↥L × Bool) := if p.2 then (e p.1).val.out.2 else (e p.1).val.out.1
      let : Nonempty (↥L × Bool) := ⟨⟨⟨anchor,Finset.mem_insert_self _ _⟩,false⟩⟩
      let pt (b : B) := endpoint (Function.invFun slot b)
      have hit (p : ↥L × Bool) : pt (slot p) = endpoint p :=
        congrArg endpoint (Function.leftInverse_invFun slot.injective p)
      let code (i : Fin n) : B := if h : ∃ b, pt b = i then h.choose else 0
      have decode (p : ↥L × Bool) : pt (code (endpoint p)) = endpoint p := by
        have h : ∃ b, pt b = endpoint p := ⟨_,hit p⟩
        simpa only [code,dif_pos h] using h.choose_spec
      let K := G.comap pt
      have kfree : K.CliqueFree 4 := by
        rw [cliqueFree_iff,isEmpty_iff]
        intro f
        exact free_of_top_hom legal (fun i => pt (f i)) (fun _ _ ne => f.toHom.map_adj ne)
      let embed := (inc s.card K kfree).some
      let v := fun i => embed (code i)
      have edge (a : ↥L) : Sym2.map v (e a).val ∈ (U s.card).edgeSet := by
        let r := (e a).val.out
        have eq : s(r.1,r.2) = (e a).val := (e a).val.out_eq
        rw [← eq]
        apply embed.map_rel_iff.mpr
        change G.Adj (pt (code r.1)) (pt (code r.2))
        rw [show pt (code r.1) = r.1 from decode (a,false),
            show pt (code r.2) = r.2 from decode (a,true), ← SimpleGraph.mem_edgeSet,eq]
        exact (e a).property
      refine ⟨fun a => ⟨_,edge a⟩,?_⟩
      intro a b c h
      obtain ⟨x,y,z,ab,bc,ca⟩ := test a b c h
      exact ⟨v x,v y,v z,congrArg (Sym2.map v) ab,congrArg (Sym2.map v) bc,congrArg (Sym2.map v) ca⟩
    choose e test using atSize
    let label (a : X) (s : Finset X) := e s
      (if h : a ∈ insert anchor s then ⟨a,h⟩ else ⟨anchor,Finset.mem_insert_self _ _⟩)
    refine ⟨X,?_⟩
    intro d
    obtain ⟨a,b,c,h,ab,ac⟩ := hard fun x => d (label x)
    refine ⟨label a,label b,label c,ab,ac,?_⟩
    filter_upwards [Filter.eventually_finset_mem_atTop a, Filter.eventually_finset_mem_atTop b,
      Filter.eventually_finset_mem_atTop c] with s ha hb hc
    have ma := Finset.mem_insert_of_mem (b := anchor) ha
    have mb := Finset.mem_insert_of_mem (b := anchor) hb
    have mc := Finset.mem_insert_of_mem (b := anchor) hc
    simpa only [label,dif_pos ma,dif_pos mb,dif_pos mc] using test s ⟨a,ma⟩ ⟨b,mb⟩ ⟨c,mc⟩ h
  · rintro ⟨I,h⟩
    exact main ⟨I,fun s => u s.card,fun s => U s.card,fun s => free s.card,h⟩ common_coordinate


/-- A binary cut on the ultrafilter classes of a finite list of vertex
sequences agrees, at almost every coordinate, with an actual vertex cut. -/
private theorem realize_cut {J : Type} (U : Ultrafilter J)
    (bit : (J → ℕ) → Bool)
    (same : ∀ f g, (f =ᶠ[U] g) → bit f = bit g) (S : Finset (J → ℕ)) :
    ∀ᶠ j in U, ∃ cut : ℕ → Bool, ∀ f ∈ S, cut (f j) = bit f := by
  classical
  have pair (f g : J → ℕ) : ∀ᶠ j in U, f j = g j → bit f = bit g := by
    by_cases eq : bit f = bit g
    · exact .of_forall fun _ _ => eq
    · have ne : ¬ f =ᶠ[U] g := fun h => eq (same f g h)
      exact (Ultrafilter.eventually_not.mpr ne).mono fun _ hn he => (hn he).elim
  have all : ∀ᶠ j in U, ∀ f ∈ S, ∀ g ∈ S, f j = g j → bit f = bit g :=
    S.eventually_all.mpr fun f _ => S.eventually_all.mpr fun g _ => pair f g
  filter_upwards [all] with j ok
  refine ⟨fun v => decide (∃ g ∈ S, g j = v ∧ bit g = true),?_⟩
  intro f hf
  cases h : bit f with
  | false =>
    apply decide_eq_false
    rintro ⟨g,hg,e,b⟩
    exact Bool.noConfusion (b.symm.trans ((ok g hg f hf e).trans h))
  | true => exact decide_eq_true ⟨f,hf,rfl,h⟩

/-- Countably many coordinates admit a countable colouring avoiding every
eventual triangle, even for an arbitrary proper filter and arbitrary factors
on finite ordinal vertex sets. Thus finite Ramsey strength is insufficient
on a countable index set in the fixed-factor criterion. -/
theorem countable_coordinates {J : Type} [Countable J] (l : Filter J) [NeBot l]
    (n : J → ℕ) (G : (j : J) → SimpleGraph (Fin (n j))) :
    ∃ d : ((j : J) → (G j).edgeSet) → ℕ, ∀ a b c, d a = d b → d a = d c →
      ¬ ∀ᶠ j in l, ∃ x y z : Fin (n j), (a j : Sym2 _) = s(x,y) ∧
        (b j : Sym2 _) = s(y,z) ∧ (c j : Sym2 _) = s(z,x) := by
  classical
  let U := Ultrafilter.of l
  let rel : Setoid (J → ℕ) := {
    r := EventuallyEq U
    iseqv := ⟨EventuallyEq.refl _, EventuallyEq.symm, EventuallyEq.trans⟩ }
  let rep (f : J → ℕ) : J → ℕ := (Quotient.mk rel f).out
  have sound (f : J → ℕ) : rep f =ᶠ[U] f :=
    Quotient.exact (Quotient.out_eq (Quotient.mk rel f))
  have stable {f g : J → ℕ} (h : f =ᶠ[U] g) : rep f = rep g :=
    congrArg Quotient.out (Quotient.sound (s := rel) h)
  let E := (j : J) → (G j).edgeSet
  let L (a : E) (j : J) := ((a j).val.out.1 : ℕ)
  let R (a : E) (j : J) := ((a j).val.out.2 : ℕ)
  have sep (a : E) : ∃ j, rep (L a) j ≠ rep (R a) j := by
    by_contra! h
    have eq := funext h
    have lr : L a =ᶠ[U] R a := (sound _).symm.trans (eq ▸ sound (R a))
    obtain ⟨j,ej⟩ := lr.exists
    have edge := (a j).property
    rw [← (a j).val.out_eq] at edge
    exact (show (G j).Adj (a j).val.out.1 (a j).val.out.2 from edge).ne (Fin.ext ej)
  choose index diff using sep
  let key (a : E) := (index a, rep (L a) (index a))
  obtain ⟨enc,inj⟩ := Countable.exists_injective_nat (J × ℕ)
  refine ⟨fun a => enc (key a),?_⟩
  intro a b c ab ac tri
  have kb := inj ab
  have kc := inj ac
  let bit (v : J → ℕ) := decide (rep v (key a).1 = (key a).2)
  have opposite (p : E) (k : key p = key a) : bit (L p) ≠ bit (R p) := by
    simp only [bit,← k]
    simp [key,Ne.symm (diff p)]
  let S : Finset (J → ℕ) := {L a,R a,L b,R b,L c,R c}
  have realize := realize_cut U bit (fun f g h => by simp only [bit,stable h]) S
  obtain ⟨j,⟨cut,hcut⟩,x,y,z,xy,yz,zx⟩ := (realize.and (Ultrafilter.of_le _ tri)).exists
  have side (p : E) (hl : L p ∈ S) (hr : R p ∈ S) (k : key p = key a)
      (v w : Fin (n j)) (edge : (p j).val = s(v,w)) : cut v ≠ cut w := by
    have ne : cut (L p j) ≠ cut (R p j) := by rw [hcut _ hl,hcut _ hr]; exact opposite p k
    have oriented : s((p j).val.out.1,(p j).val.out.2) = s(v,w) := (p j).val.out_eq.trans edge
    rcases Sym2.eq_iff.mp oriented with h | h
    · simpa only [L,R,h.1,h.2] using ne
    · simpa only [L,R,h.1,h.2] using ne.symm
  have A := side a (by simp [S]) (by simp [S]) rfl x y xy
  have B := side b (by simp [S]) (by simp [S]) kb.symm y z yz
  have C := side c (by simp [S]) (by simp [S]) kc.symm z x zx
  revert A B C
  cases cut x <;> cases cut y <;> cases cut z <;> decide

/-- Every witness in the product reduction requires an uncountable index set. -/
theorem uncountable_index {I : Type} (n : Finset I → ℕ)
    (G : (s : Finset I) → SimpleGraph (Fin (n s)))
    (hard : ∀ d : ((s : Finset I) → (G s).edgeSet) → ℕ,
      ∃ a b c, d a = d b ∧ d a = d c ∧ ∀ᶠ s in (atTop : Filter (Finset I)),
        ∃ x y z : Fin (n s), (a s : Sym2 _) = s(x,y) ∧
          (b s : Sym2 _) = s(y,z) ∧ (c s : Sym2 _) = s(z,x)) : ¬ Countable I := by
  intro small
  let _ : Countable I := small
  obtain ⟨d,avoids⟩ := countable_coordinates atTop n G
  obtain ⟨a,b,c,ab,ac,triangle⟩ := hard d
  exact avoids a b c ab ac triangle

end OMA.R_Erdos595_erdos_595_R2_H1_R1
