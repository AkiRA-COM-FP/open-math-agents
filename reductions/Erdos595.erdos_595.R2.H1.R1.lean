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

end OMA.R_Erdos595_erdos_595_R2_H1_R1
