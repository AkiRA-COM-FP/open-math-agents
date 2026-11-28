import FormalConjectures.Paper.BurningNumberConjecture
import Mathlib

/-!
A proof of the asymptotic burning-number bound of Norin and Turcotte.

A diameter path gives each vertex of a tree a position and a height.
Counting vertices above the path gives one- and two-ball covers of small
pieces. For fixed nonnegative prices on radius intervals, choose the
radius that minimises cumulative price divided by squared radius. The
resulting cover has bounded price and uses a bounded number of balls.
A sum of squared deviations selects covers whose radii fit into distinct
ignition rounds.
-/

namespace BurningNumberConjecture.Proof
section
open SimpleGraph
lemma path_dist {V : Type} {G : SimpleGraph V} (hG : G.IsTree)
    {a b : V} {p : G.Walk a b} (hp : p.IsPath) : p.length = G.dist a b := by
  obtain ⟨q,hq,e⟩ := hG.connected.exists_path_of_dist a b
  rwa [(hG.existsUnique_path _ _).unique hp hq]

end
section
open SimpleGraph
variable {V : Type} {G : SimpleGraph V}
lemma frontier (S : Set V) {u v : V} (p : G.Walk u v) (hu : u ∈ S) (hv : v ∉ S) :
    ∃ a ∈ S, ∃ b ∉ S, G.Adj a b := by
  induction p with
  | nil => exact (hv hu).elim
  | @cons u v w e p ih =>
    by_cases h : v ∈ S
    · exact ih h hv
    · exact ⟨_,hu,_,h,e⟩

end

section
open SimpleGraph

variable {V : Type} [Fintype V] {G : SimpleGraph V} {x y : V}

def Tag (G : SimpleGraph V) (x y v : V) (d i h : ℕ) : Prop :=
  i ≤ d ∧ G.dist x v = i+h ∧ G.dist y v = d-i+h

lemma Tag.unique {v : V} {d i h j k : ℕ} (a : Tag G x y v d i h)
    (b : Tag G x y v d j k) : (i,h) = (j,k) := by unfold Tag at *; congr 1 <;> omega

lemma tag_getVert (ht : G.IsTree) {p : G.Walk x y} (hp : p.IsPath) {i : ℕ} (hi : i ≤ p.length) :
    Tag G x y (p.getVert i) p.length i 0 := by
  simpa [Tag,hi,Walk.take_length,Walk.drop_length,Nat.min_eq_left hi] using
    And.intro (path_dist ht (hp.take i)).symm (path_dist ht (hp.drop i).reverse).symm

/-- A point attaching to a diameter path at index i and height h has
witnesses of all heights below h at that same index. -/
theorem coordinates (ht : G.IsTree) (p : G.Walk x y) (hp : p.IsPath) :
    ∀ v, ∃ i h, Tag G x y v p.length i h ∧ G.dist (p.getVert i) v ≤ h ∧
      ∀ k ≤ h, ∃ w, Tag G x y w p.length i k := by
  classical
  intro v
  obtain ⟨q,hq⟩ := ht.connected.exists_isPath v x
  induction q with
  | @nil u =>
    have tag := tag_getVert ht hp (i := 0) (by omega)
    simp only [Walk.getVert_zero] at tag
    exact ⟨0,0,tag,by simp,fun k hk => ⟨u,by simpa [show k=0 by omega] using tag⟩⟩
  | @cons v u x e q ih =>
    by_cases hv : v ∈ p.support
    · obtain ⟨i,eq,hi⟩ := Walk.mem_support_iff_exists_getVert.mp hv
      have tag := tag_getVert ht hp hi
      rw [eq] at tag
      exact ⟨i,0,tag,by simp [eq],fun k hk => ⟨v,by simpa [show k=0 by omega] using tag⟩⟩
    obtain ⟨hq',fresh⟩ := (Walk.cons_isPath_iff _ _).mp hq
    obtain ⟨i,h,⟨hi,hx,hy⟩,hd,chain⟩ := ih p hp hq'
    let b := (p.reverse.append q.reverse).toPath
    have hb := b.prop.concat (fun hw => ?_) e.symm
    case refine_1 =>
      have := (p.reverse.append q.reverse).support_toPath_subset_support hw
      simp_all [Walk.mem_support_append_iff]
    have tag : Tag G x y v p.length i (h+1) := by
      have h1 := path_dist ht hq.reverse
      have h2 := path_dist ht hq'.reverse
      have h3 := path_dist ht hb
      simp only [Walk.length_reverse,Walk.length_cons,Walk.length_concat,path_dist ht b.prop] at h1 h2 h3
      unfold Tag; omega
    exact ⟨i,h+1,tag,ht.connected.dist_triangle.trans (Nat.add_le_add hd
      (dist_eq_one_iff_adj.mpr e.symm).le),fun k hk => by
        by_cases eq : k=h+1
        · exact ⟨_,eq ▸ tag⟩
        · exact chain k (by omega)⟩

end

section
open SimpleGraph
variable {V : Type} [Fintype V]

/- Count the diameter path and the two vertical columns above distinct positions. -/
private lemma three_ranges (tag : V → ℕ × ℕ) {d H z i j : ℕ} (sep : i=j → z=0)
    (p : Fin (d+1) → V) (a : Fin H → V) (b : Fin z → V)
    (hp : ∀ n, tag (p n) = (n.val,0)) (ha : ∀ n, tag (a n) = (i,n.val+1))
    (hb : ∀ n, tag (b n) = (j,n.val+1)) : d+H+z+1 ≤ Fintype.card V := by
  let f : Fin (d+1) ⊕ (Fin H ⊕ Fin z) → V := Sum.elim p (Sum.elim a b)
  have inj : Function.Injective f := by
    intro x y h
    have hh := congrArg tag h
    rcases x with x | x | x <;> rcases y with y | y | y <;>
      simp [f,hp,ha,hb] at hh ⊢ <;> first | exact Fin.ext (by omega) | grind
  have := Fintype.card_le_of_injective _ inj
  simp at this
  omega

theorem spine_data {G : SimpleGraph V} (ht : G.IsTree) :
    ∃ (x y : V) (p : G.Walk x y) (I H z : ℕ) (j h : V → ℕ) (tip : V),
      H ≤ I ∧ I+H ≤ p.length ∧ z ≤ H ∧ p.length+H+z+1 ≤ Fintype.card V ∧
      G.dist x y = p.length ∧ G.dist x tip = I+H ∧ G.dist y tip = p.length-I+H ∧
      ∀ v, h v ≤ j v ∧ j v+h v ≤ p.length ∧ G.dist (p.getVert (j v)) v ≤ h v ∧
        (j v = I ∧ h v ≤ H ∨ h v ≤ z) := by
  classical
  let _ := ht.connected.nonempty
  obtain ⟨x,y,hd⟩ := G.exists_dist_eq_diam
  obtain ⟨p,path,plen⟩ := ht.connected.exists_path_of_dist x y
  choose j h tag dist chain using coordinates ht p path
  have bounds (v) : h v ≤ j v ∧ j v + h v ≤ p.length := by
    have left := G.dist_le_diam (G.connected_iff_ediam_ne_top.mp ht.connected) (u := x) (v := v)
    have right := G.dist_le_diam (G.connected_iff_ediam_ne_top.mp ht.connected) (u := y) (v := v)
    obtain ⟨_,_,_⟩ := tag v
    omega
  obtain ⟨u,_,hu⟩ := Finset.exists_max_image Finset.univ h Finset.univ_nonempty
  let z := min (h u) (Fintype.card V-(p.length+h u+1))
  have points (v : V) (k : ℕ) (hk : k ≤ h v) : ∃ t, (j t,h t) = (j v,k) := by
    obtain ⟨t,ht⟩ := chain v k hk
    exact ⟨t,(tag t).unique ht⟩
  choose a ha using fun n : Fin (h u) => points u (n+1) n.isLt
  have on (k : Fin (p.length+1)) : (j (p.getVert k),h (p.getVert k)) = (k.val,0) := by
    exact (tag _).unique (tag_getVert ht path (by omega))
  have pack (v) (s : ℕ) (hs : s ≤ h v) (sep : j u = j v → s=0) : p.length+h u+s+1 ≤ Fintype.card V := by
    choose b hb using fun n : Fin s => points v (n+1) (n.isLt.trans_le hs)
    exact three_ranges (fun v => (j v,h v)) sep (fun n => p.getVert n) a b on ha hb
  have base := pack u 0 (Nat.zero_le _) (fun _ => rfl)
  obtain ⟨_,e₁,e₂⟩ := tag u
  refine ⟨x,y,p,j u,h u,z,j,h,u,(bounds u).1,(bounds u).2,min_le_left ..,by dsimp [z]; omega,
    plen.symm,e₁,e₂,fun v => ⟨(bounds v).1,(bounds v).2,dist v,?_⟩⟩
  by_cases he : j v = j u
  · exact Or.inl ⟨he,hu _ (by simp)⟩
  · exact Or.inr (le_min (hu _ (by simp)) (by have := pack v (h v) le_rfl (by tauto); omega))

end

section
open SimpleGraph BurningNumberConjecture

/- Rounding a position on a path down to a vertex costs at most one round.
The reduced distance records this allowance; the scheduler restores it. -/
variable {V : Type} {T : SimpleGraph V}

noncomputable def cost (T : SimpleGraph V) (u v : V) : ℝ := (T.dist u v : ℝ)-1

theorem centre_on_walk {a b : V} (p : T.Walk a b) (hc : T.Connected) (x : ℝ) :
    ∃ c : V, ∀ j : ℕ, ∀ w : V,
      cost T c w ≤ |x - j| + T.dist (p.getVert j) w := by
  have seg {i j : ℕ} (h : i ≤ j) : (T.dist (p.getVert i) (p.getVert j) : ℝ) ≤ (j : ℝ)-i := by
    let q := (p.drop i).take (j-i)
    have eq : (p.drop i).getVert (j-i) = p.getVert j := by rw [p.drop_getVert, Nat.add_sub_of_le h]
    rw [← Nat.cast_sub h, ← eq]
    exact_mod_cast (dist_le q).trans (show q.length ≤ j-i by simp [q, Walk.take_length])
  have move (i j : ℕ) (v : V) :
      (T.dist (p.getVert i) v : ℝ) ≤ |(i : ℝ)-j| + T.dist (p.getVert j) v := by
    have dom (a b : ℕ) : (T.dist (p.getVert a) (p.getVert b) : ℝ) ≤ |(a:ℝ)-b| := by
      wlog h : a ≤ b generalizing a b
      · rw [SimpleGraph.dist_comm,abs_sub_comm]; exact this _ _ (by omega)
      rw [abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast h)),neg_sub]
      exact seg h
    exact (Nat.cast_le (α := ℝ)).mpr hc.dist_triangle |>.trans (by push_cast; linarith [dom i j])
  let n := ⌊x⌋₊
  refine ⟨p.getVert n, fun j w => ?_⟩
  have step := move n j w
  change (T.dist (p.getVert n) w : ℝ)-1 ≤ _
  by_cases hx : 0 ≤ x
  · have lo : (n:ℝ) ≤ x := Nat.floor_le hx
    have hi : x < (n:ℝ)+1 := Nat.lt_floor_add_one x
    grind [abs_eq_max_neg]
  · have hn : n = 0 := Nat.floor_eq_zero.mpr (by linarith)
    rw [hn,Nat.cast_zero] at step
    rw [hn]
    grind [abs_eq_max_neg]

end

section
open SimpleGraph
variable {V : Type} {G : SimpleGraph V}
lemma two_parts_bound {X Y : Set V} {d : ℕ} {u v w : V}
    (hx : ∀ a ∈ X, ∀ b ∈ X, G.dist a b ≤ d)
    (hy : ∀ a ∈ Y, ∀ b ∈ Y, G.dist a b ≤ d)
    (hu : u ∈ X ∪ Y) (hv : v ∈ X ∪ Y) (hw : w ∈ X ∪ Y) :
    G.dist u v ≤ d ∨ G.dist u w ≤ d ∨ G.dist v w ≤ d := by
  rcases hu with h|h <;> rcases hv with h'|h' <;> rcases hw with h''|h'' <;> grind

end
section
open SimpleGraph

/- The physical parameters needed to apply the normalized local profile. -/
def HasPieceProfiles {V W : Type} (dist : W → V → ℝ) (l L : ℝ) : Prop :=
  ∃ m B : ℝ, 0 ≤ m ∧ m ≤ l/2 ∧ B ≤ 2*m ∧ 2*m+B = L ∧
    (∃ u : W, ∀ v, dist u v ≤ B) ∧
    (∀ t ≥ m, ∀ s ≥ 0, B ≤ s+t →
      ∃ u w : W, ∀ v, dist u v ≤ s ∨ dist w v ≤ t)

/- A finite tree covered by two sets of diameter at most l has the physical
one/two-ball profiles at any L between its edge count and 2l. -/
end

section
open SimpleGraph

inductive Branch {V : Type} (G : SimpleGraph V) : V → Type
  | root (v : V) : Branch G v
  | join {u v : V} (e : G.Adj u v) (a : Branch G u) (b : Branch G v) : Branch G u

variable {V : Type} {G : SimpleGraph V} {r : V}

def Branch.size : {r : V} → Branch G r → ℕ
  | _, .root _ => 0
  | _, .join _ a b => a.size+b.size+1

def Branch.vertices [DecidableEq V] : {r : V} → Branch G r → Finset V
  | r, .root _ => {r}
  | _, .join _ a b => a.vertices ∪ b.vertices

lemma Branch.root_mem [DecidableEq V] (t : Branch G r) : r ∈ t.vertices := by
  induction t <;> simp_all [vertices]

lemma Branch.card [DecidableEq V] (t : Branch G r) : t.vertices.card ≤ t.size+1 := by
  induction t with
  | root => simp [vertices,size]
  | join e a b ha hb =>
    exact (Finset.card_union_le ..).trans (by dsimp [size]; omega)

lemma Branch.connected [DecidableEq V] (t : Branch G r) :
    (G.induce (↑t.vertices : Set V)).Connected := by
  induction t with
  | root v => rw [connected_iff_exists_forall_reachable]
              refine ⟨⟨v,by simp [vertices]⟩,fun ⟨w,hw⟩ => ?_⟩
              obtain rfl : w = v := by simpa [vertices] using hw
              exact Reachable.rfl
  | join e a b ha hb =>
    rw [show (↑(join e a b).vertices : Set V) = ↑a.vertices ∪ ↑b.vertices by ext; simp [vertices]]
    exact connected_induce_union ha.preconnected hb.preconnected a.root_mem b.root_mem e

lemma Branch.dist_le [DecidableEq V] (t : Branch G r) {u v : V} (hu : u ∈ t.vertices)
    (hv : v ∈ t.vertices) : G.dist u v ≤ t.size := by
  classical
  obtain ⟨p,hp⟩ := t.connected.exists_isPath ⟨u,hu⟩ ⟨v,hv⟩
  have h := hp.length_lt
  have num : Fintype.card (↑t.vertices : Set V) = t.vertices.card := Fintype.card_coe _
  rw [num] at h
  have hd := SimpleGraph.dist_le (p.map (Embedding.induce _).toHom)
  simp only [Walk.length_map] at hd
  exact hd.trans (by have := t.card; omega)

def Minimal [DecidableEq V] (l : ℕ) (t : Σ r, Branch G r) : Prop :=
  l ≤ t.2.size ∧ t.2.size ≤ 2*l ∧ ∀ x ∈ t.2.vertices, ∀ y ∈ t.2.vertices, ∀ z ∈ t.2.vertices,
    G.dist x y ≤ l ∨ G.dist x z ≤ l ∨ G.dist y z ≤ l

end
section
open SimpleGraph

/- A connected induced subgraph of a tree contains its ambient geodesics. -/
theorem tree_induce_dist {V : Type} {G : SimpleGraph V} (ht : G.IsTree)
    {S : Set V} (hc : (G.induce S).Connected) (x y : S) :
    (G.induce S).dist x y = G.dist x.val y.val := by
  obtain ⟨p,hp,hd⟩ := (hc x y).exists_path_of_dist
  let f := Embedding.induce (G := G) S
  calc
    _ = p.length := hd.symm
    _ = (p.map f.toHom).length := (p.length_map _).symm
    _ = _ := path_dist ht (hp.map f.injective : (p.map f.toHom).IsPath)

/- One- and two-ball profiles for the actual fragment of the spanning-tree
decomposition. All centres and distances are in the ambient tree. -/
theorem branch_piece_profiles {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (ht : G.IsTree) {l : ℕ} (u : Σ r, Branch G r) (hu : Minimal l u) :
    HasPieceProfiles (fun (c : V) (v : (↑u.2.vertices : Set V)) => cost G c v.val) l u.2.size := by
  classical
  obtain ⟨_,hcap,close⟩ := hu
  let S : Set V := ↑u.2.vertices
  let P := G.induce S
  have hc : P.Connected := u.2.connected
  have tree : P.IsTree := ⟨hc,ht.isAcyclic.induce S⟩
  let L : ℝ := u.2.size
  have hsize : (Fintype.card S : ℝ) ≤ L+1 := by
    dsimp [L]; exact_mod_cast (show Fintype.card S ≤ u.2.size+1 from (Fintype.card_coe _).le.trans u.2.card)
  have cap : L ≤ 2*l := by dsimp [L]; exact_mod_cast hcap
  obtain ⟨x,y,p,I,H,z,j,h,u,hle,hright,hz,hcard,dxy,dx,dy,hv⟩ := spine_data tree
  have short := close x x.prop y y.prop u u.prop
  simp only [P,tree_induce_dist ht hc] at dxy dx dy
  rw [dxy,dx,dy] at short
  have short' : H + min I (p.length-I) ≤ l := by omega
  let D : ℝ := p.length
  let i : ℝ := I
  have mass : D+(H:ℝ)+z ≤ L := by
    have := Nat.cast_le (α := ℝ).mpr hcard
    dsimp [D]; push_cast at this; linarith
  have hi : (H:ℝ) ≤ i := Nat.cast_le.mpr hle
  have hj : i+(H:ℝ) ≤ D := by dsimp [i,D]; exact_mod_cast hright
  have hz' := Nat.cast_le (α := ℝ).mpr hz
  have hshort : (H:ℝ)+min i (D-i) ≤ l := by
    have := Nat.cast_le (α := ℝ).mpr short'
    push_cast [Nat.cast_sub (show I ≤ p.length by omega)] at this
    exact this
  let m := max (L/4) (((H:ℝ)+min i (D-i))/2)
  let B := L-2*m
  have head : (H:ℝ)+min i (D-i) ≤ 2*m := by dsimp [m]; grind
  have space : D/2+z ≤ B := by dsimp [B,m]; grind
  let q := p.map (Embedding.induce (G := G) S).toHom
  let centre (s : ℝ) := (centre_on_walk q ht.connected s).choose
  have bound (s : ℝ) (v : S) : cost G (centre s) v.val ≤ |s-j v|+h v := by
    apply ((centre_on_walk q ht.connected _).choose_spec (j v) v.val).trans
    apply add_le_add le_rfl
    exact_mod_cast (show G.dist (q.getVert (j v)) v.val ≤ h v by
      rw [show q.getVert (j v) = (p.getVert (j v)).val from Walk.getVert_map ..,← tree_induce_dist ht hc]
      exact (hv v).2.2.1)
  have geom (v) : (h v : ℝ) ≤ j v ∧ (j v : ℝ)+h v ≤ D := by
    obtain ⟨k,e,_⟩ := hv v
    exact ⟨by exact_mod_cast k,by dsimp [D]; exact_mod_cast e⟩
  refine ⟨m,B,?_,?_,?_,by dsimp [B]; ring,⟨centre (D/2),fun v => ?_⟩,?_⟩
  · dsimp [m]; grind
  · dsimp [m]; grind
  · dsimp [B,m]; grind
  · have := geom v; have := bound (D/2) v; grind [abs_eq_max_neg]
  intro t ht s hs hsum
  let flip (x : ℝ) := if i ≤ D-i then x else D-x
  refine ⟨centre (flip (D-(B-t))),centre (flip t),fun v => ?_⟩
  obtain ⟨_,_,_,htip | hlow⟩ := hv v
  · right
    obtain ⟨e₁,e₂⟩ := htip
    have k : (j v : ℝ) = i := by dsimp [i]; exact_mod_cast e₁
    have h := Nat.cast_le (α := ℝ).mpr e₂
    have := bound (flip t) v
    dsimp [flip] at *
    grind [abs_eq_max_neg]
  · have low := Nat.cast_le (α := ℝ).mpr hlow
    obtain ⟨lo,hi⟩ := geom v
    have right := bound (flip (D-(B-t))) v
    have left := bound (flip t) v
    clear * - low lo hi right left hsum space
    by_cases side : i ≤ D-i <;> simp [flip,side] at right left ⊢ <;>
      grind only [abs_eq_max_neg,max_def]

end
section

/- A pair of adjacent uniform intervals of nondecreasing density is a
nonnegative mixture of two uniforms ending at one, tested against arbitrary
masses of the full range and of the upper interval. -/
lemma tail_decomposition {a b : ℝ} (hab : a < b) (hb : b < 1) (h : 1-b ≤ b-a) :
    ∃ α β : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ α*(1+a)+β*(1+b) = a+2*b+1 ∧
      ∀ u v : ℝ, (u-v)/(b-a)+v/(1-b) = α*(u/(1-a))+β*(v/(1-b)) := by
  have h1 := sub_pos.mpr hab
  have h2 := sub_pos.mpr hb
  have h3 := sub_pos.mpr (hab.trans hb)
  refine ⟨(1-a)/(b-a), 1-(1-b)/(b-a), by positivity,
    sub_nonneg.mpr ((div_le_one h1).mpr h), ?_, fun u v => ?_⟩ <;> field_simp <;> ring

end
section
open SimpleGraph BurningNumberConjecture
variable {V : Type} {T : SimpleGraph V}
variable {Q : Type} (bin : Q → ℝ → ℝ)

/- A cover records its radius histogram and the number of ignition rounds it uses. -/
def Attain (T : SimpleGraph V) (S : Set V) (R B : ℝ) : Set (Q → ℝ) :=
  {x | ∃ bs : List (ℝ × V), (∀ p ∈ bs, p.1 ∈ Set.Icc 0 R) ∧
    (bs.length : ℝ) ≤ B ∧
    (∀ v ∈ S, ∃ p ∈ bs, cost T p.2 v ≤ p.1) ∧
    ∀ q, x q = (bs.map (fun p => bin q p.1)).sum}

lemma attainable_mono {S : Set V} {R B R' B' : ℝ} (hr : R ≤ R') (hb : B ≤ B') :
    Attain bin T S R B ⊆ Attain bin T S R' B' := by
  rintro x ⟨bs,hs,hcost,hcov,hist⟩
  exact ⟨bs,fun p hp => ⟨(hs p hp).1,(hs p hp).2.trans hr⟩,hcost.trans hb,hcov,hist⟩

lemma attainable_add {S Z : Set V} {R A B : ℝ} {x y : Q → ℝ}
    (hx : x ∈ Attain bin T S R A) (hy : y ∈ Attain bin T Z R B) :
    x+y ∈ Attain bin T (S ∪ Z) R (A+B) := by
  obtain ⟨xs,hxs,hxa,hxc,hxi⟩ := hx
  obtain ⟨ys,hys,hya,hyc,hyi⟩ := hy
  refine ⟨xs++ys,fun p h => (List.mem_append.mp h).elim (hxs p) (hys p),
    by simpa using add_le_add hxa hya, fun v hv => ?_, fun q => by simp [hxi,hyi]⟩
  rcases hv with h|h
  · obtain ⟨p,h,hp⟩ := hxc v h
    exact ⟨p,List.mem_append_left _ h,hp⟩
  · obtain ⟨p,h,hp⟩ := hyc v h
    exact ⟨p,List.mem_append_right _ h,hp⟩

/- A profile is attainable at every nonnegative system of bin prices. -/
def Offers {Q : Type} [Fintype Q] (C : Set (Q → ℝ)) (x : Q → ℝ) : Prop :=
  ∀ w : Q → ℝ, (∀ k, 0 ≤ w k) → ∃ y ∈ C, ∑ k, w k*y k ≤ ∑ k, w k*x k

end
section
open MeasureTheory Set
open scoped unitInterval

/- The uniform parameter on the closed unit interval has its canonical probability measure. -/
private lemma unit_mean (f : ℝ → ℝ) :
    (∫ y : I, f y) = ∫ y in (0:ℝ)..1, f y := by
  rw [integral_subtype measurableSet_Icc f, intervalIntegral.integral_of_le zero_le_one,
    setIntegral_congr_set Ioc_ae_eq_Icc]

noncomputable def bin (u v : ℝ) : ℝ → ℝ := (Ioc u v).indicator 1

/- Length of the intersection of (a,b] with the bin (u,v]. -/
def overlap (a b u v : ℝ) := max 0 (min b v - max a u)

lemma integral_bin {a b : ℝ} (hab : a ≤ b) (u v : ℝ) :
    (∫ x in a..b, bin u v x) = overlap a b u v := by
  rw [intervalIntegral.integral_of_le hab, bin, integral_indicator_one measurableSet_Ioc,
    Measure.real, Measure.restrict_apply measurableSet_Ioc, Set.inter_comm, Set.Ioc_inter_Ioc,
    Real.volume_Ioc, ENNReal.toReal_ofReal']
  exact max_comm ..

lemma bin_measurable (u v : ℝ) : Measurable (bin u v) :=
  measurable_const.indicator measurableSet_Ioc

lemma bin_mem (u v x : ℝ) : bin u v x ∈ Icc (0:ℝ) 1 := by
  by_cases h : x ∈ Ioc u v <;> simp [bin, h]

/- Both affine orientations carry the uniform parameter to the same interval law. -/
theorem affine_bin_means {a b : ℝ} (h : a < b) (u v : ℝ) :
    (∫ y : I, bin u v (a + (y:ℝ)*(b-a))) = overlap a b u v / (b-a) ∧
    (∫ y : I, bin u v (b - (y:ℝ)*(b-a))) = overlap a b u v / (b-a) := by
  have hu := intervalIntegral.integral_comp_add_mul (a := 0) (b := 1) (bin u v) (sub_ne_zero.mpr h.ne') a
  have hd := intervalIntegral.integral_comp_sub_mul (a := 0) (b := 1) (bin u v) (sub_ne_zero.mpr h.ne') b
  constructor
  · rw [unit_mean (fun y => bin u v (a + y*(b-a)))]
    simpa [mul_comm, smul_eq_mul, div_eq_mul_inv, integral_bin h.le] using hu
  · rw [unit_mean (fun y => bin u v (b - y*(b-a)))]
    simpa [mul_comm, smul_eq_mul, div_eq_mul_inv, integral_bin h.le] using hd

lemma int_bin (u v : ℝ) (g : I → ℝ) (hg : Measurable g) :
    Integrable (fun y => bin u v (g y)) volume :=
  (memLp_of_bounded (Filter.Eventually.of_forall (fun y => bin_mem u v (g y)))
    ((bin_measurable u v).comp hg).aestronglyMeasurable 1).integrable le_rfl

/- Subtract adjacent overlap lengths to use the upper-tail mixture identity. -/
theorem overlap_split {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (u v : ℝ) :
    overlap a b u v = overlap a c u v - overlap b c u v := by
  have hi : Integrable (bin u v) volume :=
    (integrable_indicator_iff measurableSet_Ioc).mpr (integrableOn_const (by simp [Real.volume_Ioc]))
  have h := intervalIntegral.integral_add_adjacent_intervals
    (a := a) (b := b) (c := c) hi.intervalIntegrable hi.intervalIntegrable
  rw [integral_bin hab, integral_bin hbc, integral_bin (hab.trans hbc)] at h
  linarith

end
section
open SimpleGraph MeasureTheory Finset Set
open scoped Pointwise unitInterval
variable {V Q : Type} [Fintype Q] {G : SimpleGraph V} (lo hi : Q → ℝ)

lemma bin_scale {R : ℝ} (hR : 0 < R) (u v t : ℝ) :
    bin u v (R*t) = bin (u/R) (v/R) t := by
  have hm : R*t ∈ Ioc u v ↔ t ∈ Ioc (u/R) (v/R) := by
    simp only [Set.mem_Ioc,div_lt_iff₀ hR,le_div_iff₀ hR,mul_comm R t]
  simp only [bin,Set.indicator,hm,Pi.one_apply]

lemma overlap_scale {R : ℝ} (hR : 0 < R) (a b u v : ℝ) :
    overlap a b (u/R) (v/R) = overlap (R*a) (R*b) u v / R := by
  apply (eq_div_iff hR.ne').mpr
  simp only [overlap,max_mul_of_nonneg _ _ hR.le,min_mul_of_nonneg _ _ hR.le,sub_mul,
    div_mul_cancel₀ _ hR.ne',zero_mul]
  rw [mul_comm a R,mul_comm b R]

/- The price of a uniform radius drawn from the upper interval, tested against the bin prices. -/
noncomputable def tailPrice (w : Q → ℝ) (R a : ℝ) : ℝ :=
  ∑ q, w q*(overlap a 1 (lo q/R) (hi q/R)/(1-a))

def Law (G : SimpleGraph V) (S : Set V) (R δ moment : ℝ) : Prop :=
  ∀ (w : Q → ℝ) (Y : ℝ), 0 ≤ Y →
    (∀ a ∈ Icc 0 (1-δ), tailPrice lo hi w R a ≤ (1+a)*Y) →
    ∃ x ∈ Attain (fun q => bin (lo q) (hi q)) G S R moment, ∑ q, w q*x q ≤ moment*Y

lemma Law.add {S Z : Set V} {R δ M N : ℝ}
    (hS : Law lo hi G S R δ M) (hZ : Law lo hi G Z R δ N) :
    Law lo hi G (S ∪ Z) R δ (M+N) := by
  intro w Y hy ht
  obtain ⟨x,hx,hs⟩ := hS w Y hy ht
  obtain ⟨y,hy,hz⟩ := hZ w Y hy ht
  exact ⟨x+y,attainable_add _ hx hy,by simpa [mul_add,add_mul,sum_add_distrib] using add_le_add hs hz⟩

lemma Law.weaken {S Z : Set V} {R δ M M' : ℝ} (sub : Z ⊆ S)
    (hm : M ≤ M') (h : Law lo hi G S R δ M) : Law lo hi G Z R δ M' := by
  intro w Y hy ht
  obtain ⟨x,⟨bs,hr,hc,cov,hx⟩,hb⟩ := h w Y hy ht
  exact ⟨x,⟨bs,hr,hc.trans hm,fun v hv => cov v (sub hv),hx⟩,hb.trans (mul_le_mul_of_nonneg_right hm hy)⟩

lemma tail_mass {R a : ℝ} (hr : 0 < R) (ha : 0 ≤ a) (ha' : a ≤ 1) (u v : ℝ) :
    overlap a 1 (u/R) (v/R) = overlap 0 R u v/R - overlap 0 (R*a) u v/R := by
  rw [overlap_scale hr,mul_one,overlap_split (a := 0) (b := R*a) (c := R)
    (mul_nonneg hr.le ha) (by nlinarith [mul_le_mul_of_nonneg_left ha' hr.le]) u v]
  ring

end

section
open MeasureTheory Set

lemma mean_offer {Ω Q : Type} [MeasurableSpace Ω] [Fintype Q]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → Q → ℝ) {C : Set (Q → ℝ)}
    (hC : ∀ ω, f ω ∈ C) (hint : ∀ q, Integrable (fun ω => f ω q) μ) :
    ∀ w : Q → ℝ, ∃ x ∈ C, ∑ q, w q*x q ≤ ∑ q, w q*(∫ ω, f ω q ∂μ) := by
  intro w
  have hi q := (hint q).const_mul (w q)
  obtain ⟨ω,hω⟩ := exists_le_integral (integrable_finsetSum Finset.univ (fun q _ => hi q))
  exact ⟨f ω,hC ω,by simpa [integral_finsetSum _ (fun q _ => hi q),integral_const_mul] using hω⟩

end
section
open SimpleGraph MeasureTheory Set Finset
open scoped unitInterval
variable {V Q : Type} [Fintype V] [Fintype Q] [DecidableEq V] {G : SimpleGraph V}

private lemma single_law (lo hi : Q → ℝ) {S : Set V} {R δ : ℝ} (hr : 0 < R)
    (hd : 0 < δ) (hd' : δ ≤ 1/2) (one : ∀ t ∈ Set.Icc (1-δ) 1,
      ∃ c : V, ∀ v ∈ S, cost G c v ≤ R*t) : Law lo hi G S R δ (2-δ) := by
  classical
  let f (y : I) := 1-δ+(y:ℝ)*δ
  let X (y : I) (q : Q) := bin (lo q/R) (hi q/R) (f y)
  have hX (y : I) : X y ∈ Attain (fun q => bin (lo q) (hi q)) G S R (2-δ) := by
    have hl : 1-δ ≤ f y := by dsimp [f]; linarith [mul_nonneg y.prop.1 hd.le]
    have hu : f y ≤ 1 := by dsimp [f]; linarith [mul_le_mul_of_nonneg_right y.prop.2 hd.le]
    have rng : R*f y ∈ Set.Icc 0 R := ⟨mul_nonneg hr.le (by linarith),by nlinarith [mul_le_mul_of_nonneg_left hu hr.le]⟩
    obtain ⟨c,hc⟩ := one (f y) ⟨hl,hu⟩
    refine ⟨[(R*f y,c)],?_,by simp; linarith,?_,fun q => by simp [X,bin_scale hr]⟩
    · simpa using rng
    · intro v hv
      exact ⟨(R*f y,c),by simp,hc v hv⟩
  have hx := mean_offer volume X hX (fun q =>
    int_bin (lo q/R) (hi q/R) f (by dsimp [f]; fun_prop))
  intro w Y hy tail
  obtain ⟨x,hx,hb⟩ := hx w
  refine ⟨x,hx,hb.trans ?_⟩
  have ht := tail (1-δ) ⟨by linarith,le_rfl⟩
  simpa only [show 1+(1-δ)=2-δ by ring] using
    (show ∑ q, w q*(∫ y : I, X y q) ≤ (1+(1-δ))*Y from (le_of_eq_of_le (by
      apply Finset.sum_congr rfl; intro q _; congr 1
      simpa [X,f] using (affine_bin_means (a := 1-δ) (b := 1) (by linarith) (lo q/R) (hi q/R)).1) ht))

theorem piece_law (lo hi : Q → ℝ) (ht : G.IsTree) {R δ : ℝ}
    (hr : 0 < R) (hd : 0 < δ) (hd' : δ ≤ 1/2)
    {l : ℕ} (he : (l:ℝ) = 2*R*(1-δ)) (u : Σ r, Branch G r) (hu : Minimal l u) :
    Law lo hi G (↑u.2.vertices : Set V) R δ ((u.2.size:ℝ)/R+2*δ) := by
  classical
  have low : 2*(1-δ) ≤ (u.2.size:ℝ)/R := (le_div_iff₀ hr).mpr (by
    rw [mul_right_comm,← he]; exact_mod_cast hu.1)
  obtain ⟨m₀,B₀,_,hm₀,hB₀,heq,one,two⟩ := branch_piece_profiles ht u hu
  simp only [Subtype.forall] at one two
  let m := m₀/R
  let B := B₀/R
  have hm : m ≤ 1-δ := (div_le_iff₀ hr).mpr (by linarith [hm₀,he])
  have hB : B ≤ 2*m := by dsimp [B,m]; field_simp; linarith
  have hL : 2*m+B = u.2.size/R := by dsimp [B,m]; rw [← heq]; ring
  by_cases short : B ≤ 1-δ
  · apply Law.weaken lo hi Set.Subset.rfl (show 2-δ ≤ (u.2.size:ℝ)/R+2*δ by linarith)
    apply single_law lo hi hr hd hd'
    intro t ht'
    obtain ⟨c,hc⟩ := one
    have ht := (div_le_iff₀ hr).mp (short.trans ht'.1)
    exact ⟨c,fun v hv => by linarith only [hc v hv,ht,mul_comm t R]⟩
  · let a := max 0 (B-1)
    let b := max m (1/2)
    have bounds : 0 ≤ a ∧ m ≤ b ∧ b ≤ 1-δ ∧ b < 1 ∧ 1-b ≤ b-a ∧ a < b ∧
        a+2*b+1 ≤ (u.2.size:ℝ)/R+2*δ  := by
      have ha₀ : 0 ≤ a := le_max_left ..
      have ha₁ : B-1 ≤ a := le_max_right ..
      have hb₀ : 1/2 ≤ b := le_max_right ..
      have hb₁ : m ≤ b := le_max_left ..
      rcases max_choice 0 (B-1) with h|h <;> change a = _ at h <;>
        rcases max_choice m (1/2) with h'|h' <;> change b = _ at h' <;>
        refine ⟨?_,?_,?_,?_,?_,?_,?_⟩ <;> linarith
    obtain ⟨ha,mb,hb,hb1,hw,hab,hm⟩ := bounds
    let s (y : I) := b-(y:ℝ)*(b-a)
    let t (y : I) := b+(y:ℝ)*(1-b)
    let X (y : I) (q : Q) := bin (lo q/R) (hi q/R) (s y) + bin (lo q/R) (hi q/R) (t y)
    have hX (y : I) : X y ∈ Attain (fun q => bin (lo q) (hi q)) G (↑u.2.vertices) R ((u.2.size:ℝ)/R+2*δ) := by
      have hsy : s y ∈ Set.Icc 0 1 := by
        have := mul_le_mul_of_nonneg_right y.prop.2 (sub_nonneg.mpr hab.le)
        have := mul_nonneg y.prop.1 (sub_nonneg.mpr hab.le)
        constructor <;> dsimp [s] <;> linarith
      have hty : t y ∈ Set.Icc 0 1 := by
        have := mul_le_mul_of_nonneg_right y.prop.2 (sub_nonneg.mpr hb1.le)
        have := mul_nonneg y.prop.1 (sub_nonneg.mpr hb1.le)
        constructor <;> dsimp [t] <;> linarith
      have width := mul_le_mul_of_nonneg_right y.prop.2 (by linarith : 0 ≤ 2*b-a-1)
      obtain ⟨d,c,hc⟩ := two (t y*R) ((div_le_iff₀ hr).mp (by
        change m ≤ t y; dsimp [t]; nlinarith [mul_nonneg y.prop.1 (sub_nonneg.mpr hb1.le)]))
        (s y*R) (mul_nonneg hsy.1 hr.le) (by
          rw [← add_mul]; apply (div_le_iff₀ hr).mp
          change B ≤ s y+t y
          have hbase : B ≤ a+1 := by dsimp [a]; grind
          dsimp [s,t]; linarith)
      refine ⟨[(R*s y,d),(R*t y,c)],?_,by simp; linarith,?_,fun q => by simp [X,bin_scale hr]⟩
      · simp only [List.mem_cons,List.not_mem_nil,or_false]
        rintro _ (rfl|rfl) <;> constructor <;> dsimp <;> nlinarith [mul_nonneg hr.le hsy.1,
          mul_nonneg hr.le hty.1,mul_le_mul_of_nonneg_left hsy.2 hr.le,mul_le_mul_of_nonneg_left hty.2 hr.le]
      · intro v hv
        rcases hc v hv with h | h
        · exact ⟨(R*s y,d),by simp,by simpa [mul_comm] using h⟩
        · exact ⟨(R*t y,c),by simp,by simpa [mul_comm] using h⟩
    have si q := int_bin (lo q/R) (hi q/R) s (by dsimp [s]; fun_prop)
    have ti q := int_bin (lo q/R) (hi q/R) t (by dsimp [t]; fun_prop)
    have HX := mean_offer volume X hX (fun q => (si q).add (ti q))
    obtain ⟨α,β,hα,hβ,hmean,hbin⟩ := tail_decomposition hab hb1 hw
    intro w Y hY tail
    obtain ⟨x,hx,hcost⟩ := HX w
    refine ⟨x,hx,hcost.trans ?_⟩
    calc
      _ = α*tailPrice lo hi w R a + β*tailPrice lo hi w R b := by
        simp only [tailPrice,Finset.mul_sum,←Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro q _
        rw [show (∫ y, X y q) = _ from (integral_add (si q) (ti q)).trans
          (congrArg₂ (·+·) (affine_bin_means hab (lo q/R) (hi q/R)).2 (affine_bin_means hb1 _ _).1)]
        rw [overlap_split hab.le hb1.le,hbin]; ring
      _ ≤ (a+2*b+1)*Y := by
        rw [←hmean,add_mul,mul_assoc,mul_assoc]
        exact add_le_add (mul_le_mul_of_nonneg_left (tail a ⟨ha,hab.le.trans hb⟩) hα)
          (mul_le_mul_of_nonneg_left (tail b ⟨ha.trans hab.le,hb⟩) hβ)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hY

end

section
open SimpleGraph BurningNumberConjecture

theorem burn_of_scheduled_pieces {V : Type} {J : Type*} {T G : SimpleGraph V} (hTG : T ≤ G)
    (hc : T.Connected) {K : ℕ} (t : J ↪ Fin K) (c : J → V)
    (r : J → ℝ) (ht : ∀ j, ⌈r j⌉₊ + (t j : ℕ) < K)
    (hcover : ∀ v, ∃ j, cost T (c j) v ≤ r j) :
    burningNumber G ≤ K+2 := by
  let f := t.trans (Fin.castLEEmb (show K ≤ K+2 by omega))
  let ignite := Function.extend f (fun j => (c j)) (fun _ => Classical.choice hc.nonempty)
  refine Nat.sInf_le ⟨ignite,fun v => ?_⟩
  obtain ⟨j,hj⟩ := hcover v
  refine ⟨f j,?_,?_⟩ <;> rw [show ignite (f j) = (c j) from f.injective.extend_apply ..]
  · exact (hc.preconnected _ _).mono hTG
  · have hceil := Nat.le_ceil (r j)
    change (T.dist (c j) v : ℝ)-1 ≤ r j at hj
    have hh : T.dist (c j) v ≤ ⌈r j⌉₊+2 := by exact_mod_cast (show (T.dist (c j) v : ℝ) ≤ ⌈r j⌉₊+2 by linarith)
    have hanti := (hc.preconnected (c j) v).dist_anti hTG
    have := ht j
    change G.dist (c j) v + (t j : ℕ) < K+2
    omega

end

section
open Finset



theorem select_uniform {I : Type*} [Fintype I] {Q : ℕ}
    (A : I → Set (Fin Q → ℝ)) (b : I → ℝ) {B η d : ℝ}
    (price : ∀ i (w : Fin Q → ℝ), (∀ k, 0 ≤ w k) → ∃ v ∈ A i, ∑ k, w k*v k ≤ ∑ k, w k*b i)
    (cap : ∀ i v, v ∈ A i → ∀ k, v k ∈ Set.Icc 0 B) (bc : ∀ i, 0 ≤ b i)
    (hB : 0 ≤ B) (he : 0 < η) (hd : 0 < d)
    (hm : (∑ i, b i) ≤ (1-η)*d) (hv : 2*B*Q ≤ η^2*d) :
    ∃ y : I → Fin Q → ℝ, (∀ i, y i ∈ A i) ∧ ∀ k, (∑ i, y i k) ≤ d := by
  classical
  let score (D : Fin Q → ℝ) := ∑ k, (max 0 (D k))^2
  have step i (D : Fin Q → ℝ) : ∃ v ∈ A i, score ((v-fun _ : Fin Q => b i)+D) ≤ score D + (Q:ℝ)*(2*B*b i) := by
    let w (k : Fin Q) := if b i ≤ B then 2*max 0 (D k)+B else 0
    obtain ⟨v,hv,hw⟩ := price i w (fun k => by dsimp [w]; split <;> positivity)
    have each (k : Fin Q) : (max 0 ((v k-b i+D k)))^2 ≤
        (max 0 (D k))^2 + w k*v k-w k*b i+2*B*b i := by
      obtain ⟨h₁,h₂⟩ := cap i v hv k
      have h₃ := bc i
      by_cases h₄ : b i ≤ B
      case neg =>
        have hl : (v k-b i+D k) ≤ D k := by linarith
        rw [show w k = 0 by simp [w,h₄]]
        nlinarith only [(sq_le_sq₀ (le_max_left 0 _) (le_max_left 0 _)).mpr (max_le_max_left 0 hl),mul_nonneg hB h₃]
      have E : (v k-b i)^2 ≤ B*v k+B*b i := by
        nlinarith [mul_nonneg h₁ (sub_nonneg.mpr h₂),mul_nonneg h₃ (sub_nonneg.mpr h₄),mul_nonneg h₁ h₃]
      let S := max 0 (D k)
      have hu : (max 0 ((v k-b i+D k)))^2 ≤ (S+(v k-b i))^2 := by
        by_cases h : 0 ≤ (v k-b i+D k)
        · rw [max_eq_right h]; apply (sq_le_sq₀ h _).mpr <;>
            dsimp [S] at * <;> linarith [le_max_right 0 (D k)]
        · rw [max_eq_left (le_of_not_ge h),zero_pow (by decide : 2 ≠ 0)]; exact sq_nonneg _
      dsimp [S] at hu
      rw [show w k = 2*max 0 (D k)+B by simp [w,h₄]]
      nlinarith only [hu,E]
    refine ⟨v,hv,?_⟩
    have h := sum_le_sum (s := univ) (fun k _ => each k)
    simp only [sum_add_distrib,sum_sub_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at h
    change (∑ k, (max 0 (v k-b i+D k))^2) ≤ (∑ k, (max 0 (D k))^2) + (Q:ℝ)*(2*B*b i)
    linarith only [h,hw]
  have build (s : Finset I) : ∃ y : I → Fin Q → ℝ, (∀ i ∈ s, y i ∈ A i) ∧
      score (∑ i ∈ s, (y i-fun _ => b i)) ≤ ∑ i ∈ s, (Q:ℝ)*(2*B*b i) := by
    induction s using Finset.induction_on with
    | empty => exact ⟨0,by simp,by simp [score]⟩
    | @insert i s hi ih =>
      obtain ⟨y,hy,h⟩ := ih
      obtain ⟨v,hv,hstep⟩ := step i (∑ j ∈ s, (y j-fun _ => b j))
      refine ⟨Function.update y i v,?_,?_⟩
      · intro j hj
        rcases mem_insert.mp hj with rfl|hj
        · simpa using hv
        · simpa [Function.update_of_ne (ne_of_mem_of_not_mem hj hi)] using hy j hj
      · rw [sum_insert hi,sum_insert hi,Function.update_self]
        simpa only [sum_congr rfl (fun j hj => by rw [Function.update_of_ne (ne_of_mem_of_not_mem hj hi)] :
          ∀ j ∈ s, Function.update y i v j-(fun _ => b j)=y j-(fun _ => b j))] using hstep.trans (add_le_add h le_rfl) |>.trans_eq (add_comm ..)
  obtain ⟨y,hy,hs⟩ := build univ
  simp only [score,Finset.sum_apply,Pi.sub_apply,sum_sub_distrib,← mul_sum] at hs
  refine ⟨y,fun i => hy i (mem_univ i),fun k => ?_⟩
  have h := (single_le_sum (f := fun k => (max 0 (∑ i, y i k - ∑ i, b i))^2)
    (fun _ _ => sq_nonneg _) (mem_univ k)).trans hs
  have hsq : (max 0 (∑ i, y i k - ∑ i, b i))^2 ≤ (η*d)^2 := by
    nlinarith only [h,mul_le_mul_of_nonneg_right hv hd.le,
      mul_le_mul_of_nonneg_left (show ∑ i, b i ≤ d by nlinarith [mul_pos he hd]) (by positivity : 0 ≤ 2*B*Q)]
  have := (le_max_right 0 _).trans (le_of_sq_le_sq hsq (mul_pos he hd).le)
  linarith

end

section
open Finset

/- Assign disjoint blocks of d rounds to the radius bins, largest radii first. -/
theorem exists_rounds_of_bins {I : Type*} [Fintype I] {Q d : ℕ}
    (b : I → Fin Q) (r : I → ℕ) (hr : ∀ i, r i ≤ (b i + 1 : ℕ) * d)
    (hb : ∀ q, (univ.filter (fun i => b i = q)).card ≤ d) :
    ∃ f : I ↪ Fin (Q*d + d), ∀ i, r i + (f i : ℕ) < Q*d + d := by
  classical
  let u (k : Fin Q) : {i // b i = k} ↪ Fin d := Classical.choice
    (Function.Embedding.nonempty_of_card_le (by simpa [Fintype.card_subtype] using hb k))
  let t := (Equiv.sigmaFiberEquiv b).symm.toEmbedding.trans
    ((Function.Embedding.sigmaMap (β' := fun _ => Fin d) Fin.revPerm.toEmbedding u).trans
    ((Equiv.sigmaEquivProd _ _).trans finProdFinEquiv).toEmbedding)
  refine ⟨t.trans (Fin.castLEEmb (by omega)), fun i => ?_⟩
  let j := u (b i) ⟨i,rfl⟩
  change r i + ((j : ℕ) + d * ((b i).rev : ℕ)) < Q*d + d
  have hh : ((b i).rev : ℕ) + ((b i : ℕ) + 1) = Q := by have := (b i).isLt; simp [Fin.rev]
  have := congrArg (fun x => x*d) hh
  have := hr i
  have := j.isLt
  nlinarith

end

section

theorem outer_parameters {ε : ℝ} (he : 0 < ε) :
    ∃ q : ℕ, ∃ ξ η : ℝ, 0 < ξ ∧ 0 < η ∧ ∀ (M : ℕ) (B : ℝ), ∃ n₀ : ℕ, ∀ n ≥ n₀, ∃ d : ℕ,
      0 < d ∧ 2/ξ ≤ (d:ℝ) ∧ B*(q+1) ≤ η^2*d ∧
      (1+ξ)*((n : ℝ)+M*(((q+1)*d : ℕ):ℝ))*d / (((q+1)*d : ℕ):ℝ)^2 ≤ (1-η)*d ∧
      (((q+1)*d+d+2 : ℕ) : ℝ) ≤ (1+ε)*Real.sqrt n := by
  obtain ⟨q,hq⟩ := exists_nat_gt (4/ε)
  have hp : 0 < (q:ℝ) := lt_trans (by positivity) hq
  have hqε := (div_lt_iff₀ he).mp hq
  let Q : ℝ := q+1
  have hQ : 0 < Q := by dsimp [Q]; positivity
  refine ⟨q,1/q,1/Q,by positivity,by positivity,fun M B => ?_⟩
  let C := max (1+2*(q:ℝ)) (max ((M:ℝ)*Q) (B*(q+1)/(1/Q)^2))
  have hCq : 1+2*(q:ℝ) ≤ C := le_max_left ..
  have hC : 1 ≤ C := by linarith
  obtain ⟨N,hN⟩ := exists_nat_gt (2*((Q+1)*(C+1)+2)/ε)
  refine ⟨N^2,fun n hn => ?_⟩
  let s := Real.sqrt n
  have hs : (N:ℝ) ≤ s := Real.le_sqrt_of_sq_le (by exact_mod_cast hn)
  have hs₀ : 0 ≤ s := Real.sqrt_nonneg _
  let d := ⌈s/q+C⌉₊
  have lo : s/q+C ≤ (d:ℝ) := Nat.le_ceil _
  have hi : (d:ℝ) < s/q+C+1 := Nat.ceil_lt_add_one (by linarith [div_nonneg hs₀ hp.le])
  have hd : 0 < (d:ℝ) := by linarith [div_nonneg hs₀ hp.le]
  have big : C ≤ (d:ℝ) := by linarith [div_nonneg hs₀ hp.le]
  refine ⟨d,by exact_mod_cast hd,by simpa [div_div_eq_mul_div] using (show 2*(q:ℝ) ≤ d by linarith),?_,?_,?_⟩
  · have := (div_le_iff₀ (by positivity : 0 < (1/Q)^2)).mp
        (((le_max_right ..).trans (le_max_right ..)).trans big)
    linarith
  · push_cast
    change (1+1/(q:ℝ))*((n:ℝ)+M*(Q*d))*d/(Q*d)^2 ≤ (1-1/Q)*d
    have hm : (M:ℝ)*Q ≤ C := (le_max_left ..).trans (le_max_right ..)
    have hlow := (div_le_iff₀ hp).mp (show s/q ≤ d-C by linarith)
    have hq₁ : 1 ≤ (q:ℝ) := by exact_mod_cast (show 1 ≤ q by exact_mod_cast hp)
    have hh : s + C ≤ (q:ℝ)*d := by nlinarith [mul_nonneg (sub_nonneg.mpr hq₁) (by linarith : 0 ≤ C)]
    have H := mul_le_mul_of_nonneg_right hh (mul_nonneg hp.le hd.le)
    have H' := mul_le_mul_of_nonneg_left (show s ≤ (q:ℝ)*d by linarith) hs₀
    have hM := mul_le_mul_of_nonneg_right hm hd.le
    have hC' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hq₁ (by linarith : 0 ≤ C)) hd.le
    have key : (n:ℝ)+M*(Q*d) ≤ ((q:ℝ)*d)^2 := by nlinarith only [H,H',hM,hC',show s^2 = n from Real.sq_sqrt (by positivity)]
    apply (div_le_iff₀ (sq_pos_of_pos (mul_pos hQ hd))).mpr
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left key (by positivity : 0 ≤ 1+1/(q:ℝ))) hd.le
    convert this using 1
    dsimp [Q]; field_simp; ring
  · have hconst := (div_lt_iff₀ he).mp (hN.trans_le hs)
    have hratio := mul_le_mul_of_nonneg_right (le_of_lt hqε) (div_nonneg hs₀ hp.le)
    have hdiv : (q:ℝ)*(s/q) = s := by field_simp
    have H := mul_lt_mul_of_pos_left hi (by positivity : 0 < Q+1)
    push_cast
    change Q*(d:ℝ)+d+2 ≤ (1+ε)*s
    dsimp [Q] at *
    linear_combination (norm := ring_nf) (2:ℝ)⁻¹ * hconst.le + H.le + (1/2:ℝ)*hratio + (1+ε/2)*hdiv <;> norm_num

end

section
open Set

def gridLo {q : ℕ} (d : ℕ) (k : Fin (q+1)) : ℝ := if k = 0 then -1 else (k:ℕ)*d
def gridHi {q : ℕ} (d : ℕ) (k : Fin (q+1)) : ℝ := ((k:ℕ)+1 : ℕ)*d

lemma grid_pick {q d : ℕ} {r : ℝ} (hr : 0 ≤ r) (hR : r ≤ (((q+1)*d : ℕ):ℝ)) :
    ∃ k : Fin (q+1), r ≤ gridHi d k ∧
      ∀ t : Fin (q+1), bin (gridLo d t) (gridHi d t) r = if k=t then 1 else 0 := by
  classical
  have hex : ∃ n : ℕ, r ≤ (((n+1)*d:ℕ):ℝ) := ⟨q,hR⟩
  let k : Fin (q+1) := ⟨Nat.find hex, Nat.lt_succ_iff.mpr (Nat.find_min' hex hR)⟩
  have iff (t : Fin (q+1)) : k=t ↔ r ∈ Ioc (gridLo d t) (gridHi d t) := by
    rw [← Fin.val_inj,show k.val = Nat.find hex by rfl,Nat.find_eq_iff]
    change (_ ∧ _) ↔ _ < r ∧ _
    by_cases ht : t=0
    · subst t; simp [gridLo,gridHi]; grind
    · have hpos : 0 < t.val := Nat.pos_of_ne_zero (fun h => ht (Fin.ext h))
      simp only [gridLo,if_neg ht,gridHi]
      push_cast
      constructor
      · rintro ⟨hu,hl⟩
        have := hl (t.val-1) (by omega)
        rw [← Nat.cast_one (R := ℝ), ← Nat.cast_add,Nat.sub_add_cancel hpos] at this
        exact ⟨by exact lt_of_not_ge (by simpa using this),hu⟩
      · rintro ⟨hl,hu⟩
        refine ⟨hu,fun n hn => not_le.mpr (lt_of_le_of_lt ?_ hl)⟩
        exact_mod_cast Nat.mul_le_mul_right d hn
  refine ⟨k,((iff k).mp rfl).2,fun t => ?_⟩
  simp [bin, Set.indicator, ← iff]

lemma overlap_grid_le {q d : ℕ} (k : Fin (q+1)) (R : ℝ) :
    overlap 0 R (gridLo d k) (gridHi d k) ≤ d := by
  unfold overlap
  apply max_le (Nat.cast_nonneg _)
  by_cases h : k = 0
  · subst k; simpa [gridLo, gridHi] using (min_le_right R (d:ℝ))
  · exact (sub_le_sub (min_le_right ..) (le_max_right ..)).trans (by
      simp [gridHi,gridLo,h,add_mul])

end

/- Build a rooted description of a spanning tree, then split it into small
connected pieces. The remaining fragment always contains the attachment vertex. -/

section
open SimpleGraph
variable {V : Type} {G : SimpleGraph V} {r : V}
lemma Branch.attach [DecidableEq V] (t : Branch G r) {u v : V}
    (hu : u ∈ t.vertices) (e : G.Adj u v) :
    ∃ t' : Branch G r, t'.size = t.size+1 ∧ t'.vertices = insert v t.vertices := by
  induction t with
  | root r =>
    have eq : u = r := by simpa [vertices] using hu
    subst u
    exact ⟨.join e (.root _) (.root _),rfl,by ext; simp [vertices,or_comm]⟩
  | join ab a b ia ib =>
    rcases Finset.mem_union.mp hu with h | h
    · obtain ⟨q,hq,hv⟩ := ia h
      exact ⟨.join ab q b,by simp [size,hq]; omega,by ext; simp [vertices,hv] <;> tauto⟩
    · obtain ⟨q,hq,hv⟩ := ib h
      exact ⟨.join ab a q,by simp [size,hq] <;> omega,by ext; simp [vertices,hv] <;> tauto⟩

lemma spanning [Fintype V] [DecidableEq V] (hc : G.Connected) (r : V) :
    ∃ t : Branch G r, t.vertices = Finset.univ ∧ t.size+1 = Fintype.card V := by
  classical
  suffices grow : ∀ t : Branch G r, t.size+1 = t.vertices.card →
      ∃ b : Branch G r, b.vertices = Finset.univ ∧ b.size+1 = Fintype.card V from
    grow (.root r) (by simp [Branch.size,Branch.vertices])
  intro t ht
  generalize hM : Fintype.card V - t.vertices.card = m
  induction m using Nat.strong_induction_on generalizing t with
  | h m ih =>
    by_cases hall : t.vertices = Finset.univ
    · exact ⟨t,hall,by simpa [hall] using ht⟩
    obtain ⟨v,hv⟩ := not_forall.mp (fun he => hall (Finset.eq_univ_of_forall he))
    obtain ⟨p⟩ := hc r v
    obtain ⟨a,ha,b,hb,e⟩ := frontier (↑t.vertices) p t.root_mem hv
    obtain ⟨q,hq,hv'⟩ := t.attach ha e
    have hcard : q.vertices.card = t.vertices.card + 1 := by rw [hv', Finset.card_insert_of_notMem hb]
    have := Finset.card_le_univ q.vertices
    exact ih _ (by omega) q (by omega) rfl

lemma chop [DecidableEq V] (t : Branch G r) {l : ℕ} (hl : 0 < l) :
    ∃ (rest : Branch G r) (pieces : List (Σ r, Branch G r)), rest.size < l ∧
      (∀ u ∈ pieces, Minimal l u) ∧ rest.size+(pieces.map (fun p => p.2.size)).sum = t.size ∧
      ∀ v ∈ t.vertices, v ∈ rest.vertices ∨ ∃ p ∈ pieces, v ∈ p.2.vertices := by
  induction t with
  | root => exact ⟨.root _,[],hl,by simp,by simp [Branch.size],by simp⟩
  | join e a b ia ib =>
    obtain ⟨u,us,hu,hus,hw,hv⟩ := ia
    obtain ⟨v,vs,hv',hvs,hw',hv''⟩ := ib
    let w := Branch.join e u v
    let ps := us++vs
    have hp : ∀ z ∈ ps, Minimal l z := fun z hz => (List.mem_append.mp hz).elim (hus z) (hvs z)
    have size : w.size+(ps.map (fun p => p.2.size)).sum = (Branch.join e a b).size := by
      simp [w,ps,Branch.size]; omega
    have cover (x) (h : x ∈ (Branch.join e a b).vertices) : x ∈ w.vertices ∨ ∃ p ∈ ps, x ∈ p.2.vertices := by
      simp only [w,ps,Branch.vertices,Finset.mem_union,List.mem_append] at *
      grind
    by_cases h : w.size < l
    · exact ⟨w,ps,h,hp,size,cover⟩
    refine ⟨.root _,⟨_,w⟩::ps,hl,?_,by simpa [Branch.size] using size,fun x hx => Or.inr (by simpa using cover x hx)⟩
    simp only [List.mem_cons,forall_eq_or_imp]
    refine ⟨⟨le_of_not_gt h,by dsimp [w,Branch.size]; omega,fun x hx y hy z hz => ?_⟩,hp⟩
    exact two_parts_bound (fun _ ha _ hb => (u.dist_le ha hb).trans hu.le)
      (fun _ ha _ hb => (v.dist_le ha hb).trans hv'.le) (Finset.mem_union.mp hx)
      (Finset.mem_union.mp hy) (Finset.mem_union.mp hz)

end
section
open SimpleGraph Finset

theorem outer_partition {V : Type} [Fintype V] [DecidableEq V] {T : SimpleGraph V}
    (hc : T.Connected) {D : ℕ} (hD : 0 < D) :
    ∃ (m : ℕ) (s : Fin m → Σ r, Branch T r) (L : Fin m → ℕ),
      (∀ i, (s i).2.size ≤ L i ∧ D ≤ L i ∧ L i ≤ 2*D) ∧
      (∑ i, L i) ≤ Fintype.card V - 1 + D ∧ ∀ v, ∃ i, v ∈ (s i).2.vertices := by
  classical
  let root := Classical.choice hc.nonempty
  obtain ⟨t,ht,hsize⟩ := spanning hc root
  obtain ⟨rest,ps,hr,hps,hsum,hcover⟩ := chop t hD
  let s : Fin (ps.length+1) → Σ r, Branch T r := Fin.cases ⟨root,rest⟩ ps.get
  let L : Fin (ps.length+1) → ℕ := Fin.cases D (fun j => (ps.get j).2.size)
  refine ⟨_,s,L,?_,?_,fun v => ?_⟩
  · intro i
    cases i using Fin.cases with
    | zero => exact ⟨hr.le,le_rfl,by change D ≤ 2*D; omega⟩
    | succ j =>
      have h := hps (ps.get j) (List.get_mem ..)
      exact ⟨le_rfl,h.1,h.2.1⟩
  · have eq : (∑ j : Fin ps.length, (ps.get j).2.size) = (ps.map (fun p => p.2.size)).sum := by
      rw [← List.sum_ofFn]
      change (List.ofFn ((fun p : Σ r, Branch T r => p.2.size) ∘ ps.get)).sum = _
      rw [← List.map_ofFn, List.ofFn_get]
    rw [Fin.sum_univ_succ]
    simp only [L, Fin.cases_zero, Fin.cases_succ, eq]
    omega
  · rcases hcover v (ht ▸ mem_univ _) with hv | ⟨p,hp,hv⟩
    · exact ⟨0,hv⟩
    · obtain ⟨j,rfl⟩ := List.get_of_mem hp
      exact ⟨j.succ,hv⟩
end

section
open SimpleGraph MeasureTheory Set
open scoped unitInterval
variable {V Q : Type} [Fintype V] [Fintype Q] [DecidableEq V] {G : SimpleGraph V}

/- A fragment smaller than the cut fits in one ball drawn from the top interval. -/
lemma remainder_law (lo hi : Q → ℝ) (ht : G.IsTree) {r : V} (t : Branch G r)
    {R δ : ℝ} (hr : 0 < R) (hd : 0 < δ) (hd' : δ ≤ 1/2)
    {l : ℕ} (cut : (l:ℝ) = 2*R*(1-δ)) (hsmall : t.size < l) :
    Law lo hi G (↑t.vertices) R δ 2 := by
  classical
  have hmin : Minimal t.size ⟨r,t⟩ := by
    exact ⟨le_rfl,by change t.size ≤ 2*t.size; omega,fun _ hx _ hy _ _ => Or.inl (t.dist_le hx hy)⟩
  obtain ⟨m,B,_,_,hB,he,one,_⟩ := branch_piece_profiles ht ⟨r,t⟩ hmin
  obtain ⟨c,hc⟩ := one
  have hcut : (t.size : ℝ) < 2*R*(1-δ) := cut ▸ Nat.cast_lt.mpr hsmall
  apply Law.weaken lo hi Set.Subset.rfl (show 2-δ ≤ 2 by linarith)
  apply single_law lo hi hr hd hd'
  intro t' ht'
  exact ⟨c,fun v hv => (hc ⟨v,hv⟩).trans (by nlinarith [mul_le_mul_of_nonneg_left ht'.1 hr.le])⟩

/- Glue all completed fragments onto a fixed remainder, charging only one extra ball. -/
lemma glue_piece_list (lo hi : Q → ℝ) (ht : G.IsTree) {R δ : ℝ}
    (hr : 0 < R) (hd : 0 < δ) (hd' : δ ≤ 1/2) {l : ℕ} (cut : (l:ℝ) = 2*R*(1-δ)) {Z : Set V}
    (hz : Law lo hi G Z R δ 2) (ps : List (Σ r, Branch G r))
    (hps : ∀ u ∈ ps, Minimal l u) :
    let s : ℝ := ((ps.map (fun u => u.2.size)).sum : ℕ)
    Law lo hi G {v | v ∈ Z ∨ ∃ u ∈ ps, v ∈ u.2.vertices} R δ (2+(1+2*δ)*(s/R)) := by
  induction ps with
  | nil => simpa using hz
  | cons u ps ih =>
    have hm := hps u List.mem_cons_self
    have hsize : 2*R*(1-δ) ≤ u.2.size := cut ▸ Nat.cast_le.mpr hm.1
    have ratio : 1 ≤ (u.2.size:ℝ)/R := (le_div_iff₀ hr).mpr (by
      nlinarith [mul_nonneg hr.le (show 0 ≤ 1-2*δ by linarith)])
    have piece := piece_law lo hi ht hr hd hd' cut u hm
    have whole := Law.add lo hi (ih (fun v hv => hps v (List.mem_cons_of_mem _ hv))) piece
    apply Law.weaken lo hi _ _ whole
    · intro v hv
      rcases hv with h | ⟨u',hu,hv⟩
      · exact Or.inl (Or.inl h)
      · rcases List.mem_cons.mp hu with rfl | hu
        · exact Or.inr hv
        · exact Or.inl (Or.inr ⟨u',hu,hv⟩)
    · simp only [List.map_cons,List.sum_cons,Nat.cast_add,add_div]
      nlinarith only [mul_le_mul_of_nonneg_left ratio hd.le]

theorem exact_branch_law (lo hi : Q → ℝ) (ht : G.IsTree) {r : V} (t : Branch G r)
    {L R : ℝ} (hs : (t.size:ℝ) ≤ L) (hR : 1 ≤ R) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/(2*R) ∧
      Law lo hi G (↑t.vertices) R δ (2+(1+2*δ)*(L/R)) := by
  let l := ⌈2*R⌉₊-1
  have hr : 0 < R := by linarith
  have pos : 0 < 2*R := by positivity
  have succ : (l:ℝ)+1 = ⌈2*R⌉₊ := by
    exact_mod_cast Nat.sub_add_cancel (Nat.ceil_pos.mpr pos)
  let δ := (2*R-l)/(2*R)
  have low := Nat.le_ceil (2*R)
  have high := Nat.ceil_lt_add_one (a := 2*R) pos.le
  have hd : 0 < δ := div_pos (by linarith) pos
  have bound : δ ≤ 1/(2*R) := div_le_div_of_nonneg_right (by linarith) pos.le
  have cut : (l:ℝ) = 2*R*(1-δ) := by dsimp [δ]; field_simp; ring
  have hd' : δ ≤ 1/2 := bound.trans ((div_le_iff₀ pos).mpr (by linarith))
  refine ⟨δ,hd,bound,?_⟩
  have hl : 0 < l := by exact_mod_cast (show (0:ℝ) < l by linarith)
  obtain ⟨rest,ps,hsz,hps,htotal,hcover⟩ := chop t hl
  have h := glue_piece_list lo hi ht hr hd hd' cut (remainder_law lo hi ht rest hr hd hd' cut hsz) ps hps
  let s := (ps.map (fun u => u.2.size)).sum
  have hs' : (s:ℝ) ≤ L := (Nat.cast_le.mpr (show s ≤ t.size by dsimp [s]; omega)).trans hs
  apply Law.weaken lo hi (fun v hv => hcover v hv) _ h
  exact add_le_add (le_refl 2) (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hs' hr.le)
    (by linarith : 0 ≤ 1+2*δ))

end

section
open Finset SimpleGraph Set

lemma first_bin {q d : ℕ} (k : Fin (q+1)) {s : ℝ} (hs : 0 ≤ s) (h : s ≤ d) :
    overlap 0 s (gridLo d k) (gridHi d k) = if k=0 then s else 0 := by
  by_cases hk : k = 0
  · subst k; simp [overlap,gridLo,gridHi,min_eq_left h,max_eq_right hs]
  have hk' : 1 ≤ k.val := Nat.pos_of_ne_zero (fun h => hk (Fin.ext h))
  have cut : (d:ℝ) ≤ (k:ℕ)*d := by exact_mod_cast (Nat.le_mul_of_pos_left d hk')
  simp only [if_neg hk]
  unfold overlap gridLo; simp only [if_neg hk]; apply max_eq_left
  exact sub_nonpos.mpr ((min_le_left ..).trans (h.trans (cut.trans (le_max_right ..))))

/- At the chosen radius the weighted bin mass per squared radius is minimal.
Every shorter interval therefore has enough mass to control the price of its complementary tail. -/
theorem minimum_branch {V : Type} [Fintype V] [DecidableEq V] {T : SimpleGraph V}
    (ht : T.IsTree) (t : Σ r, Branch T r) {q d : ℕ} (hd : 0 < d)
    {L R ξ : ℝ} (hs : (t.2.size:ℝ) ≤ L) (hdR : (d:ℝ) ≤ R)
    (hξ : 0 < ξ) (resolution : 2/ξ ≤ d) (room : 4*R ≤ ξ*L) :
    Offers (Attain (fun k : Fin (q+1) => bin (gridLo d k) (gridHi d k)) T (↑t.2.vertices) R ((1+ξ)*L/d))
      (fun k => (1+ξ)*L*overlap 0 R (gridLo d k) (gridHi d k)/R^2) := by
  classical
  intro w hw
  let M (s : ℝ) := ∑ k, w k*overlap 0 s (gridLo d k) (gridHi d k)
  let F (s : ℝ) := M s/s^2
  have hd' : 0 < (d:ℝ) := by exact_mod_cast hd
  have hL : 0 ≤ L := (Nat.cast_nonneg _).trans hs
  have small (s : ℝ) (hz : 0 ≤ s) (hsd : s ≤ d) : M s = w 0*s := by
    simp [M, first_bin (q := q) (d := d) _ hz hsd, mul_ite]
  have cont : Continuous M := by dsimp [M,overlap]; fun_prop
  obtain ⟨r,hr,hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hdR)
    (f := F) (cont.continuousOn.div (continuousOn_id.pow 2)
      (fun s hs => (sq_pos_of_pos (hd'.trans_le hs.1)).ne'))
  have hr' := hd'.trans_le hr.1
  have best (s : ℝ) (hs : 0 < s) (hsR : s ≤ R) : F r ≤ F s := by
    by_cases h : (d:ℝ) ≤ s
    · exact hmin ⟨h,hsR⟩
    refine (hmin (left_mem_Icc.mpr hdR)).trans ?_
    dsimp [F]; rw [small _ hd'.le le_rfl,small _ hs.le (le_of_not_ge h)]
    simpa only [sq,←div_div,mul_div_cancel_right₀ _ hd'.ne',mul_div_cancel_right₀ _ hs.ne'] using
      (div_le_div_of_nonneg_left (hw 0) hs (le_of_not_ge h))
  have hm : 0 ≤ M r := sum_nonneg (fun k _ => mul_nonneg (hw k) (le_max_left ..))
  have h₁ : (1:ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨δ,hδ,hcut,law⟩ := exact_branch_law (gridLo (q := q) d) (gridHi d) ht t.2 hs (h₁.trans hr.1)
  obtain ⟨y,hy,hcost⟩ := law w (M r/r) (div_nonneg hm hr'.le) (fun a ha => by
      have h1 : 0 < 1-a := by linarith [ha.2]
      have ha1 : a ≤ 1 := by linarith
      have lower : (M r)*a^2 ≤ M (r*a) := by
        rcases ha.1.eq_or_lt with hz|hp
        · rw [←hz,mul_zero,zero_pow (by decide),mul_zero,small 0 le_rfl hd'.le,mul_zero]
        · have h := best (r*a) (mul_pos hr' hp)
            ((show r*a ≤ r by simpa using mul_le_mul_of_nonneg_left ha1 hr'.le).trans hr.2)
          change M r/r^2 ≤ M (r*a)/(r*a)^2 at h
          field_simp at h
          exact h
      have eq : tailPrice (gridLo d) (gridHi d) w r a = (M r/r-M (r*a)/r)/(1-a) := by
        unfold tailPrice; simp_rw [tail_mass hr' ha.1 ha1]
        dsimp [M]; rw [Finset.sum_div,Finset.sum_div,←sum_sub_distrib,Finset.sum_div]
        apply sum_congr rfl; intro k _; ring
      rw [eq,div_le_iff₀ h1]; field_simp; nlinarith only [lower])
  have mom : 2+(1+2*δ)*(L/r) ≤ (1+ξ)*L/r := by
    have h₁ := (div_le_iff₀ hξ).mp (resolution.trans hr.1)
    have h₂ : 2*δ ≤ ξ/2 := by
      apply (le_of_mul_le_mul_right (a := r) _ hr')
      nlinarith only [(le_div_iff₀ (by positivity : 0 < 2*r)).mp hcut,h₁]
    field_simp; nlinarith only [room,hr.2,mul_le_mul_of_nonneg_right h₂ hL]
  refine ⟨y,attainable_mono _ hr.2 (mom.trans (div_le_div_of_nonneg_left
    (mul_nonneg (by linarith) hL) hd' hr.1)) hy,hcost.trans ?_⟩
  calc
    _ ≤ ((1+ξ)*L/r)*(M r/r) := mul_le_mul_of_nonneg_right mom (div_nonneg hm hr'.le)
    _ = ((1+ξ)*L)*F r := by dsimp [F]; ring
    _ ≤ ((1+ξ)*L)*F R := mul_le_mul_of_nonneg_left (hmin (right_mem_Icc.mpr hdR))
      (mul_nonneg (by linarith) hL)
    _ = _ := by dsimp [F,M]; rw [← mul_div_assoc,Finset.mul_sum,Finset.sum_div]
                apply sum_congr rfl; intro k _; ring

end

end BurningNumberConjecture.Proof

open BurningNumberConjecture.Proof
open MeasureTheory Finset SimpleGraph BurningNumberConjecture

theorem OMA.solution : type_of% @BurningNumberConjecture.burning_number_conjecture.variants.norin_turcotte := by
  classical
  intro ε he
  obtain ⟨q,ξ,η,hξ,hη,pars⟩ := outer_parameters he
  let M := ⌈4/ξ⌉₊
  have hM : 0 < M := Nat.ceil_pos.mpr (by positivity)
  let B : ℝ := (1+ξ)*(2*M*(q+1) : ℕ)
  obtain ⟨n₀,hN⟩ := pars M (2*B)
  refine ⟨n₀, fun V _ G hc hn => ?_⟩
  obtain ⟨T,hTG,hT⟩ := hc.exists_isTree_le
  obtain ⟨d,hd,hresolution,large,mean,time⟩ := hN (Fintype.card V) hn
  let R := (q+1)*d
  let D := M*R
  have hR : 0 < R := Nat.mul_pos (Nat.succ_pos _) hd
  obtain ⟨m,s,L,hs,hsum,hcover⟩ := outer_partition hT.connected (Nat.mul_pos hM hR)
  let F (k : Fin (q+1)) := bin (gridLo d k) (gridHi d k)
  let A i := Attain F T (↑(s i).2.vertices) R ((1+ξ)*(L i:ℝ)/d)
  let b i : ℝ := (1+ξ)*(L i:ℝ)*d/(R:ℝ)^2
  have priced i (w : Fin (q+1) → ℝ) (hw : ∀ k, 0 ≤ w k) : ∃ v ∈ A i, ∑ k, w k*v k ≤ ∑ k, w k*b i := by
    have hr : 0 ≤ (R:ℝ) := Nat.cast_nonneg _
    have hMR : (M:ℝ)*R ≤ L i := by exact_mod_cast (hs i).2.1
    have room : 4*(R:ℝ) ≤ ξ*(L i) := by
      have h := (div_le_iff₀ hξ).mp (Nat.le_ceil (4/ξ))
      change 4 ≤ (M:ℝ)*ξ at h
      nlinarith only [mul_le_mul_of_nonneg_right h hr,mul_le_mul_of_nonneg_left hMR hξ.le]
    have hdR : (d:ℝ) ≤ R := by exact_mod_cast (show d ≤ R by dsimp [R]; rw [Nat.add_mul,Nat.one_mul]; omega)
    obtain ⟨v,hv,h⟩ := minimum_branch (q := q) hT (s i) hd (Nat.cast_le.mpr (hs i).1) hdR
      hξ hresolution room w hw
    refine ⟨v,hv,h.trans (sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left ?_ (hw k)))⟩
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (overlap_grid_le _ R) (by positivity)) (sq_nonneg _)
  have means : ∑ i, b i ≤ (1-η)*d := by
    dsimp [b]
    rw [← sum_div,← sum_mul,← mul_sum,← Nat.cast_sum]
    have hc : (∑ i, L i) ≤ Fintype.card V + D := by omega
    have hc' : ((∑ i, L i : ℕ):ℝ) ≤ (Fintype.card V:ℝ)+M*R := by exact_mod_cast hc
    apply le_trans _ mean
    exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hc' (by linarith : 0 ≤ 1+ξ)) (Nat.cast_nonneg _)) (sq_nonneg _))
  have hd' : 0 < (d:ℝ) := by exact_mod_cast hd
  have budget (i) : (1+ξ)*(L i:ℝ)/d ≤ B := by
    apply (div_le_iff₀ hd').mpr
    have hL : (L i:ℝ) ≤ (2*M*(q+1) : ℕ)*d := by exact_mod_cast
      (show L i ≤ 2*M*(q+1)*d by simpa [D,R,mul_assoc] using (hs i).2.2)
    dsimp [B]; nlinarith only [mul_le_mul_of_nonneg_left hL (by linarith : 0 ≤ 1+ξ)]
  have range i (v : Fin (q+1) → ℝ) (hv : v ∈ A i) k : v k ∈ Set.Icc 0 B := by
    obtain ⟨bs,_,hlen,_,hh⟩ := hv
    have scan (l : List (ℝ × V)) : (l.map (fun z => F k z.1)).sum ∈ Set.Icc (0:ℝ) l.length := by
      induction l with
      | nil => simp
      | cons z l ih =>
        obtain ⟨lo,hi⟩ := bin_mem (gridLo d k) (gridHi d k) z.1
        change 0 ≤ F k z.1 at lo; change F k z.1 ≤ 1 at hi
        simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
        exact ⟨add_nonneg lo ih.1,by linarith [ih.2]⟩
    rw [hh k]
    exact ⟨(scan bs).1,(scan bs).2.trans (hlen.trans (budget i))⟩
  obtain ⟨y,hy,cap⟩ := select_uniform A b priced range (fun _ => by dsimp [b]; positivity)
    (by dsimp [B]; positivity) hη hd' means (by simpa using large)
  choose bs data using hy
  let r i (k : Fin (bs i).length) := ((bs i).get k).1
  have inside i (k : Fin (bs i).length) := (data i).1 _ (List.get_mem (bs i) k)
  choose label hhigh hbin using fun i (k : Fin (bs i).length) =>
    grid_pick (q := q) (d := d) (inside i k).1 (inside i k).2
  have sum_map {α : Type} (l : List α) (f : α → ℝ) :
      ∑ k : Fin l.length, f (l.get k) = (l.map f).sum := by
    rw [← List.sum_ofFn]; change (List.ofFn (f ∘ l.get)).sum = _
    rw [← List.map_ofFn, List.ofFn_get]
  let N' (k : Fin (q+1)) i : ℝ := (univ.filter (fun u => label i u = k)).card
  have value k i : N' k i = y i k := by
    rw [(data i).2.2.2 k,← sum_map]
    dsimp [N']; rw [card_filter]; push_cast
    exact sum_congr rfl (fun u _ => (hbin i u k).symm)
  obtain ⟨t,ht⟩ := exists_rounds_of_bins (fun j : Σ i, Fin (bs i).length => label j.1 j.2)
    (fun j => ⌈r j.1 j.2⌉₊) (fun j => Nat.ceil_le.mpr (by simpa [gridHi,r] using hhigh j.1 j.2)) (by
    intro k
    have hc := cap k
    simp_rw [← value, N'] at hc
    exact_mod_cast (show ((univ.filter fun j : Σ i, Fin (bs i).length => label j.1 j.2 = k).card : ℝ)
      ≤ d by simpa only [card_filter, Nat.cast_sum, Fintype.sum_sigma, Nat.cast_ite, Nat.cast_one,
        Nat.cast_zero] using hc))
  have hburn := burn_of_scheduled_pieces hTG hT.connected t
    (fun j => ((bs j.1).get j.2).2) (fun j => r j.1 j.2) ht (by
      intro v
      obtain ⟨i,hi⟩ := hcover v
      obtain ⟨u,hu,hu'⟩ := (data i).2.2.1 v hi
      obtain ⟨k,rfl⟩ := List.get_of_mem hu
      exact ⟨⟨i,k⟩,hu'⟩)
  exact (Nat.cast_le (α := ℝ).mpr hburn).trans time
