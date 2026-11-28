import FormalConjectures.Paper.BurningNumberConjecture
import Mathlib

/-!
A proof of the asymptotic burning-number bound of Norin and Turcotte.

A longest path gives each vertex of a tree a position and a height. The
two largest heights at distinct positions give a bound on the number of
vertices needed outside the path. This yields one- and two-ball covers of
each small piece. Mixing these covers bounds the expected number of radii
in each interval. A finite product of the piece distributions then gives a
cover that fits the available ignition rounds.
-/

namespace BurningSpine
open SimpleGraph
lemma path_dist {V : Type} {G : SimpleGraph V} (hG : G.IsTree)
    {a b : V} {p : G.Walk a b} (hp : p.IsPath) : p.length = G.dist a b := by
  obtain ⟨q,hq⟩ := hG.connected.exists_walk_length_eq_dist a b
  rw [Subtype.mk.inj (hG.isAcyclic.subsingleton_path a b |>.elim ⟨p,hp⟩ ⟨q,q.isPath_of_length_eq_dist hq⟩)]
  exact hq

end BurningSpine
namespace BurningPieces
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

end BurningPieces

namespace BurningSpine
open SimpleGraph

variable {V : Type} [Fintype V] {G : SimpleGraph V} {x y : V}

def Tag (G : SimpleGraph V) (x y v : V) (d i h : ℕ) : Prop :=
  i ≤ d ∧ G.dist x v = i+h ∧ G.dist y v = d-i+h

lemma Tag.unique {v : V} {d i h j k : ℕ} (a : Tag G x y v d i h)
    (b : Tag G x y v d j k) : i = j ∧ h = k := by unfold Tag at *; omega

/-- A point attaching to a diameter path at index i and height h has
witnesses of all heights below h at that same index. -/
theorem coordinates (ht : G.IsTree) (p : G.Walk x y) (hp : p.IsPath) :
    ∀ v, ∃ i h, Tag G x y v p.length i h ∧ G.dist (p.getVert i) v ≤ h ∧
      ∀ k ≤ h, ∃ w, Tag G x y w p.length i k := by
  classical
  let F (s : Finset V) (v : V) := ∃ (a : G.Walk x v) (b : G.Walk y v),
    a.IsPath ∧ b.IsPath ∧ (∀ w ∈ a.support, w ∈ s) ∧ (∀ w ∈ b.support, w ∈ s)
  let K (v : V) := ∃ i h, Tag G x y v p.length i h ∧ G.dist (p.getVert i) v ≤ h ∧
    ∀ k ≤ h, ∃ w, Tag G x y w p.length i k
  suffices grow : ∀ s : Finset V, x ∈ s → (∀ v ∈ s, K v ∧ F s v) → ∀ v, K v by
    apply grow p.support.toFinset (by simpa using p.start_mem_support)
    intro v hv
    have hv' := List.mem_toFinset.mp hv
    obtain ⟨a,b,ha,hb,rfl⟩ := hp.mem_support_iff_exists_append.mp hv'
    have hj : (a.append b).getVert a.length = v := by simp [Walk.getVert_append]
    have key : Tag G x y v (a.append b).length a.length 0 := by
      have hy := path_dist ht hb.reverse
      simpa [Tag,Walk.length_append,path_dist ht ha] using hy.symm
    refine ⟨⟨_,0,key,by simp [hj],fun k hk => ⟨v,by simpa [show k=0 by omega] using key⟩⟩,
      a,b.reverse,ha,hb.reverse,?_,?_⟩ <;> simp [Walk.mem_support_append_iff] <;> tauto
  intro s
  generalize size : Fintype.card V - s.card = n
  induction n using Nat.strong_induction_on generalizing s with
  | h n ih =>
    intro xs hyp
    by_cases full : ∀ v, v ∈ s
    · exact fun v => (hyp v (full v)).1
    obtain ⟨w,hw⟩ := not_forall.mp full
    obtain ⟨q⟩ := ht.connected x w
    obtain ⟨u,hu,v,hv,e⟩ := BurningPieces.frontier (↑s) q xs hw
    change u ∈ s at hu
    change v ∉ s at hv
    obtain ⟨⟨i,h,t,hbound,chain⟩,a,b,ha,hb,hsa,hsb⟩ := hyp u hu
    have extend {z : V} (c : G.Walk z u) (hc : c.IsPath) (hs : ∀ w ∈ c.support, w ∈ s) :
        (c.concat e).IsPath := hc.concat (fun hh => hv (hs v hh)) e
    have ha' := extend a ha hsa
    have hb' := extend b hb hsb
    have TV : Tag G x y v p.length i (h+1) := by
      obtain ⟨hi,ex,ey⟩ := t
      refine ⟨hi,?_,?_⟩
      · rw [← path_dist ht ha',Walk.length_concat,path_dist ht ha,ex]; omega
      · rw [← path_dist ht hb',Walk.length_concat,path_dist ht hb,ey]; omega
    have Kv : K v := ⟨i,h+1,TV,ht.connected.dist_triangle.trans (Nat.add_le_add hbound
      (dist_eq_one_iff_adj.mpr e).le),fun k hk => by
        by_cases eq : k=h+1
        · exact ⟨_,eq ▸ TV⟩
        · exact chain k (by omega)⟩
    let s' := insert v s
    have ct : s'.card = s.card+1 := Finset.card_insert_of_notMem hv
    apply ih _ (show Fintype.card V-s'.card<n by have := Finset.card_le_univ s'; omega) s' rfl
      (Finset.mem_insert_of_mem xs)
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · refine ⟨Kv,a.concat e,b.concat e,ha',hb',?_,?_⟩ <;>
        simp only [Walk.support_concat,List.mem_append,List.mem_singleton,Finset.mem_insert,s'] <;> grind
    · obtain ⟨k,a',b',ha,hb,hsa,hsb⟩ := hyp j hj
      exact ⟨k,_,_,ha,hb,fun w hw => Finset.mem_insert_of_mem (hsa w hw),
        fun w hw => Finset.mem_insert_of_mem (hsb w hw)⟩

end BurningSpine

namespace BurningSpine
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
  obtain ⟨p,plen⟩ := ht.connected.exists_walk_length_eq_dist x y
  have path := p.isPath_of_length_eq_dist plen
  choose j h tag dist chain using coordinates ht p path
  have bounds (v) : h v ≤ j v ∧ j v + h v ≤ p.length := by
    have left := G.dist_le_diam (G.connected_iff_ediam_ne_top.mp ht.connected) (u := x) (v := v)
    have right := G.dist_le_diam (G.connected_iff_ediam_ne_top.mp ht.connected) (u := y) (v := v)
    obtain ⟨_,_,_⟩ := tag v
    omega
  obtain ⟨u,_,hu⟩ := Finset.exists_max_image Finset.univ h Finset.univ_nonempty
  let outside (v : V) := if j v = j u then 0 else h v
  obtain ⟨w,_,hw⟩ := Finset.exists_max_image Finset.univ outside Finset.univ_nonempty
  have sep : j u = j w → outside w = 0 := fun he => by simp [outside,he]
  have zw : outside w ≤ h w := by dsimp [outside]; split <;> omega
  have points (v : V) (k : ℕ) (hk : k ≤ h v) : ∃ t, (j t,h t) = (j v,k) := by
    obtain ⟨t,ht⟩ := chain v k hk
    exact ⟨t,Prod.ext ((tag t).unique ht).1 ((tag t).unique ht).2⟩
  choose a ha using fun n : Fin (h u) => points u (n+1) n.isLt
  choose b hb using fun n : Fin (outside w) => points w (n+1) (n.isLt.trans_le zw)
  have on (k : Fin (p.length+1)) : (j (p.getVert k),h (p.getVert k)) = (k.val,0) := by
    have le : k.val ≤ p.length := by omega
    have hn := path_dist ht (path.take k)
    have hm := path_dist ht (path.drop k).reverse
    have htag : Tag G x y (p.getVert k) p.length k 0 := by
      simpa [Tag,le,Walk.take_length,Walk.drop_length,Nat.min_eq_left le] using And.intro hn.symm hm.symm
    exact Prod.ext ((tag _).unique htag).1 ((tag _).unique htag).2
  have size := three_ranges (fun v => (j v,h v)) sep (fun n => p.getVert n) a b on ha hb
  obtain ⟨_,e₁,e₂⟩ := tag u
  refine ⟨x,y,p,j u,h u,outside w,j,h,u,(bounds u).1,(bounds u).2,zw.trans (hu _ (by simp)),size,
    plen.symm,e₁,e₂,fun v => ⟨(bounds v).1,(bounds v).2,dist v,?_⟩⟩
  by_cases he : j v = j u
  · exact Or.inl ⟨he,hu _ (by simp)⟩
  · exact Or.inr (by simpa [outside,he] using hw v (Finset.mem_univ _))

end BurningSpine

namespace BurningBridge
open SimpleGraph BurningNumberConjecture

/- Rounding a position on a path down to a vertex costs at most one round.
The reduced distance records this allowance; the scheduler restores it. -/
structure Centre {V : Type} (T : SimpleGraph V) where
  endpoint : V

variable {V : Type} {T : SimpleGraph V}

noncomputable def Centre.reducedDist (c : Centre T) (v : V) : ℝ := max 0 ((T.dist c.endpoint v : ℝ)-1)

lemma Centre.round (c : Centre T) (w : V) (r : ℕ) (h : c.reducedDist w ≤ r) :
    T.dist c.endpoint w ≤ r+1 := by
  have := (le_max_right ..).trans h
  exact_mod_cast (show (T.dist c.endpoint w : ℝ) ≤ (r:ℝ)+1 by linarith)

theorem centre_on_walk {a b : V} (p : T.Walk a b) (hc : T.Connected) (x : ℝ) :
    ∃ c : Centre T, ∀ j : ℕ, ∀ w : V,
      c.reducedDist w ≤ |x - j| + T.dist (p.getVert j) w := by
  have seg {i j : ℕ} (h : i ≤ j) : (T.dist (p.getVert i) (p.getVert j) : ℝ) ≤ (j : ℝ)-i := by
    let q := (p.drop i).take (j-i)
    have eq : (p.drop i).getVert (j-i) = p.getVert j := by rw [p.drop_getVert, Nat.add_sub_of_le h]
    rw [← Nat.cast_sub h, ← eq]
    exact_mod_cast (dist_le q).trans (show q.length ≤ j-i by simp [q, Walk.take_length])
  have move (i j : ℕ) (v : V) :
      (T.dist (p.getVert i) v : ℝ) ≤ |(i : ℝ)-j| + T.dist (p.getVert j) v := by
    have triangle : (T.dist (p.getVert i) v : ℝ) ≤ T.dist (p.getVert i) (p.getVert j) + (T.dist (p.getVert j) v : ℝ) := by exact_mod_cast hc.dist_triangle
    rcases le_total i j with h | h
    · rw [abs_of_nonpos (by exact_mod_cast sub_nonpos.mpr (show (i : ℝ) ≤ j by exact_mod_cast h))]
      linarith [seg h]
    · rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h))]
      rw [SimpleGraph.dist_comm (u := p.getVert i) (v := p.getVert j)] at triangle
      linarith [seg h]
  let n := ⌊x⌋₊
  refine ⟨⟨p.getVert n⟩, fun j w => max_le (by positivity) ?_⟩
  have step := move n j w
  by_cases hx : 0 ≤ x
  · have lo := Nat.floor_le hx
    have hi := Nat.lt_floor_add_one x
    change (n:ℝ) ≤ x at lo
    change x < (n:ℝ)+1 at hi
    cases abs_cases ((n:ℝ)-j) <;> cases abs_cases (x-j) <;> dsimp at * <;> linarith
  · have hn : n = 0 := Nat.floor_eq_zero.mpr (by linarith)
    rw [hn,Nat.cast_zero,zero_sub,abs_neg,abs_of_nonneg (Nat.cast_nonneg _)] at step
    rw [abs_of_nonpos (by linarith [Nat.cast_nonneg (α := ℝ) j])]
    change (T.dist (p.getVert n) w : ℝ)-1 ≤ _
    rw [hn]; linarith

end BurningBridge

namespace BurningTripod

/- Upper bounds on distances suffice, so this also applies when a vertex is
off the three arms, up to the common error z. -/
def NearTripod {V : Type*} (dist : ℝ → V → ℝ) (a b c z : ℝ) : Prop :=
  ∀ v, (∃ x ∈ Set.Icc 0 (b+c), ∀ p ∈ Set.Icc 0 (b+c), dist p v ≤ |x-p|+z) ∨
    (∀ p ∈ Set.Icc 0 (b+c), dist p v ≤ |b-p|+a+z)

end BurningTripod

namespace BurningPieces
open SimpleGraph
variable {V : Type} {G : SimpleGraph V}
lemma two_parts_bound {X Y : Set V} {d : ℕ} {u v w : V}
    (hx : ∀ a ∈ X, ∀ b ∈ X, G.dist a b ≤ d)
    (hy : ∀ a ∈ Y, ∀ b ∈ Y, G.dist a b ≤ d)
    (hu : u ∈ X ∪ Y) (hv : v ∈ X ∪ Y) (hw : w ∈ X ∪ Y) :
    G.dist u v ≤ d ∨ G.dist u w ≤ d ∨ G.dist v w ≤ d := by
  rcases hu with h|h <;> rcases hv with h'|h' <;> rcases hw with h''|h'' <;> grind

end BurningPieces
namespace BurningTree
open SimpleGraph BurningBridge BurningTripod

/- The physical parameters needed to apply the normalized local profile. -/
def HasPieceProfiles {V : Type} (G : SimpleGraph V) (l L : ℝ) : Prop :=
  ∃ m B : ℝ, 0 ≤ m ∧ m ≤ l/2 ∧ B ≤ 2*m ∧ 2*m+B = L ∧
    (∀ t ≥ B, ∃ u : Centre G, ∀ v, u.reducedDist v ≤ t) ∧
    (∀ t ≥ m, ∀ s ≥ 0, B ≤ s+t →
      (∃ u : Centre G, ∀ v, u.reducedDist v ≤ t) ∨
      (∃ u w : Centre G, ∀ v, u.reducedDist v ≤ s ∨ w.reducedDist v ≤ t))

private theorem profiles_of_coordinates {V : Type} {G : SimpleGraph V}
    (centre : ℝ → Centre G) {a b c z l L : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) (hz : 0 ≤ z)
    (ht : NearTripod (fun p v => (centre p).reducedDist v) a b c z)
    (hsize : a+b+c+4*z ≤ L) (hmax : L ≤ 2*l) (hshort : a+b+2*z ≤ l) :
    HasPieceProfiles G l L := by
  let m := max (L/4) ((a+b)/2+z)
  let B := L-2*m
  have hl : L/4 ≤ m := le_max_left ..
  have hm : (a+b)/2+z ≤ m := le_max_right ..
  have hB : (b+c)/2+2*z ≤ B := by
    dsimp [B,m]; rcases max_choice (L/4) ((a+b)/2+z) with h|h <;> rw [h] <;> linarith
  let mid := (b+c)/2
  have hmid : mid ∈ Set.Icc 0 (b+c) := by constructor <;> dsimp [mid] <;> linarith
  have one (t : ℝ) (h : mid+z ≤ t) : ∃ u : Centre G, ∀ v, u.reducedDist v ≤ t := by
    refine ⟨centre mid, fun v => ?_⟩
    rcases ht v with ⟨y,⟨hy₀,hy₁⟩,hy⟩ | hy
    · have := hy mid hmid
      dsimp [mid] at *
      cases abs_cases (y-(b+c)/2) <;> linarith
    · have := hy mid hmid
      dsimp [mid] at *
      cases abs_cases (b-(b+c)/2) <;> linarith
  refine ⟨m,B,by linarith,max_le (by linarith) (by linarith),by dsimp [B]; linarith,
    by dsimp [B]; ring,fun t h => one t (by dsimp [mid]; linarith),?_⟩
  intro t hmt s hs hst
  by_cases h : mid+z ≤ t
  · exact Or.inl (one t h)
  right
  let p := t-z
  let q := b+c-(B-t-z)
  have hp : p ∈ Set.Icc 0 (b+c) := by constructor <;> dsimp [p,mid] at * <;> linarith
  have hq : q ∈ Set.Icc 0 (b+c) := by constructor <;> dsimp [q,mid,B] at * <;> linarith
  refine ⟨centre q,centre p,fun v => ?_⟩
  rcases ht v with ⟨y,⟨hy₀,hy₁⟩,hy⟩ | hy
  · by_cases left : y ≤ 2*p
    · right
      have := hy p hp
      cases abs_cases (y-p) <;> dsimp [p] at * <;> linarith
    · left
      have := hy q hq
      cases abs_cases (y-q) <;> dsimp [p,q] at * <;> linarith
  · right
    have := hy p hp
    cases abs_cases (b-p) <;> dsimp [p] at * <;> linarith

/- A finite tree covered by two sets of diameter at most l has the physical
one/two-ball profiles at any L between its edge count and 2l. -/
theorem minimal_piece_profiles {V : Type} [Fintype V] (G : SimpleGraph V) (hg : G.IsTree)
    {l : ℕ} {L : ℝ} (hsize : (Fintype.card V : ℝ) ≤ L+1) (hcap : L ≤ 2*l)
    (X Y : Set V) (cover : ∀ v, v ∈ X ∪ Y)
    (diamX : ∀ x ∈ X, ∀ y ∈ X, G.dist x y ≤ l)
    (diamY : ∀ x ∈ Y, ∀ y ∈ Y, G.dist x y ≤ l) :
    HasPieceProfiles G l L := by
  obtain ⟨x,y,p,I,H,z,j,h,u,hle,hright,hz,hcard,dxy,dx,dy,hv⟩ := BurningSpine.spine_data hg
  have short := BurningPieces.two_parts_bound diamX diamY (cover x) (cover y) (cover u)
  rw [dxy,dx,dy] at short
  have short' : H + min I (p.length-I) ≤ l := by omega
  let D : ℝ := p.length
  let i : ℝ := I
  let a : ℝ := H-z
  let b : ℝ := i-z
  let c : ℝ := D-i-z
  have len : D+(H:ℝ)+z ≤ L := by
    have := Nat.cast_le (α := ℝ).mpr hcard
    dsimp [D]; push_cast at this; linarith
  have h1 : (H:ℝ) ≤ i := Nat.cast_le.mpr hle
  have h2 : i+(H:ℝ) ≤ D := by dsimp [i,D]; exact_mod_cast hright
  have h3 := Nat.cast_le (α := ℝ).mpr hz
  have ha : 0 ≤ a := sub_nonneg.mpr h3
  have hab : a ≤ b := by dsimp [a,b]; linarith
  have hac : a ≤ c := by dsimp [a,c]; linarith
  have mass : a+b+c+4*z ≤ L := by dsimp [a,b,c]; linarith
  let centre (s : ℝ) := (centre_on_walk p hg.connected (s+z)).choose
  have near : NearTripod (fun s v => (centre s).reducedDist v) a b c z := by
    intro v
    obtain ⟨hj,hj',hd,casesV⟩ := hv v
    let k : ℝ := j v
    let e : ℝ := h v
    have hk : e ≤ k := Nat.cast_le.mpr hj
    have he : k+e ≤ D := by dsimp [k,e,D]; exact_mod_cast hj'
    have bound (s : ℝ) : (centre s).reducedDist v ≤ |s+z-k|+e :=
      ((centre_on_walk p hg.connected _).choose_spec (j v) v).trans (add_le_add le_rfl (Nat.cast_le.mpr hd))
    rcases casesV with ⟨eq,hu⟩ | hu
    · right
      have eq' : k=i := by dsimp [k,i]; exact_mod_cast eq
      have hh : e ≤ H := Nat.cast_le.mpr hu
      intro s hs
      have hb := bound s
      rw [show b-s = -(s+z-k) by dsimp [b]; linarith, abs_neg]
      dsimp [a]; linarith
    · left
      have hh : e ≤ z := Nat.cast_le.mpr hu
      let t := max 0 (min (b+c) (k-z))
      have nonneg : 0 ≤ b+c := by linarith
      refine ⟨t,⟨le_max_left ..,max_le nonneg (min_le_left ..)⟩,fun s hs => ?_⟩
      have hb := bound s
      obtain ⟨hs₀,hs₁⟩ := hs
      dsimp [t,b,c] at *
      rcases le_total (k-(z:ℝ)) 0 with hl | hl
      · rw [max_eq_left ((min_le_right ..).trans hl),zero_sub,abs_neg,abs_of_nonneg hs₀]
        rw [abs_of_nonneg (by linarith)] at hb
        linarith
      · rcases le_total (k-(z:ℝ)) (i-z+(D-i-z)) with hl' | hl'
        · rw [min_eq_right hl',max_eq_right hl]
          rw [show k-z-s = -(s+z-k) by ring,abs_neg]
          linarith
        · rw [min_eq_left hl', max_eq_right nonneg,abs_of_nonneg (by linarith)]
          rw [abs_of_nonpos (by linarith)] at hb
          linarith
  have hs : a+min b c+2*z ≤ l := by
    have nat := (Nat.cast_le (α := ℝ)).mpr short'
    have hi : I ≤ p.length := by omega
    push_cast [Nat.cast_sub hi] at nat
    change (H:ℝ)+min i (D-i) ≤ l at nat
    dsimp [a,b,c]; rw [min_sub_sub_right]; linarith
  by_cases sorted : b ≤ c
  · exact profiles_of_coordinates centre ha hab sorted (Nat.cast_nonneg _) near mass hcap
      (by simpa [min_eq_left sorted] using hs)
  · have mirror : NearTripod (fun s v => (centre (b+c-s)).reducedDist v) a c b z := by
      intro v
      have flip (s : ℝ) (h : s ∈ Set.Icc 0 (c+b)) : b+c-s ∈ Set.Icc 0 (b+c) := by
        obtain ⟨_,_⟩ := h; constructor <;> linarith
      rcases near v with ⟨t,⟨h₀,h₁⟩,ht⟩ | ht
      · left; refine ⟨b+c-t,⟨by linarith,by linarith⟩,fun s h => ?_⟩
        have := ht _ (flip s h)
        rwa [show t-(b+c-s) = -(b+c-t-s) by ring,abs_neg] at this
      · right; intro s h
        have := ht _ (flip s h)
        rwa [show b-(b+c-s) = -(c-s) by ring,abs_neg] at this
    exact profiles_of_coordinates _ ha hac (le_of_not_ge sorted) (Nat.cast_nonneg _) mirror
      (by linarith) hcap (by simpa [min_eq_right (le_of_not_ge sorted)] using hs)

end BurningTree

namespace BurningPieces
open SimpleGraph

inductive Branch {V : Type} (G : SimpleGraph V) : V → Type
  | root (v : V) : Branch G v
  | edge {u v : V} (e : G.Adj u v) (t : Branch G v) : Branch G u
  | join {v : V} (a b : Branch G v) : Branch G v

variable {V : Type} {G : SimpleGraph V} {r : V}

def Branch.size : {r : V} → Branch G r → ℕ
  | _, .root _ => 0
  | _, .edge _ t => t.size+1
  | _, .join a b => a.size+b.size

def Branch.vertices [DecidableEq V] : {r : V} → Branch G r → Finset V
  | r, .root _ => {r}
  | r, .edge _ t => insert r t.vertices
  | _, .join a b => a.vertices ∪ b.vertices

lemma Branch.root_mem [DecidableEq V] (t : Branch G r) : r ∈ t.vertices := by
  induction t <;> simp_all [vertices]

lemma Branch.card [DecidableEq V] (t : Branch G r) : t.vertices.card ≤ t.size+1 := by
  induction t with
  | root => simp [vertices,size]
  | @edge u v e t ih =>
    exact (Finset.card_insert_le ..).trans (by dsimp [size]; omega)
  | join t u ht hu =>
    have hi := Finset.card_pos.mpr (show (t.vertices ∩ u.vertices).Nonempty from
      ⟨_,Finset.mem_inter.mpr ⟨t.root_mem,u.root_mem⟩⟩)
    have heq := Finset.card_union_add_card_inter t.vertices u.vertices
    dsimp [size,vertices]; omega

lemma Branch.walk [DecidableEq V] (t : Branch G r) {v : V} (hv : v ∈ t.vertices) :
    ∃ p : G.Walk r v, ∀ w ∈ p.support, w ∈ t.vertices := by
  induction t with
  | root r =>
    obtain rfl : v = r := by simpa [vertices] using hv
    exact ⟨.nil,by simp [vertices]⟩
  | @edge a b e t ih =>
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact ⟨.nil,by simp [vertices]⟩
    · obtain ⟨p,hp⟩ := ih hv
      refine ⟨p.cons e,fun w hw => ?_⟩
      rcases List.mem_cons.mp hw with rfl | h
      · exact Finset.mem_insert_self ..
      · exact Finset.mem_insert_of_mem (hp _ h)
  | join t u ih jh =>
    rcases Finset.mem_union.mp hv with h | h
    · obtain ⟨p,hp⟩ := ih h
      exact ⟨p,fun w hw => Finset.mem_union_left _ (hp w hw)⟩
    · obtain ⟨p,hp⟩ := jh h
      exact ⟨p,fun w hw => Finset.mem_union_right _ (hp w hw)⟩

lemma Branch.connected [DecidableEq V] (t : Branch G r) :
    (G.induce (↑t.vertices : Set V)).Connected := by
  rw [connected_iff_exists_forall_reachable]
  refine ⟨⟨r,t.root_mem⟩,fun v => ?_⟩
  obtain ⟨p,hp⟩ := t.walk v.prop
  exact ⟨p.induce _ hp⟩

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
  l ≤ t.2.size ∧ ∃ a b : Σ r, Branch G r, a.2.size ≤ l ∧ b.2.size ≤ l ∧
    a.2.size+b.2.size = t.2.size ∧ t.2.vertices = a.2.vertices ∪ b.2.vertices

end BurningPieces
namespace BurningTree
open SimpleGraph BurningBridge BurningPieces

/- A connected induced subgraph of a tree contains its ambient geodesics. -/
theorem tree_induce_dist {V : Type} {G : SimpleGraph V} (ht : G.IsTree)
    {S : Set V} (hc : (G.induce S).Connected) (x y : S) :
    (G.induce S).dist x y = G.dist x.val y.val := by
  obtain ⟨p,hp,hd⟩ := (hc x y).exists_path_of_dist
  let f := Embedding.induce (G := G) S
  have hmap : (p.map f.toHom).IsPath := hp.map f.injective
  obtain ⟨q,hq,he⟩ := (ht.connected x.val y.val).exists_path_of_dist
  have eq : p.map f.toHom = q := (ht.existsUnique_path _ _).unique hmap hq
  calc
    _ = p.length := hd.symm
    _ = (p.map f.toHom).length := (p.length_map f.toHom).symm
    _ = q.length := congrArg (fun z : G.Walk x.val y.val => z.length) eq
    _ = _ := he

def includeCentre {V : Type} {G : SimpleGraph V} {S : Set V} (c : Centre (G.induce S)) :
    Centre G := ⟨c.endpoint.val⟩

theorem includeCentre_distance {V : Type} {G : SimpleGraph V} (ht : G.IsTree)
    {S : Set V} (hc : (G.induce S).Connected) (c : Centre (G.induce S)) (x : S) :
    (includeCentre c).reducedDist x.val = c.reducedDist x := by
  cases c <;> simp [includeCentre,Centre.reducedDist,tree_induce_dist ht hc]

/- One- and two-ball profiles for the actual fragment of the spanning-tree
decomposition. All centres and distances are in the ambient tree. -/
theorem branch_piece_profiles {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (ht : G.IsTree) {l : ℕ} (u : Σ r, Branch G r) (hu : Minimal l u) :
    ∃ m B : ℝ, 0 ≤ m ∧ m ≤ (l:ℝ)/2 ∧ B ≤ 2*m ∧ 2*m+B = u.2.size ∧
      (∀ t ≥ B, ∃ c : Centre G, ∀ v ∈ u.2.vertices, c.reducedDist v ≤ t) ∧
      (∀ t ≥ m, ∀ s ≥ 0, B ≤ s+t →
        (∃ c : Centre G, ∀ v ∈ u.2.vertices, c.reducedDist v ≤ t) ∨
        (∃ c d : Centre G, ∀ v ∈ u.2.vertices, c.reducedDist v ≤ s ∨ d.reducedDist v ≤ t)) := by
  classical
  obtain ⟨_,p,q,hp,hq,hsize,hsets⟩ := hu
  let S : Set V := ↑u.2.vertices
  let P := G.induce S
  have hc : P.Connected := u.2.connected
  have tree : P.IsTree := ⟨hc,ht.isAcyclic.induce S⟩
  let X : Set S := {x | x.val ∈ p.2.vertices}
  let Y : Set S := {x | x.val ∈ q.2.vertices}
  have hcard : Fintype.card S ≤ u.2.size+1 := by
    have heq : Fintype.card S = u.2.vertices.card := Fintype.card_coe _
    exact heq.le.trans u.2.card
  obtain ⟨m,B,hm,hm',hB,he,one,two⟩ := minimal_piece_profiles P tree
    (L := u.2.size) (l := l) (by exact_mod_cast hcard) (by exact_mod_cast (show u.2.size ≤ 2*l by omega))
    X Y (by
      intro v
      have hv : v.val ∈ u.2.vertices := v.prop
      rw [hsets, Finset.mem_union] at hv
      exact hv)
    (by intro x hx y hy; rw [tree_induce_dist ht hc]; exact (p.2.dist_le hx hy).trans hp)
    (by intro x hx y hy; rw [tree_induce_dist ht hc]; exact (q.2.dist_le hx hy).trans hq)
  have lift_one {t : ℝ} (h : ∃ c : Centre P, ∀ v, c.reducedDist v ≤ t) :
      ∃ c : Centre G, ∀ v ∈ u.2.vertices, c.reducedDist v ≤ t := by
    obtain ⟨c,hc'⟩ := h
    exact ⟨includeCentre c,fun v hv => (includeCentre_distance ht hc c ⟨v,hv⟩).le.trans (hc' _)⟩
  refine ⟨m,B,hm,hm',hB,he,fun t h => lift_one (one t h),fun t ht' s hs hst => ?_⟩
  rcases two t ht' s hs hst with h | ⟨c,d,h⟩
  · exact Or.inl (lift_one h)
  · refine Or.inr ⟨includeCentre c,includeCentre d,fun v hv => ?_⟩
    simpa only [← includeCentre_distance ht hc] using h ⟨v,hv⟩

end BurningTree
namespace BurningProfiles

/- Radius normalized to one. A two-ball cover can be chosen so both radii
are affine in the uniform parameter, or one ball from the top interval
always suffices. The two interval densities are nondecreasing. -/
lemma local_profiles {L δ m B : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1/2)
    (hL : 2*(1-δ) ≤ L) (hm : m ≤ 1-δ)
    (hmB : B ≤ 2*m) (hparam : 2*m+B = L)
    (one : ℝ → Prop) (two : ℝ → ℝ → Prop)
    (hone : ∀ t ≥ B, one t)
    (htwo : ∀ t ≥ m, ∀ s ≥ 0, B ≤ s+t → one t ∨ two s t) :
    (∀ t ∈ Set.Icc (1-δ) 1, one t) ∨
      ∃ a b : ℝ, 0 ≤ a ∧ a < b ∧ b ≤ 1-δ ∧ 1-b ≤ b-a ∧
        a+2*b+1 ≤ L+2*δ ∧
        ∀ y ∈ Set.Icc 0 1,
          let s := b - y*(b-a)
          let t := b + y*(1-b)
          s+t ≤ L ∧ (one t ∨ two s t) := by
  by_cases h : B ≤ 1-δ
  · exact Or.inl fun t ht => hone t (h.trans ht.1)
  right
  let a := max 0 (B-1)
  let b := max m (1/2)
  have ha : 0 ≤ a := le_max_left ..
  have hb : m ≤ b := le_max_left ..
  have hm' : b ≤ 1-δ := max_le hm (by linarith)
  have ha' : B ≤ a+1 := by linarith [show B-1 ≤ a from le_max_right ..]
  have width : 1-b ≤ b-a := by
    have half : 1/2 ≤ b := le_max_right ..
    rcases max_choice 0 (B-1) with h | h <;> change a = _ at h <;> linarith
  have mass : a+2*b+1 ≤ L+2*δ := by
    rcases max_choice 0 (B-1) with h | h <;> change a = _ at h <;>
      rcases max_choice m (1/2) with h' | h' <;> change b = _ at h' <;> linarith
  refine ⟨a,b,ha,by linarith,hm',width,mass,fun y ⟨hy,hy'⟩ => ?_⟩
  dsimp only
  have lo := mul_nonneg hy (by linarith : 0 ≤ 1-b)
  have small := mul_le_mul_of_nonneg_right hy' (by linarith : 0 ≤ b-a)
  have cost := mul_nonneg hy (by linarith : 0 ≤ 2*b-a-1)
  have sum := mul_le_mul_of_nonneg_right hy' (by linarith : 0 ≤ 2*b-a-1)
  refine ⟨by linarith, htwo _ (by linarith) _ (by linarith) (by linarith)⟩

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

end BurningProfiles
namespace BurningTree
open SimpleGraph BurningBridge BurningPieces BurningProfiles

/- Radii normalized by R for one minimal fragment, with centres in the original tree. -/
theorem local_geometry {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (ht : G.IsTree) {l : ℕ} (u : Σ r, Branch G r) (hu : Minimal l u)
    {R δ : ℝ} (hR : 0 < R) (hd : 0 < δ) (hd' : δ ≤ 1/2)
    (hlo : 2*(1-δ) ≤ (u.2.size : ℝ)/R) (hhi : (l:ℝ)/R ≤ 2*(1-δ)) :
    let L := (u.2.size : ℝ)/R
    let one := fun t : ℝ => ∃ c : Centre G, ∀ v ∈ u.2.vertices, c.reducedDist v ≤ t*R
    let two := fun s t : ℝ => ∃ c d : Centre G, ∀ v ∈ u.2.vertices,
      c.reducedDist v ≤ s*R ∨ d.reducedDist v ≤ t*R
    (∀ t ∈ Set.Icc (1-δ) 1, one t) ∨
      ∃ a b : ℝ, 0 ≤ a ∧ a < b ∧ b ≤ 1-δ ∧ 1-b ≤ b-a ∧
        a+2*b+1 ≤ L+2*δ ∧
        ∀ y ∈ Set.Icc 0 1,
          let s := b-y*(b-a)
          let t := b+y*(1-b)
          s+t ≤ L ∧ (one t ∨ two s t) := by
  obtain ⟨m,B,_,hm,hB,he,hone,htwo⟩ := branch_piece_profiles ht u hu
  dsimp only
  refine local_profiles (m := m/R) (B := B/R) hd hd' hlo ?_ ?_ ?_
    (fun t => ∃ c : Centre G, ∀ v ∈ u.2.vertices, c.reducedDist v ≤ t*R)
    (fun s t => ∃ c d : Centre G, ∀ v ∈ u.2.vertices, c.reducedDist v ≤ s*R ∨ d.reducedDist v ≤ t*R) ?_ ?_
  · apply (div_le_iff₀ hR).mpr
    linarith [(div_le_iff₀ hR).mp hhi]
  · have h := (div_le_div_iff_of_pos_right hR).mpr hB
    linarith only [h,show 2*m/R = 2*(m/R) by ring]
  · rw [← he]
    ring
  · intro t h
    exact hone _ ((div_le_iff₀ hR).mp h)
  · intro t h s hs hsum
    exact htwo _ ((div_le_iff₀ hR).mp h) _ (mul_nonneg hs hR.le)
      (by simpa [add_mul] using (div_le_iff₀ hR).mp hsum)

end BurningTree

namespace BurningBridge
open SimpleGraph BurningNumberConjecture
variable {V : Type} {T : SimpleGraph V}
variable {Q : Type} (bin : Q → ℝ → ℝ)

/- The additive slack of one unit lets a partition cut at an integer edge
length while its reference distribution uses an arbitrary real radius. -/
def Attain (T : SimpleGraph V) (S : Set V) (R B : ℝ) : Set (Q → ℝ) :=
  {x | ∃ bs : List (ℝ × Centre T), (∀ p ∈ bs, p.1 ∈ Set.Icc 0 R) ∧
    (bs.map Prod.fst).sum ≤ B ∧
    (∀ v ∈ S, ∃ p ∈ bs, p.2.reducedDist v ≤ p.1+1) ∧
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

lemma hull_add {S Z : Set V} {R A B : ℝ} {x y : Q → ℝ}
    (hx : x ∈ convexHull ℝ (Attain bin T S R A)) (hy : y ∈ convexHull ℝ (Attain bin T Z R B)) :
    x+y ∈ convexHull ℝ (Attain bin T (S ∪ Z) R (A+B)) := by
  open scoped Pointwise in
    have sub : Attain bin T S R A + Attain bin T Z R B ⊆ Attain bin T (S ∪ Z) R (A+B) := by
      rintro _ ⟨a,ha,b,hb,rfl⟩
      exact attainable_add bin ha hb
    exact convexHull_mono sub (by rw [convexHull_add]; exact ⟨x,hx,y,hy,rfl⟩)

end BurningBridge
namespace BurningProfiles
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

/- Sampling the single ball from the top interval has a bounded measurable count. -/
theorem single_bin_mean {δ : ℝ} (hδ : 0 < δ) (u v : ℝ) :
    let N := fun y : I => bin u v (1-δ + (y:ℝ)*δ)
    Measurable N ∧ (∀ y, N y ∈ Icc (0:ℝ) 1) ∧
      (∫ y, N y) = overlap (1-δ) 1 u v / δ := by
  refine ⟨(bin_measurable u v).comp (by fun_prop), fun _ => bin_mem .., ?_⟩
  simpa using (affine_bin_means (a := 1-δ) (b := 1) (by linarith) u v).1

/- The two radii use the very same sample y. Each bin count is measurable,
bounded by two, and has the exact sum of the two uniform interval masses. -/
theorem pair_bin_mean {a b : ℝ} (hab : a < b) (hb : b < 1) (u v : ℝ) :
    let N := fun y : I => bin u v (b - (y:ℝ)*(b-a)) + bin u v (b + (y:ℝ)*(1-b))
    Measurable N ∧ (∀ y, N y ∈ Icc (0:ℝ) 2) ∧
      (∫ y, N y) = overlap a b u v / (b-a) + overlap b 1 u v / (1-b) := by
  let S := fun y : I => bin u v (b - (y:ℝ)*(b-a))
  let T := fun y : I => bin u v (b + (y:ℝ)*(1-b))
  have hs : Measurable S := (bin_measurable u v).comp (by fun_prop)
  have ht : Measurable T := (bin_measurable u v).comp (by fun_prop)
  have intg (f : I → ℝ) (hf : Measurable f) (h : ∀ y, f y ∈ Icc (0:ℝ) 1) : Integrable f volume :=
    (memLp_of_bounded (Filter.Eventually.of_forall h) hf.aestronglyMeasurable 1).integrable le_rfl
  refine ⟨hs.add ht, fun y => ?_, ?_⟩
  · exact ⟨add_nonneg (bin_mem ..).1 (bin_mem ..).1,
      (add_le_add (bin_mem ..).2 (bin_mem ..).2).trans_eq (by norm_num)⟩
  · rw [integral_add (intg S hs (fun _ => bin_mem ..)) (intg T ht (fun _ => bin_mem ..))]
    exact congrArg₂ (· + ·) (affine_bin_means hab u v).2 (affine_bin_means hb u v).1

/- Subtract adjacent overlap lengths to use the upper-tail mixture identity. -/
theorem overlap_split {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (u v : ℝ) :
    overlap a b u v = overlap a c u v - overlap b c u v := by
  have hi : Integrable (bin u v) volume :=
    (integrable_indicator_iff measurableSet_Ioc).mpr (integrableOn_const (by simp [Real.volume_Ioc]))
  have h := intervalIntegral.integral_add_adjacent_intervals
    (a := a) (b := b) (c := c) hi.intervalIntegrable hi.intervalIntegrable
  rw [integral_bin hab, integral_bin hbc, integral_bin (hab.trans hbc)] at h
  linarith

end BurningProfiles
namespace BurningMixture
open Finset

/- The auxiliary distributions on the shorter intervals can be weighted so
that the expected count of every test set is bounded by its uniform mass
times (1+ε)L. The test set has mass u in [0,1] and mass v i in [0,a i],
measured in units of the whole interval. -/
theorem uniform_mix_supported {I : Type*} [Fintype I] {ε L : ℝ} (he : 0 < ε) (he' : ε ≤ 2)
    (hL : 0 < L) (a α : I → ℝ) (hα : ∀ i, 0 ≤ α i) (ha : ∀ i, 0 ≤ a i)
    (cut : ∀ i, a i ≤ 1 - ε/8)
    (moment : ∑ i, α i * (1+a i) ≤ (1+ε/3)*L) :
    let E := ε + ε^2/13
    ∃ (p : ℝ) (w : I → ℝ), 0 ≤ p ∧ (∀ i, 0 ≤ w i) ∧ p + ∑ i, w i = 1 ∧
      (∀ i, a i = 0 → w i = 0) ∧ ∀ u ≥ 0, ∀ v : I → ℝ, (∀ i, a i = 0 → v i = 0) →
        p * (∑ i, α i * ((u-v i)/(1-a i))) +
          ∑ i, w i * ((1+E)*L*v i / (a i)^2) ≤ (1+ε)*L*u := by
  dsimp only
  let E := ε + ε^2/13
  let A := ∑ i, α i*(1+a i)
  let s i := α i * (a i)^2 / (1-a i)
  let S := ∑ i, s i
  let B := (1+E)*L
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hd i : 0 < 1-a i := by linarith [cut i]
  have hs i : 0 ≤ s i := div_nonneg (mul_nonneg (hα i) (sq_nonneg _)) (hd i).le
  have hS : 0 ≤ S := sum_nonneg (fun i _ => hs i)
  have hD : 0 < B+S := by linarith
  have bound : ε*S ≤ 4*A := by
    dsimp [S,A]; rw [mul_sum,mul_sum]
    apply sum_le_sum
    intro i _
    dsimp [s]
    rw [← mul_div_assoc, div_le_iff₀ (hd i)]
    have ha1 : a i ≤ 1 := by linarith [cut i]
    have step : ε * (a i)^2 ≤ 4 * (1+a i) * (1-a i) := by
      have hsq : 2*(a i)^2 ≤ 1+a i := by nlinarith [mul_nonneg (sub_nonneg.mpr ha1) (by linarith [ha i] : 0 ≤ 2*a i+1)]
      nlinarith [mul_le_mul_of_nonneg_left hsq he.le,
        mul_nonneg (by linarith [cut i] : 0 ≤ 1-a i-ε/8) (by linarith [ha i] : 0 ≤ 1+a i)]
    nlinarith [mul_le_mul_of_nonneg_left step (hα i)]
  have coeff : B*(A+S) ≤ (1+ε)*L*(B+S) := by
    have hsmall : A + (E-ε)*S ≤ (1+ε)*L := by
      change A ≤ _ at moment
      dsimp [E]
      nlinarith [mul_le_mul_of_nonneg_left bound he.le,
        mul_le_mul_of_nonneg_left moment he.le,
        mul_nonneg (sub_nonneg.mpr he') (mul_nonneg he.le hL.le)]
    have hgap : 0 ≤ (E-ε)*S := by dsimp [E]; nlinarith [mul_nonneg (sq_nonneg ε) hS]
    have haux := mul_le_mul_of_nonneg_left hsmall (by linarith : 0 ≤ 1+E)
    dsimp [B]
    nlinarith [mul_nonneg hE hgap, mul_le_mul_of_nonneg_right
      (show (1+E)*(A+S) ≤ (1+ε)*((1+E)*L+S) by nlinarith [mul_nonneg hE hgap]) hL.le]
  refine ⟨B/(B+S), fun i => s i/(B+S), by positivity, fun i => div_nonneg (hs i) hD.le, ?_, ?_, ?_⟩
  · rw [← sum_div, ← add_div]; exact div_self hD.ne'
  · intro i hi; simp [s, hi]
  intro u hu v hzero
  have single (i : I) : B * (α i * ((u-v i)/(1-a i))) +
      s i * (B*v i/(a i)^2) = B*(α i*(1+a i)+s i)*u := by
    dsimp [s]
    by_cases hi : a i = 0
    · simp [hi, hzero i hi]; ring
    · field_simp [hi, (hd i).ne']; ring
  have agg := sum_congr (s₁ := univ) rfl (fun i _ => single i)
  rw [sum_add_distrib, ← mul_sum] at agg
  simp_rw [← sum_mul, ← mul_sum, sum_add_distrib] at agg
  change B/(B+S)*_ + ∑ i, s i/(B+S)*(B*v i/(a i)^2) ≤ _
  simp_rw [div_mul_eq_mul_div, ← sum_div, ← add_div, div_le_iff₀ hD]
  rw [agg]
  nlinarith [mul_le_mul_of_nonneg_right coeff hu]

/- Iterating the quadratic improvement reaches the base range after finitely
many steps, even when the starting error is arbitrarily small. -/
lemma bootstrap (P : ℝ → Prop) (base : ∀ x ≥ 2, P x)
    (step : ∀ x, 0 < x → x < 2 → P (x+x^2/13) → P x) (ε : ℝ) (he : 0 < ε) : P ε := by
  let s := ε^2/13
  have hs : 0 < s := by dsimp [s]; positivity
  have go (n : ℕ) : ∀ x ≥ ε, 2 ≤ x + n*s → P x := by
    induction n with
    | zero => simpa using fun x (_ : ε ≤ x) => base x
    | succ n ih =>
      intro x hx h
      by_cases hb : 2 ≤ x
      · exact base _ hb
      apply step _ (he.trans_le hx) (lt_of_not_ge hb)
      apply ih
      · nlinarith [sq_nonneg x]
      · push_cast at h
        have hsq := sq_le_sq' (by linarith : -x ≤ ε) hx
        dsimp [s] at *
        nlinarith
  obtain ⟨n,hn⟩ := exists_nat_gt (2/s)
  exact go n ε le_rfl (by linarith [(div_lt_iff₀ hs).mp hn])

end BurningMixture
namespace BurningMixture
open Finset Set

/- A one-step local construction. C R consists of the attainable bin-count
vectors of genuine covers using radii at most R. Bin masses are unnormalized
lengths, measured in the same coordinates at all recursive scales. -/
def Controlled {Q : Type*} (C : ℝ → Set (Q → ℝ)) (mass : ℝ → Q → ℝ)
    (L R ε : ℝ) : Prop :=
  ∃ (n : ℕ) (a α : Fin n → ℝ), (∀ i, 0 ≤ α i) ∧ (∀ i, 0 ≤ a i) ∧
    (∀ i, a i ≤ 1-ε/8) ∧ (∑ i, α i*(1+a i)) ≤ (1+ε/3)*(L/R) ∧
    ∃ x ∈ convexHull ℝ (C R), ∀ q,
      x q ≤ ∑ i, α i*((mass R q/R - mass (R*a i) q/R)/(1-a i))

def Fractional {Q : Type*} (C : ℝ → Set (Q → ℝ)) (mass : ℝ → Q → ℝ)
    (L R ε : ℝ) : Prop :=
  ∃ x ∈ convexHull ℝ (C R), ∀ q, x q ≤ (1+ε)*L*mass R q/R^2

end BurningMixture
namespace BurningBridge
open SimpleGraph BurningProfiles BurningMixture MeasureTheory Finset Set
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

/- Keep the nominal radius budget and expected first moment separate while gluing pieces. -/
def Law (G : SimpleGraph V) (S : Set V) (R cap δ moment : ℝ) : Prop :=
  ∃ (n : ℕ) (a α : Fin n → ℝ), (∀ i, 0 ≤ α i) ∧
    (∀ i, a i ∈ Icc 0 (1-δ)) ∧ ∑ i, α i*(1+a i) ≤ moment ∧
    ∃ x ∈ convexHull ℝ (Attain (fun q => bin (lo q) (hi q)) G S R cap),
      ∀ q, x q ≤ ∑ i, α i*(overlap (a i) 1 (lo q/R) (hi q/R)/(1-a i))

lemma Law.add {S Z : Set V} {R A B δ M N : ℝ}
    (hS : Law lo hi G S R A δ M) (hZ : Law lo hi G Z R B δ N) :
    Law lo hi G (S ∪ Z) R (A+B) δ (M+N) := by
  obtain ⟨n,a,α,hα,ha,hm,x,hx,hbin⟩ := hS
  obtain ⟨k,b,β,hβ,hb,hn,y,hy,ht⟩ := hZ
  refine ⟨n+k,Fin.addCases a b,Fin.addCases α β,?_,?_,?_,x+y,hull_add _ hx hy,?_⟩
  · exact Fin.addCases (fun i => by simpa using hα i) (fun i => by simpa using hβ i)
  · exact Fin.addCases (fun i => by simpa using ha i) (fun i => by simpa using hb i)
  · simpa [Fin.sum_univ_add] using add_le_add hm hn
  · intro q; simpa [Fin.sum_univ_add] using add_le_add (hbin q) (ht q)

lemma Law.weaken {S Z : Set V} {R A A' δ M M' : ℝ} (sub : Z ⊆ S) (ha : A ≤ A')
    (hm : M ≤ M') (h : Law lo hi G S R A δ M) : Law lo hi G Z R A' δ M' := by
  obtain ⟨n,a,α,hα,hs,hM,x,hx,hbin⟩ := h
  refine ⟨n,a,α,hα,hs,hM.trans hm,x,convexHull_mono ?_ hx,hbin⟩
  rintro y ⟨bs,hr,hc,cover,he⟩
  exact ⟨bs,hr,hc.trans ha,fun v hv => cover v (sub hv),he⟩

lemma Law.controlled {S : Set V} {R A ε L : ℝ} (hR : 0 < R) (he : 0 ≤ ε)
    (h : Law lo hi G S R A (ε/8) ((1+ε/3)*(L/R))) :
    Controlled (fun r => Attain (fun q => bin (lo q) (hi q)) G S r A)
      (fun r q => overlap 0 r (lo q) (hi q)) L R ε := by
  obtain ⟨n,a,α,hα,ha,hm,x,hx,hbin⟩ := h
  refine ⟨n,a,α,hα,fun i => (ha i).1,fun i => (ha i).2,hm,x,hx,fun q => (hbin q).trans_eq ?_⟩
  apply sum_congr rfl; intro i _
  have split := overlap_split (a := 0) (b := R*a i) (c := R) (mul_nonneg hR.le (ha i).1)
    (by nlinarith [mul_le_mul_of_nonneg_left (ha i).2 hR.le]) (lo q) (hi q)
  simp only
  rw [overlap_scale hR,mul_one,split]
  ring

end BurningBridge

namespace BurningMixture
open MeasureTheory Set

/- Continuous cover parameters can be collapsed to a finite mixture of actual
histograms without changing the expected count of any of the finitely many bins. -/
theorem mean_histogram_mem_hull {Ω Q : Type*} [MeasurableSpace Ω] [Fintype Q]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → Q → ℝ) {C : Set (Q → ℝ)}
    (hfinite : (range f).Finite) (hC : ∀ ω, f ω ∈ C)
    (hint : ∀ q, Integrable (fun ω => f ω q) μ) :
    (fun q => ∫ ω, f ω q ∂μ) ∈ convexHull ℝ C := by
  have hi : Integrable f μ := Integrable.of_eval hint
  have hh := (convex_convexHull ℝ (range f)).integral_mem (hfinite.isClosed_convexHull ℝ)
    (Filter.Eventually.of_forall (fun ω => subset_convexHull ℝ _ (mem_range_self ω))) hi
  have he : (fun q => ∫ ω, f ω q ∂μ) = ∫ ω, f ω ∂μ :=
    funext (fun q => (eval_integral hint q).symm)
  exact he ▸ convexHull_mono (range_subset_iff.mpr hC) hh

end BurningMixture
namespace BurningTree
open SimpleGraph BurningBridge BurningPieces BurningProfiles BurningMixture MeasureTheory Set Finset
open scoped unitInterval
variable {V Q : Type} [Fintype V] [Fintype Q] [DecidableEq V] {G : SimpleGraph V}

/- Rounding the edge cut up moves the reference radius by at most the
unit slack permitted in Attain. -/
lemma rounded_piece_scale {R δ : ℝ} (hr : 0 < R) (hd : 0 < δ) (hd' : δ ≤ 1/2) :
    let l := ⌈2*R*(1-δ)⌉₊
    let K := (l:ℝ)/(2*(1-δ))
    0 < K ∧ R ≤ K ∧ K ≤ R+1 ∧ (l:ℝ)/K = 2*(1-δ) := by
  dsimp only
  have hdelta : 0 < 1-δ := by linarith
  have hpos : 0 < 2*(1-δ) := by linarith
  have hlo := Nat.le_ceil (2*R*(1-δ))
  have hhi := Nat.ceil_lt_add_one (a := 2*R*(1-δ)) (by positivity)
  have hn : 0 < (⌈2*R*(1-δ)⌉₊ : ℝ) := lt_of_lt_of_le (by positivity) hlo
  refine ⟨div_pos hn hpos,(le_div_iff₀ hpos).mpr (by linarith), (div_le_iff₀ hpos).mpr (by linarith),?_⟩
  field_simp

lemma hist_finite {Ω : Type} (X : Ω → Q → ℝ) {a b : ℝ}
    (h : ∀ y q, X y q = 0 ∨ X y q = a ∨ X y q = b) : (range X).Finite :=
  (Set.Finite.pi' (fun _ : Q => (Set.toFinite ({0,a,b} : Set ℝ)))).subset
    (by rintro _ ⟨y,rfl⟩ q; simpa using h y q)

private lemma int_hist (f : I → ℝ) (M : ℝ) (hf : Measurable f)
    (hb : ∀ y, f y ∈ Set.Icc 0 M) : Integrable f volume :=
  (memLp_of_bounded (Filter.Eventually.of_forall hb) hf.aestronglyMeasurable 1).integrable le_rfl

/- Every completed minimal fragment has a controlled law at the original
physical radius, even when the integer cut does not equal 2 R (1−δ). -/
private lemma single_law (lo hi : Q → ℝ) {S : Set V} {R δ : ℝ} (hr : 0 < R)
    (hd : 0 < δ) (hd' : δ ≤ 1/2) (one : ∀ t ∈ Set.Icc (1-δ) 1,
      ∃ c : Centre G, ∀ v ∈ S, c.reducedDist v ≤ R*t+1) : Law lo hi G S R R δ (2-δ) := by
  classical
  let f (y : I) := 1-δ+(y:ℝ)*δ
  let X (y : I) (q : Q) := bin (lo q/R) (hi q/R) (f y)
  have hX (y : I) : X y ∈ Attain (fun q => bin (lo q) (hi q)) G S R R := by
    have hl : 1-δ ≤ f y := by dsimp [f]; linarith [mul_nonneg y.prop.1 hd.le]
    have hu : f y ≤ 1 := by dsimp [f]; linarith [mul_le_mul_of_nonneg_right y.prop.2 hd.le]
    have rng : R*f y ∈ Set.Icc 0 R := ⟨mul_nonneg hr.le (by linarith),by nlinarith [mul_le_mul_of_nonneg_left hu hr.le]⟩
    obtain ⟨c,hc⟩ := one (f y) ⟨hl,hu⟩
    refine ⟨[(R*f y,c)],?_,by simpa using rng.2,?_,fun q => by simp [X,bin_scale hr]⟩
    · simpa using rng
    · intro v hv
      exact ⟨(R*f y,c),by simp,hc v hv⟩
  have hFin := hist_finite (a := 1) (b := 2) X (by intro y q; simp only [X,bin,Set.indicator]; split_ifs <;> norm_num)
  have hx := mean_histogram_mem_hull volume X hFin hX (fun q =>
    int_hist _ 1 (single_bin_mean hd (lo q/R) (hi q/R)).1 (single_bin_mean hd _ _).2.1)
  refine ⟨1,fun _ => 1-δ,fun _ => 1,by simp,by intro i; constructor <;> linarith,?_,_,hx,?_⟩
  · simp; linarith
  · intro q
    change (∫ y, X y q) ≤ _
    rw [show (∫ y, X y q) = _ from (single_bin_mean hd (lo q/R) (hi q/R)).2.2]; simp

theorem piece_law (lo hi : Q → ℝ) (ht : G.IsTree) {R δ : ℝ}
    (hr : 0 < R) (hd : 0 < δ) (hd' : δ ≤ 1/2)
    (u : Σ r, Branch G r) (hu : BurningPieces.Minimal ⌈2*R*(1-δ)⌉₊ u) :
    Law lo hi G (↑u.2.vertices : Set V) R u.2.size δ ((u.2.size:ℝ)/R+2*δ) := by
  classical
  let l := ⌈2*R*(1-δ)⌉₊
  let K := (l:ℝ)/(2*(1-δ))
  obtain ⟨hK,hRK,hK1,he⟩ := rounded_piece_scale hr hd hd'
  change 0 < K at hK
  change R ≤ K at hRK
  change K ≤ R+1 at hK1
  change (l:ℝ)/K = 2*(1-δ) at he
  have hsize : (l:ℝ) ≤ u.2.size := by exact_mod_cast hu.1
  have low : 2*(1-δ) ≤ (u.2.size:ℝ)/K := he ▸ div_le_div_of_nonneg_right hsize hK.le
  have shr : R ≤ u.2.size := by
    have h := (le_div_iff₀ hK).mp low
    have := mul_le_mul_of_nonneg_right (show 1 ≤ 2*(1-δ) by linarith) hK.le
    linarith
  have moment := div_le_div_of_nonneg_left (Nat.cast_nonneg (α := ℝ) u.2.size) hr hRK
  have physical (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) : t*K ≤ R*t+1 := by
    nlinarith [mul_le_mul_of_nonneg_left hK1 h0]
  rcases local_geometry ht u hu hK hd hd' low he.le with one | ⟨a,b,ha,hab,hb,hw,hm,pair⟩
  · apply Law.weaken lo hi Set.Subset.rfl shr (show 2-δ ≤ (u.2.size:ℝ)/R+2*δ by linarith)
    apply single_law lo hi hr hd hd'
    intro t ht
    obtain ⟨c,hc⟩ := one t ht
    exact ⟨c,fun v hv => (hc v hv).trans (physical _ (by linarith [ht.1]) ht.2)⟩
  · have hb1 : b < 1 := by linarith
    let s (y : I) := b-(y:ℝ)*(b-a)
    let t (y : I) := b+(y:ℝ)*(1-b)
    let X (y : I) (q : Q) := bin (lo q/R) (hi q/R) (s y) + bin (lo q/R) (hi q/R) (t y)
    have hX (y : I) : X y ∈ Attain (fun q => bin (lo q) (hi q)) G (↑u.2.vertices) R u.2.size := by
      have hsy : s y ∈ Set.Icc 0 1 := by
        have := mul_le_mul_of_nonneg_right y.prop.2 (sub_nonneg.mpr hab.le)
        have := mul_nonneg y.prop.1 (sub_nonneg.mpr hab.le)
        constructor <;> dsimp [s] <;> linarith
      have hty : t y ∈ Set.Icc 0 1 := by
        have := mul_le_mul_of_nonneg_right y.prop.2 (sub_nonneg.mpr hb1.le)
        have := mul_nonneg y.prop.1 (sub_nonneg.mpr hb1.le)
        constructor <;> dsimp [t] <;> linarith
      obtain ⟨hsum,hcov⟩ := pair y y.prop
      change s y+t y ≤ _ at hsum
      have cap : R*s y + R*t y ≤ u.2.size := by
        rw [← mul_add,mul_comm]
        exact (le_div_iff₀ hr).mp (hsum.trans moment)
      obtain ⟨d,c,hc⟩ : ∃ d c : Centre G, ∀ v ∈ u.2.vertices,
          d.reducedDist v ≤ s y*K ∨ c.reducedDist v ≤ t y*K := by
        rcases hcov with ⟨c,hc⟩ | ⟨d,c,hc⟩
        · exact ⟨c,c,fun v hv => Or.inr (hc v hv)⟩
        · exact ⟨d,c,hc⟩
      refine ⟨[(R*s y,d),(R*t y,c)],?_,by simpa using cap,?_,fun q => by simp [X,bin_scale hr]⟩
      · simp only [List.mem_cons,List.not_mem_nil,or_false]
        rintro _ (rfl|rfl) <;> constructor <;> dsimp <;> nlinarith [mul_nonneg hr.le hsy.1,
          mul_nonneg hr.le hty.1,mul_le_mul_of_nonneg_left hsy.2 hr.le,mul_le_mul_of_nonneg_left hty.2 hr.le]
      · intro v hv
        rcases hc v hv with h | h
        · exact ⟨(R*s y,d),by simp,h.trans (physical _ hsy.1 hsy.2)⟩
        · exact ⟨(R*t y,c),by simp,h.trans (physical _ hty.1 hty.2)⟩
    have fx := hist_finite (a := 1) (b := 2) X (by
      intro y q; simp only [X,bin,Set.indicator]; split_ifs <;> norm_num)
    have HX := mean_histogram_mem_hull volume X fx hX (fun q =>
      int_hist _ 2 (pair_bin_mean hab hb1 (lo q/R) (hi q/R)).1 (pair_bin_mean hab hb1 _ _).2.1)
    obtain ⟨α,β,hα,hβ,hmean,hbin⟩ := tail_decomposition hab hb1 hw
    refine ⟨2,![a,b],![α,β],by intro i; fin_cases i <;> simp [hα,hβ],?_,?_,_,HX,?_⟩
    · intro i; fin_cases i <;> simp <;> constructor <;> linarith
    · simp [Fin.sum_univ_two]
      linarith
    · intro q
      change (∫ y, X y q) ≤ _
      rw [show (∫ y, X y q) = _ from (pair_bin_mean hab hb1 (lo q/R) (hi q/R)).2.2]
      simp [Fin.sum_univ_two]
      rw [overlap_split hab.le hb1.le]
      exact (hbin _ _).le

end BurningTree
namespace BurningTree
open SimpleGraph BurningBridge BurningPieces BurningProfiles BurningMixture Set
variable {V Q : Type} [Fintype V] [Fintype Q] [DecidableEq V] {G : SimpleGraph V}

end BurningTree

namespace BurningBridge
open SimpleGraph BurningNumberConjecture
variable {V : Type} {T : SimpleGraph V}
open BurningPieces

private lemma tour [DecidableEq V] {v : V} (t : Branch T v) :
    ∃ p : T.Walk v v, p.length = 2*t.size ∧ ∀ w ∈ t.vertices, w ∈ p.support := by
  induction t with
  | root v => exact ⟨.nil,rfl, by simp [Branch.vertices]⟩
  | edge e t ih =>
    obtain ⟨p,hp,hs⟩ := ih
    refine ⟨.cons e (p.append (.cons e.symm .nil)),by simp [Walk.length_append,Branch.size]; omega,?_⟩
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | h
    · simp
    · simp [Walk.mem_support_append_iff,hs _ h]
  | join a b ha hb =>
    obtain ⟨p,hp,hs⟩ := ha
    obtain ⟨q,hq,hz⟩ := hb
    exact ⟨p.append q,by simp [Walk.length_append,Branch.size,hp,hq]; omega, fun v hv =>
      by simpa only [Walk.mem_support_append_iff] using (Finset.mem_union.mp hv).imp (hs v) (hz v)⟩

lemma interval_cover {k : ℕ} (r : Fin k → ℝ) (hr : ∀ i, 0 ≤ r i) (hk : 0 < k)
    {L : ℝ} (hL : 0 ≤ L) (size : L ≤ 2 * ∑ i, r i) :
    ∃ p : Fin k → ℝ, (∀ i, p i ∈ Set.Icc 0 L) ∧
      ∀ x ∈ Set.Icc 0 L, ∃ i, |x-p i| ≤ r i := by
  induction k generalizing L with
  | zero => omega
  | succ k ih =>
    rw [Fin.sum_univ_succ] at size
    by_cases short : L ≤ 2*r 0
    · refine ⟨fun _ => L/2,fun _ => ⟨by linarith,by linarith⟩,fun x ⟨hx,hx'⟩ => ⟨0,abs_le.mpr ⟨by linarith,by linarith⟩⟩⟩
    have hk' : 0 < k := by
      by_contra! h
      obtain rfl : k = 0 := by omega
      simp only [Finset.univ_eq_empty,Finset.sum_empty,add_zero] at size
      exact short size
    have h0 := hr 0
    obtain ⟨q,hq,cover⟩ := ih (fun i => r i.succ) (fun i => hr i.succ) hk'
      (L := L-2*r 0) (by linarith) (by linarith)
    refine ⟨Fin.cases (r 0) (fun i => 2*r 0+q i), ?_, fun x ⟨hx,hx'⟩ => ?_⟩
    · intro i
      cases i using Fin.cases with
      | zero => exact ⟨h0,by simp; linarith⟩
      | succ i =>
        obtain ⟨h1,h2⟩ := hq i
        exact ⟨by simp; linarith,by simp; linarith⟩
    · by_cases left : x ≤ 2*r 0
      · exact ⟨0,by simp; exact abs_le.mpr ⟨by linarith,by linarith⟩⟩
      · obtain ⟨i,hi⟩ := cover (x-2*r 0) ⟨by linarith,by linarith⟩
        exact ⟨i.succ,by simpa [sub_add_eq_sub_sub] using hi⟩

/- The fractional induction base: any nonempty list of nonnegative real radii
whose sum reaches the number of spanning-tree edges covers the vertex set. -/
theorem cover_of_sum [DecidableEq V] (hT : T.Connected) {v : V} (t : Branch T v)
    {k : ℕ} (r : Fin k → ℝ) (hk : 0 < k) (hr : ∀ i, 0 ≤ r i)
    (sum : (t.size : ℝ) ≤ ∑ i, r i) :
    ∃ c : Fin k → Centre T, ∀ w ∈ t.vertices, ∃ i, (c i).reducedDist w ≤ r i := by
  obtain ⟨q,hq,all⟩ := tour t
  have hlen : (q.length : ℝ) = 2*t.size := by exact_mod_cast hq
  obtain ⟨p,hp,cover⟩ := interval_cover r hr hk (L := q.length) (by positivity) (by linarith)
  choose c hc using fun i => centre_on_walk q hT (p i)
  refine ⟨c,fun w hw => ?_⟩
  obtain ⟨j,hj,hlen⟩ := Walk.mem_support_iff_exists_getVert.mp (all w hw)
  obtain ⟨i,hi⟩ := cover (j : ℝ) ⟨by positivity,by exact_mod_cast hlen⟩
  have bound := hc i j w
  rw [hj,dist_self,Nat.cast_zero,add_zero,abs_sub_comm] at bound
  exact ⟨i,bound.trans hi⟩

end BurningBridge

namespace BurningBridge
open SimpleGraph BurningProfiles BurningMixture MeasureTheory Finset Set
open scoped unitInterval
variable {V Q : Type} [Fintype V] [Fintype Q]

/- Use the same uniform parameter for all pairs. Each pair has constant
total radius R and both coordinates have the uniform law on [0,R]. -/
theorem fractional_base [DecidableEq V] (T : SimpleGraph V) (ht : T.Connected) {v : V} (u : BurningPieces.Branch T v) (lo hi : Q → ℝ)
    (L R ε : ℝ) (hR : 0 < R) (hsmall : 2*R ≤ L) (he : 2 ≤ ε)
    (order : (u.size : ℝ) ≤ L) :
    Fractional (fun t => Attain (fun q => bin (lo q) (hi q)) T (↑u.vertices) t (L+t))
      (fun t q => overlap 0 t (lo q) (hi q)) L R ε := by
  classical
  let k := ⌈L/R⌉₊
  have hL : 0 < L := by linarith
  have hlow : L ≤ (k:ℝ)*R := (div_le_iff₀ hR).mp (Nat.le_ceil _)
  have hhigh : (k:ℝ)*R ≤ L+R := by
    have := Nat.ceil_lt_add_one (div_nonneg hL.le hR.le)
    dsimp [k]
    calc
      _ ≤ (L/R+1)*R := mul_le_mul_of_nonneg_right this.le hR.le
      _ = _ := by field_simp
  have kpos : 0 < k := Nat.ceil_pos.mpr (div_pos hL hR)
  let r (y : I) : Fin (k+k) → ℝ := fun i => if i.val < k then R*(y:ℝ) else R-R*(y:ℝ)
  have inside (y : I) (i) : r y i ∈ Icc 0 R := by
    have hh := mul_le_mul_of_nonneg_left y.prop.2 hR.le
    have hp := mul_nonneg hR.le y.prop.1
    dsimp [r]; split <;> constructor <;> linarith
  have sumr (y : I) : ∑ i, r y i = k*R := by
    rw [Fin.sum_univ_add]; simp [r,Fin.is_lt]
  let X (y : I) (q : Q) := (k : ℝ)*(bin (lo q) (hi q) (R*y) + bin (lo q) (hi q) (R-R*y))
  have attainable (y) : X y ∈ Attain (fun q => bin (lo q) (hi q)) T (↑u.vertices) R (L+R) := by
    obtain ⟨c,hc⟩ := cover_of_sum ht u (r y) (by omega) (fun i => (inside y i).1)
      (by rw [sumr]; exact order.trans hlow)
    use List.ofFn (fun i => (r y i,c i))
    refine ⟨?_,?_,?_,?_⟩
    · intro p hp
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
      apply inside
    · simpa [List.map_ofFn,List.sum_ofFn,Function.comp_def,sumr] using hhigh
    · intro v hv
      obtain ⟨i,hi⟩ := hc v hv
      exact ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,hi.trans (by linarith)⟩
    · intro q
      simp [List.map_ofFn,List.sum_ofFn,Function.comp_def,Fin.sum_univ_add,r,X,Fin.is_lt]; ring
  have ints (q : Q) :
      Integrable (fun y : I => bin (lo q) (hi q) (R*y)) ∧
      Integrable (fun y : I => bin (lo q) (hi q) (R-R*y)) := by
    have int (g : I → ℝ) (hg : Measurable g) :
        Integrable (fun y => bin (lo q) (hi q) (g y)) volume :=
      (memLp_of_bounded (Filter.Eventually.of_forall (fun y => bin_mem (lo q) (hi q) (g y)))
        ((bin_measurable ..).comp hg).aestronglyMeasurable 1).integrable le_rfl
    exact ⟨int _ (by fun_prop),int _ (by fun_prop)⟩
  have finite := BurningTree.hist_finite (a := (k:ℝ)) (b := 2*k) X
    (by intro y q; simp only [X,bin,Set.indicator]; split_ifs <;> norm_num [mul_comm])
  refine ⟨_,mean_histogram_mem_hull volume X finite attainable
    (fun q => ((ints q).1.add (ints q).2).const_mul _),fun q => ?_⟩
  obtain ⟨hu,hd⟩ := affine_bin_means (a := 0) hR (lo q) (hi q)
  simp only [zero_add,sub_zero,mul_comm _ R] at hu hd
  simp only [X,integral_const_mul,integral_add (ints q).1 (ints q).2,hu,hd]
  let u := overlap 0 R (lo q) (hi q)
  change (k:ℝ)*(u/R+u/R) ≤ (1+ε)*L*u/R^2
  rw [le_div_iff₀ (sq_pos_of_pos hR)]
  have hup : 2*(k:ℝ)*R ≤ (1+ε)*L := by nlinarith [mul_nonneg (by linarith : 0 ≤ ε-2) hL.le]
  have h0 : 0 ≤ u := le_max_left ..
  calc
    (k:ℝ)*(u/R+u/R)*R^2 = 2*k*R*u := by field_simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hup h0

end BurningBridge

namespace BurningBridge
open SimpleGraph BurningNumberConjecture

theorem burn_of_scheduled_pieces {V : Type} {J : Type*} {T G : SimpleGraph V} (hTG : T ≤ G)
    (hc : T.Connected) {K : ℕ} (t : J ↪ Fin K) (c : J → Centre T)
    (r : J → ℝ) (ht : ∀ j, ⌈r j⌉₊ + (t j : ℕ) < K)
    (hcover : ∀ v, ∃ j, (c j).reducedDist v ≤ r j+1) :
    burningNumber G ≤ K+2 := by
  let f := t.trans (Fin.castLEEmb (show K ≤ K+2 by omega))
  let ignite := Function.extend f (fun j => (c j).endpoint) (fun _ => Classical.choice hc.nonempty)
  refine Nat.sInf_le ⟨ignite,fun v => ?_⟩
  obtain ⟨j,hj⟩ := hcover v
  refine ⟨f j,?_,?_⟩ <;> rw [show ignite (f j) = (c j).endpoint from f.injective.extend_apply ..]
  · exact (hc.preconnected _ _).mono hTG
  · have hceil := Nat.le_ceil (r j)
    have hh := (c j).round v (⌈r j⌉₊+1) (by push_cast; linarith)
    have hanti := (hc.preconnected (c j).endpoint v).dist_anti hTG
    have := ht j
    change G.dist (c j).endpoint v + (t j : ℕ) < K+2
    omega

end BurningBridge

namespace BurningCover
open MeasureTheory ProbabilityTheory Finset

theorem select_counts {I : Type*} [Fintype I] {Ω : I → Type*} [∀ i, Finite (Ω i)]
    [∀ i, MeasurableSpace (Ω i)] [∀ i, MeasurableSingletonClass (Ω i)]
    (μ : (i : I) → Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)] {q : ℕ}
    (N : Fin (q+1) → (i : I) → Ω i → ℝ) {B η d : ℝ}
    (hn : ∀ k i x, 0 ≤ N k i x) (hb : ∀ (k : Fin q) i x, N k.succ i x ≤ B)
    (hB : 0 ≤ B) (he : 0 < η) (hd : 0 < d)
    (hm : ∀ k, (∑ i, ∫ x, N k i x ∂μ i) ≤ (1-η)*d) (hv : B*q ≤ η^3*d) :
    ∃ ω : Π i, Ω i, ∀ k, (∑ i, N k i (ω i)) ≤ d := by
  classical
  let P := Measure.pi μ
  let S k := ∑ i, fun ω : Π i, Ω i => N k i (ω i)
  let m k := ∫ ω, S k ω ∂P
  let D (k : Fin q) ω := (S k.succ ω - m k.succ)^2
  have mean k : m k ≤ (1-η)*d := by
    simpa [m,S,P,Finset.sum_apply,integral_finsetSum _ (fun _ _ => Integrable.of_finite),
      integral_comp_eval (measurable_of_finite _).aestronglyMeasurable] using hm k
  have var (k : Fin q) : (∫ ω, D k ω ∂P) ≤ B*((1-η)*d) := by
    have lp i : MemLp (N k.succ i) 2 (μ i) := memLp_of_bounded (Filter.Eventually.of_forall
      (fun x => (⟨hn k.succ i x, hb k i x⟩ : N k.succ i x ∈ Set.Icc 0 B)))
      (measurable_of_finite _).aestronglyMeasurable 2
    rw [show (∫ ω, D k ω ∂P) = variance (S k.succ) P from
      (variance_eq_integral (measurable_of_finite _).aemeasurable).symm, variance_sum_pi lp]
    apply le_trans _ (mul_le_mul_of_nonneg_left (hm k.succ) hB)
    rw [mul_sum]
    apply sum_le_sum; intro i _
    have h := variance_le_sub_mul_sub (μ := μ i) (Filter.Eventually.of_forall
      (fun x => (⟨hn k.succ i x, hb k i x⟩ : N k.succ i x ∈ Set.Icc 0 B)))
      (measurable_of_finite _).aemeasurable
    nlinarith [sq_nonneg (∫ x, N k.succ i x ∂μ i)]
  let a := η^2*d
  have ha : 0 < a := by dsimp [a]; positivity
  obtain ⟨ω,hω⟩ := exists_le_integral (μ := P) (f := fun ω => a*S 0 ω + ∑ k, D k ω)
    Integrable.of_finite
  rw [integral_add Integrable.of_finite Integrable.of_finite, integral_const_mul,
    integral_finsetSum _ (fun _ _ => Integrable.of_finite)] at hω
  have hsum := sum_le_sum (s := univ) (fun k _ => var k)
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
  have total : a*S 0 ω + ∑ k, D k ω ≤ a*d := by
    have h := add_le_add (mul_le_mul_of_nonneg_left (mean 0) ha.le) hsum
    change _ ≤ a*((1-η)*d) + _ at h
    have h' := hω.trans h
    dsimp [a] at *
    nlinarith only [h',mul_le_mul_of_nonneg_right hv hd.le,
      mul_nonneg (mul_nonneg (Nat.cast_nonneg q) hB) (mul_nonneg he.le hd.le)]
  have hl : 0 ≤ S 0 ω := by simpa [S, Finset.sum_apply] using sum_nonneg (fun i _ => hn 0 i (ω i))
  refine ⟨ω, fun k => ?_⟩
  suffices h : S k ω ≤ d by simpa [S, Finset.sum_apply] using h
  cases k using Fin.cases with
  | zero =>
    apply le_of_mul_le_mul_left _ ha
    exact (le_add_of_nonneg_right (sum_nonneg (fun k _ => sq_nonneg _))).trans total
  | succ k =>
    have one := single_le_sum (f := fun k => D k ω) (fun _ _ => sq_nonneg _) (mem_univ k)
    have H : (S k.succ ω - m k.succ)^2 ≤ (η*d)^2 := by
      change D k ω ≤ _
      nlinarith only [one,total,mul_nonneg ha.le hl,show a*d = (η*d)^2 by dsimp [a]; ring]
    linarith [le_of_sq_le_sq H (mul_pos he hd).le,mean k.succ]
end BurningCover

namespace BurningCover
open Finset

/- Assign disjoint blocks of d rounds to the radius bins, largest radii first. -/
theorem exists_rounds_of_bins {I : Type*} [Fintype I] {Q d : ℕ}
    (b : I → Fin Q) (r : I → ℕ) (hr : ∀ i, r i ≤ (b i + 1 : ℕ) * d)
    (hb : ∀ q, (univ.filter (fun i => b i = q)).card ≤ d) :
    ∃ f : I ↪ Fin (Q*d + d), ∀ i, r i + (f i : ℕ) < Q*d + d := by
  classical
  let F q := univ.filter (fun i => b i = q)
  have h q : Nonempty (↥(F q) ↪ Fin d) :=
    Function.Embedding.nonempty_of_card_le (by simpa only [Fintype.card_coe, Fintype.card_fin] using hb q)
  let u (i : I) := (h (b i)).some ⟨i, by simp [F]⟩
  let t i := finProdFinEquiv ((b i).rev, u i)
  have inj : Function.Injective t := by
    intro i j hij
    have hp := finProdFinEquiv.injective hij
    have he : b i = b j := Fin.rev_injective (congrArg Prod.fst hp)
    have same {p q} (x : F p) (y : F q) (e : p = q)
        (hu : (h p).some x = (h q).some y) : x.val = y.val := by
      subst q
      exact congrArg Subtype.val ((h p).some.injective hu)
    exact same ⟨i, by simp [F]⟩ ⟨j, by simp [F]⟩ he (congrArg Prod.snd hp)
  refine ⟨⟨fun i => (t i).castLE (by omega), fun _ _ h => inj (Fin.ext (congrArg (Fin.val (n := Q*d + d)) h))⟩,
    fun i => ?_⟩
  change r i + ((u i : ℕ) + d * ((b i).rev : ℕ)) < Q*d + d
  have hu := (u i).isLt
  have hq : ((b i).rev : ℕ) + ((b i : ℕ) + 1) = Q := by
    have := (b i).isLt
    simp [Fin.rev]
  have hid := congrArg (fun x => x * d) hq
  simp only [Nat.add_mul, Nat.one_mul] at hid
  rw [Nat.mul_comm d]
  have hi := hr i
  rw [Nat.add_mul, Nat.one_mul] at hi
  omega

end BurningCover

namespace BurningCover
open Finset MeasureTheory ProbabilityTheory

/- Select a local cover on each piece and assign a different round to every ball.
The bound on *total radius* per sample bounds positive-bin counts; it gives no
pointwise bound on the number of balls in bin zero. -/
theorem schedule_piece_laws {I : Type*} [Fintype I] {Ω : I → Type*} [∀ i, Finite (Ω i)]
    [∀ i, MeasurableSpace (Ω i)] [∀ i, MeasurableSingletonClass (Ω i)]
    (μ : (i : I) → Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (J : (i : I) → Ω i → Type*) [∀ i x, Fintype (J i x)]
    {q d : ℕ} (hd : 0 < d) (b : ∀ i x, J i x → Fin (q+1))
    (r : ∀ i x, J i x → ℝ) (hr : ∀ i x j, 0 ≤ r i x j)
    (hlo : ∀ i x j, b i x j ≠ 0 → (d : ℝ) ≤ r i x j)
    (hhi : ∀ i x j, r i x j ≤ (((b i x j : ℕ) + 1)*d : ℕ))
    {B η : ℝ} (hB : 0 ≤ B) (hη : 0 < η)
    (load : ∀ i x, (∑ j, r i x j) ≤ B*d)
    (mean : ∀ k : Fin (q+1), (∑ i, ∫ x, ((univ.filter (fun j => b i x j = k)).card : ℝ) ∂μ i)
      ≤ (1-η)*d)
    (large : B*q ≤ η^3*d) :
    ∃ ω : Π i, Ω i, ∃ t : (Σ i, J i (ω i)) ↪ Fin ((q+1)*d+d),
      ∀ j, ⌈r j.1 (ω j.1) j.2⌉₊ + (t j : ℕ) < (q+1)*d+d := by
  classical
  let N (k : Fin (q+1)) (i : I) (x : Ω i) : ℝ := (univ.filter (fun j => b i x j = k)).card
  have hd' : 0 < (d : ℝ) := by exact_mod_cast hd
  have lim (k : Fin q) i x : N k.succ i x ≤ B := by
    let s := univ.filter (fun j => b i x j = k.succ)
    apply le_of_mul_le_mul_right _ hd'
    calc
      _ = ∑ _j ∈ s, (d : ℝ) := by simp [s,N]
      _ ≤ ∑ j ∈ s, r i x j := sum_le_sum (fun j hj => hlo i x j (by
        rw [(mem_filter.mp hj).2]; exact Fin.succ_ne_zero k))
      _ ≤ ∑ j, r i x j := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun j _ _ => hr i x j)
      _ ≤ _ := load i x
  obtain ⟨ω,cap⟩ := select_counts μ N (fun _ _ _ => Nat.cast_nonneg _) lim hB hη hd' mean large
  refine ⟨ω, exists_rounds_of_bins (fun j : Σ i, J i (ω i) => b j.1 (ω j.1) j.2)
    (fun j => ⌈r j.1 (ω j.1) j.2⌉₊) (fun j => Nat.ceil_le.mpr (hhi ..)) ?_⟩
  intro k
  have hc := cap k
  dsimp [N] at hc
  exact_mod_cast (show ((univ.filter fun j : Σ i, J i (ω i) => b j.1 (ω j.1) j.2 = k).card : ℝ)
    ≤ d by simpa only [card_filter, Nat.cast_sum, Fintype.sum_sigma, Nat.cast_ite, Nat.cast_one,
      Nat.cast_zero] using hc)

end BurningCover

namespace BurningCover

theorem outer_parameters {ε : ℝ} (he : 0 < ε) :
    ∃ q : ℕ, ∃ η : ℝ, 0 < η ∧ ∀ B : ℝ, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∃ d : ℕ,
      0 < d ∧ B*q ≤ η^3*d ∧
      (1+ε/2)*(n : ℝ)*d / (((q+1 : ℕ) : ℝ)*d)^2 ≤ (1-η)*d ∧
      (((q+1)*d+d+2 : ℕ) : ℝ) ≤ (1+ε)*Real.sqrt n := by
  let A := 1+ε/2
  have hA : 1 < A := by dsimp [A]; linarith
  have hA₀ : 0 < A := by linarith
  obtain ⟨q,hq⟩ := exists_nat_gt (4*A/ε)
  let Q : ℝ := (q : ℝ)+1
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have ratio : A/Q < ε/4 := by
    apply (div_lt_iff₀ hQ).mpr
    have hh := (div_lt_iff₀ he).mp hq
    dsimp [Q]; nlinarith
  let η := 1 - 1/A
  have hη : 0 < η := sub_pos.mpr ((div_lt_one hA₀).mpr hA)
  refine ⟨q,η,hη,fun B => ?_⟩
  obtain ⟨N,hN⟩ := exists_nat_gt (max (4*(Q+3)/ε) (Q*(max 0 (B*q/η^3)+1)/A))
  refine ⟨N^2,fun n hn => ?_⟩
  let s := Real.sqrt n
  have hs : (N : ℝ) ≤ s := Real.le_sqrt_of_sq_le (by exact_mod_cast hn)
  have hlo := (le_max_left _ _).trans_lt hN |>.trans_le hs
  have hbig := (le_max_right _ _).trans_lt hN |>.trans_le hs
  have spos : 0 < s := lt_trans (by positivity : 0 < 4*(Q+3)/ε) hlo
  let d := ⌈A*s/Q⌉₊
  have de : A*s/Q ≤ (d : ℝ) := Nat.le_ceil _
  have du : (d : ℝ) < A*s/Q+1 := Nat.ceil_lt_add_one (by positivity)
  have dpos : 0 < (d : ℝ) := lt_of_lt_of_le (by positivity) de
  have hdQ := (div_le_iff₀ hQ).mp de
  have big := (div_lt_iff₀ hA₀).mp hbig
  have dgt : max 0 (B*q/η^3) < (d:ℝ) := by
    apply lt_of_mul_lt_mul_left (a := Q) _ hQ.le
    nlinarith only [big,hdQ,hQ]
  have sizes : B*q ≤ η^3*d := by
    have hv := (div_lt_iff₀ (pow_pos hη 3)).mp ((le_max_right _ _).trans_lt dgt)
    linarith
  refine ⟨d,by exact_mod_cast dpos,sizes,?_,?_⟩
  · change A*(n:ℝ)*d / (((q+1 : ℕ):ℝ)*d)^2 ≤ (1-η)*d
    rw [show (((q+1 : ℕ):ℝ)) = Q by simp [Q], show 1-η = 1/A by dsimp [η]; ring]
    apply (div_le_iff₀ (sq_pos_of_pos (mul_pos hQ dpos))).mpr
    have hsq := (sq_le_sq₀ (mul_nonneg hA₀.le spos.le) (mul_nonneg hQ.le dpos.le)).mpr
      (show A*s ≤ Q*d by linarith)
    have hs2 : s^2 = n := Real.sq_sqrt (by positivity)
    rw [mul_pow, hs2] at hsq
    field_simp
    nlinarith only [hsq]
  · have dQlt := mul_lt_mul_of_pos_left du hQ
    have key : Q*(A*s/Q) = A*s := by field_simp
    have extra := mul_lt_mul_of_pos_right ratio spos
    have hround := (div_lt_iff₀ he).mp hlo
    push_cast
    change Q*(d:ℝ)+d+2 ≤ (1+ε)*s
    rw [mul_add, key] at dQlt
    have hfact : A*s/Q = (A/Q)*s := by ring
    rw [hfact] at du
    dsimp [A] at dQlt
    nlinarith only [dQlt,du,extra,hround]

end BurningCover

namespace BurningBridge
open SimpleGraph BurningNumberConjecture MeasureTheory Finset
open BurningCover

/- The finite local cover laws needed at one scale. The radius cutoff is
(q+1)d, and the probability laws on different pieces will be sampled independently. -/
structure PieceLaws {V : Type} (T : SimpleGraph V) (q d : ℕ) (A B : ℝ) where
  pieces : ℕ
  choices : Fin pieces → ℕ
  law : ∀ i, PMF (Fin (choices i))
  balls : ∀ i, Fin (choices i) → ℕ
  bin : ∀ i x, Fin (balls i x) → Fin (q+1)
  radius : ∀ i x, Fin (balls i x) → ℝ
  centre : ∀ i x, Fin (balls i x) → Centre T
  nonneg : ∀ i x j, 0 ≤ radius i x j
  lower : ∀ i x j, bin i x j ≠ 0 → (d : ℝ) ≤ radius i x j
  upper : ∀ i x j, radius i x j ≤ (((bin i x j : ℕ)+1)*d : ℕ)
  load : ∀ i x, (∑ j, radius i x j) ≤ B*d
  expected [Fintype V] : ∀ k, (∑ i, ∫ x, ((univ.filter (fun j => bin i x j = k)).card : ℝ)
      ∂(law i).toMeasure) ≤ A*(Fintype.card V : ℝ)*d / (((q+1 : ℕ):ℝ)*d)^2
  cover : ∀ (ω : ∀ i, Fin (choices i)) v, ∃ i j, (centre i (ω i) j).reducedDist v ≤ radius i (ω i) j + 1

end BurningBridge

namespace BurningCover

/- A padded residual of at most C times the cutoff R is absorbed by the
difference between the ε/4 local-law error and the ε/2 scheduling error. -/
theorem absorb_padding {ε C : ℝ} (he : 0 < ε) (hC : 0 ≤ C) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ R : ℝ, R ≤ (1+ε)*Real.sqrt n →
      (1+ε/4)*(n+C*R) ≤ (1+ε/2)*(n:ℝ) := by
  obtain ⟨M,hM⟩ := exists_nat_gt (4*(1+ε/4)*C*(1+ε)/ε)
  refine ⟨M^2,fun n hn R hr => ?_⟩
  have hs : (M:ℝ) ≤ Real.sqrt n := Real.le_sqrt_of_sq_le (by exact_mod_cast hn)
  have h := (div_lt_iff₀ he).mp (hM.trans_le hs)
  have ha : 0 ≤ (1+ε/4)*C := mul_nonneg (by linarith) hC
  have h₁ := mul_le_mul_of_nonneg_left hr ha
  have h₂ := mul_le_mul_of_nonneg_right h.le (Real.sqrt_nonneg (n:ℝ))
  nlinarith only [h₁,h₂, Real.sq_sqrt (show 0 ≤ (n:ℝ) by positivity),
    congrArg (fun y : ℝ => ε*y) (Real.sq_sqrt (show 0 ≤ (n:ℝ) by positivity))]

end BurningCover

namespace BurningProfiles
open Set

def gridLo {q : ℕ} (d : ℕ) (k : Fin (q+1)) : ℝ := if k = 0 then -1 else (k:ℕ)*d
def gridHi {q : ℕ} (d : ℕ) (k : Fin (q+1)) : ℝ := ((k:ℕ)+1 : ℕ)*d

lemma grid_pick {q d : ℕ} {r : ℝ} (hr : 0 ≤ r) (hR : r ≤ (((q+1)*d : ℕ):ℝ)) :
    ∃ k : Fin (q+1), (k ≠ 0 → (d:ℝ) ≤ r) ∧ r ≤ gridHi d k ∧
      ∀ t : Fin (q+1), bin (gridLo d t) (gridHi d t) r = if k=t then 1 else 0 := by
  classical
  have hex : ∃ n : ℕ, r ≤ (((n+1)*d:ℕ):ℝ) := ⟨q,hR⟩
  let k : Fin (q+1) := ⟨Nat.find hex, Nat.lt_succ_iff.mpr (Nat.find_min' hex hR)⟩
  have hu : r ≤ gridHi d k := by simpa [k,gridHi] using Nat.find_spec hex
  have hl (n : ℕ) (hn : n < k.val) : (((n+1)*d:ℕ):ℝ) < r := lt_of_not_ge (Nat.find_min hex hn)
  have low (hk : k ≠ 0) : ((k.val*d:ℕ):ℝ) < r := by
    have hp : 0 < k.val := Nat.pos_of_ne_zero (fun h => hk (Fin.ext h))
    simpa [Nat.sub_add_cancel hp] using hl (k.val-1) (by omega)
  refine ⟨k,fun hk => le_trans ?_ (low hk).le,hu,fun t => ?_⟩
  · exact_mod_cast (show d ≤ k.val*d by
      have hh : 1 ≤ k.val := Nat.pos_of_ne_zero (fun h => hk (Fin.ext h))
      simpa using Nat.mul_le_mul_right d hh)
  have iff : r ∈ Ioc (gridLo d t) (gridHi d t) ↔ k=t := by
    constructor
    · intro hx
      rcases lt_trichotomy t.val k.val with h | h | h
      · have := hl _ h
        exact False.elim ((not_lt_of_ge hx.2) (by simpa [gridHi] using this))
      · exact Fin.ext h.symm
      · have ht : t ≠ 0 := by intro eq; subst t; simp at h
        have le := Nat.mul_le_mul_right d h
        have hi : gridHi d k ≤ gridLo d t := by
          simp [gridHi,gridLo,ht]; exact_mod_cast le
        exact False.elim (not_lt_of_ge (hu.trans hi) hx.1)
    · rintro rfl
      exact ⟨by by_cases h : k = 0
                · simp [gridLo,h]; linarith
                · simpa [gridLo,h] using low h,hu⟩
  simp [bin, Set.indicator, iff]

lemma overlap_grid_le {q d : ℕ} (k : Fin (q+1)) (R : ℝ) :
    overlap 0 R (gridLo d k) (gridHi d k) ≤ d := by
  unfold overlap
  apply max_le (Nat.cast_nonneg _)
  by_cases h : k = 0
  · subst k; simpa [gridLo, gridHi] using (min_le_right R (d:ℝ))
  · exact (sub_le_sub (min_le_right ..) (le_max_right ..)).trans (by
      simp [gridHi,gridLo,h,add_mul])

end BurningProfiles
namespace BurningBridge
open BurningProfiles MeasureTheory Finset

/- The convex combination can be sampled on a standard finite index type.
Every sample retains the actual list of radii and centres witnessing attainability. -/
theorem list_law {V Q : Type} {T : SimpleGraph V} (f : Q → ℝ → ℝ) {S : Set V}
    {R cap : ℝ} {x : Q → ℝ} (hx : x ∈ convexHull ℝ (Attain f T S R cap)) :
    ∃ (n : ℕ) (p : PMF (Fin n)) (bs : Fin n → List (ℝ × Centre T)),
      (∀ j, (∀ z ∈ bs j, z.1 ∈ Set.Icc 0 R) ∧ ((bs j).map Prod.fst).sum ≤ cap ∧
        ∀ v ∈ S, ∃ z ∈ bs j, z.2.reducedDist v ≤ z.1+1) ∧
      ∀ k, (∫ j, ((bs j).map (fun z => f k z.1)).sum ∂p.toMeasure) = x k := by
  classical
  obtain ⟨J,inst,w,z,hw,h₁,hz,rfl⟩ := mem_convexHull_iff_exists_fintype.mp hx
  choose bs hbs using hz
  let e := (Fintype.equivFin J).symm
  let p := PMF.ofFintype (fun j => ENNReal.ofReal (w (e j))) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hw _), e.sum_comp w, h₁, ENNReal.ofReal_one])
  refine ⟨_,p,fun j => bs (e j),fun j => ⟨(hbs _).1,(hbs _).2.1,(hbs _).2.2.1⟩,fun k => ?_⟩
  simp only [PMF.integral_eq_sum, p, PMF.ofFintype_apply, ENNReal.toReal_ofReal (hw _),
    smul_eq_mul,Finset.sum_apply,Pi.smul_apply]
  calc
    _ = ∑ j, w (e j) * z (e j) k := sum_congr rfl (fun j _ => by rw [(hbs (e j)).2.2.2 k])
    _ = _ := e.sum_comp (fun j => w j*z j k)

end BurningBridge

namespace BurningBridge
open BurningProfiles MeasureTheory Finset SimpleGraph

theorem piece_laws_of_hulls {V : Type} [vfin : Fintype V] {T : SimpleGraph V} (_ht : T.Connected)
    {q d m : ℕ} (S : Fin m → Set V) (cap : Fin m → ℝ) {A B : ℝ}
    (all : ∀ v, ∃ i, v ∈ S i) (load : ∀ i, cap i ≤ B*d)
    (x : Fin m → Fin (q+1) → ℝ)
    (hx : ∀ i, x i ∈ convexHull ℝ (Attain (fun k => bin (gridLo d k) (gridHi d k)) T
      (S i) (((q+1)*d : ℕ):ℝ) (cap i)))
    (mean : ∀ k, ∑ i, x i k ≤ A*(Fintype.card V : ℝ)*d / (((q+1 : ℕ):ℝ)*d)^2) :
    Nonempty (PieceLaws T q d A B) := by
  classical
  choose n p bs data hist using fun i => list_law _ (hx i)
  let r i j (k : Fin (bs i j).length) := ((bs i j).get k).1
  have inside i j (k : Fin (bs i j).length) := (data i j).1 _ (List.get_mem (bs i j) k)
  choose label hlow hhigh hbin using fun i j (k : Fin (bs i j).length) =>
    grid_pick (q := q) (d := d) (inside i j k).1 (inside i j k).2
  have sum_map {α : Type} (l : List α) (f : α → ℝ) :
      ∑ k : Fin l.length, f (l.get k) = (l.map f).sum := by
    rw [← List.sum_ofFn]; change (List.ofFn (f ∘ l.get)).sum = _
    rw [← List.map_ofFn, List.ofFn_get]
  refine ⟨⟨m,n,p,fun i j => (bs i j).length,label,r,fun i j k => ((bs i j).get k).2,
    fun i j k => (inside i j k).1,hlow,
    (fun i j k => by simpa [gridHi,r] using hhigh i j k),?_,?_,?_⟩⟩
  · intro i j
    exact (sum_map (bs i j) Prod.fst).le.trans ((data i j).2.1.trans (load i))
  · intro inst k
    cases Subsingleton.elim inst vfin
    apply (le_of_eq ?_).trans (mean k)
    apply sum_congr rfl; intro i _
    rw [← hist i k]
    apply integral_congr_ae
    filter_upwards with j
    rw [← sum_map, card_filter]
    push_cast
    apply sum_congr rfl
    intro t _
    simpa using (hbin i j t k).symm
  · intro ω v
    obtain ⟨i,hi⟩ := all v
    obtain ⟨u,hu,hu'⟩ := (data i (ω i)).2.2 v hi
    obtain ⟨k,rfl⟩ := List.get_of_mem hu
    exact ⟨i,k,hu'⟩

end BurningBridge

/- Build a rooted description of a spanning tree, then split it into small
connected pieces. The remaining fragment always contains the attachment vertex. -/

namespace BurningPieces
open SimpleGraph
variable {V : Type} {G : SimpleGraph V} {r : V}
lemma Branch.attach [DecidableEq V] (t : Branch G r) {u v : V}
    (hu : u ∈ t.vertices) (e : G.Adj u v) :
    ∃ t' : Branch G r, t'.size = t.size+1 ∧ t'.vertices = insert v t.vertices := by
  induction t with
  | root r =>
    have eq : u = r := by simpa [vertices] using hu
    subst u
    exact ⟨.edge e (.root v),rfl,by ext; simp [vertices,or_comm]⟩
  | @edge a b ab t ih =>
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact ⟨.join (.edge ab t) (.edge e (.root v)),by simp [size],by ext; simp [vertices]; tauto⟩
    · obtain ⟨q,hq,hv⟩ := ih hu
      exact ⟨.edge ab q,by simp [size,hq],by simp [vertices,hv,Finset.insert_comm]⟩
  | join a b ia ib =>
    rcases Finset.mem_union.mp hu with h | h
    · obtain ⟨q,hq,hv⟩ := ia h
      exact ⟨.join q b,by simp [size,hq] <;> omega,by ext; simp [vertices,hv] <;> tauto⟩
    · obtain ⟨q,hq,hv⟩ := ib h
      exact ⟨.join a q,by simp [size,hq] <;> omega,by ext; simp [vertices,hv] <;> tauto⟩

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
  classical
  induction t with
  | root => exact ⟨.root _,[],hl,by simp,by simp [Branch.size],by simp⟩
  | @edge a b e t ih =>
    obtain ⟨u,ps,hu,hp,hw,hv⟩ := ih
    let w := Branch.edge e u
    by_cases small : w.size < l
    · refine ⟨w,ps,small,hp,by dsimp [w,Branch.size]; omega,fun v h => ?_⟩
      rcases Finset.mem_insert.mp h with rfl | h
      · exact Or.inl (Finset.mem_insert_self ..)
      · exact (hv v h).imp_left (Finset.mem_insert_of_mem)
    · refine ⟨.root _,⟨_,w⟩::ps,hl,?_,by simp [w,Branch.size]; omega,fun v h => ?_⟩
      · simp only [List.mem_cons, forall_eq_or_imp]
        refine ⟨⟨le_of_not_gt small, ⟨_,Branch.edge e (.root _)⟩,⟨_,u⟩,hl,hu.le,by dsimp [w,Branch.size]; omega,?_⟩,hp⟩
        ext x; simp [w,Branch.vertices]; have := u.root_mem; grind
      · rcases Finset.mem_insert.mp h with rfl | h
        · exact Or.inl (by simp [Branch.vertices])
        · rcases hv v h with h | ⟨p,hp,hv⟩
          · exact Or.inr ⟨_,List.mem_cons_self ..,Finset.mem_insert_of_mem h⟩
          · exact Or.inr ⟨_,List.mem_cons_of_mem _ hp,hv⟩
  | join a b ia ib =>
    obtain ⟨u,us,hu,hus,hw,hv⟩ := ia
    obtain ⟨v,vs,hv',hvs,hw',hv''⟩ := ib
    let w := Branch.join u v
    let ps := us++vs
    have hp : ∀ z ∈ ps, Minimal l z := by intro z hz; exact (List.mem_append.mp hz).elim (hus z) (hvs z)
    have size : w.size + (ps.map (fun p => p.2.size)).sum = (a.join b).size := by
      simp [w,ps,Branch.size]; omega
    have cover (x) (hx : x ∈ (a.join b).vertices) : x ∈ w.vertices ∨ ∃ t ∈ ps, x ∈ t.2.vertices := by
      rcases Finset.mem_union.mp hx with hx | hx
      · rcases hv x hx with hx | ⟨t,ht,hx⟩
        · exact Or.inl (Finset.mem_union_left _ hx)
        · exact Or.inr ⟨t,List.mem_append_left _ ht,hx⟩
      · rcases hv'' x hx with hx | ⟨t,ht,hx⟩
        · exact Or.inl (Finset.mem_union_right _ hx)
        · exact Or.inr ⟨t,List.mem_append_right _ ht,hx⟩
    by_cases small : w.size < l
    · exact ⟨w,ps,small,hp,size,cover⟩
    · refine ⟨.root _,⟨_,w⟩::ps,hl,?_,by simpa [Branch.size] using size, fun x hx => Or.inr ?_⟩
      · simp only [List.mem_cons,forall_eq_or_imp]
        exact ⟨⟨le_of_not_gt small,⟨_,u⟩,⟨_,v⟩,hu.le,hv'.le,rfl,rfl⟩,hp⟩
      · rcases cover x hx with h | ⟨t,ht,h⟩
        · exact ⟨_,List.mem_cons_self ..,h⟩
        · exact ⟨_,List.mem_cons_of_mem _ ht,h⟩

end BurningPieces
namespace BurningPieces
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
      obtain ⟨hmin,a,b,ha,hb,heq,_⟩ := hps (ps.get j) (List.get_mem ..)
      exact ⟨le_rfl,hmin,by change (ps.get j).2.size ≤ 2*D; omega⟩
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
end BurningPieces
namespace BurningBridge
open Finset SimpleGraph BurningPieces BurningProfiles

/- A per-branch fractional histogram bound; only branches of padded length
between M times the cutoff and twice that length are needed. -/
def OuterBranchEstimate (ξ : ℝ) (q M : ℕ) : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (V : Type) [Fintype V] [DecidableEq V] (T : SimpleGraph V), T.IsTree →
    ∀ (t : Σ r, Branch T r) (L : ℕ), t.2.size ≤ L →
      M*((q+1)*d) ≤ L →
      let R : ℝ := ((q+1)*d : ℕ)
      ∃ x ∈ convexHull ℝ (Attain (fun k : Fin (q+1) => bin (gridLo d k) (gridHi d k))
        T (↑t.2.vertices) R (L+R)), ∀ k, x k ≤ (1+ξ)*L*overlap 0 R (gridLo d k) (gridHi d k)/R^2

theorem piece_laws_of_branch_estimate {ξ A : ℝ} (hξ : 0 ≤ ξ) {q M d : ℕ}
    (hM : 0 < M) (hd : 0 < d) (H : OuterBranchEstimate ξ q M)
    {V : Type} [Fintype V] [DecidableEq V] {T : SimpleGraph V} (ht : T.IsTree)
    (hpad : (1+ξ)*((Fintype.card V:ℝ)+M*(((q+1)*d:ℕ):ℝ)) ≤ A*(Fintype.card V:ℝ)) :
    Nonempty (PieceLaws T q d A (((2*M+1)*(q+1):ℕ):ℝ)) := by
  classical
  let R := (q+1)*d
  let D := M*R
  have hR : 0 < R := Nat.mul_pos (Nat.succ_pos _) hd
  obtain ⟨m,s,L,hs,hsum,hcover⟩ := outer_partition ht.connected (Nat.mul_pos hM hR)
  choose x hx hmean using fun i => H d hd V T ht (s i) (L i) (hs i).1 (hs i).2.1
  apply piece_laws_of_hulls ht.connected (fun i => (↑(s i).2.vertices : Set V))
    (fun i => (L i : ℝ)+R) hcover _ x hx
  · intro k
    have bound i : x i k ≤ (1+ξ)*(L i:ℝ)*d/(R:ℝ)^2 := by
      refine (hmean i k).trans (div_le_div_of_nonneg_right ?_ (sq_nonneg _))
      exact mul_le_mul_of_nonneg_left (overlap_grid_le k R) (by positivity)
    have hh := sum_le_sum (s := univ) (fun i _ => bound i)
    simp_rw [← sum_div, ← sum_mul, ← mul_sum, ← Nat.cast_sum] at hh
    have hc : (∑ i, L i) ≤ Fintype.card V + D := by omega
    have hc' : ((∑ i, L i : ℕ):ℝ) ≤ (Fintype.card V:ℝ)+M*R := by exact_mod_cast hc
    rw [← Nat.cast_mul]
    exact hh.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
      ((mul_le_mul_of_nonneg_left hc' (by linarith : 0 ≤ 1+ξ)).trans hpad) (Nat.cast_nonneg _)) (sq_nonneg _))
  · intro i
    have hh := (hs i).2.2
    change L i ≤ 2*(M*R) at hh
    have hh' : L i + R ≤ ((2*M+1)*(q+1))*d := by
      calc
        _ ≤ 2*(M*R)+R := Nat.add_le_add_right hh _
        _ = _ := by dsimp [R]; ring
    exact_mod_cast hh'

end BurningBridge

namespace BurningBridge
open BurningCover Finset SimpleGraph BurningNumberConjecture

theorem norin_turcotte_of_outer_branch_estimate
    (branch : ∀ ξ : ℝ, 0 < ξ → ∀ q : ℕ, ∃ M : ℕ, 0 < M ∧ OuterBranchEstimate ξ q M) :
    type_of% @burning_number_conjecture.variants.norin_turcotte := by
  classical
  intro ε he
  obtain ⟨q,η,hη,pars⟩ := outer_parameters he
  obtain ⟨M,hM,H⟩ := branch (ε/4) (by positivity) q
  let B : ℝ := (((2*M+1)*(q+1):ℕ):ℝ)
  obtain ⟨n₀,hN⟩ := pars B
  obtain ⟨N,hP⟩ := absorb_padding (C := (M:ℝ)) he (by positivity)
  refine ⟨max N n₀, fun V _ G hc hn => ?_⟩
  obtain ⟨T,hTG,hT⟩ := hc.exists_isTree_le
  obtain ⟨d,hd,large,mean,time⟩ := hN (Fintype.card V) ((le_max_right ..).trans hn)
  have hR : (((q+1)*d:ℕ):ℝ) ≤ (1+ε)*Real.sqrt (Fintype.card V) :=
    (Nat.cast_le.mpr (show (q+1)*d ≤ (q+1)*d+d+2 by omega)).trans time
  obtain ⟨p⟩ := piece_laws_of_branch_estimate (by positivity : 0 ≤ ε/4) hM hd H hT
    (hP _ ((le_max_left ..).trans hn) _ hR)
  obtain ⟨ω,t,ht⟩ := schedule_piece_laws (fun i => (p.law i).toMeasure)
    (fun i x => Fin (p.balls i x)) hd p.bin p.radius p.nonneg p.lower p.upper
    (Nat.cast_nonneg _) hη p.load (fun k => (p.expected k).trans mean) large
  have hburn := burn_of_scheduled_pieces hTG hT.connected t
    (fun j => p.centre j.1 (ω j.1) j.2) (fun j => p.radius j.1 (ω j.1) j.2) ht (by
      intro v; obtain ⟨i,j,h⟩ := p.cover ω v; exact ⟨⟨i,j⟩,h⟩)
  exact (Nat.cast_le (α := ℝ).mpr hburn).trans time

end BurningBridge

namespace BurningTree
open SimpleGraph BurningPieces BurningBridge BurningProfiles BurningMixture MeasureTheory Set
open scoped unitInterval
variable {V Q : Type} [Fintype V] [Fintype Q] [DecidableEq V] {G : SimpleGraph V}

/- A fragment smaller than the cut fits in one ball drawn from the top interval. -/
lemma remainder_law (lo hi : Q → ℝ) (ht : G.IsTree) {r : V} (t : Branch G r)
    {R δ : ℝ} (hr : 0 < R) (hd : 0 < δ) (hd' : δ ≤ 1/2)
    (hsmall : t.size < ⌈2*R*(1-δ)⌉₊) :
    Law lo hi G (↑t.vertices) R R δ 2 := by
  classical
  have hmin : BurningPieces.Minimal t.size ⟨r,t⟩ := by
    refine ⟨le_rfl,⟨r,t⟩,⟨r,.root r⟩,le_rfl,Nat.zero_le _,by simp [Branch.size],?_⟩
    exact (Finset.union_eq_left.mpr (Finset.singleton_subset_iff.mpr t.root_mem)).symm
  obtain ⟨m,B,_,_,hB,he,one,_⟩ := branch_piece_profiles ht ⟨r,t⟩ hmin
  obtain ⟨c,hc⟩ := one B le_rfl
  have hcut : (t.size : ℝ) < 2*R*(1-δ) := Nat.lt_ceil.mp hsmall
  apply Law.weaken lo hi Set.Subset.rfl le_rfl (show 2-δ ≤ 2 by linarith)
  apply single_law lo hi hr hd hd'
  intro t' ht'
  exact ⟨c,fun v hv => (hc v hv).trans (by nlinarith [mul_le_mul_of_nonneg_left ht'.1 hr.le])⟩

/- Glue all completed fragments onto a fixed remainder, charging only one extra ball. -/
lemma glue_piece_list (lo hi : Q → ℝ) (ht : G.IsTree) {R δ : ℝ}
    (hr : 0 < R) (hd : 0 < δ) (hd' : δ ≤ 1/2) {Z : Set V}
    (hz : Law lo hi G Z R R δ 2) (ps : List (Σ r, Branch G r))
    (hps : ∀ u ∈ ps, BurningPieces.Minimal ⌈2*R*(1-δ)⌉₊ u) :
    let s : ℝ := ((ps.map (fun u => u.2.size)).sum : ℕ)
    Law lo hi G {v | v ∈ Z ∨ ∃ u ∈ ps, v ∈ u.2.vertices} R (R+s) δ (2+(1+2*δ)*(s/R)) := by
  induction ps with
  | nil => simpa using hz
  | cons u ps ih =>
    have hm := hps u List.mem_cons_self
    have hsize := (Nat.le_ceil (2*R*(1-δ))).trans (Nat.cast_le.mpr hm.1)
    have ratio : 1 ≤ (u.2.size:ℝ)/R := (le_div_iff₀ hr).mpr (by
      nlinarith [mul_nonneg hr.le (show 0 ≤ 1-2*δ by linarith)])
    have piece := piece_law lo hi ht hr hd hd' u hm
    have whole := Law.add lo hi (ih (fun v hv => hps v (List.mem_cons_of_mem _ hv))) piece
    apply Law.weaken lo hi _ _ _ whole
    · intro v hv
      rcases hv with h | ⟨u',hu,hv⟩
      · exact Or.inl (Or.inl h)
      · rcases List.mem_cons.mp hu with rfl | hu
        · exact Or.inr hv
        · exact Or.inl (Or.inr ⟨u',hu,hv⟩)
    · simp; linarith
    · simp only [List.map_cons,List.sum_cons,Nat.cast_add,add_div]
      nlinarith only [mul_le_mul_of_nonneg_left ratio hd.le]

/- Controlled law for a whole branch with a real upper budget for its edge count. -/
theorem controlled_tree (lo hi : Q → ℝ) (ht : G.IsTree) {r : V} (t : Branch G r)
    {L R ε : ℝ} (hs : (t.size:ℝ) ≤ L) (hr : 0 < R) (he : 0 < ε) (he' : ε ≤ 4)
    (hsmall : 24*R ≤ ε*L) :
    Controlled (fun s => Attain (fun q => bin (lo q) (hi q)) G (↑t.vertices) s (L+R))
      (fun s q => overlap 0 s (lo q) (hi q)) L R ε := by
  classical
  let δ := ε/8
  have hd : 0 < δ := by dsimp [δ]; positivity
  have hd' : δ ≤ 1/2 := by dsimp [δ]; linarith
  have hl : 0 < ⌈2*R*(1-δ)⌉₊ := Nat.ceil_pos.mpr (mul_pos (by positivity) (by linarith))
  obtain ⟨rest,ps,hsz,hps,htotal,hcover⟩ := chop t hl
  have h := glue_piece_list lo hi ht hr hd hd' (remainder_law lo hi ht rest hr hd hd' hsz) ps hps
  let s := (ps.map (fun u => u.2.size)).sum
  have hs' : (s:ℝ) ≤ L := (Nat.cast_le.mpr (show s ≤ t.size by dsimp [s]; omega)).trans hs
  apply Law.controlled lo hi hr he.le
  apply Law.weaken lo hi (fun v hv => hcover v hv) (by change R+(s:ℝ) ≤ L+R; linarith) _ h
  change 2+(1+2*δ)*((s:ℝ)/R) ≤ (1+ε/3)*(L/R)
  have h₁ := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hs' hr.le) (show 0 ≤ 1+2*δ by linarith)
  apply (show 2+(1+2*δ)*(s/R) ≤ 2+(1+2*δ)*(L/R) by linarith only [h₁]).trans
  dsimp only [δ]
  field_simp
  nlinarith

end BurningTree

namespace BurningMixture
open Finset Set
theorem fractional_bootstrap_from {Q : Type*} (C : ℝ → Set (Q → ℝ)) (mono : Monotone C)
    (mass : ℝ → Q → ℝ) (hm : ∀ R > 0, ∀ q, 0 ≤ mass R q) (hz : ∀ q, mass 0 q = 0)
    {L Rmax εmin : ℝ} (hL : 0 < L)
    (base : ∀ ε ≥ 2, ∀ R ∈ Ioc 0 Rmax, Fractional C mass L R ε)
    (localCover : ∀ ε, εmin ≤ ε → 0 < ε → ε < 2 → ∀ R ∈ Ioc 0 Rmax, Controlled C mass L R ε)
    (ε : ℝ) (he : 0 < ε) (hmin : εmin ≤ ε) : ∀ R ∈ Ioc 0 Rmax, Fractional C mass L R ε := by
  classical
  apply bootstrap (P := fun e => εmin ≤ e → ∀ R ∈ Ioc 0 Rmax, Fractional C mass L R e) (fun e he _ => base e he) _ ε he hmin
  intro e he he' ih hlow R hR
  obtain ⟨n,a,α,hα,ha,cut,moment,x,hx,hctrl⟩ := localCover e hlow he he' R hR
  obtain ⟨p,w,hp,hw,hw₁,hw₀,mix⟩ := uniform_mix_supported he he'.le
    (div_pos hL hR.1) a α hα ha cut moment
  let E := e+e^2/13
  have branch (i : Fin n) : ∃ z ∈ convexHull ℝ (C R), ∀ q,
      w i*z q ≤ w i*((1+E)*(L/R)*(mass (R*a i) q/R)/(a i)^2) := by
    by_cases h : a i = 0
    · exact ⟨x,hx,fun q => by simp [hw₀ i h]⟩
    have pos := lt_of_le_of_ne (ha i) (Ne.symm h)
    have less : R*a i ≤ R := by
      have hi : a i ≤ 1 := by linarith [cut i]
      simpa using mul_le_mul_of_nonneg_left hi hR.1.le
    obtain ⟨z,hz',hq⟩ := ih (by nlinarith [sq_nonneg e]) (R*a i) ⟨mul_pos hR.1 pos, less.trans hR.2⟩
    refine ⟨z, convexHull_mono (mono less) hz', fun q => mul_le_mul_of_nonneg_left ?_ (hw i)⟩
    exact (hq q).trans_eq (by dsimp [E]; ring)
  choose z hmem hbound using branch
  let weights : Option (Fin n) → ℝ := Option.elim' p w
  let points : Option (Fin n) → Q → ℝ := Option.elim' x z
  have inHull : (∑ j, weights j • points j) ∈ convexHull ℝ (C R) := by
    apply (convex_convexHull ℝ _).sum_mem
    · rintro (_ | i) _; exact hp; exact hw i
    · simpa [weights, Fintype.sum_option] using hw₁
    · rintro (_ | i) _; exact hx; exact hmem i
  refine ⟨_,inHull,fun q => ?_⟩
  simp only [Fintype.sum_option, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change p*x q + ∑ i, w i*z i q ≤ _
  have h := mix (mass R q/R) (div_nonneg (hm R hR.1 q) hR.1.le)
    (fun i => mass (R*a i) q/R) (fun i hi => by simp [hi, hz q])
  exact ((add_le_add (mul_le_mul_of_nonneg_left (hctrl q) hp)
    (sum_le_sum (fun i _ => hbound i q))).trans h).trans_eq (by ring)

end BurningMixture

namespace BurningBridge
open BurningProfiles BurningMixture BurningPieces SimpleGraph Set
variable {V Q : Type} [Fintype V] [Fintype Q] [DecidableEq V] {T : SimpleGraph V}

/- Above the requested accuracy the same length-to-radius ratio suffices for
every recursive use of the local construction. -/
theorem fractional_branch (t : Σ r, Branch T r) (lo hi : Q → ℝ) {L R ξ : ℝ}
    (hξ : 0 < ξ) (hR : 0 < R) (len : 2*R ≤ L) (room : 24*R ≤ ξ*L)
    (ht : T.IsTree) (hs : (t.2.size:ℝ) ≤ L) :
    Fractional (fun z => Attain (fun q => bin (lo q) (hi q)) T (↑t.2.vertices) z (L+z))
      (fun z q => overlap 0 z (lo q) (hi q)) L R ξ := by
  have hL : 0 < L := by linarith
  have hz (q : Q) : overlap 0 0 (lo q) (hi q) = 0 :=
    max_eq_left (sub_nonpos.mpr ((min_le_left ..).trans (le_max_left ..)))
  refine fractional_bootstrap_from _ (fun _ _ h => attainable_mono _ h (add_le_add le_rfl h)) _
    (fun s hs q => le_max_left _ _) hz hL ?_ ?_ ξ hξ (le_refl ξ) R ⟨hR,le_rfl⟩
  · intro e he s hs
    exact fractional_base T ht.connected t.2 _ _ _ _ _ hs.1 (by linarith [hs.2]) he ‹(t.2.size:ℝ) ≤ L›
  · intro e hlow he he' s hs
    exact BurningTree.controlled_tree _ _ ht t.2 ‹(t.2.size:ℝ) ≤ L› hs.1 he (by linarith)
      (by nlinarith [hs.2,mul_le_mul_of_nonneg_right hlow hL.le])

end BurningBridge

namespace BurningBridge
open SimpleGraph BurningPieces BurningProfiles BurningMixture

theorem branch_estimate {ξ : ℝ} (hξ : 0 < ξ) (q : ℕ) :
    ∃ M : ℕ, 0 < M ∧ OuterBranchEstimate ξ q M := by
  let M := max 2 ⌈24/ξ⌉₊
  refine ⟨M,lt_of_lt_of_le (by decide : 0 < 2) (le_max_left ..),?_⟩
  intro d hd V inst dec T ht t L hs hmin
  let R := ((q+1)*d : ℕ)
  have hR : 0 < (R : ℝ) := by exact_mod_cast Nat.mul_pos (Nat.succ_pos _) hd
  have hMR : (M:ℝ)*R ≤ L := by exact_mod_cast hmin
  have hTwo : (2:ℝ) ≤ M := by exact_mod_cast (le_max_left 2 ⌈24/ξ⌉₊)
  have hRatio : 24/ξ ≤ M := (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right ..))
  have hRoom : 24*(R:ℝ) ≤ ξ*L := calc
    _ ≤ ((M:ℝ)*ξ)*R := mul_le_mul_of_nonneg_right ((div_le_iff₀ hξ).mp hRatio) hR.le
    _ = ξ*(M*R) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hMR hξ.le
  exact fractional_branch t (gridLo d) (gridHi d) hξ hR
    ((mul_le_mul_of_nonneg_right hTwo hR.le).trans hMR) hRoom ht (Nat.cast_le.mpr hs)

end BurningBridge

theorem OMA.solution : type_of% @BurningNumberConjecture.burning_number_conjecture.variants.norin_turcotte :=
  BurningBridge.norin_turcotte_of_outer_branch_estimate (fun _ he q => BurningBridge.branch_estimate he q)
