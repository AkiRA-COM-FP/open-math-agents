import OMAReductions.R_Erdos89_erdos_89_R1

-- Reduction of Erdos89.erdos_89.R1.H2. Credit: @wispiANt
open Finset Filter EuclideanGeometry

namespace OMA.R_Erdos89_erdos_89_R1_H2_R3

/-- The remaining squarefree diagonal estimate. For every dense subset and
assignment of occupied pins, any modulus compatible with the vertical progression
in each pin-column pair puts more than k pairs in some form-value residue.
Every nonempty family of realized gaps also exceeds the divisor budget.
The estimate is only required outside the polynomial coefficient range for
fixed exponent r and density parameter t₀, chosen uniformly in the configuration. -/
def H1 : Prop :=
  ∃ r t₀ C : ℕ, ∀ (d : ℕ) (S : Finset (ℤ × ℤ)) (k : ℕ), 0 < d → Squarefree d →
    0 < k → (S.card : ℝ) ≤ Real.exp ((k:ℝ)^2) →
    (∀ p ∈ S, ∀ W : ℕ, (∀ z ∈ S, (z.1-p.1).natAbs ≤ W) →
      W^2 ≤ t₀*S.card → d^r < W^2) →
    (∀ T ⊆ S, S.card ≤ 2*T.card → ∀ (M : ℤ), 0 < M →
      ∀ (p : ℤ × ℤ → ℤ × ℤ) (t s : (ℤ × ℤ) × ℤ → ℤ),
      (∀ x ∈ T, let e := (p x,x.1)
        p x ∈ S ∧ s e ∣ x.2-(p x).2-t e ∧
        M ∣ (d:ℤ)*s e*(2*t e+s e) ∧ M ∣ 2*(d:ℤ)*(s e)^2) →
      ∃ r : ℤ, k < ((T.image fun x => (p x,x.1)).filter fun e =>
        ((e.2-e.1.1)^2+(d:ℤ)*(t e)^2) % M = r).card) →
    (∀ (A : Finset ℕ) (X : ℕ → Finset ℕ) (W : ℕ → ℕ),
      (∀ a ∈ A, X a ⊆ range (W a+1)) →
      (∀ a ∈ A, ∀ u ∈ X a, ∃ x ∈ S, ∃ y ∈ S,
        u = (x.1-y.1).natAbs ∧ a = d*(x.2-y.2).natAbs^2) →
      let mass := ∑ a ∈ A, (X a).card
      let cost := ∑ a ∈ A, ∑ b ∈ A, if a=b then (X a).card else
        let h := max a b-min a b
        min (min (X a).card (X b).card) (h.divisors.filter fun j =>
          j ≤ h/j ∧ h/j+j ≤ 2*W (min a b) ∧ h/j-j ≤ 2*W (max a b) ∧ j%2 = (h/j)%2).card
      0 < mass → k*mass^2 < S.card*cost) →
    let q := fun v : ℤ × ℤ => v.1^2+(d:ℤ)*v.2^2
    S.card ≤ k*C*((S.offDiag.image fun xy => q (xy.1-xy.2)).card+1)

/-- The complementary finite estimate for minimizers without a binary quadratic
lattice model on any subset containing half the points. -/
def H2 : Prop :=
  let X := {p : ℝ² // ∀ i : Fin 2, IsIntegral ℤ (p i)}
  ∃ C : ℕ, ∀ (S : Finset X) (k : ℕ), 0 < k → (S.card : ℝ) ≤ Real.exp ((k:ℝ)^2) →
    distinctDistances S = minimalDistinctDistances X S.card →
    (∀ T ⊆ S, S.card ≤ 2*T.card → ¬ (∃ (f : X → ℤ × ℤ) (a b c : ℝ), ∀ x ∈ T, ∀ y ∈ T,
          dist x y^2 = a*(f x-f y).1^2+b*(f x-f y).1*(f x-f y).2+c*(f x-f y).2^2)) →
    S.card ≤ k*C*(distinctDistances S+1)

section Shells

/-- On a line through the origin a nonzero quadratic level has at most two points. -/
private theorem line_shell (T : Finset (ℤ × ℤ)) (a b c r u v : ℝ) (hr : r ≠ 0)
    (huv : u ≠ 0 ∨ v ≠ 0)
    (line : ∀ x ∈ T, u*x.1+v*x.2 = 0)
    (shell : ∀ x ∈ T, a*x.1^2+b*x.1*x.2+c*x.2^2 = r) : T.card ≤ 2 := by
  classical
  have count (g : ℤ × ℤ → ℝ) (l : ℝ)
      (inj : Set.InjOn g (T : Set (ℤ × ℤ)))
      (he : ∀ x ∈ T, l*(g x)^2 = r) : T.card ≤ 2 := by
    rcases T.eq_empty_or_nonempty with rfl|⟨x,hx⟩
    · simp
    have hl : l ≠ 0 := by intro h; simpa [h,hr.symm] using he x hx
    have sub : T.image g ⊆ {g x,-g x} := by
      intro t ht
      obtain ⟨y,hy,rfl⟩ := mem_image.mp ht
      have hh := mul_left_cancel₀ hl ((he y hy).trans (he x hx).symm)
      simpa using sq_eq_sq_iff_eq_or_eq_neg.mp hh
    rw [← card_image_of_injOn inj]
    exact (card_le_card sub).trans (card_le_two ..)
  by_cases hv : v = 0
  · have hu := huv.resolve_right (not_not.mpr hv)
    have zero (x) (hx : x ∈ T) : (x.1:ℝ) = 0 := by
      have := line x hx
      simpa [hv,hu] using this
    refine count (fun x => x.2) c ?_ ?_
    · intro x hx y hy h
      change (x.2:ℝ) = y.2 at h
      exact Prod.ext (by exact_mod_cast (zero x hx).trans (zero y hy).symm) (by exact_mod_cast h)
    · intro x hx
      simpa [zero x hx] using shell x hx
  let t := -u/v
  have eqt (x) (hx : x ∈ T) : (x.2:ℝ) = t*x.1 := by
    dsimp [t]
    rw [div_mul_eq_mul_div,eq_div_iff hv]
    linarith [line x hx]
  refine count (fun x => x.1) (a+b*t+c*t^2) ?_ ?_
  · intro x hx y hy h
    change (x.1:ℝ) = y.1 at h
    have he : (x.2:ℝ) = y.2 := (eqt x hx).trans (by rw [h,← eqt y hy])
    exact Prod.ext (by exact_mod_cast h) (by exact_mod_cast he)
  · intro x hx
    have hh := shell x hx
    rw [eqt x hx] at hh
    linear_combination hh

/-- A second independent quadratic equation restricts a shell to two lines. -/
private theorem conic_shell (T : Finset (ℤ × ℤ)) (a b c r A B C : ℝ) (hr : r ≠ 0)
    (hn : A ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0)
    (hom : ∀ x ∈ T, A*x.1^2+B*x.1*x.2+C*x.2^2 = 0)
    (shell : ∀ x ∈ T, a*x.1^2+b*x.1*x.2+c*x.2^2 = r) : T.card ≤ 4 := by
  classical
  have split (u v U V : ℝ) (h₁ : u ≠ 0 ∨ v ≠ 0) (h₂ : U ≠ 0 ∨ V ≠ 0)
      (cover : ∀ x ∈ T, (u*x.1+v*x.2)*(U*x.1+V*x.2) = 0) : T.card ≤ 4 := by
    let L := T.filter fun x => u*x.1+v*x.2 = 0
    let M := T.filter fun x => U*x.1+V*x.2 = 0
    have sub : T ⊆ L ∪ M := by
      intro x hx
      rcases mul_eq_zero.mp (cover x hx) with h|h
      · exact mem_union_left _ (mem_filter.mpr ⟨hx,h⟩)
      · exact mem_union_right _ (mem_filter.mpr ⟨hx,h⟩)
    have bounds (u v : ℝ) (h : u ≠ 0 ∨ v ≠ 0) :
        (T.filter fun x => u*x.1+v*x.2 = 0).card ≤ 2 :=
      line_shell _ a b c r u v hr h (fun _ hx => (mem_filter.mp hx).2)
        (fun x hx => shell x (mem_filter.mp hx).1)
    exact (card_le_card sub).trans ((card_union_le L M).trans (Nat.add_le_add (bounds u v h₁) (bounds U V h₂)))
  by_cases hC : C = 0
  · apply split 1 0 A B (Or.inl one_ne_zero) (by tauto)
    intro x hx
    have he := hom x hx
    rw [hC] at he
    linear_combination he
  rcases T.eq_empty_or_nonempty with rfl|⟨o,ho⟩
  · simp
  have hx : (o.1:ℝ) ≠ 0 := by
    intro h
    have he := hom o ho
    simp [h,hC] at he
    have hz := shell o ho
    simp [h,he,hr.symm] at hz
  let t := (o.2:ℝ)/o.1
  have ht : t*(o.1:ℝ) = o.2 := div_mul_cancel₀ _ hx
  have root : A+B*t+C*t^2 = 0 := by
    apply (mul_eq_zero.mp (show (A+B*t+C*t^2)*(o.1:ℝ)^2 = 0 by
      calc
        _ = A*o.1^2 + B*o.1*(t*o.1) + C*(t*o.1)^2 := by ring
        _ = 0 := by rw [ht]; exact hom o ho)).resolve_right (pow_ne_zero _ hx)
  apply split (-t) 1 (B+C*t) C (Or.inr one_ne_zero) (Or.inr hC)
  intro x hx
  linear_combination hom x hx - (x.1:ℝ)^2*root

private theorem observe_value (f : ℝ →ₗ[ℚ] ℚ) (a b c : ℝ) (x y : ℤ) :
    f (a*x^2+b*x*y+c*y^2) = f a*x^2+f b*x*y+f c*y^2 := by
  have scale (r : ℝ) (v : ℤ) : f (r*v) = f r*v := by
    simpa [zsmul_eq_mul, mul_comm] using map_zsmul f v r
  rw [show a*x^2+b*x*y+c*y^2 = a*((x^2:ℤ):ℝ)+b*((x*y:ℤ):ℝ)+c*((y^2:ℤ):ℝ) by push_cast; ring]
  rw [map_add, map_add, scale, scale, scale]
  push_cast
  ring

/-- Without a common rational scale, each positive level of an oblique binary form
contains at most four integral vectors. No preferred lattice axes are required. -/
theorem oblique_shell (T : Finset (ℤ × ℤ)) (a b c r : ℝ) (hr : 0 < r)
    (incomm : ¬ ∃ L : ℝ, 0 < L ∧ ∃ A B C : ℚ, a=L*A ∧ b=L*B ∧ c=L*C)
    (hs : ∀ x ∈ T, a*x.1^2+b*x.1*x.2+c*x.2^2 = r) : T.card ≤ 4 := by
  obtain ⟨f,hf⟩ := Module.Projective.exists_dual_ne_zero ℚ hr.ne'
  let g := fun x : ℝ => (f r:ℝ)*x-r*(f x:ℝ)
  have hfr : (f r:ℝ) ≠ 0 := by exact_mod_cast hf
  have hn : g a ≠ 0 ∨ g b ≠ 0 ∨ g c ≠ 0 := by
    by_contra! h
    have prop (x : ℝ) (hx : g x = 0) : x = r*((f x/f r : ℚ):ℝ) := by
      rw [Rat.cast_div,mul_div_assoc',eq_div_iff hfr]
      dsimp [g] at hx
      linarith
    exact incomm ⟨r,hr,_,_,_,prop a h.1,prop b h.2.1,prop c h.2.2⟩
  apply conic_shell T a b c r (g a) (g b) (g c) hr.ne' hn _ hs
  intro x hx
  have he := hs x hx
  have hq := congrArg f he
  rw [observe_value] at hq
  have he' : (f a:ℝ)*x.1^2+(f b:ℝ)*x.1*x.2+(f c:ℝ)*x.2^2 = (f r:ℝ) := by
    exact_mod_cast hq
  dsimp [g]
  linear_combination (f r:ℝ)*he - r*he'

/-- Three commensurable squared side lengths of a noncollinear lattice triangle
force a common rational scale for all three coefficients of the ambient form. -/
theorem triangle_forces_scale (a b c : ℝ) (i j k l : ℤ) (hn : i*l-j*k ≠ 0)
    (L : ℝ) (hL : 0 < L) (s t u : ℚ)
    (h₁ : a*i^2+b*i*j+c*j^2 = L*s)
    (h₂ : a*k^2+b*k*l+c*l^2 = L*t)
    (h₃ : a*((i:ℝ)-k)^2+b*(i-k)*(j-l)+c*((j:ℝ)-l)^2 = L*u) :
    ∃ M : ℝ, 0 < M ∧ ∃ A B C : ℚ, a=M*A ∧ b=M*B ∧ c=M*C := by
  have hdet : (i:ℝ)*l-j*k ≠ 0 := by exact_mod_cast hn
  refine ⟨L/((i:ℝ)*l-j*k)^2,by positivity,
    l^2*s-(j:ℚ)*l*(s+t-u)+j^2*t,
    -2*(k:ℚ)*l*s+((i:ℚ)*l+j*k)*(s+t-u)-2*i*j*t,
    k^2*s-(i:ℚ)*k*(s+t-u)+i^2*t,?_,?_,?_⟩ <;>
    push_cast <;> rw [div_mul_eq_mul_div,eq_div_iff (pow_ne_zero _ hdet)]
  · linear_combination ((l:ℝ)^2-j*l)*h₁ + ((j:ℝ)^2-j*l)*h₂ + ((j:ℝ)*l)*h₃
  · linear_combination (-2*(k:ℝ)*l+i*l+j*k)*h₁ + (-2*(i:ℝ)*j+i*l+j*k)*h₂ -
      ((i:ℝ)*l+j*k)*h₃
  · linear_combination ((k:ℝ)^2-i*k)*h₁ + ((i:ℝ)^2-i*k)*h₂ + ((i:ℝ)*k)*h₃


/-- From a single pin, count at most four targets per positive distance. -/
private theorem irrational_count {X : Type*} [MetricSpace X] (T : Finset X)
    (f : X → ℤ × ℤ) (a b c : ℝ)
    (incomm : ¬ ∃ L : ℝ, 0 < L ∧ ∃ A B C : ℚ, a=L*A ∧ b=L*B ∧ c=L*C)
    (chart : ∀ x ∈ T, ∀ y ∈ T, dist x y^2 = a*(f x-f y).1^2 +
      b*(f x-f y).1*(f x-f y).2+c*(f x-f y).2^2) :
    T.card ≤ 4*distinctDistances T+1 := by
  classical
  rcases T.eq_empty_or_nonempty with rfl|⟨p,hp⟩
  · simp
  have inj : Set.InjOn f (T : Set X) := by
    intro x hx y hy e
    have he := chart x hx y hy
    rw [e,sub_self] at he
    simpa using he
  have hm : ∀ x ∈ T.erase p, dist x p ∈ distanceSet T :=
    fun x hx => mem_image.mpr ⟨(x,p),mem_offDiag.mpr ⟨mem_of_mem_erase hx,hp,ne_of_mem_erase hx⟩,rfl⟩
  have hc := card_le_mul_card_image_of_maps_to hm 4 (by
    intro r hr
    let U := (T.erase p).filter fun x => dist x p = r
    let g := fun x => f x-f p
    have pos : 0 < r := by
      obtain ⟨⟨x,y⟩,h,rfl⟩ := mem_image.mp hr
      exact dist_pos.mpr (mem_offDiag.mp h).2.2
    have hi : Set.InjOn g (U : Set X) := by
      intro x hx y hy h
      exact inj (mem_of_mem_erase (mem_filter.mp hx).1) (mem_of_mem_erase (mem_filter.mp hy).1)
        (sub_left_inj.mp h)
    change U.card ≤ 4
    rw [← card_image_of_injOn hi]
    apply oblique_shell _ a b c (r^2) (sq_pos_of_pos pos) incomm
    intro z hz
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
    obtain ⟨hxt,hr⟩ := mem_filter.mp hx
    exact (chart x (mem_of_mem_erase hxt) p hp).symm.trans (congrArg (fun d : ℝ => d^2) hr))
  change (T.erase p).card ≤ 4*distinctDistances T at hc
  rw [← card_erase_add_one hp]
  exact Nat.add_le_add_right hc 1

end Shells

-- uses note #142812
-- uses note #142818
-- uses note #142820

/-- Clear the denominators of finitely many rational multiples without changing the ratios. -/
private theorem common_table_unit (V : Finset ℝ) (L : ℝ)
    (rat : ∀ a ∈ V, ∃ r : ℚ, a = L*r) :
    ∃ m : ℕ, 0 < m ∧ ∀ a ∈ V, ∃ z : ℤ, (m:ℝ)*a = L*z := by
  classical
  induction V using Finset.induction_on with
  | empty => exact ⟨1,by decide,by simp⟩
  | @insert v V hv ih =>
    obtain ⟨m,hm,old⟩ := ih (fun a ha => rat a (mem_insert_of_mem ha))
    obtain ⟨r,hr⟩ := rat v (mem_insert_self ..)
    have hd : (r.den:ℝ)*(r:ℝ) = r.num := by
      exact_mod_cast (mul_comm (r.den:ℚ) r).trans (Rat.mul_den_eq_num r)
    refine ⟨m*r.den,Nat.mul_pos hm r.den_pos,fun a ha => ?_⟩
    rcases mem_insert.mp ha with rfl|ha
    · refine ⟨(m:ℤ)*r.num,?_⟩
      push_cast
      rw [hr,← hd]
      ring
    · obtain ⟨z,hz⟩ := old a ha
      refine ⟨(r.den:ℤ)*z,?_⟩
      push_cast
      linear_combination (r.den:ℝ)*hz


/-- The dual Gram form recovers squared length from the two dot products. -/
private theorem gram_recovery (e f g h u v : ℝ) :
    (g^2+h^2)*(2*(e*u+f*v))^2 + (-2)*(e*g+f*h)*(2*(e*u+f*v))*(2*(g*u+h*v)) +
      (e^2+f^2)*(2*(g*u+h*v))^2 = 4*(e*h-f*g)^2*(u^2+v^2) := by ring

private theorem pin_delta (x y p q : ℝ²) :
    (dist x p^2-dist x q^2)-(dist y p^2-dist y q^2) =
      2*((q 0-p 0)*(x 0-y 0)+(q 1-p 1)*(x 1-y 1)) := by
  simp only [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq, sq_abs]
  ring

/-- With three commensurable squared-distance tables, their differences give
integer coordinates. The table on the pin triangle gives the integral form. -/
private theorem three_pin_chart {X : Type*} [PseudoMetricSpace X] (v : X → ℝ²)
    (iso : ∀ x y, dist (v x) (v y) = dist x y) (T : Finset X) (p q r : X)
    (hq : q ∈ T) (hr : r ∈ T)
    (hn : (v q 0-v p 0)*(v r 1-v p 1) ≠ (v q 1-v p 1)*(v r 0-v p 0))
    (L : ℝ) (hL : 0 < L)
    (tab : ∀ x ∈ T, ∀ o : X, o = p ∨ o = q ∨ o = r → ∃ n : ℤ, dist x o^2 = L*n) :
    ∃ a b c : ℤ, 0 < a ∧ b^2 < 4*a*c ∧ ∃ F : X → ℤ × ℤ, ∃ K : ℝ, 0 < K ∧
      ∀ x ∈ T, ∀ y ∈ T,
        (((a*(F x-F y).1^2+b*(F x-F y).1*(F x-F y).2+c*(F x-F y).2^2 : ℤ) : ℝ)) =
          K*dist x y^2 := by
  let I := fun x o : X => ⌊dist x o^2/L⌋
  have val (x) (hx : x ∈ T) (o) (ho : o = p ∨ o = q ∨ o = r) :
      dist x o^2 = L*(I x o : ℝ) := by
    obtain ⟨n,hn⟩ := tab x hx o ho
    simp [I,hn,hL.ne']
  let a := I r p
  let c := I q p
  let b := I r q - a - c
  let e := v q 0-v p 0
  let f := v q 1-v p 1
  let g := v r 0-v p 0
  let h := v r 1-v p 1
  have ha : L*(a:ℝ) = g^2+h^2 := by
    rw [← val r hr p (Or.inl rfl), ← iso]
    simp [g,h,EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq]
  have hc : L*(c:ℝ) = e^2+f^2 := by
    rw [← val q hq p (Or.inl rfl), ← iso]
    simp [e,f,EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq]
  have hb : L*(b:ℝ) = -2*(e*g+f*h) := by
    dsimp [b]
    push_cast
    rw [mul_sub,mul_sub,ha,hc,← val r hr q (Or.inr (Or.inl rfl)),← iso]
    simp only [e,f,g,h,EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq, sq_abs]
    ring
  have hdet : 0 < (e*h-f*g)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hn)
  have discr : L^2*(4*(a:ℝ)*c-(b:ℝ)^2) = 4*(e*h-f*g)^2 := calc
    _ = 4*(L*(a:ℝ))*(L*(c:ℝ))-(L*(b:ℝ))^2 := by ring
    _ = _ := by rw [ha,hb,hc]; ring
  have hd : (b:ℝ)^2 < 4*(a:ℝ)*c := by
    have pos : 0 < L^2*(4*(a:ℝ)*c-(b:ℝ)^2) := by rw [discr]; positivity
    exact sub_pos.mp (pos_of_mul_pos_right pos (sq_nonneg _))
  have ha0 : (0:ℝ) < a := by
    have hn0 : 0 ≤ L*(a:ℝ) := by rw [ha]; positivity
    have hnon := nonneg_of_mul_nonneg_right hn0 hL
    exact lt_of_le_of_ne hnon (by intro he; rw [← he] at hd; nlinarith [sq_nonneg (b:ℝ)])
  let F := fun x : X => (I x p-I x q,I x p-I x r)
  refine ⟨a,b,c,by exact_mod_cast ha0,by exact_mod_cast hd,F,4*(e*h-f*g)^2/L^3,by positivity,?_⟩
  intro x hx y hy
  have delta (o) (ho : o = p ∨ o = q ∨ o = r) :
      L*(((I x p-I x o)-(I y p-I y o) : ℤ):ℝ) =
        2*((v o 0-v p 0)*(v x 0-v y 0)+(v o 1-v p 1)*(v x 1-v y 1)) := by
    push_cast
    simp only [mul_sub, ← val x hx p (Or.inl rfl), ← val x hx o ho,
      ← val y hy p (Or.inl rfl), ← val y hy o ho, ← iso]
    simpa only [mul_sub] using pin_delta (v x) (v y) (v p) (v o)
  let s : ℝ := ((F x-F y).1:ℤ)
  let t : ℝ := ((F x-F y).2:ℤ)
  have hs : L*s = _ := delta q (Or.inr (Or.inl rfl))
  have ht : L*t = _ := delta r (Or.inr (Or.inr rfl))
  push_cast
  change (a:ℝ)*s^2+b*s*t+c*t^2 = _
  rw [div_mul_eq_mul_div,eq_div_iff (pow_ne_zero _ hL.ne')]
  calc
    _ = (L*(a:ℝ))*(L*s)^2+(L*(b:ℝ))*(L*s)*(L*t)+(L*(c:ℝ))*(L*t)^2 := by ring
    _ = _ := by
      rw [ha,hb,hc,hs,ht,← iso,EuclideanSpace.dist_sq_eq,Fin.sum_univ_two]
      simp only [Real.dist_eq,sq_abs]
      exact gram_recovery e f g h (v x 0-v y 0) (v x 1-v y 1)

/-- The two integral coordinates preserve distinctness and the form-value budget. -/
private theorem three_pin_model :
  let X := {p : ℝ² // ∀ i : Fin 2, IsIntegral ℤ (p i)}
  ∀ (P T : Finset X), T ⊆ P →
    (∃ p ∈ T, ∃ q ∈ T, ∃ r ∈ T,
        (q.val 0-p.val 0)*(r.val 1-p.val 1) ≠ (q.val 1-p.val 1)*(r.val 0-p.val 0) ∧
        ∃ L : ℝ, 0 < L ∧ ∀ x ∈ T, ∀ o : X, o = p ∨ o = q ∨ o = r →
          ∃ n : ℚ, dist x o^2 = L*n) →
      ∃ a b c : ℤ, 0 < a ∧ b^2 < 4*a*c ∧ ∃ S : Finset (ℤ × ℤ),
        S.card = T.card ∧
        let q := fun z : ℤ × ℤ => a*z.1^2 + b*z.1*z.2 + c*z.2^2
        (S.offDiag.image fun xy => q (xy.1 - xy.2)).card ≤ distinctDistances P := by
  classical
  let X := {x : ℝ² // ∀ i : Fin 2, IsIntegral ℤ (x i)}
  intro _ P T hsub htri
  obtain ⟨p,_,q,hq,r,hr,hn,L,hL,rep⟩ := htri
  let E := T ×ˢ ({p,q,r} : Finset X)
  let V := E.image fun e => dist e.1 e.2^2
  have rat : ∀ s ∈ V, ∃ n : ℚ, s = L*n := by
    intro s hs
    obtain ⟨⟨x,o⟩,h,rfl⟩ := mem_image.mp hs
    obtain ⟨hx,ho⟩ := mem_product.mp h
    exact rep x hx o (by simpa using ho)
  obtain ⟨m,hm,hint⟩ := common_table_unit V L rat
  have hm' : 0 < (m:ℝ) := by exact_mod_cast hm
  have htable (x) (hx : x ∈ T) (o) (ho : o = p ∨ o = q ∨ o = r) :
      ∃ n : ℤ, dist x o^2 = (L/m)*n := by
    have hmem : (x,o) ∈ E := mem_product.mpr ⟨hx,by simpa using ho⟩
    obtain ⟨n,hn⟩ := hint _ (mem_image.mpr ⟨(x,o),hmem,rfl⟩)
    refine ⟨n,?_⟩
    rw [div_mul_eq_mul_div,eq_div_iff hm'.ne',mul_comm]
    exact hn
  obtain ⟨a,b,c,ha,hd,F,K,hK,he⟩ :=
    three_pin_chart (fun x : X => x.val) (fun _ _ => rfl) T p q r hq hr hn (L/m) (div_pos hL hm') htable
  have hinj : Set.InjOn F (T : Set X) := by
    intro x hx y hy hxy
    have h := he x hx y hy
    rw [hxy,sub_self] at h
    simp at h
    rcases h with h|h
    · exact (hK.ne' h).elim
    · exact dist_eq_zero.mp h
  refine ⟨a,b,c,ha,hd,T.image F,card_image_of_injOn hinj,?_⟩
  apply card_le_card_of_surjOn (fun z : ℝ => ⌊K*z^2⌋)
  intro n hn
  obtain ⟨⟨s,t⟩,hst,rfl⟩ := mem_image.mp hn
  obtain ⟨hs,ht,hne⟩ := mem_offDiag.mp hst
  obtain ⟨x,hx,rfl⟩ := mem_image.mp hs
  obtain ⟨y,hy,rfl⟩ := mem_image.mp ht
  refine ⟨dist x y,mem_image.mpr ⟨(x,y),mem_offDiag.mpr
    ⟨hsub hx,hsub hy,fun h => hne (congrArg F h)⟩,rfl⟩,?_⟩
  change ⌊K*dist x y^2⌋ = _
  rw [← he x hx y hy,Int.floor_intCast]


/-- Three points with vanishing coordinate determinant lie on one affine line. -/
private theorem collinear_of_det (x y z : ℝ²) (hxy : x ≠ y)
    (h : (y 0-x 0)*(z 1-x 1) = (y 1-x 1)*(z 0-x 0)) :
    Collinear ℝ ({x,y,z} : Set ℝ²) := by
  apply (collinear_iff_of_mem (by simp : x ∈ ({x,y,z} : Set ℝ²))).2
  refine ⟨y-x,?_⟩
  intro t ht
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
  rcases ht with hmem|hmem|hmem <;> subst t
  · exact ⟨0,by simp⟩
  · exact ⟨1,by simp⟩
  by_cases hx : y 0-x 0 = 0
  · have hy : y 1-x 1 ≠ 0 := by
      intro he
      apply hxy
      ext i
      fin_cases i <;> simp_all <;> linarith
    refine ⟨(z 1-x 1)/(y 1-x 1),?_⟩
    ext i
    change z i = (z 1-x 1)/(y 1-x 1)*(y i-x i)+x i
    rcases (show i = 0 ∨ i = 1 by omega) with hi|hi <;> rw [hi]
    · rw [hx,mul_zero,zero_add]
      rw [hx,zero_mul] at h
      exact sub_eq_zero.mp ((mul_eq_zero.mp h.symm).resolve_left hy)
    · field_simp
      ring
  · refine ⟨(z 0-x 0)/(y 0-x 0),?_⟩
    ext i
    change z i = (z 0-x 0)/(y 0-x 0)*(y i-x i)+x i
    rcases (show i = 0 ∨ i = 1 by omega) with hi|hi <;> rw [hi] <;> field_simp
    · ring
    · linear_combination h

/-- Without a noncollinear triangle, each pinned distance has at most two targets. -/
private theorem flat_count (T : Finset {p : ℝ² // ∀ i : Fin 2, IsIntegral ℤ (p i)})
    (flat : ∀ x ∈ T, ∀ y ∈ T, ∀ z ∈ T,
      (y.val 0-x.val 0)*(z.val 1-x.val 1) = (y.val 1-x.val 1)*(z.val 0-x.val 0)) :
    T.card ≤ 2*distinctDistances T+1 := by
  classical
  rcases T.eq_empty_or_nonempty with rfl|⟨p,hp⟩
  · simp
  have hm : ∀ x ∈ T.erase p, dist x p ∈ distanceSet T :=
    fun x hx => mem_image.mpr ⟨(x,p),mem_offDiag.mpr ⟨mem_of_mem_erase hx,hp,ne_of_mem_erase hx⟩,rfl⟩
  have hc := card_le_mul_card_image_of_maps_to hm 2 (by
    intro r _
    by_contra! h
    obtain ⟨x,hx,y,hy,z,hz,hxy,hxz,hyz⟩ := two_lt_card.mp h
    obtain ⟨hx,ex⟩ := mem_filter.mp hx
    obtain ⟨hy,ey⟩ := mem_filter.mp hy
    obtain ⟨hz,ez⟩ := mem_filter.mp hz
    let E : Set ℝ² := {v | dist v p.val = r}
    have sphere : Cospherical E := ⟨p.val,r,fun _ hv => hv⟩
    have ind := sphere.affineIndependent_of_mem_of_ne (show x.val ∈ E from ex)
      (show y.val ∈ E from ey) (show z.val ∈ E from ez)
      (Subtype.val_injective.ne hxy) (Subtype.val_injective.ne hxz) (Subtype.val_injective.ne hyz)
    apply (affineIndependent_iff_not_collinear_set.mp ind)
    exact collinear_of_det _ _ _ (Subtype.val_injective.ne hxy)
      (flat x (mem_of_mem_erase hx) y (mem_of_mem_erase hy) z (mem_of_mem_erase hz)))
  change (T.erase p).card ≤ 2*distinctDistances T at hc
  rw [← card_erase_add_one hp]
  exact Nat.add_le_add_right hc 1


/-- A single integral linear embedding works for every finite subset. It preserves
the entire set of form values on distinct pairs up to one common scaling. -/
private theorem squarefree_model (a b c : ℤ) (ha : 0 < a) (hdisc : b^2 < 4*a*c) :
    let values := fun (q : ℤ × ℤ → ℤ) (T : Finset (ℤ × ℤ)) => T.offDiag.image fun xy => q (xy.1-xy.2)
    ∃ d : ℕ, 0 < d ∧ Squarefree d ∧ ∃ F : ℤ × ℤ → ℤ × ℤ, Function.Injective F ∧
      ∀ S : Finset (ℤ × ℤ), (S.image F).card = S.card ∧
        values (fun z => z.1^2 + (d : ℤ)*z.2^2) (S.image F) =
          (values (fun z => a*z.1^2 + b*z.1*z.2 + c*z.2^2) S).image (4*a * ·) := by
  intro values
  have hp : 0 < 4*a*c - b^2 := by omega
  obtain ⟨d,r,hd,hr,he,hsq⟩ := Nat.sq_mul_squarefree_of_pos (show 0 < (4*a*c-b^2).toNat by omega)
  have he' : (r : ℤ)^2 * d = 4*a*c - b^2 := by
    simpa only [Nat.cast_mul, Nat.cast_pow, Int.toNat_of_nonneg hp.le] using
      congrArg (fun n : ℕ => (n : ℤ)) he
  let F (p : ℤ × ℤ) : ℤ × ℤ := (2*a*p.1+b*p.2, (r:ℤ)*p.2)
  have hinj : Function.Injective F := by
    rintro ⟨x,y⟩ ⟨u,v⟩ h
    have hxy := congrArg Prod.fst h
    have hyv := congrArg Prod.snd h
    change (r:ℤ)*y = (r:ℤ)*v at hyv
    have : y = v := mul_left_cancel₀ (by exact_mod_cast hr.ne') hyv
    subst v
    change 2*a*x+b*y = 2*a*u+b*y at hxy
    exact Prod.ext (mul_left_cancel₀ (by positivity : 2*a ≠ 0) (add_right_cancel hxy)) rfl
  refine ⟨d, hd, hsq, F, hinj, fun S => ⟨Finset.card_image_of_injective _ hinj, ?_⟩⟩
  let Q := fun z : ℤ × ℤ => a*z.1^2 + b*z.1*z.2 + c*z.2^2
  let D := fun z : ℤ × ℤ => z.1^2 + (d:ℤ)*z.2^2
  have hval (p t : ℤ × ℤ) : D (F p - F t) = 4*a*Q (p-t) := by
    dsimp [D, F, Q]
    linear_combination (p.2-t.2)^2 * he'
  have mem_values (q : ℤ × ℤ → ℤ) (T : Finset (ℤ × ℤ)) (w : ℤ) :
      w ∈ values q T ↔ ∃ p ∈ T, ∃ t ∈ T, p ≠ t ∧ q (p-t) = w := by
    constructor
    · intro h
      obtain ⟨⟨p,t⟩, hpt, hval⟩ := Finset.mem_image.mp h
      obtain ⟨hp, ht, hne⟩ := Finset.mem_offDiag.mp hpt
      exact ⟨p,hp,t,ht,hne,hval⟩
    · rintro ⟨p,hp,t,ht,hne,hval⟩
      exact Finset.mem_image.mpr ⟨(p,t), Finset.mem_offDiag.mpr ⟨hp,ht,hne⟩, hval⟩
  ext w
  change w ∈ values D (S.image F) ↔ w ∈ (values Q S).image _
  rw [mem_values, Finset.mem_image]
  constructor
  · rintro ⟨u, hu, v, hv, hne, rfl⟩
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hv
    exact ⟨_, (mem_values ..).mpr ⟨p,hp,t,ht,fun e => hne (congrArg F e),rfl⟩,
      (hval p t).symm⟩
  · rintro ⟨w,hw,rfl⟩
    obtain ⟨p,hp,t,ht,hne,rfl⟩ := (mem_values ..).mp hw
    exact ⟨_,Finset.mem_image_of_mem F hp,_,Finset.mem_image_of_mem F ht,hinj.ne hne,hval p t⟩

/-- Exact divisibility test for the fixed divisor of a shifted quadratic progression. -/
theorem progression_modulus (M d t s : ℤ) :
    (∀ j : ℤ, M ∣ d*((t+s*j)^2-t^2)) ↔
      M ∣ d*s*(2*t+s) ∧ M ∣ 2*d*s^2 := by
  constructor
  · intro h
    refine ⟨?_,?_⟩
    · convert h 1 using 1
      ring
    · have e : 2*d*s^2 = d*((t+s*1)^2-t^2) + d*((t+s*(-1))^2-t^2) := by ring
      rw [e]
      exact dvd_add (h 1) (h (-1))
  · rintro ⟨⟨a,ha⟩,⟨b,hb⟩⟩ j
    obtain ⟨u,hu⟩ := (Int.even_mul_pred_self j).two_dvd
    refine ⟨a*j+b*u,?_⟩
    linear_combination j*ha + u*hb + d*s^2*hu

/-- Distinct pin-column pairs can occupy different vertical arithmetic
progressions, provided each progression fixes a residue of the form. -/
theorem shifted_pin_bound (d : ℕ) (hd : 0 < d) (S T : Finset (ℤ × ℤ))
    (p : ℤ × ℤ → ℤ × ℤ) (M : ℤ) (t s : (ℤ × ℤ) × ℤ → ℤ) (hsub : T ⊆ S) (k : ℕ)
    (pins : ∀ x ∈ T, let e := (p x,x.1)
      p x ∈ S ∧ s e ∣ x.2-(p x).2-t e ∧
      M ∣ (d:ℤ)*s e*(2*t e+s e) ∧ M ∣ 2*(d:ℤ)*(s e)^2)
    (hcap : ∀ r : ℤ, ((T.image fun x => (p x,x.1)).filter fun e =>
      ((e.2-e.1.1)^2+(d:ℤ)*(t e)^2) % M = r).card ≤ k) :
    let q := fun v : ℤ × ℤ => v.1^2+(d:ℤ)*v.2^2
    T.card ≤ 2*k*((S.offDiag.image fun xy => q (xy.1-xy.2)).card+1) := by
  classical
  intro q
  let V := S.offDiag.image fun xy => q (xy.1-xy.2)
  let f := fun x : ℤ × ℤ => q (x-p x)
  let label := fun x : ℤ × ℤ => (p x,x.1)
  have hm : ∀ x ∈ T, f x ∈ insert 0 V := by
    intro x hx
    by_cases he : x=p x
    · have hz : x-p x=0 := sub_eq_zero.mpr he
      change q (x-p x) ∈ insert 0 V
      rw [hz]
      simp [q]
    · exact mem_insert_of_mem (mem_image.mpr ⟨(x,p x),mem_offDiag.mpr ⟨hsub hx,(pins x hx).1,he⟩,rfl⟩)
  have h := card_le_mul_card_image_of_maps_to hm (2*k) (by
    intro r _
    let U := T.filter fun x => f x=r
    let C := (T.image label).filter fun e => ((e.2-e.1.1)^2+(d:ℤ)*(t e)^2) % M = r % M
    let g := fun x : ℤ × ℤ => (label x,decide ((p x).2 ≤ x.2))
    have eqv (x) (hx : x ∈ U) : (x.1-(p x).1)^2+(d:ℤ)*(x.2-(p x).2)^2 = r := (mem_filter.mp hx).2
    have sub : U.image g ⊆ C ×ˢ (univ : Finset Bool) := by
      intro z hz
      obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
      refine mem_product.mpr ⟨mem_filter.mpr ⟨mem_image_of_mem _ (mem_filter.mp hx).1,?_⟩,mem_univ _⟩
      let e := label x
      change ((x.1-(p x).1)^2+(d:ℤ)*(t e)^2) % M = r % M
      obtain ⟨_,⟨j,hj⟩,h₁,h₂⟩ := pins x (mem_filter.mp hx).1
      have hv : x.2-(p x).2 = t e+s e*j := by change x.2-(p x).2-t e=s e*j at hj; omega
      obtain ⟨u,hu⟩ := (progression_modulus M d (t e) (s e)).2 ⟨h₁,h₂⟩ j
      have val : r = ((x.1-(p x).1)^2+(d:ℤ)*(t e)^2)+M*u := by
        rw [← eqv x hx,hv]
        linear_combination hu
      rw [val]
      simp
    have inj : Set.InjOn g (U : Set (ℤ × ℤ)) := by
      intro x hx y hy he
      have hl : label x=label y := congrArg Prod.fst he
      have ep : p x=p y := congrArg Prod.fst hl
      have ex : x.1=y.1 := congrArg Prod.snd hl
      have e := (eqv x hx).trans (eqv y hy).symm
      rw [ep,ex] at e
      have ey := sq_eq_sq_iff_eq_or_eq_neg.mp
        (mul_left_cancel₀ (by exact_mod_cast hd.ne' : (d:ℤ) ≠ 0) (add_left_cancel e))
      have sign := congrArg Prod.snd he
      simp [g,ep] at sign
      exact Prod.ext ex (by omega)
    have hc := card_le_card sub
    rw [card_image_of_injOn inj,card_product] at hc
    change U.card ≤ 2*k
    exact hc.trans (by simpa [mul_comm] using Nat.mul_le_mul_right 2 (hcap (r % M))))
  exact h.trans (Nat.mul_le_mul_left _ (card_insert_le ..))

/-- Targets may choose different pins. Vertical divisibility fixes the horizontal
square modulo d*m²; all pins draw values from the same set of pair values. -/
theorem assigned_pin_bound (d : ℕ) (hd : 0 < d) (S T : Finset (ℤ × ℤ))
    (p : ℤ × ℤ → ℤ × ℤ) (m : ℤ) (hsub : T ⊆ S) (k : ℕ)
    (pins : ∀ x ∈ T, p x ∈ S ∧ m ∣ x.2-(p x).2)
    (hcap : ∀ r : ℤ, ((T.image fun x => (p x,x.1)).filter fun e =>
      (e.2-e.1.1)^2 % ((d:ℤ)*m^2) = r).card ≤ k) :
    let q := fun v : ℤ × ℤ => v.1^2+(d:ℤ)*v.2^2
    T.card ≤ 2*k*((S.offDiag.image fun xy => q (xy.1-xy.2)).card+1) := by
  classical
  apply shifted_pin_bound d hd S T p ((d:ℤ)*m^2) (fun _ => 0) (fun _ => m) hsub k
  · intro x hx
    obtain ⟨hp,hm⟩ := pins x hx
    exact ⟨hp,by simpa using hm,⟨1,by ring⟩,⟨2,by ring⟩⟩
  · simpa using hcap

/-- Each pinned value fixes the horizontal square residue. Within each column its
targets are determined by the sign of their vertical displacement. -/
theorem residue_pin_bound (d : ℕ) (hd : 0 < d) (S T : Finset (ℤ × ℤ))
    (p : ℤ × ℤ) (hp : p ∈ S) (hsub : T ⊆ S) (k : ℕ)
    (hcap : ∀ r : ℤ, ((T.image Prod.fst).filter fun x => (x-p.1)^2 % (d:ℤ) = r).card ≤ k) :
    let q := fun v : ℤ × ℤ => v.1^2+(d:ℤ)*v.2^2
    T.card ≤ 2*k*((S.offDiag.image fun xy => q (xy.1-xy.2)).card+1) := by
  classical
  apply assigned_pin_bound d hd S T (fun _ => p) 1 hsub k (fun _ _ => ⟨hp,one_dvd _⟩)
  intro r
  let C := (T.image Prod.fst).filter fun x => (x-p.1)^2 % (d:ℤ) = r
  have sub : ((T.image fun x => (p,x.1)).filter fun e =>
      (e.2-e.1.1)^2 % ((d:ℤ)*1^2) = r) ⊆ C.image (fun x => (p,x)) := by
    intro z hz
    obtain ⟨hz,hr⟩ := mem_filter.mp hz
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
    exact mem_image.mpr ⟨x.1,mem_filter.mpr ⟨mem_image_of_mem _ hx,by simpa using hr⟩,rfl⟩
  exact (card_le_card sub).trans (card_image_le.trans (hcap r))

-- uses note #91253
-- uses note #91254
-- uses note #91256
private lemma factor_of_collision (a b x y : ℕ) (hab : a < b) (he : x^2+a = y^2+b) :
    y < x ∧ b-a = (x-y)*(x+y) := by
  have hyx : y < x := by
    by_contra! h
    have := Nat.pow_le_pow_left h 2
    omega
  refine ⟨hyx,?_⟩
  have ht := Nat.sub_add_cancel hyx.le
  have hs := Nat.sub_add_cancel hab.le
  nlinarith only [he,hs,congrArg (fun z : ℕ => z*(x+y)) ht]

/-- Exact divisor parametrization of the overlap of two shifted square sets
with complete horizontal gaps from zero through W. -/
private theorem overlap_exact (a b U V : ℕ) (hab : a < b) :
    let row := fun (a : ℕ) (X : Finset ℕ) => X.image fun x => x^2+a
    let factors := fun (h U V : ℕ) => h.divisors.filter fun j =>
      j ≤ h/j ∧ h/j+j ≤ 2*U ∧ h/j-j ≤ 2*V ∧ j%2 = (h/j)%2
    ((row a (range (U+1))) ∩ (row b (range (V+1)))).card = (factors (b-a) U V).card := by
  intro row factors
  let H := b-a
  have hH : 0 < H := Nat.sub_pos_of_lt hab
  let u (s : ℕ) := (H/s+s)/2
  let v (s : ℕ) := (H/s-s)/2
  have decode (s) (hs : s ∈ factors H U V) :
      u s ≤ U ∧ v s ≤ V ∧ u s-v s = s ∧ u s+v s = H/s ∧ (u s)^2+a = (v s)^2+b := by
    obtain ⟨hd,hle,hwidth,hheight,hpar⟩ := mem_filter.mp hs
    have hmul := Nat.div_mul_cancel (Nat.mem_divisors.mp hd).1
    have hsub := Nat.sub_add_cancel hab.le
    have hdiff : u s = v s+s := by dsimp [u,v]; omega
    have hsum : u s+v s = H/s := by dsimp [u,v]; omega
    refine ⟨by dsimp [u]; omega,by dsimp [v]; omega,by omega,hsum,?_⟩
    rw [← hsum] at hmul
    change H+a=b at hsub
    nlinarith only [hmul,hsub,congrArg (fun z : ℕ => z*(u s+v s)) hdiff]
  let f (s : ℕ) := (u s)^2+a
  have himage : (factors H U V).image f = row a (range (U+1)) ∩ row b (range (V+1)) := by
    ext z
    constructor
    · intro hz
      obtain ⟨s,hs,rfl⟩ := mem_image.mp hz
      obtain ⟨hu,hv,_,_,he⟩ := decode s hs
      exact mem_inter.mpr ⟨mem_image.mpr ⟨_,mem_range.mpr (Nat.lt_succ_of_le hu),rfl⟩,
        mem_image.mpr ⟨_,mem_range.mpr (Nat.lt_succ_of_le hv),he.symm⟩⟩
    · intro hz
      obtain ⟨ha,hb⟩ := mem_inter.mp hz
      obtain ⟨x,hx,rfl⟩ := mem_image.mp ha
      obtain ⟨y,hy,he⟩ := mem_image.mp hb
      obtain ⟨hlt,hm⟩ := factor_of_collision a b x y hab he.symm
      have hd : H/(x-y) = x+y := by
        change (b-a)/(x-y)=_
        rw [hm,Nat.mul_div_cancel_left _ (Nat.sub_pos_of_lt hlt)]
      have hxW := mem_range.mp hx
      have hyW := mem_range.mp hy
      refine mem_image.mpr ⟨x-y,mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨⟨x+y,hm⟩,hH.ne'⟩,?_⟩,?_⟩
      · rw [hd]; omega
      · change ((H/(x-y)+(x-y))/2)^2+a=x^2+a
        rw [hd,show (x+y+(x-y))/2=x by omega]
  rw [← himage]
  apply card_image_of_injOn
  intro s hs t ht he
  obtain ⟨_,_,hds,_,hes⟩ := decode s hs
  obtain ⟨_,_,hdt,_,het⟩ := decode t ht
  change (u s)^2+a = (u t)^2+a at he
  have hu := Nat.pow_left_injective (by decide : 2 ≠ 0) (Nat.add_right_cancel he)
  have hv := Nat.pow_left_injective (by decide : 2 ≠ 0)
    (Nat.add_right_cancel (hes.symm.trans (he.trans het)))
  omega

/-- Deleting horizontal gaps can only decrease the overlap. -/
private theorem overlap_le (a b U V : ℕ) (hab : a < b) (X Y : Finset ℕ)
    (hx : X ⊆ range (U+1)) (hy : Y ⊆ range (V+1)) :
    let row := fun (a : ℕ) (X : Finset ℕ) => X.image fun x => x^2+a
    let factors := fun (h U V : ℕ) => h.divisors.filter fun j =>
      j ≤ h/j ∧ h/j+j ≤ 2*U ∧ h/j-j ≤ 2*V ∧ j%2 = (h/j)%2
    ((row a X) ∩ (row b Y)).card ≤ (factors (b-a) U V).card := by
  intro row factors
  rw [← overlap_exact a b U V hab]
  exact card_le_card (inter_subset_inter (image_mono _ hx) (image_mono _ hy))

private theorem count_row (a : ℕ) (X : Finset ℕ) :
    let row := fun (a : ℕ) (X : Finset ℕ) => X.image fun x => x^2+a
    (row a X).card = X.card := by
  intro row
  exact card_image_of_injective _ (fun _ _ he => Nat.pow_left_injective (by decide : 2 ≠ 0)
    (Nat.add_right_cancel he))

/-- Cauchy-Schwarz counts incidences of distinct values with rows.
The off-diagonal charges retain the parity and width of admissible factors. -/
private theorem union_bound (A : Finset ℕ) (X : ℕ → Finset ℕ) (W : ℕ → ℕ)
    (hW : ∀ a ∈ A, X a ⊆ range (W a+1)) :
    let row := fun (a : ℕ) (X : Finset ℕ) => X.image fun x => x^2+a
    let factors := fun (h U V : ℕ) => h.divisors.filter fun j =>
      j ≤ h/j ∧ h/j+j ≤ 2*U ∧ h/j-j ≤ 2*V ∧ j%2 = (h/j)%2
    (∑ a ∈ A, (X a).card)^2 ≤ (A.biUnion fun a => row a (X a)).card *
      ∑ a ∈ A, ∑ b ∈ A, if a=b then (X a).card else
        min (min (X a).card (X b).card) (factors (max a b-min a b) (W (min a b)) (W (max a b))).card := by
  intro row factors
  classical
  have hcount (a) : (row a (X a)).card = (X a).card := count_row a (X a)
  let F (a) := row a (X a)
  let U := A.biUnion F
  let ind (a z : ℕ) : ℕ := if z ∈ F a then 1 else 0
  have sub (a) (ha : a ∈ A) : F a ⊆ U := subset_biUnion_of_mem _ ha
  have mass : (∑ a ∈ A, (X a).card) = ∑ z ∈ U, ∑ a ∈ A, ind a z := by
    rw [sum_comm]
    apply sum_congr rfl
    intro a ha
    have he : U.filter (fun z => z ∈ F a) = F a := by ext z; simp only [mem_filter]; exact
      ⟨fun h => h.2,fun h => ⟨sub a ha h,h⟩⟩
    simp only [ind,sum_boole,Nat.cast_id,he,F,hcount]
  have pair (a b) (ha : a ∈ A) : (∑ z ∈ U, ind a z * ind b z) = ((F a) ∩ (F b)).card := by
    have hi (z) : ind a z * ind b z = if z ∈ F a ∩ F b then 1 else 0 := by
      by_cases h : z ∈ F a <;> simp [ind,h]
    have he : U.filter (fun z => z ∈ F a ∩ F b) = F a ∩ F b := by
      ext z
      simp only [mem_filter]
      exact ⟨fun h => h.2,fun h => ⟨sub a ha (mem_inter.mp h).1,h⟩⟩
    simp only [hi,sum_boole,Nat.cast_id,he]
  have energy : (∑ z ∈ U, (∑ a ∈ A, ind a z)^2) =
      ∑ a ∈ A, ∑ b ∈ A, ((F a) ∩ (F b)).card := by
    simp only [pow_two,sum_mul,mul_sum]
    rw [sum_comm (s := U) (t := A)]
    apply sum_congr rfl
    intro a ha
    rw [sum_comm]
    exact sum_congr rfl fun b _ => by simpa only [Nat.mul_comm] using pair a b ha
  rw [mass]
  apply sq_sum_le_card_mul_sum_sq.trans
  apply Nat.mul_le_mul_left
  rw [energy]
  apply sum_le_sum
  intro a ha
  apply sum_le_sum
  intro b hb
  split_ifs with he
  · subst b; simp [F,hcount]
  · apply le_min
    · apply le_min
      · simpa [F,hcount] using card_le_card (inter_subset_left (s₁ := F a) (s₂ := F b))
      · simpa [F,hcount] using card_le_card (inter_subset_right (s₁ := F a) (s₂ := F b))
    · rcases lt_or_gt_of_ne he with h|h
      · simpa only [F,max_eq_right h.le,min_eq_left h.le] using
          overlap_le a b (W a) (W b) h (X a) (X b) (hW a ha) (hW b hb)
      · simpa only [F,max_eq_left h.le,min_eq_right h.le,inter_comm] using
          overlap_le b a (W b) (W a) h (X b) (X a) (hW b hb) (hW a ha)

/-- The integer gaps can come from any pairs in S, including from a common pin.
The square of their total count is controlled by the distinct values times
a divisor sum that only uses row offsets, widths and row sizes. -/
theorem divisor_gap_bound (d : ℕ) (S : Finset (ℤ × ℤ))
    (A : Finset ℕ) (X : ℕ → Finset ℕ) (W : ℕ → ℕ)
    (width : ∀ a ∈ A, X a ⊆ range (W a+1))
    (realized : ∀ a ∈ A, ∀ u ∈ X a, ∃ x ∈ S, ∃ y ∈ S,
      u = (x.1-y.1).natAbs ∧ a = d*(x.2-y.2).natAbs^2) :
    let q := fun v : ℤ × ℤ => v.1^2+(d:ℤ)*v.2^2
    let mass := ∑ a ∈ A, (X a).card
    let cost := ∑ a ∈ A, ∑ b ∈ A, if a=b then (X a).card else
        let h := max a b-min a b
        min (min (X a).card (X b).card) (h.divisors.filter fun j =>
          j ≤ h/j ∧ h/j+j ≤ 2*W (min a b) ∧ h/j-j ≤ 2*W (max a b) ∧ j%2 = (h/j)%2).card
    mass^2 ≤ ((S.offDiag.image fun xy => q (xy.1-xy.2)).card+1)*cost := by
  classical
  intro q mass cost
  let U := A.biUnion fun a => (X a).image fun x => x^2+a
  let V := S.offDiag.image fun xy => q (xy.1-xy.2)
  have sub : U.image (Nat.cast : ℕ → ℤ) ⊆ insert 0 V := by
    intro v hv
    obtain ⟨n,hn,rfl⟩ := mem_image.mp hv
    obtain ⟨a,ha,hn⟩ := mem_biUnion.mp hn
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hn
    obtain ⟨x,hx,y,hy,rfl,rfl⟩ := realized a ha u hu
    by_cases he : x=y
    · simp [he]
    · apply mem_insert_of_mem
      refine mem_image.mpr ⟨(x,y),mem_offDiag.mpr ⟨hx,hy,he⟩,?_⟩
      simp [q]
  have card := card_le_card sub
  rw [card_image_of_injective _ Nat.cast_injective] at card
  exact (union_bound A X W width).trans
    (Nat.mul_le_mul_right cost (card.trans (card_insert_le ..)))

/-- Raising the divisor count to a fixed power costs at most a constant times n. -/
private theorem divisor_power_bound (k : ℕ) (hk : 0 < k) :
    ∃ C : ℕ, ∀ n : ℕ, 0 < n → n.divisors.card^k ≤ C*n := by
  classical
  let B := k^k
  refine ⟨B^(2^k),?_⟩
  intro n hn
  let P := n.primeFactors
  let f (p : ℕ) := if p < 2^k then B else 1
  have step (p : ℕ) (hp : p ∈ P) :
      (n.factorization p+1)^k ≤ f p*p^(n.factorization p) := by
    let a := n.factorization p
    change (a+1)^k ≤ f p*p^a
    by_cases small : p < 2^k
    · simp only [f,if_pos small]
      have hm := Nat.mod_lt a hk
      have he := Nat.mod_add_div a k
      have ha : a+1 ≤ k*(a/k+1) := by rw [Nat.mul_add_one]; omega
      have powle := Nat.pow_le_pow_left (show a/k+1 ≤ 2^(a/k) from (a/k).lt_two_pow_self) k
      calc
        _ ≤ (k*(a/k+1))^k := Nat.pow_le_pow_left ha k
        _ ≤ B*(2^(a/k))^k := by rw [mul_pow]; exact Nat.mul_le_mul_left _ powle
        _ ≤ B*p^a := by
          apply Nat.mul_le_mul_left
          rw [← pow_mul]
          exact (Nat.pow_le_pow_right (by decide) (Nat.div_mul_le_self a k)).trans
            (Nat.pow_le_pow_left (Nat.prime_of_mem_primeFactors hp).two_le _)
    · simp only [f,if_neg small,one_mul]
      calc
        _ ≤ (2^a)^k := Nat.pow_le_pow_left a.lt_two_pow_self k
        _ = (2^k)^a := by rw [← pow_mul,← pow_mul,Nat.mul_comm]
        _ ≤ _ := Nat.pow_le_pow_left (by omega) a
  have size : (P.filter fun p => p < 2^k).card ≤ 2^k := by
    apply (card_le_card (show P.filter (fun p => p < 2^k) ⊆ range (2^k) from
      fun p hp => mem_range.mpr (mem_filter.mp hp).2)).trans
    simp
  have prod : (∏ p ∈ P, f p) ≤ B^(2^k) := by
    simp only [f,← prod_filter,prod_const]
    exact Nat.pow_le_pow_right (pow_pos hk _) size
  rw [Nat.card_divisors hn.ne',← prod_pow]
  calc
    _ ≤ ∏ p ∈ P, (f p * p^(n.factorization p)) := prod_le_prod' step
    _ = (∏ p ∈ P, f p)*n := by rw [prod_mul_distrib]; exact congrArg _ (Nat.prod_primeFactors_pow_factorization hn.ne').symm
    _ ≤ _ := Nat.mul_le_mul_right _ prod

/-- For a positive difference h of vertical squares, each pair of divisors
of d*h and h accounts for at most one repeated unsigned gap pair. -/
private theorem decode_repeat (d : ℕ) (hd : 0 < d) (u v x y : ℕ) (hux : u < x)
    (eqv : u^2+d*v^2 = x^2+d*y^2) :
    let h := v^2-y^2
    0 < h ∧ d*h ≤ x^2 ∧ ∃ i ∈ (d*h).divisors, ∃ j ∈ h.divisors,
      ((d*h/i+i)/2,(h/j-j)/2) = (x,y) := by
  intro h
  have hv : y < v := by
    by_contra! hy
    have he := Nat.mul_le_mul_left d (Nat.pow_le_pow_left hy 2)
    have he' := Nat.pow_lt_pow_left hux (by decide : 2 ≠ 0)
    omega
  have hh : 0 < h := Nat.sub_pos_of_lt (Nat.pow_lt_pow_left hv (by decide))
  have hy := Nat.sub_add_cancel (Nat.pow_le_pow_left hv.le 2)
  change h+y^2=v^2 at hy
  have factorV : h = (v-y)*(v+y) := by
    have he := Nat.sub_add_cancel hv.le
    nlinarith only [hy,congrArg (fun z : ℕ => z*(v+y)) he]
  have factorH : d*h = (x-u)*(x+u) := by
    have he := Nat.sub_add_cancel hux.le
    nlinarith only [eqv,congrArg (d*·) hy,congrArg (fun z : ℕ => z*(x+u)) he]
  refine ⟨hh,by nlinarith only [eqv,congrArg (d*·) hy,Nat.zero_le (u^2)],
    x-u,Nat.mem_divisors.mpr ⟨⟨_,factorH⟩,(Nat.mul_pos hd hh).ne'⟩,
    v-y,Nat.mem_divisors.mpr ⟨⟨_,factorV⟩,hh.ne'⟩,?_⟩
  have h₁ : d*h/(x-u)=x+u := by rw [factorH,Nat.mul_div_cancel_left _ (Nat.sub_pos_of_lt hux)]
  have h₂ : h/(v-y)=v+y := by rw [factorV,Nat.mul_div_cancel_left _ (Nat.sub_pos_of_lt hv)]
  rw [h₁,h₂]
  exact Prod.ext (by dsimp; omega) (by dsimp; omega)

/-- Only W²/d positive differences of vertical squares can cause a repeat,
regardless of how high the selected rows extend. -/
theorem gap_repeat_bound (d W : ℕ) (hd : 0 < d) (T : Finset (ℕ × ℕ))
    (width : ∀ z ∈ T, z.1 ≤ W) :
    let q := fun z : ℕ × ℕ => z.1^2+d*z.2^2
    T.card ≤ (T.image q).card + ∑ h ∈ Icc 1 (W^2/d), (d*h).divisors.card*h.divisors.card := by
  classical
  intro q
  let E := T.filter fun z => ∃ w ∈ T, w.1 < z.1 ∧ q w=q z
  let F (h : ℕ) := ((d*h).divisors ×ˢ h.divisors).image fun ij =>
    ((d*h/ij.1+ij.1)/2,(h/ij.2-ij.2)/2)
  have sub : E ⊆ (Icc 1 (W^2/d)).biUnion F := by
    intro z hz
    obtain ⟨hzt,w,_,hw,he⟩ := mem_filter.mp hz
    obtain ⟨hh,hb,i,hi,j,hj,hij⟩ := decode_repeat d hd w.1 w.2 z.1 z.2 hw he
    let h := w.2^2-z.2^2
    refine mem_biUnion.mpr ⟨h,mem_Icc.mpr ⟨hh,?_⟩,mem_image.mpr
      ⟨(i,j),mem_product.mpr ⟨hi,hj⟩,hij⟩⟩
    exact (Nat.le_div_iff_mul_le hd).mpr (by
      rw [Nat.mul_comm]; exact hb.trans (Nat.pow_le_pow_left (width z hzt) 2))
  have cost : E.card ≤ ∑ h ∈ Icc 1 (W^2/d), (d*h).divisors.card*h.divisors.card := by
    apply (card_le_card sub).trans (card_biUnion_le.trans ?_)
    exact sum_le_sum fun h _ => card_image_le.trans (le_of_eq (card_product ..))
  have inj : Set.InjOn q ((T \ E : Finset _) : Set _) := by
    intro z hz w hw e
    obtain ⟨hz,hnz⟩ := mem_sdiff.mp hz
    obtain ⟨hw,hnw⟩ := mem_sdiff.mp hw
    rcases lt_trichotomy z.1 w.1 with h|h|h
    · exact (hnw (mem_filter.mpr ⟨hw,z,hz,h,e⟩)).elim
    · apply Prod.ext h
      change z.1^2+d*z.2^2=w.1^2+d*w.2^2 at e
      rw [h] at e
      exact Nat.pow_left_injective (by decide : 2 ≠ 0)
        (Nat.eq_of_mul_eq_mul_left hd (Nat.add_left_cancel e))
    · exact (hnz (mem_filter.mpr ⟨hz,w,hw,h,e.symm⟩)).elim
  have good := card_le_card (image_mono q (sdiff_subset : T \ E ⊆ T))
  rw [card_image_of_injOn inj] at good
  have part := card_sdiff_add_card_eq_card (show E ⊆ T from filter_subset ..)
  omega

/-- Uniform in the coefficient and in the selected rows: the number lost
to repeated values is at most W²/t once d grows polynomially with W. -/
theorem polynomial_coefficient_gaps (r t : ℕ) : ∃ D₀ : ℕ, ∀ d W : ℕ,
    D₀ ≤ d → 0 < d → W^2 ≤ d^r → ∀ T : Finset (ℕ × ℕ), (∀ z ∈ T, z.1 ≤ W) →
    let q := fun z : ℕ × ℕ => z.1^2+d*z.2^2
    t*T.card ≤ t*(T.image q).card+W^2 := by
  classical
  let k := 2*r+1
  have hk : 0 < k := by dsimp [k]; omega
  obtain ⟨C,divisor⟩ := divisor_power_bound k hk
  refine ⟨t^k*C^2,?_⟩
  intro d W hd₀ hd hW T width q
  have bound (h : ℕ) (hh : h ∈ Icc 1 (W^2/d)) :
      t*((d*h).divisors.card*h.divisors.card) ≤ d := by
    obtain ⟨hhp,hhmax⟩ := mem_Icc.mp hh
    have hdh : d*h ≤ W^2 := by
      rw [Nat.mul_comm]; exact (Nat.le_div_iff_mul_le hd).mp hhmax
    have hh₁ : h ≤ d^r := (Nat.le_mul_of_pos_left _ hd).trans (hdh.trans hW)
    have hd₁ := hdh.trans hW
    suffices he : (t*((d*h).divisors.card*h.divisors.card))^k ≤ d^k by
      by_contra! hn
      exact (Nat.not_lt_of_ge he) (Nat.pow_lt_pow_left hn hk.ne')
    calc
      _ = t^k*((d*h).divisors.card^k*h.divisors.card^k) := by simp only [mul_pow]
      _ ≤ t^k*((C*(d*h))*(C*h)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul
        (divisor _ (Nat.mul_pos hd hhp)) (divisor _ hhp))
      _ ≤ t^k*((C*d^r)*(C*d^r)) := by gcongr
      _ = (t^k*C^2)*(d^r*d^r) := by ring
      _ ≤ d*(d^r*d^r) := Nat.mul_le_mul_right _ hd₀
      _ = d^k := by dsimp [k]; rw [show 2*r+1=r+r+1 by omega,pow_succ,pow_add]; ring
  have cost : t*(∑ h ∈ Icc 1 (W^2/d), (d*h).divisors.card*h.divisors.card) ≤ W^2 := by
    rw [mul_sum]
    exact (sum_le_sum bound).trans (by simpa using Nat.div_mul_le_self (W^2) d)
  have he := Nat.mul_le_mul_left t (gap_repeat_bound d W hd T width)
  rw [Nat.mul_add] at he
  exact he.trans (Nat.add_le_add_left cost _)

/-- At least half the points of a full L by L box give different values
as soon as L²≤d^r and d exceeds a threshold depending only on r. -/
theorem polynomial_coefficient_box (r : ℕ) : ∃ D₀ : ℕ, ∀ d L : ℕ,
    D₀ ≤ d → 0 < d → L^2 ≤ d^r →
    L^2 ≤ 2*(((range L) ×ˢ (range L)).image fun z => z.1^2+d*z.2^2).card := by
  obtain ⟨D₀,h⟩ := polynomial_coefficient_gaps r 2
  refine ⟨D₀,?_⟩
  intro d L h₀ hd hL
  have he := h d L h₀ hd hL ((range L) ×ˢ (range L)) (fun z hz =>
    (mem_range.mp (mem_product.mp hz).1).le)
  simp only [card_product,card_range] at he
  rw [← pow_two] at he
  omega


/-- Linear distinct-value bound with a constant independent of d and S.
Only the horizontal span is restricted; the selected heights can be arbitrary. -/
theorem polynomial_coefficient_strip (r t : ℕ) : ∃ B : ℕ,
    ∀ (d W : ℕ) (S : Finset (ℤ × ℤ)) (p : ℤ × ℤ), 0 < d → p ∈ S →
    (∀ z ∈ S, (z.1-p.1).natAbs ≤ W) → W^2 ≤ d^r → W^2 ≤ t*S.card →
    let q := fun z : ℤ × ℤ => z.1^2+(d:ℤ)*z.2^2
    S.card ≤ B*((S.offDiag.image fun xy => q (xy.1-xy.2)).card+1) := by
  classical
  obtain ⟨D₀,hlarge⟩ := polynomial_coefficient_gaps r (8*(t+1))
  refine ⟨max 8 (4*(D₀^r+1)),?_⟩
  intro d W S p hd hp width scale dense q
  let g := fun z : ℤ × ℤ => ((z.1-p.1).natAbs,(z.2-p.2).natAbs)
  let T := S.image g
  let f := fun z : ℕ × ℕ => z.1^2+d*z.2^2
  let V := S.offDiag.image fun xy => q (xy.1-xy.2)
  let sign := fun z : ℤ × ℤ => (decide (p.1 ≤ z.1),decide (p.2 ≤ z.2))
  have nT : S.card ≤ 4*T.card := by
    have inj : Function.Injective (fun z => (g z,sign z)) := by
      intro x y he
      have h := congrArg Prod.fst he
      have hs := congrArg Prod.snd he
      simp [g,sign,Prod.mk.injEq] at h hs
      exact Prod.ext (by omega) (by omega)
    have sub : (S.image fun z => (g z,sign z)) ⊆ T ×ˢ (univ : Finset (Bool × Bool)) := by
      intro z hz
      obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
      exact mem_product.mpr ⟨mem_image_of_mem _ hx,mem_univ _⟩
    simpa [card_image_of_injective _ inj,Nat.mul_comm] using card_le_card sub
  have cols : ∀ z ∈ T, z.1 ≤ W := by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
    exact width x hx
  have vals : (T.image f).card ≤ V.card+1 := by
    have sub : ((T.image f).image (Nat.cast : ℕ → ℤ)) ⊆ insert 0 V := by
      intro z hz
      obtain ⟨n,hn,rfl⟩ := mem_image.mp hz
      obtain ⟨u,hu,rfl⟩ := mem_image.mp hn
      obtain ⟨x,hx,rfl⟩ := mem_image.mp hu
      by_cases h : x=p
      · simp [h,f,g]
      · exact mem_insert_of_mem (mem_image.mpr ⟨(x,p),mem_offDiag.mpr ⟨hx,hp,h⟩,by simp [f,g,q]⟩)
    exact (by simpa only [card_image_of_injective _ Nat.cast_injective] using card_le_card sub :
      (T.image f).card ≤ (insert 0 V).card).trans (card_insert_le ..)
  by_cases big : D₀ ≤ d
  · have e := hlarge d W big hd scale T cols
    change 8*(t+1)*T.card ≤ 8*(t+1)*(T.image f).card+W^2 at e
    have ey := Nat.mul_le_mul_left (8*(t+1)) vals
    have ex := Nat.mul_le_mul_left (t+1) nT
    have hl : (t+1)*S.card ≤ (t+1)*(8*(V.card+1)) := by nlinarith
    exact (Nat.le_of_mul_le_mul_left hl (by omega)).trans
      (Nat.mul_le_mul_right _ (le_max_left ..))
  · have hW : W ≤ D₀^r := (show W ≤ W^2 by nlinarith only [Nat.le_mul_self W]).trans
        (scale.trans (Nat.pow_le_pow_left (by omega) r))
    have small : T.card ≤ (W+1)*(T.image f).card := by
      have inj : Function.Injective (fun z : ℕ × ℕ => (z.1,f z)) := by
        intro x y he
        obtain ⟨ex,eqv⟩ := Prod.mk.inj he
        apply Prod.ext ex
        change x.1^2+d*x.2^2=y.1^2+d*y.2^2 at eqv
        rw [ex] at eqv
        exact Nat.pow_left_injective (by decide : 2 ≠ 0)
          (Nat.eq_of_mul_eq_mul_left hd (Nat.add_left_cancel eqv))
      have sub : (T.image fun z => (z.1,f z)) ⊆ range (W+1) ×ˢ T.image f := by
        intro z hz
        obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
        exact mem_product.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le (cols x hx)),mem_image_of_mem _ hx⟩
      simpa [card_image_of_injective _ inj] using card_le_card sub
    calc
      _ ≤ 4*((W+1)*(T.image f).card) := nT.trans (Nat.mul_le_mul_left _ small)
      _ ≤ 4*((D₀^r+1)*(V.card+1)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) vals)
      _ = 4*(D₀^r+1)*(V.card+1) := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (le_max_right ..)

/-- Transfer the squarefree bound using the assigned pins, the divisor estimate,
or the remaining arithmetic hypothesis. -/
theorem integral_form_bound (arith : H1) :
  ∃ C : ℕ, ∀ a b c : ℤ, 0 < a → b^2 < 4*a*c → ∀ (S : Finset (ℤ × ℤ)) (k : ℕ),
    0 < k → (S.card : ℝ) ≤ Real.exp ((k:ℝ)^2) →
    let q := fun v : ℤ × ℤ => a*v.1^2+b*v.1*v.2+c*v.2^2
    S.card ≤ k*C*((S.offDiag.image fun xy => q (xy.1-xy.2)).card+1) := by
  classical
  obtain ⟨r,t₀,C,hard⟩ := arith
  obtain ⟨B,strip⟩ := polynomial_coefficient_strip r t₀
  refine ⟨max (max C B) 4,?_⟩
  intro a b c ha hdisc A k hk hsize Q
  let V := fun (q : ℤ × ℤ → ℤ) (T : Finset (ℤ × ℤ)) => T.offDiag.image fun xy => q (xy.1-xy.2)
  obtain ⟨d,hd,hsq,F,_,hF⟩ := squarefree_model a b c ha hdisc
  obtain ⟨hc,hv⟩ := hF A
  let S := A.image F
  let q := fun v : ℤ × ℤ => v.1^2+(d:ℤ)*v.2^2
  change S.card = A.card at hc
  change V q S = (V Q A).image (4*a * ·) at hv
  have hvals := congrArg Finset.card hv
  rw [card_image_of_injective _ (mul_right_injective₀ (by positivity : 4*a ≠ 0))] at hvals
  change A.card ≤ k*max (max C B) 4*((V Q A).card+1)
  rw [← hc,← hvals]
  by_cases outside : ∀ p ∈ S, ∀ W : ℕ, (∀ z ∈ S, (z.1-p.1).natAbs ≤ W) →
      W^2 ≤ t₀*S.card → d^r < W^2
  swap
  · push Not at outside
    obtain ⟨p,hp,W,width,dense,scale⟩ := outside
    have h := strip d W S p hd hp width scale dense
    exact h.trans (Nat.mul_le_mul_right _ (show B ≤ k*max (max C B) 4 by
      calc
        B ≤ max (max C B) 4 := (le_max_right ..).trans (le_max_left ..)
        _ ≤ _ := Nat.le_mul_of_pos_left _ hk))
  by_cases heavy : ∀ T ⊆ S, S.card ≤ 2*T.card → ∀ (M : ℤ), 0 < M →
      ∀ (p : ℤ × ℤ → ℤ × ℤ) (t s : (ℤ × ℤ) × ℤ → ℤ),
      (∀ x ∈ T, let e := (p x,x.1)
        p x ∈ S ∧ s e ∣ x.2-(p x).2-t e ∧
        M ∣ (d:ℤ)*s e*(2*t e+s e) ∧ M ∣ 2*(d:ℤ)*(s e)^2) →
      ∃ r : ℤ, k < ((T.image fun x => (p x,x.1)).filter fun e =>
        ((e.2-e.1.1)^2+(d:ℤ)*(t e)^2) % M = r).card
  · by_cases costly : ∀ (A : Finset ℕ) (X : ℕ → Finset ℕ) (W : ℕ → ℕ),
      (∀ a ∈ A, X a ⊆ range (W a+1)) →
      (∀ a ∈ A, ∀ u ∈ X a, ∃ x ∈ S, ∃ y ∈ S,
        u = (x.1-y.1).natAbs ∧ a = d*(x.2-y.2).natAbs^2) →
      let mass := ∑ a ∈ A, (X a).card
      let cost := ∑ a ∈ A, ∑ b ∈ A, if a=b then (X a).card else
        let h := max a b-min a b
        min (min (X a).card (X b).card) (h.divisors.filter fun j =>
          j ≤ h/j ∧ h/j+j ≤ 2*W (min a b) ∧ h/j-j ≤ 2*W (max a b) ∧ j%2 = (h/j)%2).card
      0 < mass → k*mass^2 < S.card*cost
    · have h := hard d S k hd hsq hk (by rwa [hc]) outside heavy costly
      exact h.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left k ((le_max_left C B).trans (le_max_left ..))))
    dsimp only at costly
    push Not at costly
    obtain ⟨A',X,W,width,pairs,pos,cheap⟩ := costly
    let mass := ∑ a ∈ A', (X a).card
    let cost := ∑ a ∈ A', ∑ b ∈ A', if a=b then (X a).card else
      let h := max a b-min a b
      min (min (X a).card (X b).card) (h.divisors.filter fun j =>
        j ≤ h/j ∧ h/j+j ≤ 2*W (min a b) ∧ h/j-j ≤ 2*W (max a b) ∧ j%2 = (h/j)%2).card
    change 0 < mass at pos
    change S.card*cost ≤ k*mass^2 at cheap
    have energy := divisor_gap_bound d S A' X W width pairs
    change mass^2 ≤ ((V q S).card+1)*cost at energy
    have hcpos : 0 < cost := by
      by_contra! he
      rw [show cost = 0 by omega,mul_zero] at energy
      exact (Nat.not_lt_of_ge energy) (pow_pos pos 2)
    apply Nat.le_of_mul_le_mul_right _ hcpos
    calc
      _ ≤ k*mass^2 := cheap
      _ ≤ k*(((V q S).card+1)*cost) := Nat.mul_le_mul_left _ energy
      _ = k*1*((V q S).card+1)*cost := by ring
      _ ≤ _ := by gcongr; omega
  push Not at heavy
  obtain ⟨T,hsub,half,M,_,p,t,s,pins,cap⟩ := heavy
  have h := shifted_pin_bound d hd S T p M t s hsub k pins cap
  calc
    _ ≤ 2*T.card := half
    _ ≤ 2*(2*k*((V q S).card+1)) := Nat.mul_le_mul_left _ h
    _ = k*4*((V q S).card+1) := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left k (le_max_right ..))

/-- The common-scale estimate follows from the integral-form estimate. -/
theorem common_scale_bound (arith : H1) :
  let X := {p : ℝ² // ∀ i : Fin 2, IsIntegral ℤ (p i)}
  ∃ C : ℕ, ∀ (T : Finset X) (k : ℕ), 0 < k → (T.card : ℝ) ≤ Real.exp ((k:ℝ)^2) →
    (∃ L : ℝ, 0 < L ∧ ∀ x ∈ T, ∀ y ∈ T, ∃ t : ℚ, dist x y^2 = L*t) →
    T.card ≤ k*C*(distinctDistances T+1) := by
  classical
  obtain ⟨C,bound⟩ := integral_form_bound arith
  refine ⟨max C 2,?_⟩
  intro T k hk hsize scale
  obtain ⟨L,hL,rat⟩ := scale
  by_cases tri : ∃ x ∈ T, ∃ y ∈ T, ∃ z ∈ T,
      (y.val 0-x.val 0)*(z.val 1-x.val 1) ≠ (y.val 1-x.val 1)*(z.val 0-x.val 0)
  · obtain ⟨p,hp,q,hq,r,hr,hn⟩ := tri
    obtain ⟨a,b,c,ha,hd,S,hcard,hvalues⟩ := three_pin_model T T (fun _ h => h)
      ⟨p,hp,q,hq,r,hr,hn,L,hL,by
        intro x hx o ho
        rcases ho with rfl|rfl|rfl
        exacts [rat x hx _ hp,rat x hx _ hq,rat x hx _ hr]⟩
    have h := bound a b c ha hd S k hk (by rwa [hcard])
    rw [← hcard]
    exact h.trans (Nat.mul_le_mul (Nat.mul_le_mul_left k (le_max_left ..))
      (Nat.add_le_add_right hvalues 1))
  · push Not at tri
    calc
      _ ≤ 2*distinctDistances T+1 := flat_count T tri
      _ ≤ 1*2*(distinctDistances T+1) := by omega
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul hk (le_max_right ..))


theorem main : H1 → H2 → OMA.R_Erdos89_erdos_89_R1.H2 := by
  classical
  rintro arith ⟨H,hard⟩
  obtain ⟨R,rational⟩ := common_scale_bound arith
  let C := max (2*R) (max H 8)
  let X := {p : ℝ² // ∀ i : Fin 2, IsIntegral ℤ (p i)}
  let f (j : ℕ) : X := ⟨EuclideanSpace.single 0 (j : ℝ), by
    intro i
    by_cases h : i = 0
    · subst i
      simpa using (isIntegral_natCast (R := ℤ) (B := ℝ) j)
    · simpa [PiLp.single_apply, h] using (isIntegral_zero : IsIntegral ℤ (0:ℝ))⟩
  have : Infinite X := Infinite.of_injective f (by
    intro i j hij
    simpa [f] using congrArg (fun p : X => p.val 0) hij)


  apply Asymptotics.IsBigO.of_bound (4*((C:ℝ)+1))
  filter_upwards [eventually_ge_atTop (⌈Real.exp 1⌉₊+2)] with n hn
  have hn2 : 2 ≤ n := by omega
  have hnpos : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hexp : Real.exp 1 ≤ (n:ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (by omega : ⌈Real.exp 1⌉₊ ≤ n))
  have hlog : 1 ≤ Real.log (n:ℝ) := by simpa using Real.log_le_log (Real.exp_pos _) hexp
  let z := Real.sqrt (Real.log n)
  have hz : 1 ≤ z := by simpa [z] using Real.sqrt_le_sqrt hlog
  let k := ⌈z⌉₊
  have hceil : z ≤ (k:ℝ) := Nat.le_ceil _
  have hk : 0 < k := by exact_mod_cast (zero_lt_one.trans_le (hz.trans hceil))
  have hround : (k:ℝ) ≤ 2*z := by
    have h := Nat.ceil_lt_add_one (zero_le_one.trans hz)
    dsimp [k]; linarith
  have hcap : (n:ℝ) ≤ Real.exp ((k:ℝ)^2) := by
    rw [← Real.exp_log hnpos]
    apply Real.exp_le_exp.mpr
    have he : z^2 = Real.log n := Real.sq_sqrt (zero_le_one.trans hlog)
    nlinarith [mul_nonneg (sub_nonneg.mpr hceil) (by positivity : 0 ≤ (k:ℝ)+z)]
  obtain ⟨S₀,h₀⟩ := Infinite.exists_subset_card_eq X n
  obtain ⟨S,hS,hD⟩ := Nat.sInf_mem (show
    {d : ℕ | ∃ S : Finset X, S.card=n ∧ distinctDistances S=d}.Nonempty from ⟨_,S₀,h₀,rfl⟩)
  change distinctDistances S = minimalDistinctDistances X n at hD
  have hfb : S.card ≤ k*(C+1)*(distinctDistances S+1) := by
    by_cases hno : ∀ T ⊆ S, S.card ≤ 2*T.card → ¬ (∃ (f : X → ℤ × ℤ) (a b c : ℝ), ∀ x ∈ T, ∀ y ∈ T,
          dist x y^2 = a*(f x-f y).1^2+b*(f x-f y).1*(f x-f y).2+c*(f x-f y).2^2)
    · have hb := hard S k hk (hS ▸ hcap) (by simpa [hS] using hD) hno
      exact hb.trans (by dsimp [C]; gcongr; omega)
    push Not at hno
    obtain ⟨T,hsub,hhalf,f,a,b,c,chart⟩ := hno
    have mono : distinctDistances T ≤ distinctDistances S := by
      apply card_le_card
      intro r hr
      obtain ⟨⟨x,y⟩,h,rfl⟩ := mem_image.mp hr
      obtain ⟨hx,hy,hne⟩ := mem_offDiag.mp h
      exact mem_image.mpr ⟨(x,y),mem_offDiag.mpr ⟨hsub hx,hsub hy,hne⟩,rfl⟩
    by_cases scale : ∃ L : ℝ, 0 < L ∧ ∃ A B C : ℚ, a=L*A ∧ b=L*B ∧ c=L*C
    · obtain ⟨L,hL,A,B,C',rfl,rfl,rfl⟩ := scale
      have ht : (T.card:ℝ) ≤ Real.exp ((k:ℝ)^2) :=
        (by exact_mod_cast card_le_card hsub : (T.card:ℝ) ≤ S.card).trans (hS ▸ hcap)
      have hb := rational T k hk ht ⟨L,hL,fun x hx y hy => ?_⟩
      · calc
          _ ≤ 2*T.card := hhalf
          _ ≤ 2*(k*R*(distinctDistances T+1)) := Nat.mul_le_mul_left _ hb
          _ = k*(2*R)*(distinctDistances T+1) := by ring
          _ ≤ _ := by dsimp [C]; gcongr; omega
      · let w := f x-f y
        refine ⟨A*w.1^2+B*w.1*w.2+C'*w.2^2,?_⟩
        rw [chart x hx y hy]
        push_cast
        dsimp [w]
        ring
    · have he := irrational_count T f a b c scale chart
      calc
        _ ≤ 2*T.card := hhalf
        _ ≤ 2*(4*distinctDistances T+1) := Nat.mul_le_mul_left _ he
        _ ≤ 1*8*(distinctDistances S+1) := by omega
        _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul (by omega : 1 ≤ k) (by dsimp [C]; omega : 8 ≤ C+1))
  have hd : 0 < distinctDistances S := by
    obtain ⟨x,hx,y,hy,hxy⟩ := one_lt_card.mp (by omega : 1 < S.card)
    exact card_pos.mpr ⟨_,mem_image.mpr ⟨(x,y),mem_offDiag.mpr ⟨hx,hy,hxy⟩,rfl⟩⟩
  let D : ℝ := distinctDistances S
  have hd' : (1:ℝ) ≤ D := by dsimp [D]; exact_mod_cast (show 1 ≤ distinctDistances S from hd)
  rw [hS] at hfb
  have hh : (n:ℝ) ≤ (k:ℝ)*((C:ℝ)+1)*(D+1) := by dsimp [D]; exact_mod_cast hfb
  change ‖(n:ℝ)/z‖ ≤ 4*((C:ℝ)+1)*‖(minimalDistinctDistances X n : ℝ)‖
  rw [← hD,Real.norm_eq_abs,abs_of_nonneg (by positivity),Real.norm_eq_abs,Nat.abs_cast,
    div_le_iff₀ (zero_lt_one.trans_le hz)]
  change (n:ℝ) ≤ 4*((C:ℝ)+1)*D*z
  calc
    _ ≤ _ := hh
    _ ≤ (2*z)*((C:ℝ)+1)*(2*D) := by gcongr; linarith
    _ = _ := by ring

end OMA.R_Erdos89_erdos_89_R1_H2_R3
