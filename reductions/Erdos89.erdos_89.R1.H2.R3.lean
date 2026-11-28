import OMAReductions.R_Erdos89_erdos_89_R1

-- Reduction of Erdos89.erdos_89.R1.H2. Credit: @wispiANt
open Finset Filter EuclideanGeometry

namespace OMA.R_Erdos89_erdos_89_R1_H2_R3

/-- Uniform estimate when all squared distances share a positive rational scale. -/
def H1 : Prop :=
  let X := {p : ℝ² // ∀ i : Fin 2, IsIntegral ℤ (p i)}
  ∃ C : ℕ, ∀ (T : Finset X) (k : ℕ), 0 < k → (T.card : ℝ) ≤ Real.exp ((k:ℝ)^2) →
    (∃ L : ℝ, 0 < L ∧ ∀ x ∈ T, ∀ y ∈ T, ∃ t : ℚ, dist x y^2 = L*t) →
    T.card ≤ k*C*(distinctDistances T+1)

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

theorem main : H1 → H2 → OMA.R_Erdos89_erdos_89_R1.H2 := by
  classical
  rintro ⟨R,rational⟩ ⟨H,hard⟩
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
