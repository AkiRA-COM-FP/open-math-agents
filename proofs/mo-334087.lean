import OMAStatements.S_mo_334087

namespace OMA.S_mo_334087
open Matrix Finset
theorem shiftedHerm {n : ℕ} {A : Mat n} (h : A.PosSemidef) (k : ℕ) : (shifted A k).IsHermitian :=
  h.1.sub ((isHermitian_diagonal_iff.mpr fun _ => IsSelfAdjoint.all _).smul (IsSelfAdjoint.all (k:ℝ)))
end OMA.S_mo_334087

namespace OMA.S_mo_334087
open Matrix Finset
private abbrev Vec (n : ℕ) := Fin n → ℝ

lemma projection_bound {n : ℕ} (P : Mat n) (hp : P.IsHermitian) (he : P*P=P) :
    (((n:ℝ)+1-P.trace) • diagPart P - P).PosSemidef := by
  have hsym (i j : Fin n) : P j i=P i j := hp.apply i j
  have hrow (i : Fin n) : (∑ j,(P i j)^2)=P i i := by
    have hh := congrArg (fun M : Mat n => M i i) he
    simpa only [Matrix.mul_apply,fun j => hsym i j,pow_two] using hh
  have hd0 (i : Fin n) : 0≤P i i := (sum_nonneg fun j _ => sq_nonneg (P i j)).trans_eq (hrow i)
  have hd1 (i : Fin n) : P i i≤1 := by
    have h := single_le_sum (s:=univ) (f:=fun j => (P i j)^2)
      (fun j _ => sq_nonneg (P i j)) (mem_univ i)
    rw [hrow] at h
    nlinarith
  have htr : (∑ i, (1-P i i))=(n:ℝ)-P.trace := by simp [sum_sub_distrib,Matrix.trace]
  have hk : 0≤(n:ℝ)+1-P.trace := by
    linarith [htr,sum_nonneg (s:=univ) (fun i _ => sub_nonneg.mpr (hd1 i))]
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨((isHermitian_diagonal_iff.mpr fun _ => IsSelfAdjoint.all _).smul (IsSelfAdjoint.all _)).sub hp,?_⟩
  intro x
  let y := P *ᵥ x
  let S := ∑ i,(y i)^2
  let W := ∑ i,P i i*(x i)^2
  have hfix : P*ᵥy=y := by change P*ᵥ(P*ᵥx)=P*ᵥx; rw [mulVec_mulVec,he]
  have hS : 0≤S := sum_nonneg fun _ _ => sq_nonneg _
  have hW : 0≤W := sum_nonneg fun i _ => mul_nonneg (hd0 i) (sq_nonneg _)
  have hxy : x ⬝ᵥ y = S := by
    rw [← hfix,Matrix.dotProduct_mulVec]
    have ht : P.transpose=P := hp
    have hy : x ᵥ* P=y := by rw [← ht,vecMul_transpose]
    rw [hy]
    simp [S,dotProduct,pow_two]
  have hcoord (i : Fin n) : (y i)^2 ≤ P i i*S := by
    have hy : (∑ j,P i j*y j)=y i := congrFun hfix i
    simpa only [hy,hrow,S] using sum_mul_sq_le_sq_mul_sq univ (P i) y
  let g := fun i => (y i)^2 + (1-P i i)*S
  have hg (i : Fin n) : 0≤g i := add_nonneg (sq_nonneg _) (mul_nonneg (by linarith [hd1 i]) hS)
  have ht (i : Fin n) : (x i*y i)^2 ≤ (P i i*(x i)^2)*g i := by
    have h := mul_nonneg (sub_nonneg.mpr (hd1 i)) (sub_nonneg.mpr (hcoord i))
    have hc : (y i)^2 ≤ P i i*g i := by dsimp [g]; nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hc (sq_nonneg (x i))]
  have hgs : (∑ i,g i) = ((n:ℝ)+1-P.trace)*S := by
    simp only [g,sum_add_distrib,← sum_mul,htr]
    change S+_ = _
    ring
  have hcs := sum_sq_le_sum_mul_sum_of_sq_le_mul univ
    (fun i _ => mul_nonneg (hd0 i) (sq_nonneg (x i))) (fun i _ => hg i) (fun i _ => ht i)
  change (x ⬝ᵥ y)^2 ≤ W*∑ i,g i at hcs
  rw [hxy,hgs] at hcs
  have hfinal : S≤((n:ℝ)+1-P.trace)*W := by
    rcases hS.eq_or_lt with h|h
    · rw [← h]; exact mul_nonneg hk hW
    · apply (mul_le_mul_iff_left₀ h).mp
      nlinarith [hcs]
  have hw : x ⬝ᵥ (diagPart P *ᵥ x) = W := by
    simp only [diagPart,dotProduct,mulVec_diagonal,W]
    exact sum_congr rfl fun i _ => by ring
  rw [show star x=x by rfl,sub_mulVec,dotProduct_sub,smul_mulVec,dotProduct_smul,hw]
  change 0 ≤ _*W-x ⬝ᵥ y
  linarith
end OMA.S_mo_334087

namespace OMA.S_mo_334087
open Matrix Finset Unitary

private lemma psd_trace_product {n : ℕ} {A B : Mat n} (ha : A.PosSemidef) (hb : B.PosSemidef) :
    0 ≤ (B*A).trace := by
  let U : unitary (Mat n) := ha.1.eigenvectorUnitary
  let L := diagonal ha.1.eigenvalues
  have hs : A = (U : Mat n) * L * star (U : Mat n) := by
    simpa [U,L,conjStarAlgAut_apply] using ha.1.spectral_theorem
  have hps : ((star (U : Mat n))*B*(U : Mat n)).PosSemidef := hb.conjTranspose_mul_mul_same _
  rw [hs,← Matrix.mul_assoc,trace_mul_comm,← Matrix.mul_assoc,← Matrix.mul_assoc]
  change 0 ≤ ∑ i, ((star (U : Mat n)*B*(U : Mat n))*L) i i
  apply Finset.sum_nonneg
  intro i _
  rw [show L = diagonal ha.1.eigenvalues from rfl,Matrix.mul_diagonal]
  exact mul_nonneg hps.diag_nonneg (ha.eigenvalues_nonneg i)

private lemma trace_shift {n : ℕ} (A P : Mat n) (k : ℕ) (ha : A.PosSemidef)
    (hp : ((k:ℝ) • diagPart P - P).PosSemidef) : (P*shifted A k).trace ≤ 0 := by
  have h := psd_trace_product ha hp
  have hdiag : (diagPart P * A).trace=(P*diagPart A).trace := by
    simp [diagPart,Matrix.trace,Matrix.diag,Matrix.diagonal_mul,Matrix.mul_diagonal]
  rw [sub_mul,Matrix.smul_mul,trace_sub,trace_smul,hdiag] at h
  rw [shifted,mul_sub,Matrix.mul_smul,trace_sub,trace_smul]
  simpa only [smul_eq_mul,sub_nonpos,sub_nonneg] using h

private lemma trace_conj {n : ℕ} (U : unitary (Mat n)) (M : Mat n) :
    (conjStarAlgAut ℝ _ U M).trace = M.trace := by
  rw [conjStarAlgAut_apply,trace_mul_cycle,Unitary.coe_star_mul_self,one_mul]

private lemma eigen_sum {n : ℕ} (A : Mat n) (ha : A.PosSemidef) (k : ℕ) (S : Finset (Fin n))
    (hcard : S.card+k=n+1)
    (bound : ∀ P : Mat n, P.IsHermitian → P*P=P →
        (((n:ℝ)+1-P.trace) • diagPart P - P).PosSemidef) :
    ∑ i ∈ S, (shiftedHerm ha k).eigenvalues i ≤ 0 := by
  let H := shifted A k
  let hs : H.IsHermitian := shiftedHerm ha k
  let U := hs.eigenvectorUnitary
  let F := conjStarAlgAut ℝ _ U
  let e : Fin n → ℝ := fun i => if i ∈ S then 1 else 0
  let E := diagonal e
  let P := F E
  have hE : E.IsHermitian := isHermitian_diagonal_iff.mpr fun _ => IsSelfAdjoint.all _
  have hP : P.IsHermitian := by
    change star (F E)=F E
    rw [← map_star,show star E=E from hE]
  have hEE : E*E=E := by
    change diagonal e * diagonal e = diagonal e
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases hi : i∈S <;> simp [e,hi]
  have hPP : P*P=P := by change F E*F E=F E; rw [← map_mul,hEE]
  have htr : P.trace=(S.card:ℝ) := by
    change (conjStarAlgAut ℝ _ U E).trace=_
    rw [trace_conj,show E=diagonal e from rfl,trace_diagonal]
    simp [e]
  have hc : (n:ℝ)+1-P.trace=k := by
    rw [htr]
    have he : (S.card:ℝ)+(k:ℝ)=(n:ℝ)+1 := by exact_mod_cast hcard
    linarith
  have hb := bound P hP hPP
  rw [hc] at hb
  have ht := trace_shift A P k ha hb
  have spec : H = F (diagonal hs.eigenvalues) := by simpa [F,U] using hs.spectral_theorem
  change (P*H).trace ≤ 0 at ht
  rw [spec,show P=F E from rfl,← map_mul,trace_conj] at ht
  change (diagonal e * diagonal hs.eigenvalues).trace ≤ 0 at ht
  rw [diagonal_mul_diagonal,trace_diagonal] at ht
  simpa [e,Finset.sum_ite_mem] using ht
end OMA.S_mo_334087

namespace OMA.S_mo_334087
open Matrix Finset
private lemma scalar_interval {n : ℕ} (e : Fin n → ℝ) (he : Antitone e)
    (k m : ℕ) (hk : 1 ≤ k) (hm : 1 ≤ m) (hkm : k*m ≤ n) (a : ℝ) (ha : 0 ≤ a)
    (hnn : ∀ i, 0 ≤ e i+(k:ℝ)*a) (hs : ∑ i, (e i+(k:ℝ)*a) = (n:ℝ)*a) :
    ∑ i ∈ (univ.filter (fun i : Fin n => m-1 ≤ i.val ∧ i.val<n-m*(k-1))), e i ≤ 0 := by
  let l := m-1
  let b := n-m*(k-1)
  have hspan : m*(k-1)+m = k*m := by
    calc
      _ = m*((k-1)+1) := by rw [Nat.mul_add,Nat.mul_one]
      _ = _ := by rw [Nat.sub_add_cancel hk,Nat.mul_comm]
  have hb : b + m*(k-1)=n := by dsimp [b]; omega
  have hl : l<b := by dsimp [l,b]; omega
  have hbn : b ≤ n := Nat.sub_le _ _
  have hkn : n ≤ k*b := by
    have hmk : m ≤ b := by omega
    have hh := Nat.mul_le_mul_left (k-1) hmk
    have h1 := Nat.sub_add_cancel hk
    nlinarith [Nat.add_mul (k-1) 1 b, Nat.one_mul b]
  let L := univ.filter (fun i : Fin n => i.val<l)
  let T := univ.filter (fun i : Fin n => i.val<b)
  let I := T \ L
  let f (i : Fin n) := e i+(k:ℝ)*a
  have hLT : L⊆T := by intro j hj; simp only [L,T,mem_filter,mem_univ,true_and] at hj ⊢; omega
  have hlc : L.card=l := by simp [L,Fin.card_filter_val_lt,min_eq_right (show l ≤ n by omega)]
  have hbc : T.card=b := by simp [T,Fin.card_filter_val_lt,min_eq_right hbn]
  have hcard : I.card+L.card=T.card := by rw [← card_sdiff_add_card_eq_card hLT]
  have hsum := sum_sdiff hLT (f:=f)
  change ∑ i ∈ I, f i + ∑ i ∈ L,f i = ∑ i ∈ T,f i at hsum
  have horder (i : Fin n) (hi : i∈I) (j : Fin n) (hj : j∈L) : f i ≤ f j := by
    simp only [I,L,T,mem_sdiff,mem_filter,mem_univ,true_and,not_lt] at hi hj
    exact add_le_add (he (show j ≤ i by exact hj.le.trans hi.2)) le_rfl
  have hcross : (L.card:ℝ) * (∑ i ∈ I, f i) ≤ (I.card:ℝ)*(∑ i ∈ L,f i) := calc
    _ = ∑ j ∈ L, ∑ i ∈ I,f i := by simp
    _ ≤ ∑ j ∈ L, ∑ _i ∈ I,f j := sum_le_sum fun j hj => sum_le_sum fun i hi => horder i hi j hj
    _ = _ := by simp [mul_sum]
  have hupper : ∑ i ∈ T,f i ≤ (n:ℝ)*a := (sum_le_univ_sum_of_nonneg (fun i => hnn i)).trans_eq hs
  have hcard' : (I.card:ℝ)+(L.card:ℝ)=b := by exact_mod_cast hcard.trans hbc
  have hbn' : (n:ℝ) ≤ (k:ℝ)*b := by exact_mod_cast hkn
  have hscaled : (b:ℝ)*(∑ i ∈ I,f i) ≤ (I.card:ℝ)*((n:ℝ)*a) := calc
    _ = (I.card:ℝ)*(∑ i ∈ I,f i)+(L.card:ℝ)*(∑ i ∈ I,f i) := by rw [← hcard',add_mul]
    _ ≤ (I.card:ℝ)*(∑ i ∈ I,f i)+(I.card:ℝ)*(∑ i ∈ L,f i) := by linarith only [hcross]
    _ = (I.card:ℝ)*(∑ i ∈ T,f i) := by rw [← mul_add,hsum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hupper (by positivity)
  have hh : ∑ i ∈ I,f i ≤ (I.card:ℝ)*((k:ℝ)*a) := by
    apply le_of_mul_le_mul_left (a:=(b:ℝ)) _ (by exact_mod_cast (show 0<b by omega))
    exact hscaled.trans (by nlinarith only [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hbn' ha) (I.card.cast_nonneg : (0:ℝ) ≤ I.card)])
  have hi : (univ.filter (fun i : Fin n => m-1 ≤ i.val ∧ i.val<n-m*(k-1)))=I := by
    ext i; simp [I,L,T,l,b,and_comm]
  rw [hi]
  simp only [f,sum_add_distrib,sum_const,nsmul_eq_mul] at hh
  linarith

lemma constant_interval {n : ℕ} (A : Mat n) (ha : A.PosSemidef)
    (k m : ℕ) (hk : 1 ≤ k) (hm : 1 ≤ m) (hkm : k*m ≤ n) (a : ℝ) (hc : ∀ i, A i i=a) :
    ∑ i ∈ (univ.filter (fun i : Fin (Fintype.card (Fin n)) => m-1 ≤ i.val ∧ i.val<n-m*(k-1))),
      (shiftedHerm ha k).eigenvalues₀ i ≤ 0 := by
  let H := shifted A k
  let hH := shiftedHerm ha k
  have hd : (k:ℝ) • diagPart A = algebraMap ℝ (Mat n) ((k:ℝ)*a) := by
    ext i j
    by_cases h : i=j <;> simp [diagPart,Matrix.algebraMap_eq_diagonal,h,hc]
  let E := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n)))
  have hval (i : Fin (Fintype.card (Fin n))) :
      hH.eigenvalues (E i)=hH.eigenvalues₀ i := by simp [Matrix.IsHermitian.eigenvalues,E]
  have hn : 0<n := (Nat.mul_pos (by omega : 0<k) (by omega : 0 < m)).trans_le hkm
  have ha0 : 0 ≤ a := hc ⟨0,hn⟩ ▸ ha.diag_nonneg
  have hnn (i : Fin (Fintype.card (Fin n))) : 0 ≤ hH.eigenvalues₀ i+(k:ℝ)*a := by
    apply (Matrix.posSemidef_iff_isHermitian_and_spectrum_nonneg.mp ha).2
    rw [spectrum.add_mem_iff,← hd,neg_add_eq_sub,← hval]
    exact hH.eigenvalues_mem_spectrum_real _
  have htrace : (∑ i, hH.eigenvalues₀ i)=H.trace := by
    rw [hH.trace_eq_sum_eigenvalues]
    exact Fintype.sum_equiv E _ _ fun i => (hval i).symm
  have hsum : ∑ i,(hH.eigenvalues₀ i + (k:ℝ)*a) = (Fintype.card (Fin n):ℝ)*a := by
    rw [sum_add_distrib,htrace]
    simp [H,shifted,Matrix.trace,Matrix.diag,diagPart,hc]
  simpa only [Fintype.card_fin] using
    scalar_interval _ hH.eigenvalues₀_antitone k m hk hm (by simpa using hkm) a ha0 hnn hsum
end OMA.S_mo_334087

open OMA.S_mo_334087
theorem OMA.solution : type_of% @OMA.S_mo_334087.main :=
  ⟨fun _ => projection_bound,fun _ A ha k =>
      ⟨shiftedHerm ha k,fun S hc => eigen_sum A ha k S hc (fun P => projection_bound P)⟩,
   fun _ A ha k m hk hm hkm a hc =>
      ⟨shiftedHerm ha k,constant_interval A ha k m hk hm hkm a hc⟩⟩
