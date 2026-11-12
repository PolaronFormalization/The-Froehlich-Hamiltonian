module
public import GW.Gross.MainDressedSmall

/-! Source main:dressed-form, manuscript6664–6795.
Actual closed dressed forms on Q, original operator representatives,
uniform comparison and full mixed transport of the interacting form. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal BigOperators
namespace GW.Gross
open GW.Model GW.Fock GW.Analysis

/- Source argument component Maps02. -/
-- Source6664–6795: all factors are actual bounded maps on the original Q.
def dressedQPairAlgebraic {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A B : FreeFormDomain →L[ℂ] H) : GW.Operators.AlgebraicForm FreeFormDomain :=
  ((innerₛₗ ℂ).comp A.toLinearMap).compl₂ B.toLinearMap
lemma dressedQPair_bound {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A B : FreeFormDomain →L[ℂ] H) (u w : FreeFormDomain) :
    ‖dressedQPairAlgebraic A B u w‖ ≤ (‖A‖*‖B‖)*‖u‖*‖w‖ := by
  change ‖⟪A u,B w⟫_ℂ‖ ≤ _
  calc
    _ ≤ ‖A u‖*‖B w‖ := norm_inner_le_norm _ _
    _ ≤ (‖A‖*‖u‖)*(‖B‖*‖w‖) :=
      mul_le_mul (A.le_opNorm u) (B.le_opNorm w) (norm_nonneg _) (by positivity)
    _ = _ := by ring
def dressedQPair {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A B : FreeFormDomain →L[ℂ] H) : BoundedForm FreeFormDomain :=
  GW.Operators.boundedAlgebraicForm (dressedQPairAlgebraic A B) (C := ‖A‖*‖B‖)
    (mul_nonneg (norm_nonneg A) (norm_nonneg B))
    (dressedQPair_bound A B)
lemma dressedQPair_apply {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A B : FreeFormDomain →L[ℂ] H) (u w : FreeFormDomain) : dressedQPair A B u w = ⟪A u,B w⟫_ℂ := rfl

def dressedQAnnihilator (f : OneBoson) : FreeFormDomain →L[ℂ] Physical :=
  (commutatorPhaseAnnihilatorMap f).comp grossFormRootMap
lemma dressedQAnnihilator_graph (f : OneBoson) (u : FreeFormDomain) :
    (freeFormDomainInclusion u,dressedQAnnihilator f u) ∈
      (generalizedAnnihilation (phaseMultiplicationKernel f)).graph := by
  have h := commutatorPhaseAnnihilatorMap_graph f (grossFormRootMap u)
  rw [grossFormRootMap_value] at h
  exact h

def dressedExplicitForm (g : OneBoson) (fs : Fin 3 → OneBoson) (C : ℝ) : BoundedForm FreeFormDomain :=
  dressedQPair (ContinuousLinearMap.id ℂ FreeFormDomain) (ContinuousLinearMap.id ℂ FreeFormDomain)-
    dressedQPair freeFormDomainInclusion freeFormDomainInclusion+
    dressedQPair freeFormDomainInclusion (uvFieldLinear g)+
    (C:ℂ) • dressedQPair freeFormDomainInclusion freeFormDomainInclusion-
    (2:ℂ) • (∑ j : Fin 3, (dressedQPair (dressedQAnnihilator (fs j)) (grossFormMomentumMap j)+
      dressedQPair (grossFormMomentumMap j) (dressedQAnnihilator (fs j))))+
    ∑ j : Fin 3,dressedQPair (uvFieldLinear (fs j)) (uvFieldLinear (fs j))

lemma dressedExplicitForm_apply (g : OneBoson) (fs : Fin 3 → OneBoson) (C : ℝ) (u w : FreeFormDomain) :
    dressedExplicitForm g fs C u w = uniformBaseForm u w+
      ⟪freeFormDomainInclusion u,uvFieldLinear g w⟫_ℂ+(C:ℂ)*⟪freeFormDomainInclusion u,freeFormDomainInclusion w⟫_ℂ-
      2*(∑ j : Fin 3,(⟪dressedQAnnihilator (fs j) u,grossFormMomentumMap j w⟫_ℂ+
        ⟪grossFormMomentumMap j u,dressedQAnnihilator (fs j) w⟫_ℂ))+
      ∑ j : Fin 3,⟪uvFieldLinear (fs j) u,uvFieldLinear (fs j) w⟫_ℂ := by
  simp only [dressedExplicitForm,ContinuousLinearMap.add_apply,ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,dressedQPair_apply,
    ContinuousLinearMap.id_apply,uniformBaseForm_apply,smul_eq_mul]

/- Source argument component Continuity02. -/
lemma dressedQPair_opNorm {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A B : FreeFormDomain →L[ℂ] H) : ‖dressedQPair A B‖ ≤ ‖A‖*‖B‖ :=
  (form_norm_le_iff (dressedQPair A B) (mul_nonneg (norm_nonneg A) (norm_nonneg B))).mpr
    (dressedQPair_bound A B)
lemma dressedQPair_add_left {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A A' B : FreeFormDomain →L[ℂ] H) : dressedQPair (A+A') B = dressedQPair A B+dressedQPair A' B := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro w
  simp only [ContinuousLinearMap.add_apply,dressedQPair_apply,inner_add_left]
lemma dressedQPair_add_right {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A B B' : FreeFormDomain →L[ℂ] H) : dressedQPair A (B+B') = dressedQPair A B+dressedQPair A B' := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro w
  simp only [ContinuousLinearMap.add_apply,dressedQPair_apply,inner_add_right]
lemma dressedQPair_continuous {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    Continuous (fun p : (FreeFormDomain →L[ℂ] H) × (FreeFormDomain →L[ℂ] H) => dressedQPair p.1 p.2) :=
  fiberBilinear_continuous dressedQPair dressedQPair_add_left dressedQPair_add_right dressedQPair_opNorm

lemma dressedQAnnihilator_difference_bound (f g : OneBoson) :
    ‖dressedQAnnihilator f-dressedQAnnihilator g‖ ≤ ‖f-g‖ := by
  apply (dressedQAnnihilator f-dressedQAnnihilator g).opNorm_le_bound (norm_nonneg (f-g))
  intro u
  change ‖commutatorPhaseAnnihilatorMap f (grossFormRootMap u)-
    commutatorPhaseAnnihilatorMap g (grossFormRootMap u)‖ ≤ ‖f-g‖*‖u‖
  exact (derivative_annihilator_coefficient_bound f g (grossFormRootMap u)).trans
    (mul_le_mul_of_nonneg_left (grossFormRootMap_norm u) (norm_nonneg (f-g)))
lemma dressedQAnnihilator_continuous : Continuous dressedQAnnihilator := by
  have h : LipschitzWith (1:NNReal) dressedQAnnihilator := lipschitzWith_iff_norm_sub_le.mpr (fun f g => by
    simpa only [NNReal.coe_one,one_mul] using dressedQAnnihilator_difference_bound f g)
  exact h.continuous

lemma dressedQField_difference_bound (f g : OneBoson) :
    ‖uvFieldLinear f-uvFieldLinear g‖ ≤ 2*‖f-g‖ := by
  apply (uvFieldLinear f-uvFieldLinear g).opNorm_le_bound (by positivity)
  intro u
  change ‖grossFormFieldMap f (grossFormRootMap u)-grossFormFieldMap g (grossFormRootMap u)‖ ≤ (2*‖f-g‖)*‖u‖
  rw [← grossFormFieldMap_sub]
  exact (grossFormFieldMap_bound (f-g) (grossFormRootMap u)).trans
    (mul_le_mul_of_nonneg_left (grossFormRootMap_norm u) (by positivity))
lemma dressedQField_continuous : Continuous uvFieldLinear := by
  have h : LipschitzWith (2:NNReal) uvFieldLinear := lipschitzWith_iff_norm_sub_le.mpr (fun f g => by
    simpa only [NNReal.coe_ofNat] using dressedQField_difference_bound f g)
  exact h.continuous

/- Source argument component LimitComponents03. -/
-- Supply the existing bounded-convergence instance explicitly; no topology is changed.
local instance : ContinuousAdd (BoundedForm FreeFormDomain) :=
  (ContinuousLinearMap.isTopologicalAddGroup (E := FreeFormDomain)
    (F := FreeFormDomain →L[ℂ] ℂ) (σ := starRingEnd ℂ)).toContinuousAdd

lemma dressedContinuous_pair_limit {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (f : X × Y → Z) (hc : Continuous f)
    (As : ℝ → X) (Bs : ℝ → Y) (A : X) (B : Y)
    (hA : Tendsto As atTop (𝓝 A)) (hB : Tendsto Bs atTop (𝓝 B)) :
    Tendsto (fun R => f (As R,Bs R)) atTop (𝓝 (f (A,B))) :=
  (hc.tendsto (A,B)).comp (hA.prodMk_nhds hB)

lemma dressedQAnnihilator_tendsto (fs : ℝ → OneBoson) (f : OneBoson) (hf : Tendsto fs atTop (𝓝 f)) :
    Tendsto (fun R => dressedQAnnihilator (fs R)) atTop (𝓝 (dressedQAnnihilator f)) :=
  (dressedQAnnihilator_continuous.tendsto f).comp hf
lemma dressedQField_tendsto (fs : ℝ → OneBoson) (f : OneBoson) (hf : Tendsto fs atTop (𝓝 f)) :
    Tendsto (fun R => uvFieldLinear (fs R)) atTop (𝓝 (uvFieldLinear f)) :=
  (dressedQField_continuous.tendsto f).comp hf
lemma dressedQPair_tendsto (As Bs : ℝ → FreeFormDomain →L[ℂ] Physical)
    (A B : FreeFormDomain →L[ℂ] Physical) (hA : Tendsto As atTop (𝓝 A)) (hB : Tendsto Bs atTop (𝓝 B)) :
    Tendsto (fun R => dressedQPair (As R) (Bs R)) atTop (𝓝 (dressedQPair A B)) :=
  dressedContinuous_pair_limit (fun p => dressedQPair p.1 p.2)
    (dressedQPair_continuous (H := Physical)) As Bs A B hA hB

lemma dressedQCrossComponent_tendsto (fs : ℝ → OneBoson) (f : OneBoson) (j : Fin 3)
    (hf : Tendsto fs atTop (𝓝 f)) :
    Tendsto (fun R => dressedQPair (dressedQAnnihilator (fs R)) (grossFormMomentumMap j)+
      dressedQPair (grossFormMomentumMap j) (dressedQAnnihilator (fs R))) atTop
      (𝓝 (dressedQPair (dressedQAnnihilator f) (grossFormMomentumMap j)+
        dressedQPair (grossFormMomentumMap j) (dressedQAnnihilator f))) := by
  have ha := dressedQAnnihilator_tendsto fs f hf
  have hl := dressedQPair_tendsto (fun R => dressedQAnnihilator (fs R)) (fun _ => grossFormMomentumMap j)
    (dressedQAnnihilator f) (grossFormMomentumMap j) ha tendsto_const_nhds
  have hr := dressedQPair_tendsto (fun _ => grossFormMomentumMap j) (fun R => dressedQAnnihilator (fs R))
    (grossFormMomentumMap j) (dressedQAnnihilator f) tendsto_const_nhds ha
  exact hl.add hr
lemma dressedQSquareComponent_tendsto (fs : ℝ → OneBoson) (f : OneBoson) (hf : Tendsto fs atTop (𝓝 f)) :
    Tendsto (fun R => dressedQPair (uvFieldLinear (fs R)) (uvFieldLinear (fs R))) atTop
      (𝓝 (dressedQPair (uvFieldLinear f) (uvFieldLinear f))) :=
  dressedQPair_tendsto (fun R => uvFieldLinear (fs R)) (fun R => uvFieldLinear (fs R))
    (uvFieldLinear f) (uvFieldLinear f) (dressedQField_tendsto fs f hf) (dressedQField_tendsto fs f hf)

/- Source argument component Counterterm01. -/
lemma dressed_counterterm_split_density (α K R : ℝ) (hR : K ≤ R) (k : GW.Space) :
    dressedCountertermDensity α (highRegion K) k =
      dressedCountertermDensity α (highRegion K ∩ lowRegion R) k+
        dressedCountertermDensity α (highRegion R) k := by
  by_cases hk : K < ‖k‖
  · by_cases hkr : ‖k‖ ≤ R
    · simp only [dressedCountertermDensity,Set.indicator_of_mem (show k ∈ highRegion K from hk),
        Set.indicator_of_mem (show k ∈ highRegion K ∩ lowRegion R from ⟨hk,hkr⟩),
        Set.indicator_of_notMem (show k ∉ highRegion R from not_lt.mpr hkr),add_zero]
    · have hrk : R < ‖k‖ := lt_of_not_ge hkr
      simp only [dressedCountertermDensity,Set.indicator_of_mem (show k ∈ highRegion K from hk),
        Set.indicator_of_notMem (show k ∉ highRegion K ∩ lowRegion R from fun h => hkr h.2),
        Set.indicator_of_mem (show k ∈ highRegion R from hrk),zero_add]
  · have hrk : ¬ R < ‖k‖ := not_lt.mpr ((le_of_not_gt hk).trans hR)
    simp only [dressedCountertermDensity,Set.indicator_of_notMem (show k ∉ highRegion K from hk),
      Set.indicator_of_notMem (show k ∉ highRegion K ∩ lowRegion R from fun h => hk h.1),
      Set.indicator_of_notMem (show k ∉ highRegion R from hrk),add_zero]

lemma dressedInfiniteCounterterm_split (α K R : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (hR : K ≤ R) :
    dressedInfiniteCounterterm α K = conjugationCounterterm α K R+dressedInfiniteCounterterm α R := by
  have hRp : 0 < R := hK.trans_le hR
  have hs := dressedCountertermDensity_integrable α K hα hK (highRegion K ∩ lowRegion R)
    ((highRegion_measurable K).inter (lowRegion_measurable R)) (fun _ h => h.1)
  have ht := dressedCountertermDensity_integrable α R hα hRp (highRegion R) (highRegion_measurable R) (fun _ h => h)
  change (∫ k, dressedCountertermDensity α (highRegion K) k ∂volume) = _
  rw [integral_congr_ae (Eventually.of_forall (dressed_counterterm_split_density α K R hR)),integral_add hs ht]
  congr 1
  exact integral_indicator ((highRegion_measurable K).inter (lowRegion_measurable R))

lemma dressedInfiniteCounterterm_error (α K R : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (hR : K ≤ R) :
    ‖dressedInfiniteCounterterm α K-conjugationCounterterm α K R‖ ≤ 2*coefficientETail α R := by
  rw [dressedInfiniteCounterterm_split α K R hα hK hR,add_sub_cancel_left]
  exact dressedInfiniteCounterterm_bound α R hα (hK.trans_le hR)

lemma dressedCounterterm_real_tendsto (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) :
    Tendsto (fun R : ℝ => conjugationCounterterm α K R) atTop (𝓝 (dressedInfiniteCounterterm α K)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht : Tendsto (fun R : ℝ => 2*coefficientETail α R) atTop (𝓝 0) := by
    simpa only [mul_zero] using (coefficientETail_tendsto α hα).const_mul 2
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ ht
  filter_upwards [eventually_ge_atTop K] with R hR
  rw [norm_sub_rev]
  exact dressedInfiniteCounterterm_error α K R hα hK hR

/- Source argument component Cross01. -/
lemma dressedQ_cross_bound (fs : Fin 3 → OneBoson) (u : FreeFormDomain) (a : ℝ) (ha : 0 ≤ a)
    (hm : (∑ j : Fin 3, ‖fs j‖^2) ≤ a^2) :
    ‖∑ j : Fin 3,(⟪dressedQAnnihilator (fs j) u,grossFormMomentumMap j u⟫_ℂ+
      ⟪grossFormMomentumMap j u,dressedQAnnihilator (fs j) u⟫_ℂ)‖ ≤ a*uniformFreeEnergy u := by
  let N := ‖physicalNumberPower (1/2) (uniformRootInput u)‖
  let P := ‖freeMomentumModulus ⟨(show freeFormOperator.domain from u).val,freeForm_momentum_mem u⟩‖
  have hN : 0 ≤ N := norm_nonneg _
  have hP : 0 ≤ P := norm_nonneg _
  have hcoeff := Real.sqrt_le_sqrt hm
  rw [Real.sqrt_sq ha] at hcoeff
  have hpsum : Real.sqrt (∑ j : Fin 3, ‖grossFormMomentumMap j u‖^2) = P := by
    rw [← grossFormMomentum_norm_sq,Real.sqrt_sq (norm_nonneg _)]
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt (s := Finset.univ)
    (fun j : Fin 3 => ‖fs j‖) (fun j : Fin 3 => ‖grossFormMomentumMap j u‖)
  have hs : (∑ j : Fin 3, ‖dressedQAnnihilator (fs j) u‖*‖grossFormMomentumMap j u‖) ≤ a*N*P := by
    calc
      _ ≤ ∑ j : Fin 3, (‖fs j‖*N)*‖grossFormMomentumMap j u‖ :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (uniformAnnihilator_bound (fs j) u) (norm_nonneg _))
      _ = N*(∑ j : Fin 3, ‖fs j‖*‖grossFormMomentumMap j u‖) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ N*(Real.sqrt (∑ j : Fin 3, ‖fs j‖^2)*Real.sqrt (∑ j : Fin 3, ‖grossFormMomentumMap j u‖^2)) :=
        mul_le_mul_of_nonneg_left hcs hN
      _ ≤ N*(a*P) := by
        rw [hpsum]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcoeff hP) hN
      _ = _ := by ring
  have ht : ‖∑ j : Fin 3,(⟪dressedQAnnihilator (fs j) u,grossFormMomentumMap j u⟫_ℂ+
      ⟪grossFormMomentumMap j u,dressedQAnnihilator (fs j) u⟫_ℂ)‖ ≤
      2*(∑ j : Fin 3, ‖dressedQAnnihilator (fs j) u‖*‖grossFormMomentumMap j u‖) := by
    apply (norm_sum_le _ _).trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    have h₁ := norm_inner_le_norm (𝕜 := ℂ) (dressedQAnnihilator (fs j) u) (grossFormMomentumMap j u)
    have h₂ := norm_inner_le_norm (𝕜 := ℂ) (grossFormMomentumMap j u) (dressedQAnnihilator (fs j) u)
    exact (norm_add_le _ _).trans (by nlinarith)
  have hnp : 2*N*P ≤ N^2+P^2 := by nlinarith [sq_nonneg (N-P)]
  have he : uniformFreeEnergy u = P^2+N^2 := rfl
  have hf := mul_le_mul_of_nonneg_left hnp ha
  rw [he]
  nlinarith

/- Source argument component Squares01. -/
lemma dressedQ_field_bound (f : OneBoson) (u : FreeFormDomain) :
    ‖uvFieldLinear f u‖ ≤ 2*‖f‖*‖u‖ := by
  have hb := grossFormFieldMap_bound f (grossFormRootMap u)
  exact hb.trans (mul_le_mul_of_nonneg_left (grossFormRootMap_norm u) (by positivity))
lemma dressedQ_square_bound (fs : Fin 3 → OneBoson) (u : FreeFormDomain) (a : ℝ)
    (hm : (∑ j : Fin 3, ‖fs j‖^2) ≤ a^2) :
    ‖∑ j : Fin 3,⟪uvFieldLinear (fs j) u,uvFieldLinear (fs j) u⟫_ℂ‖ ≤ 4*a^2*‖u‖^2 := by
  have hb (j : Fin 3) : ‖⟪uvFieldLinear (fs j) u,uvFieldLinear (fs j) u⟫_ℂ‖ ≤ 4*‖fs j‖^2*‖u‖^2 := by
    have hs := dressedQ_field_bound (fs j) u
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hs 2
    exact (norm_inner_le_norm (uvFieldLinear (fs j) u) (uvFieldLinear (fs j) u)).trans (by nlinarith)
  calc
    _ ≤ ∑ j : Fin 3, ‖⟪uvFieldLinear (fs j) u,uvFieldLinear (fs j) u⟫_ℂ‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin 3, 4*‖fs j‖^2*‖u‖^2 := Finset.sum_le_sum (fun j _ => hb j)
    _ = 4*(∑ j : Fin 3, ‖fs j‖^2)*‖u‖^2 := by rw [Finset.mul_sum,Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm (by norm_num)) (sq_nonneg _)

lemma dressedQ_low_bound (g : OneBoson) (u : FreeFormDomain) :
    ‖⟪freeFormDomainInclusion u,uvFieldLinear g u⟫_ℂ‖ ≤
      (1/4:ℝ)*uniformFreeEnergy u+4*‖g‖^2*‖freeFormDomainInclusion u‖^2 := by
  have h := uniformField_diagonal_bound g u
  have he := uniformFreeEnergy_root_le u
  have hg := sq_nonneg ((1/2:ℝ)*‖physicalNumberPower (1/2) (uniformRootInput u)‖-
    2*‖g‖*‖freeFormDomainInclusion u‖)
  exact h.trans (by nlinarith)

/- Source argument component Diagonal01. -/
lemma dressedQ_scalar_bound (C c : ℝ) (hc : |C| ≤ c) (u : FreeFormDomain) :
    ‖(C:ℂ)*⟪freeFormDomainInclusion u,freeFormDomainInclusion u⟫_ℂ‖ ≤ c*‖freeFormDomainInclusion u‖^2 := by
  calc
    _ = |C| *‖⟪freeFormDomainInclusion u,freeFormDomainInclusion u⟫_ℂ‖ := by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    _ ≤ |C| *(‖freeFormDomainInclusion u‖*‖freeFormDomainInclusion u‖) :=
      mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (abs_nonneg C)
    _ ≤ c*(‖freeFormDomainInclusion u‖*‖freeFormDomainInclusion u‖) :=
      mul_le_mul_of_nonneg_right hc (mul_self_nonneg _)
    _ = _ := by ring

lemma dressedQ_error_triangle (l t z s : ℂ) :
    ‖l+t-2*z+s‖ ≤ ‖l‖+‖t‖+2*‖z‖+‖s‖ := by
  have h₁ := norm_add_le (l+t-2*z) s
  have h₂ := norm_sub_le (l+t) (2*z)
  have h₃ := norm_add_le l t
  simp only [norm_mul,Complex.norm_ofNat] at h₂
  linarith

lemma dressedExplicitForm_diagonal_error (g : OneBoson) (fs : Fin 3 → OneBoson) (C c a : ℝ)
    (ha : 0 ≤ a) (hm : (∑ j : Fin 3, ‖fs j‖^2) ≤ a^2) (hc : |C| ≤ c) (u : FreeFormDomain) :
    ‖dressedExplicitForm g fs C u u-uniformBaseForm u u‖ ≤
      (2*a+4*a^2+(1/4:ℝ))*uniformFreeEnergy u+
        (4*a^2+c+4*‖g‖^2)*‖freeFormDomainInclusion u‖^2 := by
  let l : ℂ := ⟪freeFormDomainInclusion u,uvFieldLinear g u⟫_ℂ
  let t : ℂ := (C:ℂ)*⟪freeFormDomainInclusion u,freeFormDomainInclusion u⟫_ℂ
  let z : ℂ := ∑ j : Fin 3,(⟪dressedQAnnihilator (fs j) u,grossFormMomentumMap j u⟫_ℂ+
    ⟪grossFormMomentumMap j u,dressedQAnnihilator (fs j) u⟫_ℂ)
  let s : ℂ := ∑ j : Fin 3,⟪uvFieldLinear (fs j) u,uvFieldLinear (fs j) u⟫_ℂ
  have he : dressedExplicitForm g fs C u u-uniformBaseForm u u = l+t-2*z+s := by
    rw [dressedExplicitForm_apply]
    dsimp only [l,t,z,s]
    ring
  rw [he]
  have hl : ‖l‖ ≤ (1/4:ℝ)*uniformFreeEnergy u+4*‖g‖^2*‖freeFormDomainInclusion u‖^2 := dressedQ_low_bound g u
  have ht : ‖t‖ ≤ c*‖freeFormDomainInclusion u‖^2 := dressedQ_scalar_bound C c hc u
  have hz : ‖z‖ ≤ a*uniformFreeEnergy u := dressedQ_cross_bound fs u a ha hm
  have hs : ‖s‖ ≤ 4*a^2*‖u‖^2 := dressedQ_square_bound fs u a hm
  have hn := uniformFreeEnergy_norm u
  have h := dressedQ_error_triangle l t z s
  nlinarith

/- Source argument component Hermitian03. -/
lemma dressedQPair_swap {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A B : FreeFormDomain →L[ℂ] H) (u w : FreeFormDomain) :
    dressedQPair A B u w = star (dressedQPair B A w u) :=
  (inner_conj_symm _ _).symm
lemma dressedQCross_hermitian (f : OneBoson) (j : Fin 3) (u w : FreeFormDomain) :
    ⟪dressedQAnnihilator f u,grossFormMomentumMap j w⟫_ℂ+
      ⟪grossFormMomentumMap j u,dressedQAnnihilator f w⟫_ℂ =
    star (⟪dressedQAnnihilator f w,grossFormMomentumMap j u⟫_ℂ+
      ⟪grossFormMomentumMap j w,dressedQAnnihilator f u⟫_ℂ) := by
  rw [star_add]
  simp only [Complex.star_def,inner_conj_symm]
  exact add_comm _ _
lemma dressedExplicitForm_hermitian (g : OneBoson) (fs : Fin 3 → OneBoson) (C : ℝ)
    (u w : FreeFormDomain) :
    dressedExplicitForm g fs C u w = star (dressedExplicitForm g fs C w u) := by
  have hb := uniformBaseForm_hermitian u w
  have hl := uvFieldForm_hermitian g u w
  change ⟪freeFormDomainInclusion u,uvFieldLinear g w⟫_ℂ =
    star ⟪freeFormDomainInclusion w,uvFieldLinear g u⟫_ℂ at hl
  have hc := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun j _ => dressedQCross_hermitian (fs j) j u w)
  rw [← star_sum] at hc
  rw [dressedExplicitForm_apply,dressedExplicitForm_apply,hb,hl,hc]
  simp only [star_add,star_sub,star_mul,map_ofNat,Complex.star_def,Complex.conj_ofReal,inner_conj_symm,map_sum]
  ring

/- Source argument component Comparison03. -/
def dressedFiniteForm (α K R : ℝ) (hα : 0 ≤ α) (hK : 0 < K) : BoundedForm FreeFormDomain :=
  dressedExplicitForm (cutoffL2 α K hα hK) (derivativeFiniteCoefficient α K R hα hK) (conjugationCounterterm α K R)
def dressedInfiniteForm (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) : BoundedForm FreeFormDomain :=
  dressedExplicitForm (cutoffL2 α K hα hK) (derivativeCoefficient α K hα hK) (dressedInfiniteCounterterm α K)
def dressedFormComparisonConstant (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) : ℝ :=
  4*(grossSourceA α K hα hK)^2+2*coefficientETail α K+4*‖cutoffL2 α K hα hK‖^2
lemma dressedFormComparisonConstant_nonneg (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) :
    0 ≤ dressedFormComparisonConstant α K hα hK := by
  unfold dressedFormComparisonConstant
  have hE := coefficientETail_nonneg α K
  positivity

lemma dressedForm_relative_coefficient (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (hKS : standardGrossCutoff α ≤ K) :
    2*grossSourceA α K hα hK+4*(grossSourceA α K hα hK)^2+(1/4:ℝ) ≤ 1/2 := by
  have hr := dressedRelativeCoefficient_witness α (1/8) K hα (by norm_num) hKS
  have hs : 1 ≤ Real.sqrt 2 := by
    have he := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
    nlinarith [Real.sqrt_nonneg 2]
  have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ 4*(grossSourceA α K hα hK)^2 by positivity)
  have ht := Real.sqrt_nonneg (coefficientTTail α K)
  unfold dressedRelativeCoefficient at hr
  nlinarith

lemma dressedExplicitForm_source_error (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (hKS : standardGrossCutoff α ≤ K) (fs : Fin 3 → OneBoson) (C : ℝ)
    (hm : (∑ j : Fin 3, ‖fs j‖^2) ≤ (grossSourceA α K hα hK)^2)
    (hc : |C| ≤ 2*coefficientETail α K) (u : FreeFormDomain) :
    ‖dressedExplicitForm (cutoffL2 α K hα hK) fs C u u-uniformBaseForm u u‖ ≤
      (1/2:ℝ)*uniformFreeEnergy u+dressedFormComparisonConstant α K hα hK*‖freeFormDomainInclusion u‖^2 := by
  have h := dressedExplicitForm_diagonal_error (cutoffL2 α K hα hK) fs C (2*coefficientETail α K)
    (grossSourceA α K hα hK) (norm_nonneg _) hm hc u
  have hr := dressedForm_relative_coefficient α K hα hK hKS
  exact h.trans (add_le_add (mul_le_mul_of_nonneg_right hr (uniformFreeEnergy_nonneg u)) le_rfl)

/- Source argument component Limit05. -/
local instance : ContinuousAdd (BoundedForm FreeFormDomain) :=
  (ContinuousLinearMap.isTopologicalAddGroup (E := FreeFormDomain)
    (F := FreeFormDomain →L[ℂ] ℂ) (σ := starRingEnd ℂ)).toContinuousAdd
local instance : ContinuousSub (BoundedForm FreeFormDomain) :=
  @IsTopologicalAddGroup.to_continuousSub (BoundedForm FreeFormDomain) _ _
    (ContinuousLinearMap.isTopologicalAddGroup (E := FreeFormDomain)
      (F := FreeFormDomain →L[ℂ] ℂ) (σ := starRingEnd ℂ))
local instance : ContinuousSMul ℂ (BoundedForm FreeFormDomain) :=
  ContinuousLinearMap.continuousSMul

lemma dressedQCrossSum_tendsto (fs : ℝ → Fin 3 → OneBoson) (f : Fin 3 → OneBoson)
    (hf : ∀ j, Tendsto (fun R => fs R j) atTop (𝓝 (f j))) :
    Tendsto (fun R => ∑ j : Fin 3,(dressedQPair (dressedQAnnihilator (fs R j)) (grossFormMomentumMap j)+
      dressedQPair (grossFormMomentumMap j) (dressedQAnnihilator (fs R j)))) atTop
      (𝓝 (∑ j : Fin 3,(dressedQPair (dressedQAnnihilator (f j)) (grossFormMomentumMap j)+
        dressedQPair (grossFormMomentumMap j) (dressedQAnnihilator (f j))))) :=
  tendsto_finsetSum Finset.univ (fun j _ => dressedQCrossComponent_tendsto (fun R => fs R j) (f j) j (hf j))
lemma dressedQSquareSum_tendsto (fs : ℝ → Fin 3 → OneBoson) (f : Fin 3 → OneBoson)
    (hf : ∀ j, Tendsto (fun R => fs R j) atTop (𝓝 (f j))) :
    Tendsto (fun R => ∑ j : Fin 3,dressedQPair (uvFieldLinear (fs R j)) (uvFieldLinear (fs R j))) atTop
      (𝓝 (∑ j : Fin 3,dressedQPair (uvFieldLinear (f j)) (uvFieldLinear (f j)))) :=
  tendsto_finsetSum Finset.univ (fun j _ => dressedQSquareComponent_tendsto (fun R => fs R j) (f j) (hf j))
lemma dressedQScalar_tendsto (Cs : ℝ → ℝ) (C : ℝ) (hC : Tendsto Cs atTop (𝓝 C)) :
    Tendsto (fun R => (Cs R : ℂ) • dressedQPair freeFormDomainInclusion freeFormDomainInclusion) atTop
      (𝓝 ((C:ℂ) • dressedQPair freeFormDomainInclusion freeFormDomainInclusion)) := by
  have hc : Tendsto (fun R => (Cs R : ℂ)) atTop (𝓝 (C:ℂ)) := Complex.continuous_ofReal.continuousAt.tendsto.comp hC
  exact hc.smul tendsto_const_nhds

lemma dressedExplicitForm_tendsto (g : OneBoson) (fs : ℝ → Fin 3 → OneBoson) (f : Fin 3 → OneBoson)
    (hf : ∀ j : Fin 3, Tendsto (fun R => fs R j) atTop (𝓝 (f j)))
    (Cs : ℝ → ℝ) (C : ℝ) (hC : Tendsto Cs atTop (𝓝 C)) :
    Tendsto (fun R => dressedExplicitForm g (fs R) (Cs R)) atTop (𝓝 (dressedExplicitForm g f C)) := by
  let b0 : BoundedForm FreeFormDomain :=
    dressedQPair (ContinuousLinearMap.id ℂ FreeFormDomain) (ContinuousLinearMap.id ℂ FreeFormDomain)-
      dressedQPair freeFormDomainInclusion freeFormDomainInclusion+
      dressedQPair freeFormDomainInclusion (uvFieldLinear g)
  have hb0 : Tendsto (fun _ : ℝ => b0) atTop (𝓝 b0) := tendsto_const_nhds
  have hx := dressedQCrossSum_tendsto fs f hf
  have hs := dressedQSquareSum_tendsto fs f hf
  have ht := dressedQScalar_tendsto Cs C hC
  exact ((hb0.add ht).sub (hx.const_smul (2:ℂ))).add hs

lemma dressedForms_real_tendsto (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) :
    Tendsto (fun R : ℝ => dressedFiniteForm α K R hα hK) atTop (𝓝 (dressedInfiniteForm α K hα hK)) :=
  dressedExplicitForm_tendsto (cutoffL2 α K hα hK) (fun R => derivativeFiniteCoefficient α K R hα hK)
    (derivativeCoefficient α K hα hK) (derivativeFiniteCoefficient_tendsto α K hα hK)
    (conjugationCounterterm α K) (dressedInfiniteCounterterm α K) (dressedCounterterm_real_tendsto α K hα hK)

/- Source argument component Weyl01. -/
lemma dressedH0ToQ_dense : DenseRange constructionH0ToQ := by
  intro u
  apply closure_mono _ (freeFormCore_dense u)
  intro v hv
  have hv' : freeFormDomainInclusion v ∈ freeCutoffCore := hv
  let w : freeHamiltonian.domain := ⟨freeFormDomainInclusion v,freeCutoffCore_le_H0 hv'⟩
  refine ⟨w,?_⟩
  apply grossFormDomainInclusion_injective
  exact constructionH0ToQ_value w

def dressedFiniteQWeyl (α K R : ℝ) (hα : 0 ≤ α) (hK : 0 < K) : FreeFormDomain →L[ℂ] FreeFormDomain :=
  grossFormWeylMap (grossFiniteDressingCoefficient α K R hα hK)
    (fun j => grossForm_truncate_momentum_memLp (grossDressingCoefficient α K hα hK) j
      (grossForm_momentum_memLp α K hα hK j) R)
    (grossForm_truncate_even (grossDressingCoefficient α K hα hK) R (grossForm_coefficient_even α K hα hK))
def dressedInfiniteQWeyl (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) : FreeFormDomain →L[ℂ] FreeFormDomain :=
  grossFormWeylMap (grossDressingCoefficient α K hα hK) (grossForm_momentum_memLp α K hα hK)
    (grossForm_coefficient_even α K hα hK)

lemma dressedFiniteQWeyl_source (α K R : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (u : FreeFormDomain) :
    dressedFiniteQWeyl α K R hα hK u = grossSourceFiniteQInput true α K R hα hK u := rfl
lemma dressedInfiniteQWeyl_source (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (u : FreeFormDomain) :
    dressedInfiniteQWeyl α K hα hK u = grossSourceQInput true α K hα hK u := rfl
lemma dressedFiniteQWeyl_value (α K R : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (u : FreeFormDomain) :
    freeFormDomainInclusion (dressedFiniteQWeyl α K R hα hK u) =
      grossWeylCoefficient (grossFiniteDressingCoefficient α K R hα hK) (freeFormDomainInclusion u) :=
  grossFormWeylMap_value _ _ _ u
lemma dressedInfiniteQWeyl_value (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (u : FreeFormDomain) :
    freeFormDomainInclusion (dressedInfiniteQWeyl α K hα hK u) =
      grossWeylCoefficient (grossDressingCoefficient α K hα hK) (freeFormDomainInclusion u) :=
  grossFormWeylMap_value _ _ _ u
lemma dressedFiniteQWeyl_on_H0 (α K R : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (w : freeHamiltonian.domain) :
    dressedFiniteQWeyl α K R hα hK (constructionH0ToQ w) =
      constructionH0ToQ (conjugationFiniteWeylInput α K R hα hK w) := by
  apply grossFormDomainInclusion_injective
  rw [dressedFiniteQWeyl_value,constructionH0ToQ_value,constructionH0ToQ_value]
  rfl
lemma dressedQWeyl_real_tendsto (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (u : FreeFormDomain) :
    Tendsto (fun R : ℝ => dressedFiniteQWeyl α K R hα hK u) atTop (𝓝 (dressedInfiniteQWeyl α K hα hK u)) :=
  tendsto_iff_norm_sub_tendsto_zero.mpr (grossSource_strong_Q true α K hα hK u)

/- Source argument component Shift01. -/
lemma dressedForm_shift_bounds (q : BoundedForm FreeFormDomain) (C : ℝ) (hC : 0 ≤ C)
    (he : ∀ u : FreeFormDomain, ‖q u u-uniformBaseForm u u‖ ≤
      (1/2:ℝ)*uniformFreeEnergy u+C*‖freeFormDomainInclusion u‖^2) (u : FreeFormDomain) :
    (1/2:ℝ)*‖u‖^2 ≤ (q u u).re+(C+1)*‖freeFormDomainInclusion u‖^2 ∧
    (q u u).re+(C+1)*‖freeFormDomainInclusion u‖^2 ≤ (5/2+2*C)*‖u‖^2 := by
  have h := (Complex.abs_re_le_norm (q u u-uniformBaseForm u u)).trans (he u)
  rw [Complex.sub_re,uniformBaseForm_energy] at h
  have hlo := neg_le_of_abs_le h
  have hup := le_of_abs_le h
  have hn := uniformFreeEnergy_norm u
  have hE := uniformFreeEnergy_nonneg u
  have hp := mul_nonneg hC hE
  have hj := mul_nonneg hC (sq_nonneg ‖freeFormDomainInclusion u‖)
  constructor <;> nlinarith

/- Source argument component Closed01. -/
def dressedClosedFormData (q : BoundedForm FreeFormDomain) (C : ℝ) (hC : 0 ≤ C)
    (hh : ∀ u w : FreeFormDomain, q u w = star (q w u))
    (he : ∀ u : FreeFormDomain, ‖q u u-uniformBaseForm u u‖ ≤
      (1/2:ℝ)*uniformFreeEnergy u+C*‖freeFormDomainInclusion u‖^2) :
    GW.Operators.CoerciveFormData FreeFormDomain Physical where
  embedding := freeFormDomainInclusion
  embedding_injective := freeFormWeightedGraph.embedding_injective.comp
    (GW.Spaces.weightedDomainIsometry freeFormWeightedGraph).injective
  embedding_dense := freeFormDomainInclusion_dense
  form := GW.Operators.boundedFormAlgebraic q
  hermitian := hh
  continuous_form := (q.continuous.comp continuous_fst).clm_apply continuous_snd
  shift := C+1
  lower := 1/2
  upper := 5/2+2*C
  lower_pos := by norm_num
  lower_le_upper := by linarith
  lower_bound := fun u => (dressedForm_shift_bounds q C hC he u).1
  upper_bound := fun u => (dressedForm_shift_bounds q C hC he u).2

lemma dressedClosedFormData_domain (q : BoundedForm FreeFormDomain) (C : ℝ) (hC : 0 ≤ C)
    (hh : ∀ u w : FreeFormDomain, q u w = star (q w u))
    (he : ∀ u : FreeFormDomain, ‖q u u-uniformBaseForm u u‖ ≤
      (1/2:ℝ)*uniformFreeEnergy u+C*‖freeFormDomainInclusion u‖^2) :
    Set.range (GW.Operators.completedEnergyEmbedding (dressedClosedFormData q C hC hh he)) =
      (freeFormOperator.domain : Set Physical) := by
  rw [GW.Operators.completedEnergyEmbedding_range]
  exact freeFormDomainInclusion_range

lemma dressedClosedFormData_complete (q : BoundedForm FreeFormDomain) (C : ℝ) (hC : 0 ≤ C)
    (hh : ∀ u w : FreeFormDomain, q u w = star (q w u))
    (he : ∀ u : FreeFormDomain, ‖q u u-uniformBaseForm u u‖ ≤
      (1/2:ℝ)*uniformFreeEnergy u+C*‖freeFormDomainInclusion u‖^2) :
    CompleteSpace (GW.Operators.EnergySpace (dressedClosedFormData q C hC hh he)) := inferInstance

/- Source argument component Data01. -/
lemma dressedFiniteForm_error (α K R : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (hKS : standardGrossCutoff α ≤ K) (u : FreeFormDomain) :
    ‖dressedFiniteForm α K R hα hK u u-uniformBaseForm u u‖ ≤
      (1/2:ℝ)*uniformFreeEnergy u+dressedFormComparisonConstant α K hα hK*‖freeFormDomainInclusion u‖^2 :=
  dressedExplicitForm_source_error α K hα hK hKS (derivativeFiniteCoefficient α K R hα hK)
    (conjugationCounterterm α K R) (dressed_finite_coefficient_mass α K R hα hK)
    (dressedFiniteCounterterm_bound α K R hα hK) u
lemma dressedInfiniteForm_error (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (hKS : standardGrossCutoff α ≤ K) (u : FreeFormDomain) :
    ‖dressedInfiniteForm α K hα hK u u-uniformBaseForm u u‖ ≤
      (1/2:ℝ)*uniformFreeEnergy u+dressedFormComparisonConstant α K hα hK*‖freeFormDomainInclusion u‖^2 :=
  dressedExplicitForm_source_error α K hα hK hKS (derivativeCoefficient α K hα hK)
    (dressedInfiniteCounterterm α K) (dressed_infinite_coefficient_mass α K hα hK).le
    (dressedInfiniteCounterterm_bound α K hα hK) u

def dressedFiniteClosedData (α K R : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (hKS : standardGrossCutoff α ≤ K) :
    GW.Operators.CoerciveFormData FreeFormDomain Physical :=
  dressedClosedFormData (dressedFiniteForm α K R hα hK) (dressedFormComparisonConstant α K hα hK)
    (dressedFormComparisonConstant_nonneg α K hα hK)
    (dressedExplicitForm_hermitian (cutoffL2 α K hα hK) (derivativeFiniteCoefficient α K R hα hK) (conjugationCounterterm α K R))
    (dressedFiniteForm_error α K R hα hK hKS)
def dressedInfiniteClosedData (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (hKS : standardGrossCutoff α ≤ K) :
    GW.Operators.CoerciveFormData FreeFormDomain Physical :=
  dressedClosedFormData (dressedInfiniteForm α K hα hK) (dressedFormComparisonConstant α K hα hK)
    (dressedFormComparisonConstant_nonneg α K hα hK)
    (dressedExplicitForm_hermitian (cutoffL2 α K hα hK) (derivativeCoefficient α K hα hK) (dressedInfiniteCounterterm α K))
    (dressedInfiniteForm_error α K hα hK hKS)

lemma dressedForm_diagonal_comparison (q : BoundedForm FreeFormDomain) (C : ℝ)
    (he : ∀ u : FreeFormDomain, ‖q u u-uniformBaseForm u u‖ ≤
      (1/2:ℝ)*uniformFreeEnergy u+C*‖freeFormDomainInclusion u‖^2) (u : FreeFormDomain) :
    (1/2:ℝ)*uniformFreeEnergy u-C*‖freeFormDomainInclusion u‖^2 ≤ (q u u).re ∧
    (q u u).re ≤ (3/2:ℝ)*uniformFreeEnergy u+C*‖freeFormDomainInclusion u‖^2 := by
  have h := (Complex.abs_re_le_norm (q u u-uniformBaseForm u u)).trans (he u)
  rw [Complex.sub_re,uniformBaseForm_energy] at h
  have hlo := neg_le_of_abs_le h
  have hup := le_of_abs_le h
  constructor <;> linarith

/- Source argument component Action01. -/
lemma dressedQRoot_on_H0 (w : freeHamiltonian.domain) :
    grossFormRootMap (constructionH0ToQ w) = commutatorGraphRootMap (conjugationSourceGraph w) :=
  Subtype.ext rfl
lemma dressedQMomentum_on_H0 (j : Fin 3) (w : freeHamiltonian.domain) :
    grossFormMomentumMap j (constructionH0ToQ w) =
      electronMomentumCoordinate j (commutatorMomentumInput (conjugationSourceGraph w) j) := by
  change electronMomentumCoordinate j (grossFormMomentumInput j (constructionH0ToQ w)) = _
  exact congrArg (fun x : (electronMomentumCoordinate j).domain => electronMomentumCoordinate j x) (Subtype.ext rfl)
lemma dressedQAnnihilator_on_H0 (f : OneBoson) (w : freeHamiltonian.domain) :
    dressedQAnnihilator f (constructionH0ToQ w) =
      commutatorPhaseAnnihilatorMap f (commutatorGraphRootMap (conjugationSourceGraph w)) := by
  change commutatorPhaseAnnihilatorMap f (grossFormRootMap (constructionH0ToQ w)) = _
  rw [dressedQRoot_on_H0]

lemma dressedQ_creator_pairing (f : OneBoson) (j : Fin 3) (v : FreeFormDomain) (w : freeHamiltonian.domain) :
    ⟪dressedQAnnihilator f v,grossFormMomentumMap j (constructionH0ToQ w)⟫_ℂ =
      ⟪freeFormDomainInclusion v,commutatorPhaseCreatorMap f
        (commutatorGraphMomentumRootMap j (conjugationSourceGraph w))⟫_ℂ := by
  rw [dressedQMomentum_on_H0]
  have hg := commutatorPhaseCreatorMap_graph f (commutatorGraphMomentumRootMap j (conjugationSourceGraph w))
  rw [commutatorGraphMomentumRootMap_value] at hg
  exact uvFormalAdjoint_graph_pairing _ _ (uvCreatorAnnihilator_formal (phaseMultiplicationKernel f)).symm
    _ _ _ _ (dressedQAnnihilator_graph f v) hg

lemma dressedQ_derivative_pairing (f : OneBoson) (j : Fin 3) (v : FreeFormDomain) (w : freeHamiltonian.domain)
    (pa : Physical)
    (hpa : (commutatorPhaseAnnihilatorMap f (commutatorGraphRootMap (conjugationSourceGraph w)),pa) ∈
      (electronMomentumCoordinate j).graph) :
    ⟪grossFormMomentumMap j v,dressedQAnnihilator f (constructionH0ToQ w)⟫_ℂ =
      ⟪freeFormDomainInclusion v,pa⟫_ℂ := by
  rw [dressedQAnnihilator_on_H0]
  exact uvFormalAdjoint_graph_pairing _ _ (dressed_momentum_symmetric j) _ _ _ _
    (grossFormMomentumMap_graph j v) hpa

lemma dressedQ_square_pairing (f : OneBoson) (v : FreeFormDomain) (w : freeHamiltonian.domain) :
    ⟪uvFieldLinear f v,uvFieldLinear f (constructionH0ToQ w)⟫_ℂ =
      ⟪freeFormDomainInclusion v,conjugationSquareMap f w⟫_ℂ :=
  uvFormalAdjoint_graph_pairing _ _ (generalizedField_symmetric (phaseMultiplicationKernel f)) _ _ _ _
    (uvFieldLinear_graph f v) (conjugationSquareMap_graph f w)

lemma dressedExplicitForm_on_H0 (g : OneBoson) (fs : Fin 3 → OneBoson) (C : ℝ)
    (v : FreeFormDomain) (w : freeHamiltonian.domain) (pa : Fin 3 → Physical)
    (hpa : ∀ j, (commutatorPhaseAnnihilatorMap (fs j) (commutatorGraphRootMap (conjugationSourceGraph w)),pa j) ∈
      (electronMomentumCoordinate j).graph) :
    dressedExplicitForm g fs C v (constructionH0ToQ w) =
      ⟪freeFormDomainInclusion v,freeHamiltonian w+constructionFieldRestriction g w+
        (-((2:ℂ) • (∑ j : Fin 3,commutatorPhaseCreatorMap (fs j)
            (commutatorGraphMomentumRootMap j (conjugationSourceGraph w))))-
          (2:ℂ) • (∑ j : Fin 3,pa j)+
          (∑ j : Fin 3,conjugationSquareMap (fs j) w)+(C:ℂ) • w.val)⟫_ℂ := by
  rw [dressedExplicitForm_apply,constructionBase_on_H0,constructionH0ToQ_value]
  have hcross : (∑ j : Fin 3,(⟪dressedQAnnihilator (fs j) v,grossFormMomentumMap j (constructionH0ToQ w)⟫_ℂ+
      ⟪grossFormMomentumMap j v,dressedQAnnihilator (fs j) (constructionH0ToQ w)⟫_ℂ)) =
      ∑ j : Fin 3,(⟪freeFormDomainInclusion v,commutatorPhaseCreatorMap (fs j)
        (commutatorGraphMomentumRootMap j (conjugationSourceGraph w))⟫_ℂ+⟪freeFormDomainInclusion v,pa j⟫_ℂ) :=
    Finset.sum_congr rfl (fun j _ => congrArg₂ (fun x y : ℂ => x+y)
      (dressedQ_creator_pairing (fs j) j v w) (dressedQ_derivative_pairing (fs j) j v w (pa j) (hpa j)))
  have hsquare := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun j _ => dressedQ_square_pairing (fs j) v w)
  rw [hcross,hsquare]
  change _ = ⟪freeFormDomainInclusion v,freeHamiltonian w+uvFieldLinear g (constructionH0ToQ w)+_⟫_ℂ
  simp only [inner_add_right,inner_sub_right,inner_neg_right,inner_smul_right,inner_sum,Finset.sum_add_distrib]
  ring

/- Source argument component FiniteOperator03. -/
lemma dressedFiniteForm_on_H0 (α K R : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (v : FreeFormDomain) (w : freeHamiltonian.domain) :
    dressedFiniteForm α K R hα hK v (constructionH0ToQ w) =
      ⟪freeFormDomainInclusion v,conjugationDressedHamiltonian α K R hα hK w⟫_ℂ := by
  let fs := derivativeFiniteCoefficient α K R hα hK
  let U := conjugationSourceGraph w
  let pa : Fin 3 → Physical := fun j => commutatorAnnihilatorRightMap (fs j) j
    (derivativeFiniteCoefficient_second_memLp α K R hα hK j) U
  let c : Physical := ∑ j : Fin 3,commutatorPhaseCreatorMap (fs j) (commutatorGraphMomentumRootMap j U)
  let a : Physical := derivativeFiniteDot α K R hα hK U
  let s : Physical := ∑ j : Fin 3,conjugationSquareMap (fs j) w
  have hg (j : Fin 3) : (commutatorPhaseAnnihilatorMap (fs j) (commutatorGraphRootMap U),pa j) ∈
      (electronMomentumCoordinate j).graph := commutatorAnnihilator_graph_all (fs j) j (derivativeFiniteCoefficient_second_memLp α K R hα hK j) U
  have hq : dressedFiniteForm α K R hα hK v (constructionH0ToQ w) =
      ⟪freeFormDomainInclusion v,freeHamiltonian w+constructionFieldRestriction (cutoffL2 α K hα hK) w+
        (-((2:ℂ) • c)-(2:ℂ) • a+s+(conjugationCounterterm α K R : ℂ) • w.val)⟫_ℂ :=
    dressedExplicitForm_on_H0 (cutoffL2 α K hα hK) fs (conjugationCounterterm α K R) v w pa hg
  have hv : conjugationFiniteRemainder α K R hα hK w =
      -((2:ℂ) • c)-(2:ℂ) • a+s+(conjugationCounterterm α K R : ℂ) • w.val := by
    have h : conjugationFiniteRemainder α K R hα hK w =
        -((2:ℕ) • c)-(2:ℕ) • a+s+(conjugationCounterterm α K R : ℂ) • w.val :=
      conjugationRemainder_value (grossTruncateCoefficient (grossDressingCoefficient α K hα hK) R)
        (grossForm_finite_first_memLp (grossDressingCoefficient α K hα hK) R)
        (fun i j => grossForm_finite_second_memLp (grossDressingCoefficient α K hα hK) R j i)
        (conjugationCounterterm α K R) w
    have hc : (2:ℂ) • c = (2:ℕ) • c := Nat.cast_smul_eq_nsmul ℂ 2 c
    have ha : (2:ℂ) • a = (2:ℕ) • a := Nat.cast_smul_eq_nsmul ℂ 2 a
    rw [← hc,← ha] at h
    exact h
  rw [← hv] at hq
  change dressedFiniteForm α K R hα hK v (constructionH0ToQ w) =
    ⟪freeFormDomainInclusion v,freeHamiltonian w+
      (constructionFieldRestriction (cutoffL2 α K hα hK) w+conjugationFiniteRemainder α K R hα hK w)⟫_ℂ
  exact hq.trans (congrArg (fun x : Physical => ⟪freeFormDomainInclusion v,x⟫_ℂ) (add_assoc _ _ _))

lemma dressedFiniteForm_representative (α K R : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (hKS : standardGrossCutoff α ≤ K) (hR : K ≤ R) :
    conjugationDressedHamiltonian α K R hα hK = GW.Operators.formOperator (dressedFiniteClosedData α K R hα hK hKS) := by
  apply GW.Operators.formOperator_unique (dressedFiniteClosedData α K R hα hK hKS)
    (conjugationDressedHamiltonian α K R hα hK) (dressedFiniteHamiltonian_selfadjoint α K R hα hK hKS hR)
  intro x
  let w : freeHamiltonian.domain := ⟨x.val,x.property⟩
  refine ⟨constructionH0ToQ w,constructionH0ToQ_value w,?_⟩
  intro v
  change dressedFiniteForm α K R hα hK v (constructionH0ToQ w) =
    ⟪freeFormDomainInclusion v,conjugationDressedHamiltonian α K R hα hK w⟫_ℂ
  exact dressedFiniteForm_on_H0 α K R hα hK v w

lemma dressedFiniteForm_domain (α K R : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (hKS : standardGrossCutoff α ≤ K) :
    Set.range (GW.Operators.completedEnergyEmbedding (dressedFiniteClosedData α K R hα hK hKS)) =
      (freeFormOperator.domain : Set Physical) :=
  by
    rw [GW.Operators.completedEnergyEmbedding_range]
    exact freeFormDomainInclusion_range

/- Source argument component Interacting02. -/
local instance : ContinuousAdd (BoundedForm FreeFormDomain) :=
  (ContinuousLinearMap.isTopologicalAddGroup (E := FreeFormDomain)
    (F := FreeFormDomain →L[ℂ] ℂ) (σ := starRingEnd ℂ)).toContinuousAdd

def dressedFreeBoundedForm : BoundedForm FreeFormDomain :=
  dressedQPair (ContinuousLinearMap.id ℂ FreeFormDomain) (ContinuousLinearMap.id ℂ FreeFormDomain)-
    dressedQPair freeFormDomainInclusion freeFormDomainInclusion
lemma dressedFreeBoundedForm_apply (u w : FreeFormDomain) :
    dressedFreeBoundedForm u w = uniformBaseForm u w := rfl

def dressedInteractingFiniteForm (α R : ℝ) (hα : 0 ≤ α) (hR : 0 < R) : BoundedForm FreeFormDomain :=
  dressedFreeBoundedForm+uvCutoffBoundedForm α R hα hR
def dressedInteractingInfiniteForm (α : ℝ) (hα : 0 ≤ α) : BoundedForm FreeFormDomain :=
  dressedFreeBoundedForm+constructionLimitForm α hα
lemma dressedInteractingFiniteForm_apply (α R : ℝ) (hα : 0 ≤ α) (hR : 0 < R) (u w : FreeFormDomain) :
    dressedInteractingFiniteForm α R hα hR u w = uniformBaseForm u w+uvCutoffForm α R hα hR u w := rfl
lemma dressedInteractingInfiniteForm_apply (α : ℝ) (hα : 0 ≤ α) (u w : FreeFormDomain) :
    dressedInteractingInfiniteForm α hα u w = constructionTotalLimitForm α hα u w := rfl

lemma dressedInteractingFiniteForm_on_H0 (α R : ℝ) (hα : 0 ≤ α) (hR : 0 < R)
    (v : FreeFormDomain) (w : freeHamiltonian.domain) :
    dressedInteractingFiniteForm α R hα hR v (constructionH0ToQ w) =
      ⟪freeFormDomainInclusion v,constructionCutoffHamiltonian α R hα hR w⟫_ℂ := by
  change uniformBaseForm v (constructionH0ToQ w)+uvFieldForm (cutoffL2 α R hα hR) v (constructionH0ToQ w) = _
  rw [constructionBase_on_H0,constructionField_on_H0]
  exact (inner_add_right _ _ _).symm

lemma dressedInteractingForms_real_tendsto (α : ℝ) (hα : 0 ≤ α) :
    Tendsto (fun R : ℝ => dressedInteractingFiniteForm α (constructionRealCutoff R).val hα (constructionRealCutoff R).property)
      atTop (𝓝 (dressedInteractingInfiniteForm α hα)) := by
  have hb : Tendsto (fun _ : ℝ => dressedFreeBoundedForm) atTop (𝓝 dressedFreeBoundedForm) := tendsto_const_nhds
  exact hb.add (constructionReal_boundedForm_tendsto α hα)
lemma dressedRealCutoff_value_tendsto :
    Tendsto (fun R : ℝ => (constructionRealCutoff R).val) atTop atTop := by
  have he : (fun R : ℝ => (constructionRealCutoff R).val) =ᶠ[atTop] (fun R => R) :=
    constructionRealCutoff_eventually
  exact tendsto_id.congr' he.symm

lemma dressedFiniteForm_transport_on_H0 (α K R : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (hR : 0 < R) (hKR : K ≤ R) (u : FreeFormDomain) (w : freeHamiltonian.domain) :
    dressedFiniteForm α K R hα hK u (constructionH0ToQ w) =
      dressedInteractingFiniteForm α R hα hR (dressedFiniteQWeyl α K R hα hK u)
        (dressedFiniteQWeyl α K R hα hK (constructionH0ToQ w)) := by
  rw [dressedFiniteQWeyl_on_H0,dressedInteractingFiniteForm_on_H0,dressedFiniteQWeyl_value,
    LinearIsometryEquiv.inner_map_eq_flip,conjugationFinite_action α K R hα hK hR hKR]
  exact dressedFiniteForm_on_H0 α K R hα hK u w

lemma dressedFiniteForm_transport (α K R : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (hR : 0 < R) (hKR : K ≤ R) (u w : FreeFormDomain) :
    dressedFiniteForm α K R hα hK u w =
      dressedInteractingFiniteForm α R hα hR (dressedFiniteQWeyl α K R hα hK u)
        (dressedFiniteQWeyl α K R hα hK w) := by
  have he := dressedH0ToQ_dense.equalizer (dressedFiniteForm α K R hα hK u).continuous
    ((dressedInteractingFiniteForm α R hα hR (dressedFiniteQWeyl α K R hα hK u)).continuous.comp
      (dressedFiniteQWeyl α K R hα hK).continuous) (by
        funext x
        exact dressedFiniteForm_transport_on_H0 α K R hα hK hR hKR u x)
  exact congr_fun he w

/- Source argument component Transport02. -/
lemma dressedForm_norm_limit {Z : Type*} [NormedAddCommGroup Z]
    (bs : ℝ → Z) (b : Z) (h : Tendsto bs atTop (𝓝 b)) :
    Tendsto (fun R => ‖bs R-b‖) atTop (𝓝 0) :=
  tendsto_iff_norm_sub_tendsto_zero.mp h

lemma dressedInfiniteForm_transport (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (u w : FreeFormDomain) :
    dressedInfiniteForm α K hα hK u w =
      constructionTotalLimitForm α hα (grossSourceQInput true α K hα hK u)
        (grossSourceQInput true α K hα hK w) := by
  let rs : ℝ → ℝ := fun R => (constructionRealCutoff R).val
  let bs : ℝ → BoundedForm FreeFormDomain := fun R => dressedFiniteForm α K (rs R) hα hK
  let cs : ℝ → BoundedForm FreeFormDomain := fun R => dressedInteractingFiniteForm α (rs R) hα
    (constructionRealCutoff R).property
  have hb : Tendsto bs atTop (𝓝 (dressedInfiniteForm α K hα hK)) :=
    (dressedForms_real_tendsto α K hα hK).comp dressedRealCutoff_value_tendsto
  have hc : Tendsto cs atTop (𝓝 (dressedInteractingInfiniteForm α hα)) :=
    dressedInteractingForms_real_tendsto α hα
  have hu : Tendsto (fun R => dressedFiniteQWeyl α K (rs R) hα hK u) atTop
      (𝓝 (dressedInfiniteQWeyl α K hα hK u)) :=
    (dressedQWeyl_real_tendsto α K hα hK u).comp dressedRealCutoff_value_tendsto
  have hw : Tendsto (fun R => dressedFiniteQWeyl α K (rs R) hα hK w) atTop
      (𝓝 (dressedInfiniteQWeyl α K hα hK w)) :=
    (dressedQWeyl_real_tendsto α K hα hK w).comp dressedRealCutoff_value_tendsto
  have hl : Tendsto (fun R => bs R u w) atTop (𝓝 (dressedInfiniteForm α K hα hK u w)) :=
    mixed_form_tendsto (dressedForm_norm_limit bs _ hb) tendsto_const_nhds tendsto_const_nhds
  have hr : Tendsto (fun R => cs R (dressedFiniteQWeyl α K (rs R) hα hK u)
      (dressedFiniteQWeyl α K (rs R) hα hK w)) atTop
      (𝓝 (dressedInteractingInfiniteForm α hα (dressedInfiniteQWeyl α K hα hK u)
        (dressedInfiniteQWeyl α K hα hK w))) :=
    mixed_form_tendsto (dressedForm_norm_limit cs _ hc) hu hw
  have he : (fun R => bs R u w) =ᶠ[atTop]
      (fun R => cs R (dressedFiniteQWeyl α K (rs R) hα hK u)
        (dressedFiniteQWeyl α K (rs R) hα hK w)) := by
    filter_upwards [eventually_ge_atTop K] with R hR
    have hKR : K ≤ rs R := hR.trans (le_max_right 1 R)
    exact dressedFiniteForm_transport α K (rs R) hα hK (constructionRealCutoff R).property hKR u w
  exact tendsto_nhds_unique hl (hr.congr' he.symm)

/- Source argument component InfiniteOperator02. -/
lemma dressedInfiniteForm_on_H0 (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (v : FreeFormDomain) (w : freeHamiltonian.domain) :
    dressedInfiniteForm α K hα hK v (constructionH0ToQ w) =
      ⟪freeFormDomainInclusion v,dressedInfiniteHamiltonian α K hα hK w⟫_ℂ := by
  let fs := derivativeCoefficient α K hα hK
  let U := conjugationSourceGraph w
  let pa : Fin 3 → Physical := fun j => commutatorPhaseAnnihilatorMap (fs j)
    (commutatorGraphMomentumRootMap j U)+derivativeSingularMap α K hα hK j U
  let c : Physical := ∑ j : Fin 3,commutatorPhaseCreatorMap (fs j) (commutatorGraphMomentumRootMap j U)
  let a : Physical := derivativeInfiniteDot α K hα hK U
  let s : Physical := ∑ j : Fin 3,conjugationSquareMap (fs j) w
  have hg (j : Fin 3) : (commutatorPhaseAnnihilatorMap (fs j) (commutatorGraphRootMap U),pa j) ∈
      (electronMomentumCoordinate j).graph := derivative_infinite_component_graph α K hα hK j U
  have hq : dressedInfiniteForm α K hα hK v (constructionH0ToQ w) =
      ⟪freeFormDomainInclusion v,freeHamiltonian w+constructionFieldRestriction (cutoffL2 α K hα hK) w+
        (-((2:ℂ) • c)-(2:ℂ) • a+s+(dressedInfiniteCounterterm α K : ℂ) • w.val)⟫_ℂ :=
    dressedExplicitForm_on_H0 (cutoffL2 α K hα hK) fs (dressedInfiniteCounterterm α K) v w pa hg
  have hv : dressedInfiniteRemainder α K hα hK w =
      -((2:ℂ) • c)-(2:ℂ) • a+s+(dressedInfiniteCounterterm α K : ℂ) • w.val := by
    have h := dressedInfiniteRemainder_value α K hα hK w
    have hc : (2:ℂ) • c = (2:ℕ) • c := Nat.cast_smul_eq_nsmul ℂ 2 c
    have ha : (2:ℂ) • a = (2:ℕ) • a := Nat.cast_smul_eq_nsmul ℂ 2 a
    rw [← hc,← ha] at h
    exact h
  rw [← hv] at hq
  change dressedInfiniteForm α K hα hK v (constructionH0ToQ w) =
    ⟪freeFormDomainInclusion v,freeHamiltonian w+
      (constructionFieldRestriction (cutoffL2 α K hα hK) w+dressedInfiniteRemainder α K hα hK w)⟫_ℂ
  exact hq.trans (congrArg (fun x : Physical => ⟪freeFormDomainInclusion v,x⟫_ℂ) (add_assoc _ _ _))

lemma dressedInfiniteForm_representative (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (hKS : standardGrossCutoff α ≤ K) :
    dressedInfiniteHamiltonian α K hα hK = GW.Operators.formOperator (dressedInfiniteClosedData α K hα hK hKS) := by
  apply GW.Operators.formOperator_unique (dressedInfiniteClosedData α K hα hK hKS)
    (dressedInfiniteHamiltonian α K hα hK) (dressedInfiniteHamiltonian_selfadjoint α K hα hK hKS)
  intro x
  let w : freeHamiltonian.domain := ⟨x.val,x.property⟩
  refine ⟨constructionH0ToQ w,constructionH0ToQ_value w,?_⟩
  intro v
  change dressedInfiniteForm α K hα hK v (constructionH0ToQ w) =
    ⟪freeFormDomainInclusion v,dressedInfiniteHamiltonian α K hα hK w⟫_ℂ
  exact dressedInfiniteForm_on_H0 α K hα hK v w

lemma dressedInfiniteForm_domain (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (hKS : standardGrossCutoff α ≤ K) :
    Set.range (GW.Operators.completedEnergyEmbedding (dressedInfiniteClosedData α K hα hK hKS)) =
      (freeFormOperator.domain : Set Physical) :=
  by
    rw [GW.Operators.completedEnergyEmbedding_range]
    exact freeFormDomainInclusion_range

/- Source argument component Public01. -/
lemma main_dressed_form (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (hKS : standardGrossCutoff α ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ R : ℝ, K ≤ R →
        conjugationDressedHamiltonian α K R hα hK = GW.Operators.formOperator (dressedFiniteClosedData α K R hα hK hKS) ∧
        Set.range (GW.Operators.completedEnergyEmbedding (dressedFiniteClosedData α K R hα hK hKS)) =
          (freeFormOperator.domain : Set Physical) ∧
        ∀ u : FreeFormDomain,
          (1/2:ℝ)*uniformFreeEnergy u-C*‖freeFormDomainInclusion u‖^2 ≤ (dressedFiniteForm α K R hα hK u u).re ∧
          (dressedFiniteForm α K R hα hK u u).re ≤ (3/2:ℝ)*uniformFreeEnergy u+C*‖freeFormDomainInclusion u‖^2) ∧
      dressedInfiniteHamiltonian α K hα hK = GW.Operators.formOperator (dressedInfiniteClosedData α K hα hK hKS) ∧
      Set.range (GW.Operators.completedEnergyEmbedding (dressedInfiniteClosedData α K hα hK hKS)) =
        (freeFormOperator.domain : Set Physical) ∧
      (∀ u : FreeFormDomain,
        (1/2:ℝ)*uniformFreeEnergy u-C*‖freeFormDomainInclusion u‖^2 ≤ (dressedInfiniteForm α K hα hK u u).re ∧
        (dressedInfiniteForm α K hα hK u u).re ≤ (3/2:ℝ)*uniformFreeEnergy u+C*‖freeFormDomainInclusion u‖^2) ∧
      ∀ u w : FreeFormDomain, dressedInfiniteForm α K hα hK u w =
        constructionTotalLimitForm α hα (grossSourceQInput true α K hα hK u) (grossSourceQInput true α K hα hK w) := by
  refine ⟨dressedFormComparisonConstant α K hα hK,dressedFormComparisonConstant_nonneg α K hα hK,?_,
    dressedInfiniteForm_representative α K hα hK hKS,dressedInfiniteForm_domain α K hα hK hKS,?_,?_⟩
  · intro R hR
    refine ⟨dressedFiniteForm_representative α K R hα hK hKS hR,dressedFiniteForm_domain α K R hα hK hKS,?_⟩
    exact dressedForm_diagonal_comparison _ _ (dressedFiniteForm_error α K R hα hK hKS)
  · exact dressedForm_diagonal_comparison _ _ (dressedInfiniteForm_error α K hα hK hKS)
  · exact dressedInfiniteForm_transport α K hα hK

end GW.Gross
