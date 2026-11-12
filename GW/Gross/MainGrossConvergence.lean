module
public import GW.Gross.MainTails
public import GW.Fock.FockWeylDerivative
public import GW.Operators.BasicFractionalFree
public import GW.Analysis.DenseStrongLimit
@[expose] public section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal
namespace GW.Gross
open GW.Model GW.Fock GW.Analysis


def grossCoefficientMajorant (α K : ℝ) (k : GW.Space) : ℝ :=
  (highRegion K).indicator (fun k => (v α k)^2/(1+‖k‖^2)) k

lemma grossCoefficientMajorant_integrable (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) :
    Integrable (grossCoefficientMajorant α K) volume := by
  have hi := (nonnegative_realIntegral_of_lintegral
    (((v_measurable α).pow_const 2).div (measurable_const.add (measurable_norm.pow_const 2)))
    (fun k => div_nonneg (sq_nonneg _) (add_nonneg zero_le_one (sq_nonneg _)))
    (coefficientETailENN_finite α K hα hK)).1
  exact (integrable_indicator_iff (highRegion_measurable K)).mpr hi

lemma grossCoefficientMajorant_integral (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) :
    (∫ k, grossCoefficientMajorant α K k ∂volume) = coefficientETail α K := by
  change (∫ k, (highRegion K).indicator (fun k => (v α k)^2/(1+‖k‖^2)) k ∂volume) = _
  rw [integral_indicator (highRegion_measurable K)]
  exact (coefficientETail_eq_integral α K hα hK).symm

lemma grossCoefficient_norm_sq_bound (α K : ℝ) (k : GW.Space) :
    ‖(b α K k : ℂ)‖^2 ≤ grossCoefficientMajorant α K k := by
  rw [Complex.norm_real,Real.norm_eq_abs,sq_abs]
  by_cases hk : K < ‖k‖
  · rw [b,if_pos hk,grossCoefficientMajorant,Set.indicator_of_mem hk,div_pow,neg_sq]
    apply div_le_div_of_nonneg_left (sq_nonneg _)
    · positivity
    · nlinarith [sq_nonneg ‖k‖]
  · rw [b,if_neg hk,grossCoefficientMajorant,Set.indicator_of_notMem hk]
    norm_num

lemma grossCoefficient_memLp (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) :
    MemLp (fun k : GW.Space => (b α K k : ℂ)) 2 (volume : Measure GW.Space) := by
  have hm : Measurable (fun k : GW.Space => (b α K k : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp (b_measurable α K)
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  apply (grossCoefficientMajorant_integrable α K hα hK).mono'
    (hm.norm.pow_const 2).aestronglyMeasurable
  exact Eventually.of_forall (fun k => by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact grossCoefficient_norm_sq_bound α K k)

def grossDressingCoefficient (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) : OneBoson :=
  (grossCoefficient_memLp α K hα hK).toLp (fun k => (b α K k : ℂ))

lemma grossDressingCoefficient_ae (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) :
    grossDressingCoefficient α K hα hK =ᵐ[volume] fun k => (b α K k : ℂ) := MemLp.coeFn_toLp _

lemma grossDressingCoefficient_norm_sq (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) :
    ‖grossDressingCoefficient α K hα hK‖^2 ≤ coefficientETail α K := by
  rw [GW.Analysis.l2_norm_sq (𝕜 := ℂ)]
  calc
    _ ≤ ∫ k, grossCoefficientMajorant α K k ∂volume := by
      apply integral_mono_ae ((Lp.memLp (grossDressingCoefficient α K hα hK)).integrable_norm_pow
        (p := 2) (by norm_num)) (grossCoefficientMajorant_integrable α K hα hK)
      filter_upwards [grossDressingCoefficient_ae α K hα hK] with k hk
      rw [hk]
      exact grossCoefficient_norm_sq_bound α K k
    _ = _ := grossCoefficientMajorant_integral α K hα hK



def grossTruncateCoefficient (f : OneBoson) (Λ : ℝ) : OneBoson :=
  ((Lp.memLp f).indicator (lowRegion_measurable Λ).nullMeasurableSet).toLp ((lowRegion Λ).indicator f)

lemma grossTruncateCoefficient_ae (f : OneBoson) (Λ : ℝ) :
    grossTruncateCoefficient f Λ =ᵐ[volume] (lowRegion Λ).indicator f := MemLp.coeFn_toLp _

lemma grossTruncateCoefficient_inner_im_zero (f : OneBoson) (Λ : ℝ) :
    (⟪grossTruncateCoefficient f Λ,f⟫_ℂ).im = 0 := by
  rw [L2.inner_def]
  have hi := integral_im (L2.integrable_inner (𝕜 := ℂ) (grossTruncateCoefficient f Λ) f)
  change (∫ k, (⟪grossTruncateCoefficient f Λ k,f k⟫_ℂ).im ∂volume) =
    (∫ k, ⟪grossTruncateCoefficient f Λ k,f k⟫_ℂ ∂volume).im at hi
  rw [← hi]
  apply integral_eq_zero_of_ae
  filter_upwards [grossTruncateCoefficient_ae f Λ] with k hk
  rw [hk]
  by_cases h : k ∈ lowRegion Λ
  · rw [Set.indicator_of_mem h]
    convert! inner_self_im (𝕜 := ℂ) (f k) using 1 <;> rfl
  · rw [Set.indicator_of_notMem h,inner_zero_left]
    rfl

lemma grossTruncate_phase_inner_im_zero (f : OneBoson) (Λ : ℝ) (x : GW.Space) :
    (⟪phaseAt (grossTruncateCoefficient f Λ) x,phaseAt f x⟫_ℂ).im = 0 := by
  rw [weylPhase_inner,grossTruncateCoefficient_inner_im_zero]

def grossFiniteDressingCoefficient (α K Λ : ℝ) (hα : 0 ≤ α) (hK : 0 < K) : OneBoson :=
  grossTruncateCoefficient (grossDressingCoefficient α K hα hK) Λ

lemma grossFiniteDressingCoefficient_ae (α K Λ : ℝ) (hα : 0 ≤ α) (hK : 0 < K) :
    grossFiniteDressingCoefficient α K Λ hα hK =ᵐ[volume]
      (lowRegion Λ).indicator (fun k => (b α K k : ℂ)) := by
  change grossTruncateCoefficient (grossDressingCoefficient α K hα hK) Λ =ᵐ[volume] _
  filter_upwards [grossTruncateCoefficient_ae (grossDressingCoefficient α K hα hK) Λ,
    grossDressingCoefficient_ae α K hα hK] with k ht hb
  rw [ht]
  by_cases h : k ∈ lowRegion Λ
  · rw [Set.indicator_of_mem h,Set.indicator_of_mem h,hb]
  · rw [Set.indicator_of_notMem h,Set.indicator_of_notMem h]

lemma grossFiniteDressingCoefficient_at_K (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) :
    grossFiniteDressingCoefficient α K K hα hK = 0 := by
  apply Lp.ext
  filter_upwards [grossFiniteDressingCoefficient_ae α K K hα hK,Lp.coeFn_zero ℂ 2 (volume : Measure GW.Space)] with k hf hz
  rw [hf,hz]
  by_cases h : k ∈ lowRegion K
  · rw [Set.indicator_of_mem h,b,ite_eq_right (not_lt.mpr h)]
    rfl
  · rw [Set.indicator_of_notMem h]
    rfl

lemma grossFiniteDressingCoefficient_tail (α K Λ : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (hKL : K ≤ Λ) :
    grossFiniteDressingCoefficient α K Λ hα hK-grossDressingCoefficient α K hα hK =
      -grossDressingCoefficient α Λ hα (hK.trans_le hKL) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (grossFiniteDressingCoefficient α K Λ hα hK) (grossDressingCoefficient α K hα hK),
    Lp.coeFn_neg (grossDressingCoefficient α Λ hα (hK.trans_le hKL)),
    grossFiniteDressingCoefficient_ae α K Λ hα hK,grossDressingCoefficient_ae α K hα hK,
    grossDressingCoefficient_ae α Λ hα (hK.trans_le hKL)] with k hd hn hf hK hΛ
  rw [hd,Pi.sub_apply,hn,Pi.neg_apply,hf,hK,hΛ]
  by_cases h : k ∈ lowRegion Λ
  · rw [Set.indicator_of_mem h,sub_self,b,ite_eq_right (not_lt.mpr h)]
    simp
  · have hΛ : Λ < ‖k‖ := lt_of_not_ge h
    have hK : K < ‖k‖ := lt_of_le_of_lt hKL hΛ
    rw [Set.indicator_of_notMem h,b,b,ite_eq_left hK,ite_eq_left hΛ,zero_sub]

lemma grossFiniteDressingCoefficient_error_sq (α K Λ : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (hKL : K ≤ Λ) :
    ‖grossFiniteDressingCoefficient α K Λ hα hK-grossDressingCoefficient α K hα hK‖^2 ≤ coefficientETail α Λ := by
  rw [grossFiniteDressingCoefficient_tail α K Λ hα hK hKL,norm_neg]
  exact grossDressingCoefficient_norm_sq α Λ hα (hK.trans_le hKL)

lemma grossFiniteDressingCoefficient_error_tendsto (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) :
    Tendsto (fun Λ : ℝ => ‖grossFiniteDressingCoefficient α K Λ hα hK-grossDressingCoefficient α K hα hK‖)
      atTop (𝓝 0) := by
  have hs : Tendsto (fun Λ : ℝ => ‖grossFiniteDressingCoefficient α K Λ hα hK-grossDressingCoefficient α K hα hK‖^2)
      atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ => sq_nonneg _)) _ (coefficientETail_tendsto α hα)
    filter_upwards [eventually_ge_atTop K] with Λ hΛ
    exact grossFiniteDressingCoefficient_error_sq α K Λ hα hK hΛ
  have hh := (Real.continuous_sqrt.tendsto 0).comp hs
  simpa only [Function.comp_def,Real.sqrt_zero,Real.sqrt_sq_eq_abs,abs_norm] using hh



def grossWeylCoefficient (f : OneBoson) : Physical ≃ₗᵢ[ℂ] Physical :=
  fiberWeylUnitary (phaseAt f) (phaseAt_continuous f).stronglyMeasurable

lemma grossWeylCoefficient_ae (f : OneBoson) (U : Physical) :
    grossWeylCoefficient f U =ᵐ[volume] fun x => weylUnitary (phaseAt f x) (U x) :=
  fiberWeylUnitary_ae (phaseAt f) (phaseAt_continuous f).stronglyMeasurable U

lemma grossWeylCoefficient_symm_apply (f : OneBoson) (U : Physical) :
    (grossWeylCoefficient f).symm U = grossWeylCoefficient (-f) U := by
  change (fiberWeylUnitary (phaseAt f) (phaseAt_continuous f).stronglyMeasurable).symm U = _
  rw [fiberWeylUnitary_symm_apply]
  apply Lp.ext
  filter_upwards [fiberWeylUnitary_ae (fun x => -phaseAt f x)
      (continuous_neg.comp_stronglyMeasurable (phaseAt_continuous f).stronglyMeasurable) U,
    grossWeylCoefficient_ae (-f) U] with x h₁ h₂
  rw [h₁,h₂]
  have he : phaseAt (-f) x = -phaseAt f x := (weylPhaseIsometry x).map_neg f
  rw [he]

lemma grossPhase_difference_norm (a b : OneBoson) (x : GW.Space) :
    ‖phaseAt a x-phaseAt b x‖ = ‖a-b‖ := by
  have he : phaseAt (a-b) x = phaseAt a x-phaseAt b x := (weylPhaseIsometry x).map_sub a b
  rw [← he,phaseAt_norm]

set_option backward.isDefEq.respectTransparency.types false in
lemma grossWeyl_difference_root (a b : OneBoson) (hab : (⟪a,b⟫_ℂ).im = 0) (U : FiberPhysicalRoot) :
    ‖grossWeylCoefficient a (fiberPhysicalRootInput U).val-
      grossWeylCoefficient b (fiberPhysicalRootInput U).val‖ ≤ 2*‖a-b‖*‖U‖ := by
  let G := fiberRootRepresentative U
  have hG := fiberRootRepresentative_ambient U
  have hh : ‖grossWeylCoefficient a (fiberPhysicalRootInput U).val-
      grossWeylCoefficient b (fiberPhysicalRootInput U).val‖ ≤ 2*‖a-b‖*‖G‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [grossWeylCoefficient_ae a (fiberPhysicalRootInput U).val,
      grossWeylCoefficient_ae b (fiberPhysicalRootInput U).val,
      Lp.coeFn_sub (grossWeylCoefficient a (fiberPhysicalRootInput U).val)
        (grossWeylCoefficient b (fiberPhysicalRootInput U).val),hG] with x ha hb hs hg
    rw [hs,Pi.sub_apply,ha,hb]
    have he : (fiberPhysicalRootInput U).val x = numberDomainEmbedding (1/2) (by norm_num) (G x) := hg.symm
    rw [he]
    have hi : (⟪phaseAt a x,phaseAt b x⟫_ℂ).im = 0 := by rw [weylPhase_inner,hab]
    have hp := weyl_difference_graph (phaseAt a x) (phaseAt b x) (G x)
    rw [hi,abs_zero,zero_mul,add_zero,grossPhase_difference_norm] at hp
    exact hp
  exact hh.trans_eq (congrArg (fun r : ℝ => 2*‖a-b‖*r)
    ((physicalNumberGraphBochnerUnitary (1/2) (by norm_num)).symm.norm_map U))

lemma grossWeyl_inverse_difference_root (a b : OneBoson) (hab : (⟪a,b⟫_ℂ).im = 0) (U : FiberPhysicalRoot) :
    ‖(grossWeylCoefficient a).symm (fiberPhysicalRootInput U).val-
      (grossWeylCoefficient b).symm (fiberPhysicalRootInput U).val‖ ≤ 2*‖a-b‖*‖U‖ := by
  rw [grossWeylCoefficient_symm_apply,grossWeylCoefficient_symm_apply]
  have hi : (⟪-a,-b⟫_ℂ).im = 0 := by rw [inner_neg_left,inner_neg_right,neg_neg,hab]
  have hh := grossWeyl_difference_root (-a) (-b) hi U
  have he : -a-(-b) = -(a-b) := by abel
  simpa only [he,norm_neg] using hh



def grossFreeHalfInverse : Physical →L[ℂ] Physical :=
  (physicalWeightEmbedding freeFormWeight freeFormWeight_measurable freeFormWeight_one).comp
    freeFourierRepresentation.toContinuousLinearEquiv.toContinuousLinearMap

def grossFreeHalfInverseInput (U : Physical) : freeFormOperator.domain :=
  ⟨grossFreeHalfInverse U,physicalWeightEmbedding_mem freeFormWeight freeFormWeight_measurable freeFormWeight_one
    (freeFourierRepresentation U)⟩

lemma grossFreeHalfInverse_action (U : Physical) :
    freeFormOperator (grossFreeHalfInverseInput U) = U := by
  apply freeFourierRepresentation.injective
  exact physicalWeightProduct_embedding freeFormWeight freeFormWeight_measurable freeFormWeight_one
    (freeFourierRepresentation U)

lemma grossFreeHalfInverse_on_domain (U : freeFormOperator.domain) :
    grossFreeHalfInverse (freeFormOperator U) = U.val :=
  physicalWeightEmbedding_product freeFormWeight freeFormWeight_measurable freeFormWeight_one U

lemma grossFreeHalfInverse_negative_symbol (n : ℕ) (q : GW.Space) :
    fractionalFreeWeight (-1) n q*freeFormWeight n q = 1 := by
  have hp : 0 < freeGraphWeight n q := zero_lt_one.trans_le (freeGraphWeight_one n q)
  rw [fractionalFreeWeight,freeFormWeight,Real.sqrt_eq_rpow]
  rw [show (-1:ℝ)/2=-(1/2:ℝ) by ring,Real.rpow_neg hp.le,
    inv_mul_cancel₀ (Real.rpow_pos_of_pos hp _).ne']

lemma grossFreeHalfInverse_negative_ae (U : Physical) (n : ℕ) :
    (fun q => (fractionalFreeWeight (-1) n q : ℂ) • freeFourierRepresentation U n q) =ᵐ[volume]
      freeFourierRepresentation (grossFreeHalfInverse U) n := by
  have hh := physicalSectorMultiplier_action freeFormWeight (grossFreeHalfInverseInput U) n
  change (fun q => (freeFormWeight n q : ℂ) • freeFourierRepresentation (grossFreeHalfInverse U) n q) =ᵐ[volume]
    freeFourierRepresentation (freeFormOperator (grossFreeHalfInverseInput U)) n at hh
  rw [grossFreeHalfInverse_action] at hh
  filter_upwards [hh] with q hq
  rw [← hq,smul_smul,← Complex.ofReal_mul,grossFreeHalfInverse_negative_symbol,Complex.ofReal_one,one_smul]

lemma grossFreeHalfNegative_domain : (freeFractionalOperator (-1)).domain = ⊤ := by
  apply Submodule.ext
  intro U
  constructor
  · intro _
    trivial
  · intro _
    apply (physicalSectorMultiplier_domain (fractionalFreeWeight (-1)) U).mpr
    exact ⟨freeFourierRepresentation (grossFreeHalfInverse U),fun n => grossFreeHalfInverse_negative_ae U n⟩

def grossFreeHalfNegativeInput (U : Physical) : (freeFractionalOperator (-1)).domain :=
  ⟨U,by rw [grossFreeHalfNegative_domain]; trivial⟩

lemma grossFreeHalfInverse_original (U : Physical) :
    freeFractionalOperator (-1) (grossFreeHalfNegativeInput U) = grossFreeHalfInverse U := by
  apply freeFourierRepresentation.injective
  apply lp.ext
  funext n
  apply Lp.ext
  exact (physicalSectorMultiplier_action (fractionalFreeWeight (-1)) (grossFreeHalfNegativeInput U) n).symm.trans
    (grossFreeHalfInverse_negative_ae U n)

lemma grossFreeHalfInverse_root (U : Physical) :
    ∃ V : FiberPhysicalRoot, (fiberPhysicalRootInput V).val = grossFreeHalfInverse U ∧ ‖V‖ ≤ ‖U‖ := by
  have hb (n : ℕ) (q : GW.Space) : |Real.sqrt ((n:ℝ)+1)| ≤ 1*|freeFormWeight n q| := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _),one_mul,
      abs_of_nonneg ((zero_lt_one.trans_le (freeFormWeight_one n q)).le)]
    apply Real.sqrt_le_sqrt
    unfold freeGraphWeight freeEnergySymbol
    nlinarith [sq_nonneg ‖q‖]
  have hd : ∃ hm : grossFreeHalfInverse U ∈ (physicalShiftedNumberPower (1/2)).domain,
      ‖physicalShiftedNumberPower (1/2) ⟨grossFreeHalfInverse U,hm⟩‖ ≤ ‖U‖ := by
    rw [physicalShiftedNumberHalf_eq_sectorMultiplier]
    obtain ⟨hm,hb⟩ := physicalSectorMultiplier_domination (fun n _ => Real.sqrt ((n:ℝ)+1)) freeFormWeight
      (fun _ => measurable_const) zero_le_one hb (grossFreeHalfInverseInput U)
    change grossFreeHalfInverse U ∈ (physicalSectorMultiplier (fun n _ => Real.sqrt ((n:ℝ)+1))).domain at hm
    change ‖physicalSectorMultiplier (fun n _ => Real.sqrt ((n:ℝ)+1)) ⟨grossFreeHalfInverse U,hm⟩‖ ≤
      1*‖freeFormOperator (grossFreeHalfInverseInput U)‖ at hb
    rw [grossFreeHalfInverse_action,one_mul] at hb
    exact ⟨hm,hb⟩
  obtain ⟨hm,hb⟩ := hd
  let V : FiberPhysicalRoot := ⟨grossFreeHalfInverse U,hm⟩
  refine ⟨V,rfl,?_⟩
  change ‖physicalShiftedNumberPower (1/2) (fiberPhysicalRootInput V)‖ ≤ ‖U‖
  exact hb



def grossWeylSide (adj : Bool) (f : OneBoson) : Physical ≃ₗᵢ[ℂ] Physical :=
  if adj then grossWeylCoefficient f else (grossWeylCoefficient f).symm

lemma grossWeylSide_unitary_ae (f : OneBoson) (U : Physical) :
    grossWeylSide false f U =ᵐ[volume] fun x => weylUnitary (-phaseAt f x) (U x) := by
  change (grossWeylCoefficient f).symm U =ᵐ[volume] _
  rw [grossWeylCoefficient_symm_apply]
  filter_upwards [grossWeylCoefficient_ae (-f) U] with x hx
  rw [hx]
  have he : phaseAt (-f) x = -phaseAt f x := (weylPhaseIsometry x).map_neg f
  rw [he]

lemma grossWeylSide_adjoint (f : OneBoson) :
    (grossWeylSide true f : Physical →L[ℂ] Physical) =
      (grossWeylSide false f : Physical →L[ℂ] Physical).adjoint := by
  change (grossWeylCoefficient f : Physical →L[ℂ] Physical) =
    ((grossWeylCoefficient f).symm : Physical →L[ℂ] Physical).adjoint
  rw [LinearIsometryEquiv.adjoint_eq_symm,LinearIsometryEquiv.symm_symm]

lemma grossWeylSide_adjoint_ae (f : OneBoson) (U : Physical) :
    grossWeylSide true f U =ᵐ[volume] fun x => weylUnitary (phaseAt f x) (U x) :=
  grossWeylCoefficient_ae f U

lemma grossWeylSide_norm (adj : Bool) (f : OneBoson) :
    ‖(grossWeylSide adj f : Physical →L[ℂ] Physical)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro U
  change ‖grossWeylSide adj f U‖ ≤ 1*‖U‖
  rw [LinearIsometryEquiv.norm_map,one_mul]

lemma grossWeylSide_difference_root (adj : Bool) (a b : OneBoson) (hab : (⟪a,b⟫_ℂ).im = 0)
    (U : FiberPhysicalRoot) :
    ‖grossWeylSide adj a (fiberPhysicalRootInput U).val-grossWeylSide adj b (fiberPhysicalRootInput U).val‖ ≤
      2*‖a-b‖*‖U‖ := by
  cases adj
  · exact grossWeyl_inverse_difference_root a b hab U
  · exact grossWeyl_difference_root a b hab U

def grossWeylWeightedDifference (adj : Bool) (a b : OneBoson) : Physical →L[ℂ] Physical :=
  ((grossWeylSide adj a : Physical →L[ℂ] Physical)-(grossWeylSide adj b : Physical →L[ℂ] Physical)).comp grossFreeHalfInverse

lemma grossWeylWeightedDifference_bound (adj : Bool) (a b : OneBoson) (hab : (⟪a,b⟫_ℂ).im = 0) :
    ‖grossWeylWeightedDifference adj a b‖ ≤ 2*‖a-b‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro U
  obtain ⟨V,hV,hb⟩ := grossFreeHalfInverse_root U
  change ‖grossWeylSide adj a (grossFreeHalfInverse U)-grossWeylSide adj b (grossFreeHalfInverse U)‖ ≤ _
  rw [← hV]
  exact (grossWeylSide_difference_root adj a b hab V).trans (mul_le_mul_of_nonneg_left hb (by positivity))

lemma gross_dressing_weighted_bound (adj : Bool) (α K Λ : ℝ) (hα : 0 ≤ α) (hK : 0 < K) :
    ‖grossWeylWeightedDifference adj (grossFiniteDressingCoefficient α K Λ hα hK) (grossDressingCoefficient α K hα hK)‖ ≤
      2*‖grossFiniteDressingCoefficient α K Λ hα hK-grossDressingCoefficient α K hα hK‖ :=
  grossWeylWeightedDifference_bound adj _ _ (grossTruncateCoefficient_inner_im_zero _ Λ)

lemma gross_dressing_weighted_tendsto (adj : Bool) (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) :
    Tendsto (fun Λ : ℝ => ‖grossWeylWeightedDifference adj (grossFiniteDressingCoefficient α K Λ hα hK)
      (grossDressingCoefficient α K hα hK)‖) atTop (𝓝 0) := by
  have hh := (grossFiniteDressingCoefficient_error_tendsto α K hα hK).const_mul 2
  simp only [mul_zero] at hh
  exact squeeze_zero (fun _ => norm_nonneg _) (fun Λ => gross_dressing_weighted_bound adj α K Λ hα hK) hh

lemma gross_dressing_strong_form (adj : Bool) (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (U : freeFormOperator.domain) :
    Tendsto (fun Λ : ℝ => grossWeylSide adj (grossFiniteDressingCoefficient α K Λ hα hK) U.val) atTop
      (𝓝 (grossWeylSide adj (grossDressingCoefficient α K hα hK) U.val)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hb (Λ : ℝ) :
      ‖grossWeylSide adj (grossFiniteDressingCoefficient α K Λ hα hK) U.val-
        grossWeylSide adj (grossDressingCoefficient α K hα hK) U.val‖ ≤
      ‖grossWeylWeightedDifference adj (grossFiniteDressingCoefficient α K Λ hα hK)
        (grossDressingCoefficient α K hα hK)‖*‖freeFormOperator U‖ := by
    have hh := ContinuousLinearMap.le_opNorm
      (grossWeylWeightedDifference adj (grossFiniteDressingCoefficient α K Λ hα hK)
        (grossDressingCoefficient α K hα hK)) (freeFormOperator U)
    change ‖grossWeylSide adj (grossFiniteDressingCoefficient α K Λ hα hK) (grossFreeHalfInverse (freeFormOperator U))-
      grossWeylSide adj (grossDressingCoefficient α K hα hK) (grossFreeHalfInverse (freeFormOperator U))‖ ≤ _ at hh
    rwa [grossFreeHalfInverse_on_domain] at hh
  have ht := (gross_dressing_weighted_tendsto adj α K hα hK).mul_const ‖freeFormOperator U‖
  simp only [zero_mul] at ht
  exact squeeze_zero (fun _ => norm_nonneg _) hb ht

lemma gross_dressing_strong (adj : Bool) (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (U : Physical) :
    Tendsto (fun Λ : ℝ => grossWeylSide adj (grossFiniteDressingCoefficient α K Λ hα hK) U) atTop
      (𝓝 (grossWeylSide adj (grossDressingCoefficient α K hα hK) U)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨V,hV,hUV⟩ := Metric.mem_closure_iff.mp (freeFormOperator_selfadjoint.1 U) (ε/4) (by positivity)
  have hv := Metric.tendsto_nhds.mp (gross_dressing_strong_form adj α K hα hK ⟨V,hV⟩) (ε/2) (by positivity)
  filter_upwards [hv] with Λ hΛ
  rw [dist_eq_norm] at hUV hΛ ⊢
  have hh := dense_strong_difference_bound
    (grossWeylSide adj (grossFiniteDressingCoefficient α K Λ hα hK) : Physical →L[ℂ] Physical)
    (grossWeylSide adj (grossDressingCoefficient α K hα hK) : Physical →L[ℂ] Physical)
    (grossWeylSide_norm adj _) (grossWeylSide_norm adj _) U V
  change ‖grossWeylSide adj (grossFiniteDressingCoefficient α K Λ hα hK) U-
    grossWeylSide adj (grossDressingCoefficient α K hα hK) U‖ ≤ 2*1*‖U-V‖+
      ‖grossWeylSide adj (grossFiniteDressingCoefficient α K Λ hα hK) V-
        grossWeylSide adj (grossDressingCoefficient α K hα hK) V‖ at hh
  nlinarith

lemma gross_dressing_quantitative (adj : Bool) (α K η Λ : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (hη : 0 < η) (hΛ : 1+max K (56*unitBallVolume*α/η^2) ≤ Λ) :
    ‖grossWeylWeightedDifference adj (grossFiniteDressingCoefficient α K Λ hα hK) (grossDressingCoefficient α K hα hK)‖ ≤ η := by
  have hKΛ : K ≤ Λ := by linarith [le_max_left K (56*unitBallVolume*α/η^2)]
  have hΛpos : 0 < Λ := hK.trans_le hKΛ
  have hd : ‖grossFiniteDressingCoefficient α K Λ hα hK-grossDressingCoefficient α K hα hK‖^2 ≤
      14*unitBallVolume*α/Λ :=
    (grossFiniteDressingCoefficient_error_sq α K Λ hα hK hKΛ).trans
      ((coefficientETail_le_D α Λ hα hΛpos).trans (coefficientDTail_bound α Λ hα hΛpos))
  have hq : 56*unitBallVolume*α/Λ ≤ η^2 := by
    apply (div_le_iff₀ hΛpos).mpr
    have hbound : 56*unitBallVolume*α/η^2 ≤ Λ := by linarith [le_max_right K (56*unitBallVolume*α/η^2)]
    have hh := (div_le_iff₀ (sq_pos_of_pos hη)).mp hbound
    nlinarith
  have hh := gross_dressing_weighted_bound adj α K Λ hα hK
  have hs : (2*‖grossFiniteDressingCoefficient α K Λ hα hK-grossDressingCoefficient α K hα hK‖)^2 ≤ η^2 := by
    calc
      _ ≤ 4*(14*unitBallVolume*α/Λ) := by nlinarith
      _ = 56*unitBallVolume*α/Λ := by ring
      _ ≤ _ := hq
  nlinarith [norm_nonneg (grossFiniteDressingCoefficient α K Λ hα hK-grossDressingCoefficient α K hα hK)]



lemma gross_dressing_strong_quantitative (adj : Bool) (α K η Λ : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (hη : 0 < η) (U : Physical) (V : freeFormOperator.domain) (hUV : ‖U-V.val‖ < η/4)
    (hΛ : 1+max K (56*unitBallVolume*α/(η/(2*(1+‖freeFormOperator V‖)))^2) ≤ Λ) :
    ‖grossWeylSide adj (grossFiniteDressingCoefficient α K Λ hα hK) U-
      grossWeylSide adj (grossDressingCoefficient α K hα hK) U‖ < η := by
  let ε := η/(2*(1+‖freeFormOperator V‖))
  have hε : 0 < ε := div_pos hη (by positivity)
  have hw := gross_dressing_quantitative adj α K ε Λ hα hK hε hΛ
  have hv := ContinuousLinearMap.le_opNorm
    (grossWeylWeightedDifference adj (grossFiniteDressingCoefficient α K Λ hα hK)
      (grossDressingCoefficient α K hα hK)) (freeFormOperator V)
  change ‖grossWeylSide adj (grossFiniteDressingCoefficient α K Λ hα hK) (grossFreeHalfInverse (freeFormOperator V))-
    grossWeylSide adj (grossDressingCoefficient α K hα hK) (grossFreeHalfInverse (freeFormOperator V))‖ ≤ _ at hv
  rw [grossFreeHalfInverse_on_domain] at hv
  have hs := hv.trans (mul_le_mul_of_nonneg_right hw (norm_nonneg (freeFormOperator V)))
  have hd := dense_strong_difference_bound
    (grossWeylSide adj (grossFiniteDressingCoefficient α K Λ hα hK) : Physical →L[ℂ] Physical)
    (grossWeylSide adj (grossDressingCoefficient α K hα hK) : Physical →L[ℂ] Physical)
    (grossWeylSide_norm adj _) (grossWeylSide_norm adj _) U V.val
  change ‖grossWeylSide adj (grossFiniteDressingCoefficient α K Λ hα hK) U-
    grossWeylSide adj (grossDressingCoefficient α K hα hK) U‖ ≤ 2*1*‖U-V.val‖+
      ‖grossWeylSide adj (grossFiniteDressingCoefficient α K Λ hα hK) V.val-
        grossWeylSide adj (grossDressingCoefficient α K hα hK) V.val‖ at hd
  have he : ε*(2*(1+‖freeFormOperator V‖)) = η := by
    exact div_mul_cancel₀ η (ne_of_gt (by positivity : 0 < 2*(1+‖freeFormOperator V‖)))
  nlinarith


end GW.Gross
