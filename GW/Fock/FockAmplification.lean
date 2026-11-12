module
public import GW.Fock.ProductDensity
public import GW.Fock.Coordinates
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.PiSystem
public import Mathlib.Analysis.Normed.Operator.Extend
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace ENNReal
namespace GW.Fock
section BoundedAmplification
variable {Y E F : Type*} [MeasurableSpace Y] (μ : Measure Y)
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

def amplify (T : E →L[ℂ] F) : Lp E 2 μ →L[ℂ] Lp F 2 μ := T.compLpL 2 μ
lemma amplify_ae (T : E →L[ℂ] F) (u : Lp E 2 μ) :
    amplify μ T u =ᵐ[μ] fun y => T (u y) := T.coeFn_compLp u
lemma amplify_norm_le (T : E →L[ℂ] F) : ‖amplify μ T‖ ≤ ‖T‖ := T.norm_compLpL_le

lemma amplify_indicator (T : E →L[ℂ] F) {A : Set Y} (hA : MeasurableSet A) (hf : μ A ≠ ∞) (v : E) :
    amplify μ T (indicatorConstLp 2 hA hf v) = indicatorConstLp 2 hA hf (T v) :=
  compLp_indicatorConst μ hA hf T v

lemma amplify_norm_eq (T : E →L[ℂ] F) {A : Set Y} (hA : MeasurableSet A)
    (hpos : 0 < μ A) (hfinite : μ A ≠ ∞) : ‖amplify μ T‖ = ‖T‖ := by
  apply le_antisymm (amplify_norm_le μ T)
  apply T.opNorm_le_bound (norm_nonneg (amplify μ T))
  intro v
  have h := (amplify μ T).le_opNorm (indicatorConstLp 2 hA hfinite v)
  rw [amplify_indicator,norm_indicatorConstLp (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞),norm_indicatorConstLp (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞)] at h
  have hc : 0 < (μ.real A) ^ (1/(2 : ℝ≥0∞).toReal) :=
    Real.rpow_pos_of_pos (ENNReal.toReal_pos (ne_of_gt hpos) hfinite) _
  nlinarith

variable [CompleteSpace E] [CompleteSpace F]

lemma amplify_adjoint (T : E →L[ℂ] F) : (amplify μ T).adjoint = amplify μ T.adjoint := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro u v
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [amplify_ae μ T.adjoint u,amplify_ae μ T v] with y hu hv
  rw [hu,hv]
  exact T.adjoint_inner_left (v y) (u y)
def amplificationLinear : (E →L[ℂ] F) →ₗ[ℂ] (Lp E 2 μ →L[ℂ] Lp F 2 μ) where
  toFun := amplify μ
  map_add' := ContinuousLinearMap.add_compLpL
  map_smul' := ContinuousLinearMap.smul_compLpL

end BoundedAmplification
section Contraction
variable {Z E : Type*} [MeasurableSpace Z] (ν : Measure Z)
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [InnerProductSpace ℂ E] [CompleteSpace E] in
lemma normProduct_integrable (f : Lp ℂ 2 ν) (v : Lp E 2 ν) :
    Integrable (fun z => ‖f z‖*‖v z‖) ν :=
  (Lp.memLp f).norm.integrable_mul (Lp.memLp v).norm

omit [CompleteSpace E] in
lemma normProduct_integral_le (f : Lp ℂ 2 ν) (v : Lp E 2 ν) :
    (∫ z, ‖f z‖*‖v z‖ ∂ν) ≤ ‖f‖*‖v‖ := by
  have hf : MemLp (fun z => ‖f z‖) (ENNReal.ofReal (2 : ℝ)) ν := by
    simpa only [ENNReal.ofReal_ofNat] using (Lp.memLp f).norm
  have hv : MemLp (fun z => ‖v z‖) (ENNReal.ofReal (2 : ℝ)) ν := by
    simpa only [ENNReal.ofReal_ofNat] using (Lp.memLp v).norm
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg
    (show (2 : ℝ).HolderConjugate 2 by rw [Real.holderConjugate_iff];norm_num)
    (Eventually.of_forall (fun z => norm_nonneg (f z)))
    (Eventually.of_forall (fun z => norm_nonneg (v z))) hf hv
  simp only [Real.rpow_two] at h
  rw [← GW.Analysis.l2_norm_sq (𝕜 := ℂ),← GW.Analysis.l2_norm_sq (𝕜 := ℂ)] at h
  simpa only [← Real.sqrt_eq_rpow,Real.sqrt_sq_eq_abs,abs_norm] using h

omit [CompleteSpace E] in
lemma contraction_integrable (f : Lp ℂ 2 ν) (v : Lp E 2 ν) :
    Integrable (fun z => (starRingEnd ℂ) (f z) • v z) ν := by
  apply (normProduct_integrable ν f v).mono'
    ((Lp.memLp f).aestronglyMeasurable.star.smul (Lp.memLp v).aestronglyMeasurable)
  exact Eventually.of_forall (fun z => by
    change ‖star (f z) • v z‖ ≤ ‖f z‖*‖v z‖
    rw [norm_smul,norm_star])

def contractionValue (f : Lp ℂ 2 ν) (v : Lp E 2 ν) : E :=
  ∫ z, (starRingEnd ℂ) (f z) • v z ∂ν

omit [CompleteSpace E] in
lemma contractionValue_bound (f : Lp ℂ 2 ν) (v : Lp E 2 ν) :
    ‖contractionValue ν f v‖ ≤ ‖f‖*‖v‖ := by
  calc
    _ ≤ ∫ z, ‖(starRingEnd ℂ) (f z) • v z‖ ∂ν := norm_integral_le_integral_norm _
    _ = ∫ z, ‖f z‖*‖v z‖ ∂ν := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => by
        change ‖star (f z) • v z‖ = ‖f z‖*‖v z‖
        rw [norm_smul,norm_star])
    _ ≤ _ := normProduct_integral_le ν f v

omit [CompleteSpace E] in
lemma contractionValue_add (f : Lp ℂ 2 ν) (v w : Lp E 2 ν) :
    contractionValue ν f (v+w) = contractionValue ν f v+contractionValue ν f w := by
  unfold contractionValue
  calc
    _ = ∫ z, (starRingEnd ℂ) (f z) • v z+(starRingEnd ℂ) (f z) • w z ∂ν := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_add v w] with z hz
      rw [hz,Pi.add_apply,smul_add]
    _ = _ := integral_add (contraction_integrable ν f v) (contraction_integrable ν f w)

omit [CompleteSpace E] in
lemma contractionValue_smul (f : Lp ℂ 2 ν) (c : ℂ) (v : Lp E 2 ν) :
    contractionValue ν f (c • v) = c • contractionValue ν f v := by
  unfold contractionValue
  calc
    _ = ∫ z, c • ((starRingEnd ℂ) (f z) • v z) ∂ν := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_smul c v] with z hz
      rw [hz,Pi.smul_apply,smul_comm]
    _ = _ := integral_smul _ _

def contraction (f : Lp ℂ 2 ν) : Lp E 2 ν →L[ℂ] E :=
  ({toFun := contractionValue ν f,map_add' := contractionValue_add ν f,
    map_smul' := contractionValue_smul ν f} : Lp E 2 ν →ₗ[ℂ] E).mkContinuous ‖f‖ (contractionValue_bound ν f)

omit [CompleteSpace E] in
lemma contraction_norm (f : Lp ℂ 2 ν) : ‖contraction (E := E) ν f‖ ≤ ‖f‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (contractionValue_bound ν f)

omit [CompleteSpace E] in
lemma contractionValue_congr_ae (f : Lp ℂ 2 ν) (v : Lp E 2 ν)
    {f' : Z → ℂ} {v' : Z → E} (hf : f =ᵐ[ν] f') (hv : v =ᵐ[ν] v') :
    contractionValue ν f v = ∫ z, (starRingEnd ℂ) (f' z) • v' z ∂ν := by
  apply integral_congr_ae
  filter_upwards [hf,hv] with z hz hw
  rw [hz,hw]

def tensorEmbedding (f : Lp ℂ 2 ν) : E →L[ℂ] Lp E 2 ν :=
  (ContinuousLinearMap.compLpL₂ 2 ν
    ((ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] E →L[ℂ] E).flip)).flip f

omit [CompleteSpace E] in
lemma tensorEmbedding_apply (f : Lp ℂ 2 ν) (e : E) :
    tensorEmbedding ν f e = (ContinuousLinearMap.toSpanSingleton ℂ e).compLp f := rfl

omit [CompleteSpace E] in
lemma tensorEmbedding_ae (f : Lp ℂ 2 ν) (e : E) :
    tensorEmbedding ν f e =ᵐ[ν] (fun z => f z • e) :=
  (ContinuousLinearMap.toSpanSingleton ℂ e).coeFn_compLp f

omit [CompleteSpace E] in
lemma tensorEmbedding_norm (f : Lp ℂ 2 ν) : ‖tensorEmbedding (E := E) ν f‖ ≤ ‖f‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f)
  intro e
  rw [tensorEmbedding_apply,simpleTensor_norm]

lemma contraction_pairing (f : Lp ℂ 2 ν) (e : E) (v : Lp E 2 ν) :
    ⟪e,contraction ν f v⟫_ℂ = ⟪tensorEmbedding ν f e,v⟫_ℂ := by
  change ⟪e,∫ z, (starRingEnd ℂ) (f z) • v z ∂ν⟫_ℂ = _
  rw [← integral_inner (contraction_integrable ν f v) e,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [tensorEmbedding_ae ν f e] with z hz
  rw [hz,inner_smul_right,inner_smul_left]

lemma tensorEmbedding_adjoint (f : Lp ℂ 2 ν) : (tensorEmbedding (E := E) ν f).adjoint = contraction ν f := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro v e
  have h := congrArg (starRingEnd ℂ) (contraction_pairing ν f e v)
  simpa only [inner_conj_symm] using h

end Contraction
section ProductSimple
variable {Y Z E : Type*} [MeasurableSpace Y] [MeasurableSpace Z]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (μ : Measure Y) (ν : Measure Z) [SigmaFinite μ] [SigmaFinite ν]

/-- Evaluation is used only on a fixed finite-valued simple function of L² classes. -/
def simpleProductRep (s : SimpleFunc Y (Lp E 2 ν)) : Y × Z → E := fun p => s p.1 p.2

omit [InnerProductSpace ℂ E] [CompleteSpace E] [SigmaFinite ν] in
lemma simpleProductRep_strong (s : SimpleFunc Y (Lp E 2 ν)) : StronglyMeasurable (simpleProductRep ν s) := by
  classical
  induction s using SimpleFunc.induction' with
  | const c => exact (Lp.stronglyMeasurable c).comp_measurable measurable_snd
  | @pcw f g A hA hf hg =>
    have he : simpleProductRep ν (f.piecewise A hA g) =
        Set.piecewise (Prod.fst ⁻¹' A) (simpleProductRep ν f) (simpleProductRep ν g) := by
      funext p
      by_cases hp : p.1 ∈ A <;> simp [simpleProductRep,SimpleFunc.piecewise_apply,Set.piecewise,hp]
    rw [he]
    exact hf.piecewise (hA.preimage measurable_fst) hg

omit [SigmaFinite μ] in
lemma simpleProductRep_lintegral (s : SimpleFunc Y (Lp E 2 ν)) :
    (∫⁻ p, ENNReal.ofReal (‖simpleProductRep ν s p‖^2) ∂μ.prod ν) =
      ∫⁻ y, ENNReal.ofReal (‖s y‖^2) ∂μ := by
  have hm : AEMeasurable (fun p => ENNReal.ofReal (‖simpleProductRep ν s p‖^2)) (μ.prod ν) :=
    ((simpleProductRep_strong ν s).norm.pow 2).aemeasurable.ennreal_ofReal
  rw [lintegral_prod _ hm]
  apply lintegral_congr_ae
  exact Eventually.of_forall (fun y => by
    change (∫⁻ z, ENNReal.ofReal (‖s y z‖^2) ∂ν) = ENNReal.ofReal (‖s y‖^2)
    exact (ofReal_integral_eq_lintegral_ofReal ((Lp.memLp (s y)).integrable_norm_pow (p := 2) (by norm_num))
      (Eventually.of_forall (fun _ => sq_nonneg _))).symm.trans
      (congrArg ENNReal.ofReal (GW.Analysis.l2_norm_sq (𝕜 := ℂ) (s y)).symm))

lemma simpleProductRep_memLp (s : SimpleFunc Y (Lp E 2 ν)) (hs : MemLp s 2 μ) :
    MemLp (simpleProductRep ν s) 2 (μ.prod ν) := by
  apply (memLp_two_iff_integrable_sq_norm (simpleProductRep_strong ν s).aestronglyMeasurable).mpr
  refine ⟨(simpleProductRep_strong ν s).norm.pow 2 |>.aestronglyMeasurable,?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun _ => sq_nonneg _))).mpr
  rw [simpleProductRep_lintegral]
  exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun _ => sq_nonneg _))).mp
    (hs.integrable_norm_pow (p := 2) (by norm_num)).2

def simpleProductClass (s : SimpleFunc Y (Lp E 2 ν)) (hs : MemLp s 2 μ) : Lp E 2 (μ.prod ν) :=
  (simpleProductRep_memLp μ ν s hs).toLp (simpleProductRep ν s)

lemma simpleProductClass_ae (s : SimpleFunc Y (Lp E 2 ν)) (hs : MemLp s 2 μ) :
    simpleProductClass μ ν s hs =ᵐ[μ.prod ν] simpleProductRep ν s := MemLp.coeFn_toLp _

lemma simpleProductRep_integral (s : SimpleFunc Y (Lp E 2 ν)) (hs : MemLp s 2 μ) :
    (∫ p, ‖simpleProductRep ν s p‖^2 ∂μ.prod ν) = ∫ y, ‖s y‖^2 ∂μ := by
  rw [integral_prod _ ((simpleProductRep_memLp μ ν s hs).integrable_norm_pow (p := 2) (by norm_num))]
  apply integral_congr_ae
  exact Eventually.of_forall (fun y => (GW.Analysis.l2_norm_sq (𝕜 := ℂ) (s y)).symm)

lemma simpleProductClass_norm_sq (s : SimpleFunc Y (Lp E 2 ν)) (hs : MemLp s 2 μ) :
    ‖simpleProductClass μ ν s hs‖^2 = ∫ y, ‖s y‖^2 ∂μ := by
  rw [GW.Analysis.l2_norm_sq (𝕜 := ℂ)]
  exact (integral_congr_ae ((simpleProductClass_ae μ ν s hs).mono
    (fun _ hx => congrArg (fun e : E => ‖e‖^2) hx))).trans (simpleProductRep_integral μ ν s hs)

omit [InnerProductSpace ℂ E] [CompleteSpace E] [SigmaFinite μ] [SigmaFinite ν] in
lemma simpleProductRep_congr_ae (s t : SimpleFunc Y (Lp E 2 ν)) (h : s =ᵐ[μ] t) :
    simpleProductRep ν s =ᵐ[μ.prod ν] simpleProductRep ν t := by
  filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae h] with p hp
  exact congrArg (fun v : Lp E 2 ν => v p.2) hp

omit [SigmaFinite μ] in
lemma simpleProductRep_add_ae (s t : SimpleFunc Y (Lp E 2 ν)) :
    simpleProductRep ν (s + t) =ᵐ[μ.prod ν]
      (fun p => simpleProductRep ν s p + simpleProductRep ν t p) := by
  apply (Measure.ae_prod_iff_ae_ae ((simpleProductRep_strong ν (s+t)).measurableSet_eq_fun
    ((simpleProductRep_strong ν s).add (simpleProductRep_strong ν t)))).mpr
  exact Eventually.of_forall (fun y => Lp.coeFn_add (s y) (t y))

omit [SigmaFinite μ] in
lemma simpleProductRep_smul_ae (c : ℂ) (s : SimpleFunc Y (Lp E 2 ν)) :
    simpleProductRep ν (c • s) =ᵐ[μ.prod ν]
      (fun p => c • simpleProductRep ν s p) := by
  apply (Measure.ae_prod_iff_ae_ae ((simpleProductRep_strong ν (c • s)).measurableSet_eq_fun
    ((simpleProductRep_strong ν s).const_smul c))).mpr
  exact Eventually.of_forall (fun y => Lp.coeFn_smul c (s y))

lemma simpleProductClass_congr (s t : SimpleFunc Y (Lp E 2 ν))
    (hs : MemLp s 2 μ) (ht : MemLp t 2 μ) (h : s =ᵐ[μ] t) :
    simpleProductClass μ ν s hs = simpleProductClass μ ν t ht := by
  apply Lp.ext
  exact (simpleProductClass_ae μ ν s hs).trans
    ((simpleProductRep_congr_ae μ ν s t h).trans (simpleProductClass_ae μ ν t ht).symm)

lemma simpleProductClass_add (s t : SimpleFunc Y (Lp E 2 ν))
    (hs : MemLp s 2 μ) (ht : MemLp t 2 μ) :
    simpleProductClass μ ν (s+t) (hs.add ht) =
      simpleProductClass μ ν s hs + simpleProductClass μ ν t ht := by
  apply Lp.ext
  filter_upwards [simpleProductClass_ae μ ν (s+t) (hs.add ht),
    simpleProductRep_add_ae μ ν s t, simpleProductClass_ae μ ν s hs,
    simpleProductClass_ae μ ν t ht,
    Lp.coeFn_add (simpleProductClass μ ν s hs) (simpleProductClass μ ν t ht)] with p h₁ h₂ h₃ h₄ h₅
  rw [h₁,h₂,h₅]
  simp only [Pi.add_apply]
  rw [h₃,h₄]

lemma simpleProductClass_smul (c : ℂ) (s : SimpleFunc Y (Lp E 2 ν)) (hs : MemLp s 2 μ) :
    simpleProductClass μ ν (c • s) (hs.const_smul c) = c • simpleProductClass μ ν s hs := by
  apply Lp.ext
  filter_upwards [simpleProductClass_ae μ ν (c • s) (hs.const_smul c),
    simpleProductRep_smul_ae μ ν c s, simpleProductClass_ae μ ν s hs,
    Lp.coeFn_smul c (simpleProductClass μ ν s hs)] with p h₁ h₂ h₃ h₄
  rw [h₁,h₂,h₄]
  simp only [Pi.smul_apply]
  rw [h₃]

attribute [local instance] Lp.simpleFunc.smul Lp.simpleFunc.module Lp.simpleFunc.normedSpace

/-- The initial map uses only a finite simple representative of an iterated class. -/
def simpleProductLinear : Lp.simpleFunc (Lp E 2 ν) 2 μ →ₗ[ℂ] Lp E 2 (μ.prod ν) where
  toFun s := simpleProductClass μ ν (Lp.simpleFunc.toSimpleFunc s) (Lp.simpleFunc.memLp s)
  map_add' s t := by
    exact (simpleProductClass_congr μ ν _ _ _ _ (Lp.simpleFunc.add_toSimpleFunc s t)).trans
      (simpleProductClass_add μ ν _ _ _ _)
  map_smul' c s := by
    exact (simpleProductClass_congr μ ν _ _ _ _ (Lp.simpleFunc.smul_toSimpleFunc c s)).trans
      (simpleProductClass_smul μ ν c _ _)

def simpleInclusion : Lp.simpleFunc (Lp E 2 ν) 2 μ →ₗ[ℂ] Lp (Lp E 2 ν) 2 μ where
  toFun s := s.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma simpleProductLinear_norm (s : Lp.simpleFunc (Lp E 2 ν) 2 μ) :
    ‖simpleProductLinear μ ν s‖ = ‖simpleInclusion μ ν s‖ := by
  have h : ‖simpleProductLinear μ ν s‖^2 = ‖simpleInclusion μ ν s‖^2 := by
    change ‖simpleProductClass μ ν (Lp.simpleFunc.toSimpleFunc s) (Lp.simpleFunc.memLp s)‖^2 = _
    rw [simpleProductClass_norm_sq,GW.Analysis.l2_norm_sq (𝕜 := ℂ)]
    apply integral_congr_ae
    exact (Lp.simpleFunc.toSimpleFunc_eq_toFun s).mono
      (fun y hy => congrArg (fun v : Lp E 2 ν => ‖v‖^2) hy)
  nlinarith [norm_nonneg (simpleProductLinear μ ν s),norm_nonneg (simpleInclusion μ ν s)]

omit [CompleteSpace E] [SigmaFinite μ] [SigmaFinite ν] in
lemma simpleInclusion_dense : DenseRange (simpleInclusion (E := E) μ ν) :=
  Lp.simpleFunc.denseRange (by norm_num)

/-- Norm-limit extension from finite simple iterated functions; no arbitrary-class evaluation. -/
def productIsometry : Lp (Lp E 2 ν) 2 μ →ₗᵢ[ℂ] Lp E 2 (μ.prod ν) :=
  (simpleProductLinear μ ν).extendOfIsometry (simpleInclusion_dense μ ν)
    (simpleProductLinear_norm μ ν)

lemma productIsometry_simple (s : Lp.simpleFunc (Lp E 2 ν) 2 μ) :
    productIsometry μ ν (s : Lp (Lp E 2 ν) 2 μ) = simpleProductLinear μ ν s :=
  LinearMap.extendOfIsometry_eq _ _ _ s

lemma productIsometry_toLp (s : SimpleFunc Y (Lp E 2 ν)) (hs : MemLp s 2 μ) :
    productIsometry μ ν (hs.toLp s) = simpleProductClass μ ν s hs := by
  change productIsometry μ ν ((s.toLp hs : Lp.simpleFunc (Lp E 2 ν) 2 μ) : Lp (Lp E 2 ν) 2 μ) = _
  rw [productIsometry_simple]
  exact simpleProductClass_congr μ ν (Lp.simpleFunc.toSimpleFunc (s.toLp hs)) s
    (Lp.simpleFunc.memLp (s.toLp hs)) hs (Lp.simpleFunc.toSimpleFunc_toLp s hs)

lemma productIsometry_indicator_ae (A : Set Y) (hA : MeasurableSet A) (hAf : μ A ≠ ∞)
    (v : Lp E 2 ν) :
    productIsometry μ ν (indicatorConstLp 2 hA hAf v) =ᵐ[μ.prod ν]
      (Prod.fst ⁻¹' A).indicator (fun p => v p.2) := by
  classical
  let s : SimpleFunc Y (Lp E 2 ν) :=
    (SimpleFunc.const Y v).piecewise A hA (SimpleFunc.const Y 0)
  have hsfun : (s : Y → Lp E 2 ν) = A.indicator (fun _ => v) := by
    funext y; by_cases hy : y ∈ A <;> simp [s,SimpleFunc.piecewise_apply,hy]
  have hs : MemLp s 2 μ := hsfun ▸ memLp_indicator_const 2 hA.nullMeasurableSet v (.inr hAf)
  have he : indicatorConstLp 2 hA hAf v = hs.toLp s := by
    apply Lp.ext
    exact indicatorConstLp_coeFn.trans (hsfun ▸ hs.coeFn_toLp.symm)
  rw [he,productIsometry_toLp]
  apply (simpleProductClass_ae μ ν s hs).trans
  filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae (Lp.coeFn_zero E 2 ν)] with p hp
  change s p.1 p.2 = _
  by_cases hy : p.1 ∈ A
  · simp [s,SimpleFunc.piecewise_apply,hy]
  · simpa [s,SimpleFunc.piecewise_apply,hy] using hp

lemma productIsometry_rectangle (A : Set Y) (B : Set Z)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAf : μ A ≠ ∞) (hBf : ν B ≠ ∞) (e : E) :
    productIsometry μ ν (indicatorConstLp 2 hA hAf (indicatorConstLp 2 hB hBf e)) =
      indicatorConstLp 2 (hA.prod hB) (by rw [Measure.prod_prod]; exact ENNReal.mul_ne_top hAf hBf) e := by
  apply Lp.ext
  filter_upwards [productIsometry_indicator_ae μ ν A hA hAf (indicatorConstLp 2 hB hBf e),
    (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae
      (indicatorConstLp_coeFn (p := 2) (hs := hB) (hμs := hBf) (c := e)),
    indicatorConstLp_coeFn (μ := μ.prod ν) (p := 2) (hs := hA.prod hB)
      (hμs := by rw [Measure.prod_prod]; exact ENNReal.mul_ne_top hAf hBf) (c := e)] with p h₁ h₂ h₃
  rw [h₁,h₃]
  by_cases ha : p.1 ∈ A <;> by_cases hb : p.2 ∈ B <;> simp [ha,hb,h₂]

omit [CompleteSpace E] in
/-- Squared-error dominated convergence for indicators inside one finite-measure set. -/
lemma indicatorLp_tendsto {X : Type*} [MeasurableSpace X] (ρ : Measure X)
    (R C : Set X) (S : ℕ → Set X) (hR : MeasurableSet R) (hRf : ρ R ≠ ∞)
    (hC : MeasurableSet C) (hCf : ρ C ≠ ∞) (hS : ∀ n, MeasurableSet (S n))
    (hSf : ∀ n, ρ (S n) ≠ ∞) (hSR : ∀ n, S n ⊆ R)
    (hl : ∀ x, ∀ᶠ n in atTop, x ∈ S n ↔ x ∈ C) (e : E) :
    Tendsto (fun n => indicatorConstLp 2 (hS n) (hSf n) e) atTop
      (𝓝 (indicatorConstLp 2 hC hCf e)) := by
  classical
  obtain ⟨hs,hf,ht⟩ := GW.Analysis.dominated_l2_convergence (𝕜 := ℂ)
    (μ := ρ) (fs := fun n => (S n).indicator (fun _ => e))
    (f := C.indicator (fun _ => e)) (g := R.indicator (fun _ => ‖e‖))
    (fun n => stronglyMeasurable_const.aestronglyMeasurable.indicator (hS n))
    (Eventually.of_forall (fun x => tendsto_const_nhds.congr' ((hl x).mono (fun n hn => by
      simp only [Set.indicator]; rw [hn]))))
    (measurable_const.indicator hR)
    ((memLp_indicator_const 2 hR.nullMeasurableSet ‖e‖ (.inr hRf)).integrable_norm_pow
      (p := 2) (by norm_num) |>.congr (Eventually.of_forall (fun x => by
        by_cases hx : x ∈ R <;> simp [hx])))
    (fun n => Eventually.of_forall (fun x => by
      by_cases hx : x ∈ S n
      · simp [hx,hSR n hx]
      · by_cases hr : x ∈ R <;> simp [hx,hr]))
  have heq n : (hs n).toLp _ = indicatorConstLp 2 (hS n) (hSf n) e := by
    apply Lp.ext
    exact (hs n).coeFn_toLp.trans indicatorConstLp_coeFn.symm
  have heqf : hf.toLp _ = indicatorConstLp 2 hC hCf e := by
    apply Lp.ext
    exact hf.coeFn_toLp.trans indicatorConstLp_coeFn.symm
  simpa only [heq,heqf] using tendsto_iff_norm_sub_tendsto_zero.mpr ht

omit [InnerProductSpace ℂ E] [CompleteSpace E] in
lemma indicatorLp_set_congr {X : Type*} [MeasurableSpace X] (ρ : Measure X)
    {S T : Set X} (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hfS : ρ S ≠ ∞) (hfT : ρ T ≠ ∞) (h : S = T) (e : E) :
    indicatorConstLp 2 hS hfS e = indicatorConstLp 2 hT hfT e := by
  subst T
  rfl

/-- The finite-rectangle restriction in the manuscript's pi-system induction. -/
lemma rectangle_indicator_restriction
    (V : Submodule ℂ (Lp E 2 (μ.prod ν))) (hV : IsClosed (V : Set (Lp E 2 (μ.prod ν))))
    (hrect : ∀ (A : Set Y) (B : Set Z) (hA : MeasurableSet A) (hB : MeasurableSet B)
      (hAf : μ A ≠ ∞) (hBf : ν B ≠ ∞) (e : E),
      indicatorConstLp 2 (hA.prod hB) (by rw [Measure.prod_prod]; exact ENNReal.mul_ne_top hAf hBf) e ∈ V)
    (A₀ : Set Y) (B₀ : Set Z) (hA₀ : MeasurableSet A₀) (hB₀ : MeasurableSet B₀)
    (hAf₀ : μ A₀ ≠ ∞) (hBf₀ : ν B₀ ≠ ∞) :
    ∀ C (hC : MeasurableSet C) (e : E),
      indicatorConstLp 2 (hC.inter (hA₀.prod hB₀))
        ((measure_mono Set.inter_subset_right).trans_lt (by
          rw [Measure.prod_prod]; exact ENNReal.mul_lt_top hAf₀.lt_top hBf₀.lt_top)).ne e ∈ V := by
  classical
  let R := A₀ ×ˢ B₀
  have hR : MeasurableSet R := hA₀.prod hB₀
  have hRf : (μ.prod ν) R < ∞ := by
    rw [Measure.prod_prod]; exact ENNReal.mul_lt_top hAf₀.lt_top hBf₀.lt_top
  have hf (C : Set (Y × Z)) : (μ.prod ν) (C ∩ R) ≠ ∞ :=
    ((measure_mono Set.inter_subset_right).trans_lt hRf).ne
  intro D hD
  refine MeasurableSpace.induction_on_inter generateFrom_prod.symm isPiSystem_prod ?_ ?_ ?_ ?_ D hD
  · intro e
    have he : indicatorConstLp (μ := μ.prod ν) 2 (MeasurableSet.empty.inter hR) (hf ∅) e = 0 := by
      apply Lp.ext
      filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := MeasurableSet.empty.inter hR)
        (hμs := hf ∅) (c := e), Lp.coeFn_zero E 2 (μ.prod ν)] with p hp h0
      simpa using hp.trans h0.symm
    rw [he]; exact V.zero_mem
  · rintro _ ⟨A,hA,B,hB,rfl⟩ e
    have he : (A ×ˢ B) ∩ R = (A ∩ A₀) ×ˢ (B ∩ B₀) := by ext p; simp [R]; tauto
    have h := hrect (A ∩ A₀) (B ∩ B₀) (hA.inter hA₀) (hB.inter hB₀)
      ((measure_mono Set.inter_subset_right).trans_lt hAf₀.lt_top).ne
      ((measure_mono Set.inter_subset_right).trans_lt hBf₀.lt_top).ne e
    exact (indicatorLp_set_congr (μ.prod ν) _ _ _ _ he e) ▸ h
  · intro C hC ih e
    have he : indicatorConstLp 2 (hC.compl.inter hR) (hf Cᶜ) e =
        indicatorConstLp 2 hR hRf.ne e - indicatorConstLp 2 (hC.inter hR) (hf C) e := by
      apply Lp.ext
      filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hC.compl.inter hR) (hμs := hf Cᶜ) (c := e),
        indicatorConstLp_coeFn (p := 2) (hs := hR) (hμs := hRf.ne) (c := e),
        indicatorConstLp_coeFn (p := 2) (hs := hC.inter hR) (hμs := hf C) (c := e),
        Lp.coeFn_sub (indicatorConstLp 2 hR hRf.ne e) (indicatorConstLp 2 (hC.inter hR) (hf C) e)]
        with p h₁ h₂ h₃ h₄
      rw [h₁,h₄]; simp only [Pi.sub_apply]; rw [h₂,h₃]
      by_cases hc : p ∈ C <;> by_cases hr : p ∈ R <;> simp [hc,hr]
    rw [he]
    exact V.sub_mem (hrect A₀ B₀ hA₀ hB₀ hAf₀ hBf₀ e) (ih e)
  · intro C hd hC ih e
    let S (n : ℕ) := ⋃ i ∈ Finset.range n, C i
    have hS n : MeasurableSet (S n) := by exact MeasurableSet.iUnion (fun i => MeasurableSet.iUnion (fun _ => hC i))
    have hSmem n : indicatorConstLp 2 ((hS n).inter hR) (hf (S n)) e ∈ V := by
      induction n with
      | zero =>
        have he : indicatorConstLp (μ := μ.prod ν) 2 ((hS 0).inter hR) (hf (S 0)) e = 0 := by
          apply Lp.ext
          filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := (hS 0).inter hR) (hμs := hf (S 0)) (c := e),
            Lp.coeFn_zero E 2 (μ.prod ν)] with p hp h0
          simpa [S] using hp.trans h0.symm
        rw [he]; exact V.zero_mem
      | succ n hn =>
        have hdis : Disjoint (S n ∩ R) (C n ∩ R) := by
          rw [Set.disjoint_left]
          rintro p ⟨hp,_⟩ ⟨hq,_⟩
          rcases Set.mem_iUnion.mp hp with ⟨i,hi⟩
          rcases Set.mem_iUnion.mp hi with ⟨hi,hpi⟩
          exact Set.disjoint_left.mp (hd (Finset.mem_range.mp hi).ne) hpi hq
        have he : S (n+1) ∩ R = (S n ∩ R) ∪ (C n ∩ R) := by
          ext p
          simp only [S,Set.mem_inter_iff,Set.mem_union,Set.mem_iUnion,Finset.mem_range]
          constructor
          · rintro ⟨⟨i,hi,hpi⟩,hr⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
            · exact Or.inl ⟨⟨i,hi,hpi⟩,hr⟩
            · exact Or.inr ⟨hpi,hr⟩
          · rintro (⟨⟨i,hi,hpi⟩,hr⟩ | ⟨hp,hr⟩)
            · exact ⟨⟨i,hi.trans (Nat.lt_succ_self n),hpi⟩,hr⟩
            · exact ⟨⟨n,Nat.lt_succ_self n,hp⟩,hr⟩
        have heq := indicatorConstLp_disjoint_union (p := 2) ((hS n).inter hR) ((hC n).inter hR)
          (hf (S n)) (hf (C n)) hdis e
        have heq' := (indicatorLp_set_congr (μ.prod ν) ((hS (n+1)).inter hR)
          (((hS n).inter hR).union ((hC n).inter hR)) (hf (S (n+1))) _ he e).trans heq
        rw [heq']
        exact V.add_mem hn (ih n e)
    apply hV.mem_of_tendsto (indicatorLp_tendsto (μ.prod ν) R ((⋃ i, C i) ∩ R)
      (fun n => S n ∩ R) hR hRf.ne ((MeasurableSet.iUnion hC).inter hR) (hf (⋃ i,C i))
      (fun n => (hS n).inter hR) (fun n => hf (S n)) (fun _ => Set.inter_subset_right) ?_ e)
      (Eventually.of_forall hSmem)
    intro p
    by_cases hp : p ∈ ⋃ i,C i
    · rcases Set.mem_iUnion.mp hp with ⟨i,hi⟩
      filter_upwards [eventually_gt_atTop i] with n hn
      constructor
      · rintro ⟨_,hr⟩; exact ⟨Set.mem_iUnion.mpr ⟨i,hi⟩,hr⟩
      · rintro ⟨_,hr⟩; exact ⟨Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr hn,hi⟩⟩,hr⟩
    · exact Eventually.of_forall (fun n => by
        have hn : p ∉ S n := by
          intro hh; rcases Set.mem_iUnion.mp hh with ⟨i,hi⟩
          rcases Set.mem_iUnion.mp hi with ⟨_,hi⟩
          exact hp (Set.mem_iUnion.mpr ⟨i,hi⟩)
        simp [hp,hn])

/-- Exhaust the factors after the finite-rectangle induction, then use native simple density. -/
lemma rectangle_dense_criterion
    (V : Submodule ℂ (Lp E 2 (μ.prod ν))) (hV : IsClosed (V : Set (Lp E 2 (μ.prod ν))))
    (hrect : ∀ (A : Set Y) (B : Set Z) (hA : MeasurableSet A) (hB : MeasurableSet B)
      (hAf : μ A ≠ ∞) (hBf : ν B ≠ ∞) (e : E),
      indicatorConstLp 2 (hA.prod hB) (by rw [Measure.prod_prod]; exact ENNReal.mul_ne_top hAf hBf) e ∈ V) :
    V = ⊤ := by
  have hind (C : Set (Y × Z)) (hC : MeasurableSet C) (hCf : (μ.prod ν) C ≠ ∞) (e : E) :
      indicatorConstLp 2 hC hCf e ∈ V := by
    let R (n : ℕ) := spanningSets μ n ×ˢ spanningSets ν n
    have hR n : MeasurableSet (R n) := (measurableSet_spanningSets μ n).prod (measurableSet_spanningSets ν n)
    have hCR n : MeasurableSet (C ∩ R n) := hC.inter (hR n)
    have hf n : (μ.prod ν) (C ∩ R n) ≠ ∞ := ((measure_mono Set.inter_subset_left).trans_lt hCf.lt_top).ne
    apply hV.mem_of_tendsto (indicatorLp_tendsto (μ.prod ν) C C (fun n => C ∩ R n)
      hC hCf hC hCf hCR hf (fun _ => Set.inter_subset_left) ?_ e)
      (Eventually.of_forall (fun n => rectangle_indicator_restriction μ ν V hV hrect
        (spanningSets μ n) (spanningSets ν n) (measurableSet_spanningSets μ n)
        (measurableSet_spanningSets ν n) (measure_spanningSets_lt_top μ n).ne
        (measure_spanningSets_lt_top ν n).ne C hC e))
    intro p
    filter_upwards [eventually_mem_spanningSets μ p.1,eventually_mem_spanningSets ν p.2] with n hn hm
    simp [R,hn,hm]
  apply top_unique
  intro f _
  apply Lp.induction (p := 2) (μ := μ.prod ν) (by norm_num) (fun f => f ∈ V)
    (fun e C hC hCf => hind C hC hCf.ne e)
    (fun _ _ _ _ _ hf hg => V.add_mem hf hg) hV f

lemma productIsometry_surjective : Function.Surjective (productIsometry (E := E) μ ν) := by
  have hr : (productIsometry (E := E) μ ν).toLinearMap.range = ⊤ := by
    apply rectangle_dense_criterion μ ν _ (productIsometry μ ν).isometry.isClosedEmbedding.isClosed_range
    intro A B hA hB hAf hBf e
    exact ⟨indicatorConstLp 2 hA hAf (indicatorConstLp 2 hB hBf e),
      productIsometry_rectangle μ ν A B hA hB hAf hBf e⟩
  exact LinearMap.range_eq_top.mp hr

/-- The actual product unitary, obtained from simple functions and the proved dense range. -/
def productUnitary : Lp (Lp E 2 ν) 2 μ ≃ₗᵢ[ℂ] Lp E 2 (μ.prod ν) :=
  LinearIsometryEquiv.ofSurjective (productIsometry μ ν) (productIsometry_surjective μ ν)

lemma productUnitary_rectangle (A : Set Y) (B : Set Z)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAf : μ A ≠ ∞) (hBf : ν B ≠ ∞) (e : E) :
    productUnitary μ ν (indicatorConstLp 2 hA hAf (indicatorConstLp 2 hB hBf e)) =
      indicatorConstLp 2 (hA.prod hB) (by rw [Measure.prod_prod]; exact ENNReal.mul_ne_top hAf hBf) e :=
  productIsometry_rectangle μ ν A B hA hB hAf hBf e

lemma product_map_ext {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (A B : Lp E 2 (μ.prod ν) →L[ℂ] F)
    (h : ∀ (S : Set Y) (T : Set Z) (hS : MeasurableSet S) (hT : MeasurableSet T)
      (hSf : μ S ≠ ∞) (hTf : ν T ≠ ∞) (e : E),
      A (indicatorConstLp 2 (hS.prod hT) (by rw [Measure.prod_prod]; exact ENNReal.mul_ne_top hSf hTf) e) =
      B (indicatorConstLp 2 (hS.prod hT) (by rw [Measure.prod_prod]; exact ENNReal.mul_ne_top hSf hTf) e)) : A = B := by
  have ht : (A-B).ker = ⊤ := by
    apply rectangle_dense_criterion μ ν _ (A-B).isClosed_ker
    intro S T hS hT hSf hTf e
    change A _ - B _ = 0
    exact sub_eq_zero.mpr (h S T hS hT hSf hTf e)
  apply ContinuousLinearMap.ext
  intro f
  have hf : f ∈ (A-B).ker := ht ▸ Submodule.mem_top
  exact sub_eq_zero.mp hf

lemma productUnitary_natural {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F] (T : E →L[ℂ] F) (u : Lp (Lp E 2 ν) 2 μ) :
    productUnitary μ ν (amplify μ (amplify ν T) u) =
      amplify (μ.prod ν) T (productUnitary μ ν u) := by
  have h : (productUnitary (E := F) μ ν).toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((amplify μ (amplify ν T)).comp (productUnitary (E := E) μ ν).symm.toContinuousLinearEquiv.toContinuousLinearMap) =
      amplify (μ.prod ν) T := by
    apply product_map_ext μ ν
    intro A B hA hB hAf hBf e
    change productUnitary μ ν (amplify μ (amplify ν T)
      ((productUnitary μ ν).symm (indicatorConstLp 2 (hA.prod hB) (by rw [Measure.prod_prod]; exact ENNReal.mul_ne_top hAf hBf) e))) = _
    have hi : (productUnitary μ ν).symm (indicatorConstLp 2 (hA.prod hB) (by rw [Measure.prod_prod]; exact ENNReal.mul_ne_top hAf hBf) e) =
        indicatorConstLp 2 hA hAf (indicatorConstLp 2 hB hBf e) := by
      exact (congrArg (productUnitary (E := E) μ ν).symm
        (productUnitary_rectangle μ ν A B hA hB hAf hBf e)).symm.trans
        ((productUnitary (E := E) μ ν).symm_apply_apply _)
    rw [hi,amplify_indicator,amplify_indicator,productUnitary_rectangle,amplify_indicator]
  have he := congrArg (fun L => L (productUnitary μ ν u)) h
  change productUnitary μ ν (amplify μ (amplify ν T)
    ((productUnitary μ ν).symm (productUnitary μ ν u))) = _ at he
  simpa only [LinearIsometryEquiv.symm_apply_apply] using he

/-- Exchange of product coordinates, preserving the actual product measure. -/
def swapProduct : Lp E 2 (μ.prod ν) ≃ₗᵢ[ℂ] Lp E 2 (ν.prod μ) :=
  LinearIsometryEquiv.ofSurjective
    (Lp.compMeasurePreservingₗᵢ ℂ Prod.swap (Measure.measurePreserving_swap (μ := ν) (ν := μ)))
    (fun v => ⟨Lp.compMeasurePreserving Prod.swap (Measure.measurePreserving_swap (μ := μ) (ν := ν)) v, by
      change Lp.compMeasurePreserving Prod.swap (Measure.measurePreserving_swap (μ := ν) (ν := μ))
        (Lp.compMeasurePreserving Prod.swap (Measure.measurePreserving_swap (μ := μ) (ν := ν)) v) = v
      rw [← Lp.compMeasurePreserving_comp_apply]
      have he : Prod.swap ∘ (Prod.swap : Z × Y → Y × Z) = id := by funext p; rfl
      simp only [he,Lp.compMeasurePreserving_id_apply]⟩)

lemma swapProduct_ae (v : Lp E 2 (μ.prod ν)) :
    swapProduct μ ν v =ᵐ[ν.prod μ] fun p => v p.swap :=
  Lp.coeFn_compMeasurePreserving _ _

def reverseProduct : Lp (Lp E 2 ν) 2 μ ≃ₗᵢ[ℂ] Lp (Lp E 2 μ) 2 ν :=
  ((productUnitary μ ν).trans (swapProduct μ ν)).trans (productUnitary ν μ).symm

lemma productFunction_memLp (f : Lp ℂ 2 μ) (v : Lp E 2 ν) :
    MemLp (fun p : Y × Z => f p.1 • v p.2) 2 (μ.prod ν) := by
  apply (memLp_two_iff_integrable_sq_norm
    (((Lp.stronglyMeasurable f).comp_measurable measurable_fst).smul
      ((Lp.stronglyMeasurable v).comp_measurable measurable_snd)).aestronglyMeasurable).mpr
  exact ((Lp.memLp f).integrable_norm_pow (p := 2) (by norm_num) |>.mul_prod
    ((Lp.memLp v).integrable_norm_pow (p := 2) (by norm_num))).congr
    (Eventually.of_forall (fun p => by
      change ‖f p.1‖^2 * ‖v p.2‖^2 = ‖f p.1 • v p.2‖^2
      rw [norm_smul,mul_pow]))

def productFunction (f : Lp ℂ 2 μ) (v : Lp E 2 ν) : Lp E 2 (μ.prod ν) :=
  (productFunction_memLp μ ν f v).toLp _

lemma productFunction_ae (f : Lp ℂ 2 μ) (v : Lp E 2 ν) :
    productFunction μ ν f v =ᵐ[μ.prod ν] fun p => f p.1 • v p.2 := MemLp.coeFn_toLp _

lemma productFunction_norm (f : Lp ℂ 2 μ) (v : Lp E 2 ν) :
    ‖productFunction μ ν f v‖ = ‖f‖ * ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [GW.Analysis.l2_norm_sq (𝕜 := ℂ)]
  calc
    _ = ∫ p : Y × Z, ‖f p.1‖^2 * ‖v p.2‖^2 ∂μ.prod ν := by
      apply integral_congr_ae
      filter_upwards [productFunction_ae μ ν f v] with p hp
      rw [hp,norm_smul,mul_pow]
    _ = (∫ y, ‖f y‖^2 ∂μ) * (∫ z, ‖v z‖^2 ∂ν) := integral_prod_mul (μ := μ) (ν := ν) (fun y => ‖f y‖^2) (fun z => ‖v z‖^2)
    _ = (‖f‖ * ‖v‖)^2 := by rw [← GW.Analysis.l2_norm_sq (𝕜 := ℂ),← GW.Analysis.l2_norm_sq (𝕜 := ℂ)]; ring

lemma productFunction_add (f g : Lp ℂ 2 μ) (v : Lp E 2 ν) :
    productFunction μ ν (f+g) v = productFunction μ ν f v + productFunction μ ν g v := by
  apply Lp.ext
  filter_upwards [productFunction_ae μ ν (f+g) v,productFunction_ae μ ν f v,productFunction_ae μ ν g v,
    (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae (Lp.coeFn_add f g),
    Lp.coeFn_add (productFunction μ ν f v) (productFunction μ ν g v)] with p h₁ h₂ h₃ h₄ h₅
  simp only [Pi.add_apply] at h₄ h₅
  rw [h₁,h₄,h₅,h₂,h₃,add_smul]

lemma productFunction_smul (c : ℂ) (f : Lp ℂ 2 μ) (v : Lp E 2 ν) :
    productFunction μ ν (c • f) v = c • productFunction μ ν f v := by
  apply Lp.ext
  filter_upwards [productFunction_ae μ ν (c • f) v,productFunction_ae μ ν f v,
    (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae (Lp.coeFn_smul c f),
    Lp.coeFn_smul c (productFunction μ ν f v)] with p h₁ h₂ h₃ h₄
  simp only [Pi.smul_apply] at h₃ h₄
  rw [h₁,h₃,h₄,h₂,smul_smul,smul_eq_mul]

def productFunctionMap (v : Lp E 2 ν) : Lp ℂ 2 μ →L[ℂ] Lp E 2 (μ.prod ν) :=
  LinearMap.mkContinuous
    { toFun := fun f => productFunction μ ν f v
      map_add' := fun f g => productFunction_add μ ν f g v
      map_smul' := fun c f => productFunction_smul μ ν c f v }
    ‖v‖ (fun f => by
      change ‖productFunction μ ν f v‖ ≤ ‖v‖ * ‖f‖
      rw [productFunction_norm,mul_comm])

lemma productUnitary_tensor (f : Lp ℂ 2 μ) (v : Lp E 2 ν) :
    productUnitary μ ν (tensorEmbedding μ f v) = productFunction μ ν f v := by
  let L := (productUnitary μ ν).toContinuousLinearEquiv.toContinuousLinearMap.comp (ContinuousLinearMap.toSpanSingleton ℂ v |>.compLpL 2 μ)
  change L f = productFunctionMap μ ν v f
  apply Lp.induction (p := 2) (μ := μ) (by norm_num) (fun f => L f = productFunctionMap μ ν v f)
    ?_ ?_ (isClosed_eq L.continuous (productFunctionMap μ ν v).continuous) f
  · intro c A hA hAf
    change productUnitary μ ν ((ContinuousLinearMap.toSpanSingleton ℂ v).compLp
      (indicatorConstLp 2 hA hAf.ne c)) = productFunction μ ν (indicatorConstLp 2 hA hAf.ne c) v
    rw [compLp_indicatorConst]
    apply Lp.ext
    filter_upwards [productIsometry_indicator_ae μ ν A hA hAf.ne (c • v),
      productFunction_ae μ ν (indicatorConstLp 2 hA hAf.ne c) v,
      (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae
        (indicatorConstLp_coeFn (p := 2) (hs := hA) (hμs := hAf.ne) (c := c)),
      (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae (Lp.coeFn_smul c v)] with p h₁ h₂ h₃ h₄
    change productIsometry μ ν (indicatorConstLp 2 hA hAf.ne (c • v)) p = _
    rw [h₁,h₂,h₃]
    by_cases hp : p.1 ∈ A
    · simpa [hp] using h₄
    · simp [hp]
  · intro f g _ _ _ hf hg
    rw [map_add,map_add,hf,hg]

omit [CompleteSpace E] in
lemma product_slice_memLp (v : Lp E 2 (μ.prod ν)) :
    ∀ᵐ y ∂μ, MemLp (fun z => v (y,z)) 2 ν := by
  have hi := ((Lp.memLp v).integrable_norm_pow (p := 2) (by norm_num)).prod_right_ae
  filter_upwards [hi] with y hy
  exact (memLp_two_iff_integrable_sq_norm
    ((Lp.stronglyMeasurable v).comp_measurable measurable_prodMk_left).aestronglyMeasurable).mpr hy

def spectatorContractionRep (f : Lp ℂ 2 ν) (v : Lp E 2 (μ.prod ν)) (y : Y) : E :=
  ∫ z, (starRingEnd ℂ) (f z) • v (y,z) ∂ν

lemma spectatorContractionRep_strong (f : Lp ℂ 2 ν) (v : Lp E 2 (μ.prod ν)) :
    StronglyMeasurable (spectatorContractionRep μ ν f v) :=
  (((Lp.stronglyMeasurable f).star.comp_measurable measurable_snd).smul
    (Lp.stronglyMeasurable v)).integral_prod_right'

lemma spectatorContractionRep_bound (f : Lp ℂ 2 ν) (v : Lp E 2 (μ.prod ν)) :
    ∀ᵐ y ∂μ, ‖spectatorContractionRep μ ν f v y‖^2 ≤
      ‖f‖^2 * (∫ z, ‖v (y,z)‖^2 ∂ν) := by
  filter_upwards [product_slice_memLp μ ν v] with y hy
  let w := hy.toLp (fun z => v (y,z))
  have he : spectatorContractionRep μ ν f v y = contraction ν f w := by
    symm
    exact contractionValue_congr_ae ν f w Filter.EventuallyEq.rfl hy.coeFn_toLp
  have hn : ‖w‖^2 = ∫ z, ‖v (y,z)‖^2 ∂ν := by
    rw [GW.Analysis.l2_norm_sq (𝕜 := ℂ)]
    exact integral_congr_ae (hy.coeFn_toLp.mono (fun z hz => congrArg (fun e : E => ‖e‖^2) hz))
  have hb := (contraction ν f).le_opNorm w
  have hb' : ‖contraction ν f w‖ ≤ ‖f‖ * ‖w‖ :=
    hb.trans (mul_le_mul_of_nonneg_right (contraction_norm ν f) (norm_nonneg _))
  rw [he]
  nlinarith [norm_nonneg (contraction ν f w),norm_nonneg f,norm_nonneg w]

lemma spectatorContractionRep_memLp (f : Lp ℂ 2 ν) (v : Lp E 2 (μ.prod ν)) :
    MemLp (spectatorContractionRep μ ν f v) 2 μ := by
  apply (memLp_two_iff_integrable_sq_norm (spectatorContractionRep_strong μ ν f v).aestronglyMeasurable).mpr
  apply (((Lp.memLp v).integrable_norm_pow (p := 2) (by norm_num)).integral_prod_left.const_mul (‖f‖^2)).mono'
    ((spectatorContractionRep_strong μ ν f v).norm.pow 2).aestronglyMeasurable
  filter_upwards [spectatorContractionRep_bound μ ν f v] with y hy
  change ‖(‖spectatorContractionRep μ ν f v y‖^2 : ℝ)‖ ≤ _
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact hy

def spectatorContractionClass (f : Lp ℂ 2 ν) (v : Lp E 2 (μ.prod ν)) : Lp E 2 μ :=
  (spectatorContractionRep_memLp μ ν f v).toLp _

lemma spectatorContractionClass_ae (f : Lp ℂ 2 ν) (v : Lp E 2 (μ.prod ν)) :
    spectatorContractionClass μ ν f v =ᵐ[μ] spectatorContractionRep μ ν f v := MemLp.coeFn_toLp _

lemma slice_contraction_integrable (f : Lp ℂ 2 ν) {v : Z → E} (hv : MemLp v 2 ν) :
    Integrable (fun z => (starRingEnd ℂ) (f z) • v z) ν := by
  apply (contraction_integrable ν f (hv.toLp v)).congr
  exact hv.coeFn_toLp.mono (fun z hz => congrArg (fun e : E => (starRingEnd ℂ) (f z) • e) hz)

lemma spectatorContractionClass_norm (f : Lp ℂ 2 ν) (v : Lp E 2 (μ.prod ν)) :
    ‖spectatorContractionClass μ ν f v‖ ≤ ‖f‖ * ‖v‖ := by
  have hn : ‖spectatorContractionClass μ ν f v‖^2 ≤ ‖f‖^2 * ‖v‖^2 := by
    rw [GW.Analysis.l2_norm_sq (𝕜 := ℂ)]
    calc
      _ = ∫ y, ‖spectatorContractionRep μ ν f v y‖^2 ∂μ := by
        exact integral_congr_ae ((spectatorContractionClass_ae μ ν f v).mono
          (fun y hy => congrArg (fun e : E => ‖e‖^2) hy))
      _ ≤ ∫ y, ‖f‖^2 * (∫ z, ‖v (y,z)‖^2 ∂ν) ∂μ :=
        integral_mono_ae ((spectatorContractionRep_memLp μ ν f v).integrable_norm_pow (p := 2) (by norm_num))
          (((Lp.memLp v).integrable_norm_pow (p := 2) (by norm_num)).integral_prod_left.const_mul _)
          (spectatorContractionRep_bound μ ν f v)
      _ = ‖f‖^2 * ‖v‖^2 := by
        rw [integral_const_mul,← integral_prod _ ((Lp.memLp v).integrable_norm_pow (p := 2) (by norm_num)),
          ← GW.Analysis.l2_norm_sq (𝕜 := ℂ)]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg f) (norm_nonneg v))).mp
  simpa only [mul_pow] using hn

lemma spectatorContractionClass_add (f : Lp ℂ 2 ν) (v w : Lp E 2 (μ.prod ν)) :
    spectatorContractionClass μ ν f (v+w) = spectatorContractionClass μ ν f v + spectatorContractionClass μ ν f w := by
  apply Lp.ext
  filter_upwards [spectatorContractionClass_ae μ ν f (v+w),spectatorContractionClass_ae μ ν f v,
    spectatorContractionClass_ae μ ν f w,product_slice_memLp μ ν v,product_slice_memLp μ ν w,
    Measure.ae_ae_of_ae_prod (Lp.coeFn_add v w),
    Lp.coeFn_add (spectatorContractionClass μ ν f v) (spectatorContractionClass μ ν f w)] with y h₁ h₂ h₃ hv hw ha h₄
  simp only [Pi.add_apply] at h₄
  rw [h₁,h₄,h₂,h₃]
  change (∫ z, (starRingEnd ℂ) (f z) • (v+w) (y,z) ∂ν) = _
  calc
    _ = ∫ z, ((starRingEnd ℂ) (f z) • v (y,z) + (starRingEnd ℂ) (f z) • w (y,z)) ∂ν := by
      apply integral_congr_ae
      filter_upwards [ha] with z hz
      simp only [Pi.add_apply] at hz
      rw [hz,smul_add]
    _ = _ := integral_add (slice_contraction_integrable ν f hv) (slice_contraction_integrable ν f hw)

lemma spectatorContractionClass_smul (c : ℂ) (f : Lp ℂ 2 ν) (v : Lp E 2 (μ.prod ν)) :
    spectatorContractionClass μ ν f (c • v) = c • spectatorContractionClass μ ν f v := by
  apply Lp.ext
  filter_upwards [spectatorContractionClass_ae μ ν f (c • v),spectatorContractionClass_ae μ ν f v,
    Measure.ae_ae_of_ae_prod (Lp.coeFn_smul c v),
    Lp.coeFn_smul c (spectatorContractionClass μ ν f v)] with y h₁ h₂ ha h₃
  simp only [Pi.smul_apply] at h₃
  rw [h₁,h₃,h₂]
  change (∫ z, (starRingEnd ℂ) (f z) • (c • v) (y,z) ∂ν) = _
  calc
    _ = ∫ z, c • ((starRingEnd ℂ) (f z) • v (y,z)) ∂ν := by
      apply integral_congr_ae
      filter_upwards [ha] with z hz
      simp only [Pi.smul_apply] at hz
      rw [hz,smul_comm]
    _ = _ := integral_smul c _

def spectatorContraction (f : Lp ℂ 2 ν) : Lp E 2 (μ.prod ν) →L[ℂ] Lp E 2 μ :=
  LinearMap.mkContinuous
    { toFun := fun v => spectatorContractionClass μ ν f v
      map_add' := fun v w => spectatorContractionClass_add μ ν f v w
      map_smul' := fun c v => spectatorContractionClass_smul μ ν c f v }
    ‖f‖ (fun v => spectatorContractionClass_norm μ ν f v)

/-- The representative specified by the source assigns zero to exceptional non-L² slices. -/
def spectatorSection (f : Lp ℂ 2 ν) (v : Lp E 2 (μ.prod ν)) (y : Y) : E := by
  classical
  exact if MemLp (fun z => v (y,z)) 2 ν then spectatorContractionRep μ ν f v y else 0

lemma spectatorSection_exceptional (f : Lp ℂ 2 ν) (v : Lp E 2 (μ.prod ν)) (y : Y)
    (hy : ¬ MemLp (fun z => v (y,z)) 2 ν) : spectatorSection μ ν f v y = 0 := by
  simp only [spectatorSection,ite_eq_right hy]

lemma spectatorSection_ae (f : Lp ℂ 2 ν) (v : Lp E 2 (μ.prod ν)) :
    spectatorContraction μ ν f v =ᵐ[μ] spectatorSection μ ν f v := by
  apply (spectatorContractionClass_ae μ ν f v).trans
  filter_upwards [product_slice_memLp μ ν v] with y hy
  simp only [spectatorSection,ite_eq_left hy]

lemma spectatorSection_memLp (f : Lp ℂ 2 ν) (v : Lp E 2 (μ.prod ν)) :
    MemLp (spectatorSection μ ν f v) 2 μ :=
  MemLp.ae_eq (spectatorSection_ae μ ν f v) (Lp.memLp _)

lemma spectatorSection_toLp (f : Lp ℂ 2 ν) (v : Lp E 2 (μ.prod ν)) :
    (spectatorSection_memLp μ ν f v).toLp _ = spectatorContraction μ ν f v := by
  apply Lp.ext
  exact (MemLp.coeFn_toLp _).trans (spectatorSection_ae μ ν f v).symm

lemma spectatorContraction_norm (f : Lp ℂ 2 ν) : ‖spectatorContraction (E := E) μ ν f‖ ≤ ‖f‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (spectatorContractionClass_norm μ ν f)

lemma spectatorContraction_productFunction (f : Lp ℂ 2 ν) (γ : Lp ℂ 2 μ) (v : Lp E 2 ν) :
    spectatorContraction μ ν f (productFunction μ ν γ v) = tensorEmbedding μ γ (contraction ν f v) := by
  apply Lp.ext
  filter_upwards [spectatorContractionClass_ae μ ν f (productFunction μ ν γ v),
    Measure.ae_ae_of_ae_prod (productFunction_ae μ ν γ v),
    tensorEmbedding_ae μ γ (contraction ν f v)] with y h₁ ha h₂
  change spectatorContractionClass μ ν f (productFunction μ ν γ v) y = _
  rw [h₁,h₂]
  change (∫ z, (starRingEnd ℂ) (f z) • productFunction μ ν γ v (y,z) ∂ν) =
    γ y • (∫ z, (starRingEnd ℂ) (f z) • v z ∂ν)
  calc
    _ = ∫ z, γ y • ((starRingEnd ℂ) (f z) • v z) ∂ν := by
      apply integral_congr_ae
      filter_upwards [ha] with z hz
      rw [hz,smul_comm]
    _ = _ := integral_smul _ _

lemma productFunction_indicator (A : Set Y) (B : Set Z)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAf : μ A ≠ ∞) (hBf : ν B ≠ ∞) (e : E) :
    productFunction μ ν (indicatorConstLp 2 hA hAf (1 : ℂ)) (indicatorConstLp 2 hB hBf e) =
      indicatorConstLp 2 (hA.prod hB) (by rw [Measure.prod_prod]; exact ENNReal.mul_ne_top hAf hBf) e := by
  rw [← productUnitary_tensor,tensorEmbedding_apply,simpleTensor_indicatorConst,productUnitary_rectangle]

lemma spectatorContraction_identification (f : Lp ℂ 2 ν) (v : Lp E 2 (μ.prod ν)) :
    spectatorContraction μ ν f v = amplify μ (contraction (E := E) ν f) ((productUnitary (E := E) μ ν).symm v) := by
  have h : spectatorContraction (E := E) μ ν f = (amplify μ (contraction (E := E) ν f)).comp
      (productUnitary (E := E) μ ν).symm.toContinuousLinearEquiv.toContinuousLinearMap := by
    apply product_map_ext μ ν
    intro A B hA hB hAf hBf e
    have hi : (productUnitary (E := E) μ ν).symm
        (indicatorConstLp 2 (hA.prod hB) (by rw [Measure.prod_prod]; exact ENNReal.mul_ne_top hAf hBf) e) =
        indicatorConstLp 2 hA hAf (indicatorConstLp 2 hB hBf e) := by
      exact (congrArg (productUnitary (E := E) μ ν).symm
        (productUnitary_rectangle μ ν A B hA hB hAf hBf e)).symm.trans
        ((productUnitary (E := E) μ ν).symm_apply_apply _)
    change spectatorContraction μ ν f _ = amplify μ (contraction (E := E) ν f) ((productUnitary (E := E) μ ν).symm _)
    rw [hi,← productFunction_indicator μ ν A B hA hB hAf hBf e,
      spectatorContraction_productFunction,tensorEmbedding_apply,simpleTensor_indicatorConst,amplify_indicator]
  exact congrArg (fun T => T v) h

/-- A measure-preserving spectator change acts on the actual second product coordinate. -/
def spectatorPullback (ρ : Z → Z) (hρ : MeasurePreserving ρ ν ν) :
    Lp E 2 (μ.prod ν) →L[ℂ] Lp E 2 (μ.prod ν) :=
  (Lp.compMeasurePreservingₗᵢ ℂ (Prod.map id ρ) ((MeasurePreserving.id μ).prod hρ)).toContinuousLinearMap

lemma spectatorPullback_ae (ρ : Z → Z) (hρ : MeasurePreserving ρ ν ν) (v : Lp E 2 (μ.prod ν)) :
    spectatorPullback μ ν ρ hρ v =ᵐ[μ.prod ν] fun p => v (p.1,ρ p.2) :=
  Lp.coeFn_compMeasurePreserving _ _

lemma productUnitary_spectator (ρ : Z → Z) (hρ : MeasurePreserving ρ ν ν)
    (u : Lp (Lp E 2 ν) 2 μ) :
    productUnitary μ ν (amplify μ (Lp.compMeasurePreservingₗᵢ ℂ ρ hρ).toContinuousLinearMap u) =
      spectatorPullback μ ν ρ hρ (productUnitary μ ν u) := by
  let R : Lp E 2 ν →L[ℂ] Lp E 2 ν := (Lp.compMeasurePreservingₗᵢ ℂ ρ hρ).toContinuousLinearMap
  have h : (productUnitary μ ν).toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((amplify μ R).comp (productUnitary μ ν).symm.toContinuousLinearEquiv.toContinuousLinearMap) =
      spectatorPullback μ ν ρ hρ := by
    apply product_map_ext μ ν
    intro A B hA hB hAf hBf e
    have hB' : MeasurableSet (ρ ⁻¹' B) := hB.preimage hρ.measurable
    have hBf' : ν (ρ ⁻¹' B) ≠ ∞ := by rwa [hρ.measure_preimage hB.nullMeasurableSet]
    let hf : (μ.prod ν) (A ×ˢ B) ≠ ∞ := by rw [Measure.prod_prod]; exact ENNReal.mul_ne_top hAf hBf
    have hi : (productUnitary μ ν).symm (indicatorConstLp 2 (hA.prod hB) hf e) =
        indicatorConstLp 2 hA hAf (indicatorConstLp 2 hB hBf e) := by
      exact (congrArg (productUnitary (E := E) μ ν).symm
        (productUnitary_rectangle μ ν A B hA hB hAf hBf e)).symm.trans
        ((productUnitary (E := E) μ ν).symm_apply_apply _)
    have hR : R (indicatorConstLp 2 hB hBf e) = indicatorConstLp 2 hB' hBf' e :=
      Lp.indicatorConstLp_compMeasurePreserving hB hBf e hρ
    have hS : spectatorPullback μ ν ρ hρ (indicatorConstLp 2 (hA.prod hB) hf e) =
        indicatorConstLp 2 (hA.prod hB') (by rw [Measure.prod_prod]; exact ENNReal.mul_ne_top hAf hBf') e := by
      change Lp.compMeasurePreserving (Prod.map id ρ) ((MeasurePreserving.id μ).prod hρ) _ = _
      rw [Lp.indicatorConstLp_compMeasurePreserving]
      apply indicatorLp_set_congr
      ext p; rfl
    change productUnitary μ ν (amplify μ R ((productUnitary μ ν).symm _)) = _
    rw [hi,amplify_indicator,hR,productUnitary_rectangle,hS]
  have he := congrArg (fun L => L (productUnitary μ ν u)) h
  change productUnitary μ ν (amplify μ R ((productUnitary μ ν).symm (productUnitary μ ν u))) = _ at he
  simpa only [LinearIsometryEquiv.symm_apply_apply] using he

lemma amplify_tensor {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (T : E →L[ℂ] F) (γ : Lp ℂ 2 μ) (v : E) :
    amplify μ T (tensorEmbedding μ γ v) = tensorEmbedding μ γ (T v) := by
  apply Lp.ext
  filter_upwards [amplify_ae μ T (tensorEmbedding μ γ v),tensorEmbedding_ae μ γ v,
    tensorEmbedding_ae μ γ (T v)] with y h₁ h₂ h₃
  rw [h₁,h₂,h₃,map_smul]

/-- Bounded action in a single factor under the proved actual product identifications. -/
def factorAmplification {W F : Type*} [MeasurableSpace W]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (ξ : Measure W) [SigmaFinite ξ] (T : Lp E 2 ν →L[ℂ] Lp F 2 ξ) :
    Lp E 2 (μ.prod ν) →L[ℂ] Lp F 2 (μ.prod ξ) :=
  (productUnitary μ ξ).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((amplify μ T).comp (productUnitary μ ν).symm.toContinuousLinearEquiv.toContinuousLinearMap)

lemma factorAmplification_product {W F : Type*} [MeasurableSpace W]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (ξ : Measure W) [SigmaFinite ξ] (T : Lp E 2 ν →L[ℂ] Lp F 2 ξ)
    (γ : Lp ℂ 2 μ) (v : Lp E 2 ν) :
    factorAmplification μ ν ξ T (productFunction μ ν γ v) = productFunction μ ξ γ (T v) := by
  change productUnitary μ ξ (amplify μ T ((productUnitary μ ν).symm (productFunction μ ν γ v))) = _
  rw [← productUnitary_tensor,LinearIsometryEquiv.symm_apply_apply,amplify_tensor,productUnitary_tensor]

end ProductSimple
instance sectorMeasure_sigmaFinite (n : ℕ) : SigmaFinite (sectorMeasure n) := by
  unfold sectorMeasure
  infer_instance

section SymmetricAmplification
variable {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)

def symmetricInclusion (n : ℕ) : (symmetricSector n) →ₗᵢ[ℂ] AmbientSector n :=
  (symmetricSector n).toSubmodule.subtypeₗᵢ

def symmetricProjection (n : ℕ) : AmbientSector n →L[ℂ] (symmetricSector n) :=
  LinearMap.mkContinuous
    { toFun := fun v => ⟨symmetrizer n v,symmetrizer_mem n v⟩
      map_add' := fun u v => Subtype.ext (map_add (symmetrizer n) u v)
      map_smul' := fun c v => Subtype.ext (map_smul (symmetrizer n) c v) }
    1 (fun v => by simpa using symmetrizer_norm_le n v)

lemma amplifiedSymmetric_range (n : ℕ) (u : Lp (AmbientSector n) 2 μ) :
    (∃ v : Lp (symmetricSector n) 2 μ,
      amplify μ (symmetricInclusion n).toContinuousLinearMap v = u) ↔
      amplify μ (symmetrizer n) u = u := by
  constructor
  · rintro ⟨v,rfl⟩
    apply Lp.ext
    filter_upwards [amplify_ae μ (symmetrizer n) (amplify μ (symmetricInclusion n).toContinuousLinearMap v),
      amplify_ae μ (symmetricInclusion n).toContinuousLinearMap v] with y h₁ h₂
    rw [h₁,h₂]
    exact symmetrizer_of_fixed n (v y) (v y).property
  · intro hu
    refine ⟨amplify μ (symmetricProjection n) u,?_⟩
    apply Lp.ext
    filter_upwards [amplify_ae μ (symmetricInclusion n).toContinuousLinearMap (amplify μ (symmetricProjection n) u),
      amplify_ae μ (symmetricProjection n) u,amplify_ae μ (symmetrizer n) u] with y h₁ h₂ h₃
    rw [h₁,h₂]
    change symmetrizer n (u y) = u y
    rw [← h₃,hu]

lemma amplifiedSymmetric_fixed (n : ℕ) (u : Lp (AmbientSector n) 2 μ) :
    amplify μ (symmetrizer n) u = u ↔
      ∀ τ : Equiv.Perm (Fin n), amplify μ (permutationL2 n τ).toContinuousLinearMap u = u := by
  constructor
  · intro hu τ
    apply Lp.ext
    filter_upwards [amplify_ae μ (symmetrizer n) u,
      amplify_ae μ (permutationL2 n τ).toContinuousLinearMap u] with y hs hp
    rw [hu] at hs
    rw [hp]
    change permutationL2 n τ (u y) = u y
    rw [hs]
    exact symmetrizer_fixed n τ (u y)
  · intro hu
    have hτ (τ : Equiv.Perm (Fin n)) : ∀ᵐ y ∂μ, permutationL2 n τ (u y) = u y := by
      have h := amplify_ae μ (permutationL2 n τ).toContinuousLinearMap u
      rw [hu τ] at h
      exact h.symm
    apply Lp.ext
    filter_upwards [ae_all_iff.mpr hτ,amplify_ae μ (symmetrizer n) u] with y hy hs
    rw [hs]
    exact symmetrizer_of_fixed n (u y) hy

lemma amplifiedSymmetric_norm (n : ℕ) (v : Lp (symmetricSector n) 2 μ) :
    ‖amplify μ (symmetricInclusion n).toContinuousLinearMap v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [GW.Analysis.l2_norm_sq (𝕜 := ℂ),GW.Analysis.l2_norm_sq (𝕜 := ℂ)]
  apply integral_congr_ae
  filter_upwards [amplify_ae μ (symmetricInclusion n).toContinuousLinearMap v] with y hy
  rw [hy]
  exact congrArg (fun r : ℝ => r^2) ((symmetricInclusion n).norm_map (v y))


variable [SigmaFinite μ]

def symmetricProductInclusion (n : ℕ) : Lp (symmetricSector n) 2 μ →ₗᵢ[ℂ]
    Lp ℂ 2 (μ.prod (sectorMeasure n)) :=
  (productUnitary μ (sectorMeasure n)).toLinearIsometry.comp
    { toLinearMap := (amplify μ (symmetricInclusion n).toContinuousLinearMap).toLinearMap
      norm_map' := amplifiedSymmetric_norm μ n }

lemma symmetricProduct_closed (n : ℕ) : IsClosed (Set.range (symmetricProductInclusion μ n)) :=
  (symmetricProductInclusion μ n).isometry.isClosedEmbedding.isClosed_range

def productPermutation (n : ℕ) (τ : Equiv.Perm (Fin n)) :
    Lp ℂ 2 (μ.prod (sectorMeasure n)) →L[ℂ] Lp ℂ 2 (μ.prod (sectorMeasure n)) :=
  spectatorPullback μ (sectorMeasure n) (coordinatePermutation n τ) (coordinatePermutation_preserving n τ)

lemma productPermutation_ae (n : ℕ) (τ : Equiv.Perm (Fin n))
    (v : Lp ℂ 2 (μ.prod (sectorMeasure n))) :
    productPermutation μ n τ v =ᵐ[μ.prod (sectorMeasure n)]
      fun p => v (p.1,fun i => p.2 (τ i)) := by
  simpa only [productPermutation,coordinatePermutation_eq] using
    spectatorPullback_ae μ (sectorMeasure n) (coordinatePermutation n τ) (coordinatePermutation_preserving n τ) v

lemma symmetricProduct_range (n : ℕ) (v : Lp ℂ 2 (μ.prod (sectorMeasure n))) :
    v ∈ Set.range (symmetricProductInclusion μ n) ↔ ∀ τ : Equiv.Perm (Fin n), productPermutation μ n τ v = v := by
  let U := productUnitary (E := ℂ) μ (sectorMeasure n)
  have hperm (τ : Equiv.Perm (Fin n)) (u : Lp (AmbientSector n) 2 μ) :
      U (amplify μ (permutationL2 n τ).toContinuousLinearMap u) = productPermutation μ n τ (U u) :=
    productUnitary_spectator μ (sectorMeasure n) (coordinatePermutation n τ) (coordinatePermutation_preserving n τ) u
  constructor
  · rintro ⟨w,rfl⟩ τ
    change productPermutation μ n τ (U (amplify μ (symmetricInclusion n).toContinuousLinearMap w)) =
      U (amplify μ (symmetricInclusion n).toContinuousLinearMap w)
    rw [← hperm]
    have hf := (amplifiedSymmetric_range μ n _).mp ⟨w,rfl⟩
    rw [(amplifiedSymmetric_fixed μ n _).mp hf τ]
  · intro hv
    have hf : amplify μ (symmetrizer n) (U.symm v) = U.symm v := by
      apply (amplifiedSymmetric_fixed μ n _).mpr
      intro τ
      apply U.injective
      rw [hperm,LinearIsometryEquiv.apply_symm_apply,hv τ]
    obtain ⟨w,hw⟩ := (amplifiedSymmetric_range μ n _).mpr hf
    refine ⟨w,?_⟩
    change U (amplify μ (symmetricInclusion n).toContinuousLinearMap w) = v
    rw [hw,LinearIsometryEquiv.apply_symm_apply]


lemma amplifiedSymmetrizer_average (n : ℕ) (u : Lp (AmbientSector n) 2 μ) :
    amplify μ (symmetrizer n) u = ((n.factorial : ℂ)⁻¹) •
      ∑ τ : Equiv.Perm (Fin n), amplify μ (permutationL2 n τ).toContinuousLinearMap u := by
  change amplificationLinear μ (((n.factorial : ℂ)⁻¹) •
    ∑ τ : Equiv.Perm (Fin n), (permutationL2 n τ).toContinuousLinearMap) u = _
  rw [map_smul,map_sum]
  simp only [smul_apply,sum_apply]
  rfl

def productSymmetrizer (n : ℕ) : Lp ℂ 2 (μ.prod (sectorMeasure n)) →L[ℂ]
    Lp ℂ 2 (μ.prod (sectorMeasure n)) :=
  (productUnitary μ (sectorMeasure n)).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((amplify μ (symmetrizer n)).comp
      (productUnitary μ (sectorMeasure n)).symm.toContinuousLinearEquiv.toContinuousLinearMap)

lemma productSymmetrizer_average (n : ℕ) (v : Lp ℂ 2 (μ.prod (sectorMeasure n))) :
    productSymmetrizer μ n v = ((n.factorial : ℂ)⁻¹) •
      ∑ τ : Equiv.Perm (Fin n), productPermutation μ n τ v := by
  change productUnitary μ (sectorMeasure n)
    (amplify μ (symmetrizer n) ((productUnitary μ (sectorMeasure n)).symm v)) = _
  rw [amplifiedSymmetrizer_average,map_smul,map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro τ _
  exact (productUnitary_spectator μ (sectorMeasure n) (coordinatePermutation n τ)
    (coordinatePermutation_preserving n τ) ((productUnitary μ (sectorMeasure n)).symm v)).trans
    (congrArg (productPermutation μ n τ) (LinearIsometryEquiv.apply_symm_apply _ _))

/-- This is the exact positive-sector electron/product map on the existing physical sector. -/
def electronSectorProduct (n : ℕ) : ElectronSector (n+1) →ₗᵢ[ℂ]
    Lp ℂ 2 ((volume : Measure GW.Space).prod (sectorMeasure (n+1))) :=
  symmetricProductInclusion volume (n+1)

lemma electronSectorProduct_range (n : ℕ)
    (v : Lp ℂ 2 ((volume : Measure GW.Space).prod (sectorMeasure (n+1)))) :
    v ∈ Set.range (electronSectorProduct n) ↔
      ∀ τ : Equiv.Perm (Fin (n+1)), productPermutation volume (n+1) τ v = v :=
  symmetricProduct_range volume (n+1) v

/-- Vacuum fibers remain scalars, separately from positive-sector splitting. -/
def vacuumElectronIdentification : ElectronSector 0 ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure GW.Space) :=
  LinearIsometryEquiv.refl ℂ _
end SymmetricAmplification

end GW.Fock
