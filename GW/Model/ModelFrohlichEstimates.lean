module
public import GW.Model.Coefficient
public import GW.Model.ModelPowerIntegrals
public import GW.Analysis.L2Quotient
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
@[expose] public section
noncomputable section
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
namespace GW.Model

def highRegion (K : ℝ) : Set GW.Space := {k | K < ‖k‖}
def lowRegion (K : ℝ) : Set GW.Space := {k | ‖k‖ ≤ K}

lemma highRegion_measurable (K : ℝ) : MeasurableSet (highRegion K) :=
  measurableSet_lt measurable_const measurable_norm

lemma lowRegion_measurable (K : ℝ) : MeasurableSet (lowRegion K) :=
  measurableSet_le measurable_norm measurable_const

lemma v_norm_sq (α : ℝ) (hα : 0 ≤ α) (k : GW.Space) :
    ‖(v α k : ℂ)‖^2 = α / ‖k‖^2 := by
  rw [Complex.norm_real,Real.norm_of_nonneg (v_nonneg α k),v_sq hα]

lemma cutoff_sq_lintegral (α R : ℝ) (hα : 0 ≤ α) :
    (∫⁻ k, ENNReal.ofReal (‖(cutoff α R k : ℂ)‖^2) ∂(volume : Measure GW.Space)) =
      ENNReal.ofReal α * interiorPowerIntegral 2 R := by
  let s : Set GW.Space := {k | 0 < ‖k‖ ∧ ‖k‖ ≤ R}
  have hs : MeasurableSet s := (measurableSet_lt measurable_const measurable_norm).inter (lowRegion_measurable R)
  have he (k : GW.Space) : ENNReal.ofReal (‖(cutoff α R k : ℂ)‖^2) =
      s.indicator (fun k => ENNReal.ofReal α * ENNReal.ofReal (‖k‖ ^ (-(2:ℝ)))) k := by
    by_cases h₀ : k = 0
    · subst k; simp [cutoff,s]
    by_cases hk : ‖k‖ ≤ R
    · have hmem : k ∈ s := ⟨norm_pos_iff.mpr h₀,hk⟩
      rw [Set.indicator_of_mem hmem,cutoff,if_pos hk,v_norm_sq α hα,
        Real.rpow_neg (norm_nonneg _),Real.rpow_ofNat,← ENNReal.ofReal_mul hα,div_eq_mul_inv]
    · have hmem : k ∉ s := fun h => hk h.2
      rw [Set.indicator_of_notMem hmem,cutoff,if_neg hk]
      simp
  simp_rw [he]
  rw [lintegral_indicator hs,lintegral_const_mul _ (by fun_prop)]
  rfl

lemma cutoff_sq_bound (α R : ℝ) (hα : 0 ≤ α) (hR : 0 < R) :
    (∫⁻ k, ENNReal.ofReal (‖(cutoff α R k : ℂ)‖^2) ∂(volume : Measure GW.Space)) ≤
      ENNReal.ofReal (7*unitBallVolume*α*R) := by
  rw [cutoff_sq_lintegral α R hα]
  refine (show ENNReal.ofReal α * interiorPowerIntegral 2 R ≤
    ENNReal.ofReal α * ENNReal.ofReal (7*unitBallVolume*R) by gcongr; exact interiorPowerIntegral_two_bound hR).trans_eq ?_
  rw [← ENNReal.ofReal_mul hα]
  congr 1
  ring

lemma cutoff_memLp (α R : ℝ) (hα : 0 ≤ α) (hR : 0 < R) :
    MemLp (fun k => (cutoff α R k : ℂ)) 2 (volume : Measure GW.Space) := by
  have hm : AEStronglyMeasurable (fun k => (cutoff α R k : ℂ)) (volume : Measure GW.Space) :=
    (Complex.continuous_ofReal.measurable.comp (cutoff_measurable α R)).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  refine ⟨hm.norm.pow 2,?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun _ => sq_nonneg _))).mpr
  exact (cutoff_sq_bound α R hα hR).trans_lt ENNReal.ofReal_lt_top

def cutoffL2 (α R : ℝ) (hα : 0 ≤ α) (hR : 0 < R) : GW.OnePhonon :=
  (cutoff_memLp α R hα hR).toLp _

lemma cutoffL2_ae (α R : ℝ) (hα : 0 ≤ α) (hR : 0 < R) :
    cutoffL2 α R hα hR =ᵐ[(volume : Measure GW.Space)] fun k => (cutoff α R k : ℂ) :=
  MemLp.coeFn_toLp _

lemma cutoffL2_norm_sq (α R : ℝ) (hα : 0 ≤ α) (hR : 0 < R) :
    ‖cutoffL2 α R hα hR‖^2 ≤ 7*unitBallVolume*α*R := by
  apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) unitBallVolume_pos.le) hα) hR.le)).mp
  rw [GW.Analysis.l2_norm_sq (𝕜 := ℂ),ofReal_integral_eq_lintegral_ofReal
    ((Lp.memLp (cutoffL2 α R hα hR)).integrable_norm_pow (p := 2) (by norm_num))
    (Eventually.of_forall (fun _ => sq_nonneg _))]
  exact (lintegral_congr_ae ((cutoffL2_ae α R hα hR).mono
    (fun k hk => congrArg (fun z : ℂ => ENNReal.ofReal (‖z‖^2)) hk))).trans_le
      (cutoff_sq_bound α R hα hR)

def coefficientDTailENN (α K : ℝ) : ℝ≥0∞ :=
  ∫⁻ k in highRegion K, ENNReal.ofReal ((v α k)^2/‖k‖^2) ∂(volume : Measure GW.Space)

def coefficientETailENN (α K : ℝ) : ℝ≥0∞ :=
  ∫⁻ k in highRegion K, ENNReal.ofReal ((v α k)^2/(1+‖k‖^2)) ∂(volume : Measure GW.Space)

def coefficientConvolutionENN (α K : ℝ) (q : GW.Space) : ℝ≥0∞ :=
  ∫⁻ k in highRegion K, ENNReal.ofReal ((v α k)^2/(1+‖q-k‖^2)) ∂(volume : Measure GW.Space)

lemma coefficientDTailENN_eq (α K : ℝ) (hα : 0 ≤ α) :
    coefficientDTailENN α K = ENNReal.ofReal α * exteriorPowerIntegral 4 K := by
  unfold coefficientDTailENN exteriorPowerIntegral radialPowerIntegral
  rw [← lintegral_const_mul _ (by fun_prop)]
  apply lintegral_congr
  intro k
  rw [v_sq hα,div_div,← pow_add,← ENNReal.ofReal_mul hα,Real.rpow_neg (norm_nonneg _),
    Real.rpow_ofNat]
  rfl

lemma coefficientDTailENN_bound (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) :
    coefficientDTailENN α K ≤ ENNReal.ofReal (14*unitBallVolume*α/K) := by
  rw [coefficientDTailENN_eq α K hα]
  refine (show ENNReal.ofReal α * exteriorPowerIntegral 4 K ≤
    ENNReal.ofReal α * ENNReal.ofReal (14*unitBallVolume/K) by gcongr; exact exteriorPowerIntegral_four_bound hK).trans_eq ?_
  rw [← ENNReal.ofReal_mul hα]
  congr 1
  ring

lemma coefficientETailENN_le_D (α K : ℝ) :
    coefficientETailENN α K ≤ coefficientDTailENN α K := by
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem (μ := (volume : Measure GW.Space)) (highRegion_measurable K)] with k hk
  apply ENNReal.ofReal_le_ofReal
  by_cases h : 0 < ‖k‖
  · exact div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos h) (by linarith)
  · have he : k = 0 := norm_eq_zero.mp (le_antisymm (le_of_not_gt h) (norm_nonneg _))
    simp [he]

def convolutionTailFactor (K : ℝ) (k : GW.Space) : ℝ :=
  (highRegion K).indicator (fun k => (‖k‖^2)⁻¹) k

def convolutionResolventFactor (k : GW.Space) : ℝ := (1+‖k‖^2)⁻¹

lemma convolutionTailFactor_measurable (K : ℝ) : Measurable (convolutionTailFactor K) :=
  ((measurable_norm.pow_const 2).inv).indicator (highRegion_measurable K)

lemma convolutionResolventFactor_measurable : Measurable convolutionResolventFactor := by
  unfold convolutionResolventFactor
  fun_prop

lemma convolutionTailFactor_nonneg (K : ℝ) (k : GW.Space) : 0 ≤ convolutionTailFactor K k := by
  by_cases hk : k ∈ highRegion K
  · rw [convolutionTailFactor,Set.indicator_of_mem hk]
    positivity
  · simp [convolutionTailFactor,hk]

lemma convolutionResolventFactor_nonneg (k : GW.Space) : 0 ≤ convolutionResolventFactor k := by
  unfold convolutionResolventFactor
  positivity

lemma convolutionTailFactor_sq (K : ℝ) :
    (∫⁻ k, ENNReal.ofReal (convolutionTailFactor K k ^ 2) ∂(volume : Measure GW.Space)) =
      exteriorPowerIntegral 4 K := by
  have h (k : GW.Space) :
      ENNReal.ofReal (convolutionTailFactor K k ^ 2) =
        (highRegion K).indicator (fun k => ENNReal.ofReal (‖k‖^(-(4:ℝ)))) k := by
    by_cases hk : k ∈ highRegion K
    · rw [convolutionTailFactor,Set.indicator_of_mem hk,Set.indicator_of_mem hk,
        Real.rpow_neg (norm_nonneg _),Real.rpow_ofNat,inv_pow,← pow_mul]
    · simp [convolutionTailFactor,hk]
  simp_rw [h]
  rw [lintegral_indicator (highRegion_measurable K)]
  rfl

lemma convolutionResolventFactor_sq_bound :
    (∫⁻ k, ENNReal.ofReal (convolutionResolventFactor k ^ 2) ∂(volume : Measure GW.Space)) ≤
      ENNReal.ofReal (15*unitBallVolume) := by
  let s := lowRegion 1
  let t := highRegion 1
  have hs : MeasurableSet s := lowRegion_measurable 1
  have ht : sᶜ = t := by
    ext k
    change (¬ ‖k‖ ≤ (1:ℝ)) ↔ 1 < ‖k‖
    exact not_le
  rw [← lintegral_add_compl _ hs,ht]
  have hlo :
      (∫⁻ k in s, ENNReal.ofReal (convolutionResolventFactor k ^ 2) ∂(volume : Measure GW.Space)) ≤
        ENNReal.ofReal unitBallVolume := by
    have h : (∫⁻ _k in s, (1:ℝ≥0∞) ∂(volume : Measure GW.Space)) =
        ENNReal.ofReal unitBallVolume := by
      rw [setLIntegral_one]
      have hset : s = closedBall (0 : GW.Space) 1 := by
        ext k
        change ‖k‖ ≤ (1:ℝ) ↔ dist k 0 ≤ 1
        rw [dist_zero_right]
      rw [hset]
      simpa using spaceClosedBallVolume 1 zero_lt_one
    rw [← h]
    apply lintegral_mono
    intro k
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    have hb : convolutionResolventFactor k ≤ 1 := by
      unfold convolutionResolventFactor
      exact inv_le_one_of_one_le₀ (by linarith [sq_nonneg ‖k‖])
    simpa using pow_le_pow_left₀ (convolutionResolventFactor_nonneg k) hb 2
  have hhi :
      (∫⁻ k in t, ENNReal.ofReal (convolutionResolventFactor k ^ 2) ∂(volume : Measure GW.Space)) ≤
        exteriorPowerIntegral 4 1 := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem (μ := (volume : Measure GW.Space)) (highRegion_measurable 1)] with k hk
    apply ENNReal.ofReal_le_ofReal
    have hpos : 0 < ‖k‖ := zero_lt_one.trans hk
    have hb : convolutionResolventFactor k ≤ (‖k‖^2)⁻¹ := by
      apply inv_anti₀ (sq_pos_of_pos hpos)
      linarith
    rw [Real.rpow_neg (norm_nonneg _),Real.rpow_ofNat,show (4:ℕ) = 2*2 by decide,pow_mul,← inv_pow]
    exact pow_le_pow_left₀ (convolutionResolventFactor_nonneg k) hb 2
  refine (add_le_add hlo (hhi.trans (exteriorPowerIntegral_four_bound zero_lt_one))).trans_eq ?_
  rw [← ENNReal.ofReal_add unitBallVolume_pos.le (div_nonneg (mul_nonneg (by norm_num) unitBallVolume_pos.le) zero_le_one)]
  congr 1
  ring

lemma real_memLp_of_sq_lintegral {f : GW.Space → ℝ} (hf : Measurable f)
    (h : (∫⁻ k, ENNReal.ofReal (f k^2) ∂(volume : Measure GW.Space)) < ∞) :
    MemLp f 2 (volume : Measure GW.Space) := by
  apply (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr
  exact ⟨(hf.pow_const 2).aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun k => sq_nonneg (f k)))).mpr h⟩

lemma convolutionTailFactor_memLp (K : ℝ) (hK : 0 < K) :
    MemLp (convolutionTailFactor K) 2 (volume : Measure GW.Space) :=
  real_memLp_of_sq_lintegral (convolutionTailFactor_measurable K) (by
    rw [convolutionTailFactor_sq]
    exact (exteriorPowerIntegral_finite_iff hK 4).mpr (by norm_num))

lemma convolutionResolventFactor_memLp :
    MemLp convolutionResolventFactor 2 (volume : Measure GW.Space) :=
  real_memLp_of_sq_lintegral convolutionResolventFactor_measurable
    (convolutionResolventFactor_sq_bound.trans_lt ENNReal.ofReal_lt_top)

def convolutionReflection (q : GW.Space) : GW.Space ≃ᵐ GW.Space where
  toFun k := q-k
  invFun k := q-k
  left_inv k := sub_sub_cancel q k
  right_inv k := sub_sub_cancel q k
  measurable_toFun := by
    change Measurable (fun k : GW.Space => q-k)
    exact measurable_const.sub measurable_id
  measurable_invFun := by
    change Measurable (fun k : GW.Space => q-k)
    exact measurable_const.sub measurable_id

lemma convolutionReflection_preserving (q : GW.Space) :
    MeasurePreserving (convolutionReflection q) (volume : Measure GW.Space) volume := by
  letI : (volume : Measure GW.Space).IsNegInvariant :=
    ⟨(LinearIsometryEquiv.neg ℝ (E := GW.Space)).measurePreserving.map_eq⟩
  exact (volume : Measure GW.Space).measurePreserving_sub_left q

lemma convolutionShiftFactor_memLp (q : GW.Space) :
    MemLp (fun k => convolutionResolventFactor (q-k)) 2 (volume : Measure GW.Space) :=
  convolutionResolventFactor_memLp.comp_measurePreserving (convolutionReflection_preserving q)

lemma convolutionShiftFactor_integral_sq (q : GW.Space) :
    (∫ k, convolutionResolventFactor (q-k)^2 ∂(volume : Measure GW.Space)) =
      ∫ k, convolutionResolventFactor k^2 ∂(volume : Measure GW.Space) :=
  (convolutionReflection_preserving q).integral_comp' (fun k => convolutionResolventFactor k^2)

lemma real_integral_sq_le_of_lintegral_le {f : GW.Space → ℝ}
    (hf : MemLp f 2 (volume : Measure GW.Space)) {C : ℝ} (hC : 0 ≤ C)
    (h : (∫⁻ k, ENNReal.ofReal (f k^2) ∂(volume : Measure GW.Space)) ≤ ENNReal.ofReal C) :
    (∫ k, f k^2 ∂(volume : Measure GW.Space)) ≤ C := by
  have hi := (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mp hf
  apply (ENNReal.ofReal_le_ofReal_iff hC).mp
  rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun _ => sq_nonneg _))]
  exact h

lemma convolutionFactors_integrable (K : ℝ) (hK : 0 < K) (q : GW.Space) :
    Integrable (fun k => convolutionTailFactor K k * convolutionResolventFactor (q-k)) (volume : Measure GW.Space) :=
  (convolutionTailFactor_memLp K hK).integrable_mul (convolutionShiftFactor_memLp q)

lemma convolutionFactors_integral_bound (K : ℝ) (hK : 0 < K) (q : GW.Space) :
    (∫ k, convolutionTailFactor K k * convolutionResolventFactor (q-k) ∂(volume : Measure GW.Space)) ≤
      Real.sqrt (14*unitBallVolume/K) * Real.sqrt (15*unitBallVolume) := by
  have hf : MemLp (convolutionTailFactor K) (ENNReal.ofReal (2:ℝ)) (volume : Measure GW.Space) := by
    simpa only [ENNReal.ofReal_ofNat] using convolutionTailFactor_memLp K hK
  have hg : MemLp (fun k => convolutionResolventFactor (q-k)) (ENNReal.ofReal (2:ℝ)) (volume : Measure GW.Space) := by
    simpa only [ENNReal.ofReal_ofNat] using convolutionShiftFactor_memLp q
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg
    (show (2:ℝ).HolderConjugate 2 by rw [Real.holderConjugate_iff]; norm_num)
    (Eventually.of_forall (convolutionTailFactor_nonneg K))
    (Eventually.of_forall (fun k => convolutionResolventFactor_nonneg (q-k))) hf hg
  simp only [Real.rpow_two,← Real.sqrt_eq_rpow] at h
  apply h.trans
  apply mul_le_mul _ _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  · apply Real.sqrt_le_sqrt
    apply real_integral_sq_le_of_lintegral_le (convolutionTailFactor_memLp K hK)
      (div_nonneg (mul_nonneg (by norm_num) unitBallVolume_pos.le) hK.le)
    rw [convolutionTailFactor_sq]
    exact exteriorPowerIntegral_four_bound hK
  · apply Real.sqrt_le_sqrt
    rw [convolutionShiftFactor_integral_sq]
    exact real_integral_sq_le_of_lintegral_le convolutionResolventFactor_memLp
      (mul_nonneg (by norm_num) unitBallVolume_pos.le) convolutionResolventFactor_sq_bound

def convolutionConstant : ℝ := Real.sqrt 210 * unitBallVolume

lemma convolutionConstant_nonneg : 0 ≤ convolutionConstant :=
  mul_nonneg (Real.sqrt_nonneg _) unitBallVolume_pos.le

lemma convolutionConstants_exact (K : ℝ) (hK : 0 < K) :
    Real.sqrt (14*unitBallVolume/K) * Real.sqrt (15*unitBallVolume) =
      convolutionConstant * K^(-(1/2):ℝ) := by
  have hA : 0 ≤ 14*unitBallVolume/K := div_nonneg (mul_nonneg (by norm_num) unitBallVolume_pos.le) hK.le
  have hL : 0 ≤ 15*unitBallVolume := mul_nonneg (by norm_num) unitBallVolume_pos.le
  rw [Real.rpow_neg hK.le,← Real.sqrt_eq_rpow]
  apply (sq_eq_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (mul_nonneg convolutionConstant_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)))).mp
  rw [mul_pow,Real.sq_sqrt hA,Real.sq_sqrt hL,mul_pow,inv_pow,Real.sq_sqrt hK.le,
    convolutionConstant,mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 210)]
  ring

lemma coefficientConvolutionENN_integral (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (q : GW.Space) :
    coefficientConvolutionENN α K q =
      ENNReal.ofReal (α * ∫ k, convolutionTailFactor K k * convolutionResolventFactor (q-k)
        ∂(volume : Measure GW.Space)) := by
  have hi := (convolutionFactors_integrable K hK q).const_mul α
  have hnon : ∀ᵐ k ∂(volume : Measure GW.Space),
      0 ≤ α * (convolutionTailFactor K k * convolutionResolventFactor (q-k)) :=
    Eventually.of_forall (fun k => mul_nonneg hα
      (mul_nonneg (convolutionTailFactor_nonneg K k) (convolutionResolventFactor_nonneg (q-k))))
  rw [← integral_const_mul,ofReal_integral_eq_lintegral_ofReal hi hnon]
  unfold coefficientConvolutionENN
  rw [← lintegral_indicator (highRegion_measurable K)]
  apply lintegral_congr
  intro k
  by_cases hk : k ∈ highRegion K
  · rw [Set.indicator_of_mem hk,convolutionTailFactor,Set.indicator_of_mem hk,
      convolutionResolventFactor,v_sq hα,div_eq_mul_inv,div_eq_mul_inv,mul_assoc]
  · rw [Set.indicator_of_notMem hk,convolutionTailFactor,Set.indicator_of_notMem hk,zero_mul,mul_zero,
      ENNReal.ofReal_zero]

lemma coefficientConvolutionENN_bound (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (q : GW.Space) :
    coefficientConvolutionENN α K q ≤ ENNReal.ofReal (convolutionConstant * α * K^(-(1/2):ℝ)) := by
  rw [coefficientConvolutionENN_integral α K hα hK]
  apply ENNReal.ofReal_le_ofReal
  have h := convolutionFactors_integral_bound K hK q
  rw [convolutionConstants_exact K hK] at h
  calc
    _ ≤ α * (convolutionConstant * K^(-(1/2):ℝ)) := mul_le_mul_of_nonneg_left h hα
    _ = _ := by ring

def coefficientDTail (α K : ℝ) : ℝ := (coefficientDTailENN α K).toReal
def coefficientETail (α K : ℝ) : ℝ := (coefficientETailENN α K).toReal
def coefficientConvolution (α K : ℝ) (q : GW.Space) : ℝ := (coefficientConvolutionENN α K q).toReal

def coefficientTTail (α K : ℝ) : ℝ := sSup (Set.range (coefficientConvolution α K))

lemma coefficientDTailENN_finite (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) :
    coefficientDTailENN α K ≠ ∞ :=
  ((coefficientDTailENN_bound α K hα hK).trans_lt ENNReal.ofReal_lt_top).ne

lemma coefficientETailENN_finite (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) :
    coefficientETailENN α K ≠ ∞ :=
  ((coefficientETailENN_le_D α K).trans_lt (lt_top_iff_ne_top.mpr (coefficientDTailENN_finite α K hα hK))).ne

lemma coefficientConvolutionENN_finite (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (q : GW.Space) :
    coefficientConvolutionENN α K q ≠ ∞ :=
  ((coefficientConvolutionENN_bound α K hα hK q).trans_lt ENNReal.ofReal_lt_top).ne

lemma coefficientConvolution_bound (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (q : GW.Space) :
    coefficientConvolution α K q ≤ convolutionConstant * α * K^(-(1/2):ℝ) := by
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (coefficientConvolutionENN_bound α K hα hK q)).trans_eq
    (ENNReal.toReal_ofReal (mul_nonneg (mul_nonneg convolutionConstant_nonneg hα)
      (Real.rpow_nonneg hK.le _)))

lemma coefficientConvolution_range_nonempty (α K : ℝ) :
    (Set.range (coefficientConvolution α K)).Nonempty := ⟨_,0,rfl⟩

lemma coefficientConvolution_range_bddAbove (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) :
    BddAbove (Set.range (coefficientConvolution α K)) :=
  ⟨_,fun x ⟨q,hq⟩ => hq ▸ coefficientConvolution_bound α K hα hK q⟩

lemma coefficientConvolution_le_T (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (q : GW.Space) :
    coefficientConvolution α K q ≤ coefficientTTail α K :=
  le_csSup (coefficientConvolution_range_bddAbove α K hα hK) ⟨q,rfl⟩

lemma coefficientTTail_nonneg (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) :
    0 ≤ coefficientTTail α K :=
  ENNReal.toReal_nonneg.trans (coefficientConvolution_le_T α K hα hK 0)

lemma coefficientTTail_bound (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) :
    coefficientTTail α K ≤ convolutionConstant * α * K^(-(1/2):ℝ) :=
  csSup_le (coefficientConvolution_range_nonempty α K)
    (fun x ⟨q,hq⟩ => hq ▸ coefficientConvolution_bound α K hα hK q)

lemma coefficientDTail_nonneg (α K : ℝ) : 0 ≤ coefficientDTail α K := ENNReal.toReal_nonneg
lemma coefficientETail_nonneg (α K : ℝ) : 0 ≤ coefficientETail α K := ENNReal.toReal_nonneg

lemma coefficientETail_le_D (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) :
    coefficientETail α K ≤ coefficientDTail α K :=
  ENNReal.toReal_mono (coefficientDTailENN_finite α K hα hK) (coefficientETailENN_le_D α K)

lemma coefficientDTail_bound (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) :
    coefficientDTail α K ≤ 14*unitBallVolume*α/K := by
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (coefficientDTailENN_bound α K hα hK)).trans_eq
    (ENNReal.toReal_ofReal (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) unitBallVolume_pos.le) hα) hK.le))

lemma highRegion_antitone : Antitone highRegion := fun _ _ h _ hk => h.trans_lt hk

lemma coefficientDTail_antitone (α : ℝ) (hα : 0 ≤ α) {K₁ K₂ : ℝ} (hK₁ : 0 < K₁) (hK : K₁ ≤ K₂) :
    coefficientDTail α K₂ ≤ coefficientDTail α K₁ := by
  apply ENNReal.toReal_mono (coefficientDTailENN_finite α K₁ hα hK₁)
  exact lintegral_mono' (Measure.restrict_mono (highRegion_antitone hK) le_rfl) le_rfl

lemma coefficientETail_antitone (α : ℝ) (hα : 0 ≤ α) {K₁ K₂ : ℝ} (hK₁ : 0 < K₁) (hK : K₁ ≤ K₂) :
    coefficientETail α K₂ ≤ coefficientETail α K₁ := by
  apply ENNReal.toReal_mono (coefficientETailENN_finite α K₁ hα hK₁)
  exact lintegral_mono' (Measure.restrict_mono (highRegion_antitone hK) le_rfl) le_rfl

lemma coefficientConvolution_antitone (α : ℝ) (hα : 0 ≤ α) {K₁ K₂ : ℝ}
    (hK₁ : 0 < K₁) (hK : K₁ ≤ K₂) (q : GW.Space) :
    coefficientConvolution α K₂ q ≤ coefficientConvolution α K₁ q := by
  apply ENNReal.toReal_mono (coefficientConvolutionENN_finite α K₁ hα hK₁ q)
  exact lintegral_mono' (Measure.restrict_mono (highRegion_antitone hK) le_rfl) le_rfl

lemma coefficientTTail_antitone (α : ℝ) (hα : 0 ≤ α) {K₁ K₂ : ℝ} (hK₁ : 0 < K₁) (hK : K₁ ≤ K₂) :
    coefficientTTail α K₂ ≤ coefficientTTail α K₁ := by
  apply csSup_le (coefficientConvolution_range_nonempty α K₂)
  rintro _ ⟨q,rfl⟩
  exact (coefficientConvolution_antitone α hα hK₁ hK q).trans (coefficientConvolution_le_T α K₁ hα hK₁ q)

lemma coefficientDTail_tendsto (α : ℝ) (hα : 0 ≤ α) : Tendsto (coefficientDTail α) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (coefficientDTail_nonneg α))
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with K hK
    exact coefficientDTail_bound α K hα hK
  · have h := (tendsto_rpow_neg_atTop (show 0 < (1:ℝ) by norm_num)).const_mul (14*unitBallVolume*α)
    change Tendsto (fun K : ℝ => 14*unitBallVolume*α/K) atTop (𝓝 0)
    simpa only [Real.rpow_neg_one,div_eq_mul_inv,mul_zero] using h

lemma coefficientETail_tendsto (α : ℝ) (hα : 0 ≤ α) : Tendsto (coefficientETail α) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (coefficientETail_nonneg α)) _ (coefficientDTail_tendsto α hα)
  filter_upwards [eventually_gt_atTop (0:ℝ)] with K hK
  exact coefficientETail_le_D α K hα hK

lemma coefficientTTail_tendsto (α : ℝ) (hα : 0 ≤ α) : Tendsto (coefficientTTail α) atTop (𝓝 0) := by
  have ht := (tendsto_rpow_neg_atTop (show 0 < (1/2:ℝ) by norm_num)).const_mul (convolutionConstant*α)
  rw [mul_zero] at ht
  apply squeeze_zero' _ _ ht
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with K hK
    exact coefficientTTail_nonneg α K hα hK
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with K hK
    exact coefficientTTail_bound α K hα hK

lemma cutoff_sq_restrict (α R : ℝ) :
    (∫⁻ k in lowRegion R, ENNReal.ofReal ((v α k)^2) ∂(volume : Measure GW.Space)) =
      ∫⁻ k, ENNReal.ofReal (‖(cutoff α R k : ℂ)‖^2) ∂(volume : Measure GW.Space) := by
  rw [← lintegral_indicator (lowRegion_measurable R)]
  apply lintegral_congr
  intro k
  by_cases hk : k ∈ lowRegion R
  · have hk' : ‖k‖ ≤ R := hk
    rw [Set.indicator_of_mem hk,cutoff,if_pos hk',Complex.norm_real,Real.norm_of_nonneg (v_nonneg α k)]
  · have hk' : ¬ ‖k‖ ≤ R := hk
    rw [Set.indicator_of_notMem hk,cutoff,if_neg hk']
    simp

def coefficientWeightedIntegralENN (α : ℝ) : ℝ≥0∞ :=
  ∫⁻ k, ENNReal.ofReal ((v α k)^2/(1+‖k‖^2)) ∂(volume : Measure GW.Space)

lemma coefficientWeightedIntegralENN_bound (α : ℝ) (hα : 0 ≤ α) :
    coefficientWeightedIntegralENN α ≤ ENNReal.ofReal (21*unitBallVolume*α) := by
  unfold coefficientWeightedIntegralENN
  rw [← lintegral_add_compl _ (lowRegion_measurable 1)]
  have hset : (lowRegion 1)ᶜ = highRegion 1 := by
    ext k
    change (¬ ‖k‖ ≤ (1:ℝ)) ↔ 1 < ‖k‖
    exact not_le
  rw [hset]
  have hl :
      (∫⁻ k in lowRegion 1, ENNReal.ofReal ((v α k)^2/(1+‖k‖^2)) ∂(volume : Measure GW.Space)) ≤
        ENNReal.ofReal (7*unitBallVolume*α) := by
    calc
      _ ≤ ∫⁻ k in lowRegion 1, ENNReal.ofReal ((v α k)^2) ∂(volume : Measure GW.Space) := by
        apply lintegral_mono
        intro k
        apply ENNReal.ofReal_le_ofReal
        exact div_le_self (sq_nonneg _) (by linarith [sq_nonneg ‖k‖])
      _ ≤ _ := by
        rw [cutoff_sq_restrict]
        simpa only [mul_one] using cutoff_sq_bound α 1 hα zero_lt_one
  have hh : coefficientETailENN α 1 ≤ ENNReal.ofReal (14*unitBallVolume*α) := by
    exact (coefficientETailENN_le_D α 1).trans (by
      simpa only [div_one] using coefficientDTailENN_bound α 1 hα zero_lt_one)
  refine (add_le_add hl hh).trans_eq ?_
  rw [← ENNReal.ofReal_add (mul_nonneg (mul_nonneg (by norm_num) unitBallVolume_pos.le) hα)
    (mul_nonneg (mul_nonneg (by norm_num) unitBallVolume_pos.le) hα)]
  congr 1
  ring

lemma coefficientWeightedIntegralENN_finite (α : ℝ) (hα : 0 ≤ α) :
    coefficientWeightedIntegralENN α < ∞ :=
  (coefficientWeightedIntegralENN_bound α hα).trans_lt ENNReal.ofReal_lt_top

lemma coefficient_zero_coupling (K : ℝ) :
    coefficientDTail 0 K = 0 ∧ coefficientETail 0 K = 0 ∧ coefficientTTail 0 K = 0 ∧
    coefficientWeightedIntegralENN 0 = 0 ∧ ∀ q, coefficientConvolutionENN 0 K q = 0 := by
  have ht (q : GW.Space) : coefficientConvolutionENN 0 K q = 0 := by simp [coefficientConvolutionENN]
  refine ⟨by simp [coefficientDTail,coefficientDTailENN],
    by simp [coefficientETail,coefficientETailENN],?_,by simp [coefficientWeightedIntegralENN],ht⟩
  unfold coefficientTTail
  have he : coefficientConvolution 0 K = fun _ : GW.Space => (0:ℝ) := by
    funext q
    simp [coefficientConvolution,ht]
  rw [he]
  simp

lemma nonnegative_realIntegral_of_lintegral {μ : Measure GW.Space} {g : GW.Space → ℝ}
    (hg : Measurable g) (h₀ : ∀ k, 0 ≤ g k)
    (hf : (∫⁻ k, ENNReal.ofReal (g k) ∂μ) ≠ ∞) :
    Integrable g μ ∧ (∫ k, g k ∂μ) = (∫⁻ k, ENNReal.ofReal (g k) ∂μ).toReal := by
  have hnon : ∀ᵐ k ∂μ, 0 ≤ g k := Eventually.of_forall h₀
  have hi : Integrable g μ :=
    ⟨hg.aestronglyMeasurable,(hasFiniteIntegral_iff_ofReal hnon).mpr (lt_top_iff_ne_top.mpr hf)⟩
  refine ⟨hi,?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hi hnon,ENNReal.toReal_ofReal (integral_nonneg h₀)]

lemma coefficientDTail_eq_integral (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) :
    coefficientDTail α K = ∫ k in highRegion K, (v α k)^2/‖k‖^2 ∂(volume : Measure GW.Space) := by
  exact (nonnegative_realIntegral_of_lintegral
    (((v_measurable α).pow_const 2).div (measurable_norm.pow_const 2))
    (fun k => div_nonneg (sq_nonneg _) (sq_nonneg _))
    (coefficientDTailENN_finite α K hα hK)).2.symm

lemma coefficientETail_eq_integral (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) :
    coefficientETail α K = ∫ k in highRegion K, (v α k)^2/(1+‖k‖^2) ∂(volume : Measure GW.Space) := by
  exact (nonnegative_realIntegral_of_lintegral
    (((v_measurable α).pow_const 2).div (measurable_const.add (measurable_norm.pow_const 2)))
    (fun k => div_nonneg (sq_nonneg _) (add_nonneg zero_le_one (sq_nonneg _)))
    (coefficientETailENN_finite α K hα hK)).2.symm

lemma coefficientConvolution_eq_integral (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (q : GW.Space) :
    coefficientConvolution α K q =
      ∫ k in highRegion K, (v α k)^2/(1+‖q-k‖^2) ∂(volume : Measure GW.Space) := by
  exact (nonnegative_realIntegral_of_lintegral
    (((v_measurable α).pow_const 2).div
      (measurable_const.add ((measurable_const.sub measurable_id).norm.pow_const 2)))
    (fun k => div_nonneg (sq_nonneg _) (add_nonneg zero_le_one (sq_nonneg _)))
    (coefficientConvolutionENN_finite α K hα hK q)).2.symm

lemma coefficientWeightedIntegral_bound (α : ℝ) (hα : 0 ≤ α) :
    (∫ k, (v α k)^2/(1+‖k‖^2) ∂(volume : Measure GW.Space)) ≤ 21*unitBallVolume*α := by
  have he := (nonnegative_realIntegral_of_lintegral
    (((v_measurable α).pow_const 2).div (measurable_const.add (measurable_norm.pow_const 2)))
    (fun k => div_nonneg (sq_nonneg _) (add_nonneg zero_le_one (sq_nonneg _)))
    (coefficientWeightedIntegralENN_finite α hα).ne).2
  exact he.le.trans ((ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (coefficientWeightedIntegralENN_bound α hα)).trans_eq
    (ENNReal.toReal_ofReal (mul_nonneg (mul_nonneg (by norm_num) unitBallVolume_pos.le) hα)))

lemma cutoffL2_zero_coupling (R : ℝ) (hR : 0 < R) :
    cutoffL2 0 R le_rfl hR = 0 := by
  apply Lp.ext
  filter_upwards [cutoffL2_ae 0 R le_rfl hR,Lp.coeFn_zero ℂ 2 (volume : Measure GW.Space)]
    with k hk hz
  rw [hk,hz]
  simp [cutoff]

end GW.Model
