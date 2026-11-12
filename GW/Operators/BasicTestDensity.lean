module
public import GW.Analysis.BridgePhaseDerivative
public import GW.Analysis.BridgeShear
public import GW.Analysis.BridgeSmoothConvolution
public import GW.Analysis.RealMultiplier
public import GW.Fock.FockAmplification
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
@[expose] public section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace ENNReal
namespace GW.Analysis

def testDensityBump : ContDiffBump (0 : GW.Space) := ⟨1,2,by norm_num,by norm_num⟩

def testMollifier : GW.Space → ℝ := testDensityBump.normed volume

lemma testMollifier_nonneg (x : GW.Space) : 0 ≤ testMollifier x :=
  testDensityBump.nonneg_normed x

lemma testMollifier_contDiff : ContDiff ℝ ∞ testMollifier := testDensityBump.contDiff_normed

lemma testMollifier_integrable : Integrable testMollifier (volume : Measure GW.Space) :=
  testDensityBump.integrable_normed

lemma testMollifier_integral : (∫ x, testMollifier x ∂(volume : Measure GW.Space)) = 1 :=
  testDensityBump.integral_normed

lemma testMollifier_support : tsupport testMollifier = Metric.closedBall (0 : GW.Space) 2 :=
  testDensityBump.tsupport_normed_eq

def testMollifierScaled (ε : ℝ) (x : GW.Space) : ℝ := (ε^3)⁻¹ * testMollifier (ε⁻¹ • x)

lemma testMollifierScaled_nonneg (ε : ℝ) (hε : 0 < ε) (x : GW.Space) :
    0 ≤ testMollifierScaled ε x :=
  mul_nonneg (inv_nonneg.mpr (pow_nonneg hε.le _)) (testMollifier_nonneg _)

lemma testMollifierScaled_contDiff (ε : ℝ) : ContDiff ℝ ∞ (testMollifierScaled ε) := by
  unfold testMollifierScaled
  exact contDiff_const.mul (testMollifier_contDiff.comp (contDiff_id.const_smul ε⁻¹))

lemma testMollifierScaled_support_subset (ε : ℝ) (hε : 0 < ε) :
    tsupport (testMollifierScaled ε) ⊆ Metric.closedBall (0 : GW.Space) (2*ε) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  apply Metric.mem_closedBall.mpr
  rw [dist_zero_right]
  have ht : ε⁻¹ • x ∈ tsupport testMollifier := by
    apply subset_tsupport
    intro hz
    exact hx (by unfold testMollifierScaled; rw [hz,mul_zero])
  rw [testMollifier_support,Metric.mem_closedBall,dist_zero_right,norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr hε.le)] at ht
  rw [inv_mul_eq_div] at ht
  exact (div_le_iff₀ hε).mp ht

lemma testMollifierScaled_hasCompactSupport (ε : ℝ) (hε : 0 < ε) :
    HasCompactSupport (testMollifierScaled ε) :=
  (isCompact_closedBall _ _).of_isClosed_subset isClosed_closure (testMollifierScaled_support_subset ε hε)

lemma testMollifierScaled_integral (ε : ℝ) (hε : 0 < ε) :
    (∫ x, testMollifierScaled ε x ∂(volume : Measure GW.Space)) = 1 := by
  unfold testMollifierScaled
  rw [integral_const_mul,scale_integral ε⁻¹ (inv_ne_zero hε.ne') testMollifier
    testMollifier_contDiff.continuous.stronglyMeasurable,testMollifier_integral]
  rw [mul_one,abs_of_nonneg (inv_nonneg.mpr (pow_nonneg (inv_nonneg.mpr hε.le) _))]
  rw [inv_pow]
  exact mul_inv_cancel₀ (inv_ne_zero (pow_ne_zero _ hε.ne'))

lemma modulation_phaseAt (y : GW.Space) (u : GW.OnePhonon) : modulation y u = phaseAt u y := by
  apply Lp.ext
  filter_upwards [modulation_ae y u,phaseAt_ae u y] with q h₁ h₂
  rw [h₁,h₂,physicalPhase_comm y q,smul_eq_mul]

lemma translation_continuous_scalar (u : GW.OnePhonon) :
    Continuous (fun y : GW.Space => translation y u) := by
  have he : (fun y : GW.Space => translation y u) =
      fun y => physicalFourierUnitary.symm (phaseAt (physicalFourierUnitary u) y) := by
    funext y
    apply physicalFourierUnitary.injective
    rw [LinearIsometryEquiv.apply_symm_apply,physicalFourier_translation,modulation_phaseAt]
  rw [he]
  exact physicalFourierUnitary.symm.continuous.comp (phaseAt_continuous _)

lemma translation_zero_scalar (u : GW.OnePhonon) : translation (0 : GW.Space) u = u := by
  apply Lp.ext
  simpa only [sub_zero] using translation_ae (0 : GW.Space) u

def mollifiedTranslationIntegrand (u : GW.OnePhonon) (ε : ℝ) (y : GW.Space) : GW.OnePhonon :=
  testMollifier y • translation (ε • y) u

lemma mollifiedTranslationIntegrand_continuous (u : GW.OnePhonon) (ε : ℝ) :
    Continuous (mollifiedTranslationIntegrand u ε) := by
  unfold mollifiedTranslationIntegrand
  exact testMollifier_contDiff.continuous.smul
    ((translation_continuous_scalar u).comp (continuous_const_smul ε))

lemma mollifiedTranslationIntegrand_norm (u : GW.OnePhonon) (ε : ℝ) (y : GW.Space) :
    ‖mollifiedTranslationIntegrand u ε y‖ = testMollifier y * ‖u‖ := by
  unfold mollifiedTranslationIntegrand
  rw [norm_smul,Real.norm_of_nonneg (testMollifier_nonneg y),(translation (ε • y)).norm_map]

lemma mollifiedTranslationIntegrand_integrable (u : GW.OnePhonon) (ε : ℝ) :
    Integrable (mollifiedTranslationIntegrand u ε) volume := by
  apply (testMollifier_integrable.mul_const ‖u‖).mono'
    (mollifiedTranslationIntegrand_continuous u ε).aestronglyMeasurable
  exact Eventually.of_forall (fun y => (mollifiedTranslationIntegrand_norm u ε y).le)

def mollifiedTranslation (u : GW.OnePhonon) (ε : ℝ) : GW.OnePhonon :=
  ∫ y, mollifiedTranslationIntegrand u ε y ∂(volume : Measure GW.Space)

lemma mollifiedTranslation_zero (u : GW.OnePhonon) : mollifiedTranslation u 0 = u := by
  unfold mollifiedTranslation mollifiedTranslationIntegrand
  simp_rw [zero_smul,translation_zero_scalar]
  rw [integral_smul_const,testMollifier_integral,one_smul]

lemma mollifiedTranslation_continuous (u : GW.OnePhonon) : Continuous (mollifiedTranslation u) := by
  apply continuous_iff_seqContinuous.mpr
  intro f ε h
  exact tendsto_integral_of_dominated_convergence (fun y => testMollifier y * ‖u‖)
    (fun n => (mollifiedTranslationIntegrand_continuous u (f n)).aestronglyMeasurable)
    (testMollifier_integrable.mul_const ‖u‖)
    (fun n => Eventually.of_forall (fun y => (mollifiedTranslationIntegrand_norm u (f n) y).le))
    (Eventually.of_forall (fun y => by
      have hc : Continuous (fun δ : ℝ => mollifiedTranslationIntegrand u δ y) := by
        unfold mollifiedTranslationIntegrand
        have hL : Continuous (fun δ : ℝ => δ • y) := continuous_id.smul continuous_const
        exact ((translation_continuous_scalar u).comp hL).const_smul (testMollifier y)
      have hh : Tendsto (fun δ : ℝ => mollifiedTranslationIntegrand u δ y) (𝓝 ε)
          (𝓝 (mollifiedTranslationIntegrand u ε y)) := hc.continuousAt
      exact hh.comp h))

lemma mollifiedTranslation_tendsto (u : GW.OnePhonon) :
    Tendsto (mollifiedTranslation u) (𝓝[>] (0:ℝ)) (𝓝 u) := by
  have h : Tendsto (mollifiedTranslation u) (𝓝 (0:ℝ)) (𝓝 (mollifiedTranslation u 0)) :=
    (mollifiedTranslation_continuous u).continuousAt
  rw [mollifiedTranslation_zero] at h
  exact h.mono_left nhdsWithin_le_nhds

def mollifierPairingProduct (u g : GW.OnePhonon) (ε : ℝ) (p : GW.Space × GW.Space) : ℂ :=
  (testMollifier p.2 : ℂ) * ⟪g p.1,u (p.1-ε • p.2)⟫_ℂ

lemma mollifierPairingProduct_measurable (u g : GW.OnePhonon) (ε : ℝ) :
    Measurable (mollifierPairingProduct u g ε) := by
  unfold mollifierPairingProduct
  have hu : Measurable (fun p : GW.Space × GW.Space => u (p.1-ε • p.2)) :=
    (Lp.stronglyMeasurable u).measurable.comp
    (measurable_fst.sub (measurable_const_smul ε |>.comp measurable_snd))
  have hg : Measurable (fun p : GW.Space × GW.Space => g p.1) :=
    (Lp.stronglyMeasurable g).measurable.comp measurable_fst
  have hr : Measurable (fun p : GW.Space × GW.Space => (testMollifier p.2 : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp (testMollifier_contDiff.continuous.measurable.comp measurable_snd)
  simp only [RCLike.inner_apply']
  exact hr.mul ((Complex.continuous_conj.measurable.comp hg).mul hu)

lemma mollifierPairingProduct_integrable (u g : GW.OnePhonon) (ε : ℝ) :
    Integrable (mollifierPairingProduct u g ε) ((volume : Measure GW.Space).prod volume) := by
  have hm : AEStronglyMeasurable (mollifierPairingProduct u g ε) ((volume : Measure GW.Space).prod volume) :=
    (mollifierPairingProduct_measurable u g ε).aestronglyMeasurable
  apply (integrable_prod_iff' hm).mpr
  constructor
  · apply Eventually.of_forall
    intro y
    have he : (fun x => ⟪g x,translation (ε • y) u x⟫_ℂ) =ᵐ[volume]
        (fun x => ⟪g x,u (x-ε • y)⟫_ℂ) :=
      (translation_ae (ε • y) u).mono (fun x hx => congrArg (fun z : ℂ => ⟪g x,z⟫_ℂ) hx)
    exact ((L2.integrable_inner g (translation (ε • y) u)).congr he).const_mul (testMollifier y : ℂ)
  · apply ((testMollifier_integrable.mul_const ‖g‖).mul_const ‖u‖).mono'
      hm.norm.prod_swap.integral_prod_right'
    apply Eventually.of_forall
    intro y
    have h (x : GW.Space) : ‖mollifierPairingProduct u g ε (x,y)‖ =
        testMollifier y * (‖g x‖ * ‖u (x-ε • y)‖) := by
      unfold mollifierPairingProduct
      change ‖(testMollifier y : ℂ) * ⟪g x,u (x-ε • y)⟫_ℂ‖ = _
      rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (testMollifier_nonneg y),RCLike.inner_apply',
        norm_mul,Complex.norm_conj]
    have hI : (∫ x, ‖mollifierPairingProduct u g ε (x,y)‖ ∂(volume : Measure GW.Space)) =
        testMollifier y * ∫ x, ‖g x‖ * ‖u (x-ε • y)‖ ∂(volume : Measure GW.Space) :=
      (integral_congr_ae (Eventually.of_forall h)).trans (integral_const_mul _ _)
    change ‖∫ x, ‖mollifierPairingProduct u g ε (x,y)‖ ∂(volume : Measure GW.Space)‖ ≤ _
    rw [hI]
    have hb := GW.Fock.normProduct_integral_le (volume : Measure GW.Space) g (translation (ε • y) u)
    rw [(translation (ε • y)).norm_map] at hb
    have he : (∫ x, ‖g x‖ * ‖u (x-ε • y)‖ ∂(volume : Measure GW.Space)) =
        ∫ x, ‖g x‖ * ‖translation (ε • y) u x‖ ∂(volume : Measure GW.Space) := by
      apply integral_congr_ae
      exact (translation_ae (ε • y) u).mono (fun x hx => by
        change ‖g x‖ * ‖u (x-ε • y)‖ = ‖g x‖ * ‖translation (ε • y) u x‖
        rw [hx])
    rw [he,Real.norm_of_nonneg (mul_nonneg (testMollifier_nonneg y)
      (integral_nonneg (fun x => mul_nonneg (norm_nonneg (g x)) (norm_nonneg (translation (ε • y) u x)))))]
    exact (mul_le_mul_of_nonneg_left hb (testMollifier_nonneg y)).trans_eq (mul_assoc _ _ _).symm

lemma mollifiedTranslation_pairing (u g : GW.OnePhonon) (ε : ℝ) :
    ⟪g,mollifiedTranslation u ε⟫_ℂ =
      ∫ p, mollifierPairingProduct u g ε p ∂((volume : Measure GW.Space).prod volume) := by
  let L := innerSL ℂ g
  change L (∫ y, mollifiedTranslationIntegrand u ε y ∂(volume : Measure GW.Space)) = _
  rw [← L.integral_comp_comm (mollifiedTranslationIntegrand_integrable u ε),
    integral_prod_symm _ (mollifierPairingProduct_integrable u g ε)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro y
  change ⟪g,testMollifier y • translation (ε • y) u⟫_ℂ = _
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ),inner_smul_right,L2.inner_def]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact (translation_ae (ε • y) u).mono (fun x hx => by
    change _ * ⟪g x,translation (ε • y) u x⟫_ℂ = _ * ⟪g x,u (x-ε • y)⟫_ℂ
    rw [hx]
    rfl)

lemma mollifier_pullback_ae {E : Type*} {f g : GW.Space → E}
    (h : f =ᵐ[(volume : Measure GW.Space)] g) (ε : ℝ) :
    (fun p : GW.Space × GW.Space => f (p.1-ε • p.2)) =ᵐ[(volume : Measure GW.Space).prod volume]
      (fun p : GW.Space × GW.Space => g (p.1-ε • p.2)) := by
  have hq : QuasiMeasurePreserving (Prod.fst : GW.Space × GW.Space → GW.Space)
      ((volume : Measure GW.Space).prod (volume : Measure GW.Space)) (volume : Measure GW.Space) :=
    Measure.quasiMeasurePreserving_fst
  have hm := hq.comp (momentumShear_preserving (-ε)).quasiMeasurePreserving
  have he := hm.ae_eq_comp h
  simpa only [Function.comp_def,momentumShear_apply,neg_smul,sub_eq_add_neg] using he

lemma testReflection_preserving (x : GW.Space) :
    MeasurePreserving (fun y : GW.Space => x-y) (volume : Measure GW.Space) volume := by
  letI : (volume : Measure GW.Space).IsNegInvariant :=
    ⟨(LinearIsometryEquiv.neg ℝ (E := GW.Space)).measurePreserving.map_eq⟩
  exact (volume : Measure GW.Space).measurePreserving_sub_left x

lemma testMollifierPointwise_integrable (u : GW.OnePhonon) (hu : Integrable (u : GW.Space → ℂ) volume)
    (ε : ℝ) (hε : 0 < ε) (x : GW.Space) :
    Integrable (fun y => testMollifier y • u (x-ε • y)) (volume : Measure GW.Space) := by
  have hi : Integrable (fun y : GW.Space => u (x-y)) (volume : Measure GW.Space) :=
    (testReflection_preserving x).integrable_comp_of_integrable hu
  have hscale : Integrable (fun y : GW.Space => u (x-ε • y)) (volume : Measure GW.Space) :=
    (integrable_comp_smul_iff volume (fun y : GW.Space => u (x-y)) hε.ne').mpr hi
  have hs : HasCompactSupport testMollifier := testDensityBump.hasCompactSupport_normed
  obtain ⟨C,hC⟩ := hs.exists_bound_of_continuous testMollifier_contDiff.continuous
  apply (hscale.norm.const_mul C).mono'
    (testMollifier_contDiff.continuous.stronglyMeasurable.aestronglyMeasurable.smul hscale.1)
  exact Eventually.of_forall (fun y => by
    change ‖testMollifier y • u (x-ε • y)‖ ≤ _
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (hC y) (norm_nonneg _))

lemma testMollifierPointwise_eq (u : GW.OnePhonon) (ε : ℝ) (hε : 0 < ε) (x : GW.Space) :
    (∫ y, testMollifier y • u (x-ε • y) ∂(volume : Measure GW.Space)) =
      smoothConvolution (testMollifierScaled ε) (u : GW.Space → ℂ) x := by
  let f : GW.Space → ℂ := fun z => testMollifierScaled ε (x-z) • u z
  let R : GW.Space ≃ₜ GW.Space := Homeomorph.subLeft x
  have hR : MeasurePreserving R (volume : Measure GW.Space) volume := testReflection_preserving x
  have hF : StronglyMeasurable (fun z : GW.Space => testMollifier (ε⁻¹ • z) • u (x-z)) :=
    ((testMollifier_contDiff.continuous.comp (continuous_const_smul _)).stronglyMeasurable).smul
      ((Lp.stronglyMeasurable u).comp_measurable (continuous_sub_left x).measurable)
  have he := scale_integral_vector ε hε.ne' (fun z : GW.Space => testMollifier (ε⁻¹ • z) • u (x-z)) hF
  have h₀ (y : GW.Space) : ε⁻¹ • (ε • y) = y := by rw [smul_smul,inv_mul_cancel₀ hε.ne',one_smul]
  simp_rw [h₀] at he
  rw [he,abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hε.le 3))]
  let z : ℂ := ∫ y, testMollifier (ε⁻¹ • y) • u (x-y) ∂(volume : Measure GW.Space)
  change Complex.ofReal ((ε^3)⁻¹) • z = _
  have hz := RCLike.real_smul_eq_coe_smul (K := ℂ) ((ε^3)⁻¹) z
  change (ε^3)⁻¹ • z = Complex.ofReal ((ε^3)⁻¹) • z at hz
  rw [← hz]
  change (ε^3)⁻¹ • (∫ y, testMollifier (ε⁻¹ • y) • u (x-y) ∂(volume : Measure GW.Space)) = _
  rw [← integral_smul]
  calc
    _ = ∫ z, f (R z) ∂(volume : Measure GW.Space) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => by
        change (ε^3)⁻¹ • (testMollifier (ε⁻¹ • z) • u (x-z)) =
          testMollifierScaled ε (x-(x-z)) • u (x-z)
        rw [sub_sub_cancel,testMollifierScaled,smul_smul])
    _ = _ := hR.integral_comp R.measurableEmbedding f

def smoothMollifiedRep (u : GW.OnePhonon) (ε : ℝ) : GW.Space → ℂ :=
  smoothConvolution (testMollifierScaled ε) (u : GW.Space → ℂ)

lemma smoothMollifiedRep_contDiff (u : GW.OnePhonon) (hu : Integrable (u : GW.Space → ℂ) volume)
    (ε : ℝ) (hε : 0 < ε) : ContDiff ℝ ∞ (smoothMollifiedRep u ε) :=
  smoothConvolution_contDiff (testMollifierScaled_contDiff ε) (testMollifierScaled_hasCompactSupport ε hε) hu

lemma smoothMollifiedRep_hasCompactSupport (u : GW.OnePhonon) (ε : ℝ) (hε : 0 < ε)
    (L : Set GW.Space) (hL : IsCompact L) (hzero : ∀ᵐ y ∂(volume : Measure GW.Space), y ∉ L → u y = 0) :
    HasCompactSupport (smoothMollifiedRep u ε) :=
  (IsCompact.add (show IsCompact (tsupport (testMollifierScaled ε)) from testMollifierScaled_hasCompactSupport ε hε)
    hL).of_isClosed_subset isClosed_closure (smoothConvolution_support (testMollifierScaled_hasCompactSupport ε hε) _ L hL hzero)

def smoothMollifiedClass (u : GW.OnePhonon) (hu : Integrable (u : GW.Space → ℂ) volume)
    (ε : ℝ) (hε : 0 < ε) (L : Set GW.Space) (hL : IsCompact L)
    (hzero : ∀ᵐ y ∂(volume : Measure GW.Space), y ∉ L → u y = 0) : GW.OnePhonon :=
  ((smoothMollifiedRep_contDiff u hu ε hε).continuous.memLp_of_hasCompactSupport
    (smoothMollifiedRep_hasCompactSupport u ε hε L hL hzero)).toLp (smoothMollifiedRep u ε)

lemma smoothMollifiedClass_ae (u : GW.OnePhonon) (hu : Integrable (u : GW.Space → ℂ) volume)
    (ε : ℝ) (hε : 0 < ε) (L : Set GW.Space) (hL : IsCompact L)
    (hzero : ∀ᵐ y ∂(volume : Measure GW.Space), y ∉ L → u y = 0) :
    smoothMollifiedClass u hu ε hε L hL hzero =ᵐ[(volume : Measure GW.Space)] smoothMollifiedRep u ε :=
  MemLp.coeFn_toLp _

lemma smoothMollifiedClass_eq (u : GW.OnePhonon) (hu : Integrable (u : GW.Space → ℂ) volume)
    (ε : ℝ) (hε : 0 < ε) (L : Set GW.Space) (hL : IsCompact L)
    (hzero : ∀ᵐ y ∂(volume : Measure GW.Space), y ∉ L → u y = 0) :
    mollifiedTranslation u ε = smoothMollifiedClass u hu ε hε L hL hzero := by
  apply ext_inner_left ℂ
  intro g
  rw [mollifiedTranslation_pairing,integral_prod _ (mollifierPairingProduct_integrable u g ε),L2.inner_def]
  apply integral_congr_ae
  filter_upwards [smoothMollifiedClass_ae u hu ε hε L hL hzero] with x hx
  change (∫ y, mollifierPairingProduct u g ε (x,y) ∂(volume : Measure GW.Space)) =
    ⟪g x,smoothMollifiedClass u hu ε hε L hL hzero x⟫_ℂ
  rw [hx,show smoothMollifiedRep u ε x = _ from (testMollifierPointwise_eq u ε hε x).symm]
  let Lx := innerSL ℂ (g x)
  have he := Lx.integral_comp_comm (testMollifierPointwise_integrable u hu ε hε x)
  change _ = Lx (∫ y, testMollifier y • u (x-ε • y) ∂(volume : Measure GW.Space))
  rw [← he]
  apply integral_congr_ae
  exact Eventually.of_forall (fun y => by
    change (testMollifier y : ℂ) * ⟪g x,u (x-ε • y)⟫_ℂ = ⟪g x,testMollifier y • u (x-ε • y)⟫_ℂ
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ) (testMollifier y) (u (x-ε • y)),inner_smul_right] <;> rfl)

structure SmoothScalarTest where
  value : GW.Space → ℂ
  smooth : ContDiff ℝ ∞ value
  compact : HasCompactSupport value

def SmoothScalarTest.toL2 (φ : SmoothScalarTest) : GW.OnePhonon :=
  (φ.smooth.continuous.memLp_of_hasCompactSupport φ.compact).toLp φ.value

lemma SmoothScalarTest.toL2_ae (φ : SmoothScalarTest) :
    φ.toL2 =ᵐ[(volume : Measure GW.Space)] φ.value :=
  MemLp.coeFn_toLp _

def testTruncate (u : GW.OnePhonon) (R : ℕ) : GW.OnePhonon :=
  realCutoff (m := fun x : GW.Space => ‖x‖) continuous_norm.measurable R u

lemma testTruncate_ae (u : GW.OnePhonon) (R : ℕ) :
    testTruncate u R =ᵐ[(volume : Measure GW.Space)]
      (Metric.closedBall (0 : GW.Space) (R:ℝ)).indicator (u : GW.Space → ℂ) := by
  have he : realCutoffSet (fun x : GW.Space => ‖x‖) R = Metric.closedBall (0 : GW.Space) (R:ℝ) := by
    ext x
    simp only [realCutoffSet,mem_setOf_eq,Metric.mem_closedBall,dist_zero_right,abs_norm]
  simpa only [testTruncate,he] using
    (realCutoff_ae (m := fun x : GW.Space => ‖x‖) continuous_norm.measurable R u).symm

lemma testTruncate_tendsto (u : GW.OnePhonon) : Tendsto (testTruncate u) atTop (𝓝 u) :=
  realCutoff_tendsto (m := fun x : GW.Space => ‖x‖) continuous_norm.measurable u

lemma testTruncate_support_ae (u : GW.OnePhonon) (R : ℕ) :
    ∀ᵐ x ∂(volume : Measure GW.Space), x ∉ Metric.closedBall (0 : GW.Space) (R:ℝ) →
      testTruncate u R x = 0 := by
  filter_upwards [testTruncate_ae u R] with x hx ho
  exact hx.trans (indicator_of_notMem ho _)

lemma testTruncate_integrable (u : GW.OnePhonon) (R : ℕ) :
    Integrable (testTruncate u R : GW.Space → ℂ) (volume : Measure GW.Space) := by
  let B := Metric.closedBall (0 : GW.Space) (R:ℝ)
  let f := B.indicator (u : GW.Space → ℂ)
  have h : MemLp f 2 (volume : Measure GW.Space) :=
    (Lp.memLp (testTruncate u R)).ae_eq (testTruncate_ae u R)
  have hi := h.mono_exponent_of_measure_support_ne_top
    (fun x hx => indicator_of_notMem hx _) (measure_closedBall_lt_top.ne) (by norm_num : (1:ℝ≥0∞) ≤ 2)
  exact (memLp_one_iff_integrable.mp hi).congr (testTruncate_ae u R).symm

lemma smoothScalarTest_dense : Dense (Set.range SmoothScalarTest.toL2) := by
  apply Metric.dense_iff.mpr
  intro u δ hδ
  have hδ2 : 0 < δ/2 := by positivity
  obtain ⟨R,hR⟩ := (Metric.tendsto_nhds.mp (testTruncate_tendsto u) (δ/2) hδ2).exists
  let w := testTruncate u R
  have hw := testTruncate_integrable u R
  let L := Metric.closedBall (0 : GW.Space) (R:ℝ)
  have hL : IsCompact L := isCompact_closedBall _ _
  have h0 := testTruncate_support_ae u R
  have hh := Metric.tendsto_nhds.mp (mollifiedTranslation_tendsto w) (δ/2) hδ2
  have hp : ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ), 0 < ε := self_mem_nhdsWithin
  have hex : ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ), 0 < ε ∧ dist (mollifiedTranslation w ε) w < δ/2 :=
    hp.and hh
  obtain ⟨ε,hε,he⟩ := hex.exists
  let φ : SmoothScalarTest := ⟨smoothMollifiedRep w ε,smoothMollifiedRep_contDiff w hw ε hε,
    smoothMollifiedRep_hasCompactSupport w ε hε L hL h0⟩
  have hclass : φ.toL2 = mollifiedTranslation w ε :=
    (smoothMollifiedClass_eq w hw ε hε L hL h0).symm
  refine ⟨φ.toL2,?_,⟨φ,rfl⟩⟩
  apply Metric.mem_ball.mpr
  rw [hclass]
  exact (dist_triangle _ w _).trans_lt (by change dist (mollifiedTranslation w ε) w + dist w u < δ; linarith)

def LocalSquareIntegrable {E : Type*} [NormedAddCommGroup E] (f : GW.Space → E) : Prop :=
  ∀ R : ℕ, MemLp f 2 ((volume : Measure GW.Space).restrict (Metric.closedBall (0 : GW.Space) (R:ℝ)))

def shiftedRealMollifierTest (ε : ℝ) (hε : 0 < ε) (x : GW.Space) : SmoothScalarTest where
  value := fun y => (testMollifierScaled ε (x-y) : ℂ)
  smooth := Complex.ofRealCLM.contDiff.comp
    ((testMollifierScaled_contDiff ε).comp (contDiff_const.sub contDiff_id))
  compact := by
    have h := (testMollifierScaled_hasCompactSupport ε hε).comp_homeomorph (Homeomorph.subLeft x)
    exact h.comp_left Complex.ofReal_zero

def localTestTruncRep {E : Type*} [Zero E] (f : GW.Space → E) (R : ℕ) : GW.Space → E :=
  (Metric.closedBall (0 : GW.Space) (R:ℝ)).indicator f

lemma localTestTruncRep_memLp {E : Type*} [NormedAddCommGroup E] (f : GW.Space → E)
    (hf : LocalSquareIntegrable f) (R : ℕ) :
    MemLp (localTestTruncRep f R) 2 (volume : Measure GW.Space) :=
  (memLp_indicator_iff_restrict measurableSet_closedBall.nullMeasurableSet).mpr (hf R)

def localTestTruncClass (f : GW.Space → ℂ) (hf : LocalSquareIntegrable f) (R : ℕ) : GW.OnePhonon :=
  (localTestTruncRep_memLp f hf R).toLp (localTestTruncRep f R)

lemma localTestTruncClass_ae (f : GW.Space → ℂ) (hf : LocalSquareIntegrable f) (R : ℕ) :
    localTestTruncClass f hf R =ᵐ[(volume : Measure GW.Space)] localTestTruncRep f R :=
  MemLp.coeFn_toLp _

lemma localTestTruncClass_integrable (f : GW.Space → ℂ) (hf : LocalSquareIntegrable f) (R : ℕ) :
    Integrable (localTestTruncClass f hf R : GW.Space → ℂ) volume := by
  have h := (localTestTruncRep_memLp f hf R).mono_exponent_of_measure_support_ne_top
    (fun x hx => indicator_of_notMem hx _) measure_closedBall_lt_top.ne (by norm_num : (1:ℝ≥0∞) ≤ 2)
  exact (memLp_one_iff_integrable.mp h).congr (localTestTruncClass_ae f hf R).symm

lemma localTestTruncClass_support (f : GW.Space → ℂ) (hf : LocalSquareIntegrable f) (R : ℕ) :
    ∀ᵐ y ∂(volume : Measure GW.Space), y ∉ Metric.closedBall (0 : GW.Space) (R:ℝ) →
      localTestTruncClass f hf R y = 0 := by
  filter_upwards [localTestTruncClass_ae f hf R] with y hy hn
  exact hy.trans (indicator_of_notMem hn _)

lemma scaledMollifier_zero_outside (ε : ℝ) (hε : 0 < ε) {p : GW.Space} (hp : 2*ε < ‖p‖) :
    testMollifierScaled ε p = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro h
  have hb := testMollifierScaled_support_subset ε hε h
  rw [Metric.mem_closedBall,dist_zero_right] at hb
  exact (not_lt_of_ge hb) hp

lemma localSmoothMollifiedRep_zero (f : GW.Space → ℂ) (hf : LocalSquareIntegrable f)
    (hpair : ∀ φ : SmoothScalarTest, (∫ y, ⟪φ.value y,f y⟫_ℂ ∂(volume : Measure GW.Space)) = 0)
    (R : ℕ) (x : GW.Space) (hx : ‖x‖ ≤ (R:ℝ)) (ε : ℝ) (hε : 0 < ε) (he : 2*ε < 1) :
    smoothMollifiedRep (localTestTruncClass f hf (R+1)) ε x = 0 := by
  let φ := shiftedRealMollifierTest ε hε x
  unfold smoothMollifiedRep smoothConvolution
  refine (integral_congr_ae ?_).trans (hpair φ)
  filter_upwards [localTestTruncClass_ae f hf (R+1)] with y hy
  change testMollifierScaled ε (x-y) • localTestTruncClass f hf (R+1) y = ⟪φ.value y,f y⟫_ℂ
  rw [hy]
  change _ = ⟪(testMollifierScaled ε (x-y) : ℂ),f y⟫_ℂ
  rw [RCLike.inner_apply',Complex.conj_ofReal]
  by_cases h : y ∈ Metric.closedBall (0 : GW.Space) ((R+1:ℕ):ℝ)
  · rw [localTestTruncRep,indicator_of_mem h,RCLike.real_smul_eq_coe_smul (K := ℂ),smul_eq_mul] <;> rfl
  · have hybig : (R:ℝ)+1 < ‖y‖ := by
      simpa only [Metric.mem_closedBall,dist_zero_right,Nat.cast_add,Nat.cast_one,not_le] using h
    have hb : ‖y‖ ≤ ‖x‖ + ‖x-y‖ := by
      have ht := norm_sub_le x (x-y)
      rw [sub_sub_cancel] at ht
      exact ht
    have hz := scaledMollifier_zero_outside ε hε (show 2*ε < ‖x-y‖ by linarith)
    rw [hz,zero_smul,Complex.ofReal_zero,zero_mul]

lemma localSquareIntegrable_scalar_vanishes (f : GW.Space → ℂ) (hf : LocalSquareIntegrable f)
    (hpair : ∀ φ : SmoothScalarTest, (∫ y, ⟪φ.value y,f y⟫_ℂ ∂(volume : Measure GW.Space)) = 0) :
    f =ᵐ[(volume : Measure GW.Space)] 0 := by
  have h (R : ℕ) : ∀ᵐ y ∂(volume : Measure GW.Space), ‖y‖ ≤ (R:ℝ) → f y = 0 := by
    let u := localTestTruncClass f hf (R+1)
    let L := Metric.closedBall (0 : GW.Space) ((R+1:ℕ):ℝ)
    have hL : IsCompact L := isCompact_closedBall _ _
    have hu := localTestTruncClass_integrable f hf (R+1)
    have h0 := localTestTruncClass_support f hf (R+1)
    let T : GW.OnePhonon →L[ℂ] GW.OnePhonon := realCutoff (m := fun x : GW.Space => ‖x‖) continuous_norm.measurable R
    have hcut : ∀ ε : ℝ, 0 < ε → 2*ε < 1 → T (mollifiedTranslation u ε) = 0 := by
      intro ε hε he
      rw [smoothMollifiedClass_eq u hu ε hε L hL h0]
      apply Lp.ext
      filter_upwards [testTruncate_ae (smoothMollifiedClass u hu ε hε L hL h0) R,
        smoothMollifiedClass_ae u hu ε hε L hL h0,Lp.coeFn_zero ℂ 2 (volume : Measure GW.Space)]
        with y hy hs hz
      change T (smoothMollifiedClass u hu ε hε L hL h0) y = (0 : GW.OnePhonon) y
      rw [hz]
      change T (smoothMollifiedClass u hu ε hε L hL h0) y =
        (Metric.closedBall (0 : GW.Space) (R:ℝ)).indicator (smoothMollifiedClass u hu ε hε L hL h0 : GW.Space → ℂ) y at hy
      rw [hy]
      by_cases hmem : y ∈ Metric.closedBall (0 : GW.Space) (R:ℝ)
      · have hnorm : ‖y‖ ≤ (R:ℝ) := by simpa only [Metric.mem_closedBall,dist_zero_right] using hmem
        rw [indicator_of_mem hmem,hs]
        exact localSmoothMollifiedRep_zero f hf hpair R y hnorm ε hε he
      · exact indicator_of_notMem hmem _
    have hlim := T.continuous.continuousAt.tendsto.comp (mollifiedTranslation_tendsto u)
    have hεpos : ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ), 0 < ε := self_mem_nhdsWithin
    have hεsmall : ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ), ε < (1/2:ℝ) :=
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0:ℝ)<1/2))
    have hc : Tendsto (fun ε => T (mollifiedTranslation u ε)) (𝓝[>] 0) (𝓝 (0:GW.OnePhonon)) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [hεpos,hεsmall] with ε hp hs
      exact (hcut ε hp (by linarith)).symm
    have hT : T u = 0 := tendsto_nhds_unique hlim hc
    filter_upwards [testTruncate_ae u R,localTestTruncClass_ae f hf (R+1),
      Lp.coeFn_zero ℂ 2 (volume : Measure GW.Space)] with y hy hu' hz hnorm
    have hmem : y ∈ Metric.closedBall (0 : GW.Space) (R:ℝ) := by
      simpa only [Metric.mem_closedBall,dist_zero_right] using hnorm
    have hmem' : y ∈ L := by
      change dist y 0 ≤ ((R+1:ℕ):ℝ)
      rw [dist_zero_right,Nat.cast_add,Nat.cast_one]
      linarith
    change T u y = _ at hy
    rw [hT,indicator_of_mem hmem] at hy
    rw [localTestTruncRep,indicator_of_mem hmem'] at hu'
    exact hu'.symm.trans (hy.symm.trans hz)
  filter_upwards [ae_all_iff.mpr h] with y hy
  obtain ⟨R,hR⟩ := exists_nat_gt ‖y‖
  exact hy R hR.le

lemma localSquareIntegrable_hilbert_vanishes {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (f : GW.Space → E)
    (hm : AEStronglyMeasurable f (volume : Measure GW.Space)) (hf : LocalSquareIntegrable f)
    (hpair : ∀ (φ : SmoothScalarTest) (e : E),
      (∫ y, ⟪φ.value y • e,f y⟫_ℂ ∂(volume : Measure GW.Space)) = 0) :
    f =ᵐ[(volume : Measure GW.Space)] 0 := by
  have hpair_e (e : E) : (fun x => ⟪e,f x⟫_ℂ) =ᵐ[(volume : Measure GW.Space)] 0 := by
    apply localSquareIntegrable_scalar_vanishes
    · intro R
      exact (hf R).const_inner e
    · intro φ
      refine (integral_congr_ae (Eventually.of_forall (fun y => ?_))).trans (hpair φ e)
      rw [RCLike.inner_apply',inner_smul_left]
  let g := hm.mk f
  obtain ⟨D,hDsub,hDc,hD⟩ := hm.stronglyMeasurable_mk.isSeparable_range.exists_countable_dense_subset
  letI : Countable D := hDc.to_subtype
  have hz : ∀ᵐ x ∂(volume : Measure GW.Space), ∀ e : D, ⟪(e : E),f x⟫_ℂ = 0 :=
    ae_all_iff.mpr (fun e => hpair_e e.val)
  filter_upwards [hm.ae_eq_mk,hz] with x hx hzx
  have hg : f x ∈ closure D := by
    apply hD
    exact ⟨x,hx.symm⟩
  have hc : IsClosed {e : E | ⟪e,f x⟫_ℂ = 0} :=
    isClosed_eq (continuous_id.inner continuous_const) continuous_const
  have hsub : D ⊆ {e : E | ⟪e,f x⟫_ℂ = 0} := fun e he => hzx ⟨e,he⟩
  have hself : ⟪f x,f x⟫_ℂ = 0 := closure_minimal hsub hc hg
  exact inner_self_eq_zero.mp hself

lemma localSquareIntegrable_aeStronglyMeasurable {E : Type*} [NormedAddCommGroup E]
    (f : GW.Space → E) (hf : LocalSquareIntegrable f) :
    AEStronglyMeasurable f (volume : Measure GW.Space) := by
  apply l2_limit_measurable (fs := fun n => localTestTruncRep f n)
    (fun n => (localTestTruncRep_memLp f hf n).aestronglyMeasurable)
  apply Eventually.of_forall
  intro x
  obtain ⟨N,hN⟩ := exists_nat_gt ‖x‖
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop N] with n hn
  have hx : x ∈ Metric.closedBall (0:GW.Space) (n:ℝ) := by
    rw [Metric.mem_closedBall,dist_zero_right]
    exact hN.le.trans (Nat.cast_le.mpr hn)
  exact (indicator_of_mem hx f).symm

lemma localSquareIntegrable_hilbert_vanishes_of_tests {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (f : GW.Space → E) (hf : LocalSquareIntegrable f)
    (hpair : ∀ (φ : SmoothScalarTest) (e : E),
      (∫ y, ⟪φ.value y • e,f y⟫_ℂ ∂(volume : Measure GW.Space)) = 0) :
    f =ᵐ[(volume : Measure GW.Space)] 0 :=
  localSquareIntegrable_hilbert_vanishes f (localSquareIntegrable_aeStronglyMeasurable f hf) hf hpair

def SmoothScalarTest.toSchwartzMap (φ : SmoothScalarTest) : SchwartzMap GW.Space ℂ :=
  φ.compact.toSchwartzMap φ.smooth

lemma SmoothScalarTest.toSchwartzMap_apply (φ : SmoothScalarTest) (x : GW.Space) :
    φ.toSchwartzMap x = φ.value x := rfl

end GW.Analysis
