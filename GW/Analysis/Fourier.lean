module
public import GW.Analysis.L2Quotient
public import GW.Analysis.RealMultiplier
public import GW.Operators.ResolventAlgebra
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace ENNReal FourierTransform
namespace GW.Analysis

lemma physical_finrank : Module.finrank ℝ GW.Space = 3 := by simp [GW.Space]

lemma scale_integral (a : ℝ) (ha : a ≠ 0) (f : GW.Space → ℝ) (hf : StronglyMeasurable f) :
    (∫ x, f (a • x)) = |(a^3)⁻¹| * ∫ x, f x := by
  have hm := Measure.map_addHaar_smul (volume : Measure GW.Space) ha
  rw [physical_finrank] at hm
  calc
    _ = ∫ x, f x ∂Measure.map (fun x : GW.Space => a • x) volume :=
      (integral_map (measurable_const_smul a).aemeasurable hf.aestronglyMeasurable).symm
    _ = _ := by rw [hm,integral_smul_measure,ENNReal.toReal_ofReal (abs_nonneg _)];rfl

section Dilation
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def dilationAmplitude (a : ℝ) : ℝ := a^(-(3 : ℝ)/2)
def dilationRepresentative (a : ℝ) (v : Lp H 2 (volume : Measure GW.Space)) : GW.Space → H :=
  fun p => (dilationAmplitude a : ℂ) • v (a⁻¹ • p)

lemma dilationRepresentative_stronglyMeasurable (a : ℝ) (v : Lp H 2 (volume : Measure GW.Space)) :
    StronglyMeasurable (dilationRepresentative a v) :=
  ((Lp.stronglyMeasurable v).comp_measurable (measurable_const_smul a⁻¹)).const_smul _

lemma dilationAmplitude_sq (a : ℝ) (ha : 0 < a) :
    dilationAmplitude a ^ 2 * a^3 = 1 := by
  unfold dilationAmplitude
  rw [← Real.rpow_natCast,← Real.rpow_mul ha.le]
  norm_num
  exact inv_mul_cancel₀ (pow_ne_zero _ (ne_of_gt ha))
lemma dilationRepresentative_integrable_sq (a : ℝ) (ha : 0 < a)
    (v : Lp H 2 (volume : Measure GW.Space)) :
    Integrable (fun p => ‖dilationRepresentative a v p‖^2) := by
  have hv : Integrable (fun p : GW.Space => ‖v p‖^2) := by
    have h := (Lp.memLp v).norm_rpow two_ne_zero ENNReal.ofNat_ne_top
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,memLp_one_iff_integrable] using h
  have hm := Measure.map_addHaar_smul (volume : Measure GW.Space) (inv_ne_zero (ne_of_gt ha))
  have hvmap : Integrable (fun p : GW.Space => ‖v p‖^2)
      (Measure.map (fun p : GW.Space => a⁻¹ • p) volume) := by
    rw [hm]
    exact hv.smul_measure ENNReal.ofReal_ne_top
  have hc := hvmap.comp_aemeasurable (measurable_const_smul a⁻¹).aemeasurable
  have h := hc.const_mul (dilationAmplitude a ^ 2)
  simpa only [dilationRepresentative,norm_smul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,
    mul_comm (dilationAmplitude a ^ 2),Function.comp_def] using h

lemma dilationRepresentative_integral_sq (a : ℝ) (ha : 0 < a)
    (v : Lp H 2 (volume : Measure GW.Space)) :
    (∫ p, ‖dilationRepresentative a v p‖^2) = ∫ p, ‖v p‖^2 := by
  simp only [dilationRepresentative,norm_smul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  rw [integral_const_mul,scale_integral a⁻¹ (inv_ne_zero (ne_of_gt ha))
    (fun p => ‖v p‖^2) ((Lp.stronglyMeasurable v).norm.pow 2)]
  rw [← inv_pow,inv_inv,abs_of_nonneg (pow_nonneg ha.le 3),← mul_assoc,dilationAmplitude_sq a ha,one_mul]

def dilationClass (a : ℝ) (ha : 0 < a) (v : Lp H 2 (volume : Measure GW.Space)) :
    Lp H 2 (volume : Measure GW.Space) :=
  l2Class (dilationRepresentative_stronglyMeasurable a v).aestronglyMeasurable
    (dilationRepresentative_integrable_sq a ha v)

lemma dilationClass_ae (a : ℝ) (ha : 0 < a) (v : Lp H 2 (volume : Measure GW.Space)) :
    dilationClass a ha v =ᵐ[volume] dilationRepresentative a v :=
  l2Class_ae _ _

lemma dilationClass_norm (a : ℝ) (ha : 0 < a) (v : Lp H 2 (volume : Measure GW.Space)) :
    ‖dilationClass a ha v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [l2_norm_sq (𝕜 := ℂ),l2_norm_sq (𝕜 := ℂ)]
  exact (integral_congr_ae ((dilationClass_ae a ha v).mono
    (fun _ hx => congrArg (fun v : H => ‖v‖^2) hx))).trans (dilationRepresentative_integral_sq a ha v)

lemma dilationClass_add (a : ℝ) (ha : 0 < a) (u v : Lp H 2 (volume : Measure GW.Space)) :
    dilationClass a ha (u+v) = dilationClass a ha u + dilationClass a ha v := by
  apply Lp.ext
  have hq := Measure.quasiMeasurePreserving_smul (volume : Measure GW.Space) (inv_ne_zero (ne_of_gt ha))
  filter_upwards [dilationClass_ae a ha (u+v),dilationClass_ae a ha u,dilationClass_ae a ha v,
    Lp.coeFn_add (dilationClass a ha u) (dilationClass a ha v),hq.ae (Lp.coeFn_add u v)] with p hs hu hv hc hsum
  rw [hc,Pi.add_apply,hs,hu,hv]
  change (dilationAmplitude a : ℂ) • (u+v) (a⁻¹ • p) =
    (dilationAmplitude a : ℂ) • u (a⁻¹ • p) + (dilationAmplitude a : ℂ) • v (a⁻¹ • p)
  rw [hsum,Pi.add_apply,smul_add]

lemma dilationClass_smul (a : ℝ) (ha : 0 < a) (c : ℂ) (u : Lp H 2 (volume : Measure GW.Space)) :
    dilationClass a ha (c • u) = c • dilationClass a ha u := by
  apply Lp.ext
  have hq := Measure.quasiMeasurePreserving_smul (volume : Measure GW.Space) (inv_ne_zero (ne_of_gt ha))
  filter_upwards [dilationClass_ae a ha (c • u),dilationClass_ae a ha u,
    Lp.coeFn_smul c (dilationClass a ha u),hq.ae (Lp.coeFn_smul c u)] with p hs hu hc hsmul
  rw [hc,Pi.smul_apply,hs,hu]
  change (dilationAmplitude a : ℂ) • (c • u) (a⁻¹ • p) = c • ((dilationAmplitude a : ℂ) • u (a⁻¹ • p))
  rw [hsmul,Pi.smul_apply,smul_comm]

def dilationIsometry (a : ℝ) (ha : 0 < a) :
    Lp H 2 (volume : Measure GW.Space) →ₗᵢ[ℂ] Lp H 2 (volume : Measure GW.Space) where
  toLinearMap := {toFun := dilationClass a ha,map_add' := dilationClass_add a ha,map_smul' := dilationClass_smul a ha}
  norm_map' := dilationClass_norm a ha

lemma dilationAmplitude_inv (a : ℝ) (ha : 0 < a) :
    dilationAmplitude a⁻¹ = (dilationAmplitude a)⁻¹ :=
  Real.inv_rpow ha.le _

lemma dilationClass_inverse (a : ℝ) (ha : 0 < a) (u : Lp H 2 (volume : Measure GW.Space)) :
    dilationClass a ha (dilationClass a⁻¹ (inv_pos.mpr ha) u) = u := by
  apply Lp.ext
  have hq := Measure.quasiMeasurePreserving_smul (volume : Measure GW.Space) (inv_ne_zero (ne_of_gt ha))
  filter_upwards [dilationClass_ae a ha (dilationClass a⁻¹ (inv_pos.mpr ha) u),
    hq.ae (dilationClass_ae a⁻¹ (inv_pos.mpr ha) u)] with p hout hin
  rw [hout]
  change (dilationAmplitude a : ℂ) • dilationClass a⁻¹ (inv_pos.mpr ha) u (a⁻¹ • p) = u p
  rw [hin]
  change (dilationAmplitude a : ℂ) • ((dilationAmplitude a⁻¹ : ℂ) • u ((a⁻¹)⁻¹ • (a⁻¹ • p))) = u p
  have hscale : (a⁻¹)⁻¹ • (a⁻¹ • p) = p := by rw [inv_inv,smul_smul,mul_inv_cancel₀ (ne_of_gt ha),one_smul]
  have hA : dilationAmplitude a ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos ha _)
  rw [hscale,smul_smul,dilationAmplitude_inv a ha,← Complex.ofReal_mul,
    mul_inv_cancel₀ hA,Complex.ofReal_one,one_smul]

lemma dilationClass_inverse_right (a : ℝ) (ha : 0 < a) (u : Lp H 2 (volume : Measure GW.Space)) :
    dilationClass a⁻¹ (inv_pos.mpr ha) (dilationClass a ha u) = u := by
  simpa only [inv_inv] using dilationClass_inverse a⁻¹ (inv_pos.mpr ha) u

def dilationUnitary (a : ℝ) (ha : 0 < a) :
    Lp H 2 (volume : Measure GW.Space) ≃ₗᵢ[ℂ] Lp H 2 (volume : Measure GW.Space) :=
  LinearIsometryEquiv.ofSurjective (dilationIsometry a ha)
    (fun u => ⟨dilationClass a⁻¹ (inv_pos.mpr ha) u,dilationClass_inverse a ha u⟩)

lemma dilationUnitary_symm (a : ℝ) (ha : 0 < a) (u : Lp H 2 (volume : Measure GW.Space)) :
    (dilationUnitary a ha).symm u = dilationClass a⁻¹ (inv_pos.mpr ha) u := by
  apply (dilationUnitary a ha).injective
  exact ((dilationUnitary a ha).apply_symm_apply u).trans (dilationClass_inverse a ha u).symm

def spatialScale (a : ℝ) (ha : a ≠ 0) : GW.Space ≃L[ℝ] GW.Space :=
  ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := GW.Space) (Units.mk0 a ha)

lemma spatialScale_apply (a : ℝ) (ha : a ≠ 0) (p : GW.Space) : spatialScale a ha p = a • p := rfl

def schwartzDilation (a : ℝ) (ha : 0 < a) (f : SchwartzMap GW.Space H) : SchwartzMap GW.Space H :=
  (dilationAmplitude a : ℂ) •
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (spatialScale a⁻¹ (inv_ne_zero (ne_of_gt ha)))) f

lemma schwartzDilation_apply (a : ℝ) (ha : 0 < a) (f : SchwartzMap GW.Space H) (p : GW.Space) :
    schwartzDilation a ha f p = (dilationAmplitude a : ℂ) • f (a⁻¹ • p) := rfl

lemma dilationUnitary_schwartz (a : ℝ) (ha : 0 < a) (f : SchwartzMap GW.Space H) :
    dilationUnitary a ha (f.toLp 2) = (schwartzDilation a ha f).toLp 2 := by
  apply Lp.ext
  have hq := Measure.quasiMeasurePreserving_smul (volume : Measure GW.Space) (inv_ne_zero (ne_of_gt ha))
  filter_upwards [dilationClass_ae a ha (f.toLp 2),hq.ae (f.coeFn_toLp 2 (volume : Measure GW.Space)),
    (schwartzDilation a ha f).coeFn_toLp 2 (volume : Measure GW.Space)] with p hd hf hs
  change dilationClass a ha (f.toLp 2) p = _
  rw [hd,hs]
  change (dilationAmplitude a : ℂ) • (f.toLp 2 (volume : Measure GW.Space)) (a⁻¹ • p) = _
  rw [hf]
  rfl

lemma scale_integral_vector (a : ℝ) (ha : a ≠ 0) (f : GW.Space → H) (hf : StronglyMeasurable f) :
    (∫ x, f (a • x)) = (↑|(a^3)⁻¹| : ℂ) • ∫ x, f x := by
  have hm := Measure.map_addHaar_smul (volume : Measure GW.Space) ha
  rw [physical_finrank] at hm
  calc
    _ = ∫ x, f x ∂Measure.map (fun x : GW.Space => a • x) volume :=
      (integral_map (measurable_const_smul a).aemeasurable hf.aestronglyMeasurable).symm
    _ = _ := by
      rw [hm,integral_smul_measure,ENNReal.toReal_ofReal (abs_nonneg _),RCLike.real_smul_eq_coe_smul (K := ℂ)]
      rfl

lemma dilationAmplitude_inverse_jacobian (a : ℝ) (ha : 0 < a) :
    dilationAmplitude a⁻¹ * |(a^3)⁻¹| = dilationAmplitude a := by
  rw [dilationAmplitude_inv a ha,abs_of_nonneg (inv_nonneg.mpr (pow_nonneg ha.le 3))]
  have hA : dilationAmplitude a ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos ha _)
  field_simp [hA,ne_of_gt ha]
  nlinarith [dilationAmplitude_sq a ha]

end Dilation
lemma physicalFourierScale_pos : 0 < (2 : ℝ)*Real.pi := mul_pos (by norm_num) Real.pi_pos

def physicalPhase (k x : GW.Space) : ℂ := Complex.exp ((↑(-⟪x,k⟫_ℝ) : ℂ)*Complex.I)

lemma physicalPhase_temperate (k : GW.Space) : (physicalPhase k).HasTemperateGrowth := by
  unfold physicalPhase
  exact Complex.hasTemperateGrowth_exp_mul_I.comp (by fun_prop)

lemma physicalPhase_norm (k x : GW.Space) : ‖physicalPhase k x‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I _

@[fun_prop]
lemma continuous_physicalPhase (k : GW.Space) : Continuous (physicalPhase k) := by
  unfold physicalPhase
  fun_prop

lemma physicalPhase_add (k l x : GW.Space) : physicalPhase (k+l) x = physicalPhase k x * physicalPhase l x := by
  unfold physicalPhase
  rw [inner_add_right,neg_add,Complex.ofReal_add,add_mul,Complex.exp_add]

lemma physicalPhase_add_space (k x y : GW.Space) : physicalPhase k (x+y) = physicalPhase k x * physicalPhase k y := by
  unfold physicalPhase
  rw [inner_add_left,neg_add,Complex.ofReal_add,add_mul,Complex.exp_add]

lemma physicalPhase_comm (k x : GW.Space) : physicalPhase k x = physicalPhase x k := by
  unfold physicalPhase
  rw [real_inner_comm]

section PhysicalFourier
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def physicalFourierUnitary : Lp H 2 (volume : Measure GW.Space) ≃ₗᵢ[ℂ] Lp H 2 (volume : Measure GW.Space) :=
  (Lp.fourierTransformₗᵢ GW.Space H).trans (dilationUnitary (2*Real.pi) physicalFourierScale_pos)

def schwartzPhysicalFourier (f : SchwartzMap GW.Space H) : SchwartzMap GW.Space H :=
  schwartzDilation (2*Real.pi) physicalFourierScale_pos (𝓕 f)

def physicalFourierIntegral (f : GW.Space → H) (p : GW.Space) : H :=
  (dilationAmplitude (2*Real.pi) : ℂ) • ∫ x, physicalPhase p x • f x

lemma physicalFourier_schwartz (f : SchwartzMap GW.Space H) :
    physicalFourierUnitary (f.toLp 2) = (schwartzPhysicalFourier f).toLp 2 := by
  change dilationUnitary (2*Real.pi) physicalFourierScale_pos (𝓕 (f.toLp 2)) = _
  rw [SchwartzMap.toLp_fourier_eq,dilationUnitary_schwartz]
  rfl

omit [CompleteSpace H] in
lemma schwartzPhysicalFourier_apply (f : SchwartzMap GW.Space H) (p : GW.Space) :
    schwartzPhysicalFourier f p = physicalFourierIntegral f p := by
  rw [schwartzPhysicalFourier,schwartzDilation_apply]
  change (dilationAmplitude (2*Real.pi) : ℂ) • 𝓕 (f : GW.Space → H) ((2*Real.pi)⁻¹ • p) = _
  rw [Real.fourier_eq']
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by
    have he : -2*Real.pi*⟪x,(2*Real.pi)⁻¹ • p⟫_ℝ = -⟪x,p⟫_ℝ := by
      rw [inner_smul_right]
      field_simp
    change Complex.exp ((↑(-2*Real.pi*⟪x,(2*Real.pi)⁻¹ • p⟫_ℝ) : ℂ)*Complex.I) • f x =
      physicalPhase p x • f x
    rw [he]
    rfl)
def schwartzPhysicalFourierInv (f : SchwartzMap GW.Space H) : SchwartzMap GW.Space H :=
  𝓕⁻ (schwartzDilation (2*Real.pi)⁻¹ (inv_pos.mpr physicalFourierScale_pos) f)

lemma physicalFourierInv_schwartz (f : SchwartzMap GW.Space H) :
    physicalFourierUnitary.symm (f.toLp 2) = (schwartzPhysicalFourierInv f).toLp 2 := by
  change (Lp.fourierTransformₗᵢ GW.Space H).symm
    ((dilationUnitary (2*Real.pi) physicalFourierScale_pos).symm (f.toLp 2)) = _
  rw [dilationUnitary_symm]
  change 𝓕⁻ (dilationUnitary (2*Real.pi)⁻¹ (inv_pos.mpr physicalFourierScale_pos) (f.toLp 2)) = _
  rw [dilationUnitary_schwartz,SchwartzMap.toLp_fourierInv_eq]
  rfl

def physicalFourierInvIntegral (f : GW.Space → H) (x : GW.Space) : H :=
  (dilationAmplitude (2*Real.pi) : ℂ) • ∫ p, physicalPhase (-x) p • f p

omit [CompleteSpace H] in
lemma schwartzPhysicalFourierInv_apply (f : SchwartzMap GW.Space H) (x : GW.Space) :
    schwartzPhysicalFourierInv f x = physicalFourierInvIntegral f x := by
  unfold schwartzPhysicalFourierInv
  rw [SchwartzMap.fourierInv_coe]
  rw [Real.fourierInv_eq']
  have he : (fun p => Complex.exp ((↑(2*Real.pi*⟪p,x⟫_ℝ) : ℂ)*Complex.I) •
      schwartzDilation (2*Real.pi)⁻¹ (inv_pos.mpr physicalFourierScale_pos) f p) =
      fun p => (dilationAmplitude (2*Real.pi)⁻¹ : ℂ) •
        (physicalPhase (-x) ((2*Real.pi) • p) • f ((2*Real.pi) • p)) := by
    funext p
    rw [schwartzDilation_apply,inv_inv]
    simp only [physicalPhase,inner_neg_right,neg_neg,inner_smul_left,conj_trivial]
    exact smul_comm _ _ _
  rw [he,integral_smul,scale_integral_vector (2*Real.pi) (ne_of_gt physicalFourierScale_pos)
    (fun p => physicalPhase (-x) p • f p) (by apply Continuous.stronglyMeasurable;fun_prop),
    smul_smul,← Complex.ofReal_mul,dilationAmplitude_inverse_jacobian (2*Real.pi) physicalFourierScale_pos]
  rfl

end PhysicalFourier

section FourierActions
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def modulation (k : GW.Space) : Lp H 2 (volume : Measure GW.Space) →L[ℂ] Lp H 2 (volume : Measure GW.Space) :=
  boundedMultiplier (physicalPhase k) (continuous_physicalPhase k).measurable
    (Eventually.of_forall (fun x => (physicalPhase_norm k x).le))

lemma modulation_ae (k : GW.Space) (u : Lp H 2 (volume : Measure GW.Space)) :
    modulation k u =ᵐ[volume] (fun x => physicalPhase k x • u x) :=
  (boundedMultiplier_ae _ _ _ u).symm

lemma modulation_norm (k : GW.Space) : ‖modulation (H := H) k‖ ≤ 1 :=
  boundedMultiplier_opNorm_le _ _ zero_le_one _

def translation (y : GW.Space) : Lp H 2 (volume : Measure GW.Space) →ₗᵢ[ℂ] Lp H 2 (volume : Measure GW.Space) :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x : GW.Space => x-y) (measurePreserving_sub_right volume y)

lemma translation_ae (y : GW.Space) (u : Lp H 2 (volume : Measure GW.Space)) :
    translation y u =ᵐ[volume] (fun x => u (x-y)) :=
  Lp.coeFn_compMeasurePreserving u (measurePreserving_sub_right volume y)

def schwartzModulation (k : GW.Space) : SchwartzMap GW.Space H →L[ℂ] SchwartzMap GW.Space H :=
  SchwartzMap.smulLeftCLM H (physicalPhase k)

lemma schwartzModulation_apply (k : GW.Space) (f : SchwartzMap GW.Space H) (x : GW.Space) :
    schwartzModulation k f x = physicalPhase k x • f x :=
  SchwartzMap.smulLeftCLM_apply_apply (physicalPhase_temperate k) f x

def schwartzTranslation (y : GW.Space) : SchwartzMap GW.Space H →L[ℂ] SchwartzMap GW.Space H :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (by fun_prop : (fun x : GW.Space => x-y).HasTemperateGrowth)
    (IsometryEquiv.subRight y).isometry.antilipschitzWith

lemma schwartzTranslation_apply (y : GW.Space) (f : SchwartzMap GW.Space H) (x : GW.Space) :
    schwartzTranslation y f x = f (x-y) := rfl

lemma modulation_schwartz (k : GW.Space) (f : SchwartzMap GW.Space H) :
    modulation k (f.toLp 2) = (schwartzModulation k f).toLp 2 := by
  apply Lp.ext
  filter_upwards [modulation_ae k (f.toLp 2),f.coeFn_toLp 2 (volume : Measure GW.Space),
    (schwartzModulation k f).coeFn_toLp 2 (volume : Measure GW.Space)] with x hm hf hs
  rw [hm,hf,hs,schwartzModulation_apply]

lemma translation_schwartz (y : GW.Space) (f : SchwartzMap GW.Space H) :
    translation y (f.toLp 2) = (schwartzTranslation y f).toLp 2 := by
  apply Lp.ext
  filter_upwards [translation_ae y (f.toLp 2),
    (measurePreserving_sub_right (volume : Measure GW.Space) y).quasiMeasurePreserving.ae
      (f.coeFn_toLp 2 (volume : Measure GW.Space)),
    (schwartzTranslation y f).coeFn_toLp 2 (volume : Measure GW.Space)] with x ht hf hs
  rw [ht,hf,hs,schwartzTranslation_apply]

lemma physicalFourierIntegral_modulation (k : GW.Space) (f : GW.Space → H) (p : GW.Space) :
    physicalFourierIntegral (fun x => physicalPhase k x • f x) p = physicalFourierIntegral f (p+k) := by
  unfold physicalFourierIntegral
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by
    change physicalPhase p x • (physicalPhase k x • f x) = physicalPhase (p+k) x • f x
    rw [smul_smul,← physicalPhase_add])

lemma physicalFourierIntegral_translation (y : GW.Space) (f : GW.Space → H) (p : GW.Space) :
    physicalFourierIntegral (fun x => f (x-y)) p = physicalPhase y p • physicalFourierIntegral f p := by
  have he : (∫ x, physicalPhase p x • f (x-y)) = physicalPhase p y • ∫ x, physicalPhase p x • f x := by
    calc
      _ = ∫ x, physicalPhase p (x+y) • f ((x+y)-y) :=
        (integral_add_right_eq_self (fun x => physicalPhase p x • f (x-y)) y).symm
      _ = ∫ x, physicalPhase p y • (physicalPhase p x • f x) := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun x => by
          change physicalPhase p (x+y) • f ((x+y)-y) = physicalPhase p y • (physicalPhase p x • f x)
          rw [add_sub_cancel_right,physicalPhase_add_space,mul_smul]
          exact smul_comm _ _ _)
      _ = _ := integral_smul _ _
  unfold physicalFourierIntegral
  rw [he,physicalPhase_comm p y]
  exact smul_comm _ _ _

lemma schwartzModulation_coe (k : GW.Space) (f : SchwartzMap GW.Space H) :
    (schwartzModulation k f : GW.Space → H) = fun x => physicalPhase k x • f x :=
  funext (schwartzModulation_apply k f)

lemma schwartzTranslation_coe (y : GW.Space) (f : SchwartzMap GW.Space H) :
    (schwartzTranslation y f : GW.Space → H) = fun x => f (x-y) := rfl

lemma schwartzPhysicalFourier_modulation (k : GW.Space) (f : SchwartzMap GW.Space H) :
    schwartzPhysicalFourier (schwartzModulation k f) = schwartzTranslation (-k) (schwartzPhysicalFourier f) := by
  ext p
  rw [schwartzPhysicalFourier_apply,schwartzModulation_coe,physicalFourierIntegral_modulation,
    schwartzTranslation_apply,schwartzPhysicalFourier_apply,sub_neg_eq_add]

lemma schwartzPhysicalFourier_translation (y : GW.Space) (f : SchwartzMap GW.Space H) :
    schwartzPhysicalFourier (schwartzTranslation y f) = schwartzModulation y (schwartzPhysicalFourier f) := by
  ext p
  rw [schwartzPhysicalFourier_apply,schwartzTranslation_coe,physicalFourierIntegral_translation,
    schwartzModulation_apply,schwartzPhysicalFourier_apply]

variable [CompleteSpace H]

lemma physicalFourier_modulation (k : GW.Space) (u : Lp H 2 (volume : Measure GW.Space)) :
    physicalFourierUnitary (modulation k u) = translation (-k) (physicalFourierUnitary u) := by
  have hd := SchwartzMap.denseRange_toLpCLM (E := GW.Space) (F := H) (p := 2)
    (μ := (volume : Measure GW.Space)) (by norm_num)
  refine hd.induction_on u (isClosed_eq
    (physicalFourierUnitary.continuous.comp (modulation k).continuous)
    ((translation (-k)).continuous.comp physicalFourierUnitary.continuous)) ?_
  intro f
  change physicalFourierUnitary (modulation k (f.toLp 2 (volume : Measure GW.Space))) =
    translation (-k) (physicalFourierUnitary (f.toLp 2 (volume : Measure GW.Space)))
  rw [modulation_schwartz,physicalFourier_schwartz,physicalFourier_schwartz,
    translation_schwartz,schwartzPhysicalFourier_modulation]

lemma physicalFourier_translation (y : GW.Space) (u : Lp H 2 (volume : Measure GW.Space)) :
    physicalFourierUnitary (translation y u) = modulation y (physicalFourierUnitary u) := by
  have hd := SchwartzMap.denseRange_toLpCLM (E := GW.Space) (F := H) (p := 2)
    (μ := (volume : Measure GW.Space)) (by norm_num)
  refine hd.induction_on u (isClosed_eq
    (physicalFourierUnitary.continuous.comp (translation y).continuous)
    ((modulation y).continuous.comp physicalFourierUnitary.continuous)) ?_
  intro f
  change physicalFourierUnitary (translation y (f.toLp 2 (volume : Measure GW.Space))) =
    modulation y (physicalFourierUnitary (f.toLp 2 (volume : Measure GW.Space)))
  rw [translation_schwartz,physicalFourier_schwartz,physicalFourier_schwartz,
    modulation_schwartz,schwartzPhysicalFourier_translation]

lemma physicalFourier_modulation_ae (k : GW.Space) (u : Lp H 2 (volume : Measure GW.Space)) :
    physicalFourierUnitary (modulation k u) =ᵐ[volume] (fun p => physicalFourierUnitary u (p+k)) := by
  rw [physicalFourier_modulation]
  simpa only [sub_neg_eq_add] using translation_ae (-k) (physicalFourierUnitary u)

lemma physicalFourier_translation_ae (y : GW.Space) (u : Lp H 2 (volume : Measure GW.Space)) :
    physicalFourierUnitary (translation y u) =ᵐ[volume]
      (fun p => physicalPhase y p • physicalFourierUnitary u p) := by
  rw [physicalFourier_translation]
  exact modulation_ae y (physicalFourierUnitary u)

/-- Maximal physical operator transported from its actual real Fourier symbol. -/
def fourierMultiplier (m : GW.Space → ℝ) :
    Lp H 2 (volume : Measure GW.Space) →ₗ.[ℂ] Lp H 2 (volume : Measure GW.Space) :=
  GW.Operators.unitaryTransport physicalFourierUnitary (realMultiplier m volume)

lemma fourierMultiplier_selfadjoint {m : GW.Space → ℝ} (hm : Measurable m) :
    IsSelfAdjointOperator (fourierMultiplier (H := H) m) :=
  GW.Operators.unitaryTransport_selfadjoint _ _ (realMultiplier_selfadjoint hm)

lemma fourierMultiplier_domain (m : GW.Space → ℝ) (u : Lp H 2 (volume : Measure GW.Space)) :
    u ∈ (fourierMultiplier m).domain ↔
      MemLp (fun p => (m p : ℂ) • physicalFourierUnitary u p) 2 (volume : Measure GW.Space) :=
  realMultiplier_domain m (physicalFourierUnitary u)

lemma fourierMultiplier_domain_map (m : GW.Space → ℝ) :
    (fourierMultiplier (H := H) m).domain =
      (realMultiplier m (volume : Measure GW.Space)).domain.map physicalFourierUnitary.symm.toLinearMap :=
  GW.Operators.unitaryTransport_domain _ _

lemma fourierMultiplier_action (m : GW.Space → ℝ) (u : (fourierMultiplier (H := H) m).domain) :
    physicalFourierUnitary (fourierMultiplier m u) =
      realMultiplier m (volume : Measure GW.Space)
        ⟨physicalFourierUnitary (u : Lp H 2 (volume : Measure GW.Space)),u.property⟩ :=
  physicalFourierUnitary.apply_symm_apply _

def momentumOperator (j : Fin 3) :
    Lp H 2 (volume : Measure GW.Space) →ₗ.[ℂ] Lp H 2 (volume : Measure GW.Space) :=
  fourierMultiplier (fun p => p j)

lemma momentumOperator_selfadjoint (j : Fin 3) : IsSelfAdjointOperator (momentumOperator (H := H) j) :=
  fourierMultiplier_selfadjoint ((EuclideanSpace.proj j).continuous.measurable)

lemma momentumOperator_domain (j : Fin 3) (u : Lp H 2 (volume : Measure GW.Space)) :
    u ∈ (momentumOperator j).domain ↔
      MemLp (fun p : GW.Space => (p j : ℂ) • physicalFourierUnitary u p) 2 (volume : Measure GW.Space) :=
  fourierMultiplier_domain (fun p => p j) u

def absoluteMomentumPower (s : ℝ) :
    Lp H 2 (volume : Measure GW.Space) →ₗ.[ℂ] Lp H 2 (volume : Measure GW.Space) :=
  fourierMultiplier (fun p => ‖p‖^s)

lemma absoluteMomentumPower_selfadjoint (s : ℝ) : IsSelfAdjointOperator (absoluteMomentumPower (H := H) s) :=
  fourierMultiplier_selfadjoint (by fun_prop)

lemma absoluteMomentumPower_domain (s : ℝ) (u : Lp H 2 (volume : Measure GW.Space)) :
    u ∈ (absoluteMomentumPower s).domain ↔
      MemLp (fun p : GW.Space => (↑(‖p‖^s) : ℂ) • physicalFourierUnitary u p) 2 (volume : Measure GW.Space) :=
  fourierMultiplier_domain (fun p => ‖p‖^s) u

lemma physicalFourier_schwartz_ae (f : SchwartzMap GW.Space H) :
    physicalFourierUnitary (f.toLp 2) =ᵐ[volume] physicalFourierIntegral f := by
  rw [physicalFourier_schwartz]
  filter_upwards [(schwartzPhysicalFourier f).coeFn_toLp 2 (volume : Measure GW.Space)] with p hp
  exact hp.trans (schwartzPhysicalFourier_apply f p)

lemma physicalFourierInv_schwartz_ae (f : SchwartzMap GW.Space H) :
    physicalFourierUnitary.symm (f.toLp 2) =ᵐ[volume] physicalFourierInvIntegral f := by
  rw [physicalFourierInv_schwartz]
  filter_upwards [(schwartzPhysicalFourierInv f).coeFn_toLp 2 (volume : Measure GW.Space)] with x hx
  exact hx.trans (schwartzPhysicalFourierInv_apply f x)

end FourierActions
end GW.Analysis

