module
public import GW.Operators.BasicTestDensity
public import GW.Analysis.BridgeStrongWeak
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff InnerProductSpace FourierTransform LineDeriv BigOperators
namespace GW.Analysis

lemma inner_momentumAxis (p : GW.Space) (j : Fin 3) : ⟪p,momentumAxis j⟫_ℝ = p j := by
  rw [momentumAxis,EuclideanSpace.inner_single_right]
  simp

def weakPlateauInput : GW.Space → ℝ :=
  (Metric.ball (0 : GW.Space) 2).indicator (fun _ => 1)

lemma weakPlateauInput_integrable : Integrable weakPlateauInput (volume : Measure GW.Space) :=
  (integrable_indicator_iff measurableSet_ball).mpr (integrableOn_const measure_ball_lt_top.ne)

lemma weakPlateauInput_range (x : GW.Space) : 0 ≤ weakPlateauInput x ∧ weakPlateauInput x ≤ 1 := by
  unfold weakPlateauInput
  by_cases h : x ∈ Metric.ball (0 : GW.Space) 2 <;> simp [h]

def weakPlateau : GW.Space → ℝ :=
  smoothConvolution (testMollifierScaled (1/8)) weakPlateauInput

lemma weakPlateau_contDiff : ContDiff ℝ ∞ weakPlateau :=
  smoothConvolution_contDiff (testMollifierScaled_contDiff _) (testMollifierScaled_hasCompactSupport _ (by norm_num))
    weakPlateauInput_integrable

lemma weakPlateau_support : tsupport weakPlateau ⊆ Metric.closedBall (0 : GW.Space) 3 := by
  have hs := smoothConvolution_support (testMollifierScaled_hasCompactSupport (1/8) (by norm_num))
    weakPlateauInput (Metric.closedBall (0 : GW.Space) 2) (isCompact_closedBall _ _)
    (Eventually.of_forall (fun x hx => indicator_of_notMem
      (fun h => hx (Metric.ball_subset_closedBall h)) _))
  intro x hx
  obtain ⟨y,hy,z,hz,rfl⟩ := Set.mem_add.mp (hs hx)
  have hy' : ‖y‖ ≤ 2*(1/8:ℝ) := by
    simpa only [Metric.mem_closedBall,dist_zero_right] using
      testMollifierScaled_support_subset (1/8) (by norm_num) hy
  have hz' : ‖z‖ ≤ 2 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hz
  apply Metric.mem_closedBall.mpr
  rw [dist_zero_right]
  exact (norm_add_le _ _).trans (by linarith)

lemma weakPlateau_hasCompactSupport : HasCompactSupport weakPlateau :=
  (isCompact_closedBall _ _).of_isClosed_subset isClosed_closure weakPlateau_support

lemma weakPlateau_mass_at (x : GW.Space) :
    (∫ y, testMollifierScaled (1/8) (x-y) ∂(volume : Measure GW.Space)) = 1 := by
  let R : GW.Space ≃ₜ GW.Space := Homeomorph.subLeft x
  have hR : MeasurePreserving R (volume : Measure GW.Space) volume := testReflection_preserving x
  exact (hR.integral_comp R.measurableEmbedding (testMollifierScaled (1/8))).trans
    (testMollifierScaled_integral (1/8) (by norm_num))

lemma weakPlateau_range (x : GW.Space) : 0 ≤ weakPlateau x ∧ weakPlateau x ≤ 1 := by
  let ε : ℝ := 1/8
  have hε : 0 < ε := by norm_num [ε]
  have hρ : Integrable (testMollifierScaled ε) (volume : Measure GW.Space) :=
    (testMollifierScaled_contDiff ε).continuous.integrable_of_hasCompactSupport
      (testMollifierScaled_hasCompactSupport ε hε)
  have hρx := (testReflection_preserving x).integrable_comp_of_integrable hρ
  have hg : Integrable (fun y => testMollifierScaled ε (x-y) * weakPlateauInput y) (volume : Measure GW.Space) := by
    apply hρx.mono'
      (((testMollifierScaled_contDiff ε).continuous.comp (continuous_sub_left x)).aestronglyMeasurable.mul
        weakPlateauInput_integrable.1)
    exact Eventually.of_forall (fun y => by
      change ‖testMollifierScaled ε (x-y) * weakPlateauInput y‖ ≤ testMollifierScaled ε (x-y)
      rw [Real.norm_of_nonneg (mul_nonneg (testMollifierScaled_nonneg ε hε _) (weakPlateauInput_range y).1)]
      exact (mul_le_mul_of_nonneg_left (weakPlateauInput_range y).2 (testMollifierScaled_nonneg ε hε _)).trans_eq (mul_one _))
  change 0 ≤ (∫ y, testMollifierScaled ε (x-y) * weakPlateauInput y) ∧
    (∫ y, testMollifierScaled ε (x-y) * weakPlateauInput y) ≤ 1
  refine ⟨integral_nonneg (fun y => mul_nonneg (testMollifierScaled_nonneg ε hε _) (weakPlateauInput_range y).1),?_⟩
  rw [← weakPlateau_mass_at x]
  exact integral_mono hg hρx (fun y =>
    (mul_le_mul_of_nonneg_left (weakPlateauInput_range y).2 (testMollifierScaled_nonneg ε hε _)).trans_eq (mul_one _))

lemma weakPlateau_eq_one (x : GW.Space) (hx : ‖x‖ ≤ 1) : weakPlateau x = 1 := by
  unfold weakPlateau smoothConvolution
  refine (integral_congr_ae ?_).trans (weakPlateau_mass_at x)
  exact Eventually.of_forall (fun y => by
    change testMollifierScaled (1/8) (x-y) * weakPlateauInput y = testMollifierScaled (1/8) (x-y)
    by_cases h : 2*(1/8:ℝ) < ‖x-y‖
    · rw [scaledMollifier_zero_outside (1/8) (by norm_num) h,zero_mul]
    · have hb : ‖y‖ ≤ ‖x‖+‖x-y‖ := by
        have hh := norm_sub_le x (x-y)
        rwa [sub_sub_cancel] at hh
      have hmem : y ∈ Metric.ball (0:GW.Space) 2 := by
        rw [Metric.mem_ball,dist_zero_right]
        linarith [le_of_not_gt h]
      rw [weakPlateauInput,indicator_of_mem hmem,mul_one])

def weakPlateauScaled (R : ℝ) (x : GW.Space) : ℝ := weakPlateau (R⁻¹ • x)

lemma weakPlateauScaled_contDiff (R : ℝ) : ContDiff ℝ ∞ (weakPlateauScaled R) :=
  weakPlateau_contDiff.comp (contDiff_id.const_smul R⁻¹)

lemma weakPlateauScaled_hasCompactSupport (R : ℝ) (hR : 0 < R) :
    HasCompactSupport (weakPlateauScaled R) :=
  weakPlateau_hasCompactSupport.comp_smul (inv_ne_zero hR.ne')

lemma weakPlateauScaled_eq_one (R : ℝ) (hR : 0 < R) (x : GW.Space) (hx : ‖x‖ ≤ R) :
    weakPlateauScaled R x = 1 := by
  apply weakPlateau_eq_one
  rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hR.le),inv_mul_eq_div]
  exact (div_le_one hR).mpr hx

lemma weakPlateau_axis_bound (j : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∀ x : GW.Space,
      ‖fderiv ℝ (weakPlateauScaled R) x (momentumAxis j)‖ ≤ C/R := by
  have hc := weakPlateau_contDiff.continuous_fderiv (by simp : (∞ : ℕ∞ω) ≠ 0)
  obtain ⟨C,hC⟩ := (weakPlateau_hasCompactSupport.fderiv (𝕜 := ℝ)).exists_bound_of_continuous hc
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine ⟨C,hC0,?_⟩
  intro R hR x
  let L : GW.Space →L[ℝ] GW.Space := R⁻¹ • ContinuousLinearMap.id ℝ GW.Space
  have hL : HasFDerivAt (fun x : GW.Space => R⁻¹ • x) L x := L.hasFDerivAt
  have hP := (weakPlateau_contDiff.differentiable (by simp : (∞ : ℕ∞ω) ≠ 0) (R⁻¹ • x)).hasFDerivAt
  have he := (hP.comp x hL).fderiv
  change fderiv ℝ (weakPlateauScaled R) x = _ at he
  rw [he]
  change ‖fderiv ℝ weakPlateau (R⁻¹ • x) (R⁻¹ • momentumAxis j)‖ ≤ _
  rw [map_smul,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hR.le)]
  calc
    _ ≤ R⁻¹ * (‖fderiv ℝ weakPlateau (R⁻¹ • x)‖*‖momentumAxis j‖) :=
      mul_le_mul_of_nonneg_left ((fderiv ℝ weakPlateau (R⁻¹ • x)).le_opNorm _) (inv_nonneg.mpr hR.le)
    _ ≤ _ := by
      rw [momentumAxis_norm,mul_one,div_eq_mul_inv,mul_comm C]
      exact mul_le_mul_of_nonneg_left (hC _) (inv_nonneg.mpr hR.le)

section WeakMomentum
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

abbrev ElectronHilbertL2 := Lp E 2 (volume : Measure GW.Space)

def schwartzMomentumDerivative (j : Fin 3) (f : SchwartzMap GW.Space E) : SchwartzMap GW.Space E :=
  (-Complex.I) • LineDeriv.lineDerivOp (momentumAxis j) f

lemma schwartzMomentumDerivative_apply (j : Fin 3) (f : SchwartzMap GW.Space E) (x : GW.Space) :
    schwartzMomentumDerivative j f x = (-Complex.I) • fderiv ℝ f x (momentumAxis j) :=
  rfl

lemma schwartzMomentumDerivative_physical (j : Fin 3) (f : SchwartzMap GW.Space E) (p : GW.Space) :
    schwartzPhysicalFourier (schwartzMomentumDerivative j f) p =
      (p j : ℂ) • schwartzPhysicalFourier f p := by
  let a : ℝ := 2*Real.pi
  let A : ℂ := dilationAmplitude a
  have ha : a ≠ 0 := physicalFourierScale_pos.ne'
  unfold schwartzPhysicalFourier
  rw [schwartzDilation_apply,schwartzDilation_apply,schwartzMomentumDerivative,FourierTransform.fourier_smul,
    SchwartzMap.fourier_lineDerivOp_eq]
  have hm : (fun q : GW.Space => ⟪q,momentumAxis j⟫_ℝ).HasTemperateGrowth :=
    ((innerSL ℝ).flip (momentumAxis j)).hasTemperateGrowth
  rw [SchwartzMap.smul_apply,SchwartzMap.smul_apply,SchwartzMap.smulLeftCLM_apply_apply hm,
    inner_momentumAxis]
  have hcast : (2:ℂ) * (Real.pi:ℂ) = (a:ℂ) := by
    unfold a
    push_cast
    rfl
  rw [hcast]
  let z := (𝓕 f) (a⁻¹ • p)
  have hq : (a⁻¹ • p) j = a⁻¹ * p j := rfl
  change A • ((-Complex.I) • (((a:ℂ)*Complex.I) • ((a⁻¹ • p) j • z))) = (p j : ℂ) • (A • z)
  rw [hq,RCLike.real_smul_eq_coe_smul (K := ℂ) (a⁻¹*p j) z]
  simp only [smul_smul]
  have he : A * (-Complex.I * ((↑a*Complex.I) * (↑(a⁻¹*p j) : ℂ))) = (p j : ℂ)*A := by
    have hb : Complex.ofReal (a⁻¹*p j) = (a:ℂ)⁻¹ * (p j : ℂ) := by
      rw [Complex.ofReal_mul,Complex.ofReal_inv]
    change A * (-Complex.I * (((a:ℂ)*Complex.I) * Complex.ofReal (a⁻¹*p j))) = (p j : ℂ)*A
    rw [hb]
    have hc : (a:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
    have hI : -Complex.I*Complex.I = 1 := by rw [neg_mul,← pow_two,Complex.I_sq,neg_neg]
    calc
      _ = A * ((-Complex.I*Complex.I) * ((↑a:ℂ)*(↑a:ℂ)⁻¹) * (p j : ℂ)) := by ring
      _ = _ := by rw [hI,mul_inv_cancel₀ hc,one_mul,one_mul,mul_comm]
  exact congrArg (fun c : ℂ => c • z) he

lemma schwartzMomentumDerivative_fourier_ae (j : Fin 3) (f : SchwartzMap GW.Space E) :
    (fun p => (p j : ℂ) • physicalFourierUnitary (f.toLp 2) p) =ᵐ[(volume : Measure GW.Space)]
      physicalFourierUnitary ((schwartzMomentumDerivative j f).toLp 2) := by
  rw [physicalFourier_schwartz,physicalFourier_schwartz]
  filter_upwards [(schwartzPhysicalFourier f).coeFn_toLp 2 (volume : Measure GW.Space),
    (schwartzPhysicalFourier (schwartzMomentumDerivative j f)).coeFn_toLp 2 (volume : Measure GW.Space)]
    with p h₁ h₂
  rw [h₁,h₂,schwartzMomentumDerivative_physical]

lemma momentumOperator_schwartz_graph (j : Fin 3) (f : SchwartzMap GW.Space E) :
    (f.toLp 2 (volume : Measure GW.Space),(schwartzMomentumDerivative j f).toLp 2 (volume : Measure GW.Space)) ∈ (momentumOperator j).graph := by
  let u : ElectronHilbertL2 (E := E) := f.toLp 2
  let v : ElectronHilbertL2 (E := E) := (schwartzMomentumDerivative j f).toLp 2
  have ha := schwartzMomentumDerivative_fourier_ae j f
  have hd : u ∈ (momentumOperator j).domain :=
    (momentumOperator_domain j u).mpr ((Lp.memLp (physicalFourierUnitary v)).ae_eq ha.symm)
  have hv : momentumOperator j ⟨u,hd⟩ = v := by
    apply physicalFourierUnitary.injective
    change physicalFourierUnitary (fourierMultiplier (fun p => p j) ⟨u,hd⟩) = physicalFourierUnitary v
    rw [fourierMultiplier_action]
    apply Lp.ext
    exact (realMultiplier_ae (fun p : GW.Space => p j) _).symm.trans ha
  exact (momentumOperator j).mem_graph_iff.mpr ⟨⟨u,hd⟩,rfl,hv⟩

def scalarSchwartzVector (f : SchwartzMap GW.Space ℂ) (e : E) : SchwartzMap GW.Space E :=
  f.postcompCLM (ContinuousLinearMap.toSpanSingleton ℂ e)

lemma scalarSchwartzVector_apply (f : SchwartzMap GW.Space ℂ) (e : E) (x : GW.Space) :
    scalarSchwartzVector f e x = f x • e := rfl

def WeakMomentumIdentity (j : Fin 3) (u v : ElectronHilbertL2 (E := E)) : Prop :=
  ∀ (φ : SmoothScalarTest) (e : E),
    ⟪(schwartzMomentumDerivative j (scalarSchwartzVector φ.toSchwartzMap e)).toLp 2,u⟫_ℂ =
      ⟪(scalarSchwartzVector φ.toSchwartzMap e).toLp 2,v⟫_ℂ

lemma momentum_graph_implies_weak (j : Fin 3) (u v : ElectronHilbertL2 (E := E))
    (h : (u,v) ∈ (momentumOperator j).graph) : WeakMomentumIdentity j u v := by
  intro φ e
  have hg := momentumOperator_schwartz_graph j (scalarSchwartzVector φ.toSchwartzMap e)
  obtain ⟨s,hs,hs'⟩ := (momentumOperator j).mem_graph_iff.mp hg
  obtain ⟨t,ht,ht'⟩ := (momentumOperator j).mem_graph_iff.mp h
  have hsa := momentumOperator_selfadjoint (H := E) j
  have hsym : (momentumOperator (H := E) j).IsFormalAdjoint (momentumOperator j) := by
    simpa only [hsa.2] using LinearPMap.adjoint_isFormalAdjoint hsa.1
  have hp := hsym s t
  change (s : ElectronHilbertL2 (E := E)) = _ at hs
  change (t : ElectronHilbertL2 (E := E)) = u at ht
  change momentumOperator j s = _ at hs'
  change momentumOperator j t = v at ht'
  rw [hs',ht,hs,ht'] at hp
  exact hp

lemma weakPlateauScaled_temperate (R : ℝ) (hR : 0 < R) :
    (weakPlateauScaled R).HasTemperateGrowth :=
  ((weakPlateauScaled_hasCompactSupport R hR).toSchwartzMap (weakPlateauScaled_contDiff R)).hasTemperateGrowth

def weakSchwartzCutoff (R : ℝ) (hR : 0 < R) (f : SchwartzMap GW.Space E) : SchwartzMap GW.Space E :=
  SchwartzMap.smulLeftCLM E (weakPlateauScaled R) f

lemma weakSchwartzCutoff_apply (R : ℝ) (hR : 0 < R) (f : SchwartzMap GW.Space E) (x : GW.Space) :
    weakSchwartzCutoff R hR f x = weakPlateauScaled R x • f x :=
  SchwartzMap.smulLeftCLM_apply_apply (weakPlateauScaled_temperate R hR) f x

def weakCutoffL2 (R : ℝ) : ElectronHilbertL2 (E := E) →L[ℂ] ElectronHilbertL2 (E := E) :=
  boundedMultiplier (fun x => (weakPlateauScaled R x : ℂ))
    (Complex.continuous_ofReal.measurable.comp (weakPlateauScaled_contDiff R).continuous.measurable)
    (C := 1) (Eventually.of_forall (fun x => by
      change ‖(weakPlateau (R⁻¹ • x) : ℂ)‖ ≤ 1
      rw [Complex.norm_real,Real.norm_of_nonneg (weakPlateau_range _).1]
      exact (weakPlateau_range _).2))

lemma weakCutoffL2_ae (R : ℝ) (u : ElectronHilbertL2 (E := E)) :
    weakCutoffL2 R u =ᵐ[(volume : Measure GW.Space)] fun x => (weakPlateauScaled R x : ℂ) • u x :=
  (boundedMultiplier_ae _ _ _ u).symm

lemma weakSchwartzCutoff_toLp (R : ℝ) (hR : 0 < R) (f : SchwartzMap GW.Space E) :
    (weakSchwartzCutoff R hR f).toLp 2 (volume : Measure GW.Space) = weakCutoffL2 R (f.toLp 2) := by
  apply Lp.ext
  filter_upwards [(weakSchwartzCutoff R hR f).coeFn_toLp 2 (volume : Measure GW.Space),
    f.coeFn_toLp 2 (volume : Measure GW.Space),weakCutoffL2_ae R (f.toLp 2)] with x h₁ h₂ h₃
  rw [h₁,h₃,h₂,weakSchwartzCutoff_apply]
  exact RCLike.real_smul_eq_coe_smul (K := ℂ) (weakPlateauScaled R x) (f x)

def weakCutoffStep (n : ℕ) : ℝ := (n:ℝ)+1

lemma weakCutoffStep_pos (n : ℕ) : 0 < weakCutoffStep n := by unfold weakCutoffStep; positivity

lemma weakCutoffStep_tendsto : Tendsto weakCutoffStep atTop atTop :=
  tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop

lemma weakCutoffL2_tendsto (u : ElectronHilbertL2 (E := E)) :
    Tendsto (fun n => weakCutoffL2 (weakCutoffStep n) u) atTop (𝓝 u) := by
  let f (n : ℕ) (x : GW.Space) := (weakPlateauScaled (weakCutoffStep n) x : ℂ) • u x
  have hrep (n : ℕ) : weakCutoffL2 (weakCutoffStep n) u =ᵐ[(volume : Measure GW.Space)] f n := weakCutoffL2_ae _ _
  have hm (n : ℕ) : AEStronglyMeasurable (f n) (volume : Measure GW.Space) :=
    (Lp.aestronglyMeasurable (weakCutoffL2 (weakCutoffStep n) u)).congr (hrep n)
  have hl : ∀ᵐ x ∂(volume : Measure GW.Space), Tendsto (fun n => f n x) atTop (𝓝 (u x)) :=
    Eventually.of_forall (fun x => by
      apply tendsto_const_nhds.congr'
      filter_upwards [weakCutoffStep_tendsto.eventually (eventually_ge_atTop ‖x‖)] with n hn
      change u x = (weakPlateauScaled (weakCutoffStep n) x : ℂ) • u x
      rw [weakPlateauScaled_eq_one _ (weakCutoffStep_pos n) x hn,Complex.ofReal_one,one_smul])
  have hb (n : ℕ) : ∀ᵐ x ∂(volume : Measure GW.Space), ‖f n x‖ ≤ ‖u x‖ :=
    Eventually.of_forall (fun x => by
      change ‖(weakPlateauScaled (weakCutoffStep n) x : ℂ) • u x‖ ≤ ‖u x‖
      rw [norm_smul,Complex.norm_real]
      have hx := weakPlateau_range ((weakCutoffStep n)⁻¹ • x)
      change ‖weakPlateau ((weakCutoffStep n)⁻¹ • x)‖ * ‖u x‖ ≤ ‖u x‖
      rw [Real.norm_of_nonneg hx.1]
      exact mul_le_of_le_one_left (norm_nonneg _) hx.2)
  obtain ⟨hs,hu,hlim⟩ := dominated_l2_convergence (𝕜 := ℂ) hm hl (Lp.stronglyMeasurable u).norm.measurable
    ((Lp.memLp u).integrable_norm_pow (p := 2) (by norm_num)) hb
  have h₁ (n : ℕ) : (hs n).toLp (f n) = weakCutoffL2 (weakCutoffStep n) u :=
    Lp.ext ((MemLp.coeFn_toLp (hs n)).trans (hrep n).symm)
  have h₂ : hu.toLp u = u := Lp.ext (MemLp.coeFn_toLp hu)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [h₁,h₂] using hlim

lemma weakSchwartzCutoff_momentum_apply (j : Fin 3) (R : ℝ) (hR : 0 < R)
    (f : SchwartzMap GW.Space E) (x : GW.Space) :
    schwartzMomentumDerivative j (weakSchwartzCutoff R hR f) x =
      (weakPlateauScaled R x : ℂ) • schwartzMomentumDerivative j f x +
      ((-Complex.I) * (fderiv ℝ (weakPlateauScaled R) x (momentumAxis j) : ℂ)) • f x := by
  have hplateau := ((weakPlateauScaled_contDiff R).differentiable (by simp) x).hasFDerivAt
  have hp := hplateau.smul (f.hasFDerivAt x)
  have he : (weakSchwartzCutoff R hR f : GW.Space → E) = fun x => weakPlateauScaled R x • f x :=
    funext (weakSchwartzCutoff_apply R hR f)
  have hd := hp.fderiv
  change fderiv ℝ (fun y => weakPlateauScaled R y • f y) x = _ at hd
  rw [schwartzMomentumDerivative_apply,he,hd,schwartzMomentumDerivative_apply]
  change (-Complex.I) •
      (weakPlateauScaled R x • fderiv ℝ f x (momentumAxis j) +
        fderiv ℝ (weakPlateauScaled R) x (momentumAxis j) • f x) = _
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ),smul_add,smul_smul]
  exact congrArg (fun c : ℂ => c • fderiv ℝ f x (momentumAxis j) +
    ((-Complex.I) * (fderiv ℝ (weakPlateauScaled R) x (momentumAxis j) : ℂ)) • f x)
    (mul_comm (-Complex.I) (weakPlateauScaled R x : ℂ))

lemma weakSchwartzCutoff_momentum_error_bound (j : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : ℝ) (hR : 0 < R) (f : SchwartzMap GW.Space E),
      ‖(schwartzMomentumDerivative j (weakSchwartzCutoff R hR f)).toLp 2 (volume : Measure GW.Space) -
          weakCutoffL2 R ((schwartzMomentumDerivative j f).toLp 2)‖ ≤ C/R * ‖f.toLp 2 (volume : Measure GW.Space)‖ := by
  obtain ⟨C,hC,hb⟩ := weakPlateau_axis_bound j
  refine ⟨C,hC,?_⟩
  intro R hR f
  let A := (schwartzMomentumDerivative j (weakSchwartzCutoff R hR f)).toLp 2 (volume : Measure GW.Space)
  let B := weakCutoffL2 R ((schwartzMomentumDerivative j f).toLp 2)
  change ‖A-B‖ ≤ _
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [(schwartzMomentumDerivative j (weakSchwartzCutoff R hR f)).coeFn_toLp 2 (volume : Measure GW.Space),
    (schwartzMomentumDerivative j f).coeFn_toLp 2 (volume : Measure GW.Space),
    f.coeFn_toLp 2 (volume : Measure GW.Space),weakCutoffL2_ae R ((schwartzMomentumDerivative j f).toLp 2),
    Lp.coeFn_sub A B] with x hA hM hf hB hAB
  change ‖(A-B) x‖ ≤ C/R*‖f.toLp 2 (volume : Measure GW.Space) x‖
  rw [hAB]
  change ‖A x-B x‖ ≤ _
  rw [hA,hB,hM,hf,weakSchwartzCutoff_momentum_apply,add_sub_cancel_left,norm_smul,norm_mul,
    norm_neg,Complex.norm_I,one_mul,Complex.norm_real]
  exact mul_le_mul_of_nonneg_right (hb R hR x) (norm_nonneg _)

lemma weakSchwartzCutoff_momentum_tendsto (j : Fin 3) (f : SchwartzMap GW.Space E) :
    Tendsto (fun n => (schwartzMomentumDerivative j (weakSchwartzCutoff (weakCutoffStep n)
      (weakCutoffStep_pos n) f)).toLp 2 (volume : Measure GW.Space)) atTop
      (𝓝 ((schwartzMomentumDerivative j f).toLp 2 (volume : Measure GW.Space))) := by
  let A (n : ℕ) := (schwartzMomentumDerivative j (weakSchwartzCutoff (weakCutoffStep n)
    (weakCutoffStep_pos n) f)).toLp 2 (volume : Measure GW.Space)
  let B (n : ℕ) := weakCutoffL2 (weakCutoffStep n) ((schwartzMomentumDerivative j f).toLp 2)
  obtain ⟨C,hC,hb⟩ := weakSchwartzCutoff_momentum_error_bound (E := E) j
  have h₀ : Tendsto (fun n => C/weakCutoffStep n*‖f.toLp 2 (volume : Measure GW.Space)‖) atTop (𝓝 0) := by
    have h := ((tendsto_inv_atTop_zero.comp weakCutoffStep_tendsto).const_mul C).mul_const
      ‖f.toLp 2 (volume : Measure GW.Space)‖
    simpa only [Function.comp_def,div_eq_mul_inv,mul_zero,zero_mul] using h
  have he : Tendsto (fun n => ‖A n-B n‖) atTop (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _) (fun n => hb _ (weakCutoffStep_pos n) f) h₀
  have hz : Tendsto (fun n => A n-B n) atTop (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mpr he
  have hB := weakCutoffL2_tendsto ((schwartzMomentumDerivative j f).toLp 2 (volume : Measure GW.Space))
  have h := hz.add hB
  simpa only [A,B,zero_add,sub_add_cancel] using h

lemma fourierMultiplier_graph_iff_ae (m : GW.Space → ℝ)
    (u v : ElectronHilbertL2 (E := E)) :
    (u,v) ∈ (fourierMultiplier m).graph ↔
      (fun p => (m p : ℂ) • physicalFourierUnitary u p) =ᵐ[(volume : Measure GW.Space)] physicalFourierUnitary v := by
  constructor
  · intro h
    obtain ⟨w,hw,hv⟩ := (fourierMultiplier m).mem_graph_iff.mp h
    change w.val = u at hw
    change fourierMultiplier m w = v at hv
    rw [← hw,← hv,fourierMultiplier_action]
    let q : (realMultiplier (H := E) m (volume : Measure GW.Space)).domain :=
      ⟨physicalFourierUnitary w.val,w.property⟩
    exact realMultiplier_ae m q
  · intro h
    have hu := (fourierMultiplier_domain m u).mpr ((Lp.memLp (physicalFourierUnitary v)).ae_eq h.symm)
    let w : (fourierMultiplier m).domain := ⟨u,hu⟩
    have hv : fourierMultiplier m w = v := by
      apply physicalFourierUnitary.injective
      rw [fourierMultiplier_action]
      apply Lp.ext
      exact (realMultiplier_ae m _).symm.trans h
    exact (fourierMultiplier m).mem_graph_iff.mpr ⟨w,rfl,hv⟩

lemma fourierMultiplier_graph_of_memLp (m : GW.Space → ℝ) (u : ElectronHilbertL2 (E := E))
    (h : MemLp (fun p => (m p : ℂ) • physicalFourierUnitary u p) 2 (volume : Measure GW.Space)) :
    ∃ v : ElectronHilbertL2 (E := E), (u,v) ∈ (fourierMultiplier m).graph :=
  ⟨_,(fourierMultiplier m).mem_graph ⟨u,(fourierMultiplier_domain m u).mpr h⟩⟩

lemma electronMomentumCoord_abs_le (p : GW.Space) (j : Fin 3) : |p j| ≤ ‖p‖ := by
  rw [← Real.norm_eq_abs]
  exact PiLp.norm_apply_le p j

lemma electronMomentumCoord_measurable (j : Fin 3) : Measurable (fun p : GW.Space => p j) :=
  (PiLp.continuous_apply 2 _ j).measurable

lemma momentum_second_domain_forward (u : ElectronHilbertL2 (E := E))
    (hu : u ∈ (absoluteMomentumPower 2).domain) :
    ∃ v : Fin 3 → ElectronHilbertL2 (E := E),
      (∀ i, (u,v i) ∈ (momentumOperator i).graph) ∧
      (∀ i j, ∃ w : ElectronHilbertL2 (E := E), (v i,w) ∈ (momentumOperator j).graph) := by
  let z := physicalFourierUnitary u
  have h₂ := (absoluteMomentumPower_domain 2 u).mp hu
  have h2 : MemLp (fun p => ((‖p‖^2 : ℝ) : ℂ) • z p) 2 (volume : Measure GW.Space) := by
    simpa only [Real.rpow_two] using h₂
  have hb : MemLp (fun p => ((1+‖p‖^2 : ℝ) : ℂ) • z p) 2 (volume : Measure GW.Space) := by
    apply ((Lp.memLp z).add h2).ae_eq
    exact Eventually.of_forall (fun p => by
      change z p + ((‖p‖^2 : ℝ) : ℂ) • z p = ((1+‖p‖^2 : ℝ) : ℂ) • z p
      rw [Complex.ofReal_add,Complex.ofReal_one,add_smul,one_smul])
  have h₁ (j : Fin 3) : MemLp (fun p => (p j : ℂ) • z p) 2 (volume : Measure GW.Space) := by
    apply hb.of_le (((Complex.continuous_ofReal.measurable.comp (electronMomentumCoord_measurable j)).aestronglyMeasurable).smul
      (Lp.aestronglyMeasurable z))
    apply Eventually.of_forall
    intro p
    change ‖(p j : ℂ) • z p‖ ≤ ‖((1+‖p‖^2 : ℝ) : ℂ) • z p‖
    rw [norm_smul,norm_smul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,
      Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ 1+‖p‖^2)]
    exact mul_le_mul_of_nonneg_right ((electronMomentumCoord_abs_le p j).trans (by nlinarith [sq_nonneg (‖p‖-1)]))
      (norm_nonneg _)
  let v (i : Fin 3) := (fourierMultiplier_graph_of_memLp (fun p => p i) u (h₁ i)).choose
  have hv (i : Fin 3) : (u,v i) ∈ (momentumOperator i).graph :=
    (fourierMultiplier_graph_of_memLp (fun p => p i) u (h₁ i)).choose_spec
  refine ⟨v,hv,?_⟩
  intro i j
  have hprod : MemLp (fun p => ((p j*p i : ℝ) : ℂ) • z p) 2 (volume : Measure GW.Space) := by
    apply h2.of_le ((Complex.continuous_ofReal.measurable.comp
      ((electronMomentumCoord_measurable j).mul (electronMomentumCoord_measurable i))).aestronglyMeasurable.smul
      (Lp.aestronglyMeasurable z))
    apply Eventually.of_forall
    intro p
    change ‖((p j*p i : ℝ) : ℂ) • z p‖ ≤ ‖((‖p‖^2 : ℝ) : ℂ) • z p‖
    rw [norm_smul,norm_smul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,abs_mul,
      Real.norm_of_nonneg (sq_nonneg ‖p‖),pow_two]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (electronMomentumCoord_abs_le p j) (electronMomentumCoord_abs_le p i) (abs_nonneg _) (norm_nonneg _))
      (norm_nonneg _)
  have hcomp : MemLp (fun p => (p j : ℂ) • physicalFourierUnitary (v i) p) 2 (volume : Measure GW.Space) := by
    apply hprod.ae_eq
    filter_upwards [(fourierMultiplier_graph_iff_ae (fun p => p i) u (v i)).mp (hv i)] with p hp
    change ((p j*p i : ℝ) : ℂ) • z p = (p j : ℂ) • physicalFourierUnitary (v i) p
    rw [← hp,Complex.ofReal_mul,smul_smul]
  exact fourierMultiplier_graph_of_memLp (fun p => p j) (v i) hcomp

lemma momentum_second_domain_reverse (u : ElectronHilbertL2 (E := E))
    (h : ∃ v : Fin 3 → ElectronHilbertL2 (E := E),
      (∀ i, (u,v i) ∈ (momentumOperator i).graph) ∧
      (∀ i, ∃ w : ElectronHilbertL2 (E := E), (v i,w) ∈ (momentumOperator i).graph)) :
    u ∈ (absoluteMomentumPower 2).domain := by
  obtain ⟨v,hv,hw⟩ := h
  let w (i : Fin 3) := (hw i).choose
  let z := physicalFourierUnitary u
  have he (i : Fin 3) : (fun p => (((p i)^2 : ℝ) : ℂ) • z p) =ᵐ[(volume : Measure GW.Space)]
      physicalFourierUnitary (w i) := by
    filter_upwards [(fourierMultiplier_graph_iff_ae (fun p => p i) u (v i)).mp (hv i),
      (fourierMultiplier_graph_iff_ae (fun p => p i) (v i) (w i)).mp (hw i).choose_spec] with p hp hq
    change (((p i)^2 : ℝ) : ℂ) • z p = _
    rw [pow_two,Complex.ofReal_mul,mul_smul]
    exact (congrArg (fun y : E => (p i : ℂ) • y) hp).trans hq
  have hs (i : Fin 3) : MemLp (fun p => (((p i)^2 : ℝ) : ℂ) • z p) 2 (volume : Measure GW.Space) :=
    (Lp.memLp (physicalFourierUnitary (w i))).ae_eq (he i).symm
  have hf (s : Finset (Fin 3)) : MemLp (fun p => ∑ i ∈ s, (((p i)^2 : ℝ) : ℂ) • z p) 2 (volume : Measure GW.Space) := by
    classical
    induction s using Finset.induction_on with
    | empty => simp only [Finset.sum_empty]; exact MemLp.zero
    | insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (hs i).add ih
  apply (absoluteMomentumPower_domain 2 u).mpr
  apply (hf Finset.univ).ae_eq
  exact Eventually.of_forall (fun p => by
    change (∑ i : Fin 3, (((p i)^2 : ℝ) : ℂ) • z p) = ((‖p‖^(2:ℝ) : ℝ) : ℂ) • z p
    rw [← Finset.sum_smul,← Complex.ofReal_sum,Real.rpow_two,EuclideanSpace.real_norm_sq_eq])

def weakCutoffScalarTest (R : ℝ) (hR : 0 < R) (f : SchwartzMap GW.Space ℂ) : SmoothScalarTest where
  value := weakSchwartzCutoff R hR f
  smooth := (weakSchwartzCutoff R hR f).smooth (⊤ : ℕ∞)
  compact := by
    have h : HasCompactSupport (fun x : GW.Space => weakPlateauScaled R x • f x) :=
      (weakPlateauScaled_hasCompactSupport R hR).smul_right (f' := (f : GW.Space → ℂ))
    rw [show (weakSchwartzCutoff R hR f : GW.Space → ℂ) = (fun x => weakPlateauScaled R x • f x)
      from funext (weakSchwartzCutoff_apply R hR f)]
    exact h

lemma weakCutoffScalarTest_vector (R : ℝ) (hR : 0 < R) (f : SchwartzMap GW.Space ℂ) (e : E) :
    scalarSchwartzVector (weakCutoffScalarTest R hR f).toSchwartzMap e =
      weakSchwartzCutoff R hR (scalarSchwartzVector f e) := by
  ext x
  rw [scalarSchwartzVector_apply,SmoothScalarTest.toSchwartzMap_apply,weakSchwartzCutoff_apply,scalarSchwartzVector_apply]
  change weakSchwartzCutoff R hR f x • e = _
  rw [weakSchwartzCutoff_apply,RCLike.real_smul_eq_coe_smul (K := ℂ) (weakPlateauScaled R x) (f x),
    RCLike.real_smul_eq_coe_smul (K := ℂ) (weakPlateauScaled R x) (f x • e),smul_eq_mul,mul_smul]

lemma weakMomentumIdentity_schwartz (j : Fin 3) (u v : ElectronHilbertL2 (E := E))
    (h : WeakMomentumIdentity j u v) (f : SchwartzMap GW.Space ℂ) (e : E) :
    ⟪(schwartzMomentumDerivative j (scalarSchwartzVector f e)).toLp 2,u⟫_ℂ =
      ⟪(scalarSchwartzVector f e).toLp 2,v⟫_ℂ := by
  let z := scalarSchwartzVector f e
  let q (n : ℕ) := weakSchwartzCutoff (weakCutoffStep n) (weakCutoffStep_pos n) z
  have h₁ : Tendsto (fun n => (q n).toLp 2 (volume : Measure GW.Space)) atTop (𝓝 (z.toLp 2)) := by
    have hv := weakCutoffL2_tendsto (z.toLp 2 (volume : Measure GW.Space))
    exact hv.congr' (Eventually.of_forall (fun n => (weakSchwartzCutoff_toLp _ _ z).symm))
  have h₂ := weakSchwartzCutoff_momentum_tendsto j z
  have hl := h₂.inner (𝕜 := ℂ) (tendsto_const_nhds (x := u))
  have hr := h₁.inner (𝕜 := ℂ) (tendsto_const_nhds (x := v))
  apply tendsto_nhds_unique hl
  apply hr.congr'
  apply Eventually.of_forall
  intro n
  have he := h (weakCutoffScalarTest (weakCutoffStep n) (weakCutoffStep_pos n) f) e
  rw [weakCutoffScalarTest_vector] at he
  exact he.symm

lemma scalarSchwartzVector_toLp (f : SchwartzMap GW.Space ℂ) (e : E) :
    (scalarSchwartzVector f e).toLp 2 (volume : Measure GW.Space) =
      (ContinuousLinearMap.toSpanSingleton ℂ e).compLpL 2 volume (f.toLp 2) := by
  apply Lp.ext
  filter_upwards [(scalarSchwartzVector f e).coeFn_toLp 2 (volume : Measure GW.Space),
    f.coeFn_toLp 2 (volume : Measure GW.Space),
    (ContinuousLinearMap.toSpanSingleton ℂ e).coeFn_compLp (f.toLp 2 (volume : Measure GW.Space))]
    with x h₁ h₂ h₃
  change ((scalarSchwartzVector f e).toLp 2 (volume : Measure GW.Space)) x =
    ((ContinuousLinearMap.toSpanSingleton ℂ e).compLp (f.toLp 2 (volume : Measure GW.Space))) x
  rw [h₁,h₃,h₂]
  rfl

lemma scalarSchwartzVector_fourier (f : SchwartzMap GW.Space ℂ) (e : E) :
    schwartzPhysicalFourier (scalarSchwartzVector f e) =
      scalarSchwartzVector (schwartzPhysicalFourier f) e := by
  ext p
  rw [scalarSchwartzVector_apply,schwartzPhysicalFourier_apply,schwartzPhysicalFourier_apply]
  let L := ContinuousLinearMap.toSpanSingleton ℂ e
  have hi : Integrable (fun x => physicalPhase p x • f x) (volume : Measure GW.Space) := by
    apply f.integrable.norm.mono'
      (((continuous_physicalPhase p).smul f.continuous).aestronglyMeasurable)
    exact Eventually.of_forall (fun x => by
      change ‖physicalPhase p x • f x‖ ≤ ‖f x‖
      rw [norm_smul,physicalPhase_norm,one_mul])
  change (dilationAmplitude (2*Real.pi) : ℂ) • ∫ x, physicalPhase p x • L (f x) =
    L ((dilationAmplitude (2*Real.pi) : ℂ) • ∫ x, physicalPhase p x • f x)
  rw [map_smul,← L.integral_comp_comm hi]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => (L.map_smul (physicalPhase p x) (f x)).symm)

lemma scalarSchwartzVector_fourierInv_toLp (θ : SchwartzMap GW.Space ℂ) (e : E) :
    physicalFourierUnitary ((scalarSchwartzVector (schwartzPhysicalFourierInv θ) e).toLp 2 (volume : Measure GW.Space)) =
      (scalarSchwartzVector θ e).toLp 2 (volume : Measure GW.Space) := by
  rw [physicalFourier_schwartz,scalarSchwartzVector_fourier,scalarSchwartzVector_toLp,scalarSchwartzVector_toLp]
  congr 1
  rw [← physicalFourier_schwartz,← physicalFourierInv_schwartz,LinearIsometryEquiv.apply_symm_apply]

lemma weakMomentumIdentity_implies_graph (j : Fin 3) (u v : ElectronHilbertL2 (E := E))
    (h : WeakMomentumIdentity j u v) : (u,v) ∈ (momentumOperator j).graph := by
  let U := physicalFourierUnitary u
  let V := physicalFourierUnitary v
  let g (p : GW.Space) := (p j : ℂ) • U p-V p
  have hloc : LocalSquareIntegrable g := by
    intro R
    let μ := (volume : Measure GW.Space).restrict (Metric.closedBall (0 : GW.Space) (R:ℝ))
    have hU : MemLp (U : GW.Space → E) 2 μ := (Lp.memLp U).mono_measure Measure.restrict_le_self
    have hV : MemLp (V : GW.Space → E) 2 μ := (Lp.memLp V).mono_measure Measure.restrict_le_self
    have hm : AEStronglyMeasurable (fun p => (p j : ℂ) • U p) μ :=
      (Complex.continuous_ofReal.measurable.comp ((PiLp.continuous_apply 2 _ j).measurable)).aestronglyMeasurable.smul hU.aestronglyMeasurable
    have hb := hU.of_le_mul (c := (R:ℝ)) hm (by
      filter_upwards [ae_restrict_mem measurableSet_closedBall] with p hp
      change ‖(p j : ℂ) • U p‖ ≤ (R:ℝ)*‖U p‖
      rw [norm_smul,Complex.norm_real,Real.norm_eq_abs]
      have hR : ‖p‖ ≤ (R:ℝ) := by simpa only [Metric.mem_closedBall,dist_zero_right] using hp
      exact mul_le_mul_of_nonneg_right ((electronMomentumCoord_abs_le p j).trans hR) (norm_nonneg _))
    exact hb.sub hV
  have hzero : g =ᵐ[(volume : Measure GW.Space)] 0 := by
    apply localSquareIntegrable_hilbert_vanishes_of_tests g hloc
    intro θ e
    let f := scalarSchwartzVector (schwartzPhysicalFourierInv θ.toSchwartzMap) e
    let w := (scalarSchwartzVector θ.toSchwartzMap e).toLp 2 (volume : Measure GW.Space)
    let M := physicalFourierUnitary ((schwartzMomentumDerivative j f).toLp 2 (volume : Measure GW.Space))
    have hW : physicalFourierUnitary (f.toLp 2 (volume : Measure GW.Space)) = w :=
      scalarSchwartzVector_fourierInv_toLp _ e
    have hM := schwartzMomentumDerivative_fourier_ae j f
    rw [hW] at hM
    have hp : ⟪M,U⟫_ℂ = ⟪w,V⟫_ℂ := by
      rw [← hW]
      change ⟪physicalFourierUnitary ((schwartzMomentumDerivative j f).toLp 2 (volume : Measure GW.Space)),physicalFourierUnitary u⟫_ℂ =
        ⟪physicalFourierUnitary (f.toLp 2 (volume : Measure GW.Space)),physicalFourierUnitary v⟫_ℂ
      rw [LinearIsometryEquiv.inner_map_map,LinearIsometryEquiv.inner_map_map]
      exact weakMomentumIdentity_schwartz j u v h _ e
    have hw : (w : GW.Space → E) =ᵐ[(volume : Measure GW.Space)] fun p => θ.value p • e := by
      exact (scalarSchwartzVector θ.toSchwartzMap e).coeFn_toLp 2 _
    have ha : (fun p => ⟪M p,U p⟫_ℂ) =ᵐ[(volume : Measure GW.Space)]
        fun p => ⟪θ.value p • e,(p j : ℂ) • U p⟫_ℂ := by
      filter_upwards [hM,hw] with p hm hq
      change (p j : ℂ) • w p = M p at hm
      change ⟪M p,U p⟫_ℂ = ⟪θ.value p • e,(p j : ℂ) • U p⟫_ℂ
      rw [← hm,hq,inner_smul_left,inner_smul_right,Complex.conj_ofReal]
    have hb : (fun p => ⟪w p,V p⟫_ℂ) =ᵐ[(volume : Measure GW.Space)]
        fun p => ⟪θ.value p • e,V p⟫_ℂ :=
      hw.mono (fun p hp => congrArg (fun y : E => ⟪y,V p⟫_ℂ) hp)
    have hia := (L2.integrable_inner M U).congr ha
    have hib := (L2.integrable_inner w V).congr hb
    simp_rw [g,inner_sub_right]
    rw [integral_sub hia hib,← integral_congr_ae ha,← integral_congr_ae hb,← L2.inner_def,← L2.inner_def,hp,sub_self]
  apply (fourierMultiplier_graph_iff_ae (fun p => p j) u v).mpr
  exact hzero.mono (fun p hp => sub_eq_zero.mp hp)

lemma momentum_graph_iff_weak (j : Fin 3) (u v : ElectronHilbertL2 (E := E)) :
    (u,v) ∈ (momentumOperator j).graph ↔ WeakMomentumIdentity j u v :=
  ⟨momentum_graph_implies_weak j u v,weakMomentumIdentity_implies_graph j u v⟩

lemma momentum_second_domain_iff_weak (u : ElectronHilbertL2 (E := E)) :
    u ∈ (absoluteMomentumPower 2).domain ↔
      ∃ v : Fin 3 → ElectronHilbertL2 (E := E),
        (∀ i, WeakMomentumIdentity i u (v i)) ∧
        (∀ i j, ∃ w : ElectronHilbertL2 (E := E), WeakMomentumIdentity j (v i) w) := by
  constructor
  · intro hu
    obtain ⟨v,hv,hw⟩ := momentum_second_domain_forward u hu
    exact ⟨v,fun i => (momentum_graph_iff_weak i u (v i)).mp (hv i),
      fun i j => ⟨(hw i j).choose,(momentum_graph_iff_weak j (v i) (hw i j).choose).mp (hw i j).choose_spec⟩⟩
  · rintro ⟨v,hv,hw⟩
    apply momentum_second_domain_reverse u
    exact ⟨v,fun i => (momentum_graph_iff_weak i u (v i)).mpr (hv i),
      fun i => ⟨(hw i i).choose,(momentum_graph_iff_weak i (v i) (hw i i).choose).mpr (hw i i).choose_spec⟩⟩

lemma scalarSchwartzVector_momentum_apply (j : Fin 3) (f : SchwartzMap GW.Space ℂ) (e : E) (x : GW.Space) :
    schwartzMomentumDerivative j (scalarSchwartzVector f e) x =
      ((-Complex.I) * fderiv ℝ f x (momentumAxis j)) • e := by
  let L := ContinuousLinearMap.toSpanSingleton ℂ e
  have h := (L.restrictScalars ℝ).hasFDerivAt.comp x (f.hasFDerivAt x)
  have he : fderiv ℝ (scalarSchwartzVector f e : GW.Space → E) x =
      (L.restrictScalars ℝ).comp (fderiv ℝ f x) := h.fderiv
  rw [schwartzMomentumDerivative_apply,he]
  change (-Complex.I) • (fderiv ℝ f x (momentumAxis j) • e) = _
  rw [smul_smul]

lemma momentum_twoStep_fourier_ae (i j : Fin 3) (u v w : ElectronHilbertL2 (E := E))
    (hv : (u,v) ∈ (momentumOperator i).graph) (hw : (v,w) ∈ (momentumOperator j).graph) :
    (fun p => ((p j*p i : ℝ) : ℂ) • physicalFourierUnitary u p) =ᵐ[(volume : Measure GW.Space)]
      physicalFourierUnitary w := by
  filter_upwards [(fourierMultiplier_graph_iff_ae (fun p => p i) u v).mp hv,
    (fourierMultiplier_graph_iff_ae (fun p => p j) v w).mp hw] with p hp hq
  change ((p j*p i : ℝ) : ℂ) • physicalFourierUnitary u p = _
  rw [Complex.ofReal_mul,mul_smul]
  exact (congrArg (fun y : E => (p j : ℂ) • y) hp).trans hq

lemma momentum_second_sum_graph (u : ElectronHilbertL2 (E := E))
    (v w : Fin 3 → ElectronHilbertL2 (E := E))
    (hv : ∀ i, (u,v i) ∈ (momentumOperator i).graph)
    (hw : ∀ i, (v i,w i) ∈ (momentumOperator i).graph) :
    (u,∑ i, w i) ∈ (absoluteMomentumPower 2).graph := by
  apply (fourierMultiplier_graph_iff_ae (fun p => ‖p‖^(2:ℝ)) u _).mpr
  have hs := Lp.coeFn_fun_finsetSum Finset.univ (fun i => physicalFourierUnitary (w i))
  have hcomp (i : Fin 3) := momentum_twoStep_fourier_ae i i u (v i) (w i) (hv i) (hw i)
  rw [map_sum]
  apply EventuallyEq.trans _ hs.symm
  filter_upwards [ae_all_iff.mpr hcomp] with p hp
  change (↑(‖p‖^(2:ℝ)) : ℂ) • physicalFourierUnitary u p = ∑ i : Fin 3, physicalFourierUnitary (w i) p
  rw [Real.rpow_two,EuclideanSpace.real_norm_sq_eq,Complex.ofReal_sum,Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [pow_two] using hp i

end WeakMomentum
end GW.Analysis
