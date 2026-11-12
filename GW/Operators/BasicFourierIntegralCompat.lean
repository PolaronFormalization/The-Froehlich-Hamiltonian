module
public import GW.Operators.BasicTestDensity
public import GW.Analysis.Fourier
public import Mathlib.MeasureTheory.Integral.Prod
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace
namespace GW.Analysis

lemma physicalPhase_joint_continuous :
    Continuous (fun q : GW.Space × GW.Space => physicalPhase q.1 q.2) := by
  unfold physicalPhase
  fun_prop

lemma physicalPhase_inverse_conjugate (p x : GW.Space) :
    (starRingEnd ℂ) (physicalPhase (-x) p) = physicalPhase p x := by
  unfold physicalPhase
  rw [inner_neg_right,neg_neg,← Complex.exp_conj,map_mul,Complex.conj_ofReal,Complex.conj_I,
    mul_neg,← neg_mul,← Complex.ofReal_neg,real_inner_comm]

section PhysicalIntegral
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

lemma physicalPhase_smul_integrable (f : GW.Space → E) (hf : Integrable f volume) (p : GW.Space) :
    Integrable (fun x => physicalPhase p x • f x) (volume : Measure GW.Space) := by
  apply hf.norm.mono' ((continuous_physicalPhase p).aestronglyMeasurable.smul hf.1)
  exact Eventually.of_forall (fun x => by
    change ‖physicalPhase p x • f x‖ ≤ ‖f x‖
    rw [norm_smul,physicalPhase_norm,one_mul])

lemma physicalFourierIntegral_norm_bound (f : GW.Space → E) (hf : Integrable f volume) (p : GW.Space) :
    ‖physicalFourierIntegral f p‖ ≤
      dilationAmplitude (2*Real.pi) * ∫ x, ‖f x‖ ∂(volume : Measure GW.Space) := by
  have ha : 0 ≤ dilationAmplitude (2*Real.pi) :=
    Real.rpow_nonneg physicalFourierScale_pos.le _
  rw [physicalFourierIntegral,norm_smul,Complex.norm_real,Real.norm_of_nonneg ha]
  apply mul_le_mul_of_nonneg_left _ ha
  exact norm_integral_le_of_norm_le hf.norm (Eventually.of_forall (fun x => by
    change ‖physicalPhase p x • f x‖ ≤ ‖f x‖
    rw [norm_smul,physicalPhase_norm,one_mul]))

lemma physicalFourierIntegral_continuous (f : GW.Space → E) (hf : Integrable f volume) :
    Continuous (physicalFourierIntegral f) := by
  apply continuous_iff_seqContinuous.mpr
  intro p q h
  have hlim : Tendsto (fun n => ∫ x, physicalPhase (p n) x • f x ∂(volume : Measure GW.Space))
      atTop (𝓝 (∫ x, physicalPhase q x • f x ∂(volume : Measure GW.Space))) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
      (fun n => (physicalPhase_smul_integrable f hf (p n)).1) hf.norm
    · exact fun n => Eventually.of_forall (fun x => by
        change ‖physicalPhase (p n) x • f x‖ ≤ ‖f x‖
        rw [norm_smul,physicalPhase_norm,one_mul])
    · apply Eventually.of_forall
      intro x
      have hc : Continuous (fun y : GW.Space => physicalPhase y x • f x) :=
        (physicalPhase_joint_continuous.comp (continuous_id.prodMk continuous_const)).smul continuous_const
      exact hc.continuousAt.tendsto.comp h
  exact hlim.const_smul (dilationAmplitude (2*Real.pi) : ℂ)

lemma physicalIntegral_localSquareIntegrable (f : GW.Space → E) (hf : Integrable f volume) :
    LocalSquareIntegrable (physicalFourierIntegral f) := by
  intro R
  let μ := (volume : Measure GW.Space).restrict (Metric.closedBall (0:GW.Space) (R:ℝ))
  let C : ℝ := dilationAmplitude (2*Real.pi) * ∫ x, ‖f x‖ ∂(volume : Measure GW.Space)
  letI : IsFiniteMeasure μ := ⟨by rw [Measure.restrict_apply_univ]; exact measure_closedBall_lt_top⟩
  have hm : AEStronglyMeasurable (physicalFourierIntegral f) μ :=
    (physicalFourierIntegral_continuous f hf).stronglyMeasurable.aestronglyMeasurable
  have hC : 0 ≤ C := (norm_nonneg _).trans (physicalFourierIntegral_norm_bound f hf 0)
  apply (memLp_const C : MemLp (fun _ : GW.Space => C) 2 μ).of_le hm
  exact Eventually.of_forall (fun p =>
    (physicalFourierIntegral_norm_bound f hf p).trans_eq (Real.norm_of_nonneg hC).symm)

def fourierIntegralPairingIntegrand (θ f : GW.Space → E) (p : GW.Space × GW.Space) : ℂ :=
  ⟪θ p.1,physicalPhase p.1 p.2 • f p.2⟫_ℂ

lemma fourierIntegralPairingIntegrand_integrable (θ f : GW.Space → E) (hθ : Integrable θ volume)
    (hf : Integrable f volume) :
    Integrable (fourierIntegralPairingIntegrand θ f) ((volume : Measure GW.Space).prod volume) := by
  have hi : Integrable (fun p : GW.Space × GW.Space => ‖θ p.1‖ * ‖f p.2‖)
      ((volume : Measure GW.Space).prod volume) :=
    hθ.norm.op_fst_snd (op := (·*·)) continuous_mul
      ⟨1,fun x y => by rw [one_mul,norm_mul]⟩ hf.norm
  apply hi.mono'
  · exact (continuous_inner (𝕜 := ℂ)).comp_aestronglyMeasurable₂ hθ.1.comp_fst
      (physicalPhase_joint_continuous.aestronglyMeasurable.smul hf.1.comp_snd)
  · apply Eventually.of_forall
    intro p
    change ‖⟪θ p.1,physicalPhase p.1 p.2 • f p.2⟫_ℂ‖ ≤ ‖θ p.1‖*‖f p.2‖
    refine (norm_inner_le_norm _ _).trans_eq ?_
    rw [norm_smul,physicalPhase_norm,one_mul]

lemma fourierInner_integral_right (e : E) (f : GW.Space → E) (hf : Integrable f volume) :
    ⟪e,∫ x, f x ∂(volume : Measure GW.Space)⟫_ℂ =
      ∫ x, ⟪e,f x⟫_ℂ ∂(volume : Measure GW.Space) :=
  ((innerSL ℂ e).integral_comp_comm hf).symm

lemma fourierInner_integral_left (f : GW.Space → E) (e : E) (hf : Integrable f volume) :
    ⟪∫ x, f x ∂(volume : Measure GW.Space),e⟫_ℂ =
      ∫ x, ⟪f x,e⟫_ℂ ∂(volume : Measure GW.Space) := by
  let L := Complex.conjLIE.toLinearIsometry.toContinuousLinearMap.comp ((innerSL ℂ e).restrictScalars ℝ)
  have he (x : E) : L x = ⟪x,e⟫_ℂ := inner_conj_symm _ _
  calc
    _ = L (∫ x, f x ∂(volume : Measure GW.Space)) := (he _).symm
    _ = ∫ x, L (f x) ∂(volume : Measure GW.Space) := (L.integral_comp_comm hf).symm
    _ = _ := integral_congr_ae (Eventually.of_forall (fun x => he (f x)))

lemma physicalFourierIntegral_pair_schwartz (θ : SchwartzMap GW.Space E) (f : GW.Space → E)
    (hf : Integrable f volume) :
    (∫ p, ⟪θ p,physicalFourierIntegral f p⟫_ℂ ∂(volume : Measure GW.Space)) =
      ∫ x, ⟪schwartzPhysicalFourierInv θ x,f x⟫_ℂ ∂(volume : Measure GW.Space) := by
  let d : ℝ := dilationAmplitude (2*Real.pi)
  let G := fourierIntegralPairingIntegrand (θ : GW.Space → E) f
  have hi := fourierIntegralPairingIntegrand_integrable (θ : GW.Space → E) f θ.integrable hf
  have hθ (x : GW.Space) : Integrable (fun p => physicalPhase (-x) p • θ p) (volume : Measure GW.Space) :=
    physicalPhase_smul_integrable _ θ.integrable (-x)
  calc
    _ = (d:ℂ) * ∫ p, ∫ x, G (p,x) ∂(volume : Measure GW.Space) ∂(volume : Measure GW.Space) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall (fun p => by
        change ⟪θ p,(d:ℂ) • ∫ x, physicalPhase p x • f x⟫_ℂ = _
        rw [inner_smul_right,fourierInner_integral_right _ _ (physicalPhase_smul_integrable f hf p)]
        rfl)
    _ = (d:ℂ) * ∫ x, ∫ p, G (p,x) ∂(volume : Measure GW.Space) ∂(volume : Measure GW.Space) :=
      congrArg ((d:ℂ)*·) (integral_integral_swap hi)
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => by
        change (d:ℂ) * (∫ p, G (p,x) ∂(volume : Measure GW.Space)) = ⟪schwartzPhysicalFourierInv θ x,f x⟫_ℂ
        rw [schwartzPhysicalFourierInv_apply]
        change _ = ⟪(d:ℂ) • ∫ p, physicalPhase (-x) p • θ p,f x⟫_ℂ
        rw [inner_smul_left,Complex.conj_ofReal,fourierInner_integral_left _ _ (hθ x)]
        congr 1
        apply integral_congr_ae
        exact Eventually.of_forall (fun p => by
          change ⟪θ p,physicalPhase p x • f x⟫_ℂ = ⟪physicalPhase (-x) p • θ p,f x⟫_ℂ
          rw [inner_smul_right,inner_smul_left,physicalPhase_inverse_conjugate]))

lemma physicalFourierIntegral_pair_toLp (θ : SchwartzMap GW.Space E) (f : GW.Space → E)
    (hf : Integrable f volume) (h₂ : MemLp f 2 (volume : Measure GW.Space)) :
    (∫ p, ⟪θ p,physicalFourierIntegral f p⟫_ℂ ∂(volume : Measure GW.Space)) =
      ⟪θ.toLp 2 (volume : Measure GW.Space),physicalFourierUnitary (h₂.toLp f)⟫_ℂ := by
  rw [physicalFourierIntegral_pair_schwartz θ f hf]
  have h : ⟪(schwartzPhysicalFourierInv θ).toLp 2 (volume : Measure GW.Space),h₂.toLp f⟫_ℂ =
      ⟪θ.toLp 2 (volume : Measure GW.Space),physicalFourierUnitary (h₂.toLp f)⟫_ℂ := by
    rw [← physicalFourierInv_schwartz]
    exact (physicalFourierUnitary.inner_map_map (physicalFourierUnitary.symm (θ.toLp 2)) (h₂.toLp f)).symm.trans
      (by rw [LinearIsometryEquiv.apply_symm_apply])
  rw [← h,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(schwartzPhysicalFourierInv θ).coeFn_toLp 2 (volume : Measure GW.Space),MemLp.coeFn_toLp h₂] with x h₁ h₃
  rw [h₁,h₃]

def fourierCompatTestVector (φ : SmoothScalarTest) (e : E) : SchwartzMap GW.Space E :=
  φ.toSchwartzMap.postcompCLM (ContinuousLinearMap.toSpanSingleton ℂ e)

lemma fourierCompatTestVector_apply (φ : SmoothScalarTest) (e : E) (x : GW.Space) :
    fourierCompatTestVector φ e x = φ.value x • e := rfl

lemma physicalFourierIntegral_compat (f : GW.Space → E) (hf : Integrable f volume)
    (h₂ : MemLp f 2 (volume : Measure GW.Space)) :
    physicalFourierIntegral f =ᵐ[(volume : Measure GW.Space)] physicalFourierUnitary (h₂.toLp f) := by
  let U := physicalFourierUnitary (h₂.toLp f)
  let g (p : GW.Space) := physicalFourierIntegral f p-U p
  have hloc : LocalSquareIntegrable g := by
    intro R
    have hU := (Lp.memLp U).mono_measure (ν := (volume : Measure GW.Space).restrict
      (Metric.closedBall (0:GW.Space) (R:ℝ))) Measure.restrict_le_self
    exact (physicalIntegral_localSquareIntegrable f hf R).sub hU
  have hzero : g =ᵐ[(volume : Measure GW.Space)] 0 := by
    apply localSquareIntegrable_hilbert_vanishes_of_tests g hloc
    intro φ e
    let θ := fourierCompatTestVector φ e
    have hpair := physicalFourierIntegral_pair_toLp θ f hf h₂
    have hi₁ : Integrable (fun p => ⟪θ p,physicalFourierIntegral f p⟫_ℂ) volume := by
      let C := dilationAmplitude (2*Real.pi) * ∫ x, ‖f x‖ ∂(volume : Measure GW.Space)
      have hm : Continuous (fun p => ⟪θ p,physicalFourierIntegral f p⟫_ℂ) :=
        θ.continuous.inner (physicalFourierIntegral_continuous f hf)
      apply (θ.integrable.norm.mul_const C).mono' hm.aestronglyMeasurable
      exact Eventually.of_forall (fun p => (norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left (physicalFourierIntegral_norm_bound f hf p) (norm_nonneg _)))
    have hi₂ : Integrable (fun p => ⟪θ p,U p⟫_ℂ) volume := by
      apply (L2.integrable_inner (θ.toLp 2 (volume : Measure GW.Space)) U).congr
      filter_upwards [θ.coeFn_toLp 2 (volume : Measure GW.Space)] with p hp
      exact congrArg (fun z : E => ⟪z,U p⟫_ℂ) hp
    have hR : (∫ p, ⟪θ p,U p⟫_ℂ ∂(volume : Measure GW.Space)) = ⟪θ.toLp 2 (volume : Measure GW.Space),U⟫_ℂ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [θ.coeFn_toLp 2 (volume : Measure GW.Space)] with p hp
      rw [hp]
    change (∫ p, ⟪φ.value p • e,physicalFourierIntegral f p-U p⟫_ℂ ∂(volume : Measure GW.Space)) = 0
    have he (p : GW.Space) : φ.value p • e = θ p := rfl
    simp_rw [he,inner_sub_right]
    rw [integral_sub hi₁ hi₂,hpair,hR,sub_self]
  exact hzero.mono (fun p hp => sub_eq_zero.mp hp)

lemma physicalFourierIntegral_memLp (f : GW.Space → E) (hf : Integrable f volume)
    (h₂ : MemLp f 2 (volume : Measure GW.Space)) :
    MemLp (physicalFourierIntegral f) 2 (volume : Measure GW.Space) :=
  (Lp.memLp (physicalFourierUnitary (h₂.toLp f))).ae_eq (physicalFourierIntegral_compat f hf h₂).symm

lemma physicalFourierIntegral_toLp (f : GW.Space → E) (hf : Integrable f volume)
    (h₂ : MemLp f 2 (volume : Measure GW.Space)) :
    (physicalFourierIntegral_memLp f hf h₂).toLp (physicalFourierIntegral f) =
      physicalFourierUnitary (h₂.toLp f) :=
  Lp.ext ((MemLp.coeFn_toLp _).trans (physicalFourierIntegral_compat f hf h₂))

lemma physicalFourierIntegral_norm_eq (f : GW.Space → E) (hf : Integrable f volume)
    (h₂ : MemLp f 2 (volume : Measure GW.Space)) :
    ‖(physicalFourierIntegral_memLp f hf h₂).toLp (physicalFourierIntegral f)‖ = ‖h₂.toLp f‖ := by
  rw [physicalFourierIntegral_toLp f hf h₂,LinearIsometryEquiv.norm_map]

end PhysicalIntegral
end GW.Analysis
