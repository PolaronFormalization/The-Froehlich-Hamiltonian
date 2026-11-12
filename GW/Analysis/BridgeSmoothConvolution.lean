module
public import GW.Conventions
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic
@[expose] public section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology Pointwise ENat ContDiff
namespace GW.Analysis

abbrev ConvMultilinear (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (m : ℕ) :=
  ContinuousMultilinearMap ℝ (fun _ : Fin m => GW.Space) E

def convolutionScalarDerivative (κ : GW.Space → ℝ) (m : ℕ) (x : GW.Space) : ConvMultilinear ℝ m :=
  iteratedFDeriv ℝ m κ x

lemma convolutionScalarDerivative_continuous {κ : GW.Space → ℝ} (hκ : ContDiff ℝ ∞ κ) (m : ℕ) :
    Continuous (convolutionScalarDerivative κ m) :=
  hκ.ftaylorSeries.cont m (by simp)

lemma convolutionScalarDerivative_hasFDerivAt {κ : GW.Space → ℝ} (hκ : ContDiff ℝ ∞ κ)
    (m : ℕ) (x : GW.Space) :
    HasFDerivAt (convolutionScalarDerivative κ m) (convolutionScalarDerivative κ (m+1) x).curryLeft x :=
  hκ.ftaylorSeries.fderiv m (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top m)) x

lemma convolutionScalarDerivative_bound {κ : GW.Space → ℝ} (hκ : ContDiff ℝ ∞ κ)
    (hs : HasCompactSupport κ) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖convolutionScalarDerivative κ m x‖ ≤ C := by
  obtain ⟨C,hC,h⟩ := hs.exists_bound_iteratedFDeriv hκ m
  exact ⟨C,hC,h m le_rfl⟩

lemma convolutionScalarSegment_hasDerivAt {κ : GW.Space → ℝ} (hκ : ContDiff ℝ ∞ κ) (m : ℕ)
    (z h : GW.Space) (t : ℝ) :
    HasDerivAt (fun s : ℝ => convolutionScalarDerivative κ m (z+s • h))
      ((convolutionScalarDerivative κ (m+1) (z+t • h)).curryLeft h) t := by
  have hv : HasDerivAt (fun s : ℝ => z+s • h) h t := by
    simpa only [id_eq,one_smul] using (((hasDerivAt_id t).smul_const h).const_add z)
  exact (convolutionScalarDerivative_hasFDerivAt hκ m (z+t • h)).comp_hasDerivAt t hv

lemma convolutionScalarSegment_integral {κ : GW.Space → ℝ} (hκ : ContDiff ℝ ∞ κ) (m : ℕ)
    (z h : GW.Space) (t : ℝ) :
    (∫ s in (0:ℝ)..t, (convolutionScalarDerivative κ (m+1) (z+s • h)).curryLeft h) =
      convolutionScalarDerivative κ m (z+t • h) - convolutionScalarDerivative κ m z := by
  have hc : Continuous (fun s : ℝ => (convolutionScalarDerivative κ (m+1) (z+s • h)).curryLeft h) :=
    ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m+1) => GW.Space) ℝ).continuous.comp
      ((convolutionScalarDerivative_continuous hκ (m+1)).comp
        (continuous_const.add (continuous_id.smul continuous_const)))).clm_apply continuous_const
  have ht := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => convolutionScalarSegment_hasDerivAt hκ m z h s) (hc.intervalIntegrable 0 t)
  simpa only [zero_smul,add_zero] using ht

lemma convolutionScalarSegment_diff_bound {κ : GW.Space → ℝ} (hκ : ContDiff ℝ ∞ κ) (m : ℕ)
    (z h : GW.Space) (t C : ℝ) (ht : 0 ≤ t)
    (hC : ∀ x, ‖convolutionScalarDerivative κ (m+1) x‖ ≤ C) :
    ‖convolutionScalarDerivative κ m (z+t • h) - convolutionScalarDerivative κ m z‖ ≤ C * ‖h‖ * t := by
  rw [← convolutionScalarSegment_integral hκ m z h t]
  have he := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := t) (C := C*‖h‖)
    (f := fun s => (convolutionScalarDerivative κ (m+1) (z+s • h)).curryLeft h)
    (fun s _ => by
      refine (((convolutionScalarDerivative κ (m+1) (z+s • h)).curryLeft).le_opNorm h).trans ?_
      rw [ContinuousMultilinearMap.curryLeft_norm]
      exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _))
  simpa only [sub_zero,abs_of_nonneg ht] using he

lemma convolutionScalar_remainder {κ : GW.Space → ℝ} (hκ : ContDiff ℝ ∞ κ) (m : ℕ)
    (z h : GW.Space) (C : ℝ) (hC : ∀ x, ‖convolutionScalarDerivative κ (m+2) x‖ ≤ C) :
    ‖convolutionScalarDerivative κ m (z+h) - convolutionScalarDerivative κ m z -
      (convolutionScalarDerivative κ (m+1) z).curryLeft h‖ ≤ (1/2:ℝ)*C*‖h‖^2 := by
  let L := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m+1) => GW.Space) ℝ
  let f (s : ℝ) := L (convolutionScalarDerivative κ (m+1) (z+s • h)) h
  let a := L (convolutionScalarDerivative κ (m+1) z) h
  have hf : Continuous f := (L.continuous.comp
    ((convolutionScalarDerivative_continuous hκ (m+1)).comp
      (continuous_const.add (continuous_id.smul continuous_const)))).clm_apply continuous_const
  have he : (∫ s in (0:ℝ)..1, f s) = convolutionScalarDerivative κ m (z+h) - convolutionScalarDerivative κ m z := by
    change (∫ s in (0:ℝ)..1, (convolutionScalarDerivative κ (m+1) (z+s • h)).curryLeft h) = _
    simpa only [one_smul] using convolutionScalarSegment_integral hκ m z h 1
  have ha : (∫ _ : ℝ in (0:ℝ)..1, a) = a := by simp
  change ‖convolutionScalarDerivative κ m (z+h) - convolutionScalarDerivative κ m z - a‖ ≤ _
  rw [← he,← ha,← intervalIntegral.integral_sub (hf.intervalIntegrable 0 1) (intervalIntegrable_const)]
  have hB (s : ℝ) (hs : s ∈ Ioc (0:ℝ) 1) : ‖f s-a‖ ≤ C*‖h‖^2*s := by
    have hs' : 0 ≤ s := hs.1.le
    change ‖L (convolutionScalarDerivative κ (m+1) (z+s • h)) h - L (convolutionScalarDerivative κ (m+1) z) h‖ ≤ _
    have hL : L (convolutionScalarDerivative κ (m+1) (z+s • h) - convolutionScalarDerivative κ (m+1) z) =
        L (convolutionScalarDerivative κ (m+1) (z+s • h)) - L (convolutionScalarDerivative κ (m+1) z) :=
      L.toLinearEquiv.map_sub _ _
    rw [← sub_apply,← hL]
    refine ((L (convolutionScalarDerivative κ (m+1) (z+s • h) - convolutionScalarDerivative κ (m+1) z)).le_opNorm h).trans ?_
    rw [L.norm_map]
    refine (mul_le_mul_of_nonneg_right (convolutionScalarSegment_diff_bound hκ (m+1) z h s C hs' hC) (norm_nonneg _)).trans_eq ?_
    ring
  refine (intervalIntegral.norm_integral_le_of_norm_le (by norm_num : (0:ℝ) ≤ 1)
    (Eventually.of_forall hB) ((continuous_const.mul continuous_id).intervalIntegrable 0 1)).trans_eq ?_
  rw [intervalIntegral.integral_const_mul,integral_id]
  ring

section Convolution
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def smoothConvolution (κ : GW.Space → ℝ) (v : GW.Space → E) (x : GW.Space) : E :=
  ∫ y, κ (x-y) • v y ∂(volume : Measure GW.Space)

def convolutionDerivativeIntegrand (κ : GW.Space → ℝ) (v : GW.Space → E)
    (m : ℕ) (x y : GW.Space) : ConvMultilinear E m :=
  (convolutionScalarDerivative κ m (x-y)).smulRight (v y)

def convolutionDerivative (κ : GW.Space → ℝ) (v : GW.Space → E) (m : ℕ) (x : GW.Space) :
    ConvMultilinear E m :=
  ∫ y, convolutionDerivativeIntegrand κ v m x y ∂(volume : Measure GW.Space)

lemma convolutionDerivativeIntegrand_measurable {κ : GW.Space → ℝ} (hκ : ContDiff ℝ ∞ κ)
    {v : GW.Space → E} (hv : AEStronglyMeasurable v volume) (m : ℕ) (x : GW.Space) :
    AEStronglyMeasurable (convolutionDerivativeIntegrand κ v m x) volume := by
  let B := ContinuousMultilinearMap.smulRightL ℝ (fun _ : Fin m => GW.Space) E
  have hK : Continuous (fun y : GW.Space => convolutionScalarDerivative κ m (x-y)) :=
    (convolutionScalarDerivative_continuous hκ m).comp (continuous_const.sub continuous_id)
  exact B.aestronglyMeasurable_comp₂ hK.aestronglyMeasurable hv

lemma convolutionDerivativeIntegrand_integrable {κ : GW.Space → ℝ} (hκ : ContDiff ℝ ∞ κ)
    (hs : HasCompactSupport κ) {v : GW.Space → E} (hv : Integrable v volume) (m : ℕ) (x : GW.Space) :
    Integrable (convolutionDerivativeIntegrand κ v m x) volume := by
  obtain ⟨C,hC,h⟩ := convolutionScalarDerivative_bound hκ hs m
  apply Integrable.mono' (hv.norm.const_mul C) (convolutionDerivativeIntegrand_measurable hκ hv.1 m x)
  exact Eventually.of_forall (fun y => by
    rw [convolutionDerivativeIntegrand,ContinuousMultilinearMap.norm_smulRight]
    exact mul_le_mul_of_nonneg_right (h (x-y)) (norm_nonneg _))

lemma convolutionDerivative_apply {κ : GW.Space → ℝ} (hκ : ContDiff ℝ ∞ κ)
    (hs : HasCompactSupport κ) {v : GW.Space → E} (hv : Integrable v volume) (m : ℕ)
    (x : GW.Space) (h : Fin m → GW.Space) :
    convolutionDerivative κ v m x h =
      ∫ y, convolutionScalarDerivative κ m (x-y) h • v y ∂(volume : Measure GW.Space) := by
  exact ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin m => GW.Space) E h).integral_comp_comm
    (convolutionDerivativeIntegrand_integrable hκ hs hv m x)).symm

lemma convolutionDerivative_continuous {κ : GW.Space → ℝ} (hκ : ContDiff ℝ ∞ κ)
    (hs : HasCompactSupport κ) {v : GW.Space → E} (hv : Integrable v volume) (m : ℕ) :
    Continuous (convolutionDerivative κ v m) := by
  apply continuous_iff_seqContinuous.mpr
  intro f x hf
  obtain ⟨C,hC,h⟩ := convolutionScalarDerivative_bound hκ hs m
  exact tendsto_integral_of_dominated_convergence (fun y => C*‖v y‖)
    (fun n => convolutionDerivativeIntegrand_measurable hκ hv.1 m (f n)) (hv.norm.const_mul C)
    (fun n => Eventually.of_forall (fun y => by
      rw [convolutionDerivativeIntegrand,ContinuousMultilinearMap.norm_smulRight]
      exact mul_le_mul_of_nonneg_right (h (f n-y)) (norm_nonneg _)))
    (Eventually.of_forall (fun y => by
      let B := ContinuousMultilinearMap.smulRightL ℝ (fun _ : Fin m => GW.Space) E
      have hc := (convolutionScalarDerivative_continuous hκ m).continuousAt.tendsto.comp (hf.sub_const y)
      let A := ContinuousLinearMap.apply ℝ (ConvMultilinear E m) (v y)
      exact ((A.continuous.comp B.continuous).continuousAt.tendsto.comp hc)))

def convolutionCurryInsert (m : ℕ) (h : GW.Space) :
    ConvMultilinear E (m+1) →L[ℝ] ConvMultilinear E m :=
  (ContinuousLinearMap.apply ℝ (ConvMultilinear E m) h).comp
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m+1) => GW.Space) E).toLinearIsometry.toContinuousLinearMap

lemma convolutionCurryInsert_apply (m : ℕ) (h : GW.Space) (f : ConvMultilinear E (m+1)) :
    convolutionCurryInsert m h f = f.curryLeft h := rfl

lemma convolutionCurryInsert_smulRight (m : ℕ) (h : GW.Space)
    (f : ConvMultilinear ℝ (m+1)) (e : E) :
    convolutionCurryInsert m h (f.smulRight e) = (f.curryLeft h).smulRight e := by
  ext w
  simp only [convolutionCurryInsert_apply, ContinuousMultilinearMap.curryLeft_apply,
    ContinuousMultilinearMap.smulRight_apply]

lemma convolutionDerivative_curry_integral {κ : GW.Space → ℝ} (hκ : ContDiff ℝ ∞ κ)
    (hs : HasCompactSupport κ) {v : GW.Space → E} (hv : Integrable v volume) (m : ℕ) (x h : GW.Space) :
    (convolutionDerivative κ v (m+1) x).curryLeft h =
      ∫ y, convolutionCurryInsert m h (convolutionDerivativeIntegrand κ v (m+1) x y) ∂(volume : Measure GW.Space) := by
  exact ((convolutionCurryInsert m h).integral_comp_comm
    (convolutionDerivativeIntegrand_integrable hκ hs hv (m+1) x)).symm

lemma convolutionDerivative_remainder {κ : GW.Space → ℝ} (hκ : ContDiff ℝ ∞ κ)
    (hs : HasCompactSupport κ) {v : GW.Space → E} (hv : Integrable v volume) (m : ℕ) (x h : GW.Space)
    (C : ℝ) (hC : ∀ z, ‖convolutionScalarDerivative κ (m+2) z‖ ≤ C) :
    ‖convolutionDerivative κ v m (x+h) - convolutionDerivative κ v m x -
      (convolutionDerivative κ v (m+1) x).curryLeft h‖ ≤
        (1/2:ℝ)*C*(∫ y, ‖v y‖ ∂(volume : Measure GW.Space))*‖h‖^2 := by
  let A := convolutionDerivativeIntegrand κ v m (x+h)
  let B := convolutionDerivativeIntegrand κ v m x
  let D := fun y => convolutionCurryInsert m h (convolutionDerivativeIntegrand κ v (m+1) x y)
  let c := (1/2:ℝ)*C*‖h‖^2
  have hA : Integrable A volume := convolutionDerivativeIntegrand_integrable hκ hs hv m (x+h)
  have hB : Integrable B volume := convolutionDerivativeIntegrand_integrable hκ hs hv m x
  have hD : Integrable D volume := (convolutionCurryInsert m h).integrable_comp
    (convolutionDerivativeIntegrand_integrable hκ hs hv (m+1) x)
  rw [convolutionDerivative_curry_integral hκ hs hv m x h]
  change ‖(∫ y, A y ∂(volume : Measure GW.Space)) - (∫ y, B y ∂(volume : Measure GW.Space)) -
    (∫ y, D y ∂(volume : Measure GW.Space))‖ ≤ _
  rw [← integral_sub hA hB]
  have hInt := integral_sub (hA.sub hB) hD
  change (∫ y, A y-B y-D y ∂(volume : Measure GW.Space)) =
    (∫ y, A y-B y ∂(volume : Measure GW.Space)) - (∫ y, D y ∂(volume : Measure GW.Space)) at hInt
  rw [← hInt]
  have hbound (y : GW.Space) : ‖A y-B y-D y‖ ≤ c*‖v y‖ := by
    let L := (ContinuousLinearMap.apply ℝ (ConvMultilinear E m) (v y)).comp
      (ContinuousMultilinearMap.smulRightL ℝ (fun _ : Fin m => GW.Space) E)
    have he : A y-B y-D y =
        L (convolutionScalarDerivative κ m ((x-y)+h) - convolutionScalarDerivative κ m (x-y) -
          (convolutionScalarDerivative κ (m+1) (x-y)).curryLeft h) := by
      rw [L.map_sub,L.map_sub]
      have hz : (x-y)+h = (x+h)-y := by abel
      rw [hz]
      change A y-B y-D y = A y-B y-((convolutionScalarDerivative κ (m+1) (x-y)).curryLeft h).smulRight (v y)
      unfold D convolutionDerivativeIntegrand
      rw [convolutionCurryInsert_smulRight]
    rw [he]
    change ‖(convolutionScalarDerivative κ m ((x-y)+h) - convolutionScalarDerivative κ m (x-y) -
          (convolutionScalarDerivative κ (m+1) (x-y)).curryLeft h).smulRight (v y)‖ ≤ _
    rw [ContinuousMultilinearMap.norm_smulRight]
    exact mul_le_mul_of_nonneg_right (convolutionScalar_remainder hκ m (x-y) h C hC) (norm_nonneg _)
  refine (norm_integral_le_of_norm_le (hv.norm.const_mul c) (Eventually.of_forall hbound)).trans_eq ?_
  rw [integral_const_mul]
  unfold c
  ring

lemma convolutionDerivative_hasFDerivAt {κ : GW.Space → ℝ} (hκ : ContDiff ℝ ∞ κ)
    (hs : HasCompactSupport κ) {v : GW.Space → E} (hv : Integrable v volume) (m : ℕ) (x : GW.Space) :
    HasFDerivAt (convolutionDerivative κ v m) (convolutionDerivative κ v (m+1) x).curryLeft x := by
  obtain ⟨C,hC,hb⟩ := convolutionScalarDerivative_bound hκ hs (m+2)
  apply hasFDerivAt_iff_isLittleO_nhds_zero.mpr
  refine Asymptotics.IsBigO.trans_isLittleO
    (g := fun h : GW.Space => ‖h‖^2) (Asymptotics.isBigO_iff.mpr ?_)
    (Asymptotics.isLittleO_norm_pow_id (by norm_num : 1 < 2))
  refine ⟨(1/2:ℝ)*C*(∫ y, ‖v y‖ ∂(volume : Measure GW.Space)),Eventually.of_forall ?_⟩
  intro h
  rw [Real.norm_of_nonneg (sq_nonneg (‖h‖))]
  exact convolutionDerivative_remainder hκ hs hv m x h C hb

def smoothConvolutionSeries (κ : GW.Space → ℝ) (v : GW.Space → E) (x : GW.Space) :
    FormalMultilinearSeries ℝ GW.Space E := fun m => convolutionDerivative κ v m x

lemma smoothConvolution_hasTaylorSeries {κ : GW.Space → ℝ} (hκ : ContDiff ℝ ∞ κ)
    (hs : HasCompactSupport κ) {v : GW.Space → E} (hv : Integrable v volume) :
    HasFTaylorSeriesUpTo ∞ (smoothConvolution κ v) (smoothConvolutionSeries κ v) := by
  constructor
  · intro x
    change (convolutionDerivative κ v 0 x).curry0 = _
    let h : Fin 0 → GW.Space := fun _ => 0
    change convolutionDerivative κ v 0 x h = _
    rw [convolutionDerivative_apply hκ hs hv]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro y
    exact congrArg (· • v y) (hκ.ftaylorSeries.zero_eq (x-y))
  · intro m _ x
    exact convolutionDerivative_hasFDerivAt hκ hs hv m x
  · intro m _
    exact convolutionDerivative_continuous hκ hs hv m

lemma smoothConvolution_contDiff {κ : GW.Space → ℝ} (hκ : ContDiff ℝ ∞ κ)
    (hs : HasCompactSupport κ) {v : GW.Space → E} (hv : Integrable v volume) :
    ContDiff ℝ ∞ (smoothConvolution κ v) :=
  (smoothConvolution_hasTaylorSeries hκ hs hv).contDiff

lemma smoothConvolution_iteratedFDeriv {κ : GW.Space → ℝ} (hκ : ContDiff ℝ ∞ κ)
    (hs : HasCompactSupport κ) {v : GW.Space → E} (hv : Integrable v volume) (m : ℕ)
    (x : GW.Space) (h : Fin m → GW.Space) :
    iteratedFDeriv ℝ m (smoothConvolution κ v) x h =
      ∫ y, iteratedFDeriv ℝ m κ (x-y) h • v y ∂(volume : Measure GW.Space) := by
  have he := (smoothConvolution_hasTaylorSeries hκ hs hv).eq_iteratedFDeriv (m := m) (by simp) x
  change convolutionDerivative κ v m x = _ at he
  rw [← he]
  exact convolutionDerivative_apply hκ hs hv m x h

lemma smoothConvolution_support {κ : GW.Space → ℝ} (hs : HasCompactSupport κ)
    (v : GW.Space → E) (L : Set GW.Space) (hL : IsCompact L)
    (hzero : ∀ᵐ y ∂(volume : Measure GW.Space), y ∉ L → v y = 0) :
    tsupport (smoothConvolution κ v) ⊆ tsupport κ + L := by
  apply closure_minimal _ (IsCompact.add (show IsCompact (tsupport κ) from hs) hL).isClosed
  intro x hx
  by_contra hnot
  have he : smoothConvolution κ v x = 0 := by
    unfold smoothConvolution
    apply integral_eq_zero_of_ae
    filter_upwards [hzero] with y hy
    change κ (x-y) • v y = (0:E)
    by_cases hmem : y ∈ L
    · have hκ : x-y ∉ tsupport κ := by
        intro hk
        exact hnot (Set.mem_add.mpr ⟨x-y,hk,y,hmem,sub_add_cancel _ _⟩)
      rw [image_eq_zero_of_notMem_tsupport hκ,zero_smul]
    · rw [hy hmem,smul_zero]
  exact hx he

end Convolution
end GW.Analysis
