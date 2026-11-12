module
public import GW.Fock.FockConvolutionUse
public import GW.Gross.MainTails
public import GW.Model.ModelCutoffWitness
public import GW.Model.ModelFrohlichEstimates

/-! Source main:singular-annihilation-limit, manuscript6423–6504.
Actual Fröhlich-dominated singular annihilation as a bounded free graph-space map,
sharp norm and real-cutoff error, and original annihilator identification in L2. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal BigOperators
namespace GW.Gross
open GW.Model GW.Fock GW.Analysis

/- Source argument component Data02. -/
open GW.Fock GW.Model

lemma singular_domination_v (α K : ℝ) (m : GW.Space → ℂ)
    (hd : ∀ᵐ k ∂(volume : Measure GW.Space), ‖m k‖ ≤ (highRegion K).indicator (fun k => |v α k|) k) :
    ∀ᵐ k ∂(volume : Measure GW.Space), ‖m k‖ ≤ |v α k| := by
  filter_upwards [hd] with k hk
  apply hk.trans
  by_cases he : k ∈ highRegion K
  · rw [Set.indicator_of_mem he]
  · rw [Set.indicator_of_notMem he]
    exact abs_nonneg _

lemma singular_cutoff_memLp (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (m : GW.Space → ℂ) (hm : Measurable m)
    (hd : ∀ᵐ k ∂(volume : Measure GW.Space), ‖m k‖ ≤ (highRegion K).indicator (fun k => |v α k|) k)
    (R : ℝ) (hR : K ≤ R) :
    MemLp ((lowRegion R).indicator m) 2 (volume : Measure GW.Space) := by
  apply (cutoff_memLp α R hα (hK.trans_le hR)).of_le
    (hm.aestronglyMeasurable.indicator (lowRegion_measurable R))
  filter_upwards [singular_domination_v α K m hd] with k hk
  by_cases he : k ∈ lowRegion R
  · have he' : ‖k‖ ≤ R := he
    simpa only [Set.indicator_of_mem he,GW.Model.cutoff,ite_eq_left he',Complex.norm_real,Real.norm_eq_abs] using hk
  · rw [Set.indicator_of_notMem he,norm_zero]
    exact norm_nonneg _

lemma singular_tail_bound (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (m : GW.Space → ℂ)
    (hd : ∀ᵐ k ∂(volume : Measure GW.Space), ‖m k‖ ≤ (highRegion K).indicator (fun k => |v α k|) k)
    (R : ℝ) (hR : K ≤ R) (q : GW.Space) :
    (∫⁻ k : GW.Space in highRegion R, ENNReal.ofReal (‖m k‖^2/(1+‖q-k‖^2))) ≤
      ENNReal.ofReal ((Real.sqrt (coefficientTTail α R))^2) := by
  have hRp : 0 < R := hK.trans_le hR
  calc
    _ ≤ coefficientConvolutionENN α R q := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_of_ae hd,ae_restrict_mem (highRegion_measurable R)] with k hk hkR
      have hkK : k ∈ highRegion K := lt_of_le_of_lt hR hkR
      rw [Set.indicator_of_mem hkK] at hk
      have hs : ‖m k‖^2 ≤ (v α k)^2 := by
        nlinarith [mul_self_le_mul_self (norm_nonneg (m k)) hk,sq_abs (v α k)]
      exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hs (by positivity))
    _ = ENNReal.ofReal (coefficientConvolution α R q) :=
      (ENNReal.ofReal_toReal (coefficientConvolutionENN_finite α R hα hRp q)).symm
    _ ≤ ENNReal.ofReal (coefficientTTail α R) :=
      ENNReal.ofReal_le_ofReal (coefficientConvolution_le_T α R hα hRp q)
    _ = ENNReal.ofReal ((Real.sqrt (coefficientTTail α R))^2) := by
      rw [Real.sq_sqrt (coefficientTTail_nonneg α R hα hRp)]

def singularConvolutionData (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (m : GW.Space → ℂ) (hm : Measurable m)
    (hd : ∀ᵐ k ∂(volume : Measure GW.Space), ‖m k‖ ≤ (highRegion K).indicator (fun k => |v α k|) k) :
    ConvolutionTailData where
  coefficient := m
  measurable := hm
  lowerCutoff := K
  lowerCutoff_nonneg := hK.le
  cutoff_memLp := singular_cutoff_memLp α K hα hK m hm hd
  error := fun R => Real.sqrt (coefficientTTail α R)
  error_nonneg := fun R _ => Real.sqrt_nonneg _
  error_tendsto := by
    simpa only [Real.sqrt_zero,Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp (coefficientTTail_tendsto α hα)
  tail_bound := singular_tail_bound α K hα hK m hd

/- Source argument component Boundary02. -/
open GW.Fock GW.Model

lemma singularAnnihilationMap_zero : convolutionAnnihilationMap (0 : OneBoson) = 0 := by
  have h := convolutionAnnihilationMap_sub (0 : OneBoson) 0
  simpa only [sub_self] using h

lemma singular_cutoff_boundary_zero (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (m : GW.Space → ℂ) (hm : Measurable m)
    (hd : ∀ᵐ k ∂(volume : Measure GW.Space), ‖m k‖ ≤ (highRegion K).indicator (fun k => |v α k|) k) :
    convolutionCutoff (singularConvolutionData α K hα hK m hm hd) K = 0 := by
  let d := singularConvolutionData α K hα hK m hm hd
  have hcut : (convolutionCutoff d K : GW.Space → ℂ) =ᵐ[volume] (lowRegion K).indicator m :=
    convolutionCutoff_ae d K le_rfl
  apply Lp.ext
  filter_upwards [hcut,hd,Lp.coeFn_zero ℂ 2 (volume : Measure GW.Space)] with k hc hk hz
  rw [hc,hz]
  by_cases he : k ∈ lowRegion K
  · have hh : k ∉ highRegion K :=
      (show ¬ K < ‖k‖ from not_lt.mpr (show ‖k‖ ≤ K from he))
    rw [Set.indicator_of_notMem hh] at hk
    rw [Set.indicator_of_mem he]
    exact norm_eq_zero.mp (le_antisymm hk (norm_nonneg _))
  · rw [Set.indicator_of_notMem he]
    rfl

def singularAnnihilationMap (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (m : GW.Space → ℂ) (hm : Measurable m)
    (hd : ∀ᵐ k ∂(volume : Measure GW.Space), ‖m k‖ ≤ (highRegion K).indicator (fun k => |v α k|) k) :
    FreeGraphDomain →L[ℂ] Physical :=
  convolutionLimit (singularConvolutionData α K hα hK m hm hd)

def singularFiniteMap (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (m : GW.Space → ℂ) (hm : Measurable m)
    (hd : ∀ᵐ k ∂(volume : Measure GW.Space), ‖m k‖ ≤ (highRegion K).indicator (fun k => |v α k|) k)
    (R : ℝ) : FreeGraphDomain →L[ℂ] Physical :=
  convolutionCutoffMap (singularConvolutionData α K hα hK m hm hd) R

lemma singularFiniteMap_boundary (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (m : GW.Space → ℂ) (hm : Measurable m)
    (hd : ∀ᵐ k ∂(volume : Measure GW.Space), ‖m k‖ ≤ (highRegion K).indicator (fun k => |v α k|) k) :
    singularFiniteMap α K hα hK m hm hd K = 0 := by
  have he := congrArg convolutionAnnihilationMap (singular_cutoff_boundary_zero α K hα hK m hm hd)
  exact he.trans singularAnnihilationMap_zero

lemma singularAnnihilation_norm (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (m : GW.Space → ℂ) (hm : Measurable m)
    (hd : ∀ᵐ k ∂(volume : Measure GW.Space), ‖m k‖ ≤ (highRegion K).indicator (fun k => |v α k|) k) :
    ‖singularAnnihilationMap α K hα hK m hm hd‖ ≤ (1/2 : ℝ)*Real.sqrt (coefficientTTail α K) := by
  have h := convolutionLimit_sharp_error (singularConvolutionData α K hα hK m hm hd) K le_rfl
  change ‖singularAnnihilationMap α K hα hK m hm hd-singularFiniteMap α K hα hK m hm hd K‖ ≤
    (1/2 : ℝ)*Real.sqrt (coefficientTTail α K) at h
  rw [singularFiniteMap_boundary,sub_zero] at h
  exact h

/- Source argument component Limit02. -/
open GW.Fock GW.Model

lemma singularAnnihilation_error (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (m : GW.Space → ℂ) (hm : Measurable m)
    (hd : ∀ᵐ k ∂(volume : Measure GW.Space), ‖m k‖ ≤ (highRegion K).indicator (fun k => |v α k|) k)
    (R : ℝ) (hR : K < R) :
    ‖singularAnnihilationMap α K hα hK m hm hd-singularFiniteMap α K hα hK m hm hd R‖ ≤
      (1/2 : ℝ)*Real.sqrt (coefficientTTail α R) :=
  convolutionLimit_sharp_error (singularConvolutionData α K hα hK m hm hd) R hR.le

lemma singularAnnihilation_tendsto (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (m : GW.Space → ℂ) (hm : Measurable m)
    (hd : ∀ᵐ k ∂(volume : Measure GW.Space), ‖m k‖ ≤ (highRegion K).indicator (fun k => |v α k|) k) :
    Tendsto (singularFiniteMap α K hα hK m hm hd) atTop
      (𝓝 (singularAnnihilationMap α K hα hK m hm hd)) :=
  convolutionLimit_tendsto (singularConvolutionData α K hα hK m hm hd)

lemma singularAnnihilation_unique (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (m : GW.Space → ℂ) (hm : Measurable m)
    (hd : ∀ᵐ k ∂(volume : Measure GW.Space), ‖m k‖ ≤ (highRegion K).indicator (fun k => |v α k|) k)
    (T : FreeGraphDomain →L[ℂ] Physical)
    (hT : Tendsto (singularFiniteMap α K hα hK m hm hd) atTop (𝓝 T)) :
    T = singularAnnihilationMap α K hα hK m hm hd :=
  tendsto_nhds_unique hT (singularAnnihilation_tendsto α K hα hK m hm hd)

lemma singularFiniteMap_coefficient (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (m : GW.Space → ℂ) (hm : Measurable m)
    (hd : ∀ᵐ k ∂(volume : Measure GW.Space), ‖m k‖ ≤ (highRegion K).indicator (fun k => |v α k|) k)
    (R : ℝ) (hR : K < R) :
    (convolutionCutoff (singularConvolutionData α K hα hK m hm hd) R : GW.Space → ℂ) =ᵐ[volume]
      (lowRegion R).indicator m :=
  convolutionCutoffMap_coefficient (singularConvolutionData α K hα hK m hm hd) R hR.le

lemma singularFiniteMap_original_graph (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (m : GW.Space → ℂ) (hm : Measurable m)
    (hd : ∀ᵐ k ∂(volume : Measure GW.Space), ‖m k‖ ≤ (highRegion K).indicator (fun k => |v α k|) k)
    (R : ℝ) (u : FreeGraphDomain) :
    (freeGraphDomainInclusion u,singularFiniteMap α K hα hK m hm hd R u) ∈
      (generalizedAnnihilation (phaseMultiplicationKernel
        (convolutionCutoff (singularConvolutionData α K hα hK m hm hd) R))).graph :=
  convolutionCutoffMap_original_graph (singularConvolutionData α K hα hK m hm hd) R u

lemma singularAnnihilation_tolerance (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (m : GW.Space → ℂ) (hm : Measurable m)
    (hd : ∀ᵐ k ∂(volume : Measure GW.Space), ‖m k‖ ≤ (highRegion K).indicator (fun k => |v α k|) k)
    (η : ℝ) (hη : 0 < η) (Λ : ℝ)
    (hΛ : max (K+1) (convolutionCutoffWitness α (2*η)) ≤ Λ) :
    ‖singularFiniteMap α K hα hK m hm hd Λ-singularAnnihilationMap α K hα hK m hm hd‖ ≤ η := by
  let R := max (K+1) (convolutionCutoffWitness α (2*η))
  have hKR : K < R := lt_of_lt_of_le (lt_add_one K) (le_max_left _ _)
  have hs := convolutionCutoffWitness_bound α (2*η) R hα (by positivity) (le_max_right _ _)
  have hb := convolutionLimit_sharp_bound (singularConvolutionData α K hα hK m hm hd) R hKR.le Λ hΛ
  exact hb.trans (by
    change (1/2 : ℝ)*Real.sqrt (coefficientTTail α R) ≤ η
    nlinarith)

/- Source argument component Continuity03. -/
open GW.Fock

lemma singularAnnihilation_coefficient_bound (f g : OneBoson) :
    ‖convolutionAnnihilationMap f-convolutionAnnihilationMap g‖ ≤ (1/2 : ℝ)*‖f-g‖ := by
  have he := convolutionAnnihilationMap_sub f g
  exact (congrArg norm he).symm.trans_le
    ((convolutionAnnihilationMap_opNorm (f-g)).trans
      (mul_le_mul_of_nonneg_left (frankSchleinConstant_le (f-g)) (by norm_num)))

lemma singularAnnihilation_coefficient_continuous : Continuous convolutionAnnihilationMap := by
  have hLip : LipschitzWith (1/2 : NNReal) convolutionAnnihilationMap :=
    lipschitzWith_iff_norm_sub_le.mpr (fun f g => singularAnnihilation_coefficient_bound f g)
  exact hLip.continuous

/- Source argument component L203. -/
open GW.Fock GW.Model

lemma singular_cutoff_L2_tendsto (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (m : GW.Space → ℂ) (hm : Measurable m)
    (hd : ∀ᵐ k ∂(volume : Measure GW.Space), ‖m k‖ ≤ (highRegion K).indicator (fun k => |v α k|) k)
    (hL2 : MemLp m 2 (volume : Measure GW.Space)) :
    Tendsto (fun R : ℝ => convolutionCutoff (singularConvolutionData α K hα hK m hm hd) R)
      atTop (𝓝 (hL2.toLp m)) := by
  let f : OneBoson := hL2.toLp m
  let d := singularConvolutionData α K hα hK m hm hd
  let W (R : ℝ) := GW.Spaces.WeightedL2.cutoff (w := fun _ : GW.Space => (1 : ℝ))
    (lowRegion R) (lowRegion_measurable R) f
  have hex : ∀ᵐ k ∂(volume : Measure GW.Space), ∀ᶠ R : ℝ in atTop, k ∈ lowRegion R :=
    Eventually.of_forall (fun k => eventually_ge_atTop ‖k‖)
  have hW : Tendsto W atTop (𝓝 f) :=
    GW.Spaces.WeightedL2.cutoff_tendsto_real (w := fun _ : GW.Space => (1 : ℝ))
      lowRegion lowRegion_measurable hex f
  have heq : (fun R : ℝ => convolutionCutoff d R) =ᶠ[atTop] W := by
    filter_upwards [eventually_ge_atTop K] with R hR
    have h₁ : (convolutionCutoff d R : GW.Space → ℂ) =ᵐ[volume] (lowRegion R).indicator m :=
      convolutionCutoff_ae d R hR
    have h₂ : (lowRegion R).indicator (f : GW.Space → ℂ) =ᵐ[volume] (W R : GW.Space → ℂ) :=
      GW.Spaces.WeightedL2.cutoff_ae (w := fun _ : GW.Space => (1 : ℝ))
        (lowRegion R) (lowRegion_measurable R) f
    apply Lp.ext
    filter_upwards [h₁,h₂,MemLp.coeFn_toLp hL2] with k hk₁ hk₂ hk₃
    by_cases hk : k ∈ lowRegion R
    · rw [Set.indicator_of_mem hk] at hk₁ hk₂
      exact hk₁.trans (hk₃.symm.trans hk₂)
    · rw [Set.indicator_of_notMem hk] at hk₁ hk₂
      exact hk₁.trans hk₂
  exact hW.congr' heq.symm

lemma singularAnnihilation_L2 (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (m : GW.Space → ℂ) (hm : Measurable m)
    (hd : ∀ᵐ k ∂(volume : Measure GW.Space), ‖m k‖ ≤ (highRegion K).indicator (fun k => |v α k|) k)
    (hL2 : MemLp m 2 (volume : Measure GW.Space)) :
    singularAnnihilationMap α K hα hK m hm hd = convolutionAnnihilationMap (hL2.toLp m) := by
  let f : OneBoson := hL2.toLp m
  let d := singularConvolutionData α K hα hK m hm hd
  have hc : Tendsto (fun R : ℝ => convolutionCutoff d R) atTop (𝓝 f) :=
    singular_cutoff_L2_tendsto α K hα hK m hm hd hL2
  have hlim : Tendsto (singularFiniteMap α K hα hK m hm hd) atTop (𝓝 (convolutionAnnihilationMap f)) :=
    (singularAnnihilation_coefficient_continuous.tendsto f).comp hc
  exact tendsto_nhds_unique (singularAnnihilation_tendsto α K hα hK m hm hd) hlim

lemma singularAnnihilation_L2_graph (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (m : GW.Space → ℂ) (hm : Measurable m)
    (hd : ∀ᵐ k ∂(volume : Measure GW.Space), ‖m k‖ ≤ (highRegion K).indicator (fun k => |v α k|) k)
    (hL2 : MemLp m 2 (volume : Measure GW.Space)) (u : FreeGraphDomain) :
    (freeGraphDomainInclusion u,singularAnnihilationMap α K hα hK m hm hd u) ∈
      (generalizedAnnihilation (phaseMultiplicationKernel (hL2.toLp m))).graph := by
  rw [singularAnnihilation_L2 α K hα hK m hm hd hL2]
  exact convolutionAnnihilation_graph (hL2.toLp m) u

/- Source argument component Public01. -/
open GW.Fock GW.Model

lemma main_singular_annihilation_limit (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (m : GW.Space → ℂ) (hm : Measurable m)
    (hd : ∀ᵐ k ∂(volume : Measure GW.Space), ‖m k‖ ≤ (highRegion K).indicator (fun k => |v α k|) k) :
    (∃! T : FreeGraphDomain →L[ℂ] Physical,
      Tendsto (singularFiniteMap α K hα hK m hm hd) atTop (𝓝 T)) ∧
    ‖singularAnnihilationMap α K hα hK m hm hd‖ ≤ (1/2 : ℝ)*Real.sqrt (coefficientTTail α K) ∧
    (∀ R : ℝ, K < R →
      ‖singularAnnihilationMap α K hα hK m hm hd-singularFiniteMap α K hα hK m hm hd R‖ ≤
        (1/2 : ℝ)*Real.sqrt (coefficientTTail α R)) ∧
    (∀ hL2 : MemLp m 2 (volume : Measure GW.Space),
      singularAnnihilationMap α K hα hK m hm hd = convolutionAnnihilationMap (hL2.toLp m)) := by
  refine ⟨?_,singularAnnihilation_norm α K hα hK m hm hd,
    singularAnnihilation_error α K hα hK m hm hd,singularAnnihilation_L2 α K hα hK m hm hd⟩
  refine ⟨singularAnnihilationMap α K hα hK m hm hd,
    singularAnnihilation_tendsto α K hα hK m hm hd,?_⟩
  intro T hT
  exact singularAnnihilation_unique α K hα hK m hm hd T hT

end GW.Gross
