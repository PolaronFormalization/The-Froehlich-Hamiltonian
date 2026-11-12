module
public import GW.Fock.FockExponentialTotality
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Analysis.InnerProductSpace.Adjoint
@[expose] public section
noncomputable section
open scoped InnerProductSpace BigOperators
namespace GW.Fock

def weylCoefficient (f g : OneBoson) : ℂ :=
  Complex.exp (-((‖f‖^2:ℝ):ℂ)/2-⟪f,g⟫_ℂ)

def weylCoherent (f g : OneBoson) : Carrier :=
  weylCoefficient f g • exponentialVector (g+f)

lemma weylCoherent_inner (f g h : OneBoson) :
    ⟪weylCoherent f g, weylCoherent f h⟫_ℂ = ⟪exponentialVector g,exponentialVector h⟫_ℂ := by
  unfold weylCoherent weylCoefficient
  rw [inner_smul_left,inner_smul_right,exponentialVector_inner,exponentialVector_inner]
  rw [← Complex.exp_conj, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  have hff : ⟪f,f⟫_ℂ = ((‖f‖^2:ℝ):ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    exact (RCLike.ofReal_pow (K := ℂ) ‖f‖ 2).symm
  simp only [map_sub,map_div,map_neg,Complex.conj_ofReal,map_ofNat,inner_conj_symm,
    inner_add_left,inner_add_right,hff]
  simp only [map_mul, map_div₀, map_neg, map_pow, map_ofNat, RCLike.conj_ofReal, Complex.conj_ofReal, RCLike.ofReal_pow, Complex.ofReal_pow]
  ring


lemma weylLinearCombination_inner (f : OneBoson) (c d : OneBoson →₀ ℂ) :
    ⟪Finsupp.linearCombination ℂ (weylCoherent f) c,
      Finsupp.linearCombination ℂ (weylCoherent f) d⟫_ℂ =
    ⟪Finsupp.linearCombination ℂ exponentialVector c,
      Finsupp.linearCombination ℂ exponentialVector d⟫_ℂ := by
  simp only [Finsupp.linearCombination_apply, Finsupp.sum_inner, Finsupp.inner_sum,
    inner_smul_left, inner_smul_right, weylCoherent_inner]

lemma weylLinearCombination_norm (f : OneBoson) (c : OneBoson →₀ ℂ) :
    ‖Finsupp.linearCombination ℂ (weylCoherent f) c‖ =
      ‖Finsupp.linearCombination ℂ exponentialVector c‖ := by
  have h := congrArg (fun z : ℂ => RCLike.re z) (weylLinearCombination_inner f c c)
  rw [← norm_sq_eq_re_inner (𝕜 := ℂ), ← norm_sq_eq_re_inner (𝕜 := ℂ)] at h
  nlinarith [norm_nonneg (Finsupp.linearCombination ℂ (weylCoherent f) c),
    norm_nonneg (Finsupp.linearCombination ℂ exponentialVector c)]


def weylCoreInput : (OneBoson →₀ ℂ) →ₗ[ℂ] Carrier :=
  Finsupp.linearCombination ℂ exponentialVector

def weylCoreOutput (f : OneBoson) : (OneBoson →₀ ℂ) →ₗ[ℂ] Carrier :=
  Finsupp.linearCombination ℂ (weylCoherent f)

lemma weylCore_kernel (f : OneBoson) :
    LinearMap.ker weylCoreInput.rangeRestrict ≤ LinearMap.ker (weylCoreOutput f) := by
  intro c hc
  have hi : weylCoreInput c = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp hc)
  rw [LinearMap.mem_ker]
  apply norm_eq_zero.mp
  change ‖Finsupp.linearCombination ℂ (weylCoherent f) c‖ = 0
  rw [weylLinearCombination_norm]
  change ‖weylCoreInput c‖ = 0
  rw [hi, norm_zero]

def weylAlgebraic (f : OneBoson) : LinearMap.range weylCoreInput →ₗ[ℂ] Carrier :=
  (weylCoreInput.rangeRestrict.liftOfSurjective weylCoreInput.surjective_rangeRestrict)
    ⟨weylCoreOutput f, weylCore_kernel f⟩

lemma weylAlgebraic_apply (f : OneBoson) (c : OneBoson →₀ ℂ) :
    weylAlgebraic f (weylCoreInput.rangeRestrict c) = weylCoreOutput f c :=
  LinearMap.equivOfSurjective_apply _ _

lemma weylAlgebraic_norm (f : OneBoson) (u : LinearMap.range weylCoreInput) :
    ‖weylAlgebraic f u‖ = ‖(u : Carrier)‖ := by
  obtain ⟨c, rfl⟩ := weylCoreInput.surjective_rangeRestrict u
  rw [weylAlgebraic_apply]
  exact weylLinearCombination_norm f c


lemma weylCore_range : LinearMap.range weylCoreInput = exponentialSpan ⊤ := by
  rw [weylCoreInput, Finsupp.range_linearCombination, exponentialSpan]
  congr 1
  ext u
  simp only [Set.mem_range, Set.mem_setOf_eq, Submodule.mem_top, true_and]
  exact ⟨fun ⟨g,h⟩ => ⟨g,h.symm⟩, fun ⟨g,h⟩ => ⟨g,h.symm⟩⟩

lemma weylCore_dense : DenseRange (LinearMap.range weylCoreInput).subtype := by
  change Dense (Set.range (Subtype.val : LinearMap.range weylCoreInput → Carrier))
  rw [Subtype.range_coe_subtype]
  rw [weylCore_range]
  exact exponentialSpan_dense ⊤ (by simp)

def weylIsometry (f : OneBoson) : Carrier →ₗᵢ[ℂ] Carrier :=
  (weylAlgebraic f).extendOfIsometry weylCore_dense (weylAlgebraic_norm f)

lemma weylIsometry_core (f : OneBoson) (u : LinearMap.range weylCoreInput) :
    weylIsometry f (u : Carrier) = weylAlgebraic f u :=
  LinearMap.extendOfIsometry_eq _ _ _ u

lemma weylIsometry_exponential (f g : OneBoson) :
    weylIsometry f (exponentialVector g) = weylCoherent f g := by
  have hi : weylCoreInput (Finsupp.single g 1) = exponentialVector g := by
    simp [weylCoreInput]
  rw [← hi]
  change weylIsometry f ((weylCoreInput.rangeRestrict (Finsupp.single g 1) : LinearMap.range weylCoreInput) : Carrier) = _
  rw [weylIsometry_core, weylAlgebraic_apply]
  simp [weylCoreOutput]


lemma weylCoefficient_comp (f g h : OneBoson) :
    weylCoefficient g h * weylCoefficient f (h+g) =
      Complex.exp (-Complex.I * ((⟪f,g⟫_ℂ).im:ℂ)) * weylCoefficient (f+g) h := by
  unfold weylCoefficient
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  rw [norm_add_sq (𝕜 := ℂ)]
  simp only [inner_add_right, inner_add_left]
  push_cast
  have hz := Complex.re_add_im ⟪f,g⟫_ℂ
  linear_combination hz


lemma exponentialVector_ext {A B : Carrier →L[ℂ] Carrier}
    (h : ∀ g : OneBoson, A (exponentialVector g) = B (exponentialVector g)) : A = B := by
  have hd : Dense (Submodule.span ℂ (Set.range exponentialVector) : Set Carrier) := by
    rw [← Finsupp.range_linearCombination]
    change Dense (LinearMap.range weylCoreInput : Set Carrier)
    rw [weylCore_range]
    exact exponentialSpan_dense ⊤ (by simp)
  apply ContinuousLinearMap.ext_on hd
  rintro u ⟨g,rfl⟩
  exact h g

lemma weylIsometry_mul (f g : OneBoson) :
    (weylIsometry f).toContinuousLinearMap.comp (weylIsometry g).toContinuousLinearMap =
      Complex.exp (-Complex.I * ((⟪f,g⟫_ℂ).im:ℂ)) • (weylIsometry (f+g)).toContinuousLinearMap := by
  apply exponentialVector_ext
  intro h
  change weylIsometry f (weylIsometry g (exponentialVector h)) =
    Complex.exp (-Complex.I * ((⟪f,g⟫_ℂ).im:ℂ)) • weylIsometry (f+g) (exponentialVector h)
  rw [weylIsometry_exponential, weylIsometry_exponential]
  unfold weylCoherent
  rw [map_smul, weylIsometry_exponential]
  unfold weylCoherent
  rw [smul_smul, smul_smul, weylCoefficient_comp]
  congr 2
  abel

lemma weylIsometry_zero : (weylIsometry 0).toContinuousLinearMap = ContinuousLinearMap.id ℂ Carrier := by
  apply exponentialVector_ext
  intro g
  change weylIsometry 0 (exponentialVector g) = exponentialVector g
  rw [weylIsometry_exponential]
  simp [weylCoherent, weylCoefficient]


lemma weylIsometry_inverse_right (f : OneBoson) (u : Carrier) :
    weylIsometry f (weylIsometry (-f) u) = u := by
  have h := weylIsometry_mul f (-f)
  have hi : (⟪f,f⟫_ℂ).im = 0 := inner_self_im (𝕜 := ℂ) f
  rw [add_neg_cancel, weylIsometry_zero] at h
  simp only [inner_neg_right, Complex.neg_im, hi, neg_zero, Complex.ofReal_zero,
    mul_zero, Complex.exp_zero, one_smul] at h
  exact congrArg (fun T : Carrier →L[ℂ] Carrier => T u) h

lemma weylIsometry_inverse_left (f : OneBoson) (u : Carrier) :
    weylIsometry (-f) (weylIsometry f u) = u := by
  simpa only [neg_neg] using weylIsometry_inverse_right (-f) u

lemma weylIsometry_surjective (f : OneBoson) : Function.Surjective (weylIsometry f) :=
  fun u => ⟨weylIsometry (-f) u, weylIsometry_inverse_right f u⟩

def weylUnitary (f : OneBoson) : Carrier ≃ₗᵢ[ℂ] Carrier :=
  LinearIsometryEquiv.ofSurjective (weylIsometry f) (weylIsometry_surjective f)

lemma weylUnitary_apply (f : OneBoson) (u : Carrier) : weylUnitary f u = weylIsometry f u := rfl

lemma weylUnitary_symm (f : OneBoson) (u : Carrier) :
    (weylUnitary f).symm u = weylUnitary (-f) u := by
  apply (weylUnitary f).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact (weylIsometry_inverse_right f u).symm

lemma weylUnitary_adjoint (f : OneBoson) :
    (weylUnitary f : Carrier →L[ℂ] Carrier).adjoint = (weylUnitary (-f) : Carrier →L[ℂ] Carrier) := by
  rw [LinearIsometryEquiv.adjoint_eq_symm]
  apply ContinuousLinearMap.ext
  intro u
  exact weylUnitary_symm f u

lemma weylUnitary_exponential (f g : OneBoson) :
    weylUnitary f (exponentialVector g) = weylCoefficient f g • exponentialVector (g+f) :=
  weylIsometry_exponential f g

lemma weylUnitary_unique (f : OneBoson) (T : Carrier →L[ℂ] Carrier)
    (hT : ∀ g, T (exponentialVector g) = weylCoefficient f g • exponentialVector (g+f)) :
    T = (weylUnitary f : Carrier →L[ℂ] Carrier) := by
  apply exponentialVector_ext
  intro g
  exact (hT g).trans (weylUnitary_exponential f g).symm


lemma exponentialVector_continuous : Continuous exponentialVector := by
  have hc := (numberDomainIsometry Sector 0 (by norm_num)).continuous.comp
    (coherentExponentialWeighted_contDiff 0 0 (by norm_num)).continuous
  change Continuous (exponentialGraph 0 (by norm_num)) at hc
  have he : exponentialGraph 0 (by norm_num) = exponentialVector := funext exponentialGraph_zero
  rw [he] at hc
  exact hc

lemma weylCoherent_continuous (g : OneBoson) : Continuous (fun f => weylCoherent f g) := by
  unfold weylCoherent
  have hc : Continuous (fun f => weylCoefficient f g) := by
    unfold weylCoefficient
    fun_prop
  have hg : Continuous (fun f : OneBoson => g+f) := continuous_const.fun_add continuous_id
  have he : Continuous (fun f : OneBoson => exponentialVector (g+f)) := exponentialVector_continuous.comp hg
  exact hc.fun_smul he

lemma weylIsometry_continuous_span (u : Carrier) (hu : u ∈ exponentialSpan ⊤) :
    Continuous (fun f => weylIsometry f u) := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, _, rfl⟩ := hx
    simpa only [weylIsometry_exponential] using weylCoherent_continuous g
  | zero =>
    simp only [map_zero]
    exact continuous_const
  | add x y hx hy ihx ihy =>
    simpa only [map_add] using ihx.fun_add ihy
  | smul a x hx ih =>
    simpa only [map_smul] using ih.fun_const_smul a

lemma weylIsometry_strong_continuous (u : Carrier) : Continuous (fun f => weylIsometry f u) := by
  apply continuous_iff_continuousAt.mpr
  intro f₀
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨v, hv, huv⟩ := (exponentialSpan_dense ⊤ (by simp)).exists_dist_lt u
    (by linarith : 0 < ε/4)
  obtain ⟨δ,hδ,hd⟩ := Metric.continuousAt_iff.mp (weylIsometry_continuous_span v hv).continuousAt
    (ε/2) (by linarith)
  refine ⟨δ,hδ,?_⟩
  intro f hf
  have hmid := hd hf
  have h₁ := dist_triangle (weylIsometry f u) (weylIsometry f v) (weylIsometry f₀ u)
  have h₂ := dist_triangle (weylIsometry f v) (weylIsometry f₀ v) (weylIsometry f₀ u)
  rw [(weylIsometry f).isometry.dist_eq] at h₁
  rw [(weylIsometry f₀).isometry.dist_eq, dist_comm v u] at h₂
  linarith


lemma weylUnitary_mul (f g : OneBoson) :
    (weylUnitary f : Carrier →L[ℂ] Carrier).comp (weylUnitary g : Carrier →L[ℂ] Carrier) =
      Complex.exp (-Complex.I * ((⟪f,g⟫_ℂ).im:ℂ)) • (weylUnitary (f+g) : Carrier →L[ℂ] Carrier) :=
  weylIsometry_mul f g

lemma weylUnitary_strong_continuous (u : Carrier) : Continuous (fun f => weylUnitary f u) :=
  weylIsometry_strong_continuous u

lemma weylUnitary_norm (f : OneBoson) : ‖(weylUnitary f : Carrier →L[ℂ] Carrier)‖ = 1 := by
  apply le_antisymm
  · apply (weylUnitary f : Carrier →L[ℂ] Carrier).opNorm_le_bound (by norm_num : (0:ℝ) ≤ 1)
    intro u
    change ‖weylUnitary f u‖ ≤ 1*‖u‖
    rw [LinearIsometryEquiv.norm_map, one_mul]
  · have hv : ‖exponentialVector 0‖ = 1 := by
      have hs := exponentialVector_norm_sq (0:OneBoson)
      simp only [norm_zero, zero_pow (by norm_num : 2 ≠ 0), Real.exp_zero] at hs
      nlinarith [norm_nonneg (exponentialVector 0)]
    have h := (weylUnitary f : Carrier →L[ℂ] Carrier).le_opNorm (exponentialVector 0)
    change ‖weylUnitary f (exponentialVector 0)‖ ≤
      ‖(weylUnitary f : Carrier →L[ℂ] Carrier)‖ * ‖exponentialVector 0‖ at h
    rwa [LinearIsometryEquiv.norm_map, hv, mul_one] at h

end GW.Fock
