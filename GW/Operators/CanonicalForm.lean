module
public import GW.Operators.FormRepresentation
public import GW.Analysis.RealMultiplier
public import GW.Spaces.WeightedCarrier
@[expose] public section
noncomputable section
open scoped Topology InnerProductSpace
namespace GW.Operators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Exactly the source hypotheses for an arbitrary nonnegative self-adjoint operator. -/
structure NonnegativeOperatorData (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  operator : H →ₗ.[ℂ] H
  selfadjoint : IsSelfAdjointOperator operator
  nonnegative : ∀ u : operator.domain, 0 ≤ (⟪(u : H),operator u⟫_ℂ).re

variable (d : NonnegativeOperatorData H)

def CanonicalDomain : Type _ := d.operator.domain
instance canonicalDomainAddCommGroup : AddCommGroup (CanonicalDomain d) :=
  inferInstanceAs (AddCommGroup d.operator.domain)
instance canonicalDomainModule : Module ℂ (CanonicalDomain d) :=
  inferInstanceAs (Module ℂ d.operator.domain)

lemma canonical_symmetric : d.operator.IsFormalAdjoint d.operator := by
  simpa only [d.selfadjoint.2] using (LinearPMap.adjoint_isFormalAdjoint d.selfadjoint.1)

def canonicalCoordinates : CanonicalDomain d ≃ₗ[ℂ] d.operator.domain := LinearEquiv.refl ℂ _
def canonicalInclusionLinear : CanonicalDomain d →ₗ[ℂ] H :=
  d.operator.domain.subtype.comp (canonicalCoordinates d).toLinearMap

set_option backward.isDefEq.respectTransparency.types false in
@[instance_reducible]
def canonicalCore : InnerProductSpace.Core ℂ (CanonicalDomain d) where
  inner u v := ⟪canonicalInclusionLinear d u,canonicalInclusionLinear d v⟫_ℂ +
    ⟪canonicalInclusionLinear d u,d.operator (canonicalCoordinates d v)⟫_ℂ
  conj_inner_symm u v := by
    simp only [map_add,inner_conj_symm]
    exact congrArg (fun z : ℂ => ⟪canonicalInclusionLinear d u,canonicalInclusionLinear d v⟫_ℂ+z)
      (canonical_symmetric d (canonicalCoordinates d u) (canonicalCoordinates d v))
  re_inner_nonneg u := by
    change 0 ≤ (⟪canonicalInclusionLinear d u,canonicalInclusionLinear d u⟫_ℂ +
      ⟪canonicalInclusionLinear d u,d.operator (canonicalCoordinates d u)⟫_ℂ).re
    have hi : (⟪canonicalInclusionLinear d u,canonicalInclusionLinear d u⟫_ℂ).re =
        ‖canonicalInclusionLinear d u‖^2 := (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm
    rw [Complex.add_re,hi]
    exact add_nonneg (sq_nonneg _) (d.nonnegative _)
  add_left u v w := by simp only [map_add,inner_add_left];ring
  smul_left u v r := by simp only [map_smul,inner_smul_left];ring
  definite u hu := by
    have hp := d.nonnegative (canonicalCoordinates d u)
    change ⟪canonicalInclusionLinear d u,canonicalInclusionLinear d u⟫_ℂ +
      ⟪canonicalInclusionLinear d u,d.operator (canonicalCoordinates d u)⟫_ℂ = 0 at hu
    have he := congrArg Complex.re hu
    have hi : (⟪canonicalInclusionLinear d u,canonicalInclusionLinear d u⟫_ℂ).re =
        ‖canonicalInclusionLinear d u‖^2 := (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm
    rw [Complex.add_re,hi,Complex.zero_re] at he
    change 0 ≤ (⟪canonicalInclusionLinear d u,d.operator (canonicalCoordinates d u)⟫_ℂ).re at hp
    have hn : ‖canonicalInclusionLinear d u‖ = 0 := by nlinarith [sq_nonneg ‖canonicalInclusionLinear d u‖]
    apply (canonicalCoordinates d).injective
    apply Subtype.ext
    exact norm_eq_zero.mp hn

instance canonicalDomainNorm : NormedAddCommGroup (CanonicalDomain d) := by
  letI : InnerProductSpace.Core ℂ (CanonicalDomain d) := canonicalCore d
  exact InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
instance canonicalDomainInner : InnerProductSpace ℂ (CanonicalDomain d) := by
  letI : InnerProductSpace.Core ℂ (CanonicalDomain d) := canonicalCore d
  exact InnerProductSpace.ofCore (canonicalCore d).toCore

lemma canonicalDomain_inner (u v : CanonicalDomain d) : ⟪u,v⟫_ℂ =
    ⟪canonicalInclusionLinear d u,canonicalInclusionLinear d v⟫_ℂ +
    ⟪canonicalInclusionLinear d u,d.operator (canonicalCoordinates d v)⟫_ℂ := rfl

lemma canonicalDomain_norm_sq (u : CanonicalDomain d) : ‖u‖^2 =
    ‖canonicalInclusionLinear d u‖^2 +
      (⟪canonicalInclusionLinear d u,d.operator (canonicalCoordinates d u)⟫_ℂ).re := by
  have h := norm_sq_eq_re_inner (𝕜 := ℂ) u
  change ‖u‖^2 = (⟪u,u⟫_ℂ).re at h
  have hi : (⟪canonicalInclusionLinear d u,canonicalInclusionLinear d u⟫_ℂ).re =
      ‖canonicalInclusionLinear d u‖^2 := (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm
  rw [canonicalDomain_inner,Complex.add_re,hi] at h
  exact h

lemma canonicalDomain_ambient_bound (u : CanonicalDomain d) :
    ‖canonicalInclusionLinear d u‖ ≤ ‖u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [canonicalDomain_norm_sq]
  exact le_add_of_nonneg_right (d.nonnegative _)

def canonicalDomainInclusion : CanonicalDomain d →L[ℂ] H :=
  (canonicalInclusionLinear d).mkContinuous 1
    (fun u => by simpa only [one_mul] using canonicalDomain_ambient_bound d u)

abbrev CanonicalEnergySpace := UniformSpace.Completion (CanonicalDomain d)

def canonicalEmbedding : CanonicalEnergySpace d →L[ℂ] H := (canonicalDomainInclusion d).fromCompletion
lemma canonicalEmbedding_coe (u : CanonicalDomain d) :
    canonicalEmbedding d (u : CanonicalEnergySpace d) = canonicalDomainInclusion d u :=
  ContinuousLinearMap.fromCompletion_apply_coe _ u

lemma canonicalEmbedding_bound (u : CanonicalEnergySpace d) : ‖canonicalEmbedding d u‖ ≤ ‖u‖ := by
  refine UniformSpace.Completion.induction_on u
    (isClosed_le (canonicalEmbedding d).continuous.norm continuous_norm) ?_
  intro v
  rw [canonicalEmbedding_coe,UniformSpace.Completion.norm_coe]
  exact canonicalDomain_ambient_bound d v

lemma canonicalEmbedding_norm : ‖canonicalEmbedding d‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  simpa only [one_mul] using canonicalEmbedding_bound d u

lemma canonicalDomain_mixed (u v : CanonicalDomain d) :
    ⟪u,v⟫_ℂ = ⟪d.operator (canonicalCoordinates d u)+canonicalInclusionLinear d u,canonicalInclusionLinear d v⟫_ℂ := by
  have hs : ⟪d.operator (canonicalCoordinates d u),canonicalInclusionLinear d v⟫_ℂ =
      ⟪canonicalInclusionLinear d u,d.operator (canonicalCoordinates d v)⟫_ℂ :=
    canonical_symmetric d _ _
  rw [canonicalDomain_inner,inner_add_left,hs,add_comm]

lemma canonicalCompletion_mixed (u : CanonicalDomain d) (v : CanonicalEnergySpace d) :
    ⟪(u : CanonicalEnergySpace d),v⟫_ℂ =
      ⟪d.operator (canonicalCoordinates d u)+canonicalInclusionLinear d u,canonicalEmbedding d v⟫_ℂ := by
  refine UniformSpace.Completion.induction_on v (isClosed_eq
    (continuous_const.inner continuous_id) (continuous_const.inner (canonicalEmbedding d).continuous)) ?_
  intro w
  rw [UniformSpace.Completion.inner_coe,canonicalEmbedding_coe]
  exact canonicalDomain_mixed d u w

lemma canonicalEmbedding_injective : Function.Injective (canonicalEmbedding d) := by
  have hzero : ∀ u, canonicalEmbedding d u = 0 → u = 0 := by
    intro u hu
    apply ext_inner_left ℂ
    intro v
    refine UniformSpace.Completion.induction_on v
      (isClosed_eq (continuous_id.inner continuous_const) (continuous_id.inner continuous_const)) ?_
    intro w
    rw [canonicalCompletion_mixed,hu,inner_zero_right,inner_zero_right]
  intro u v huv
  apply sub_eq_zero.mp
  apply hzero
  rw [map_sub,huv,sub_self]

lemma canonicalEmbedding_dense : DenseRange (canonicalEmbedding d) := by
  apply d.selfadjoint.1.mono
  intro x hx
  refine ⟨((canonicalCoordinates d).symm ⟨x,hx⟩ : CanonicalEnergySpace d),?_⟩
  rw [canonicalEmbedding_coe]
  rfl

def canonicalForm : AlgebraicForm (CanonicalEnergySpace d) :=
  innerₛₗ ℂ - embeddingForm (canonicalEmbedding d)

lemma canonicalForm_apply (u v : CanonicalEnergySpace d) :
    canonicalForm d u v = ⟪u,v⟫_ℂ-⟪canonicalEmbedding d u,canonicalEmbedding d v⟫_ℂ := rfl

lemma canonicalForm_hermitian (u v : CanonicalEnergySpace d) :
    canonicalForm d u v = star (canonicalForm d v u) := by
  simp only [canonicalForm_apply,star_sub,Complex.star_def,inner_conj_symm]

lemma canonicalForm_continuous : Continuous (fun p : CanonicalEnergySpace d × CanonicalEnergySpace d => canonicalForm d p.1 p.2) :=
  (continuous_fst.inner continuous_snd).sub
    (((canonicalEmbedding d).continuous.comp continuous_fst).inner
      ((canonicalEmbedding d).continuous.comp continuous_snd))

lemma canonicalForm_coe (u v : CanonicalDomain d) :
    canonicalForm d (u : CanonicalEnergySpace d) (v : CanonicalEnergySpace d) =
      ⟪canonicalInclusionLinear d u,d.operator (canonicalCoordinates d v)⟫_ℂ := by
  rw [canonicalForm_apply,UniformSpace.Completion.inner_coe,canonicalDomain_inner,
    canonicalEmbedding_coe,canonicalEmbedding_coe]
  change (⟪canonicalInclusionLinear d u,canonicalInclusionLinear d v⟫_ℂ +
    ⟪canonicalInclusionLinear d u,d.operator (canonicalCoordinates d v)⟫_ℂ) -
      ⟪canonicalInclusionLinear d u,canonicalInclusionLinear d v⟫_ℂ = _
  ring

set_option maxHeartbeats 800000 in
lemma canonicalForm_nonnegative (u : CanonicalEnergySpace d) : 0 ≤ (canonicalForm d u u).re := by
  have hc : Continuous (fun v : CanonicalEnergySpace d => (canonicalForm d v v).re) := by
    change Continuous (fun v : CanonicalEnergySpace d =>
      (⟪v,v⟫_ℂ-⟪canonicalEmbedding d v,canonicalEmbedding d v⟫_ℂ).re)
    exact Complex.continuous_re.comp ((continuous_id.inner continuous_id).sub
      ((canonicalEmbedding d).continuous.inner (canonicalEmbedding d).continuous))
  refine UniformSpace.Completion.induction_on u (isClosed_le continuous_const hc) ?_
  intro v
  rw [canonicalForm_coe]
  exact d.nonnegative (canonicalCoordinates d v)

lemma canonicalForm_shifted_norm (u : CanonicalEnergySpace d) :
    (canonicalForm d u u).re + ‖canonicalEmbedding d u‖^2 = ‖u‖^2 := by
  rw [canonicalForm_apply,Complex.sub_re]
  have hu := norm_sq_eq_re_inner (𝕜 := ℂ) u
  have hj := norm_sq_eq_re_inner (𝕜 := ℂ) (canonicalEmbedding d u)
  change ‖u‖^2 = (⟪u,u⟫_ℂ).re at hu
  change ‖canonicalEmbedding d u‖^2 = (⟪canonicalEmbedding d u,canonicalEmbedding d u⟫_ℂ).re at hj
  linarith

def canonicalFormData : CoerciveFormData (CanonicalEnergySpace d) H where
  embedding := canonicalEmbedding d
  embedding_injective := canonicalEmbedding_injective d
  embedding_dense := canonicalEmbedding_dense d
  form := canonicalForm d
  hermitian := canonicalForm_hermitian d
  continuous_form := canonicalForm_continuous d
  shift := 1
  lower := 1
  upper := 1
  lower_pos := zero_lt_one
  lower_le_upper := le_rfl
  lower_bound u := by simpa only [one_mul] using (canonicalForm_shifted_norm d u).symm.le
  upper_bound u := by simpa only [one_mul] using (canonicalForm_shifted_norm d u).le

lemma canonicalForm_on_domain (v : CanonicalDomain d) (u : CanonicalEnergySpace d) :
    canonicalForm d u (v : CanonicalEnergySpace d) =
      ⟪canonicalEmbedding d u,d.operator (canonicalCoordinates d v)⟫_ℂ := by
  have he : ⟪u,(v : CanonicalEnergySpace d)⟫_ℂ =
      ⟪canonicalEmbedding d u,d.operator (canonicalCoordinates d v)+canonicalInclusionLinear d v⟫_ℂ := by
    have h := congrArg (starRingEnd ℂ) (canonicalCompletion_mixed d v u)
    simpa only [inner_conj_symm] using h
  rw [canonicalForm_apply,he,canonicalEmbedding_coe]
  change ⟪canonicalEmbedding d u,d.operator (canonicalCoordinates d v)+canonicalInclusionLinear d v⟫_ℂ -
    ⟪canonicalEmbedding d u,canonicalInclusionLinear d v⟫_ℂ = _
  rw [inner_add_right,add_sub_cancel_right]

lemma canonicalForm_representing_operator : formOperator (canonicalFormData d) = d.operator := by
  symm
  apply formOperator_unique _ d.operator d.selfadjoint
  intro x
  refine ⟨((canonicalCoordinates d).symm x : CanonicalEnergySpace d),?_,?_⟩
  · change canonicalEmbedding d ((canonicalCoordinates d).symm x : CanonicalEnergySpace d) = (x : H)
    rw [canonicalEmbedding_coe]
    rfl
  · intro u
    exact canonicalForm_on_domain d ((canonicalCoordinates d).symm x) u

lemma canonicalEnergyForm_apply (u v : CanonicalEnergySpace d) :
    energyForm (canonicalFormData d) u v = ⟪u,v⟫_ℂ := by
  rw [energyForm_apply]
  change canonicalForm d u v+(1 : ℂ)*⟪canonicalEmbedding d u,canonicalEmbedding d v⟫_ℂ = _
  rw [canonicalForm_apply,one_mul,sub_add_cancel]

def canonicalClosedFormEquiv : EnergySpace (canonicalFormData d) ≃ₗᵢ[ℂ] CanonicalEnergySpace d where
  toLinearEquiv := energyCoordinates (canonicalFormData d)
  norm_map' u := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [energy_norm_sq,canonicalEnergyForm_apply]
    exact norm_sq_eq_re_inner (𝕜 := ℂ) _

lemma nonnegativeData_ext {e : NonnegativeOperatorData H} (h : d.operator = e.operator) : d = e := by
  cases d
  cases e
  cases h
  rfl

def canonicalEnergyCongr (e : NonnegativeOperatorData H) (h : d = e) :
    CanonicalEnergySpace d ≃ₗᵢ[ℂ] CanonicalEnergySpace e := by
  subst e
  exact LinearIsometryEquiv.refl ℂ _

lemma canonicalEnergyCongr_embedding (e : NonnegativeOperatorData H) (h : d = e) (u : CanonicalEnergySpace d) :
    canonicalEmbedding e (canonicalEnergyCongr d e h u) = canonicalEmbedding d u := by
  subst e
  rfl

section Multiplication
open MeasureTheory Filter
open scoped ENNReal
variable {X K : Type*} [MeasurableSpace X] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (μ : Measure X) (m : X → ℝ) (hm : Measurable m) (hm0 : ∀ x, 0 ≤ m x)

include hm0 in
omit [CompleteSpace K] in
lemma multiplier_nonnegative (u : (GW.Analysis.realMultiplier (H := K) m μ).domain) :
    0 ≤ (⟪(u : Lp K 2 μ),GW.Analysis.realMultiplier m μ u⟫_ℂ).re := by
  have he : (⟪(u : Lp K 2 μ),GW.Analysis.realMultiplier m μ u⟫_ℂ).re =
      ∫ x, (⟪(u : Lp K 2 μ) x,GW.Analysis.realMultiplier m μ u x⟫_ℂ).re ∂μ := by
    rw [L2.inner_def]
    exact (integral_re (L2.integrable_inner (𝕜 := ℂ) (u : Lp K 2 μ) (GW.Analysis.realMultiplier m μ u))).symm
  rw [he]
  apply integral_nonneg_of_ae
  filter_upwards [GW.Analysis.realMultiplier_ae m u] with x hx
  rw [← hx,inner_smul_right,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  have hi : (⟪(u : Lp K 2 μ) x,(u : Lp K 2 μ) x⟫_ℂ).re = ‖(u : Lp K 2 μ) x‖^2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm
  rw [hi]
  exact mul_nonneg (hm0 x) (sq_nonneg _)

def multiplierData : NonnegativeOperatorData (Lp K 2 μ) where
  operator := GW.Analysis.realMultiplier m μ
  selfadjoint := GW.Analysis.realMultiplier_selfadjoint hm
  nonnegative := multiplier_nonnegative μ m hm0

def canonicalMultiplierInput : CanonicalDomain (multiplierData (K := K) μ m hm hm0) →ₗ[ℂ]
    (GW.Analysis.realMultiplier (H := K) (GW.Spaces.multiplierEnergyWeight m) μ).domain where
  toFun u := GW.Spaces.multiplierEnergyInput hm hm0 (canonicalCoordinates _ u)
  map_add' u v := by apply Subtype.ext;exact (canonicalInclusionLinear _).map_add u v
  map_smul' c u := by apply Subtype.ext;exact (canonicalInclusionLinear _).map_smul c u

def canonicalMultiplierLinear : CanonicalDomain (multiplierData (K := K) μ m hm hm0) →ₗ[ℂ]
    GW.Spaces.WeightedL2 K (GW.Spaces.multiplierEnergyWeight m) μ :=
  (GW.Analysis.realMultiplier (H := K) (GW.Spaces.multiplierEnergyWeight m) μ).toFun.comp
    (canonicalMultiplierInput μ m hm hm0)

set_option backward.isDefEq.respectTransparency.types false in
def canonicalMultiplierIsometry : CanonicalDomain (multiplierData (K := K) μ m hm hm0) →ₗᵢ[ℂ]
    GW.Spaces.WeightedL2 K (GW.Spaces.multiplierEnergyWeight m) μ where
  toLinearMap := canonicalMultiplierLinear μ m hm hm0
  norm_map' u := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change ‖GW.Analysis.realMultiplier (GW.Spaces.multiplierEnergyWeight m) μ
      (canonicalMultiplierInput μ m hm hm0 u)‖^2 = ‖u‖^2
    rw [canonicalDomain_norm_sq]
    exact GW.Spaces.multiplierEnergyWeight_norm_sq hm hm0 (canonicalCoordinates _ u)

set_option backward.isDefEq.respectTransparency.types false in
lemma canonicalMultiplier_embed (u : CanonicalDomain (multiplierData (K := K) μ m hm hm0)) :
    GW.Spaces.WeightedL2.embed (GW.Spaces.multiplierEnergyWeight_measurable hm)
      (GW.Spaces.multiplierEnergyWeight_lower hm0) (canonicalMultiplierIsometry μ m hm hm0 u) =
        canonicalInclusionLinear _ u := by
  change GW.Spaces.reciprocalMap (GW.Spaces.multiplierEnergyWeight_measurable hm)
    (GW.Spaces.multiplierEnergyWeight_lower hm0)
    (GW.Analysis.realMultiplier (GW.Spaces.multiplierEnergyWeight m) μ
      (canonicalMultiplierInput μ m hm hm0 u)) = _
  exact GW.Spaces.reciprocalMap_inverse _ _ (canonicalMultiplierInput μ m hm hm0 u)

omit [CompleteSpace K] in
lemma canonicalMultiplier_cutoff_mem (n : ℕ)
    (f : GW.Spaces.WeightedL2 K (GW.Spaces.multiplierEnergyWeight m) μ) :
    GW.Spaces.WeightedL2.embed (GW.Spaces.multiplierEnergyWeight_measurable hm)
      (GW.Spaces.multiplierEnergyWeight_lower hm0)
        (GW.Spaces.WeightedL2.cutoff {x | m x ≤ (n : ℝ)} (measurableSet_le hm measurable_const) f) ∈
          (GW.Analysis.realMultiplier (H := K) m μ).domain := by
  let S := {x | m x ≤ (n : ℝ)}
  have hs : MeasurableSet S := measurableSet_le hm measurable_const
  let u := GW.Spaces.WeightedL2.embed (GW.Spaces.multiplierEnergyWeight_measurable hm)
    (GW.Spaces.multiplierEnergyWeight_lower hm0) f
  have hi : MemLp (fun x => (m x : ℂ) • S.indicator (u : X → K) x) 2 μ := by
    apply (Lp.memLp u).of_le_mul (c := (n : ℝ))
      ((Complex.continuous_ofReal.measurable.comp hm).aestronglyMeasurable.smul
        ((Lp.memLp u).aestronglyMeasurable.indicator hs))
    apply Eventually.of_forall
    intro x
    change ‖(m x : ℂ) • S.indicator (u : X → K) x‖ ≤ (n : ℝ)*‖u x‖
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hm0 x)]
      exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
    · rw [Set.indicator_of_notMem hx,smul_zero,norm_zero]
      positivity
  apply (GW.Analysis.realMultiplier_domain _ _).mpr
  apply hi.ae_eq
  filter_upwards [GW.Spaces.WeightedL2.embed_cutoff_ae (GW.Spaces.multiplierEnergyWeight_measurable hm)
    (GW.Spaces.multiplierEnergyWeight_lower hm0) S hs f] with x hx
  exact congrArg (fun v : K => (m x : ℂ) • v) hx

lemma canonicalMultiplier_dense : DenseRange (canonicalMultiplierIsometry (K := K) μ m hm hm0) := by
  intro f
  have ht := GW.Spaces.WeightedL2.cutoff_tendsto (w := GW.Spaces.multiplierEnergyWeight m)
    (fun n : ℕ => {x | m x ≤ (n : ℝ)}) (fun _ => measurableSet_le hm measurable_const)
    (Eventually.of_forall (fun x => by
      obtain ⟨N,hN⟩ := exists_nat_ge (m x)
      exact eventually_atTop.mpr ⟨N,fun n hn => hN.trans (by exact_mod_cast hn)⟩)) f
  apply mem_closure_of_tendsto ht
  apply Eventually.of_forall
  intro n
  let g := GW.Spaces.WeightedL2.cutoff (w := GW.Spaces.multiplierEnergyWeight m)
    {x | m x ≤ (n : ℝ)} (measurableSet_le hm measurable_const) f
  let v := GW.Spaces.WeightedL2.embed (GW.Spaces.multiplierEnergyWeight_measurable hm)
    (GW.Spaces.multiplierEnergyWeight_lower hm0) g
  let u : CanonicalDomain (multiplierData (K := K) μ m hm hm0) :=
    (canonicalCoordinates _).symm ⟨v,canonicalMultiplier_cutoff_mem μ m hm hm0 n f⟩
  refine ⟨u,?_⟩
  apply GW.Spaces.WeightedL2.embed_injective (GW.Spaces.multiplierEnergyWeight_measurable hm)
    (GW.Spaces.multiplierEnergyWeight_lower hm0)
  rw [canonicalMultiplier_embed]
  rfl

def canonicalMultiplierEquiv : CanonicalEnergySpace (multiplierData (K := K) μ m hm hm0) ≃ₗᵢ[ℂ]
    GW.Spaces.WeightedL2 K (GW.Spaces.multiplierEnergyWeight m) μ :=
  completionTransportEquiv (canonicalMultiplierIsometry μ m hm hm0) (canonicalMultiplier_dense μ m hm hm0)

lemma canonicalMultiplierEquiv_coe (u : CanonicalDomain (multiplierData (K := K) μ m hm hm0)) :
    canonicalMultiplierEquiv μ m hm hm0 (u : CanonicalEnergySpace _) = canonicalMultiplierIsometry μ m hm hm0 u :=
  completionTransportEquiv_coe _ _ u

lemma canonicalMultiplier_embedding : canonicalEmbedding (multiplierData (K := K) μ m hm hm0) =
    (GW.Spaces.WeightedL2.embed (GW.Spaces.multiplierEnergyWeight_measurable hm)
      (GW.Spaces.multiplierEnergyWeight_lower hm0)).comp
        (canonicalMultiplierEquiv μ m hm hm0).toContinuousLinearEquiv.toContinuousLinearMap := by
  apply ContinuousLinearMap.fromCompletion_unique
  intro u
  change canonicalDomainInclusion (multiplierData (K := K) μ m hm hm0) u =
    GW.Spaces.WeightedL2.embed (GW.Spaces.multiplierEnergyWeight_measurable hm)
      (GW.Spaces.multiplierEnergyWeight_lower hm0) (canonicalMultiplierEquiv μ m hm hm0 (u : CanonicalEnergySpace _))
  rw [canonicalMultiplierEquiv_coe,canonicalMultiplier_embed]
  rfl

lemma canonicalMultiplier_range : Set.range (canonicalEmbedding (multiplierData (K := K) μ m hm hm0)) =
    ((GW.Analysis.realMultiplier (H := K) (fun x => Real.sqrt (1+m x)) μ).domain : Set (Lp K 2 μ)) := by
  rw [canonicalMultiplier_embedding]
  ext u
  constructor
  · rintro ⟨v,rfl⟩
    exact GW.Spaces.WeightedL2.embed_mem_domain (GW.Spaces.multiplierEnergyWeight_measurable hm)
      (GW.Spaces.multiplierEnergyWeight_lower hm0) (canonicalMultiplierEquiv μ m hm hm0 v)
  · intro hu
    have hmem : u ∈ Set.range (GW.Spaces.WeightedL2.embed (H := K) (μ := μ)
        (GW.Spaces.multiplierEnergyWeight_measurable hm) (GW.Spaces.multiplierEnergyWeight_lower hm0)) := by
      rw [GW.Spaces.WeightedL2.embed_range]
      exact hu
    obtain ⟨f,hf⟩ := hmem
    refine ⟨(canonicalMultiplierEquiv μ m hm hm0).symm f,?_⟩
    change GW.Spaces.WeightedL2.embed (GW.Spaces.multiplierEnergyWeight_measurable hm)
      (GW.Spaces.multiplierEnergyWeight_lower hm0)
      (canonicalMultiplierEquiv μ m hm hm0 ((canonicalMultiplierEquiv μ m hm hm0).symm f)) = u
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact hf

lemma canonicalMultiplier_norm_integral (u : CanonicalEnergySpace (multiplierData (K := K) μ m hm hm0)) :
    ‖u‖^2 = ∫ x, (1+m x)*‖canonicalEmbedding (multiplierData μ m hm hm0) u x‖^2 ∂μ := by
  let f := canonicalMultiplierEquiv μ m hm hm0 u
  have hj : canonicalEmbedding (multiplierData (K := K) μ m hm hm0) u =
      GW.Spaces.WeightedL2.embed (GW.Spaces.multiplierEnergyWeight_measurable hm)
        (GW.Spaces.multiplierEnergyWeight_lower hm0) f := by
    rw [canonicalMultiplier_embedding]
    rfl
  rw [hj]
  calc
    _ = ‖GW.Spaces.WeightedL2.coordinates f‖^2 := by
      rw [LinearIsometryEquiv.norm_map,LinearIsometryEquiv.norm_map]
    _ = ∫ x, ‖GW.Spaces.WeightedL2.coordinates f x‖^2 ∂μ := GW.Analysis.l2_norm_sq (𝕜 := ℂ) _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [GW.Spaces.WeightedL2.weighted_embed_ae
        (GW.Spaces.multiplierEnergyWeight_measurable hm) (GW.Spaces.multiplierEnergyWeight_lower hm0) f] with x hx
      rw [← hx,norm_smul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
      rw [GW.Spaces.multiplierEnergyWeight,Real.sq_sqrt (by have h := hm0 x;linarith)]

end Multiplication
section MultiplicationAE
open MeasureTheory Filter
open scoped ENNReal
variable {X K : Type*} [MeasurableSpace X] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (μ : Measure X) (m : X → ℝ) (hm : Measurable m)

omit [CompleteSpace K] in
lemma realMultiplier_congr_ae {n : X → ℝ} (h : m =ᵐ[μ] n) :
    GW.Analysis.realMultiplier (H := K) m μ = GW.Analysis.realMultiplier n μ := by
  apply LinearPMap.ext
  · apply Submodule.ext
    intro u
    rw [GW.Analysis.realMultiplier_domain,GW.Analysis.realMultiplier_domain]
    exact memLp_congr_ae (h.mono (fun x hx => congrArg (fun t : ℝ => (t : ℂ) • u x) hx))
  · intro u hu hv
    apply Lp.ext
    filter_upwards [GW.Analysis.realMultiplier_ae m ⟨u,hu⟩,
      GW.Analysis.realMultiplier_ae n ⟨u,hv⟩,h] with x hx hy hxy
    rw [← hx,← hy,hxy]

omit [CompleteSpace K] in
lemma multiplier_nonnegativeAE (h0 : ∀ᵐ x ∂μ, 0 ≤ m x)
    (u : (GW.Analysis.realMultiplier (H := K) m μ).domain) :
    0 ≤ (⟪(u : Lp K 2 μ),GW.Analysis.realMultiplier m μ u⟫_ℂ).re := by
  have he : (⟪(u : Lp K 2 μ),GW.Analysis.realMultiplier m μ u⟫_ℂ).re =
      ∫ x, (⟪(u : Lp K 2 μ) x,GW.Analysis.realMultiplier m μ u x⟫_ℂ).re ∂μ := by
    rw [L2.inner_def]
    exact (integral_re (L2.integrable_inner (𝕜 := ℂ) (u : Lp K 2 μ) (GW.Analysis.realMultiplier m μ u))).symm
  rw [he]
  apply integral_nonneg_of_ae
  filter_upwards [GW.Analysis.realMultiplier_ae m u,h0] with x hx hm0
  rw [← hx,inner_smul_right,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  have hi : (⟪(u : Lp K 2 μ) x,(u : Lp K 2 μ) x⟫_ℂ).re = ‖(u : Lp K 2 μ) x‖^2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm
  rw [hi]
  exact mul_nonneg hm0 (sq_nonneg _)

def multiplierDataAE (h0 : ∀ᵐ x ∂μ, 0 ≤ m x) : NonnegativeOperatorData (Lp K 2 μ) where
  operator := GW.Analysis.realMultiplier m μ
  selfadjoint := GW.Analysis.realMultiplier_selfadjoint hm
  nonnegative := multiplier_nonnegativeAE μ m h0

lemma multiplierDataAE_eq (h0 : ∀ᵐ x ∂μ, 0 ≤ m x) :
    multiplierDataAE (K := K) μ m hm h0 =
      multiplierData μ (fun x => max 0 (m x)) (measurable_const.max hm) (fun x => le_max_left 0 (m x)) := by
  apply nonnegativeData_ext
  exact realMultiplier_congr_ae μ m (h0.mono (fun x hx => (max_eq_right hx).symm))

def canonicalMultiplierAEEquiv (h0 : ∀ᵐ x ∂μ, 0 ≤ m x) :
    CanonicalEnergySpace (multiplierDataAE (K := K) μ m hm h0) ≃ₗᵢ[ℂ]
      GW.Spaces.WeightedL2 K (GW.Spaces.multiplierEnergyWeight (fun x => max 0 (m x))) μ :=
  (canonicalEnergyCongr _ _ (multiplierDataAE_eq μ m hm h0)).trans
    (canonicalMultiplierEquiv μ (fun x => max 0 (m x)) (measurable_const.max hm) (fun x => le_max_left 0 (m x)))

lemma canonicalMultiplierAE_embedding (h0 : ∀ᵐ x ∂μ, 0 ≤ m x)
    (u : CanonicalEnergySpace (multiplierDataAE (K := K) μ m hm h0)) :
    canonicalEmbedding (multiplierDataAE μ m hm h0) u =
      GW.Spaces.WeightedL2.embed (GW.Spaces.multiplierEnergyWeight_measurable (measurable_const.max hm))
        (GW.Spaces.multiplierEnergyWeight_lower (fun x => le_max_left 0 (m x)))
        (canonicalMultiplierAEEquiv μ m hm h0 u) := by
  have h := canonicalEnergyCongr_embedding (multiplierDataAE (K := K) μ m hm h0)
    _ (multiplierDataAE_eq μ m hm h0) u
  rw [canonicalMultiplier_embedding] at h
  exact h.symm

lemma canonicalMultiplierAE_range (h0 : ∀ᵐ x ∂μ, 0 ≤ m x) :
    Set.range (canonicalEmbedding (multiplierDataAE (K := K) μ m hm h0)) =
      ((GW.Analysis.realMultiplier (H := K) (fun x => Real.sqrt (1+m x)) μ).domain : Set (Lp K 2 μ)) := by
  have hrange : Set.range (canonicalEmbedding (multiplierDataAE (K := K) μ m hm h0)) =
      ((GW.Analysis.realMultiplier (H := K)
        (GW.Spaces.multiplierEnergyWeight (fun x => max 0 (m x))) μ).domain : Set (Lp K 2 μ)) := by
    ext u
    constructor
    · rintro ⟨v,rfl⟩
      rw [canonicalMultiplierAE_embedding]
      exact GW.Spaces.WeightedL2.embed_mem_domain
        (GW.Spaces.multiplierEnergyWeight_measurable (measurable_const.max hm))
        (GW.Spaces.multiplierEnergyWeight_lower (fun x => le_max_left 0 (m x))) _
    · intro hu
      have hmem : u ∈ Set.range (GW.Spaces.WeightedL2.embed (H := K) (μ := μ)
          (GW.Spaces.multiplierEnergyWeight_measurable (measurable_const.max hm))
          (GW.Spaces.multiplierEnergyWeight_lower (fun x => le_max_left 0 (m x)))) := by
        rw [GW.Spaces.WeightedL2.embed_range]
        exact hu
      obtain ⟨f,hf⟩ := hmem
      refine ⟨(canonicalMultiplierAEEquiv μ m hm h0).symm f,?_⟩
      rw [canonicalMultiplierAE_embedding,LinearIsometryEquiv.apply_symm_apply]
      exact hf
  have he : GW.Analysis.realMultiplier (H := K)
      (GW.Spaces.multiplierEnergyWeight (fun x => max 0 (m x))) μ =
        GW.Analysis.realMultiplier (fun x => Real.sqrt (1+m x)) μ := by
    apply realMultiplier_congr_ae
    exact h0.mono (fun x hx => by simp only [GW.Spaces.multiplierEnergyWeight,max_eq_right hx])
  rw [he] at hrange
  exact hrange

lemma canonicalMultiplierAE_norm_integral (h0 : ∀ᵐ x ∂μ, 0 ≤ m x)
    (u : CanonicalEnergySpace (multiplierDataAE (K := K) μ m hm h0)) :
    ‖u‖^2 = ∫ x, (1+m x)*‖canonicalEmbedding (multiplierDataAE μ m hm h0) u x‖^2 ∂μ := by
  let c := canonicalEnergyCongr (multiplierDataAE (K := K) μ m hm h0) _ (multiplierDataAE_eq μ m hm h0)
  have h := canonicalMultiplier_norm_integral μ (fun x => max 0 (m x)) (measurable_const.max hm)
    (fun x => le_max_left 0 (m x)) (c u)
  have he := canonicalEnergyCongr_embedding (multiplierDataAE (K := K) μ m hm h0) _
    (multiplierDataAE_eq μ m hm h0) u
  change canonicalEmbedding _ (c u) = canonicalEmbedding _ u at he
  rw [c.norm_map,he] at h
  exact h.trans (integral_congr_ae (h0.mono (fun x hx => by dsimp only;rw [max_eq_right hx])))

end MultiplicationAE
end GW.Operators
