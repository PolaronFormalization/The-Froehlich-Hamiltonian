module
public import GW.Gross.MainUniformFormBound
public import GW.Operators.KatoRellich
public import GW.Operators.UniformFormLimit

/-! Source main:form-H, manuscript5916–5996.
Actual finite H0-domain KatoRellich operators, real bounded-form cutoff limit,
original complete form domain, representative equality and zero coupling. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal BigOperators
namespace GW.Gross
open GW.Model GW.Fock GW.Analysis

/- Source argument component Scalar01. -/
lemma constructionSqrtBound (δ t : ℝ) (hδ : 0 < δ) (ht : 0 ≤ t) :
    Real.sqrt (t+1) ≤ δ*t+1+1/(4*δ) := by
  have hroot := Real.sq_sqrt (show 0 ≤ t+1 by linarith)
  have hs := sq_nonneg (Real.sqrt (t+1)-1/(2*δ))
  have hi : 0 ≤ δ*t+1+1/(4*δ) := by positivity
  have hc : δ*(Real.sqrt (t+1)-1/(2*δ))^2 = δ*(t+1)-Real.sqrt (t+1)+1/(4*δ) := by
    rw [sub_sq,hroot]
    field_simp [ne_of_gt hδ]
    <;> ring
  have hh := mul_nonneg hδ.le hs
  rw [hc] at hh
  -- The stronger standard square estimate includes delta; split delta above one.
  by_cases hd : δ ≤ 1
  · nlinarith
  · have htroot : Real.sqrt (t+1) ≤ t+1 := by
      have hhroot := Real.sqrt_nonneg (t+1)
      nlinarith
    have hdt : t ≤ δ*t := le_mul_of_one_le_left ht (le_of_not_ge hd)
    nlinarith [div_nonneg (by norm_num : (0:ℝ) ≤ 1) (by positivity : 0 ≤ 4*δ)]

/- Source argument component Affine03. -/
lemma constructionAffineGraph (δ C : ℝ) (u : freeHamiltonian.domain) :
    (u.val,(δ:ℂ) • freeHamiltonian u+(C:ℂ) • u.val) ∈
      (physicalSectorMultiplier (fun n q => δ*freeEnergySymbol n q+C)).graph := by
  apply smoothProduct_multiplier_graph
  intro n
  have he := physicalSectorMultiplier_action freeEnergySymbol u n
  have hrep : freeFourierRepresentation ((δ:ℂ) • freeHamiltonian u+(C:ℂ) • u.val) n =
      (δ:ℂ) • freeFourierRepresentation (freeHamiltonian u) n+(C:ℂ) • freeFourierRepresentation u.val n := by
    rw [map_add,map_smul,map_smul]
    rfl
  rw [hrep]
  filter_upwards [he,Lp.coeFn_add ((δ:ℂ) • freeFourierRepresentation (freeHamiltonian u) n)
      ((C:ℂ) • freeFourierRepresentation u.val n),
    Lp.coeFn_smul (δ:ℂ) (freeFourierRepresentation (freeHamiltonian u) n),
    Lp.coeFn_smul (C:ℂ) (freeFourierRepresentation u.val n)] with q hE hsum hδ hC
  rw [hsum]
  simp only [Pi.add_apply]
  rw [hδ,hC]
  simp only [Pi.smul_apply]
  rw [Complex.ofReal_add,Complex.ofReal_mul,add_smul,mul_smul,hE]
  rfl

lemma constructionShiftedRootBound (δ : ℝ) (hδ : 0 < δ) (u : freeHamiltonian.domain) :
    ∃ hn : u.val ∈ (physicalShiftedNumberPower (1/2)).domain,
      ‖physicalShiftedNumberPower (1/2) ⟨u.val,hn⟩‖ ≤ δ*‖freeHamiltonian u‖+(1+1/(4*δ))*‖u.val‖ := by
  let C := 1+1/(4*δ)
  let T := physicalSectorMultiplier (fun n q => δ*freeEnergySymbol n q+C)
  have hg := constructionAffineGraph δ C u
  let v : T.domain := ⟨u.val,T.mem_domain_of_mem_graph hg⟩
  have hout : T v = (δ:ℂ) • freeHamiltonian u+(C:ℂ) • u.val :=
    T.mem_graph_snd_inj (T.mem_graph v) hg rfl
  have hpoint (n : ℕ) (q : GW.Space) : Real.sqrt ((n:ℝ)+1) ≤ δ*freeEnergySymbol n q+C := by
    have hn : (n:ℝ)+1 ≤ freeEnergySymbol n q+1 := by
      unfold freeEnergySymbol
      nlinarith [sq_nonneg ‖q‖]
    exact (Real.sqrt_le_sqrt hn).trans ((constructionSqrtBound δ (freeEnergySymbol n q) hδ
      (freeEnergySymbol_nonnegative n q)).trans_eq (by dsimp only [C]; ring))
  obtain ⟨hm,hb⟩ := physicalSectorMultiplier_domination (fun n _ => Real.sqrt ((n:ℝ)+1))
    (fun n q => δ*freeEnergySymbol n q+C) (fun _ => measurable_const) zero_le_one
    (fun n q => by
      rw [abs_of_nonneg (Real.sqrt_nonneg _),abs_of_nonneg (show 0 ≤ δ*freeEnergySymbol n q+C by
        have hE := freeEnergySymbol_nonnegative n q
        dsimp only [C]
        positivity),one_mul]
      exact hpoint n q) v
  have hnorm : ‖physicalSectorMultiplier (fun n q => δ*freeEnergySymbol n q+C) v‖ ≤
      δ*‖freeHamiltonian u‖+C*‖u.val‖ := by
    rw [hout]
    exact (norm_add_le _ _).trans (by
      rw [norm_smul,norm_smul,Complex.norm_real,Complex.norm_real,Real.norm_of_nonneg hδ.le,
        Real.norm_of_nonneg (show 0 ≤ C by dsimp [C]; positivity)])
  rw [physicalShiftedNumberHalf_eq_sectorMultiplier]
  refine ⟨?_,?_⟩
  · exact hm
  · have hb' := hb
    simp only [one_mul] at hb'
    exact hb'.trans hnorm

/- Source argument component Restriction01. -/
def constructionH0ToQ : freeHamiltonian.domain →ₗ[ℂ] FreeFormDomain where
  toFun u := show freeFormOperator.domain from ⟨u.val,freeHamiltonian_mem_form u⟩
  map_add' u v := Subtype.ext rfl
  map_smul' c u := Subtype.ext rfl

lemma constructionH0ToQ_value (u : freeHamiltonian.domain) :
    freeFormDomainInclusion (constructionH0ToQ u) = u.val := freeFormDomainInclusion_apply _

def constructionFieldRestriction (f : OneBoson) : freeHamiltonian.domain →ₗ[ℂ] Physical :=
  (uvFieldLinear f).toLinearMap.comp constructionH0ToQ

lemma constructionFieldRestriction_graph (f : OneBoson) (u : freeHamiltonian.domain) :
    (u.val,constructionFieldRestriction f u) ∈ (generalizedField (phaseMultiplicationKernel f)).graph := by
  have h := uvFieldLinear_graph f (constructionH0ToQ u)
  rwa [constructionH0ToQ_value] at h

lemma constructionFieldRestriction_symmetric (f : OneBoson) (u v : freeHamiltonian.domain) :
    ⟪constructionFieldRestriction f u,v.val⟫_ℂ = ⟪u.val,constructionFieldRestriction f v⟫_ℂ :=
  uvFormalAdjoint_graph_pairing _ _ (generalizedField_symmetric (phaseMultiplicationKernel f)) _ _ _ _
    (constructionFieldRestriction_graph f u) (constructionFieldRestriction_graph f v)

lemma constructionFieldRestriction_rootBound (f : OneBoson) (u : freeHamiltonian.domain)
    (hn : u.val ∈ (physicalShiftedNumberPower (1/2)).domain) :
    ‖constructionFieldRestriction f u‖ ≤ 2*‖f‖*‖physicalShiftedNumberPower (1/2) ⟨u.val,hn⟩‖ := by
  have h := grossFormFieldMap_bound f (grossFormRootMap (constructionH0ToQ u))
  have hi : fiberPhysicalRootInput (grossFormRootMap (constructionH0ToQ u)) = ⟨u.val,hn⟩ :=
    Subtype.ext ((grossFormRootMap_value _).trans (constructionH0ToQ_value u))
  rw [← fiberPhysicalRoot_norm,hi] at h
  exact h

/- Source argument component Finite02. -/
lemma constructionField_relative (f : OneBoson) (a : ℝ) (ha : 0 < a) (u : freeHamiltonian.domain) :
    ‖constructionFieldRestriction f u‖ ≤ a*‖freeHamiltonian u‖+(2*‖f‖+‖f‖^2/a)*‖u.val‖ := by
  let g := ‖f‖
  by_cases hg : g = 0
  · obtain ⟨hn,hb⟩ := constructionShiftedRootBound 1 (by norm_num) u
    have h := constructionFieldRestriction_rootBound f u hn
    change ‖constructionFieldRestriction f u‖ ≤ 2*g*_ at h
    rw [hg,mul_zero,zero_mul] at h
    exact h.trans (by positivity)
  · have hgpos : 0 < g := lt_of_le_of_ne (norm_nonneg f) (Ne.symm hg)
    let δ := a/(2*g)
    have hδ : 0 < δ := div_pos ha (mul_pos (by norm_num) hgpos)
    obtain ⟨hn,hroot⟩ := constructionShiftedRootBound δ hδ u
    have h := constructionFieldRestriction_rootBound f u hn
    have hmul := mul_le_mul_of_nonneg_left hroot (show 0 ≤ 2*g by positivity)
    have h₁ : 2*g*δ = a := by dsimp only [δ];field_simp
    have h₂ : 2*g*(1+1/(4*δ)) = 2*g+g^2/a := by
      dsimp only [δ]
      field_simp [ne_of_gt ha,ne_of_gt hgpos]
      <;> ring
    calc
      _ ≤ 2*g*(δ*‖freeHamiltonian u‖+(1+1/(4*δ))*‖u.val‖) := h.trans hmul
      _ = _ := by rw [mul_add,← mul_assoc,← mul_assoc,h₁,h₂]

def constructionCutoffHamiltonian (α L : ℝ) (hα : 0 ≤ α) (hL : 0 < L) : Physical →ₗ.[ℂ] Physical :=
  GW.Operators.perturbedOperator freeHamiltonian (constructionFieldRestriction (cutoffL2 α L hα hL))

lemma constructionCutoffHamiltonian_domain (α L : ℝ) (hα : 0 ≤ α) (hL : 0 < L) :
    (constructionCutoffHamiltonian α L hα hL).domain = freeHamiltonian.domain := rfl

lemma constructionCutoffHamiltonian_selfadjoint (α L : ℝ) (hα : 0 ≤ α) (hL : 0 < L) :
    GW.IsSelfAdjointOperator (constructionCutoffHamiltonian α L hα hL) := by
  let f := cutoffL2 α L hα hL
  exact (GW.Operators.kato_rellich freeHamiltonian freeHamiltonian_selfadjoint
    (constructionFieldRestriction f) (constructionFieldRestriction_symmetric f)
    (a := 1/4) (b := 2*‖f‖+‖f‖^2/(1/4)) (by norm_num) (by norm_num) (by positivity)
    (constructionField_relative f (1/4) (by norm_num))).1

/- Source argument component Error04. -/
lemma constructionTailDifference (α R L M : ℝ) (hα : 0 ≤ α) (hR : 0 < R) (hL : R ≤ L) (hM : R ≤ M) :
    |coefficientDTail α L-coefficientDTail α M| ≤ coefficientDTail α R := by
  have h₁ := coefficientDTail_antitone α hα hR hL
  have h₂ := coefficientDTail_antitone α hα hR hM
  have hn₁ : 0 ≤ coefficientDTail α L := ENNReal.toReal_nonneg
  have hn₂ : 0 ≤ coefficientDTail α M := ENNReal.toReal_nonneg
  exact abs_le.mpr ⟨by linarith,by linarith⟩

def constructionError (α R : ℝ) : ℝ := 2*Real.sqrt (coefficientDTail α R)

lemma constructionError_nonneg (α R : ℝ) : 0 ≤ constructionError α R := mul_nonneg (by norm_num) (Real.sqrt_nonneg _)

lemma constructionError_tendsto (α : ℝ) (hα : 0 ≤ α) : Tendsto (constructionError α) atTop (𝓝 0) := by
  change Tendsto (fun R : ℝ => 2*Real.sqrt (coefficientDTail α R)) atTop (𝓝 0)
  have h := ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (2:ℝ)) atTop (𝓝 2)).mul (Real.continuous_sqrt.continuousAt.tendsto.comp (coefficientDTail_tendsto α hα)))
  simpa only [constructionError,Function.comp_def,Real.sqrt_zero,mul_zero] using h

lemma constructionDifference_bound (α R : ℝ) (hα : 0 ≤ α) (hR : 0 < R)
    (L M : GW.Operators.PositiveCutoff) (hL : R ≤ L.val) (hM : R ≤ M.val) (u : FreeFormDomain) :
    ‖(uvCutoffForm α L.val hα L.property-uvCutoffForm α M.val hα M.property) u u‖ ≤ constructionError α R*‖u‖^2 := by
  have h := main_uv_form_bound α L.val M.val hα L.property M.property u u
  change ‖uvCutoffForm α L.val hα L.property u u-uvCutoffForm α M.val hα M.property u u‖ ≤ _
  apply h.trans
  have hs := Real.sqrt_le_sqrt (constructionTailDifference α R L.val M.val hα hR hL hM)
  have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by norm_num : (0:ℝ) ≤ 2)) (sq_nonneg ‖u‖)
  dsimp only [constructionError]
  nlinarith

/- Source argument component Data01. -/
def constructionUniformData (α : ℝ) (hα : 0 ≤ α) : GW.Operators.UniformFormData FreeFormDomain Physical where
  embedding := freeFormDomainInclusion
  embedding_injective := freeFormWeightedGraph.embedding_injective.comp (GW.Spaces.weightedDomainIsometry freeFormWeightedGraph).injective
  embedding_dense := freeFormDomainInclusion_dense
  base := uniformBaseForm
  base_hermitian := uniformBaseForm_hermitian
  base_continuous := uniformBaseForm_continuous
  base_nonnegative := uniformBaseForm_nonneg
  energy_identity := uniformBaseForm_norm
  perturbation := fun L => uvCutoffForm α L.val hα L.property
  perturbation_hermitian := fun L u v => uvFieldForm_hermitian (cutoffL2 α L.val hα L.property) u v
  relative := 1/2
  relative_nonnegative := by norm_num
  relative_small := by norm_num
  remainder := uniformFormConstant α (1/2)
  remainder_nonnegative := uniformFormConstant_nonneg α (1/2) hα (by norm_num)
  diagonal_bound := by
    intro L u
    rw [uniformBaseForm_energy]
    exact main_uniform_form_bound α (1/2) L.val hα (by norm_num) L.property u
  error := constructionError α
  error_nonnegative := fun R _ => constructionError_nonneg α R
  error_tendsto := constructionError_tendsto α hα
  difference_bound := fun R hR L M hL hM u => constructionDifference_bound α R hα hR L M hL hM u

/- Source argument component Closed03. -/
def constructionLimitForm (α : ℝ) (hα : 0 ≤ α) : BoundedForm FreeFormDomain :=
  GW.Operators.uniformLimitForm (constructionUniformData α hα)

lemma constructionLimitForm_hermitian (α : ℝ) (hα : 0 ≤ α) (u w : FreeFormDomain) :
    constructionLimitForm α hα u w = star (constructionLimitForm α hα w u) :=
  GW.Operators.uniformLimitForm_hermitian (constructionUniformData α hα) u w

lemma constructionLimitForm_bound (α : ℝ) (hα : 0 ≤ α) (u : FreeFormDomain) :
    ‖constructionLimitForm α hα u u‖ ≤ (1/2)*uniformFreeEnergy u+uniformFormConstant α (1/2)*‖freeFormDomainInclusion u‖^2 := by
  have h := GW.Operators.uniformLimitForm_diagonal (constructionUniformData α hα) u
  change ‖constructionLimitForm α hα u u‖ ≤ (1/2)*(uniformBaseForm u u).re+uniformFormConstant α (1/2)*‖freeFormDomainInclusion u‖^2 at h
  rwa [uniformBaseForm_energy] at h

def constructionClosedData (α : ℝ) (hα : 0 ≤ α) (i : Option GW.Operators.PositiveCutoff) :
    GW.Operators.CoerciveFormData FreeFormDomain Physical :=
  GW.Operators.uniformClosedData (constructionUniformData α hα) i

def constructionHamiltonian (α : ℝ) (hα : 0 ≤ α) : Physical →ₗ.[ℂ] Physical :=
  GW.Operators.formOperator (constructionClosedData α hα none)

lemma constructionHamiltonian_selfadjoint (α : ℝ) (hα : 0 ≤ α) :
    GW.IsSelfAdjointOperator (constructionHamiltonian α hα) :=
  GW.Operators.formOperator_selfadjoint (constructionClosedData α hα none)

lemma constructionHamiltonian_lower_bound (α : ℝ) (hα : 0 ≤ α)
    (u : (constructionHamiltonian α hα).domain) :
    -(uniformFormConstant α (1/2)+1)*‖u.val‖^2 ≤ (⟪u.val,constructionHamiltonian α hα u⟫_ℂ).re :=
  GW.Operators.uniform_representing_bounded_below (constructionUniformData α hα) none u

lemma constructionLimit_formDomain (α : ℝ) (hα : 0 ≤ α) :
    Set.range (GW.Operators.completedEnergyEmbedding (constructionClosedData α hα none)) =
      (freeFormOperator.domain : Set Physical) := by
  rw [GW.Operators.completedEnergyEmbedding_range]
  exact freeFormDomainInclusion_range

lemma constructionLimit_complete (α : ℝ) (hα : 0 ≤ α) :
    CompleteSpace (GW.Operators.EnergySpace (constructionClosedData α hα none)) :=
  GW.Operators.uniform_closed_complete (constructionUniformData α hα) none

/- Source argument component Pair01. -/
lemma constructionH0ToQ_canonical (u : freeHamiltonian.domain) :
    freeCanonicalFormEquiv.symm (constructionH0ToQ u) =
      ((GW.Operators.canonicalCoordinates freeNonnegativeData).symm u : GW.Operators.CanonicalEnergySpace freeNonnegativeData) := by
  apply GW.Operators.canonicalEmbedding_injective freeNonnegativeData
  rw [uniformCanonicalEmbedding,constructionH0ToQ_value,GW.Operators.canonicalEmbedding_coe]
  rfl

lemma constructionBase_on_H0 (u : freeHamiltonian.domain) (v : FreeFormDomain) :
    uniformBaseForm v (constructionH0ToQ u) = ⟪freeFormDomainInclusion v,freeHamiltonian u⟫_ℂ := by
  rw [uniformBaseForm_canonical,constructionH0ToQ_canonical,GW.Operators.canonicalForm_on_domain,
    uniformCanonicalEmbedding]
  rfl

lemma constructionField_on_H0 (f : OneBoson) (u : freeHamiltonian.domain) (v : FreeFormDomain) :
    uvFieldForm f v (constructionH0ToQ u) = ⟪freeFormDomainInclusion v,constructionFieldRestriction f u⟫_ℂ := rfl

/- Source argument component Representative02. -/
lemma constructionFinite_representative (α L : ℝ) (hα : 0 ≤ α) (hL : 0 < L) :
    constructionCutoffHamiltonian α L hα hL =
      GW.Operators.formOperator (constructionClosedData α hα (some ⟨L,hL⟩)) := by
  apply GW.Operators.formOperator_unique _ _ (constructionCutoffHamiltonian_selfadjoint α L hα hL)
  intro x
  let u : freeHamiltonian.domain := ⟨x.val,x.property⟩
  refine ⟨constructionH0ToQ u,constructionH0ToQ_value u,?_⟩
  intro v
  change GW.Operators.uniformTotalForm (constructionUniformData α hα) (some ⟨L,hL⟩) v (constructionH0ToQ u) = _
  rw [GW.Operators.uniformTotalForm_some]
  change uniformBaseForm v (constructionH0ToQ u)+uvFieldForm (cutoffL2 α L hα hL) v (constructionH0ToQ u) =
    ⟪freeFormDomainInclusion v,freeHamiltonian u+constructionFieldRestriction (cutoffL2 α L hα hL) u⟫_ℂ
  rw [constructionBase_on_H0,constructionField_on_H0,inner_add_right]

lemma constructionFinite_representative_domain (α L : ℝ) (hα : 0 ≤ α) (hL : 0 < L) :
    (GW.Operators.formOperator (constructionClosedData α hα (some ⟨L,hL⟩))).domain = freeHamiltonian.domain := by
  rw [← constructionFinite_representative]
  rfl

/- Source argument component Convergence02. -/
lemma constructionBoundedCutoff_source (α : ℝ) (hα : 0 ≤ α) (L : GW.Operators.PositiveCutoff) :
    GW.Operators.uniformBoundedForm (constructionUniformData α hα) L = uvCutoffBoundedForm α L.val hα L.property := by
  ext u w
  exact GW.Operators.uniformBoundedForm_source (constructionUniformData α hα) L u w

lemma constructionBoundedCutoff_tendsto (α : ℝ) (hα : 0 ≤ α) :
    Tendsto (fun L : GW.Operators.PositiveCutoff => uvCutoffBoundedForm α L.val hα L.property)
      atTop (𝓝 (constructionLimitForm α hα)) := by
  have h := GW.Operators.uniformLimitForm_tendsto (constructionUniformData α hα)
  have hf : GW.Operators.uniformBoundedForm (constructionUniformData α hα) =
      (fun L : GW.Operators.PositiveCutoff => uvCutoffBoundedForm α L.val hα L.property) :=
    funext (constructionBoundedCutoff_source α hα)
  rw [hf] at h
  exact h

lemma constructionCutoff_pairing_tendsto (α : ℝ) (hα : 0 ≤ α) (u w : FreeFormDomain) :
    Tendsto (fun L : GW.Operators.PositiveCutoff => uvCutoffForm α L.val hα L.property u w)
      atTop (𝓝 (constructionLimitForm α hα u w)) := by
  have heval : Continuous (fun b : BoundedForm FreeFormDomain => b u w) :=
    (ContinuousLinearMap.apply ℂ ℂ w).continuous.comp
      (ContinuousLinearMap.apply' (FreeFormDomain →L[ℂ] ℂ) (starRingEnd ℂ) u).continuous
  exact (heval.tendsto _).comp (constructionBoundedCutoff_tendsto α hα)

def constructionRealCutoff (L : ℝ) : GW.Operators.PositiveCutoff :=
  ⟨max 1 L,zero_lt_one.trans_le (le_max_left _ _)⟩

lemma constructionRealCutoff_tendsto : Tendsto constructionRealCutoff atTop atTop := by
  apply tendsto_atTop.mpr
  intro L
  exact eventually_atTop.mpr ⟨L.val,fun R hR => show L.val ≤ max 1 R from hR.trans (le_max_right _ _)⟩

lemma constructionReal_boundedForm_tendsto (α : ℝ) (hα : 0 ≤ α) :
    Tendsto (fun L : ℝ => uvCutoffBoundedForm α (constructionRealCutoff L).val hα (constructionRealCutoff L).property)
      atTop (𝓝 (constructionLimitForm α hα)) :=
  (constructionBoundedCutoff_tendsto α hα).comp constructionRealCutoff_tendsto

lemma constructionReal_pairing_tendsto (α : ℝ) (hα : 0 ≤ α) (u w : FreeFormDomain) :
    Tendsto (fun L : ℝ => uvCutoffForm α (constructionRealCutoff L).val hα (constructionRealCutoff L).property u w)
      atTop (𝓝 (constructionLimitForm α hα u w)) :=
  (constructionCutoff_pairing_tendsto α hα u w).comp constructionRealCutoff_tendsto

lemma constructionRealCutoff_eventually : ∀ᶠ L : ℝ in atTop, (constructionRealCutoff L).val = L := by
  exact eventually_atTop.mpr ⟨1,fun L hL => max_eq_right hL⟩

/- Source argument component Zero02. -/
lemma constructionCutoffForm_zero (L : ℝ) (hL : 0 < L) : uvCutoffBoundedForm 0 L le_rfl hL = 0 := by
  ext u w
  rw [uvCutoffBoundedForm_apply]
  change ⟪freeFormDomainInclusion u,grossFormFieldMap (cutoffL2 0 L le_rfl hL) (grossFormRootMap w)⟫_ℂ = 0
  rw [cutoffL2_zero_coupling,grossFormFieldMap_zero,inner_zero_right]

lemma constructionLimitForm_zero : constructionLimitForm 0 le_rfl = 0 := by
  apply tendsto_nhds_unique (constructionBoundedCutoff_tendsto 0 le_rfl)
  have h : (fun L : GW.Operators.PositiveCutoff => uvCutoffBoundedForm 0 L.val le_rfl L.property) = fun _ => 0 :=
    funext (fun L => constructionCutoffForm_zero L.val L.property)
  rw [h]
  exact tendsto_const_nhds

lemma constructionHamiltonian_zero : constructionHamiltonian 0 le_rfl = freeHamiltonian := by
  symm
  apply GW.Operators.formOperator_unique _ _ freeHamiltonian_selfadjoint
  intro u
  refine ⟨constructionH0ToQ u,constructionH0ToQ_value u,?_⟩
  intro v
  change GW.Operators.uniformTotalForm (constructionUniformData 0 le_rfl) none v (constructionH0ToQ u) = _
  rw [GW.Operators.uniformTotalForm_none]
  change uniformBaseForm v (constructionH0ToQ u)+constructionLimitForm 0 le_rfl v (constructionH0ToQ u) = _
  have hz : constructionLimitForm 0 le_rfl v (constructionH0ToQ u) = 0 := by rw [constructionLimitForm_zero];rfl
  rw [hz,add_zero,constructionBase_on_H0]
  rfl

/- Source argument component FormProperties02. -/
def constructionTotalLimitForm (α : ℝ) (hα : 0 ≤ α) : GW.Operators.AlgebraicForm FreeFormDomain :=
  (constructionClosedData α hα none).form

lemma constructionTotalLimitForm_apply (α : ℝ) (hα : 0 ≤ α) (u w : FreeFormDomain) :
    constructionTotalLimitForm α hα u w = uniformBaseForm u w+constructionLimitForm α hα u w := rfl

lemma constructionTotalLimitForm_hermitian (α : ℝ) (hα : 0 ≤ α) (u w : FreeFormDomain) :
    constructionTotalLimitForm α hα u w = star (constructionTotalLimitForm α hα w u) :=
  (constructionClosedData α hα none).hermitian u w

lemma constructionTotalLimitForm_lower (α : ℝ) (hα : 0 ≤ α) (u : FreeFormDomain) :
    -(uniformFormConstant α (1/2)+1)*‖freeFormDomainInclusion u‖^2 ≤ (constructionTotalLimitForm α hα u u).re := by
  have h := (GW.Operators.uniform_shift_bounds (constructionUniformData α hα) none u).1
  change (1-(1/2:ℝ))*‖u‖^2 ≤ (constructionTotalLimitForm α hα u u).re+(uniformFormConstant α (1/2)+1)*‖freeFormDomainInclusion u‖^2 at h
  nlinarith [sq_nonneg ‖u‖]

lemma constructionTotalLimitForm_shift_bounds (α : ℝ) (hα : 0 ≤ α) (u : FreeFormDomain) :
    (1-(1/2:ℝ))*‖u‖^2 ≤ (constructionTotalLimitForm α hα u u).re+(uniformFormConstant α (1/2)+1)*‖freeFormDomainInclusion u‖^2 ∧
    (constructionTotalLimitForm α hα u u).re+(uniformFormConstant α (1/2)+1)*‖freeFormDomainInclusion u‖^2 ≤
      (2+(1/2:ℝ)+2*uniformFormConstant α (1/2))*‖u‖^2 :=
  GW.Operators.uniform_shift_bounds (constructionUniformData α hα) none u

lemma constructionLimit_domain_intersection (α : ℝ) (hα : 0 ≤ α) :
    Set.range (GW.Operators.completedEnergyEmbedding (constructionClosedData α hα none)) =
      (freeMomentumModulus.domain : Set Physical) ∩ ((physicalNumberPower (1/2)).domain : Set Physical) := by
  rw [constructionLimit_formDomain,freeForm_domain_intersection]
  rfl

lemma constructionHamiltonian_form (α : ℝ) (hα : 0 ≤ α) (x : (constructionHamiltonian α hα).domain) :
    ∃ u : FreeFormDomain, freeFormDomainInclusion u = x.val ∧
      ∀ v, constructionTotalLimitForm α hα v u = ⟪freeFormDomainInclusion v,constructionHamiltonian α hα x⟫_ℂ := by
  let d := constructionClosedData α hα none
  let y : (GW.Operators.formOperator d).domain := x
  let u : FreeFormDomain := GW.Operators.operatorFormCoordinate d y
  have he : d.embedding u = y.val := GW.Operators.operatorFormCoordinate_embedding d y
  have hf : ∀ v, d.form v u = ⟪d.embedding v,GW.Operators.formOperator d y⟫_ℂ :=
    GW.Operators.formOperator_form_identity d y
  exact ⟨u,he,hf⟩

lemma constructionHamiltonian_unique (α : ℝ) (hα : 0 ≤ α) (T : Physical →ₗ.[ℂ] Physical)
    (hT : GW.IsSelfAdjointOperator T)
    (hform : ∀ x : T.domain, ∃ u : FreeFormDomain, freeFormDomainInclusion u = x.val ∧
      ∀ v, constructionTotalLimitForm α hα v u = ⟪freeFormDomainInclusion v,T x⟫_ℂ) :
    T = constructionHamiltonian α hα :=
  GW.Operators.formOperator_unique (constructionClosedData α hα none) T hT hform

/- Source argument component Public01. -/
lemma constructionCutoff_original (α L : ℝ) (hα : 0 ≤ α) (hL : 0 < L) (u : freeHamiltonian.domain) :
    ∃ a : (generalizedField (grossCutoffKernel α L hα hL)).domain, a.val = u.val ∧
      constructionCutoffHamiltonian α L hα hL u = freeHamiltonian u+generalizedField (grossCutoffKernel α L hα hL) a := by
  obtain ⟨a,ha,hout⟩ := (generalizedField (grossCutoffKernel α L hα hL)).mem_graph_iff.mp
    (constructionFieldRestriction_graph (cutoffL2 α L hα hL) u)
  exact ⟨a,ha,congrArg (fun z : Physical => freeHamiltonian u+z) hout.symm⟩

lemma constructionLimit_exists_unique_operator (α : ℝ) (hα : 0 ≤ α) :
    ∃! T : Physical →ₗ.[ℂ] Physical, GW.IsSelfAdjointOperator T ∧
      ∀ x : T.domain, ∃ u : FreeFormDomain, freeFormDomainInclusion u = x.val ∧
        ∀ v, constructionTotalLimitForm α hα v u = ⟪freeFormDomainInclusion v,T x⟫_ℂ := by
  refine ⟨constructionHamiltonian α hα,⟨constructionHamiltonian_selfadjoint α hα,constructionHamiltonian_form α hα⟩,?_⟩
  intro T hT
  exact constructionHamiltonian_unique α hα T hT.1 hT.2

lemma main_form_H (α : ℝ) (hα : 0 ≤ α) :
    (∀ (L : ℝ) (hL : 0 < L), GW.IsSelfAdjointOperator (constructionCutoffHamiltonian α L hα hL) ∧
      (constructionCutoffHamiltonian α L hα hL).domain = freeHamiltonian.domain) ∧
    (∀ u w : FreeFormDomain, constructionLimitForm α hα u w = star (constructionLimitForm α hα w u)) ∧
    Tendsto (fun L : ℝ => uvCutoffBoundedForm α (constructionRealCutoff L).val hα (constructionRealCutoff L).property)
      atTop (𝓝 (constructionLimitForm α hα)) ∧
    DenseRange freeFormDomainInclusion ∧
    CompleteSpace (GW.Operators.EnergySpace (constructionClosedData α hα none)) ∧
    Set.range (GW.Operators.completedEnergyEmbedding (constructionClosedData α hα none)) =
      (freeMomentumModulus.domain : Set Physical) ∩ ((physicalNumberPower (1/2)).domain : Set Physical) ∧
    GW.IsSelfAdjointOperator (constructionHamiltonian α hα) ∧
    (∀ u : (constructionHamiltonian α hα).domain,
      -(uniformFormConstant α (1/2)+1)*‖u.val‖^2 ≤ (⟪u.val,constructionHamiltonian α hα u⟫_ℂ).re) :=
  ⟨fun L hL => ⟨constructionCutoffHamiltonian_selfadjoint α L hα hL,rfl⟩,
    constructionLimitForm_hermitian α hα,constructionReal_boundedForm_tendsto α hα,
    freeFormDomainInclusion_dense,constructionLimit_complete α hα,
    constructionLimit_domain_intersection α hα,constructionHamiltonian_selfadjoint α hα,
    constructionHamiltonian_lower_bound α hα⟩

end GW.Gross
