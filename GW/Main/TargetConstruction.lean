module
public import GW.Gross.MainFormH
@[expose] public section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal BigOperators
namespace GW.Main
open GW.Model GW.Fock GW.Analysis GW.Gross

/-- Frozen target:construction: original physical Hamiltonian, exact form domain,
real-cutoff bounded-form convergence, closed shifted form and zero coupling. -/
lemma construction (α : ℝ) (hα : 0 ≤ α) :
    Tendsto (fun L : ℝ => uvCutoffBoundedForm α (constructionRealCutoff L).val hα (constructionRealCutoff L).property)
      atTop (𝓝 (constructionLimitForm α hα)) ∧
    (∀ u w : FreeFormDomain, constructionTotalLimitForm α hα u w =
      uniformBaseForm u w+constructionLimitForm α hα u w) ∧
    (∀ u w : FreeFormDomain, constructionTotalLimitForm α hα u w = star (constructionTotalLimitForm α hα w u)) ∧
    DenseRange freeFormDomainInclusion ∧
    CompleteSpace (GW.Operators.EnergySpace (constructionClosedData α hα none)) ∧
    (∀ u : FreeFormDomain,
      (1-(1/2:ℝ))*‖u‖^2 ≤ (constructionTotalLimitForm α hα u u).re+(uniformFormConstant α (1/2)+1)*‖freeFormDomainInclusion u‖^2 ∧
      (constructionTotalLimitForm α hα u u).re+(uniformFormConstant α (1/2)+1)*‖freeFormDomainInclusion u‖^2 ≤
        (2+(1/2:ℝ)+2*uniformFormConstant α (1/2))*‖u‖^2) ∧
    Set.range (GW.Operators.completedEnergyEmbedding (constructionClosedData α hα none)) =
      (freeMomentumModulus.domain : Set Physical) ∩ ((physicalNumberPower (1/2)).domain : Set Physical) ∧
    (∀ u : FreeFormDomain, -(uniformFormConstant α (1/2)+1)*‖freeFormDomainInclusion u‖^2 ≤
      (constructionTotalLimitForm α hα u u).re) ∧
    (∃! T : Physical →ₗ.[ℂ] Physical, GW.IsSelfAdjointOperator T ∧
      (∀ x : T.domain, ∃ u : FreeFormDomain, freeFormDomainInclusion u = x.val ∧
        ∀ v, constructionTotalLimitForm α hα v u = ⟪freeFormDomainInclusion v,T x⟫_ℂ) ∧
      ∃ b : ℝ, ∀ x : T.domain, -b*‖x.val‖^2 ≤ (⟪x.val,T x⟫_ℂ).re) ∧
    constructionHamiltonian 0 le_rfl = freeHamiltonian := by
  refine ⟨constructionReal_boundedForm_tendsto α hα,constructionTotalLimitForm_apply α hα,
    constructionTotalLimitForm_hermitian α hα,freeFormDomainInclusion_dense,
    constructionLimit_complete α hα,constructionTotalLimitForm_shift_bounds α hα,
    constructionLimit_domain_intersection α hα,constructionTotalLimitForm_lower α hα,?_,constructionHamiltonian_zero⟩
  refine ⟨constructionHamiltonian α hα,⟨constructionHamiltonian_selfadjoint α hα,
    constructionHamiltonian_form α hα,uniformFormConstant α (1/2)+1,constructionHamiltonian_lower_bound α hα⟩,?_⟩
  intro T hT
  exact constructionHamiltonian_unique α hα T hT.1 hT.2.1

end GW.Main
