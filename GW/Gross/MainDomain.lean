module
public import GW.Gross.MainDressedForm
public import GW.Operators.UnitaryFormTransport
/-! Source main:domain, manuscript6800–6853. Exact original Hamiltonian
operator and domain transport, cutoff independence and transported free cores. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal BigOperators
namespace GW.Gross
open GW.Model GW.Fock GW.Analysis

def domainGrossUnitary (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) : Physical ≃ₗᵢ[ℂ] Physical :=
  (grossWeylCoefficient (grossDressingCoefficient α K hα hK)).symm

def domainGrossForward (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) : FreeFormDomain →L[ℂ] FreeFormDomain :=
  grossFormWeylMap (-(grossDressingCoefficient α K hα hK))
    (fun j => grossForm_neg_momentum_memLp _ j (grossForm_momentum_memLp α K hα hK j))
    (grossForm_neg_even _ (grossForm_coefficient_even α K hα hK))
lemma domainGrossForward_value (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (v : FreeFormDomain) :
    freeFormDomainInclusion (domainGrossForward α K hα hK v) =
      domainGrossUnitary α K hα hK (freeFormDomainInclusion v) := by
  change _ = (grossWeylCoefficient (grossDressingCoefficient α K hα hK)).symm (freeFormDomainInclusion v)
  rw [grossWeylCoefficient_symm_apply]
  exact grossFormWeylMap_value _ _ _ v

def domainFormUnitaryData (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (hKS : standardGrossCutoff α ≤ K) :
    GW.Operators.FormUnitaryData (constructionClosedData α hα none) (dressedInfiniteClosedData α K hα hK hKS) where
  unitary := domainGrossUnitary α K hα hK
  common_embedding := rfl
  forward := domainGrossForward α K hα hK
  backward := dressedInfiniteQWeyl α K hα hK
  forward_embedding := domainGrossForward_value α K hα hK
  backward_embedding := by
    intro v
    change freeFormDomainInclusion (dressedInfiniteQWeyl α K hα hK v) =
      grossWeylCoefficient (grossDressingCoefficient α K hα hK) (freeFormDomainInclusion v)
    exact dressedInfiniteQWeyl_value α K hα hK v
  form_identity := by
    intro u v
    change dressedInfiniteForm α K hα hK u v =
      constructionTotalLimitForm α hα (grossSourceQInput true α K hα hK u) (grossSourceQInput true α K hα hK v)
    exact dressedInfiniteForm_transport α K hα hK u v

lemma domainHamiltonian_operator (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (hKS : standardGrossCutoff α ≤ K) :
    constructionHamiltonian α hα =
      GW.Operators.unitaryTransport (domainGrossUnitary α K hα hK) (dressedInfiniteHamiltonian α K hα hK) := by
  have h := GW.Operators.formUnitary_operator (domainFormUnitaryData α K hα hK hKS)
  change constructionHamiltonian α hα =
    GW.Operators.unitaryTransport (domainGrossUnitary α K hα hK)
      (GW.Operators.formOperator (dressedInfiniteClosedData α K hα hK hKS)) at h
  rw [← dressedInfiniteForm_representative α K hα hK hKS] at h
  exact h

lemma domainHamiltonian_domain (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (hKS : standardGrossCutoff α ≤ K) :
    (constructionHamiltonian α hα).domain =
      freeHamiltonian.domain.map (domainGrossUnitary α K hα hK).symm.toLinearMap := by
  rw [domainHamiltonian_operator α K hα hK hKS,GW.Operators.unitaryTransport_domain,
    dressedInfiniteHamiltonian_domain]

lemma domainHamiltonian_independent (α K L : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (hL : 0 < L)
    (hKS : standardGrossCutoff α ≤ K) (hLS : standardGrossCutoff α ≤ L) :
    GW.Operators.unitaryTransport (domainGrossUnitary α K hα hK) (dressedInfiniteHamiltonian α K hα hK) =
      GW.Operators.unitaryTransport (domainGrossUnitary α L hα hL) (dressedInfiniteHamiltonian α L hα hL) :=
  (domainHamiltonian_operator α K hα hK hKS).symm.trans (domainHamiltonian_operator α L hα hL hLS)

lemma domainHamiltonian_zero (K : ℝ) (hK : 0 < K) (hKS : standardGrossCutoff 0 ≤ K) :
    GW.Operators.unitaryTransport (domainGrossUnitary 0 K le_rfl hK) (dressedInfiniteHamiltonian 0 K le_rfl hK) =
      freeHamiltonian :=
  (domainHamiltonian_operator 0 K le_rfl hK hKS).symm.trans constructionHamiltonian_zero

lemma main_domain (α K : ℝ) (hα : 0 ≤ α) (hKS : standardGrossCutoff α ≤ K) :
    let hK : 0 < K := dressed_standard_cutoff_pos α K hα hKS
    constructionHamiltonian α hα =
      GW.Operators.unitaryTransport (domainGrossUnitary α K hα hK) (dressedInfiniteHamiltonian α K hα hK) ∧
    (constructionHamiltonian α hα).domain =
      freeHamiltonian.domain.map (domainGrossUnitary α K hα hK).symm.toLinearMap :=
  ⟨domainHamiltonian_operator α K hα _ hKS,domainHamiltonian_domain α K hα _ hKS⟩

lemma domainDressed_core (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (hKS : standardGrossCutoff α ≤ K) (C : Submodule ℂ Physical) (hC : freeHamiltonian.HasCore C) :
    (dressedInfiniteHamiltonian α K hα hK).HasCore C := by
  let V := dressedInfiniteRemainder α K hα hK
  have hv : ∀ u v : freeHamiltonian.domain, ⟪V u,v.val⟫_ℂ = ⟪u.val,V v⟫_ℂ :=
    dressedInfiniteRemainder_symmetric α K hα hK
  have hs : ∀ u v : freeHamiltonian.domain,
      ⟪(constructionFieldRestriction (cutoffL2 α K hα hK)+V) u,v.val⟫_ℂ =
        ⟪u.val,(constructionFieldRestriction (cutoffL2 α K hα hK)+V) v⟫_ℂ := by
    intro u v
    simp only [LinearMap.add_apply,inner_add_left,inner_add_right,
      constructionFieldRestriction_symmetric,hv]
  exact (GW.Operators.kato_rellich_core_iff freeHamiltonian freeHamiltonian_selfadjoint
    (constructionFieldRestriction (cutoffL2 α K hα hK)+V) hs
    (a := 3/8) (b := dressedGraphConstant α K hα hK) (by norm_num) (by norm_num)
    (dressedGraphConstant_nonneg α K hα hK)
    (dressed_uniform_perturbation_bound α K hα hK hKS V (dressedInfiniteRemainder_bound α K hα hK)) C).mp hC

lemma domainHamiltonian_core (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (hKS : standardGrossCutoff α ≤ K) (C : Submodule ℂ Physical) (hC : freeHamiltonian.HasCore C) :
    (constructionHamiltonian α hα).HasCore (C.map (domainGrossUnitary α K hα hK).symm.toLinearMap) := by
  rw [domainHamiltonian_operator α K hα hK hKS]
  have hc := domainDressed_core α K hα hK hKS C hC
  exact (GW.Operators.unitaryTransport_core_iff (domainGrossUnitary α K hα hK)
    (dressedInfiniteHamiltonian α K hα hK)
    (GW.Operators.selfadjoint_closed _ (dressedInfiniteHamiltonian_selfadjoint α K hα hK hKS)) C hc.le_domain).mp hc

end GW.Gross
