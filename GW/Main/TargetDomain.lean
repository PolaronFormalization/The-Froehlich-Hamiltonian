module
public import GW.Gross.MainDomain
@[expose] public section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal BigOperators
namespace GW.Main
open GW.Model GW.Fock GW.Analysis GW.Gross

/-- Frozen target:domain, manuscript196–231, with original products and full domains. -/
lemma domain (α : ℝ) (hα : 0 ≤ α) :
    let K0 := standardGrossCutoff α
    0 < K0 ∧ ∀ (K : ℝ) (hKS : K0 ≤ K),
      let hK : 0 < K := dressed_standard_cutoff_pos α K hα hKS
      let f := grossDressingCoefficient α K hα hK
      let fs := derivativeCoefficient α K hα hK
      (f =ᵐ[volume] fun k => (b α K k : ℂ)) ∧
      (∀ Ψ : Physical, domainGrossUnitary α K hα hK Ψ =ᵐ[volume]
        fun x => weylUnitary (-phaseAt f x) (Ψ x)) ∧
      (∀ f g : OneBoson, weylUnitary f (exponentialVector g) =
        Complex.exp (-((‖f‖^2:ℝ):ℂ)/2-⟪f,g⟫_ℂ) • exponentialVector (g+f)) ∧
      (∀ u : freeHamiltonian.domain,
        dressedInfiniteHamiltonian α K hα hK u = freeHamiltonian u+
          (constructionFieldRestriction (cutoffL2 α K hα hK) u+dressedInfiniteRemainder α K hα hK u)) ∧
      (∀ u : freeHamiltonian.domain, dressedInfiniteRemainder α K hα hK u =
        -(2 • (∑ j : Fin 3,commutatorPhaseCreatorMap (fs j)
          (commutatorGraphMomentumRootMap j (conjugationSourceGraph u))))-
        2 • derivativeInfiniteDot α K hα hK (conjugationSourceGraph u)+
        (∑ j : Fin 3,conjugationSquareMap (fs j) u)+(dressedInfiniteCounterterm α K : ℂ) • u.val) ∧
      dressedInfiniteCounterterm α K = ∫ k in highRegion K,
        (v α k)^2*(1/(1+‖k‖^2)^2-2/(1+‖k‖^2)) ∂volume ∧
      (∀ (u : freeHamiltonian.domain) (j : Fin 3),
        let U := commutatorSourceGraphInput u
        (u.val,commutatorPhaseAnnihilatorMap (fs j) (commutatorGraphRootMap U)) ∈
          (generalizedAnnihilation (phaseMultiplicationKernel (fs j))).graph ∧
        (commutatorPhaseAnnihilatorMap (fs j) (commutatorGraphRootMap U),
          commutatorPhaseAnnihilatorMap (fs j) (commutatorGraphMomentumRootMap j U)+derivativeSingularMap α K hα hK j U) ∈
            (electronMomentumCoordinate j).graph ∧
        (electronMomentumCoordinate j (commutatorMomentumInput U j),
          commutatorPhaseCreatorMap (fs j) (commutatorGraphMomentumRootMap j U)) ∈
            (generalizedCreation (phaseMultiplicationKernel (fs j))).graph ∧
        (u.val,constructionFieldRestriction (fs j) u) ∈ (generalizedField (phaseMultiplicationKernel (fs j))).graph ∧
        (constructionFieldRestriction (fs j) u,conjugationSquareMap (fs j) u) ∈
          (generalizedField (phaseMultiplicationKernel (fs j))).graph) ∧
      GW.IsSelfAdjointOperator (dressedInfiniteHamiltonian α K hα hK) ∧
      (dressedInfiniteHamiltonian α K hα hK).domain = freeHamiltonian.domain ∧
      (∀ u : freeHamiltonian.domain,
        ‖u.val‖+‖dressedInfiniteHamiltonian α K hα hK u‖ ≤
          (2+(3/8:ℝ)+dressedGraphConstant α K hα hK)*(‖u.val‖+‖freeHamiltonian u‖) ∧
        ‖u.val‖+‖freeHamiltonian u‖ ≤
          (1+(1+dressedGraphConstant α K hα hK)/(1-(3/8:ℝ)))*
            (‖u.val‖+‖dressedInfiniteHamiltonian α K hα hK u‖)) ∧
      (∀ (adj : Bool) (u : FreeFormDomain),
        freeFormDomainInclusion (grossSourceQInput adj α K hα hK u) = grossWeylSide adj f (freeFormDomainInclusion u) ∧
        ‖grossSourceQInput adj α K hα hK u‖ ≤ grossSourceL α K hα hK*‖u‖) ∧
      constructionHamiltonian α hα =
        GW.Operators.unitaryTransport (domainGrossUnitary α K hα hK) (dressedInfiniteHamiltonian α K hα hK) ∧
      (constructionHamiltonian α hα).domain =
        freeHamiltonian.domain.map (domainGrossUnitary α K hα hK).symm.toLinearMap ∧
      (∀ (L : ℝ) (hLS : K0 ≤ L),
        let hL : 0 < L := dressed_standard_cutoff_pos α L hα hLS
        GW.Operators.unitaryTransport (domainGrossUnitary α K hα hK) (dressedInfiniteHamiltonian α K hα hK) =
          GW.Operators.unitaryTransport (domainGrossUnitary α L hα hL) (dressedInfiniteHamiltonian α L hα hL)) := by
  dsimp only
  refine ⟨zero_lt_one.trans_le (operatorCutoffWitness_ge_one α (1/8) hα),?_⟩
  intro K hKS
  let hK : 0 < K := dressed_standard_cutoff_pos α K hα hKS
  refine ⟨grossDressingCoefficient_ae α K hα hK,?_,?_,?_,dressedInfiniteRemainder_value α K hα hK,?_,?_,
    dressedInfiniteHamiltonian_selfadjoint α K hα hK hKS,rfl,
    dressedInfiniteHamiltonian_graph_bounds α K hα hK hKS,?_,
    domainHamiltonian_operator α K hα hK hKS,domainHamiltonian_domain α K hα hK hKS,?_⟩
  · exact grossWeylSide_unitary_ae _
  · exact weylUnitary_exponential
  · intro u; rfl
  · exact integral_indicator (highRegion_measurable K)
  · intro u j
    refine ⟨derivative_source_annihilator_graph _ u,
      derivative_infinite_component_graph α K hα hK j (commutatorSourceGraphInput u),?_,
      constructionFieldRestriction_graph _ u,conjugationSquareMap_graph _ u⟩
    have hg := commutatorPhaseCreatorMap_graph (derivativeCoefficient α K hα hK j)
      (commutatorGraphMomentumRootMap j (commutatorSourceGraphInput u))
    rw [commutatorGraphMomentumRootMap_value] at hg
    exact hg
  · intro adj u
    exact ⟨grossFormSideInput_value adj _ _ _ u,main_gross_infinite_form_bound adj α K hα hK u⟩
  · intro L hLS
    exact domainHamiltonian_independent α K L hα hK _ hKS hLS

end GW.Main
