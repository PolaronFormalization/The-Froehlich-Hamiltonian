module
public import GW.Regularity.RegMainCorollary
@[expose] public section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators
namespace GW.Main
open GW.Fock GW.Gross GW.Analysis GW.Model GW.Regularity

/-- Frozen target:regularity, with the same original Hamiltonian and all real exponents. -/
lemma regularity (α : ℝ) (hα : 0 ≤ α) :
    ((constructionHamiltonian α hα).domain ≤ physicalNumberOperator.domain ⊓
      (⨅ (s : ℝ) (_ : 0 ≤ s) (_ : s < 3/2), (electronRadialPower s).domain : Submodule ℂ Physical)) ∧
    ((constructionHamiltonian α hα).domain ≤ physicalNumberOperator.domain ⊓
      (⨅ (t : ℝ) (_ : 0 ≤ t) (_ : t < 3/4), (electronLaplacianPower t).domain : Submodule ℂ Physical)) ∧
    (0 < α →
      ((constructionHamiltonian α hα).domain ⊓ (electronRadialPower (3/2)).domain = ⊥) ∧
      ((constructionHamiltonian α hα).domain ⊓ (electronLaplacianPower (3/4)).domain = ⊥) ∧
      ((constructionHamiltonian α hα).domain ⊓ freeMomentumSquare.domain = ⊥) ∧
      ((constructionHamiltonian α hα).domain ⊓ freeHamiltonian.domain = ⊥) ∧
      (∀ s : ℝ, 3/2 ≤ s → (constructionHamiltonian α hα).domain ⊓ (electronRadialPower s).domain = ⊥)) ∧
    (constructionHamiltonian 0 le_rfl = freeHamiltonian) ∧
    ((constructionHamiltonian 0 le_rfl).domain = freeHamiltonian.domain) ∧
    ((constructionHamiltonian 0 le_rfl).domain = freeMomentumSquare.domain ⊓ physicalNumberOperator.domain) ∧
    (electronRadialPower 0 = (LinearMap.id : Physical →ₗ[ℂ] Physical).toPMap ⊤) ∧
    (electronLaplacianPower 0 = (LinearMap.id : Physical →ₗ[ℂ] Physical).toPMap ⊤) := reg_main_corollary α hα

end GW.Main
