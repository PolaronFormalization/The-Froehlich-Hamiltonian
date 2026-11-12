module
public import GW.Model.ModelFrohlichEstimates
public import GW.Fock.FockGeneralizedBounds
@[expose] public section
noncomputable section
open Filter
open scoped Topology
namespace GW.Gross
open GW.Model GW.Fock

lemma grossTails_finite (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) :
    coefficientDTailENN α K ≠ ⊤ ∧ coefficientETailENN α K ≠ ⊤ ∧
      BddAbove (Set.range (coefficientConvolution α K)) ∧
      (∀ q, coefficientConvolutionENN α K q ≠ ⊤) :=
  ⟨coefficientDTailENN_finite α K hα hK, coefficientETailENN_finite α K hα hK,
    coefficientConvolution_range_bddAbove α K hα hK, coefficientConvolutionENN_finite α K hα hK⟩

lemma grossTails_tendsto (α : ℝ) (hα : 0 ≤ α) :
    Tendsto (coefficientDTail α) atTop (𝓝 0) ∧
    Tendsto (coefficientETail α) atTop (𝓝 0) ∧
    Tendsto (coefficientTTail α) atTop (𝓝 0) :=
  ⟨coefficientDTail_tendsto α hα, coefficientETail_tendsto α hα, coefficientTTail_tendsto α hα⟩

def grossCutoffKernel (α L : ℝ) (hα : 0 ≤ α) (hL : 0 < L) : BosonKernel ElectronL2 :=
  phaseMultiplicationKernel (cutoffL2 α L hα hL)

lemma grossCutoffKernel_action_norm (α L : ℝ) (hα : 0 ≤ α) (hL : 0 < L) (u : ElectronL2) :
    ‖grossCutoffKernel α L hα hL u‖ = ‖cutoffL2 α L hα hL‖ * ‖u‖ :=
  phaseMultiplicationKernel_apply_norm _ _

lemma grossCutoffKernel_norm (α L : ℝ) (hα : 0 ≤ α) (hL : 0 < L) :
    ‖grossCutoffKernel α L hα hL‖ = ‖cutoffL2 α L hα hL‖ :=
  phaseMultiplicationKernel_norm _

lemma grossCutoffKernel_bound (α L : ℝ) (hα : 0 ≤ α) (hL : 0 < L) :
    ‖grossCutoffKernel α L hα hL‖ ≤ Real.sqrt (7*unitBallVolume*α*L) := by
  rw [grossCutoffKernel_norm]
  calc
    _ = Real.sqrt (‖cutoffL2 α L hα hL‖^2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ _ := Real.sqrt_le_sqrt (cutoffL2_norm_sq α L hα hL)

end GW.Gross
