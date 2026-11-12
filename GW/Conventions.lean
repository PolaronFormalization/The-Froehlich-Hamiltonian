module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-! Fixed conventions from §3 of GW-paper-formalization.tex. -/
@[expose] public section

noncomputable section
namespace GW

/-- Physical position and both momentum variables use the Euclidean norm. -/
abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- Bochner L² with its specified measure. -/
abbrev L2 (X E : Type*) [MeasurableSpace X] [NormedAddCommGroup E]
    (μ : MeasureTheory.Measure X) := MeasureTheory.Lp E 2 μ

/-- The one-phonon Hilbert space. -/
abbrev OnePhonon := L2 Space ℂ MeasureTheory.volume

/-- Self-adjointness includes density, to exclude the adjoint fallback branch. -/
def IsSelfAdjointOperator {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (T : E →ₗ.[ℂ] E) : Prop :=
  Dense (T.domain : Set E) ∧ T.adjoint = T

end GW
