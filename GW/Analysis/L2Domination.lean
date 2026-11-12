module

public import GW.Analysis.L2Quotient
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Source bridge:l2-domination, lines 8171–8211. The integrable majorant
is the square 4*g². No separability of the entire value space is assumed. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace GW.Analysis
variable {X H : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup H]

/-- Source M106 selects a measurable limit; uniqueness identifies the intended function. -/
lemma l2_limit_measurable {fs : ℕ → X → H} {f : X → H}
    (hm : ∀ n, AEStronglyMeasurable (fs n) μ)
    (hl : ∀ᵐ x ∂μ, Tendsto (fun n => fs n x) atTop (𝓝 (f x))) :
    AEStronglyMeasurable f μ := by
  obtain ⟨g, hg, hlg⟩ := exists_stronglyMeasurable_limit_of_tendsto_ae hm
    (hl.mono (fun x hx => ⟨f x, hx⟩))
  apply hg.aestronglyMeasurable.congr
  filter_upwards [hl, hlg] with x hx hy
  exact tendsto_nhds_unique hy hx

/-- Membership is established before constructing any limit class. -/
lemma dominated_l2_membership {fs : ℕ → X → H} {f : X → H} {g : X → ℝ}
    (hm : ∀ n, AEStronglyMeasurable (fs n) μ)
    (hl : ∀ᵐ x ∂μ, Tendsto (fun n => fs n x) atTop (𝓝 (f x)))
    (hg : Measurable g) (hi : Integrable (fun x => g x ^ 2) μ)
    (hb : ∀ n, ∀ᵐ x ∂μ, ‖fs n x‖ ≤ g x) :
    (∀ n, MemLp (fs n) 2 μ) ∧ MemLp f 2 μ := by
  have hgLp : MemLp g 2 μ := (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).mpr hi
  have hbf : ∀ᵐ x ∂μ, ‖f x‖ ≤ g x := by
    filter_upwards [hl, ae_all_iff.mpr hb] with x hx hbx
    exact le_of_tendsto hx.norm (Eventually.of_forall hbx)
  constructor
  · intro n
    apply hgLp.of_le (hm n)
    filter_upwards [hb n] with x hx
    exact hx.trans (le_abs_self _)
  · apply hgLp.of_le (l2_limit_measurable hm hl)
    filter_upwards [hbf] with x hx
    exact hx.trans (le_abs_self _)

/-- The prescribed squared-error DCT proof, with already constructed L² classes. -/
lemma dominated_l2_convergence {𝕜 : Type*} [RCLike 𝕜] [InnerProductSpace 𝕜 H]
    {fs : ℕ → X → H} {f : X → H} {g : X → ℝ}
    (hm : ∀ n, AEStronglyMeasurable (fs n) μ)
    (hl : ∀ᵐ x ∂μ, Tendsto (fun n => fs n x) atTop (𝓝 (f x)))
    (hg : Measurable g) (hi : Integrable (fun x => g x ^ 2) μ)
    (hb : ∀ n, ∀ᵐ x ∂μ, ‖fs n x‖ ≤ g x) :
    ∃ (hs : ∀ n, MemLp (fs n) 2 μ) (hf : MemLp f 2 μ),
      Tendsto (fun n => ‖(hs n).toLp (fs n) - hf.toLp f‖) atTop (𝓝 0) := by
  obtain ⟨hs, hf⟩ := dominated_l2_membership hm hl hg hi hb
  refine ⟨hs, hf, ?_⟩
  have hbf : ∀ᵐ x ∂μ, ‖f x‖ ≤ g x := by
    filter_upwards [hl, ae_all_iff.mpr hb] with x hx hbx
    exact le_of_tendsto hx.norm (Eventually.of_forall hbx)
  have hbound : ∀ n, ∀ᵐ x ∂μ, ‖‖fs n x - f x‖ ^ 2‖ ≤ 4 * g x ^ 2 := by
    intro n
    filter_upwards [hb n, hbf] with x hn hfx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hg0 : 0 ≤ g x := (norm_nonneg _).trans hn
    have hdiff : ‖fs n x - f x‖ ≤ 2 * g x := by
      exact (norm_sub_le _ _).trans (by linarith)
    have hsq := mul_self_le_mul_self (norm_nonneg _) hdiff
    nlinarith
  have hsquare : Tendsto (fun n => ∫ x, ‖fs n x - f x‖ ^ 2 ∂μ) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (fun x => 4 * g x ^ 2)
      (fun n => ((hm n).sub hf.aestronglyMeasurable).norm.pow 2)
      (hi.const_mul 4) hbound (hl.mono (fun x hx => by
        simpa using ((hx.sub_const (f x)).norm.pow 2)))
    simpa using h
  have hnormsq : Tendsto (fun n => ‖(hs n).toLp (fs n) - hf.toLp f‖ ^ 2)
      atTop (𝓝 0) := by
    simpa only [l2_class_sub_norm_sq (𝕜 := 𝕜)] using hsquare
  have h := (Real.continuous_sqrt.tendsto 0).comp hnormsq
  simpa [Function.comp_def, Real.sqrt_sq_eq_abs] using h

end GW.Analysis
