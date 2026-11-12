module

public import GW.Conventions
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Tactic

/-! Source basic:mixed-form-limits. The nested operator norm is the norm
of bounded sesquilinear forms; the first argument is conjugate-linear. -/
@[expose] public section
noncomputable section
namespace GW.Analysis
open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

abbrev BoundedForm (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] :=
  E →L⋆[ℂ] E →L[ℂ] ℂ

lemma form_bound (b : BoundedForm E) (u v : E) :
    ‖b u v‖ ≤ ‖b‖ * ‖u‖ * ‖v‖ := by
  exact (b u |>.le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (b.le_opNorm u) (norm_nonneg v))

/-- The nested operator norm is exactly the manuscript mixed-bound norm. -/
lemma form_norm_le_iff (b : BoundedForm E) {C : ℝ} (hC : 0 ≤ C) :
    ‖b‖ ≤ C ↔ ∀ u v : E, ‖b u v‖ ≤ C * ‖u‖ * ‖v‖ := by
  constructor
  · intro h u v
    exact (form_bound b u v).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right h (norm_nonneg u)) (norm_nonneg v))
  · intro h
    apply b.opNorm_le_bound hC
    intro u
    exact (b u).opNorm_le_bound (mul_nonneg hC (norm_nonneg u)) (h u)

lemma mixed_form_estimate (b₁ b : BoundedForm E) (u₁ u v₁ v : E) :
    ‖b₁ u₁ v₁ - b u v‖ ≤
      ‖b₁ - b‖ * ‖u₁‖ * ‖v₁‖ + ‖b‖ * ‖u₁ - u‖ * ‖v₁‖ +
      ‖b‖ * ‖u‖ * ‖v₁ - v‖ := by
  have heq : b₁ u₁ v₁ - b u v =
      (b₁ - b) u₁ v₁ + b (u₁ - u) v₁ + b u (v₁ - v) := by
    simp only [sub_apply, map_sub]
    ring
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add (form_bound _ _ _) (form_bound _ _ _)))
    (form_bound _ _ _))

lemma form_dense_determination (b c : BoundedForm E) (D : Set E) (hD : Dense D)
    (h : ∀ u ∈ D, ∀ v ∈ D, b u v = c u v) : b = c := by
  have heq : ∀ u ∈ closure D, ∀ v ∈ closure D, b u v = c u v := by
    apply eqOn_closure₂' h
    · intro u; exact (b u).continuous
    · intro v; exact (ContinuousLinearMap.apply ℂ ℂ v).continuous.comp b.continuous
    · intro u; exact (c u).continuous
    · intro v; exact (ContinuousLinearMap.apply ℂ ℂ v).continuous.comp c.continuous
  ext u v
  exact heq u (hD.closure_eq ▸ Set.mem_univ u) v (hD.closure_eq ▸ Set.mem_univ v)

lemma mixed_form_tendsto {ι : Type*} {l : Filter ι}
    {bs : ι → BoundedForm E} {b : BoundedForm E}
    {us vs : ι → E} {u v : E}
    (hb : Tendsto (fun i => ‖bs i - b‖) l (𝓝 0)) (hu : Tendsto us l (𝓝 u))
    (hv : Tendsto vs l (𝓝 v)) :
    Tendsto (fun i => bs i (us i) (vs i)) l (𝓝 (b u v)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hU : Tendsto (fun i => ‖us i - u‖) l (𝓝 0) := by
    simpa using (hu.sub (tendsto_const_nhds (x := u))).norm
  have hV : Tendsto (fun i => ‖vs i - v‖) l (𝓝 0) := by
    simpa using (hv.sub (tendsto_const_nhds (x := v))).norm
  have hlim : Tendsto (fun i =>
      ‖bs i - b‖ * ‖us i‖ * ‖vs i‖ + ‖b‖ * ‖us i - u‖ * ‖vs i‖ +
      ‖b‖ * ‖u‖ * ‖vs i - v‖) l (𝓝 0) := by
    simpa using (((hb.mul hu.norm).mul hv.norm).add
      (((tendsto_const_nhds (x := ‖b‖)).mul hU).mul hv.norm)).add
      ((tendsto_const_nhds (x := ‖b‖ * ‖u‖)).mul hV)
  exact squeeze_zero (fun i => norm_nonneg _) (fun i => mixed_form_estimate _ _ _ _ _ _) hlim

end GW.Analysis
