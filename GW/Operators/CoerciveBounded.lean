module
public import GW.Conventions
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Tactic
/-! Source basic:coercive-bounded. Coercivity gives a norm lower bound,
closed range, surjectivity by adjoint orthogonality, and the bounded inverse. -/
@[expose] public section
noncomputable section
open scoped InnerProductSpace Topology
namespace GW.Operators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

lemma coercive_lower_bound (B : E →L[ℂ] E) {c : ℝ} (_hc : 0 < c)
    (hp : ∀ u, c * ‖u‖ ^ 2 ≤ (⟪u, B u⟫_ℂ).re) (u : E) : c * ‖u‖ ≤ ‖B u‖ := by
  by_cases hu : u = 0
  · simp [hu]
  · have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu
    have hre := Complex.re_le_norm (⟪u, B u⟫_ℂ)
    have hcs := norm_inner_le_norm (𝕜 := ℂ) u (B u)
    have hpos := hp u
    nlinarith

lemma coercive_inverse_bound (B : E →L[ℂ] E) {c : ℝ} (hc : 0 < c)
    (hp : ∀ u, c * ‖u‖ ^ 2 ≤ (⟪u, B u⟫_ℂ).re) (u : E) :
    ‖u‖ ≤ c⁻¹ * ‖B u‖ := by
  have h := coercive_lower_bound B hc hp u
  have hd : ‖u‖ ≤ ‖B u‖ / c := (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using h)
  simpa only [div_eq_mul_inv, mul_comm] using hd

variable [CompleteSpace E]

lemma coercive_bijective (B : E →L[ℂ] E) (hs : B.adjoint = B) {c : ℝ} (hc : 0 < c)
    (hp : ∀ u, c * ‖u‖ ^ 2 ≤ (⟪u, B u⟫_ℂ).re) : Function.Bijective B := by
  have ha : AntilipschitzWith ⟨c⁻¹, (inv_pos.mpr hc).le⟩ B :=
    B.antilipschitz_of_bound (coercive_inverse_bound B hc hp)
  have hinj := ha.injective
  have hclosed : IsClosed (B.range : Set E) := ha.isClosed_range B.uniformContinuous
  have hk : B.ker = ⊥ := LinearMap.ker_eq_bot.mpr hinj
  have hr : B.rangeᗮ = ⊥ := by rw [B.orthogonal_range, hs, hk]
  have hd : B.range.topologicalClosure = ⊤ := B.range.topologicalClosure_eq_top_iff.mpr hr
  have he : B.range = ⊤ := by
    rwa [hclosed.submodule_topologicalClosure_eq] at hd
  exact ⟨hinj, LinearMap.range_eq_top.mp he⟩

/-- The unique algebraic inverse is made bounded using the source lower bound. -/
def coerciveInverse (B : E →L[ℂ] E) (hs : B.adjoint = B) {c : ℝ} (hc : 0 < c)
    (hp : ∀ u, c * ‖u‖ ^ 2 ≤ (⟪u, B u⟫_ℂ).re) : E →L[ℂ] E := by
  let e := LinearEquiv.ofBijective B.toLinearMap (coercive_bijective B hs hc hp)
  refine e.symm.toLinearMap.mkContinuous c⁻¹ (fun u => ?_)
  change ‖e.symm u‖ ≤ c⁻¹ * ‖u‖
  have h := coercive_inverse_bound B hc hp (e.symm u)
  change ‖e.symm u‖ ≤ c⁻¹ * ‖e (e.symm u)‖ at h
  simpa only [e.apply_symm_apply] using h

lemma coerciveInverse_left (B : E →L[ℂ] E) (hs : B.adjoint = B) {c : ℝ} (hc : 0 < c)
    (hp : ∀ u, c * ‖u‖ ^ 2 ≤ (⟪u, B u⟫_ℂ).re) (u : E) :
    coerciveInverse B hs hc hp (B u) = u := by
  unfold coerciveInverse
  exact (LinearEquiv.ofBijective B.toLinearMap (coercive_bijective B hs hc hp)).symm_apply_apply u

lemma coerciveInverse_right (B : E →L[ℂ] E) (hs : B.adjoint = B) {c : ℝ} (hc : 0 < c)
    (hp : ∀ u, c * ‖u‖ ^ 2 ≤ (⟪u, B u⟫_ℂ).re) (u : E) :
    B (coerciveInverse B hs hc hp u) = u := by
  unfold coerciveInverse
  exact (LinearEquiv.ofBijective B.toLinearMap (coercive_bijective B hs hc hp)).apply_symm_apply u

lemma coerciveInverse_norm_le (B : E →L[ℂ] E) (hs : B.adjoint = B) {c : ℝ} (hc : 0 < c)
    (hp : ∀ u, c * ‖u‖ ^ 2 ≤ (⟪u, B u⟫_ℂ).re) :
    ‖coerciveInverse B hs hc hp‖ ≤ c⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_pos.mpr hc).le
  intro u
  have h := coercive_inverse_bound B hc hp (coerciveInverse B hs hc hp u)
  simpa only [coerciveInverse_right] using h
end GW.Operators
