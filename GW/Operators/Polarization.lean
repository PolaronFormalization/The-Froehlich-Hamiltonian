module
public import GW.Analysis.MixedForms
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.Adjoint
/-! Source basic:polarization. The algebraic form has no continuity
assumption; polarization proves the mixed bound before Riesz is applied. -/
@[expose] public section
noncomputable section
open scoped InnerProductSpace
namespace GW.Operators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
abbrev AlgebraicForm (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] :=
  E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ

lemma hermitian_re_bound (b : AlgebraicForm E)
    (hs : ∀ u v, b u v = star (b v u)) {C : ℝ}
    (hd : ∀ u, ‖b u u‖ ≤ C * ‖u‖ ^ 2) (u v : E) :
    (b u v).re ≤ C / 2 * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
  have hsym : (b v u).re = (b u v).re := by rw [hs v u]; rfl
  have hpol : 4 * (b u v).re = (b (u+v) (u+v)).re - (b (u-v) (u-v)).re := by
    simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply,
      Complex.add_re, Complex.sub_re]
    linarith
  have hplus := (Complex.re_le_norm (b (u+v) (u+v))).trans (hd (u+v))
  have hminus : -(b (u-v) (u-v)).re ≤ C * ‖u-v‖ ^ 2 :=
    ((neg_le_abs _).trans (Complex.abs_re_le_norm _)).trans (hd (u-v))
  have hpara := congrArg (fun t : ℝ => C*t) (parallelogram_law_with_norm ℂ u v)
  nlinarith

lemma hermitian_unit_bound (b : AlgebraicForm E)
    (hs : ∀ u v, b u v = star (b v u)) {C : ℝ} (hC : 0 ≤ C)
    (hd : ∀ u, ‖b u u‖ ≤ C * ‖u‖ ^ 2) (u v : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) : ‖b u v‖ ≤ C := by
  by_cases hz : b u v = 0
  · simpa only [hz, norm_zero] using hC
  let z := b u v
  let c : ℂ := star z / (‖z‖ : ℂ)
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hcn : ‖c‖ = 1 := by simp [c, hn]
  have hrot : b u (c • v) = (‖z‖ : ℂ) := by
    rw [map_smul]
    change (star z / (‖z‖ : ℂ)) * z = (‖z‖ : ℂ)
    rw [div_mul_eq_mul_div, div_eq_iff (Complex.ofReal_ne_zero.mpr hn)]
    simpa only [sq, Complex.star_def] using Complex.conj_mul' z
  have hcunit : ‖c • v‖ = 1 := by rw [norm_smul, hcn, hv, one_mul]
  have h := hermitian_re_bound b hs hd u (c • v)
  rw [hrot, Complex.ofReal_re, hu, hcunit] at h
  change ‖z‖ ≤ C
  linarith

lemma hermitian_mixed_bound (b : AlgebraicForm E)
    (hs : ∀ u v, b u v = star (b v u)) {C : ℝ} (hC : 0 ≤ C)
    (hd : ∀ u, ‖b u u‖ ≤ C * ‖u‖ ^ 2) (u v : E) :
    ‖b u v‖ ≤ C * ‖u‖ * ‖v‖ := by
  by_cases hu : u = 0
  · simp [hu]
  by_cases hv : v = 0
  · simp [hv]
  have hun : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have hvn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  let un := (‖u‖⁻¹ : ℂ) • u
  let vn := (‖v‖⁻¹ : ℂ) • v
  have hnu : ‖un‖ = 1 := by simp [un, norm_smul, hun]
  have hnv : ‖vn‖ = 1 := by simp [vn, norm_smul, hvn]
  have hunit := hermitian_unit_bound b hs hC hd un vn hnu hnv
  have hscale : b un vn = ((‖u‖⁻¹ : ℂ) * (‖v‖⁻¹ : ℂ)) * b u v := by
    simp only [un, vn, map_smulₛₗ, LinearMap.smul_apply,
      map_inv₀, smul_eq_mul, RingHom.id_apply, Complex.conj_ofReal]
    ring
  have hnscale : ‖b u v‖ = ‖u‖ * ‖v‖ * ‖b un vn‖ := by
    rw [hscale, norm_mul, norm_mul]
    simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm]
    field_simp
  rw [hnscale]
  nlinarith [mul_le_mul_of_nonneg_left hunit (mul_nonneg (norm_nonneg u) (norm_nonneg v))]
/-- Both continuity bounds are supplied by the proved mixed form estimate. -/
def boundedAlgebraicForm (b : AlgebraicForm E) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ u v, ‖b u v‖ ≤ C * ‖u‖ * ‖v‖) : GW.Analysis.BoundedForm E := by
  let L : E →ₗ⋆[ℂ] E →L[ℂ] ℂ :=
    { toFun u := (b u).mkContinuous (C * ‖u‖) (hb u)
      map_add' u v := by
        ext z
        change b (u+v) z = b u z + b v z
        simp only [map_add, LinearMap.add_apply]
      map_smul' c u := by
        ext z
        change b (c • u) z = (starRingEnd ℂ c) • b u z
        simp only [map_smulₛₗ, LinearMap.smul_apply] }
  apply L.mkContinuous C
  intro u
  exact (L u).opNorm_le_bound (mul_nonneg hC (norm_nonneg u)) (hb u)

lemma boundedAlgebraicForm_apply (b : AlgebraicForm E) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ u v, ‖b u v‖ ≤ C * ‖u‖ * ‖v‖) (u v : E) :
    boundedAlgebraicForm b hC hb u v = b u v := rfl

variable [CompleteSpace E]

/-- Riesz is reconciled with the manuscript's first-slot conjugate-linear convention. -/
lemma hermitian_form_representation (b : AlgebraicForm E)
    (hs : ∀ u v, b u v = star (b v u)) {C : ℝ} (hC : 0 ≤ C)
    (hd : ∀ u, ‖b u u‖ ≤ C * ‖u‖ ^ 2) :
    ∃! B : E →L[ℂ] E, (∀ u v, b u v = ⟪u, B v⟫_ℂ) ∧ B.adjoint = B ∧ ‖B‖ ≤ C := by
  have hb := hermitian_mixed_bound b hs hC hd
  let bc := boundedAlgebraicForm b hC hb
  let B := InnerProductSpace.continuousLinearMapOfBilin bc
  have hleft (u v : E) : ⟪B u, v⟫_ℂ = b u v :=
    InnerProductSpace.continuousLinearMapOfBilin_apply bc u v
  have hrep (u v : E) : b u v = ⟪u, B v⟫_ℂ := by
    rw [hs u v, ← hleft v u]
    simp only [Complex.star_def, inner_conj_symm]
  have hself : B.adjoint = B := by
    apply Eq.symm
    apply (ContinuousLinearMap.eq_adjoint_iff B B).mpr
    intro u v
    exact (hleft u v).trans (hrep u v)
  have hnorm : ‖B‖ ≤ C := by
    apply B.opNorm_le_bound hC
    intro v
    have hp := hb (B v) v
    rw [hrep, inner_self_eq_norm_sq_to_K] at hp
    change ‖((‖B v‖ : ℂ) ^ 2)‖ ≤ C * ‖B v‖ * ‖v‖ at hp
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_norm] at hp
    by_cases hz : B v = 0
    · simp only [hz, norm_zero]
      exact mul_nonneg hC (norm_nonneg v)
    · have hn : 0 < ‖B v‖ := norm_pos_iff.mpr hz
      nlinarith
  refine ⟨B, ⟨hrep, hself, hnorm⟩, ?_⟩
  intro B' hB'
  ext v
  exact ext_inner_left ℂ (fun u => (hB'.1 u v).symm.trans (hrep u v))

end GW.Operators
