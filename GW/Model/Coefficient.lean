module

public import GW.Conventions
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

/-! Source model:frohlich-estimates, first proof paragraph, and §7 dressing
coefficients. Integrability assertions are separate outstanding obligations. -/
@[expose] public section
noncomputable section
namespace GW.Model

/-- The fixed three-dimensional physical coefficient; division at zero gives zero. -/
def v (α : ℝ) (k : Space) : ℝ := Real.sqrt α / ‖k‖

@[simp] lemma v_at_origin (α : ℝ) : v α 0 = 0 := by simp [v]

lemma v_away_from_origin (α : ℝ) (k : Space) :
    v α k = if k = 0 then 0 else Real.sqrt α / ‖k‖ := by
  split_ifs with h
  · subst k; simp
  · rfl

lemma v_measurable (α : ℝ) : Measurable (v α) := by
  unfold v
  fun_prop

lemma v_even (α : ℝ) (k : Space) : v α (-k) = v α k := by simp [v]

lemma v_nonneg (α : ℝ) (k : Space) : 0 ≤ v α k :=
  div_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)

@[simp] lemma v_zero_coupling (k : Space) : v 0 k = 0 := by simp [v]

lemma v_sq {α : ℝ} (hα : 0 ≤ α) (k : Space) :
    (v α k) ^ 2 = α / ‖k‖ ^ 2 := by
  rw [v, div_pow, Real.sq_sqrt hα]

/-- Finite ultraviolet cutoff, including its boundary sphere. -/
def cutoff (α Λ : ℝ) (k : Space) : ℝ :=
  if ‖k‖ ≤ Λ then v α k else 0

/-- Infinite-cutoff Gross coefficient, with the prescribed negative sign. -/
def b (α K : ℝ) (k : Space) : ℝ :=
  if K < ‖k‖ then -(v α k) / (1 + ‖k‖ ^ 2) else 0

lemma cutoff_measurable (α Λ : ℝ) : Measurable (cutoff α Λ) := by
  unfold cutoff
  exact Measurable.ite (measurableSet_le measurable_norm measurable_const)
    (v_measurable α) measurable_const

lemma b_measurable (α K : ℝ) : Measurable (b α K) := by
  unfold b
  apply Measurable.ite (measurableSet_lt measurable_const measurable_norm)
  · exact (v_measurable α).neg.div (measurable_const.add (measurable_norm.pow_const 2))
  · exact measurable_const

lemma b_even (α K : ℝ) (k : Space) : b α K (-k) = b α K k := by simp [b, v_even]

@[simp] lemma b_zero_coupling (K : ℝ) (k : Space) : b 0 K k = 0 := by
  simp [b]

lemma b_nonpos {α K : ℝ} (k : Space) : b α K k ≤ 0 := by
  unfold b
  split_ifs
  · exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (v_nonneg _ _)) (by positivity)
  · exact le_rfl

/-- The coefficient cancellation used in main:conjugation, before applying fields. -/
lemma dressing_cancellation (α K : ℝ) (k : Space) :
    v α k + b α K k + ‖k‖ ^ 2 * b α K k = cutoff α K k := by
  have hd : 1 + ‖k‖ ^ 2 ≠ 0 := by positivity
  unfold b cutoff
  by_cases h : K < ‖k‖
  · simp only [h, ite_true, not_le.mpr h, ite_false]
    field_simp
    ring
  · simp only [h, ite_false, le_of_not_gt h, ite_true, add_zero, mul_zero]

end GW.Model
