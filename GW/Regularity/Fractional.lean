module

public import GW.Conventions
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Tactic

/-! Source: reg:fractional-inequalities, lines 6937–6981.
The arguments below follow subadditivity, subtraction, and the displayed
regularizing-fraction identity in the manuscript. -/
@[expose] public section

noncomputable section
open Filter
open scoped Topology
namespace GW.Regularity

lemma fractional_subadd {a b r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hr : 0 < r) (hr1 : r ≤ 1) :
    (a + b) ^ r ≤ a ^ r + b ^ r :=
  Real.rpow_add_le_add_rpow ha hb hr.le hr1

lemma fractional_difference {a b r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hr : 0 < r) (hr1 : r ≤ 1) :
    |a ^ r - b ^ r| ≤ |a - b| ^ r := by
  have step : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → b ≤ a →
      a ^ r - b ^ r ≤ (a - b) ^ r := by
    intro a b _ hb hba
    have h := fractional_subadd (sub_nonneg.mpr hba) hb hr hr1
    rw [sub_add_cancel] at h
    linarith
  apply abs_le.mpr
  constructor
  · by_cases h : b ≤ a
    · have hm := Real.rpow_le_rpow hb h hr.le
      have hn := Real.rpow_nonneg (abs_nonneg (a - b)) r
      linarith
    · have h := le_of_not_ge h
      have hs := step b a hb ha h
      rw [abs_of_nonpos (sub_nonpos.mpr h)]
      simpa only [neg_sub] using (show -(b - a) ^ r ≤ a ^ r - b ^ r by linarith)
  · by_cases h : b ≤ a
    · rw [abs_of_nonneg (sub_nonneg.mpr h)]
      exact step a b ha hb h
    · have hm := Real.rpow_le_rpow ha (le_of_not_ge h) hr.le
      have hn := Real.rpow_nonneg (abs_nonneg (a - b)) r
      linarith

/-- The bounded radial regularizer, with the same real exponents as the source. -/
def rho (ε r t : ℝ) : ℝ := t ^ r / (1 + ε * t ^ r)

lemma regularizer_difference {A B ε : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hε : 0 < ε) :
    |A / (1 + ε * A) - B / (1 + ε * B)| ≤ |A - B| := by
  have hdA : 0 < 1 + ε * A := by positivity
  have hdB : 0 < 1 + ε * B := by positivity
  have hid : A / (1 + ε * A) - B / (1 + ε * B) =
      (A - B) / ((1 + ε * A) * (1 + ε * B)) := by
    field_simp
    ring
  rw [hid, abs_div, abs_of_pos (mul_pos hdA hdB)]
  apply (div_le_iff₀ (mul_pos hdA hdB)).mpr
  have hp : 1 ≤ (1 + ε * A) * (1 + ε * B) := by
    exact one_le_mul_of_one_le_of_one_le (by nlinarith [mul_nonneg hε.le hA])
      (by nlinarith [mul_nonneg hε.le hB])
  nlinarith [abs_nonneg (A - B)]

lemma rho_difference {a b ε r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hε : 0 < ε) (hr : 0 < r) (hr1 : r ≤ 1) :
    |rho ε r a - rho ε r b| ≤ |a - b| ^ r :=
  (regularizer_difference (Real.rpow_nonneg ha r) (Real.rpow_nonneg hb r) hε).trans
    (fractional_difference ha hb hr hr1)

lemma rho_momentum_difference (q k : Space) {ε r : ℝ}
    (hε : 0 < ε) (hr : 0 < r) (hr1 : r ≤ 1) :
    |rho ε r ‖q + k‖ - rho ε r ‖k‖| ≤ ‖q‖ ^ r := by
  apply (rho_difference (norm_nonneg _) (norm_nonneg _) hε hr hr1).trans
  apply Real.rpow_le_rpow (abs_nonneg _) _ hr.le
  simpa only [add_sub_cancel_right] using abs_norm_sub_norm_le (q + k) k

lemma rho_bounds {ε r t : ℝ} (hε : 0 < ε) (ht : 0 ≤ t) :
    0 ≤ rho ε r t ∧ rho ε r t ≤ min (t ^ r) ε⁻¹ := by
  have hA := Real.rpow_nonneg ht r
  have hd : 0 < 1 + ε * t ^ r := by positivity
  refine ⟨div_nonneg hA hd.le, le_min ?_ ?_⟩
  · exact (div_le_iff₀ hd).mpr (by nlinarith [mul_nonneg hε.le hA, mul_nonneg hA (mul_nonneg hε.le hA)])
  · rw [rho, inv_eq_one_div]
    apply (div_le_div_iff₀ hd hε).mpr
    nlinarith

lemma rho_antitone {r t : ℝ} (ht : 0 ≤ t) :
    AntitoneOn (fun ε => rho ε r t) (Set.Ioi 0) := by
  intro ε hε δ _ hεδ
  have hA := Real.rpow_nonneg ht r
  unfold rho
  exact div_le_div_of_nonneg_left hA
    (by nlinarith [mul_nonneg hε.le hA])
    (by nlinarith [mul_le_mul_of_nonneg_right hεδ hA])

lemma rho_tendsto (r t : ℝ) :
    Tendsto (fun ε : ℝ => rho ε r t) (𝓝[>] 0) (𝓝 (t ^ r)) := by
  have h : Tendsto (fun ε : ℝ => t ^ r / (1 + ε * t ^ r))
      (𝓝 0) (𝓝 (t ^ r / (1 + 0 * t ^ r))) := by
    exact tendsto_const_nhds.div
      (tendsto_const_nhds.add (tendsto_id.mul tendsto_const_nhds)) (by simp)
  simpa only [zero_mul, add_zero, div_one, rho] using h.mono_left nhdsWithin_le_nhds

end GW.Regularity
