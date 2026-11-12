module
public import GW.Gross.MainTails
public import GW.Model.ModelMomentThreshold
@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace GW.Regularity
open GW.Model

def grossDressingCoefficient (α K : ℝ) (k : GW.Space) : ℝ :=
  - (highRegion K).indicator (v α) k / (1+‖k‖^2)

def grossMomentumCoefficient (α K : ℝ) (j : Fin 3) (k : GW.Space) : ℝ :=
  k j * grossDressingCoefficient α K k

def grossMomentTailDensity (α s : ℝ) (k : GW.Space) : ℝ :=
  ‖k‖^(2*s) * (v α k)^2 / (1+‖k‖^2)^2

def grossMomentTail (α K s : ℝ) : ℝ≥0∞ :=
  ∫⁻ k in highRegion K, ENNReal.ofReal (grossMomentTailDensity α s k) ∂(volume : Measure GW.Space)

def grossMomentumCoefficientMoment (α K s : ℝ) (j : Fin 3) : ℝ≥0∞ :=
  ∫⁻ k, ENNReal.ofReal (‖k‖^(2*(s-1)) * (grossMomentumCoefficient α K j k)^2)
    ∂(volume : Measure GW.Space)

lemma grossDressingCoefficient_measurable (α K : ℝ) : Measurable (grossDressingCoefficient α K) := by
  unfold grossDressingCoefficient
  exact ((v_measurable α).indicator (highRegion_measurable K)).neg.div (by fun_prop)

lemma grossMomentumCoefficient_measurable (α K : ℝ) (j : Fin 3) :
    Measurable (grossMomentumCoefficient α K j) :=
  (PiLp.continuous_apply 2 _ j).measurable.mul (grossDressingCoefficient_measurable α K)

lemma grossMomentTailDensity_measurable (α s : ℝ) : Measurable (grossMomentTailDensity α s) := by
  unfold grossMomentTailDensity
  exact ((continuous_norm.measurable.pow_const _).mul ((v_measurable α).pow_const 2)).div (by fun_prop)

lemma grossMomentTailDensity_nonneg (α s : ℝ) (k : GW.Space) : 0 ≤ grossMomentTailDensity α s k := by
  unfold grossMomentTailDensity
  positivity

lemma grossMomentTail_density_ratio (α s : ℝ) (k : GW.Space) :
    grossMomentTailDensity α s k =
      (‖k‖^2/(1+‖k‖^2))^s * momentDensity α s k := by
  let t := ‖k‖
  let w := 1+t^2
  have ht : 0 ≤ t := norm_nonneg _
  have hw : 0 < w := by unfold w; positivity
  unfold grossMomentTailDensity momentDensity
  change t^(2*s) * (v α k)^2 / w^2 = (t^2/w)^s * ((v α k)^2 * w^(s-2))
  rw [Real.div_rpow (sq_nonneg _) hw.le,
    show (t^2)^s = t^(2*s) by rw [Real.rpow_mul ht,Real.rpow_two],
    Real.rpow_sub hw,Real.rpow_two]
  have hwp : w^s ≠ 0 := (Real.rpow_pos_of_pos hw _).ne'
  field_simp [hwp]
  <;> ring

lemma grossMomentTail_density_le (α s : ℝ) (hs : 0 ≤ s) (k : GW.Space) :
    grossMomentTailDensity α s k ≤ momentDensity α s k := by
  rw [grossMomentTail_density_ratio]
  have hp : 0 < 1+‖k‖^2 := by positivity
  have h : 0 ≤ ‖k‖^2/(1+‖k‖^2) := div_nonneg (sq_nonneg _) hp.le
  have h₁ : ‖k‖^2/(1+‖k‖^2) ≤ 1 := (div_le_iff₀ hp).mpr (by linarith)
  exact (mul_le_mul_of_nonneg_right (Real.rpow_le_one h h₁ hs) (momentDensity_nonneg α s k)).trans_eq (one_mul _)

lemma grossMomentTail_density_ge (α s : ℝ) (hs : 0 ≤ s) (k : GW.Space) (hk : 1 ≤ ‖k‖) :
    (1/2:ℝ)^s * momentDensity α s k ≤ grossMomentTailDensity α s k := by
  rw [grossMomentTail_density_ratio]
  have hp : 0 < 1+‖k‖^2 := by positivity
  have h : (1/2:ℝ) ≤ ‖k‖^2/(1+‖k‖^2) := (le_div_iff₀ hp).mpr (by nlinarith)
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (by norm_num) h hs) (momentDensity_nonneg α s k)

lemma grossMomentTail_finite_iff (α K s : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s) :
    grossMomentTail α K s < ∞ ↔ physicalMoment α s < ∞ := by
  let R := max K 1
  let c := (1/2:ℝ)^s
  have hR : 0 < R := zero_lt_one.trans_le (le_max_right _ _)
  have hhigh : highRegion R ⊆ highRegion K := fun _ hk => (le_max_left K 1).trans_lt hk
  have hc : 0 < c := Real.rpow_pos_of_pos (by norm_num) _
  have hcl : (lowRegion R)ᶜ = highRegion R := by
    ext k
    change (¬ ‖k‖ ≤ R) ↔ R < ‖k‖
    exact not_le
  constructor
  · intro hj
    have hb : ENNReal.ofReal c * momentOn α s (highRegion R) ≤ grossMomentTail α K s := by
      unfold momentOn grossMomentTail
      rw [← lintegral_const_mul _ ((momentDensity_measurable α s).ennreal_ofReal)]
      calc
        _ ≤ ∫⁻ k in highRegion R, ENNReal.ofReal (grossMomentTailDensity α s k) ∂(volume : Measure GW.Space) := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem (highRegion_measurable R)] with k hk
          rw [← ENNReal.ofReal_mul hc.le]
          exact ENNReal.ofReal_le_ofReal
            (grossMomentTail_density_ge α s hs k ((le_max_right K 1).trans (show R ≤ ‖k‖ from hk.le)))
        _ ≤ _ := lintegral_mono' (Measure.restrict_mono hhigh le_rfl) (le_refl _)
    have htail : momentOn α s (highRegion R) < ∞ := by
      by_contra! h
      have htop := top_unique h
      rw [htop,ENNReal.mul_top (ENNReal.ofReal_pos.mpr hc).ne'] at hb
      exact hj.not_ge hb
    unfold physicalMoment
    rw [← lintegral_add_compl _ (lowRegion_measurable R),hcl]
    exact ENNReal.add_lt_top.mpr ⟨momentOn_low_finite α s R hα hR,htail⟩
  · intro hi
    have hb : grossMomentTail α K s ≤ physicalMoment α s := by
      unfold grossMomentTail physicalMoment
      exact lintegral_mono' Measure.restrict_le_self
        (fun k => ENNReal.ofReal_le_ofReal (grossMomentTail_density_le α s hs k))
    exact hb.trans_lt hi

lemma grossMomentTail_sharp_iff (α K s : ℝ) (hα : 0 < α) (hs : 1 ≤ s) :
    grossMomentTail α K s < ∞ ↔ s < 3/2 :=
  (grossMomentTail_finite_iff α K s hα.le (zero_le_one.trans hs)).trans (physicalMoment_finite_iff α s hα)

lemma grossMomentTail_critical (α K : ℝ) (hα : 0 < α) : grossMomentTail α K (3/2) = ∞ :=
  not_lt_top_iff.mp (fun h => (lt_irrefl (3/2:ℝ)) ((grossMomentTail_sharp_iff α K _ hα (by norm_num)).mp h))

lemma grossMomentTail_zero_coupling (K s : ℝ) : grossMomentTail 0 K s = 0 := by
  simp [grossMomentTail,grossMomentTailDensity,v]

lemma grossMomentumComponent_sum_density (α K s : ℝ) (hK : 0 < K) (k : GW.Space) :
    (∑ j : Fin 3, ‖k‖^(2*(s-1)) * (grossMomentumCoefficient α K j k)^2) =
      (highRegion K).indicator (grossMomentTailDensity α s) k := by
  by_cases hk : k ∈ highRegion K
  · let t := ‖k‖
    let b := grossDressingCoefficient α K k
    have ht : 0 < t := hK.trans (show K < ‖k‖ from hk)
    have hb : b = -(v α k)/(1+t^2) := by
      unfold b grossDressingCoefficient
      rw [indicator_of_mem hk]
    have hs : t^(2*(s-1)) * t^2 = t^(2*s) := by
      rw [← Real.rpow_two t,← Real.rpow_add ht]
      congr 1
      ring
    have hsum : (∑ j : Fin 3, t^(2*(s-1)) * (k j*b)^2) = (t^(2*(s-1))*t^2) * b^2 := by
      have hq : t^2 = ∑ j : Fin 3, (k j)^2 := EuclideanSpace.real_norm_sq_eq k
      rw [hq,Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [indicator_of_mem hk]
    calc
      _ = (t^(2*(s-1))*t^2) * b^2 := hsum
      _ = grossMomentTailDensity α s k := by
        rw [hs,hb]
        change t^(2*s) * (-(v α k)/(1+t^2))^2 = t^(2*s)*(v α k)^2/(1+t^2)^2
        rw [div_pow,neg_sq]
        ring
  · rw [indicator_of_notMem hk]
    have hb : grossDressingCoefficient α K k = 0 := by
      simp only [grossDressingCoefficient,indicator_of_notMem hk,neg_zero,zero_div]
    simp only [grossMomentumCoefficient,hb,mul_zero,zero_pow (by decide : (2:ℕ) ≠ 0),
      Finset.sum_const_zero]

lemma grossMomentTail_eq_component_sum (α K s : ℝ) (hK : 0 < K) :
    grossMomentTail α K s = ∑ j : Fin 3, grossMomentumCoefficientMoment α K s j := by
  let F (j : Fin 3) (k : GW.Space) :=
    ENNReal.ofReal (‖k‖^(2*(s-1)) * (grossMomentumCoefficient α K j k)^2)
  have hm (j : Fin 3) : Measurable (F j) :=
    ((continuous_norm.measurable.pow_const _).mul ((grossMomentumCoefficient_measurable α K j).pow_const 2)).ennreal_ofReal
  unfold grossMomentTail grossMomentumCoefficientMoment
  rw [← lintegral_indicator (highRegion_measurable K)]
  change _ = ∑ j : Fin 3, ∫⁻ k, F j k ∂(volume : Measure GW.Space)
  rw [← lintegral_finsetSum Finset.univ (fun j _ => hm j)]
  apply lintegral_congr
  intro k
  rw [← ENNReal.ofReal_sum_of_nonneg (f := fun j : Fin 3 => ‖k‖^(2*(s-1)) * (grossMomentumCoefficient α K j k)^2)
    (fun j _ => mul_nonneg (Real.rpow_nonneg (norm_nonneg k) _) (sq_nonneg _)),
    grossMomentumComponent_sum_density α K s hK k]
  change (highRegion K).indicator (fun x => ENNReal.ofReal (grossMomentTailDensity α s x)) k =
    ENNReal.ofReal ((highRegion K).indicator (grossMomentTailDensity α s) k)
  by_cases hk : k ∈ highRegion K
  · rw [indicator_of_mem hk,indicator_of_mem hk]
  · rw [indicator_of_notMem hk,indicator_of_notMem hk,ENNReal.ofReal_zero]

end GW.Regularity
