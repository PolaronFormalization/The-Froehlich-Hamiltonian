module
public import GW.Model.ModelFrohlichEstimates
@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace GW.Model

def momentDensity (α s : ℝ) (k : GW.Space) : ℝ := (v α k)^2 * (1+‖k‖^2)^(s-2)

def momentOn (α s : ℝ) (S : Set GW.Space) : ℝ≥0∞ :=
  ∫⁻ k in S, ENNReal.ofReal (momentDensity α s k) ∂(volume : Measure GW.Space)

def physicalMoment (α s : ℝ) : ℝ≥0∞ :=
  ∫⁻ k, ENNReal.ofReal (momentDensity α s k) ∂(volume : Measure GW.Space)

lemma momentDensity_measurable (α s : ℝ) : Measurable (momentDensity α s) := by
  unfold momentDensity
  exact ((v_measurable α).pow_const 2).mul (by fun_prop)

lemma momentDensity_nonneg (α s : ℝ) (k : GW.Space) : 0 ≤ momentDensity α s k :=
  mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by positivity) _)

@[simp] lemma momentOn_zero_coupling (s : ℝ) (S : Set GW.Space) : momentOn 0 s S = 0 := by
  simp [momentOn,momentDensity]

@[simp] lemma physicalMoment_zero_coupling (s : ℝ) : physicalMoment 0 s = 0 := by
  simp [physicalMoment,momentDensity]

lemma momentOn_low_bound (α s R : ℝ) (hα : 0 ≤ α) (hR : 0 < R) :
    momentOn α s (lowRegion R) ≤
      ENNReal.ofReal (max 1 ((1+R^2)^(s-2)) * (7*unitBallVolume*α*R)) := by
  let C := max 1 ((1+R^2)^(s-2))
  have hC : 0 ≤ C := zero_le_one.trans (le_max_left _ _)
  have hb (k : GW.Space) (hk : k ∈ lowRegion R) : (1+‖k‖^2)^(s-2) ≤ C := by
    have hle : ‖k‖ ≤ R := hk
    have hb := (rpow_endpoint_bounds (z := s-2) (a := 1) (b := 1+R^2) (x := 1+‖k‖^2)
      zero_lt_one (by linarith [sq_nonneg ‖k‖]) (by
        exact add_le_add_right (pow_le_pow_left₀ (norm_nonneg _) hle 2) 1)).2
    simpa only [Real.one_rpow] using hb
  change momentOn α s (lowRegion R) ≤ ENNReal.ofReal (C * (7*unitBallVolume*α*R))
  calc
    _ ≤ ∫⁻ k in lowRegion R, ENNReal.ofReal C * ENNReal.ofReal ((v α k)^2)
        ∂(volume : Measure GW.Space) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (μ := (volume : Measure GW.Space)) (lowRegion_measurable R)] with k hk
      rw [← ENNReal.ofReal_mul hC]
      apply ENNReal.ofReal_le_ofReal
      unfold momentDensity
      rw [mul_comm C]
      exact mul_le_mul_of_nonneg_left (hb k hk) (sq_nonneg _)
    _ = ENNReal.ofReal C * (∫⁻ k, ENNReal.ofReal (‖(cutoff α R k : ℂ)‖^2) ∂(volume : Measure GW.Space)) := by
      rw [lintegral_const_mul _ (((v_measurable α).pow_const 2).ennreal_ofReal),cutoff_sq_restrict]
    _ ≤ _ := by
      rw [ENNReal.ofReal_mul hC]
      gcongr
      exact cutoff_sq_bound α R hα hR

lemma momentOn_low_finite (α s R : ℝ) (hα : 0 ≤ α) (hR : 0 < R) :
    momentOn α s (lowRegion R) < ∞ :=
  (momentOn_low_bound α s R hα hR).trans_lt ENNReal.ofReal_lt_top

lemma momentDensity_factor (α s : ℝ) (hα : 0 ≤ α) (k : GW.Space) (hk : 0 < ‖k‖) :
    momentDensity α s k = α * ‖k‖^(-(6-2*s):ℝ) * (1+(‖k‖^2)⁻¹)^(s-2) := by
  let r := ‖k‖
  have hr : 0 < r := hk
  have he : 1+r^2 = r^2 * (1+(r^2)⁻¹) := by
    field_simp [ne_of_gt hr]
    ring
  change (v α k)^2*(1+r^2)^(s-2) = α*r^(-(6-2*s):ℝ)*(1+(r^2)⁻¹)^(s-2)
  have hv : (v α k)^2 = α * r^(-(2:ℝ)) := by
    rw [v_sq hα]
    change α/r^2 = _
    rw [Real.rpow_neg hr.le,Real.rpow_ofNat,div_eq_mul_inv]
  rw [hv,he,Real.mul_rpow (sq_nonneg r) (by positivity),← Real.rpow_natCast r 2,
    ← Real.rpow_mul hr.le]
  have hh : r^(-(2:ℝ)) * r^(2*(s-2)) = r^(-(6-2*s):ℝ) := by
    rw [← Real.rpow_add hr]
    congr 1
    ring
  simp only [Real.rpow_natCast]
  calc
    _ = α * (r^(-(2:ℝ)) * r^(2*(s-2))) * (1+(r^2)⁻¹)^(s-2) := by ring
    _ = _ := by rw [hh]

lemma momentDensity_compare (α s : ℝ) (hα : 0 ≤ α) (k : GW.Space) (hk : 1 ≤ ‖k‖) :
    (α*min 1 ((2:ℝ)^(s-2))) * ‖k‖^(-(6-2*s):ℝ) ≤ momentDensity α s k ∧
      momentDensity α s k ≤ (α*max 1 ((2:ℝ)^(s-2))) * ‖k‖^(-(6-2*s):ℝ) := by
  have h0 := zero_lt_one.trans_le hk
  have ht : (‖k‖^2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hk)
  have hb := rpow_endpoint_bounds (a := 1) (b := 2) (x := 1+(‖k‖^2)⁻¹) (z := s-2)
    zero_lt_one (le_add_of_nonneg_right (inv_nonneg.mpr (sq_nonneg _))) (by linarith)
  rw [Real.one_rpow] at hb
  rw [momentDensity_factor α s hα k h0]
  have hn := mul_nonneg hα (Real.rpow_nonneg h0.le (-(6-2*s)))
  constructor
  · convert mul_le_mul_of_nonneg_left hb.1 hn using 1 <;> ring
  · convert mul_le_mul_of_nonneg_left hb.2 hn using 1 <;> ring

lemma momentOn_compare (α s : ℝ) (hα : 0 ≤ α) {S : Set GW.Space} (hS : MeasurableSet S)
    (h : ∀ k ∈ S, 1 ≤ ‖k‖) :
    ENNReal.ofReal (α*min 1 ((2:ℝ)^(s-2))) * radialPowerIntegral (6-2*s) S ≤ momentOn α s S ∧
      momentOn α s S ≤ ENNReal.ofReal (α*max 1 ((2:ℝ)^(s-2))) * radialPowerIntegral (6-2*s) S := by
  have hm : Measurable (fun k : GW.Space => ENNReal.ofReal (‖k‖^(-(6-2*s):ℝ))) := by fun_prop
  have hmin : 0 ≤ α*min 1 ((2:ℝ)^(s-2)) := mul_nonneg hα
    (le_min zero_le_one (Real.rpow_nonneg (by norm_num) _))
  have hmax : 0 ≤ α*max 1 ((2:ℝ)^(s-2)) := mul_nonneg hα (zero_le_one.trans (le_max_left _ _))
  have hae := ae_restrict_mem (μ := (volume : Measure GW.Space)) hS
  constructor
  · unfold radialPowerIntegral momentOn
    rw [← lintegral_const_mul _ hm]
    apply lintegral_mono_ae
    filter_upwards [hae] with k hk
    rw [← ENNReal.ofReal_mul hmin]
    exact ENNReal.ofReal_le_ofReal (momentDensity_compare α s hα k (h k hk)).1
  · unfold radialPowerIntegral momentOn
    rw [← lintegral_const_mul _ hm]
    apply lintegral_mono_ae
    filter_upwards [hae] with k hk
    rw [← ENNReal.ofReal_mul hmax]
    exact ENNReal.ofReal_le_ofReal (momentDensity_compare α s hα k (h k hk)).2

lemma physicalMoment_split (α s : ℝ) :
    physicalMoment α s = momentOn α s (lowRegion 1) + momentOn α s (highRegion 1) := by
  have he : (lowRegion 1)ᶜ = highRegion 1 := by
    ext k
    change (¬ ‖k‖ ≤ (1:ℝ)) ↔ 1 < ‖k‖
    exact not_le
  unfold physicalMoment momentOn
  rw [← lintegral_add_compl _ (lowRegion_measurable 1),he]

lemma physicalMoment_finite_iff (α s : ℝ) (hα : 0 < α) :
    physicalMoment α s < ∞ ↔ s < 3/2 := by
  have h := momentOn_compare α s hα.le (highRegion_measurable 1) (fun _ hk => (show (1:ℝ) < _ from hk).le)
  rw [physicalMoment_split]
  constructor
  · intro hf
    have ht : momentOn α s (highRegion 1) < ∞ :=
      (le_add_left (le_refl (momentOn α s (highRegion 1)))).trans_lt hf
    have hc : ENNReal.ofReal (α*min 1 ((2:ℝ)^(s-2))) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (mul_pos hα (lt_min zero_lt_one
        (Real.rpow_pos_of_pos (by norm_num) _)))).ne'
    have hp : exteriorPowerIntegral (6-2*s) 1 < ∞ := by
      by_contra! htop
      have hh : exteriorPowerIntegral (6-2*s) 1 = ∞ := top_unique htop
      have hl := h.1
      change ENNReal.ofReal (α*min 1 ((2:ℝ)^(s-2))) *
        exteriorPowerIntegral (6-2*s) 1 ≤ momentOn α s (highRegion 1) at hl
      rw [hh,ENNReal.mul_top hc] at hl
      exact ht.not_ge hl
    have hx := (exteriorPowerIntegral_finite_iff zero_lt_one _).mp hp
    linarith
  · intro hs
    have hp := (exteriorPowerIntegral_finite_iff zero_lt_one (6-2*s)).mpr (by linarith)
    exact ENNReal.add_lt_top.mpr ⟨momentOn_low_finite α s 1 hα.le zero_lt_one,
      h.2.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hp)⟩

lemma physicalMoment_critical (α : ℝ) (hα : 0 < α) : physicalMoment α (3/2) = ∞ :=
  not_lt_top_iff.mp (fun h => (lt_irrefl (3/2:ℝ)) ((physicalMoment_finite_iff α _ hα).mp h))

lemma exteriorPowerIntegral_sharp_upper (R β : ℝ) (hR : 0 < R) (hβ : 3 < β) :
    exteriorPowerIntegral β R ≤
      ENNReal.ofReal (7*unitBallVolume*R^(3-β)/(1-(2:ℝ)^(3-β))) := by
  rw [exteriorPowerIntegral_tsum hR]
  have hpow : (2:ℝ)^(-β) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have h (m : ℕ) : radialPowerIntegral β (exteriorAnnulus R m) ≤
      ENNReal.ofReal ((7*unitBallVolume*R^(3-β))*((2:ℝ)^(3-β))^m) := by
    have he := (exteriorAnnulus_power_bounds hR β m).2
    rw [max_eq_left hpow,mul_one] at he
    change _ ≤ ENNReal.ofReal (7*unitBallVolume*(R*(2:ℝ)^m)^(3-β)) at he
    rw [dyadic_power_factor hR.le (by norm_num : (0:ℝ) ≤ 2),← mul_assoc] at he
    exact he
  refine (tsum_le_tsum h).trans_eq ?_
  exact scaled_geometric_tsum
    (mul_nonneg (mul_nonneg (by norm_num) unitBallVolume_pos.le) (Real.rpow_nonneg hR.le _))
    (Real.rpow_nonneg (by norm_num) _)
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))

lemma momentOn_high_bound (α s R : ℝ) (hα : 0 ≤ α) (hs : s < 3/2) (hR : 1 ≤ R) :
    momentOn α s (highRegion R) ≤
      ENNReal.ofReal (7*unitBallVolume*α*R^(2*s-3)/(1-(2:ℝ)^(2*s-3))) := by
  have hRpos := zero_lt_one.trans_le hR
  have h := (momentOn_compare α s hα (highRegion_measurable R)
    (fun k hk => hR.trans (show R < ‖k‖ from hk).le)).2
  rw [max_eq_left (Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)),mul_one] at h
  have hb := exteriorPowerIntegral_sharp_upper R (6-2*s) hRpos (by linarith)
  have he : 3-(6-2*s) = 2*s-3 := by ring
  rw [he] at hb
  refine h.trans ?_
  change ENNReal.ofReal α * exteriorPowerIntegral (6-2*s) R ≤ _
  calc
    _ ≤ ENNReal.ofReal α *
        ENNReal.ofReal (7*unitBallVolume*R^(2*s-3)/(1-(2:ℝ)^(2*s-3))) := by gcongr
    _ = _ := by
      rw [← ENNReal.ofReal_mul hα]
      congr 1
      ring

lemma momentOn_critical_annulus_lower (α : ℝ) (hα : 0 ≤ α) (m : ℕ) :
    ENNReal.ofReal (7*unitBallVolume*α/(8*Real.sqrt 2)) ≤
      momentOn α (3/2) (exteriorAnnulus 1 m) := by
  have hpoint (k : GW.Space) (hk : k ∈ exteriorAnnulus 1 m) : 1 ≤ ‖k‖ := by
    have h := (exteriorRadius_strictMono zero_lt_one).monotone (Nat.zero_le m)
    exact (show 1 ≤ exteriorRadius 1 m from by simpa [exteriorRadius] using h).trans hk.1.le
  have h := (momentOn_compare α (3/2) hα (exteriorAnnulus_measurable 1 m) hpoint).1
  have h₁ : (3/2:ℝ)-2 = -(1/2) := by norm_num
  have h₂ : (6:ℝ)-2*(3/2) = 3 := by norm_num
  rw [h₁,h₂,min_eq_right (Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)),
    Real.rpow_neg (by norm_num),← Real.sqrt_eq_rpow] at h
  refine le_trans ?_ h
  calc
    _ = ENNReal.ofReal (α*(Real.sqrt 2)⁻¹) * ENNReal.ofReal (7*unitBallVolume/8) := by
      rw [← ENNReal.ofReal_mul (mul_nonneg hα (inv_nonneg.mpr (Real.sqrt_nonneg _)))]
      congr 1
      ring
    _ ≤ _ := by
      gcongr
      exact exteriorAnnulus_critical_lower zero_lt_one m

lemma exteriorAnnulus_finite_union_subset (m : ℕ) :
    (⋃ j ∈ Finset.range m, exteriorAnnulus 1 j) ⊆ radialShell 1 ((2:ℝ)^m) := by
  intro k hk
  obtain ⟨j,hj,hk⟩ := mem_iUnion₂.mp hk
  have hlo := (exteriorRadius_strictMono zero_lt_one).monotone (Nat.zero_le j)
  have hhi := (exteriorRadius_strictMono zero_lt_one).monotone (Nat.succ_le_of_lt (Finset.mem_range.mp hj))
  exact ⟨(show 1 ≤ exteriorRadius 1 j from by simpa [exteriorRadius] using hlo).trans_lt hk.1,
    hk.2.trans (by simpa [exteriorRadius] using hhi)⟩

lemma momentOn_critical_finite_lower (α : ℝ) (hα : 0 ≤ α) (m : ℕ) :
    ENNReal.ofReal ((7*unitBallVolume*α/(8*Real.sqrt 2))*m) ≤
      momentOn α (3/2) (radialShell 1 ((2:ℝ)^m)) := by
  let c := 7*unitBallVolume*α/(8*Real.sqrt 2)
  have hc : 0 ≤ c := div_nonneg (mul_nonneg (mul_nonneg (by norm_num) unitBallVolume_pos.le) hα)
    (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
  calc
    _ = ∑ j ∈ Finset.range m, ENNReal.ofReal c := by
      simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
      rw [ENNReal.ofReal_mul hc,ENNReal.ofReal_natCast,mul_comm]
    _ ≤ ∑ j ∈ Finset.range m, momentOn α (3/2) (exteriorAnnulus 1 j) :=
      Finset.sum_le_sum (fun j _ => momentOn_critical_annulus_lower α hα j)
    _ = momentOn α (3/2) (⋃ j ∈ Finset.range m, exteriorAnnulus 1 j) := by
      unfold momentOn
      symm
      exact lintegral_biUnion_finset
        ((exteriorAnnulus_disjoint zero_lt_one).set_pairwise _)
        (fun j _ => exteriorAnnulus_measurable 1 j) _
    _ ≤ _ := lintegral_mono' (Measure.restrict_mono (exteriorAnnulus_finite_union_subset m) le_rfl) le_rfl

def momentTailConstant (α s : ℝ) : ℝ := 7*unitBallVolume*α/(1-(2:ℝ)^(2*s-3))

def momentTailCutoffWitness (α s η : ℝ) : ℝ :=
  1 + (momentTailConstant α s/η)^(1/(3-2*s))

lemma momentTailConstant_nonneg (α s : ℝ) (hα : 0 ≤ α) (hs : s < 3/2) :
    0 ≤ momentTailConstant α s := by
  have h : (2:ℝ)^(2*s-3) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) unitBallVolume_pos.le) hα) (sub_nonneg.mpr h.le)

lemma momentTailCutoffWitness_bound (α s η : ℝ) (hα : 0 ≤ α) (hs : s < 3/2) (hη : 0 < η) :
    1 ≤ momentTailCutoffWitness α s η ∧
      momentOn α s (highRegion (momentTailCutoffWitness α s η)) ≤ ENNReal.ofReal η := by
  let R := momentTailCutoffWitness α s η
  let B := momentTailConstant α s
  let δ := 3-2*s
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hB : 0 ≤ B := momentTailConstant_nonneg α s hα hs
  have hx : 0 ≤ B/η := div_nonneg hB hη.le
  have hR : 1 ≤ R := by
    change 1 ≤ 1 + (B/η)^(1/δ)
    exact le_add_of_nonneg_right (Real.rpow_nonneg hx _)
  refine ⟨hR,(momentOn_high_bound α s R hα hs hR).trans ?_⟩
  apply ENNReal.ofReal_le_ofReal
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have he : 2*s-3 = -δ := by dsimp [δ]; ring
  rw [he,Real.rpow_neg hRp.le]
  have h₁ : (B/η)^(1/δ) ≤ R := by
    change _ ≤ 1 + (B/η)^(1/δ)
    linarith
  have h₂ := Real.rpow_le_rpow (Real.rpow_nonneg hx _) h₁ hδ.le
  rw [← Real.rpow_mul hx,one_div,mul_comm δ⁻¹ δ,mul_inv_cancel₀ hδ.ne',Real.rpow_one] at h₂
  have h₃ : B / R^δ ≤ η := by
    apply (div_le_iff₀ (Real.rpow_pos_of_pos hRp _)).mpr
    have h := (div_le_iff₀ hη).mp h₂
    exact h.trans_eq (mul_comm _ _)
  calc
    _ = B / R^δ := by
      unfold B momentTailConstant
      rw [he]
      ring
    _ ≤ _ := h₃

lemma momentCritical_exceeds (α L : ℝ) (hα : 0 < α) (hL : 0 ≤ L) :
    ∃ m : ℕ, ENNReal.ofReal L < momentOn α (3/2) (radialShell 1 ((2:ℝ)^m)) := by
  let c := 7*unitBallVolume*α/(8*Real.sqrt 2)
  have hc : 0 < c := div_pos (mul_pos (mul_pos (by norm_num) unitBallVolume_pos) hα)
    (mul_pos (by norm_num) (Real.sqrt_pos.2 (by norm_num)))
  obtain ⟨m,hm⟩ := exists_nat_gt (L/c)
  refine ⟨m,?_⟩
  have hm' : L < c*m := by
    have hh := (div_lt_iff₀ hc).mp hm
    simpa only [mul_comm] using hh
  exact ((ENNReal.ofReal_lt_ofReal_iff (hL.trans_lt hm')).mpr hm').trans_le (momentOn_critical_finite_lower α hα.le m)

lemma physicalMoment_subcritical_bound (α s : ℝ) (hα : 0 ≤ α) (hs : s < 3/2) :
    physicalMoment α s ≤
      ENNReal.ofReal (7*unitBallVolume*α*(1+1/(1-(2:ℝ)^(2*s-3)))) := by
  rw [physicalMoment_split]
  have hl := momentOn_low_bound α s 1 hα zero_lt_one
  have htwo : 1 + (1:ℝ)^2 = 2 := by norm_num
  rw [htwo,mul_one] at hl
  rw [max_eq_left (Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)),one_mul] at hl
  have hh := momentOn_high_bound α s 1 hα hs le_rfl
  simp only [Real.one_rpow,mul_one] at hh
  refine (add_le_add hl hh).trans_eq ?_
  have h₁ : 0 ≤ 7*unitBallVolume*α := mul_nonneg (mul_nonneg (by norm_num) unitBallVolume_pos.le) hα
  have h₂ : 0 ≤ 7*unitBallVolume*α/(1-(2:ℝ)^(2*s-3)) :=
    div_nonneg h₁ (sub_nonneg.mpr (Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)))
  rw [← ENNReal.ofReal_add h₁ h₂]
  congr 1
  ring

lemma momentOn_closedBall_finite (α s r : ℝ) (hα : 0 ≤ α) (x : GW.Space) :
    momentOn α s (Metric.closedBall x r) < ∞ := by
  let R := 1 + ‖x‖ + |r|
  have hR : 0 < R := by dsimp [R]; positivity
  have hs : Metric.closedBall x r ⊆ lowRegion R := by
    intro k hk
    have hd : ‖k-x‖ ≤ r := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hk
    change ‖k‖ ≤ R
    have h₁ : ‖k‖ ≤ ‖k-x‖ + ‖x‖ := by
      have he : k = k-x+x := by abel
      calc
        ‖k‖ = ‖k-x+x‖ := congrArg norm he
        _ ≤ _ := norm_add_le _ _
    exact h₁.trans (by dsimp [R]; linarith [le_abs_self r])
  exact (lintegral_mono' (Measure.restrict_mono hs le_rfl) le_rfl).trans_lt
    (momentOn_low_finite α s R hα hR)

lemma physicalMoment_subcritical_finite (α s : ℝ) (hα : 0 ≤ α) (hs : s < 3/2) :
    physicalMoment α s < ∞ :=
  (physicalMoment_subcritical_bound α s hα hs).trans_lt ENNReal.ofReal_lt_top

lemma physicalMoment_subcritical_real_bound (α s : ℝ) (hα : 0 ≤ α) (hs : s < 3/2) :
    (∫ k, momentDensity α s k ∂(volume : Measure GW.Space)) ≤
      7*unitBallVolume*α*(1+1/(1-(2:ℝ)^(2*s-3))) := by
  have he := (nonnegative_realIntegral_of_lintegral (momentDensity_measurable α s)
    (momentDensity_nonneg α s) (physicalMoment_subcritical_finite α s hα hs).ne).2
  have hratio : (2:ℝ)^(2*s-3) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hB : 0 ≤ 7*unitBallVolume*α*(1+1/(1-(2:ℝ)^(2*s-3))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) unitBallVolume_pos.le) hα)
      (add_nonneg zero_le_one (div_nonneg zero_le_one (sub_nonneg.mpr hratio.le)))
  exact he.le.trans ((ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (physicalMoment_subcritical_bound α s hα hs)).trans_eq (ENNReal.toReal_ofReal hB))

end GW.Model
