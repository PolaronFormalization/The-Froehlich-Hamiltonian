module
public import GW.Conventions
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
@[expose] public section
noncomputable section
open Set Metric Filter MeasureTheory
open scoped Topology ENNReal
namespace GW.Model

def unitBallVolume : ℝ := (volume : Measure GW.Space).real (ball 0 1)

lemma unitBallVolume_pos : 0 < unitBallVolume := by
  exact ENNReal.toReal_pos (ne_of_gt (Metric.measure_ball_pos (μ := (volume : Measure GW.Space)) 0 zero_lt_one))
    (measure_ball_lt_top.ne)

lemma unitBallVolume_measure : (volume : Measure GW.Space) (ball 0 1) = ENNReal.ofReal unitBallVolume :=
  (ENNReal.ofReal_toReal measure_ball_lt_top.ne).symm

lemma spaceBallVolume (r : ℝ) (hr : 0 < r) :
    (volume : Measure GW.Space) (ball 0 r) = ENNReal.ofReal (unitBallVolume * r^3) := by
  rw [Measure.addHaar_ball_of_pos volume (0 : GW.Space) hr,unitBallVolume_measure,
    ← ENNReal.ofReal_mul (pow_nonneg hr.le _)]
  congr 1
  have hdim : Module.finrank ℝ GW.Space = 3 := by simp [GW.Space]
  rw [hdim,mul_comm]

lemma spaceSphereVolume (r : ℝ) :
    (volume : Measure GW.Space) (sphere 0 r) = 0 :=
  Measure.addHaar_sphere volume _ _

lemma spaceClosedBallVolume (r : ℝ) (hr : 0 < r) :
    (volume : Measure GW.Space) (closedBall 0 r) = ENNReal.ofReal (unitBallVolume * r^3) := by
  rw [Measure.addHaar_closedBall_eq_addHaar_ball,spaceBallVolume r hr]

def radialShell (a b : ℝ) : Set GW.Space := {k | a < ‖k‖ ∧ ‖k‖ ≤ b}

lemma radialShell_measurable (a b : ℝ) : MeasurableSet (radialShell a b) :=
  (measurableSet_lt measurable_const continuous_norm.measurable).inter
    (measurableSet_le continuous_norm.measurable measurable_const)

lemma radialShell_sdiff (a b : ℝ) : radialShell a b = closedBall 0 b \ closedBall 0 a := by
  ext k
  simp only [radialShell,mem_ofPred_eq,Set.mem_sdiff,mem_closedBall,dist_zero_right,not_le,and_comm]

lemma radialShell_volume (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (volume : Measure GW.Space) (radialShell a b) = ENNReal.ofReal (unitBallVolume * (b^3-a^3)) := by
  rw [radialShell_sdiff,measure_sdiff (closedBall_subset_closedBall hab)
    measurableSet_closedBall.nullMeasurableSet measure_closedBall_lt_top.ne,
    spaceClosedBallVolume b (ha.trans_le hab),spaceClosedBallVolume a ha,
    ← ENNReal.ofReal_sub _ (mul_nonneg unitBallVolume_pos.le (pow_nonneg ha.le _))]
  ring_nf

def exteriorRadius (R : ℝ) (m : ℕ) : ℝ := R * (2:ℝ)^m
def interiorRadius (R : ℝ) (m : ℕ) : ℝ := R * (1/2:ℝ)^m

def exteriorAnnulus (R : ℝ) (m : ℕ) : Set GW.Space :=
  radialShell (exteriorRadius R m) (exteriorRadius R (m+1))

def interiorAnnulus (R : ℝ) (m : ℕ) : Set GW.Space :=
  radialShell (interiorRadius R (m+1)) (interiorRadius R m)

lemma exteriorRadius_pos {R : ℝ} (hR : 0 < R) (m : ℕ) : 0 < exteriorRadius R m := by
  unfold exteriorRadius
  positivity

lemma interiorRadius_pos {R : ℝ} (hR : 0 < R) (m : ℕ) : 0 < interiorRadius R m := by
  unfold interiorRadius
  positivity

lemma exteriorRadius_succ (R : ℝ) (m : ℕ) : exteriorRadius R (m+1) = 2 * exteriorRadius R m := by
  simp only [exteriorRadius,pow_succ]
  ring

lemma interiorRadius_succ (R : ℝ) (m : ℕ) : interiorRadius R (m+1) = interiorRadius R m / 2 := by
  simp only [interiorRadius,pow_succ]
  ring

lemma exteriorRadius_strictMono {R : ℝ} (hR : 0 < R) : StrictMono (exteriorRadius R) :=
  strictMono_nat_of_lt_succ (fun m => by
    rw [exteriorRadius_succ]
    linarith [exteriorRadius_pos hR m])

lemma interiorRadius_strictAnti {R : ℝ} (hR : 0 < R) : StrictAnti (interiorRadius R) :=
  strictAnti_nat_of_succ_lt (fun m => by
    rw [interiorRadius_succ]
    linarith [interiorRadius_pos hR m])

lemma exteriorAnnulus_volume {R : ℝ} (hR : 0 < R) (m : ℕ) :
    (volume : Measure GW.Space) (exteriorAnnulus R m) =
      ENNReal.ofReal (7 * unitBallVolume * (exteriorRadius R m)^3) := by
  rw [exteriorAnnulus,radialShell_volume _ _ (exteriorRadius_pos hR m)
    ((exteriorRadius_strictMono hR).monotone (Nat.le_succ _)),exteriorRadius_succ]
  congr 1
  ring

lemma interiorAnnulus_volume {R : ℝ} (hR : 0 < R) (m : ℕ) :
    (volume : Measure GW.Space) (interiorAnnulus R m) =
      ENNReal.ofReal ((7/8) * unitBallVolume * (interiorRadius R m)^3) := by
  rw [interiorAnnulus,radialShell_volume _ _ (interiorRadius_pos hR (m+1))
    ((interiorRadius_strictAnti hR).antitone (Nat.le_succ _)),interiorRadius_succ]
  congr 1
  ring

lemma exteriorAnnulus_measurable (R : ℝ) (m : ℕ) : MeasurableSet (exteriorAnnulus R m) :=
  radialShell_measurable _ _

lemma interiorAnnulus_measurable (R : ℝ) (m : ℕ) : MeasurableSet (interiorAnnulus R m) :=
  radialShell_measurable _ _

lemma exteriorAnnulus_disjoint {R : ℝ} (hR : 0 < R) : Pairwise (fun m n => Disjoint (exteriorAnnulus R m) (exteriorAnnulus R n)) := by
  intro m n hmn
  wlog h : m < n generalizing m n
  · exact (this hmn.symm (lt_of_le_of_ne (le_of_not_gt h) hmn.symm)).symm
  apply Set.disjoint_left.mpr
  intro k hm hn
  exact (not_lt_of_ge (hm.2.trans ((exteriorRadius_strictMono hR).monotone (Nat.succ_le_of_lt h)))) hn.1

lemma interiorAnnulus_disjoint {R : ℝ} (hR : 0 < R) : Pairwise (fun m n => Disjoint (interiorAnnulus R m) (interiorAnnulus R n)) := by
  intro m n hmn
  wlog h : m < n generalizing m n
  · exact (this hmn.symm (lt_of_le_of_ne (le_of_not_gt h) hmn.symm)).symm
  apply Set.disjoint_left.mpr
  intro k hm hn
  exact (not_lt_of_ge (hn.2.trans ((interiorRadius_strictAnti hR).antitone (Nat.succ_le_of_lt h)))) hm.1

lemma exteriorAnnulus_union {R : ℝ} (hR : 0 < R) :
    (⋃ m : ℕ, exteriorAnnulus R m) = {k | R < ‖k‖} := by
  ext k
  rw [mem_iUnion]
  constructor
  · rintro ⟨m,hm⟩
    have h := (exteriorRadius_strictMono hR).monotone (Nat.zero_le m)
    change R < ‖k‖
    exact (show R ≤ exteriorRadius R m from by simpa [exteriorRadius] using h).trans_lt hm.1
  · intro hk
    change R < ‖k‖ at hk
    have ht : Tendsto (exteriorRadius R) atTop atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ) < 2)).const_mul_atTop hR
    have he : ∃ m, ‖k‖ ≤ exteriorRadius R m := (ht.eventually (eventually_ge_atTop ‖k‖)).exists
    let n := Nat.find he
    have hn : ‖k‖ ≤ exteriorRadius R n := Nat.find_spec he
    have hn₀ : n ≠ 0 := by
      intro h
      have hh : ‖k‖ ≤ exteriorRadius R 0 := h ▸ hn
      exact hk.not_ge (by simpa [exteriorRadius] using hh)
    obtain ⟨m,hm⟩ := Nat.exists_eq_succ_of_ne_zero hn₀
    have h₁ : ¬ ‖k‖ ≤ exteriorRadius R m :=
      Nat.find_min he (show m < n from hm.symm ▸ Nat.lt_succ_self _)
    exact ⟨m,lt_of_not_ge h₁,by rw [← (show n = m+1 from hm)]; exact hn⟩

lemma interiorAnnulus_union {R : ℝ} (hR : 0 < R) :
    (⋃ m : ℕ, interiorAnnulus R m) = {k | 0 < ‖k‖ ∧ ‖k‖ ≤ R} := by
  ext k
  rw [mem_iUnion]
  constructor
  · rintro ⟨m,hm⟩
    have h := (interiorRadius_strictAnti hR).antitone (Nat.zero_le m)
    exact ⟨(interiorRadius_pos hR (m+1)).trans hm.1,
      hm.2.trans (by simpa [interiorRadius] using h)⟩
  · rintro ⟨hpos,hmax⟩
    have ht : Tendsto (interiorRadius R) atTop (𝓝 0) := by
      have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
        (by norm_num : (1/2:ℝ) < 1)).const_mul R
      change Tendsto (fun m : ℕ => R * (1/2:ℝ)^m) atTop (𝓝 0)
      simpa only [mul_zero] using h
    have he : ∃ m, interiorRadius R m < ‖k‖ := (ht.eventually (gt_mem_nhds hpos)).exists
    let n := Nat.find he
    have hn : interiorRadius R n < ‖k‖ := Nat.find_spec he
    have hn₀ : n ≠ 0 := by
      intro h
      have hh : interiorRadius R 0 < ‖k‖ := h ▸ hn
      exact hh.not_ge (by simpa [interiorRadius] using hmax)
    obtain ⟨m,hm⟩ := Nat.exists_eq_succ_of_ne_zero hn₀
    have h₁ : ¬ interiorRadius R m < ‖k‖ :=
      Nat.find_min he (show m < n from hm.symm ▸ Nat.lt_succ_self _)
    exact ⟨m,by rw [← (show n = m+1 from hm)]; exact hn,le_of_not_gt h₁⟩

def radialPowerIntegral (β : ℝ) (s : Set GW.Space) : ℝ≥0∞ :=
  ∫⁻ k in s, ENNReal.ofReal (‖k‖ ^ (-β : ℝ))

lemma radialPowerIntegral_bounds (β : ℝ) {s : Set GW.Space} (hs : MeasurableSet s)
    {l u : ℝ} (hl : ∀ k ∈ s, l ≤ ‖k‖ ^ (-β : ℝ))
    (hu : ∀ k ∈ s, ‖k‖ ^ (-β : ℝ) ≤ u) :
    ENNReal.ofReal l * (volume : Measure GW.Space) s ≤ radialPowerIntegral β s ∧
      radialPowerIntegral β s ≤ ENNReal.ofReal u * (volume : Measure GW.Space) s := by
  have hae : ∀ᵐ k ∂(volume : Measure GW.Space).restrict s, k ∈ s := ae_restrict_mem hs
  constructor
  · rw [← setLIntegral_const]
    apply lintegral_mono_ae
    exact hae.mono (fun k hk => ENNReal.ofReal_le_ofReal (hl k hk))
  · rw [← setLIntegral_const]
    apply lintegral_mono_ae
    exact hae.mono (fun k hk => ENNReal.ofReal_le_ofReal (hu k hk))

lemma rpow_endpoint_bounds {a b x z : ℝ} (ha : 0 < a) (hax : a ≤ x) (hxb : x ≤ b) :
    min (a^z) (b^z) ≤ x^z ∧ x^z ≤ max (a^z) (b^z) := by
  by_cases hz : 0 ≤ z
  · exact ⟨(min_le_left _ _).trans (Real.rpow_le_rpow ha.le hax hz),
      (Real.rpow_le_rpow (ha.le.trans hax) hxb hz).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (Real.rpow_le_rpow_of_nonpos (ha.trans_le hax) hxb (le_of_not_ge hz)),
      (Real.rpow_le_rpow_of_nonpos ha hax (le_of_not_ge hz)).trans (le_max_left _ _)⟩

lemma exteriorAnnulus_power_bounds {R : ℝ} (hR : 0 < R) (β : ℝ) (m : ℕ) :
    let r := exteriorRadius R m
    ENNReal.ofReal (7 * unitBallVolume * min 1 ((2:ℝ)^(-β)) * r^(3-β)) ≤
        radialPowerIntegral β (exteriorAnnulus R m) ∧
      radialPowerIntegral β (exteriorAnnulus R m) ≤
        ENNReal.ofReal (7 * unitBallVolume * max 1 ((2:ℝ)^(-β)) * r^(3-β)) := by
  let r := exteriorRadius R m
  have hr : 0 < r := exteriorRadius_pos hR m
  have hz : 0 ≤ r^(-β) := Real.rpow_nonneg hr.le _
  have hmin : min (r^(-β)) ((2*r)^(-β)) = min 1 ((2:ℝ)^(-β)) * r^(-β) := by
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hr.le]
    simpa only [one_mul] using (min_mul_of_nonneg 1 ((2:ℝ)^(-β)) hz).symm
  have hmax : max (r^(-β)) ((2*r)^(-β)) = max 1 ((2:ℝ)^(-β)) * r^(-β) := by
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hr.le]
    simpa only [one_mul] using (max_mul_of_nonneg 1 ((2:ℝ)^(-β)) hz).symm
  have hb (k : GW.Space) (hk : k ∈ exteriorAnnulus R m) :=
    rpow_endpoint_bounds (z := -β) hr hk.1.le (hk.2.trans_eq (exteriorRadius_succ R m))
  have hh := radialPowerIntegral_bounds β (exteriorAnnulus_measurable R m)
    (fun k hk => (hmin.symm.le.trans (hb k hk).1)) (fun k hk => (hb k hk).2.trans hmax.le)
  rw [exteriorAnnulus_volume hR m] at hh
  have hv : 0 ≤ 7 * unitBallVolume * r^3 := mul_nonneg (mul_nonneg (by norm_num) unitBallVolume_pos.le) (pow_nonneg hr.le 3)
  have hn : 0 ≤ min 1 ((2:ℝ)^(-β)) * r^(-β) := by positivity
  have hm : 0 ≤ max 1 ((2:ℝ)^(-β)) * r^(-β) := by positivity
  rw [← ENNReal.ofReal_mul hn,← ENNReal.ofReal_mul hm] at hh
  have he : r^3 * r^(-β) = r^(3-β) := by
    rw [← Real.rpow_natCast r 3,← Real.rpow_add hr]
    congr 1
  constructor
  · convert hh.1 using 2
    rw [← he]
    ring
  · convert hh.2 using 2
    rw [← he]
    ring

lemma interiorAnnulus_power_bounds {R : ℝ} (hR : 0 < R) (β : ℝ) (m : ℕ) :
    let r := interiorRadius R m
    ENNReal.ofReal ((7/8) * unitBallVolume * min 1 ((2:ℝ)^β) * r^(3-β)) ≤
        radialPowerIntegral β (interiorAnnulus R m) ∧
      radialPowerIntegral β (interiorAnnulus R m) ≤
        ENNReal.ofReal ((7/8) * unitBallVolume * max 1 ((2:ℝ)^β) * r^(3-β)) := by
  let r := interiorRadius R m
  have hr : 0 < r := interiorRadius_pos hR m
  have hz : 0 ≤ r^(-β) := Real.rpow_nonneg hr.le _
  have hpow : (r/2)^(-β) = (2:ℝ)^β * r^(-β) := by
    rw [Real.div_rpow hr.le (by norm_num : (0:ℝ) ≤ 2),
      Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),div_inv_eq_mul,mul_comm]
  have hmin : min ((r/2)^(-β)) (r^(-β)) = min 1 ((2:ℝ)^β) * r^(-β) := by
    rw [min_comm,hpow]
    simpa only [one_mul] using (min_mul_of_nonneg 1 ((2:ℝ)^β) hz).symm
  have hmax : max ((r/2)^(-β)) (r^(-β)) = max 1 ((2:ℝ)^β) * r^(-β) := by
    rw [max_comm,hpow]
    simpa only [one_mul] using (max_mul_of_nonneg 1 ((2:ℝ)^β) hz).symm
  have hb (k : GW.Space) (hk : k ∈ interiorAnnulus R m) :=
    rpow_endpoint_bounds (z := -β) (div_pos hr (by norm_num))
      ((interiorRadius_succ R m).symm.le.trans hk.1.le) hk.2
  have hh := radialPowerIntegral_bounds β (interiorAnnulus_measurable R m)
    (fun k hk => hmin.symm.le.trans (hb k hk).1) (fun k hk => (hb k hk).2.trans hmax.le)
  rw [interiorAnnulus_volume hR m] at hh
  have hn : 0 ≤ min 1 ((2:ℝ)^β) * r^(-β) := by positivity
  have hm : 0 ≤ max 1 ((2:ℝ)^β) * r^(-β) := by positivity
  rw [← ENNReal.ofReal_mul hn,← ENNReal.ofReal_mul hm] at hh
  have he : r^3 * r^(-β) = r^(3-β) := by
    rw [← Real.rpow_natCast r 3,← Real.rpow_add hr]
    congr 1
  constructor
  · convert hh.1 using 2
    rw [← he]
    ring
  · convert hh.2 using 2
    rw [← he]
    ring

def exteriorPowerIntegral (β R : ℝ) : ℝ≥0∞ := radialPowerIntegral β {k | R < ‖k‖}
def interiorPowerIntegral (β R : ℝ) : ℝ≥0∞ := radialPowerIntegral β {k | 0 < ‖k‖ ∧ ‖k‖ ≤ R}

lemma exteriorPowerIntegral_tsum {R : ℝ} (hR : 0 < R) (β : ℝ) :
    exteriorPowerIntegral β R = ∑' m, radialPowerIntegral β (exteriorAnnulus R m) := by
  unfold exteriorPowerIntegral radialPowerIntegral
  rw [← exteriorAnnulus_union hR,
    lintegral_iUnion (exteriorAnnulus_measurable R) (exteriorAnnulus_disjoint hR)]

lemma interiorPowerIntegral_tsum {R : ℝ} (hR : 0 < R) (β : ℝ) :
    interiorPowerIntegral β R = ∑' m, radialPowerIntegral β (interiorAnnulus R m) := by
  unfold interiorPowerIntegral radialPowerIntegral
  rw [← interiorAnnulus_union hR,
    lintegral_iUnion (interiorAnnulus_measurable R) (interiorAnnulus_disjoint hR)]

lemma dyadic_power_factor {R q : ℝ} (hR : 0 ≤ R) (hq : 0 ≤ q) (m : ℕ) (z : ℝ) :
    (R * q^m)^z = R^z * (q^z)^m := by
  rw [Real.mul_rpow hR (pow_nonneg hq _),← Real.rpow_natCast q m,← Real.rpow_mul hq,
    mul_comm (m:ℝ) z,Real.rpow_mul hq,Real.rpow_natCast]

lemma scaled_geometric_tsum {c qratio : ℝ} (hc : 0 ≤ c) (hqratio : 0 ≤ qratio) (hqratio1 : qratio < 1) :
    (∑' m : ℕ, ENNReal.ofReal (c*qratio^m)) = ENNReal.ofReal (c/(1-qratio)) := by
  have hs : HasSum (fun m : ℕ => c * qratio^m) (c * (1-qratio)⁻¹) :=
    (hasSum_geometric_of_norm_lt_one (by simpa [Real.norm_eq_abs,abs_of_nonneg hqratio] using hqratio1)).mul_left c
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => mul_nonneg hc (pow_nonneg hqratio m)) hs.summable,
    hs.tsum_eq,div_eq_mul_inv]

lemma geometric_upper_finite {f : ℕ → ℝ≥0∞} {C qratio : ℝ}
    (hC : 0 ≤ C) (hqratio : 0 ≤ qratio) (hqratio1 : qratio < 1)
    (h : ∀ m, f m ≤ ENNReal.ofReal (C*qratio^m)) : (∑' m, f m) < ∞ := by
  refine (tsum_le_tsum h).trans_lt ?_
  rw [scaled_geometric_tsum hC hqratio hqratio1]
  exact ENNReal.ofReal_lt_top

lemma geometric_lower_infinite {f : ℕ → ℝ≥0∞} {c qratio : ℝ}
    (hc : 0 < c) (hqratio : 1 ≤ qratio)
    (h : ∀ m, ENNReal.ofReal (c*qratio^m) ≤ f m) : (∑' m, f m) = ∞ := by
  apply top_unique
  have hm (m : ℕ) : ENNReal.ofReal c ≤ f m :=
    (ENNReal.ofReal_le_ofReal (by
      have hp : 1 ≤ qratio^m := one_le_pow₀ hqratio
      nlinarith)).trans (h m)
  have ht : (∑' _m : ℕ, ENNReal.ofReal c) = ∞ :=
    ENNReal.tsum_const_eq_top_of_ne_zero (ENNReal.ofReal_pos.mpr hc).ne'
  exact ht ▸ tsum_le_tsum hm

lemma dyadic_series_finite_iff {f : ℕ → ℝ≥0∞} {R q c C z : ℝ}
    (hR : 0 < R) (hq : 0 < q) (hc : 0 < c) (hC : 0 ≤ C)
    (hl : ∀ m, ENNReal.ofReal (c*(R*q^m)^z) ≤ f m)
    (hu : ∀ m, f m ≤ ENNReal.ofReal (C*(R*q^m)^z)) :
    (∑' m, f m) < ∞ ↔ q^z < 1 := by
  have hpos := Real.rpow_pos_of_pos hR z
  have hl' (m : ℕ) : ENNReal.ofReal ((c*R^z)*(q^z)^m) ≤ f m := by
    rw [mul_assoc,← dyadic_power_factor hR.le hq.le]
    exact hl m
  have hu' (m : ℕ) : f m ≤ ENNReal.ofReal ((C*R^z)*(q^z)^m) := by
    rw [mul_assoc,← dyadic_power_factor hR.le hq.le]
    exact hu m
  constructor
  · intro h
    by_contra! hh
    have he := geometric_lower_infinite (mul_pos hc hpos) hh hl'
    exact h.ne he
  · intro h
    exact geometric_upper_finite (mul_nonneg hC hpos.le) (Real.rpow_nonneg hq.le _) h hu'

lemma exteriorPowerIntegral_finite_iff {R : ℝ} (hR : 0 < R) (β : ℝ) :
    exteriorPowerIntegral β R < ∞ ↔ 3 < β := by
  rw [exteriorPowerIntegral_tsum hR]
  have h := dyadic_series_finite_iff (R := R) (q := 2) (z := 3-β)
    hR (by norm_num) (mul_pos (mul_pos (by norm_num) unitBallVolume_pos)
      (lt_min zero_lt_one (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) _)))
    (mul_nonneg (mul_nonneg (by norm_num) unitBallVolume_pos.le)
      (le_trans zero_le_one (le_max_left _ _)))
    (fun m => (exteriorAnnulus_power_bounds hR β m).1)
    (fun m => (exteriorAnnulus_power_bounds hR β m).2)
  rw [h,Real.rpow_lt_one_iff_of_pos (by norm_num : (0:ℝ) < 2)]
  norm_num

lemma interiorPowerIntegral_finite_iff {R : ℝ} (hR : 0 < R) (β : ℝ) :
    interiorPowerIntegral β R < ∞ ↔ β < 3 := by
  rw [interiorPowerIntegral_tsum hR]
  have h := dyadic_series_finite_iff (R := R) (q := 1/2) (z := 3-β)
    hR (by norm_num) (mul_pos (mul_pos (by norm_num) unitBallVolume_pos)
      (lt_min zero_lt_one (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) _)))
    (mul_nonneg (mul_nonneg (by norm_num) unitBallVolume_pos.le)
      (le_trans zero_le_one (le_max_left _ _)))
    (fun m => (interiorAnnulus_power_bounds hR β m).1)
    (fun m => (interiorAnnulus_power_bounds hR β m).2)
  rw [h,Real.rpow_lt_one_iff_of_pos (by norm_num : (0:ℝ) < 1/2)]
  norm_num

lemma exteriorAnnulus_critical_lower {R : ℝ} (hR : 0 < R) (m : ℕ) :
    ENNReal.ofReal (7*unitBallVolume/8) ≤ radialPowerIntegral 3 (exteriorAnnulus R m) := by
  have h := (exteriorAnnulus_power_bounds hR 3 m).1
  have hcoef : (2:ℝ)^(-(3:ℝ)) = 1/8 := by
    rw [Real.rpow_neg (by norm_num),Real.rpow_ofNat]
    norm_num
  rw [hcoef, min_eq_right (by norm_num),sub_self,Real.rpow_zero,mul_one] at h
  convert h using 2 <;> ring

lemma exteriorPowerIntegral_critical {R : ℝ} (hR : 0 < R) :
    exteriorPowerIntegral 3 R = ∞ :=
  not_lt_top_iff.mp (fun h => (lt_irrefl 3) ((exteriorPowerIntegral_finite_iff hR 3).mp h))

lemma exteriorPowerIntegral_four_bound {R : ℝ} (hR : 0 < R) :
    exteriorPowerIntegral 4 R ≤ ENNReal.ofReal (14*unitBallVolume/R) := by
  rw [exteriorPowerIntegral_tsum hR]
  have h (m : ℕ) : radialPowerIntegral 4 (exteriorAnnulus R m) ≤
      ENNReal.ofReal ((7*unitBallVolume/R)*(1/2:ℝ)^m) := by
    have hh := (exteriorAnnulus_power_bounds hR 4 m).2
    have hc : (2:ℝ)^(-(4:ℝ)) = 1/16 := by
      rw [Real.rpow_neg (by norm_num),Real.rpow_ofNat]
      norm_num
    rw [hc,max_eq_left (by norm_num),mul_one] at hh
    have he : (3:ℝ)-4 = -1 := by norm_num
    rw [he] at hh
    change _ ≤ ENNReal.ofReal (7*unitBallVolume * (R * (2:ℝ)^m)^(-1:ℝ)) at hh
    rw [dyadic_power_factor hR.le (by norm_num : (0:ℝ) ≤ 2),Real.rpow_neg_one,
      Real.rpow_neg_one,← mul_assoc,← div_eq_mul_inv] at hh
    norm_num at hh ⊢
    exact hh
  refine (tsum_le_tsum h).trans_eq ?_
  rw [scaled_geometric_tsum (div_nonneg (mul_nonneg (by norm_num) unitBallVolume_pos.le) hR.le)
    (by norm_num) (by norm_num)]
  congr 1
  ring

lemma interiorPowerIntegral_two_bound {R : ℝ} (hR : 0 < R) :
    interiorPowerIntegral 2 R ≤ ENNReal.ofReal (7*unitBallVolume*R) := by
  rw [interiorPowerIntegral_tsum hR]
  have h (m : ℕ) : radialPowerIntegral 2 (interiorAnnulus R m) ≤
      ENNReal.ofReal (((7/2)*unitBallVolume*R)*(1/2:ℝ)^m) := by
    have hh := (interiorAnnulus_power_bounds hR 2 m).2
    have hc : (2:ℝ)^(2:ℝ) = 4 := by rw [Real.rpow_ofNat]; norm_num
    rw [hc,max_eq_right (by norm_num)] at hh
    have he : (3:ℝ)-2 = 1 := by norm_num
    rw [he,Real.rpow_one] at hh
    refine hh.trans_eq ?_
    congr 1
    unfold interiorRadius
    ring
  refine (tsum_le_tsum h).trans_eq ?_
  rw [scaled_geometric_tsum (mul_nonneg (mul_nonneg (by norm_num) unitBallVolume_pos.le) hR.le)
    (by norm_num) (by norm_num)]
  congr 1
  ring

end GW.Model
