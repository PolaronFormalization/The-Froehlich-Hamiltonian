module
public import GW.Spaces.WeightedL2
public import GW.Analysis.RealMultiplier
public import GW.Spaces.WeightedCarrier
public import GW.Fock.FockAmplification
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.WithDensity
@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped Topology InnerProductSpace ENNReal
namespace GW.Operators

set_option backward.isDefEq.respectTransparency.types false in
lemma quadraticKPoint_square_completion {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u a : H) (c : ℝ) (hc : 0 ≤ c) :
    ‖u-a‖^2+c*‖a‖^2 =
      (1+c)*‖a-(1+c)⁻¹ • u‖^2 + c/(1+c)*‖u‖^2 := by
  have hp : 0 < 1+c := by linarith
  rw [norm_sub_sq_real,norm_sub_sq_real,real_inner_smul_right,norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr hp.le),real_inner_comm a u]
  field_simp
  <;> ring

def kMinimizerCoefficient (w t : ℝ) : ℝ := (1+t^2*w^2)⁻¹

lemma kMinimizerCoefficient_bound (w t : ℝ) : 0 ≤ kMinimizerCoefficient w t ∧ kMinimizerCoefficient w t ≤ 1 := by
  have h : 0 ≤ t^2*w^2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  exact ⟨inv_nonneg.mpr (by linarith),(inv_le_one₀ (by linarith)).mpr (by linarith)⟩

lemma kMinimizerWeighted_bound (w t : ℝ) (hw : 1 ≤ w) (ht : 0 < t) :
    0 ≤ w*kMinimizerCoefficient w t ∧ w*kMinimizerCoefficient w t ≤ (2*t)⁻¹ := by
  have hden : 0 < 1+t^2*w^2 := by positivity
  have htw : 0 < 2*t := by positivity
  refine ⟨mul_nonneg (zero_le_one.trans hw) (kMinimizerCoefficient_bound w t).1,?_⟩
  unfold kMinimizerCoefficient
  rw [← div_eq_mul_inv,inv_eq_one_div]
  apply (div_le_div_iff₀ hden htw).mpr
  nlinarith [sq_nonneg (t*w-1)]

section Minimizer
variable {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (μ : Measure X) (w : X → ℝ) (hw : Measurable w) (hw1 : ∀ x, 1 ≤ w x)

local instance : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H

def kMinimizerMap (t : ℝ) : Lp H 2 μ →L[ℂ] Lp H 2 μ :=
  GW.Analysis.boundedMultiplier (fun x => (kMinimizerCoefficient (w x) t : ℂ))
    (Complex.continuous_ofReal.measurable.comp
      ((measurable_const.add (measurable_const.mul (hw.pow_const 2))).inv))
    (C := 1) (Eventually.of_forall (fun x => by
      rw [Complex.norm_real,Real.norm_of_nonneg (kMinimizerCoefficient_bound _ _).1]
      exact (kMinimizerCoefficient_bound _ _).2))

lemma kMinimizerMap_ae (t : ℝ) (u : Lp H 2 μ) :
    kMinimizerMap μ w hw t u =ᵐ[μ] fun x => (kMinimizerCoefficient (w x) t : ℂ) • u x :=
  (GW.Analysis.boundedMultiplier_ae _ _ _ u).symm

def kMinimizerWeightedMap (t : ℝ) (ht : 0 < t) : Lp H 2 μ →L[ℂ] Lp H 2 μ :=
  GW.Analysis.boundedMultiplier (fun x => ((w x*kMinimizerCoefficient (w x) t : ℝ) : ℂ))
    (Complex.continuous_ofReal.measurable.comp
      (hw.mul ((measurable_const.add (measurable_const.mul (hw.pow_const 2))).inv)))
    (C := (2*t)⁻¹) (Eventually.of_forall (fun x => by
      rw [Complex.norm_real,Real.norm_of_nonneg (kMinimizerWeighted_bound (w x) t (hw1 x) ht).1]
      exact (kMinimizerWeighted_bound (w x) t (hw1 x) ht).2))

include hw1 in
lemma kMinimizerMap_mem (t : ℝ) (ht : 0 < t) (u : Lp H 2 μ) :
    kMinimizerMap μ w hw t u ∈ (GW.Analysis.realMultiplier (H := H) w μ).domain := by
  refine ⟨kMinimizerWeightedMap μ w hw hw1 t ht u,?_⟩
  filter_upwards [kMinimizerMap_ae μ w hw t u,
    GW.Analysis.boundedMultiplier_ae (fun x => ((w x*kMinimizerCoefficient (w x) t : ℝ) : ℂ)) _ _ u] with x h₁ h₂
  change (w x : ℂ) • kMinimizerMap μ w hw t u x =
    GW.Analysis.boundedMultiplier (fun x => ((w x*kMinimizerCoefficient (w x) t : ℝ) : ℂ)) _ _ u x
  rw [h₁,← h₂,Complex.ofReal_mul,mul_smul]

def kMinimizer (t : ℝ) (ht : 0 < t) (u : Lp H 2 μ) :
    (GW.Analysis.realMultiplier (H := H) w μ).domain :=
  ⟨kMinimizerMap μ w hw t u,kMinimizerMap_mem μ w hw hw1 t ht u⟩

def quadraticKCost (t : ℝ) (u : Lp H 2 μ) (a : (GW.Analysis.realMultiplier (H := H) w μ).domain) : ℝ :=
  ‖u-a.val‖^2 + t^2*‖GW.Analysis.realMultiplier w μ a‖^2

def quadraticKSquared (t : ℝ) (u : Lp H 2 μ) : ℝ :=
  sInf (Set.range (quadraticKCost μ w t u))

lemma quadraticKCost_nonneg (t : ℝ) (u : Lp H 2 μ) (a : (GW.Analysis.realMultiplier (H := H) w μ).domain) :
    0 ≤ quadraticKCost μ w t u a :=
  add_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (sq_nonneg _))

lemma quadraticKCost_integral (t : ℝ) (u : Lp H 2 μ) (a : (GW.Analysis.realMultiplier (H := H) w μ).domain) :
    quadraticKCost μ w t u a =
      ∫ x, ‖u x-a.val x‖^2+t^2*(w x)^2*‖a.val x‖^2 ∂μ := by
  have hi₁ := (Lp.memLp (u-a.val)).integrable_norm_pow (p := 2) (by norm_num)
  have hi₂ := (Lp.memLp (GW.Analysis.realMultiplier w μ a)).integrable_norm_pow (p := 2) (by norm_num)
  unfold quadraticKCost
  rw [GW.Analysis.l2_norm_sq (𝕜 := ℂ),GW.Analysis.l2_norm_sq (𝕜 := ℂ),← integral_const_mul,
    ← integral_add hi₁ (hi₂.const_mul (t^2))]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub u a.val,GW.Analysis.realMultiplier_ae w a] with x h₁ h₂
  change ‖(u-a.val) x‖^2+t^2*‖GW.Analysis.realMultiplier w μ a x‖^2 = _
  rw [h₁]
  change ‖u x-a.val x‖^2+t^2*‖GW.Analysis.realMultiplier w μ a x‖^2 = _
  rw [← h₂,norm_smul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  ring

def quadraticKDensity (t : ℝ) (u : Lp H 2 μ) (x : X) : ℝ :=
  (t^2*(w x)^2/(1+t^2*(w x)^2))*‖u x‖^2

lemma quadraticKDensity_nonneg (t : ℝ) (u : Lp H 2 μ) (x : X) :
    0 ≤ quadraticKDensity μ w t u x := by
  unfold quadraticKDensity
  positivity

lemma quadraticKDensity_le (t : ℝ) (u : Lp H 2 μ) (x : X) :
    quadraticKDensity μ w t u x ≤ ‖u x‖^2 := by
  have hp : 0 < 1+t^2*(w x)^2 := by positivity
  have hq : t^2*(w x)^2/(1+t^2*(w x)^2) ≤ 1 := by
    apply (div_le_iff₀ hp).mpr
    linarith
  exact mul_le_of_le_one_left (sq_nonneg _) hq

include hw in
lemma quadraticKDensity_integrable (t : ℝ) (u : Lp H 2 μ) :
    Integrable (quadraticKDensity μ w t u) μ := by
  have hm : AEStronglyMeasurable (quadraticKDensity μ w t u) μ :=
    ((measurable_const.mul (hw.pow_const 2)).div
      (measurable_const.add (measurable_const.mul (hw.pow_const 2)))).aestronglyMeasurable.mul
        ((Lp.aestronglyMeasurable u).norm.pow 2)
  apply ((Lp.memLp u).integrable_norm_pow (p := 2) (by norm_num)).mono' hm
  exact Eventually.of_forall (fun x => by
    rw [Real.norm_of_nonneg (quadraticKDensity_nonneg μ w t u x)]
    exact quadraticKDensity_le μ w t u x)

lemma quadraticKCost_pointwise_lower (t : ℝ) (u a : H) (w : ℝ) :
    t^2*w^2/(1+t^2*w^2)*‖u‖^2 ≤ ‖u-a‖^2+t^2*w^2*‖a‖^2 := by
  rw [quadraticKPoint_square_completion u a (t^2*w^2) (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
  exact le_add_of_nonneg_left (mul_nonneg (by positivity) (sq_nonneg _))

include hw in
lemma quadraticKCost_lower (t : ℝ) (u : Lp H 2 μ) (a : (GW.Analysis.realMultiplier (H := H) w μ).domain) :
    (∫ x, quadraticKDensity μ w t u x ∂μ) ≤ quadraticKCost μ w t u a := by
  rw [quadraticKCost_integral]
  have hi₁ := (Lp.memLp (u-a.val)).integrable_norm_pow (p := 2) (by norm_num)
  have hi₂ := ((Lp.memLp (GW.Analysis.realMultiplier w μ a)).integrable_norm_pow (p := 2) (by norm_num)).const_mul (t^2)
  have hcost : Integrable (fun x => ‖u x-a.val x‖^2+t^2*(w x)^2*‖a.val x‖^2) μ := by
    apply (hi₁.add hi₂).congr
    filter_upwards [Lp.coeFn_sub u a.val,GW.Analysis.realMultiplier_ae w a] with x hx hy
    change ‖(u-a.val) x‖^2+t^2*‖GW.Analysis.realMultiplier w μ a x‖^2 = _
    rw [hx]
    change ‖u x-a.val x‖^2+t^2*‖GW.Analysis.realMultiplier w μ a x‖^2 = _
    rw [← hy,norm_smul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
    ring
  exact integral_mono (quadraticKDensity_integrable μ w hw t u) hcost
    (fun x => quadraticKCost_pointwise_lower t (u x) (a.val x) (w x))

include hw hw1 in
lemma quadraticKCost_minimizer (t : ℝ) (ht : 0 < t) (u : Lp H 2 μ) :
    quadraticKCost μ w t u (kMinimizer μ w hw hw1 t ht u) =
      ∫ x, quadraticKDensity μ w t u x ∂μ := by
  rw [quadraticKCost_integral]
  apply integral_congr_ae
  filter_upwards [kMinimizerMap_ae μ w hw t u] with x hx
  change ‖u x-kMinimizerMap μ w hw t u x‖^2+t^2*(w x)^2*‖kMinimizerMap μ w hw t u x‖^2 = _
  rw [hx]
  have hc := quadraticKPoint_square_completion (u x) ((kMinimizerCoefficient (w x) t : ℂ) • u x)
    (t^2*(w x)^2) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  rw [hc]
  have he : (kMinimizerCoefficient (w x) t : ℂ) • u x =
      (1+t^2*(w x)^2)⁻¹ • u x :=
    (RCLike.real_smul_eq_coe_smul (K := ℂ) (kMinimizerCoefficient (w x) t) (u x)).symm
  rw [he,sub_self,norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0),mul_zero,zero_add]
  rfl

include hw hw1 in
lemma quadraticKSquared_eq (t : ℝ) (ht : 0 < t) (u : Lp H 2 μ) :
    quadraticKSquared μ w t u = ∫ x, quadraticKDensity μ w t u x ∂μ := by
  have hb : BddBelow (Set.range (quadraticKCost μ w t u)) :=
    ⟨0,fun _ hx => by obtain ⟨a,rfl⟩ := hx; exact quadraticKCost_nonneg μ w t u a⟩
  apply le_antisymm
  · exact (csInf_le hb (Set.mem_range_self (kMinimizer μ w hw hw1 t ht u))).trans_eq
      (quadraticKCost_minimizer μ w hw hw1 t ht u)
  · apply le_csInf (Set.range_nonempty _)
    rintro y ⟨a,rfl⟩
    exact quadraticKCost_lower μ w hw t u a

end Minimizer
def interpolationDensity (θ r : ℝ) : ℝ := r ^ (1-2*θ) / (1+r^2)

def interpolationConstant (θ : ℝ) : ℝ := ∫ r in Ioi (0:ℝ), interpolationDensity θ r

lemma interpolationDensity_nonneg (θ r : ℝ) (hr : 0 ≤ r) : 0 ≤ interpolationDensity θ r := by
  exact div_nonneg (Real.rpow_nonneg hr _) (by positivity)

lemma interpolationDensity_near_bound (θ r : ℝ) (hr : 0 ≤ r) :
    interpolationDensity θ r ≤ r ^ (1-2*θ) := by
  unfold interpolationDensity
  exact div_le_self (Real.rpow_nonneg hr _) (by nlinarith [sq_nonneg r])

lemma interpolationDensity_far_bound (θ r : ℝ) (hr : 1 ≤ r) :
    interpolationDensity θ r ≤ r ^ (-1-2*θ) := by
  have hp : 0 < r := zero_lt_one.trans_le hr
  calc
    interpolationDensity θ r ≤ r ^ (1-2*θ) / r^2 := by
      apply div_le_div_of_nonneg_left (Real.rpow_nonneg hp.le _) (sq_pos_of_pos hp)
      nlinarith [sq_nonneg r]
    _ = r ^ (-1-2*θ) := by
      rw [← Real.rpow_natCast r 2, ← Real.rpow_sub hp]
      congr 1
      ring

lemma interpolationDensity_integrable (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    IntegrableOn (interpolationDensity θ) (Ioi 0) := by
  have hm : Measurable (interpolationDensity θ) := by
    unfold interpolationDensity
    fun_prop
  have hnear : IntegrableOn (interpolationDensity θ) (Ioo 0 1) := by
    apply ((intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0:ℝ)<1)).mpr
      (show -1 < 1-2*θ by linarith)).mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    rw [Real.norm_of_nonneg (interpolationDensity_nonneg θ r hr.1.le)]
    exact interpolationDensity_near_bound θ r hr.1.le
  have hfar : IntegrableOn (interpolationDensity θ) (Ioi 1) := by
    apply (integrableOn_Ioi_rpow_of_lt (show -1-2*θ < -1 by linarith)
      (by norm_num : (0:ℝ)<1)).mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    rw [Real.norm_of_nonneg (interpolationDensity_nonneg θ r (zero_le_one.trans hr.le))]
    exact interpolationDensity_far_bound θ r hr.le
  have hu := hnear.union hfar
  apply (integrableOn_congr_set_ae (f := interpolationDensity θ) ?_).mp hu
  have hn : ∀ᵐ r : ℝ ∂volume, r ≠ 1 := by simp [ae_iff]
  filter_upwards [hn] with r hr
  simp only [mem_union,mem_Ioo,mem_Ioi]
  constructor
  · rintro (⟨h,_⟩ | h)
    · exact h
    · linarith
  · intro h
    rcases lt_or_gt_of_ne hr with hlt | hgt
    · exact Or.inl ⟨h,hlt⟩
    · exact Or.inr hgt

lemma interpolationDensity_interval_lower (θ r : ℝ) (hr : r ∈ Icc 1 2) :
    min 1 (2 ^ (1-2*θ)) / 5 ≤ interpolationDensity θ r := by
  have hp : 0 < r := zero_lt_one.trans_le hr.1
  have hl : min 1 (2 ^ (1-2*θ)) ≤ r ^ (1-2*θ) := by
    by_cases he : 0 ≤ 1-2*θ
    · exact (min_le_left _ _).trans (Real.one_le_rpow hr.1 he)
    · exact (min_le_right _ _).trans (Real.rpow_le_rpow_of_nonpos hp hr.2 (le_of_not_ge he))
  have hn : 0 ≤ min (1:ℝ) (2 ^ (1-2*θ)) := le_min zero_le_one (Real.rpow_nonneg (by norm_num) _)
  have hd : 0 < 1+r^2 := by positivity
  unfold interpolationDensity
  apply (div_le_div_iff₀ (by norm_num : (0:ℝ)<5) hd).mpr
  have hb : 1+r^2 ≤ 5 := by nlinarith [hr.1,hr.2]
  nlinarith [mul_le_mul_of_nonneg_left hb hn]

lemma interpolationConstant_pos (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    0 < interpolationConstant θ := by
  let b := min (1:ℝ) (2 ^ (1-2*θ)) / 5
  have hb : 0 < b := div_pos (lt_min zero_lt_one (Real.rpow_pos_of_pos (by norm_num) _)) (by norm_num)
  have hi := interpolationDensity_integrable θ hθ0 hθ1
  have hrestrict : IntegrableOn (interpolationDensity θ) (Icc 1 2) :=
    hi.mono_set (fun r hr => zero_lt_one.trans_le hr.1)
  have hlow : b ≤ ∫ r in Icc (1:ℝ) 2, interpolationDensity θ r := by
    calc
      b = ∫ _ : ℝ in Icc (1:ℝ) 2, b := by simp; ring
      _ ≤ _ := integral_mono_ae (integrable_const b) hrestrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact interpolationDensity_interval_lower θ r hr
  have hsub : (∫ r in Icc (1:ℝ) 2, interpolationDensity θ r) ≤ interpolationConstant θ := by
    apply integral_mono_measure ?_ ?_ hi
    · exact Measure.restrict_mono_set _ (fun r hr => zero_lt_one.trans_le hr.1)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      exact interpolationDensity_nonneg θ r hr.le
  exact hb.trans_le (hlow.trans hsub)

section Endpoint
variable {X Y H G : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]
  (μ : Measure X) (ν : Measure Y) (w : X → ℝ) (v : Y → ℝ)
  (hw : Measurable w) (hw1 : ∀ x, 1 ≤ w x)
  (T : Lp H 2 μ →L[ℂ] Lp G 2 ν) (M₀ M₁ : ℝ)
  (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
  (hT₀ : ∀ z, ‖T z‖ ≤ M₀*‖z‖)
  (hT₁ : ∀ a : (GW.Analysis.realMultiplier (H := H) w μ).domain,
    ∃ b : (GW.Analysis.realMultiplier (H := G) v ν).domain,
      b.val = T a.val ∧ ‖GW.Analysis.realMultiplier v ν b‖ ≤ M₁*‖GW.Analysis.realMultiplier w μ a‖)

include hw hw1 hM₀ hM₁ hT₀ hT₁ in
lemma quadraticKSquared_endpoint (t : ℝ) (ht : 0 < t) (u : Lp H 2 μ) :
    quadraticKSquared ν v t (T u) ≤ M₀^2*quadraticKSquared μ w (t*M₁/M₀) u := by
  let s := t*M₁/M₀
  have hs : 0 < s := div_pos (mul_pos ht hM₁) hM₀
  let a := kMinimizer μ w hw hw1 s hs u
  obtain ⟨b,hb,hbnd⟩ := hT₁ a
  have hbelow : BddBelow (Set.range (quadraticKCost ν v t (T u))) :=
    ⟨0,fun _ hz => by obtain ⟨z,rfl⟩ := hz; exact quadraticKCost_nonneg ν v t (T u) z⟩
  have hle : quadraticKSquared ν v t (T u) ≤ quadraticKCost ν v t (T u) b :=
    csInf_le hbelow (Set.mem_range_self b)
  have hzero := hT₀ (u-a.val)
  rw [map_sub] at hzero
  have hsq₀ := sq_le_sq₀ (norm_nonneg (T u-T a.val)) (mul_nonneg hM₀.le (norm_nonneg _)) |>.mpr hzero
  have hsq₁ := sq_le_sq₀ (norm_nonneg (GW.Analysis.realMultiplier v ν b))
    (mul_nonneg hM₁.le (norm_nonneg _)) |>.mpr hbnd
  have hcost : quadraticKCost ν v t (T u) b ≤ M₀^2 * quadraticKCost μ w s u a := by
    unfold quadraticKCost
    rw [hb]
    have hscale : M₀^2*s^2 = t^2*M₁^2 := by dsimp [s]; field_simp <;> ring
    nlinarith [mul_le_mul_of_nonneg_left hsq₁ (sq_nonneg t)]
  apply (hle.trans hcost).trans_eq
  congr 1
  exact (quadraticKCost_minimizer μ w hw hw1 s hs u).trans
    (quadraticKSquared_eq μ w hw hw1 s hs u).symm

end Endpoint
lemma positiveHalfLine_scaling (a : ℝ) (ha : 0 < a) (f : ℝ → ℝ≥0∞) :
    (∫⁻ t in Ioi (0:ℝ), f (a*t)) =
      ENNReal.ofReal a⁻¹ * ∫⁻ r in Ioi (0:ℝ), f r := by
  have hp : (fun t : ℝ => a*t) ⁻¹' Ioi (0:ℝ) = Ioi 0 := by
    ext t
    simp only [mem_preimage,mem_Ioi,mul_pos_iff_of_pos_left ha]
  have hm : Measure.map (fun t : ℝ => a*t) (volume.restrict (Ioi 0)) =
      ENNReal.ofReal a⁻¹ • (volume : Measure ℝ).restrict (Ioi 0) := by
    rw [← hp,← Measure.restrict_map (measurable_const_mul a) measurableSet_Ioi,
      Real.map_volume_mul_left ha.ne',Measure.restrict_smul,abs_of_pos (inv_pos.mpr ha),hp]
  rw [← (measurableEmbedding_mulLeft₀ ha.ne').lintegral_map f,hm,lintegral_smul_measure]
  rfl

lemma interpolationDensity_scaled (θ a t : ℝ) (ha : 0 < a) (ht : 0 < t) :
    t ^ (-2*θ-1) * (t^2*a^2/(1+t^2*a^2)) =
      a ^ (1+2*θ) * interpolationDensity θ (a*t) := by
  have he₁ : t ^ (-2*θ-1) * t^2 = t ^ (1-2*θ) := by
    rw [← Real.rpow_natCast t 2,← Real.rpow_add ht]
    congr 1
    ring
  have he₂ : a ^ (1+2*θ) * a ^ (1-2*θ) = a^2 := by
    rw [← Real.rpow_add ha]
    convert Real.rpow_natCast a 2 using 1 <;> ring
  unfold interpolationDensity
  rw [Real.mul_rpow ha.le ht.le]
  have hd : 1+(a*t)^2 = 1+t^2*a^2 := by ring
  rw [hd]
  calc
    _ = (t ^ (-2*θ-1)*t^2)*a^2/(1+t^2*a^2) := by ring
    _ = (a ^ (1+2*θ)*a ^ (1-2*θ))*t ^ (1-2*θ)/(1+t^2*a^2) := by rw [he₁,he₂]; ring
    _ = _ := by ring

lemma interpolationConstant_extended (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    (∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal (interpolationDensity θ r)) =
      ENNReal.ofReal (interpolationConstant θ) := by
  symm
  apply ofReal_integral_eq_lintegral_ofReal (interpolationDensity_integrable θ hθ0 hθ1)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  exact interpolationDensity_nonneg θ r hr.le

lemma interpolationScalar_extended (θ a : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (ha : 0 < a) :
    (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal
      (t ^ (-2*θ-1)*(t^2*a^2/(1+t^2*a^2)))) =
      ENNReal.ofReal (a ^ (2*θ)) * ENNReal.ofReal (interpolationConstant θ) := by
  have hm : Measurable (fun r => ENNReal.ofReal (interpolationDensity θ r)) := by
    unfold interpolationDensity
    fun_prop
  have he : a ^ (1+2*θ) * a⁻¹ = a ^ (2*θ) := by
    rw [← Real.rpow_neg_one,← Real.rpow_add ha]
    congr 1
    ring
  calc
    _ = ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (a ^ (1+2*θ)) *
        ENNReal.ofReal (interpolationDensity θ (a*t)) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [interpolationDensity_scaled θ a t ha ht,
        ENNReal.ofReal_mul (Real.rpow_nonneg ha.le _)]
    _ = ENNReal.ofReal (a ^ (1+2*θ)) *
        (ENNReal.ofReal a⁻¹ * ENNReal.ofReal (interpolationConstant θ)) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        positiveHalfLine_scaling a ha (fun r => ENNReal.ofReal (interpolationDensity θ r)),interpolationConstant_extended θ hθ0 hθ1]
    _ = _ := by rw [← mul_assoc,← ENNReal.ofReal_mul (Real.rpow_nonneg ha.le _),he]

lemma interpolationTonelli_identity {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] (w q : X → ℝ) (hw : Measurable w) (hq : Measurable q)
    (hwpos : ∀ x, 0 < w x) (hq0 : ∀ x, 0 ≤ q x)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    (∫⁻ t in Ioi (0:ℝ), ∫⁻ x, ENNReal.ofReal
      (t ^ (-2*θ-1)*(t^2*(w x)^2/(1+t^2*(w x)^2))) * ENNReal.ofReal (q x) ∂μ) =
      ENNReal.ofReal (interpolationConstant θ) *
        ∫⁻ x, ENNReal.ofReal ((w x) ^ (2*θ)*q x) ∂μ := by
  have hm : Measurable (fun p : ℝ × X => ENNReal.ofReal
      (p.1 ^ (-2*θ-1)*(p.1^2*(w p.2)^2/(1+p.1^2*(w p.2)^2))) * ENNReal.ofReal (q p.2)) := by
    fun_prop
  rw [lintegral_lintegral_swap hm.aemeasurable]
  calc
    _ = ∫⁻ x, (ENNReal.ofReal ((w x) ^ (2*θ)) *
        ENNReal.ofReal (interpolationConstant θ)) * ENNReal.ofReal (q x) ∂μ := by
      apply lintegral_congr
      intro x
      rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
        interpolationScalar_extended θ (w x) hθ0 hθ1 (hwpos x)]
    _ = ∫⁻ x, ENNReal.ofReal (interpolationConstant θ) *
        ENNReal.ofReal ((w x) ^ (2*θ)*q x) ∂μ := by
      apply lintegral_congr
      intro x
      rw [ENNReal.ofReal_mul (Real.rpow_nonneg (hwpos x).le _)]
      ring
    _ = _ := lintegral_const_mul _ (by fun_prop)

lemma interpolationTonelli_integrableWeight {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (w q : X → ℝ) (hw : Measurable w) (hq : Integrable q μ)
    (hwpos : ∀ x, 0 < w x) (hq0 : ∀ᵐ x ∂μ, 0 ≤ q x)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    (∫⁻ t in Ioi (0:ℝ), ∫⁻ x, ENNReal.ofReal
      (t ^ (-2*θ-1)*(t^2*(w x)^2/(1+t^2*(w x)^2))) * ENNReal.ofReal (q x) ∂μ) =
      ENNReal.ofReal (interpolationConstant θ) *
        ∫⁻ x, ENNReal.ofReal ((w x) ^ (2*θ)*q x) ∂μ := by
  let ρ := μ.withDensity (fun x => ENNReal.ofReal (q x))
  haveI : IsFiniteMeasure ρ := isFiniteMeasure_withDensity
    ((lintegral_ofReal_ne_top_iff_integrable hq.aestronglyMeasurable hq0).mpr hq)
  have hd (f : X → ℝ≥0∞) (hf : Measurable f) :
      (∫⁻ x, f x ∂ρ) = ∫⁻ x, f x * ENNReal.ofReal (q x) ∂μ := by
    rw [lintegral_withDensity_eq_lintegral_mul₀' hq.aestronglyMeasurable.aemeasurable.ennreal_ofReal hf.aemeasurable]
    apply lintegral_congr
    intro x
    exact mul_comm _ _
  have h := interpolationTonelli_identity ρ w (fun _ => 1) hw measurable_const hwpos
    (fun _ => zero_le_one) θ hθ0 hθ1
  simp only [mul_one,ENNReal.ofReal_one,mul_one] at h
  calc
    _ = ∫⁻ t in Ioi (0:ℝ), ∫⁻ x, ENNReal.ofReal
        (t ^ (-2*θ-1)*(t^2*(w x)^2/(1+t^2*(w x)^2))) ∂ρ := by
      apply lintegral_congr
      intro t
      exact (hd _ (by fun_prop)).symm
    _ = _ := by
      rw [h,hd _ (by fun_prop)]
      congr 1
      apply lintegral_congr
      intro x
      exact (ENNReal.ofReal_mul (Real.rpow_nonneg (hwpos x).le _)).symm

lemma quadraticK_extended_identity {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (μ : Measure X) (w : X → ℝ) (hw : Measurable w) (hw1 : ∀ x, 1 ≤ w x)
    (u : Lp H 2 μ) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ (-2*θ-1)) *
      ENNReal.ofReal (quadraticKSquared μ w t u)) =
      ENNReal.ofReal (interpolationConstant θ) *
        ∫⁻ x, ENNReal.ofReal ((w x) ^ (2*θ)*‖u x‖^2) ∂μ := by
  calc
    _ = ∫⁻ t in Ioi (0:ℝ), ∫⁻ x, ENNReal.ofReal
        (t ^ (-2*θ-1)*(t^2*(w x)^2/(1+t^2*(w x)^2))) * ENNReal.ofReal (‖u x‖^2) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [quadraticKSquared_eq μ w hw hw1 t ht u,
        ofReal_integral_eq_lintegral_ofReal (quadraticKDensity_integrable μ w hw t u)
          (Eventually.of_forall (quadraticKDensity_nonneg μ w t u)),
        ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro x
      unfold quadraticKDensity
      have hp : 0 ≤ t ^ (-2*θ-1) := Real.rpow_nonneg ht.le _
      have hq : 0 ≤ t^2*(w x)^2/(1+t^2*(w x)^2) := by positivity
      rw [ENNReal.ofReal_mul hq,ENNReal.ofReal_mul hp,mul_assoc]
    _ = _ := interpolationTonelli_integrableWeight μ w (fun x => ‖u x‖^2) hw
      ((Lp.memLp u).integrable_norm_pow (p := 2) (by norm_num))
      (fun x => zero_lt_one.trans_le (hw1 x)) (Eventually.of_forall (fun _ => sq_nonneg _)) θ hθ0 hθ1

lemma weightedPositiveHalfLine_scaling (θ a : ℝ) (ha : 0 < a) (f : ℝ → ℝ≥0∞) :
    (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ (-2*θ-1))*f (a*t)) =
      ENNReal.ofReal (a ^ (2*θ)) *
        ∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal (r ^ (-2*θ-1))*f r := by
  have he (t : ℝ) (ht : 0 < t) :
      t ^ (-2*θ-1) = a ^ (1+2*θ)*(a*t) ^ (-2*θ-1) := by
    rw [Real.mul_rpow ha.le ht.le,← mul_assoc,← Real.rpow_add ha]
    have hz : 1+2*θ+(-2*θ-1) = 0 := by ring
    rw [hz,Real.rpow_zero,one_mul]
  have hc : a ^ (1+2*θ)*a⁻¹ = a ^ (2*θ) := by
    rw [← Real.rpow_neg_one,← Real.rpow_add ha]
    congr 1
    ring
  calc
    _ = ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (a ^ (1+2*θ))*
        (ENNReal.ofReal ((a*t) ^ (-2*θ-1))*f (a*t)) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [he t ht,ENNReal.ofReal_mul (Real.rpow_nonneg ha.le _),mul_assoc]
    _ = ENNReal.ofReal (a ^ (1+2*θ)) *
        (ENNReal.ofReal a⁻¹ * ∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal (r ^ (-2*θ-1))*f r) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,positiveHalfLine_scaling a ha (fun r => ENNReal.ofReal (r ^ (-2*θ-1))*f r)]
    _ = _ := by rw [← mul_assoc,← ENNReal.ofReal_mul (Real.rpow_nonneg ha.le _),hc]

section Mass
variable {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (μ : Measure X) (m : X → ℝ)

def interpolationMultiplierMass (u : Lp H 2 μ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (‖(m x : ℂ) • u x‖^2) ∂μ

lemma interpolationMultiplierMass_mem (hm : Measurable m) (u : Lp H 2 μ)
    (hf : interpolationMultiplierMass μ m u ≠ ∞) :
    u ∈ (GW.Analysis.realMultiplier (H := H) m μ).domain := by
  apply (GW.Analysis.realMultiplier_domain m u).mpr
  have hmeas : AEStronglyMeasurable (fun x => (m x : ℂ) • u x) μ :=
    (Complex.continuous_ofReal.measurable.comp hm).aestronglyMeasurable.smul (Lp.aestronglyMeasurable u)
  apply (memLp_two_iff_integrable_sq_norm hmeas).mpr
  refine ⟨hmeas.norm.pow 2,?_⟩
  rw [hasFiniteIntegral_iff_norm]
  simpa only [Real.norm_of_nonneg (sq_nonneg _),interpolationMultiplierMass] using lt_top_iff_ne_top.mpr hf

lemma interpolationMultiplierMass_norm (u : (GW.Analysis.realMultiplier (H := H) m μ).domain) :
    interpolationMultiplierMass μ m u.val = ENNReal.ofReal (‖GW.Analysis.realMultiplier m μ u‖^2) := by
  unfold interpolationMultiplierMass
  rw [GW.Analysis.l2_norm_sq (𝕜 := ℂ)]
  rw [ofReal_integral_eq_lintegral_ofReal
    ((Lp.memLp (GW.Analysis.realMultiplier m μ u)).integrable_norm_pow (p := 2) (by norm_num))
    (Eventually.of_forall (fun _ => sq_nonneg _))]
  apply lintegral_congr_ae
  filter_upwards [GW.Analysis.realMultiplier_ae m u] with x hx
  rw [hx]

lemma interpolationMultiplierMass_rpow (w : X → ℝ) (hw : ∀ x, 0 < w x) (θ : ℝ) (u : Lp H 2 μ) :
    interpolationMultiplierMass μ (fun x => (w x)^θ) u =
      ∫⁻ x, ENNReal.ofReal ((w x)^(2*θ)*‖u x‖^2) ∂μ := by
  apply lintegral_congr
  intro x
  rw [norm_smul,mul_pow,Complex.norm_real,Real.norm_of_nonneg (Real.rpow_nonneg (hw x).le _)]
  congr 1
  rw [← Real.rpow_natCast ((w x)^θ) 2,← Real.rpow_mul (hw x).le]
  congr 2
  ring

end Mass
lemma interpolationCoefficient_sq (M₀ M₁ θ : ℝ) (hM₀ : 0 < M₀) (hM₁ : 0 < M₁) :
    (M₀^(1-θ)*M₁^θ)^2 = M₀^2*(M₁/M₀)^(2*θ) := by
  have h₀ : M₀ ^ ((1-θ)*2) = M₀ ^ (2-2*θ) := by congr 1; ring
  have h₁ : M₁ ^ (θ*2) = M₁ ^ (2*θ) := by congr 1; ring
  rw [mul_pow,← Real.rpow_natCast (M₀^(1-θ)) 2,← Real.rpow_natCast (M₁^θ) 2,
    ← Real.rpow_mul hM₀.le,← Real.rpow_mul hM₁.le]
  norm_num only [Nat.cast_ofNat]
  rw [h₀,h₁,Real.div_rpow hM₁.le hM₀.le,
    Real.rpow_sub hM₀,Real.rpow_two]
  ring


lemma interpolationMass_estimate_of_KBound
    {X Y H G : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (μ : Measure X) (ν : Measure Y) (w : X → ℝ) (v : Y → ℝ)
    (hw : Measurable w) (hv : Measurable v) (hw1 : ∀ x, 1 ≤ w x) (hv1 : ∀ y, 1 ≤ v y)
    (M₀ M₁ : ℝ) (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (u : Lp H 2 μ) (z : Lp G 2 ν)
    (hK : ∀ t, 0 < t → quadraticKSquared ν v t z ≤ M₀^2*quadraticKSquared μ w (t*M₁/M₀) u)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    ENNReal.ofReal (interpolationConstant θ) * interpolationMultiplierMass ν (fun y => (v y)^θ) z ≤
      (ENNReal.ofReal (M₀^2)*ENNReal.ofReal ((M₁/M₀) ^ (2*θ))) *
        (ENNReal.ofReal (interpolationConstant θ) * interpolationMultiplierMass μ (fun x => (w x)^θ) u) := by
  let a := M₁/M₀
  have ha : 0 < a := div_pos hM₁ hM₀
  rw [interpolationMultiplierMass_rpow ν v (fun y => zero_lt_one.trans_le (hv1 y)),
    interpolationMultiplierMass_rpow μ w (fun x => zero_lt_one.trans_le (hw1 x)),
    ← quadraticK_extended_identity ν v hv hv1 z θ hθ0 hθ1,
    ← quadraticK_extended_identity μ w hw hw1 u θ hθ0 hθ1]
  calc
    _ ≤ ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ (-2*θ-1)) *
        (ENNReal.ofReal (M₀^2)*ENNReal.ofReal (quadraticKSquared μ w (a*t) u)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      apply mul_le_mul_right
      rw [← ENNReal.ofReal_mul (sq_nonneg M₀)]
      apply ENNReal.ofReal_le_ofReal
      have he : a*t = t*M₁/M₀ := by dsimp [a]; ring
      rw [he]
      exact hK t ht
    _ = ENNReal.ofReal (M₀^2) *
        (ENNReal.ofReal (a ^ (2*θ)) *
          ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ (-2*θ-1))*ENNReal.ofReal (quadraticKSquared μ w t u)) := by
      have he : (fun t : ℝ => ENNReal.ofReal (t ^ (-2*θ-1)) *
          (ENNReal.ofReal (M₀^2)*ENNReal.ofReal (quadraticKSquared μ w (a*t) u))) =
        (fun t => ENNReal.ofReal (M₀^2) *
          (ENNReal.ofReal (t ^ (-2*θ-1))*ENNReal.ofReal (quadraticKSquared μ w (a*t) u))) := by
        funext t
        ring
      rw [he,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        weightedPositiveHalfLine_scaling θ a ha (fun t => ENNReal.ofReal (quadraticKSquared μ w t u))]
    _ = _ := by rw [mul_assoc]


lemma interpolation_interior_mem_of_KBound
    {X Y H G : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (μ : Measure X) (ν : Measure Y) (w : X → ℝ) (v : Y → ℝ)
    (hw : Measurable w) (hv : Measurable v) (hw1 : ∀ x, 1 ≤ w x) (hv1 : ∀ y, 1 ≤ v y)
    (M₀ M₁ : ℝ) (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (u : (GW.Analysis.realMultiplier (H := H) (fun x => (w x)^θ) μ).domain)
    (z : Lp G 2 ν)
    (hK : ∀ t, 0 < t → quadraticKSquared ν v t z ≤ M₀^2*quadraticKSquared μ w (t*M₁/M₀) u.val) :
    z ∈ (GW.Analysis.realMultiplier (H := G) (fun y => (v y)^θ) ν).domain := by
  have hc := interpolationConstant_pos θ hθ0 hθ1
  have he := interpolationMass_estimate_of_KBound μ ν w v hw hv hw1 hv1 M₀ M₁ hM₀ hM₁ u.val z hK θ hθ0 hθ1
  rw [interpolationMultiplierMass_norm μ (fun x => (w x)^θ) u] at he
  have hf : (ENNReal.ofReal (M₀^2)*ENNReal.ofReal ((M₁/M₀) ^ (2*θ))) *
      (ENNReal.ofReal (interpolationConstant θ) *
        ENNReal.ofReal (‖GW.Analysis.realMultiplier (fun x => (w x)^θ) μ u‖^2)) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
  have ht := (lt_of_le_of_lt he (lt_top_iff_ne_top.mpr hf)).ne
  apply interpolationMultiplierMass_mem ν (fun y => (v y)^θ) (hv.pow_const θ)
  exact (ENNReal.lt_top_of_mul_ne_top_right ht (ENNReal.ofReal_pos.mpr hc).ne').ne


lemma weightedInterpolation_interior_of_KBound
    {X Y H G : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (μ : Measure X) (ν : Measure Y) (w : X → ℝ) (v : Y → ℝ)
    (hw : Measurable w) (hv : Measurable v) (hw1 : ∀ x, 1 ≤ w x) (hv1 : ∀ y, 1 ≤ v y)
    (M₀ M₁ : ℝ) (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (u : (GW.Analysis.realMultiplier (H := H) (fun x => (w x)^θ) μ).domain)
    (z : Lp G 2 ν)
    (hK : ∀ t, 0 < t → quadraticKSquared ν v t z ≤ M₀^2*quadraticKSquared μ w (t*M₁/M₀) u.val) :
    ∃ b : (GW.Analysis.realMultiplier (H := G) (fun y => (v y)^θ) ν).domain,
      b.val = z ∧ ‖GW.Analysis.realMultiplier (fun y => (v y)^θ) ν b‖ ≤
        M₀^(1-θ)*M₁^θ*‖GW.Analysis.realMultiplier (fun x => (w x)^θ) μ u‖ := by
  let b : (GW.Analysis.realMultiplier (H := G) (fun y => (v y)^θ) ν).domain :=
    ⟨z,interpolation_interior_mem_of_KBound μ ν w v hw hv hw1 hv1 M₀ M₁ hM₀ hM₁ θ hθ0 hθ1 u z hK⟩
  refine ⟨b,rfl,?_⟩
  have hc := interpolationConstant_pos θ hθ0 hθ1
  have he := interpolationMass_estimate_of_KBound μ ν w v hw hv hw1 hv1 M₀ M₁ hM₀ hM₁ u.val z hK θ hθ0 hθ1
  have hbmass := interpolationMultiplierMass_norm ν (fun y => (v y)^θ) b
  change interpolationMultiplierMass ν (fun y => (v y)^θ) (z) = _ at hbmass
  rw [hbmass,interpolationMultiplierMass_norm μ (fun x => (w x)^θ) u] at he
  have hf : (ENNReal.ofReal (M₀^2)*ENNReal.ofReal ((M₁/M₀) ^ (2*θ))) *
      (ENNReal.ofReal (interpolationConstant θ) *
        ENNReal.ofReal (‖GW.Analysis.realMultiplier (fun x => (w x)^θ) μ u‖^2)) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
  have hr := ENNReal.toReal_mono hf he
  simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal hc.le,
    ENNReal.toReal_ofReal (sq_nonneg _),
    ENNReal.toReal_ofReal (Real.rpow_nonneg (div_pos hM₁ hM₀).le _)] at hr
  have hs : ‖GW.Analysis.realMultiplier (fun y => (v y)^θ) ν b‖^2 ≤
      M₀^2*(M₁/M₀)^(2*θ)*‖GW.Analysis.realMultiplier (fun x => (w x)^θ) μ u‖^2 := by
    apply (mul_le_mul_iff_right₀ hc).mp
    nlinarith [hr]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg
    (mul_nonneg (Real.rpow_nonneg hM₀.le _) (Real.rpow_nonneg hM₁.le _)) (norm_nonneg _))).mp
  rw [mul_pow,interpolationCoefficient_sq M₀ M₁ θ hM₀ hM₁]
  exact hs


section MassEstimate
variable {X Y H G : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]
  (μ : Measure X) (ν : Measure Y) (w : X → ℝ) (v : Y → ℝ)
  (hw : Measurable w) (hv : Measurable v) (hw1 : ∀ x, 1 ≤ w x) (hv1 : ∀ y, 1 ≤ v y)
  (T : Lp H 2 μ →L[ℂ] Lp G 2 ν) (M₀ M₁ : ℝ)
  (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
  (hT₀ : ∀ z, ‖T z‖ ≤ M₀*‖z‖)
  (hT₁ : ∀ a : (GW.Analysis.realMultiplier (H := H) w μ).domain,
    ∃ b : (GW.Analysis.realMultiplier (H := G) v ν).domain,
      b.val = T a.val ∧ ‖GW.Analysis.realMultiplier v ν b‖ ≤ M₁*‖GW.Analysis.realMultiplier w μ a‖)

include hw hv hw1 hv1 hM₀ hM₁ hT₀ hT₁ in
lemma interpolationMass_estimate (u : Lp H 2 μ) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    ENNReal.ofReal (interpolationConstant θ) * interpolationMultiplierMass ν (fun y => (v y)^θ) (T u) ≤
      (ENNReal.ofReal (M₀^2)*ENNReal.ofReal ((M₁/M₀) ^ (2*θ))) *
        (ENNReal.ofReal (interpolationConstant θ) * interpolationMultiplierMass μ (fun x => (w x)^θ) u) := by
  let a := M₁/M₀
  have ha : 0 < a := div_pos hM₁ hM₀
  rw [interpolationMultiplierMass_rpow ν v (fun y => zero_lt_one.trans_le (hv1 y)),
    interpolationMultiplierMass_rpow μ w (fun x => zero_lt_one.trans_le (hw1 x)),
    ← quadraticK_extended_identity ν v hv hv1 (T u) θ hθ0 hθ1,
    ← quadraticK_extended_identity μ w hw hw1 u θ hθ0 hθ1]
  calc
    _ ≤ ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ (-2*θ-1)) *
        (ENNReal.ofReal (M₀^2)*ENNReal.ofReal (quadraticKSquared μ w (a*t) u)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      apply mul_le_mul_right
      rw [← ENNReal.ofReal_mul (sq_nonneg M₀)]
      apply ENNReal.ofReal_le_ofReal
      have he : a*t = t*M₁/M₀ := by dsimp [a]; ring
      rw [he]
      exact quadraticKSquared_endpoint μ ν w v hw hw1 T M₀ M₁ hM₀ hM₁ hT₀ hT₁ t ht u
    _ = ENNReal.ofReal (M₀^2) *
        (ENNReal.ofReal (a ^ (2*θ)) *
          ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ (-2*θ-1))*ENNReal.ofReal (quadraticKSquared μ w t u)) := by
      have he : (fun t : ℝ => ENNReal.ofReal (t ^ (-2*θ-1)) *
          (ENNReal.ofReal (M₀^2)*ENNReal.ofReal (quadraticKSquared μ w (a*t) u))) =
        (fun t => ENNReal.ofReal (M₀^2) *
          (ENNReal.ofReal (t ^ (-2*θ-1))*ENNReal.ofReal (quadraticKSquared μ w (a*t) u))) := by
        funext t
        ring
      rw [he,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        weightedPositiveHalfLine_scaling θ a ha (fun t => ENNReal.ofReal (quadraticKSquared μ w t u))]
    _ = _ := by rw [mul_assoc]

include hw hv hw1 hv1 hM₀ hM₁ hT₀ hT₁ in
lemma interpolation_interior_mem
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (u : (GW.Analysis.realMultiplier (H := H) (fun x => (w x)^θ) μ).domain) :
    T u.val ∈ (GW.Analysis.realMultiplier (H := G) (fun y => (v y)^θ) ν).domain := by
  have hc := interpolationConstant_pos θ hθ0 hθ1
  have he := interpolationMass_estimate μ ν w v hw hv hw1 hv1 T M₀ M₁ hM₀ hM₁ hT₀ hT₁ u.val θ hθ0 hθ1
  rw [interpolationMultiplierMass_norm μ (fun x => (w x)^θ) u] at he
  have hf : (ENNReal.ofReal (M₀^2)*ENNReal.ofReal ((M₁/M₀) ^ (2*θ))) *
      (ENNReal.ofReal (interpolationConstant θ) *
        ENNReal.ofReal (‖GW.Analysis.realMultiplier (fun x => (w x)^θ) μ u‖^2)) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
  have ht := (lt_of_le_of_lt he (lt_top_iff_ne_top.mpr hf)).ne
  apply interpolationMultiplierMass_mem ν (fun y => (v y)^θ) (hv.pow_const θ)
  exact (ENNReal.lt_top_of_mul_ne_top_right ht (ENNReal.ofReal_pos.mpr hc).ne').ne

include hw hv hw1 hv1 hM₀ hM₁ hT₀ hT₁ in
lemma weightedInterpolation_interior
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (u : (GW.Analysis.realMultiplier (H := H) (fun x => (w x)^θ) μ).domain) :
    ∃ b : (GW.Analysis.realMultiplier (H := G) (fun y => (v y)^θ) ν).domain,
      b.val = T u.val ∧ ‖GW.Analysis.realMultiplier (fun y => (v y)^θ) ν b‖ ≤
        M₀^(1-θ)*M₁^θ*‖GW.Analysis.realMultiplier (fun x => (w x)^θ) μ u‖ := by
  let b : (GW.Analysis.realMultiplier (H := G) (fun y => (v y)^θ) ν).domain :=
    ⟨T u.val,interpolation_interior_mem μ ν w v hw hv hw1 hv1 T M₀ M₁ hM₀ hM₁ hT₀ hT₁ θ hθ0 hθ1 u⟩
  refine ⟨b,rfl,?_⟩
  have hc := interpolationConstant_pos θ hθ0 hθ1
  have he := interpolationMass_estimate μ ν w v hw hv hw1 hv1 T M₀ M₁ hM₀ hM₁ hT₀ hT₁ u.val θ hθ0 hθ1
  have hbmass := interpolationMultiplierMass_norm ν (fun y => (v y)^θ) b
  change interpolationMultiplierMass ν (fun y => (v y)^θ) (T u.val) = _ at hbmass
  rw [hbmass,interpolationMultiplierMass_norm μ (fun x => (w x)^θ) u] at he
  have hf : (ENNReal.ofReal (M₀^2)*ENNReal.ofReal ((M₁/M₀) ^ (2*θ))) *
      (ENNReal.ofReal (interpolationConstant θ) *
        ENNReal.ofReal (‖GW.Analysis.realMultiplier (fun x => (w x)^θ) μ u‖^2)) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
  have hr := ENNReal.toReal_mono hf he
  simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal hc.le,
    ENNReal.toReal_ofReal (sq_nonneg _),
    ENNReal.toReal_ofReal (Real.rpow_nonneg (div_pos hM₁ hM₀).le _)] at hr
  have hs : ‖GW.Analysis.realMultiplier (fun y => (v y)^θ) ν b‖^2 ≤
      M₀^2*(M₁/M₀)^(2*θ)*‖GW.Analysis.realMultiplier (fun x => (w x)^θ) μ u‖^2 := by
    apply (mul_le_mul_iff_right₀ hc).mp
    nlinarith [hr]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg
    (mul_nonneg (Real.rpow_nonneg hM₀.le _) (Real.rpow_nonneg hM₁.le _)) (norm_nonneg _))).mp
  rw [mul_pow,interpolationCoefficient_sq M₀ M₁ θ hM₀ hM₁]
  exact hs

include hw hv hw1 hv1 hM₀ hM₁ hT₀ hT₁ in
lemma weightedInterpolation
    (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (u : (GW.Analysis.realMultiplier (H := H) (fun x => (w x)^θ) μ).domain) :
    ∃ b : (GW.Analysis.realMultiplier (H := G) (fun y => (v y)^θ) ν).domain,
      b.val = T u.val ∧ ‖GW.Analysis.realMultiplier (fun y => (v y)^θ) ν b‖ ≤
        M₀^(1-θ)*M₁^θ*‖GW.Analysis.realMultiplier (fun x => (w x)^θ) μ u‖ := by
  by_cases hz : θ = 0
  · subst θ
    let b : (GW.Analysis.realMultiplier (H := G) (fun y => (v y)^(0:ℝ)) ν).domain :=
      ⟨T u.val,⟨T u.val,Eventually.of_forall (fun y => by simp)⟩⟩
    refine ⟨b,rfl,?_⟩
    have hu : GW.Analysis.realMultiplier (fun x => (w x)^(0:ℝ)) μ u = u.val := by
      apply Lp.ext
      filter_upwards [GW.Analysis.realMultiplier_ae (fun x => (w x)^(0:ℝ)) u] with x hx
      simpa using hx.symm
    have hb : GW.Analysis.realMultiplier (fun y => (v y)^(0:ℝ)) ν b = T u.val := by
      apply Lp.ext
      filter_upwards [GW.Analysis.realMultiplier_ae (fun y => (v y)^(0:ℝ)) b] with y hy
      simpa using hy.symm
    rw [hu,hb]
    simpa using hT₀ u.val
  by_cases ho : θ = 1
  · subst θ
    have ha : u.val ∈ (GW.Analysis.realMultiplier (H := H) w μ).domain := by
      simpa only [Real.rpow_one] using u.property
    let a : (GW.Analysis.realMultiplier (H := H) w μ).domain := ⟨u.val,ha⟩
    obtain ⟨b₀,hb₀,hbound⟩ := hT₁ a
    have hbmem : b₀.val ∈ (GW.Analysis.realMultiplier (H := G) (fun y => (v y)^(1:ℝ)) ν).domain := by
      simpa only [Real.rpow_one] using b₀.property
    let b : (GW.Analysis.realMultiplier (H := G) (fun y => (v y)^(1:ℝ)) ν).domain := ⟨b₀.val,hbmem⟩
    refine ⟨b,hb₀,?_⟩
    have hu : GW.Analysis.realMultiplier (fun x => (w x)^(1:ℝ)) μ u = GW.Analysis.realMultiplier w μ a := by
      apply Lp.ext
      filter_upwards [GW.Analysis.realMultiplier_ae (fun x => (w x)^(1:ℝ)) u,
        GW.Analysis.realMultiplier_ae w a] with x hx hy
      exact hx.symm.trans (by simpa only [Real.rpow_one] using hy)
    have hb : GW.Analysis.realMultiplier (fun y => (v y)^(1:ℝ)) ν b = GW.Analysis.realMultiplier v ν b₀ := by
      apply Lp.ext
      filter_upwards [GW.Analysis.realMultiplier_ae (fun y => (v y)^(1:ℝ)) b,
        GW.Analysis.realMultiplier_ae v b₀] with y hx hy
      exact hx.symm.trans (by simpa only [Real.rpow_one] using hy)
    rw [hu,hb]
    simpa using hbound
  exact weightedInterpolation_interior μ ν w v hw hv hw1 hv1 T M₀ M₁ hM₀ hM₁ hT₀ hT₁
    θ (lt_of_le_of_ne hθ0 (Ne.symm hz)) (lt_of_le_of_ne hθ1 ho) u

end MassEstimate

lemma weightedInterpolation_unitary
    {X Y H G A B : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    [NormedAddCommGroup B] [InnerProductSpace ℂ B]
    (μ : Measure X) (ν : Measure Y) (w : X → ℝ) (v : Y → ℝ)
    (hw : Measurable w) (hv : Measurable v) (hw1 : ∀ x, 1 ≤ w x) (hv1 : ∀ y, 1 ≤ v y)
    (U : A ≃ₗᵢ[ℂ] Lp H 2 μ) (V : B ≃ₗᵢ[ℂ] Lp G 2 ν)
    (T : A →L[ℂ] B) (M₀ M₁ : ℝ) (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (hT₀ : ∀ z, ‖T z‖ ≤ M₀*‖z‖)
    (hT₁ : ∀ a : (GW.Analysis.realMultiplier (H := H) w μ).domain,
      ∃ b : (GW.Analysis.realMultiplier (H := G) v ν).domain,
        b.val = V (T (U.symm a.val)) ∧
          ‖GW.Analysis.realMultiplier v ν b‖ ≤ M₁*‖GW.Analysis.realMultiplier w μ a‖)
    (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (z : A)
    (hz : U z ∈ (GW.Analysis.realMultiplier (H := H) (fun x => (w x)^θ) μ).domain) :
    ∃ b : (GW.Analysis.realMultiplier (H := G) (fun y => (v y)^θ) ν).domain,
      b.val = V (T z) ∧ ‖GW.Analysis.realMultiplier (fun y => (v y)^θ) ν b‖ ≤
        M₀^(1-θ)*M₁^θ*‖GW.Analysis.realMultiplier (fun x => (w x)^θ) μ ⟨U z,hz⟩‖ := by
  let S := V.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (T.comp U.symm.toContinuousLinearEquiv.toContinuousLinearMap)
  have hS₀ : ∀ u, ‖S u‖ ≤ M₀*‖u‖ := by
    intro u
    change ‖V (T (U.symm u))‖ ≤ _
    rw [V.norm_map]
    exact (hT₀ (U.symm u)).trans_eq (congrArg (fun r : ℝ => M₀*r) (U.symm.norm_map u))
  obtain ⟨b,hb,hbound⟩ := weightedInterpolation μ ν w v hw hv hw1 hv1 S M₀ M₁ hM₀ hM₁ hS₀ hT₁ θ hθ0 hθ1 ⟨U z,hz⟩
  refine ⟨b,?_,hbound⟩
  change b.val = V (T (U.symm (U z))) at hb
  simpa only [U.symm_apply_apply] using hb

lemma kMinimizerMap_invariant {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (μ : Measure X) (w : X → ℝ) (hw : Measurable w)
    (S : ClosedSubmodule ℂ (Lp H 2 μ)) (hS : GW.Spaces.FunctionalWeightInvariant S hw)
    (t : ℝ) (u : S) : kMinimizerMap μ w hw t u.val ∈ S := by
  have hm : Measurable (fun r : ℝ => (kMinimizerCoefficient r t : ℂ)) := by
    unfold kMinimizerCoefficient
    fun_prop
  have hb : ∀ r : ℝ, ‖(kMinimizerCoefficient r t : ℂ)‖ ≤ 1 := by
    intro r
    rw [Complex.norm_real,Real.norm_of_nonneg (kMinimizerCoefficient_bound r t).1]
    exact (kMinimizerCoefficient_bound r t).2
  exact hS _ hm hb u

lemma quadraticKSquared_restricted_endpoint
    {X Y H G : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (μ : Measure X) (ν : Measure Y) (w : X → ℝ) (v : Y → ℝ)
    (hw : Measurable w) (hw1 : ∀ x, 1 ≤ w x)
    (S : ClosedSubmodule ℂ (Lp H 2 μ)) (R : ClosedSubmodule ℂ (Lp G 2 ν))
    (hS : GW.Spaces.FunctionalWeightInvariant S hw)
    (T : S →L[ℂ] R) (M₀ M₁ : ℝ) (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (hT₀ : ∀ z, ‖T z‖ ≤ M₀*‖z‖)
    (hT₁ : ∀ (a : (GW.Analysis.realMultiplier (H := H) w μ).domain) (ha : a.val ∈ S),
      ∃ b : (GW.Analysis.realMultiplier (H := G) v ν).domain,
        b.val = (T ⟨a.val,ha⟩).val ∧
          ‖GW.Analysis.realMultiplier v ν b‖ ≤ M₁*‖GW.Analysis.realMultiplier w μ a‖)
    (t : ℝ) (ht : 0 < t) (u : S) :
    quadraticKSquared ν v t (T u).val ≤ M₀^2*quadraticKSquared μ w (t*M₁/M₀) u.val := by
  let s := t*M₁/M₀
  have hs : 0 < s := div_pos (mul_pos ht hM₁) hM₀
  let a := kMinimizer μ w hw hw1 s hs u.val
  have haS : a.val ∈ S := kMinimizerMap_invariant μ w hw S hS s u
  let aS : S := ⟨a.val,haS⟩
  obtain ⟨b,hb,hbnd⟩ := hT₁ a haS
  have hbelow : BddBelow (Set.range (quadraticKCost ν v t (T u).val)) :=
    ⟨0,fun _ hz => by obtain ⟨z,rfl⟩ := hz; exact quadraticKCost_nonneg ν v t (T u).val z⟩
  have hle : quadraticKSquared ν v t (T u).val ≤ quadraticKCost ν v t (T u).val b :=
    csInf_le hbelow (Set.mem_range_self b)
  have hzero := hT₀ (u-aS)
  rw [map_sub] at hzero
  change ‖(T u).val-(T aS).val‖ ≤ M₀*‖u.val-a.val‖ at hzero
  have hsq₀ := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM₀.le (norm_nonneg _))).mpr hzero
  have hsq₁ := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM₁.le (norm_nonneg _))).mpr hbnd
  have hcost : quadraticKCost ν v t (T u).val b ≤ M₀^2*quadraticKCost μ w s u.val a := by
    unfold quadraticKCost
    rw [hb]
    change ‖(T u).val-(T aS).val‖^2+t^2*‖GW.Analysis.realMultiplier v ν b‖^2 ≤ _
    have hscale : M₀^2*s^2 = t^2*M₁^2 := by dsimp [s]; field_simp
    nlinarith [mul_le_mul_of_nonneg_left hsq₁ (sq_nonneg t)]
  apply (hle.trans hcost).trans_eq
  congr 1
  exact (quadraticKCost_minimizer μ w hw hw1 s hs u.val).trans
    (quadraticKSquared_eq μ w hw hw1 s hs u.val).symm

lemma functionalWeightInvariant_rpow {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {μ : Measure X} {w : X → ℝ} {hw : Measurable w}
    {S : ClosedSubmodule ℂ (Lp H 2 μ)} (hS : GW.Spaces.FunctionalWeightInvariant S hw) (θ : ℝ) :
    GW.Spaces.FunctionalWeightInvariant S (hw.pow_const θ) := by
  intro a ha c hc u
  exact hS (fun r => a (r^θ)) (ha.comp (measurable_id.pow_const θ))
    (fun r => hc (r^θ)) u

lemma weightedInterpolation_restricted_interior
    {X Y H G : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (μ : Measure X) (ν : Measure Y) (w : X → ℝ) (v : Y → ℝ)
    (hw : Measurable w) (hv : Measurable v) (hw1 : ∀ x, 1 ≤ w x) (hv1 : ∀ y, 1 ≤ v y)
    (S : ClosedSubmodule ℂ (Lp H 2 μ)) (R : ClosedSubmodule ℂ (Lp G 2 ν))
    (hS : GW.Spaces.FunctionalWeightInvariant S hw) (hR : GW.Spaces.FunctionalWeightInvariant R hv)
    (T : S →L[ℂ] R) (M₀ M₁ : ℝ) (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (hT₀ : ∀ z, ‖T z‖ ≤ M₀*‖z‖)
    (hT₁ : ∀ (a : (GW.Analysis.realMultiplier (H := H) w μ).domain) (ha : a.val ∈ S),
      ∃ b : (GW.Analysis.realMultiplier (H := G) v ν).domain,
        b.val = (T ⟨a.val,ha⟩).val ∧
          ‖GW.Analysis.realMultiplier v ν b‖ ≤ M₁*‖GW.Analysis.realMultiplier w μ a‖)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (u : S)
    (hu : u.val ∈ (GW.Analysis.realMultiplier (H := H) (fun x => (w x)^θ) μ).domain) :
    ∃ b : (GW.Analysis.realMultiplier (H := G) (fun y => (v y)^θ) ν).domain,
      b.val = (T u).val ∧
      ‖GW.Analysis.realMultiplier (fun y => (v y)^θ) ν b‖ ≤
        M₀^(1-θ)*M₁^θ*‖GW.Analysis.realMultiplier (fun x => (w x)^θ) μ ⟨u.val,hu⟩‖ ∧
      GW.Analysis.realMultiplier (fun y => (v y)^θ) ν b ∈ R := by
  have hK := quadraticKSquared_restricted_endpoint μ ν w v hw hw1 S R hS T M₀ M₁ hM₀ hM₁ hT₀ hT₁
  obtain ⟨b,hb,hbound⟩ := weightedInterpolation_interior_of_KBound μ ν w v hw hv hw1 hv1 M₀ M₁ hM₀ hM₁
    θ hθ0 hθ1 ⟨u.val,hu⟩ (T u).val (fun t ht => hK t ht u)
  refine ⟨b,hb,hbound,?_⟩
  apply GW.Spaces.invariant_product_mem
    (GW.Spaces.weightInvariant_of_functional (fun y => Real.one_le_rpow (hv1 y) hθ0.le)
      (functionalWeightInvariant_rpow hR θ)) b
  rw [hb]
  exact (T u).property

lemma kMinimizerMap_norm_le {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (μ : Measure X) (w : X → ℝ) (hw : Measurable w) (t : ℝ) :
    ‖kMinimizerMap (H := H) μ w hw t‖ ≤ 1 :=
  GW.Analysis.boundedMultiplier_opNorm_le _ _ zero_le_one _

lemma kMinimizerWeightedMap_norm_le {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (μ : Measure X) (w : X → ℝ) (hw : Measurable w) (hw1 : ∀ x, 1 ≤ w x)
    (t : ℝ) (ht : 0 < t) : ‖kMinimizerWeightedMap (H := H) μ w hw hw1 t ht‖ ≤ (2*t)⁻¹ :=
  GW.Analysis.boundedMultiplier_opNorm_le _ _ (by positivity) _

lemma quadraticKSquared_bounds {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (μ : Measure X) (w : X → ℝ) (hw : Measurable w) (hw1 : ∀ x, 1 ≤ w x)
    (t : ℝ) (ht : 0 < t) (u : Lp H 2 μ) :
    0 ≤ quadraticKSquared μ w t u ∧ quadraticKSquared μ w t u ≤ ‖u‖^2 := by
  rw [quadraticKSquared_eq μ w hw hw1 t ht u]
  refine ⟨integral_nonneg (quadraticKDensity_nonneg μ w t u),?_⟩
  rw [GW.Analysis.l2_norm_sq (𝕜 := ℂ)]
  exact integral_mono (quadraticKDensity_integrable μ w hw t u)
    ((Lp.memLp u).integrable_norm_pow (p := 2) (by norm_num)) (quadraticKDensity_le μ w t u)

lemma quadraticKIntegral_continuous {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (μ : Measure X) (w : X → ℝ) (hw : Measurable w) (u : Lp H 2 μ) :
    Continuous (fun t : ℝ => ∫ x, quadraticKDensity μ w t u x ∂μ) := by
  apply continuous_of_dominated
    (fun t => (quadraticKDensity_integrable μ w hw t u).aestronglyMeasurable)
    (bound := fun x => ‖u x‖^2)
  · intro t
    exact Eventually.of_forall (fun x => by
      rw [Real.norm_of_nonneg (quadraticKDensity_nonneg μ w t u x)]
      exact quadraticKDensity_le μ w t u x)
  · exact (Lp.memLp u).integrable_norm_pow (p := 2) (by norm_num)
  · apply Eventually.of_forall
    intro x
    unfold quadraticKDensity
    have hd : ∀ t : ℝ, 1+t^2*(w x)^2 ≠ 0 := fun t => ne_of_gt (by positivity)
    exact ((by fun_prop : Continuous (fun t : ℝ => t^2*(w x)^2)).div
      (by fun_prop : Continuous (fun t : ℝ => 1+t^2*(w x)^2)) hd).mul continuous_const

section SumMinimizer
variable {X H : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
  [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace ℂ (H n)]
  (μ : ∀ n, Measure (X n)) (w : ∀ n, X n → ℝ)
  (hw : ∀ n, Measurable (w n)) (hw1 : ∀ n x, 1 ≤ w n x)

def sumKMinimizerMap (t : ℝ) :
    GW.Spaces.WeightSum (F := H) μ →L[ℂ] GW.Spaces.WeightSum (F := H) μ :=
  GW.Spaces.diagonalMap (fun n => kMinimizerMap (H := H n) (μ n) (w n) (hw n) t)
    zero_le_one (fun n => kMinimizerMap_norm_le (μ n) (w n) (hw n) t)

def sumKMinimizerWeightedMap (t : ℝ) (ht : 0 < t) :
    GW.Spaces.WeightSum (F := H) μ →L[ℂ] GW.Spaces.WeightSum (F := H) μ :=
  GW.Spaces.diagonalMap (fun n => kMinimizerWeightedMap (H := H n) (μ n) (w n) (hw n) (hw1 n) t ht)
    (by positivity) (fun n => kMinimizerWeightedMap_norm_le (μ n) (w n) (hw n) (hw1 n) t ht)

include hw1 in
lemma sumKMinimizerMap_mem (t : ℝ) (ht : 0 < t) (u : GW.Spaces.WeightSum (F := H) μ) :
    sumKMinimizerMap μ w hw t u ∈ GW.Spaces.sumWeightDomain (F := H) μ w := by
  refine ⟨sumKMinimizerWeightedMap μ w hw hw1 t ht u,fun n => ?_⟩
  change (fun x => (w n x : ℂ) • kMinimizerMap (μ n) (w n) (hw n) t (u n) x) =ᵐ[μ n]
    kMinimizerWeightedMap (μ n) (w n) (hw n) (hw1 n) t ht (u n)
  filter_upwards [kMinimizerMap_ae (μ n) (w n) (hw n) t (u n),
    GW.Analysis.boundedMultiplier_ae (fun x => ((w n x*kMinimizerCoefficient (w n x) t : ℝ) : ℂ))
      (μ := μ n) (E := H n) _ _ (u n)] with x h₁ h₂
  change (w n x : ℂ) • kMinimizerMap (μ n) (w n) (hw n) t (u n) x =
    GW.Analysis.boundedMultiplier (fun x => ((w n x*kMinimizerCoefficient (w n x) t : ℝ) : ℂ)) _ _ (u n) x
  rw [h₁,← h₂,Complex.ofReal_mul,mul_smul]

def sumKMinimizer (t : ℝ) (ht : 0 < t) (u : GW.Spaces.WeightSum (F := H) μ) :
    GW.Spaces.sumWeightDomain (F := H) μ w :=
  ⟨sumKMinimizerMap μ w hw t u,sumKMinimizerMap_mem μ w hw hw1 t ht u⟩

def sumKCost (t : ℝ) (u : GW.Spaces.WeightSum (F := H) μ)
    (a : GW.Spaces.sumWeightDomain (F := H) μ w) : ℝ :=
  ‖u-a.val‖^2+t^2*‖GW.Spaces.sumWeightValue (F := H) μ a‖^2

def sumKSquared (t : ℝ) (u : GW.Spaces.WeightSum (F := H) μ) : ℝ :=
  sInf (Set.range (sumKCost μ w t u))

def sumKSectorInput (a : GW.Spaces.sumWeightDomain (F := H) μ w) (n : ℕ) :
    (GW.Analysis.realMultiplier (H := H n) (w n) (μ n)).domain :=
  ⟨a.val n,⟨GW.Spaces.sumWeightValue (F := H) μ a n,GW.Spaces.sumWeightValue_ae (F := H) μ a n⟩⟩

lemma sumKSectorInput_action (a : GW.Spaces.sumWeightDomain (F := H) μ w) (n : ℕ) :
    GW.Analysis.realMultiplier (w n) (μ n) (sumKSectorInput μ w a n) =
      GW.Spaces.sumWeightValue (F := H) μ a n := by
  apply Lp.ext
  exact (GW.Analysis.realMultiplier_ae (w n) (sumKSectorInput μ w a n)).symm.trans
    (GW.Spaces.sumWeightValue_ae (F := H) μ a n)

lemma sumKCost_decomposition (t : ℝ) (u : GW.Spaces.WeightSum (F := H) μ)
    (a : GW.Spaces.sumWeightDomain (F := H) μ w) :
    sumKCost μ w t u a = ∑' n, quadraticKCost (μ n) (w n) t (u n) (sumKSectorInput μ w a n) := by
  have hs₁ := (GW.Analysis.memℓp_two_iff_sq _).mp (u-a.val).property
  have hs₂ := ((GW.Analysis.memℓp_two_iff_sq _).mp (GW.Spaces.sumWeightValue (F := H) μ a).property).mul_left (t^2)
  unfold sumKCost
  rw [GW.Analysis.lp_norm_sq,GW.Analysis.lp_norm_sq,← tsum_mul_left,← hs₁.tsum_add hs₂]
  apply tsum_congr
  intro n
  unfold quadraticKCost
  rw [sumKSectorInput_action]
  rfl

include hw hw1 in
lemma sumK_sector_summable (t : ℝ) (ht : 0 < t) (u : GW.Spaces.WeightSum (F := H) μ) :
    Summable (fun n => quadraticKSquared (μ n) (w n) t (u n)) :=
  Summable.of_nonneg_of_le
    (fun n => (quadraticKSquared_bounds (μ n) (w n) (hw n) (hw1 n) t ht (u n)).1)
    (fun n => (quadraticKSquared_bounds (μ n) (w n) (hw n) (hw1 n) t ht (u n)).2)
    ((GW.Analysis.memℓp_two_iff_sq _).mp u.property)

lemma sumKCost_sector_summable (t : ℝ) (u : GW.Spaces.WeightSum (F := H) μ)
    (a : GW.Spaces.sumWeightDomain (F := H) μ w) :
    Summable (fun n => quadraticKCost (μ n) (w n) t (u n) (sumKSectorInput μ w a n)) := by
  have hs₁ := (GW.Analysis.memℓp_two_iff_sq _).mp (u-a.val).property
  have hs₂ := ((GW.Analysis.memℓp_two_iff_sq _).mp (GW.Spaces.sumWeightValue (F := H) μ a).property).mul_left (t^2)
  apply (hs₁.add hs₂).congr
  intro n
  unfold quadraticKCost
  rw [sumKSectorInput_action]
  rfl

lemma sumKMinimizer_sector (t : ℝ) (ht : 0 < t) (u : GW.Spaces.WeightSum (F := H) μ) (n : ℕ) :
    sumKSectorInput μ w (sumKMinimizer μ w hw hw1 t ht u) n =
      kMinimizer (μ n) (w n) (hw n) (hw1 n) t ht (u n) := by
  apply Subtype.ext
  rfl

include hw hw1 in
lemma sumKCost_minimizer (t : ℝ) (ht : 0 < t) (u : GW.Spaces.WeightSum (F := H) μ) :
    sumKCost μ w t u (sumKMinimizer μ w hw hw1 t ht u) =
      ∑' n, quadraticKSquared (μ n) (w n) t (u n) := by
  rw [sumKCost_decomposition]
  apply tsum_congr
  intro n
  rw [sumKMinimizer_sector,quadraticKCost_minimizer (μ n) (w n) (hw n) (hw1 n) t ht,
    quadraticKSquared_eq (μ n) (w n) (hw n) (hw1 n) t ht]

include hw hw1 in
lemma sumKCost_lower (t : ℝ) (ht : 0 < t) (u : GW.Spaces.WeightSum (F := H) μ)
    (a : GW.Spaces.sumWeightDomain (F := H) μ w) :
    (∑' n, quadraticKSquared (μ n) (w n) t (u n)) ≤ sumKCost μ w t u a := by
  rw [sumKCost_decomposition]
  apply (sumK_sector_summable μ w hw hw1 t ht u).tsum_le_tsum ?_ (sumKCost_sector_summable μ w t u a)
  intro n
  rw [quadraticKSquared_eq (μ n) (w n) (hw n) (hw1 n) t ht]
  exact quadraticKCost_lower (μ n) (w n) (hw n) t (u n) (sumKSectorInput μ w a n)

include hw hw1 in
lemma sumKSquared_eq (t : ℝ) (ht : 0 < t) (u : GW.Spaces.WeightSum (F := H) μ) :
    sumKSquared μ w t u = ∑' n, quadraticKSquared (μ n) (w n) t (u n) := by
  have hb : BddBelow (Set.range (sumKCost μ w t u)) := by
    refine ⟨0,?_⟩
    rintro y ⟨a,rfl⟩
    exact add_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  apply le_antisymm
  · exact (csInf_le hb (Set.mem_range_self (sumKMinimizer μ w hw hw1 t ht u))).trans_eq
      (sumKCost_minimizer μ w hw hw1 t ht u)
  · apply le_csInf (Set.range_nonempty _)
    rintro y ⟨a,rfl⟩
    exact sumKCost_lower μ w hw hw1 t ht u a

include hw hw1 in
lemma sumK_extended_identity (tθ : ℝ) (hθ0 : 0 < tθ) (hθ1 : tθ < 1)
    (u : GW.Spaces.WeightSum (F := H) μ) :
    (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ (-2*tθ-1))*ENNReal.ofReal (sumKSquared μ w t u)) =
      ENNReal.ofReal (interpolationConstant tθ) *
        ∑' n, interpolationMultiplierMass (μ n) (fun x => (w n x)^tθ) (u n) := by
  have hm (n : ℕ) : AEMeasurable
      (fun t : ℝ => ENNReal.ofReal (t ^ (-2*tθ-1))*ENNReal.ofReal (quadraticKSquared (μ n) (w n) t (u n)))
      (volume.restrict (Ioi 0)) := by
    have hh : Measurable (fun t : ℝ => ENNReal.ofReal (t ^ (-2*tθ-1))*
        ENNReal.ofReal (∫ x, quadraticKDensity (μ n) (w n) t (u n) x ∂μ n)) :=
      (measurable_id.pow_const _).ennreal_ofReal.mul
        (quadraticKIntegral_continuous (μ n) (w n) (hw n) (u n)).measurable.ennreal_ofReal
    apply hh.aemeasurable.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [quadraticKSquared_eq (μ n) (w n) (hw n) (hw1 n) t ht]
  calc
    _ = ∫⁻ t in Ioi (0:ℝ), ∑' n, ENNReal.ofReal (t ^ (-2*tθ-1))*
        ENNReal.ofReal (quadraticKSquared (μ n) (w n) t (u n)) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [sumKSquared_eq μ w hw hw1 t ht u,
        ENNReal.ofReal_tsum_of_nonneg (fun n => (quadraticKSquared_bounds (μ n) (w n) (hw n) (hw1 n) t ht (u n)).1)
          (sumK_sector_summable μ w hw hw1 t ht u),← ENNReal.tsum_mul_left]
    _ = ∑' n, ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ (-2*tθ-1))*
        ENNReal.ofReal (quadraticKSquared (μ n) (w n) t (u n)) := lintegral_tsum hm
    _ = ∑' n, ENNReal.ofReal (interpolationConstant tθ)*
        interpolationMultiplierMass (μ n) (fun x => (w n x)^tθ) (u n) := by
      apply tsum_congr
      intro n
      rw [quadraticK_extended_identity (μ n) (w n) (hw n) (hw1 n) (u n) tθ hθ0 hθ1,
        interpolationMultiplierMass_rpow (μ n) (w n) (fun x => zero_lt_one.trans_le (hw1 n x))]
    _ = _ := ENNReal.tsum_mul_left

def sumInterpolationMass (u : GW.Spaces.WeightSum (F := H) μ) : ℝ≥0∞ :=
  ∑' n, interpolationMultiplierMass (μ n) (w n) (u n)

include hw in
lemma sumInterpolationMass_mem (u : GW.Spaces.WeightSum (F := H) μ)
    (hf : sumInterpolationMass μ w u ≠ ∞) : u ∈ GW.Spaces.sumWeightDomain (F := H) μ w := by
  let S (n : ℕ) := interpolationMultiplierMass (μ n) (w n) (u n)
  have hS (n : ℕ) : S n ≠ ∞ := ne_top_of_le_ne_top hf (le_tsum S n)
  have hu (n : ℕ) : u n ∈ (GW.Analysis.realMultiplier (H := H n) (w n) (μ n)).domain :=
    interpolationMultiplierMass_mem (μ n) (w n) (hw n) (u n) (hS n)
  let v (n : ℕ) := GW.Analysis.realMultiplier (w n) (μ n) ⟨u n,hu n⟩
  have hn (n : ℕ) : ‖v n‖^2 = (S n).toReal := by
    have he : S n = ENNReal.ofReal (‖v n‖^2) := interpolationMultiplierMass_norm (μ n) (w n) ⟨u n,hu n⟩
    exact (ENNReal.toReal_ofReal (sq_nonneg (‖v n‖))).symm.trans (congrArg ENNReal.toReal he.symm)
  have hs : Summable (fun n => ‖v n‖^2) := by
    simp_rw [hn]
    exact ENNReal.summable_toReal hf
  exact ⟨GW.Analysis.squareSumVector v hs,fun n => GW.Analysis.realMultiplier_ae (w n) ⟨u n,hu n⟩⟩

lemma sumInterpolationMass_norm (u : GW.Spaces.sumWeightDomain (F := H) μ w) :
    sumInterpolationMass μ w u.val = ENNReal.ofReal (‖GW.Spaces.sumWeightValue (F := H) μ u‖^2) := by
  have hn (n : ℕ) : interpolationMultiplierMass (μ n) (w n) (u.val n) =
      ENNReal.ofReal (‖GW.Spaces.sumWeightValue (F := H) μ u n‖^2) := by
    calc
      _ = ENNReal.ofReal (‖GW.Analysis.realMultiplier (w n) (μ n) (sumKSectorInput μ w u n)‖^2) :=
        interpolationMultiplierMass_norm (μ n) (w n) (sumKSectorInput μ w u n)
      _ = _ := congrArg (fun z : Lp (H n) 2 (μ n) => ENNReal.ofReal (‖z‖^2)) (sumKSectorInput_action μ w u n)
  unfold sumInterpolationMass
  simp_rw [hn]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _)
    ((GW.Analysis.memℓp_two_iff_sq _).mp (GW.Spaces.sumWeightValue (F := H) μ u).property),
    ← GW.Analysis.lp_norm_sq]

end SumMinimizer
lemma sumWeightValue_coeff_congr {X H : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace ℂ (H n)]
    (μ : ∀ n, Measure (X n)) (w v : ∀ n, X n → ℝ)
    (h : ∀ n x, w n x = v n x)
    (a : GW.Spaces.sumWeightDomain (F := H) μ w) (b : GW.Spaces.sumWeightDomain (F := H) μ v)
    (hab : a.val = b.val) : GW.Spaces.sumWeightValue (F := H) μ a = GW.Spaces.sumWeightValue (F := H) μ b := by
  apply lp.ext
  funext n
  apply Lp.ext
  filter_upwards [GW.Spaces.sumWeightValue_ae (F := H) μ a n,GW.Spaces.sumWeightValue_ae (F := H) μ b n] with x ha hb
  rw [← ha,← hb,h n x,hab]

lemma sumWeightValue_one {X H : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace ℂ (H n)]
    (μ : ∀ n, Measure (X n))
    (u : GW.Spaces.sumWeightDomain (F := H) μ (fun _ _ => 1)) :
    GW.Spaces.sumWeightValue (F := H) μ u = u.val := by
  apply lp.ext
  funext n
  apply Lp.ext
  filter_upwards [GW.Spaces.sumWeightValue_ae (F := H) μ u n] with x hx
  simpa only [Complex.ofReal_one,one_smul] using hx.symm

lemma sumInterpolationMass_estimate_of_KBound
    {X Y H G : ℕ → Type*} [∀ n, MeasurableSpace (X n)] [∀ n, MeasurableSpace (Y n)]
    [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace ℂ (H n)]
    [∀ n, NormedAddCommGroup (G n)] [∀ n, InnerProductSpace ℂ (G n)]
    (μ : ∀ n, Measure (X n)) (ν : ∀ n, Measure (Y n))
    (w : ∀ n, X n → ℝ) (v : ∀ n, Y n → ℝ)
    (hw : ∀ n, Measurable (w n)) (hv : ∀ n, Measurable (v n))
    (hw1 : ∀ n x, 1 ≤ w n x) (hv1 : ∀ n y, 1 ≤ v n y)
    (M₀ M₁ : ℝ) (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (u : GW.Spaces.WeightSum (F := H) μ) (z : GW.Spaces.WeightSum (F := G) ν)
    (hK : ∀ t, 0 < t → sumKSquared ν v t z ≤ M₀^2*sumKSquared μ w (t*M₁/M₀) u)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    ENNReal.ofReal (interpolationConstant θ)*sumInterpolationMass ν (fun n y => (v n y)^θ) z ≤
      (ENNReal.ofReal (M₀^2)*ENNReal.ofReal ((M₁/M₀)^(2*θ))) *
        (ENNReal.ofReal (interpolationConstant θ)*sumInterpolationMass μ (fun n x => (w n x)^θ) u) := by
  let a := M₁/M₀
  have ha : 0 < a := div_pos hM₁ hM₀
  unfold sumInterpolationMass
  rw [← sumK_extended_identity ν v hv hv1 θ hθ0 hθ1 z,
    ← sumK_extended_identity μ w hw hw1 θ hθ0 hθ1 u]
  calc
    _ ≤ ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ (-2*θ-1)) *
        (ENNReal.ofReal (M₀^2)*ENNReal.ofReal (sumKSquared μ w (a*t) u)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      apply mul_le_mul_right
      rw [← ENNReal.ofReal_mul (sq_nonneg M₀)]
      apply ENNReal.ofReal_le_ofReal
      have he : a*t = t*M₁/M₀ := by dsimp [a]; ring
      rw [he]
      exact hK t ht
    _ = ENNReal.ofReal (M₀^2) *
        (ENNReal.ofReal (a ^ (2*θ)) *
          ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ (-2*θ-1))*ENNReal.ofReal (sumKSquared μ w t u)) := by
      have he : (fun t : ℝ => ENNReal.ofReal (t ^ (-2*θ-1)) *
          (ENNReal.ofReal (M₀^2)*ENNReal.ofReal (sumKSquared μ w (a*t) u))) =
        (fun t => ENNReal.ofReal (M₀^2) *
          (ENNReal.ofReal (t ^ (-2*θ-1))*ENNReal.ofReal (sumKSquared μ w (a*t) u))) := by
        funext t
        ring
      rw [he,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        weightedPositiveHalfLine_scaling θ a ha (fun t => ENNReal.ofReal (sumKSquared μ w t u))]
    _ = _ := by rw [mul_assoc]


lemma sumInterpolation_interior_mem_of_KBound
    {X Y H G : ℕ → Type*} [∀ n, MeasurableSpace (X n)] [∀ n, MeasurableSpace (Y n)]
    [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace ℂ (H n)]
    [∀ n, NormedAddCommGroup (G n)] [∀ n, InnerProductSpace ℂ (G n)]
    (μ : ∀ n, Measure (X n)) (ν : ∀ n, Measure (Y n))
    (w : ∀ n, X n → ℝ) (v : ∀ n, Y n → ℝ)
    (hw : ∀ n, Measurable (w n)) (hv : ∀ n, Measurable (v n))
    (hw1 : ∀ n x, 1 ≤ w n x) (hv1 : ∀ n y, 1 ≤ v n y)
    (M₀ M₁ : ℝ) (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (u : GW.Spaces.sumWeightDomain (F := H) μ (fun n x => (w n x)^θ))
    (z : GW.Spaces.WeightSum (F := G) ν)
    (hK : ∀ t, 0 < t → sumKSquared ν v t z ≤ M₀^2*sumKSquared μ w (t*M₁/M₀) u.val) :
    z ∈ GW.Spaces.sumWeightDomain (F := G) ν (fun n y => (v n y)^θ) := by
  have hc := interpolationConstant_pos θ hθ0 hθ1
  have he := sumInterpolationMass_estimate_of_KBound μ ν w v hw hv hw1 hv1 M₀ M₁ hM₀ hM₁ u.val z hK θ hθ0 hθ1
  rw [sumInterpolationMass_norm μ (fun n x => (w n x)^θ) u] at he
  have hf : (ENNReal.ofReal (M₀^2)*ENNReal.ofReal ((M₁/M₀) ^ (2*θ))) *
      (ENNReal.ofReal (interpolationConstant θ) *
        ENNReal.ofReal (‖GW.Spaces.sumWeightValue (F := H) μ u‖^2)) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
  have ht := (lt_of_le_of_lt he (lt_top_iff_ne_top.mpr hf)).ne
  apply sumInterpolationMass_mem ν (fun n y => (v n y)^θ) (fun n => (hv n).pow_const θ)
  exact (ENNReal.lt_top_of_mul_ne_top_right ht (ENNReal.ofReal_pos.mpr hc).ne').ne



lemma sumWeightedInterpolation_interior_of_KBound
    {X Y H G : ℕ → Type*} [∀ n, MeasurableSpace (X n)] [∀ n, MeasurableSpace (Y n)]
    [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace ℂ (H n)]
    [∀ n, NormedAddCommGroup (G n)] [∀ n, InnerProductSpace ℂ (G n)]
    (μ : ∀ n, Measure (X n)) (ν : ∀ n, Measure (Y n))
    (w : ∀ n, X n → ℝ) (v : ∀ n, Y n → ℝ)
    (hw : ∀ n, Measurable (w n)) (hv : ∀ n, Measurable (v n))
    (hw1 : ∀ n x, 1 ≤ w n x) (hv1 : ∀ n y, 1 ≤ v n y)
    (M₀ M₁ : ℝ) (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (u : GW.Spaces.sumWeightDomain (F := H) μ (fun n x => (w n x)^θ))
    (z : GW.Spaces.WeightSum (F := G) ν)
    (hK : ∀ t, 0 < t → sumKSquared ν v t z ≤ M₀^2*sumKSquared μ w (t*M₁/M₀) u.val) :
    ∃ b : GW.Spaces.sumWeightDomain (F := G) ν (fun n y => (v n y)^θ),
      b.val = z ∧ ‖GW.Spaces.sumWeightValue (F := G) ν b‖ ≤
        M₀^(1-θ)*M₁^θ*‖GW.Spaces.sumWeightValue (F := H) μ u‖ := by
  let b : GW.Spaces.sumWeightDomain (F := G) ν (fun n y => (v n y)^θ) :=
    ⟨z,sumInterpolation_interior_mem_of_KBound μ ν w v hw hv hw1 hv1 M₀ M₁ hM₀ hM₁ θ hθ0 hθ1 u z hK⟩
  refine ⟨b,rfl,?_⟩
  have hc := interpolationConstant_pos θ hθ0 hθ1
  have he := sumInterpolationMass_estimate_of_KBound μ ν w v hw hv hw1 hv1 M₀ M₁ hM₀ hM₁ u.val z hK θ hθ0 hθ1
  have hbmass := sumInterpolationMass_norm ν (fun n y => (v n y)^θ) b
  change sumInterpolationMass ν (fun n y => (v n y)^θ) (z) = _ at hbmass
  rw [hbmass,sumInterpolationMass_norm μ (fun n x => (w n x)^θ) u] at he
  have hf : (ENNReal.ofReal (M₀^2)*ENNReal.ofReal ((M₁/M₀) ^ (2*θ))) *
      (ENNReal.ofReal (interpolationConstant θ) *
        ENNReal.ofReal (‖GW.Spaces.sumWeightValue (F := H) μ u‖^2)) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
  have hr := ENNReal.toReal_mono hf he
  simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal hc.le,
    ENNReal.toReal_ofReal (sq_nonneg _),
    ENNReal.toReal_ofReal (Real.rpow_nonneg (div_pos hM₁ hM₀).le _)] at hr
  have hs : ‖GW.Spaces.sumWeightValue (F := G) ν b‖^2 ≤
      M₀^2*(M₁/M₀)^(2*θ)*‖GW.Spaces.sumWeightValue (F := H) μ u‖^2 := by
    apply (mul_le_mul_iff_right₀ hc).mp
    nlinarith [hr]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg
    (mul_nonneg (Real.rpow_nonneg hM₀.le _) (Real.rpow_nonneg hM₁.le _)) (norm_nonneg _))).mp
  rw [mul_pow,interpolationCoefficient_sq M₀ M₁ θ hM₀ hM₁]
  exact hs



section SumEndpoint
variable {X Y H G : ℕ → Type*} [∀ n, MeasurableSpace (X n)] [∀ n, MeasurableSpace (Y n)]
  [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace ℂ (H n)]
  [∀ n, NormedAddCommGroup (G n)] [∀ n, InnerProductSpace ℂ (G n)]
  (μ : ∀ n, Measure (X n)) (ν : ∀ n, Measure (Y n))
  (w : ∀ n, X n → ℝ) (v : ∀ n, Y n → ℝ)
  (hw : ∀ n, Measurable (w n)) (hv : ∀ n, Measurable (v n))
  (hw1 : ∀ n x, 1 ≤ w n x) (hv1 : ∀ n y, 1 ≤ v n y)
  (T : GW.Spaces.WeightSum (F := H) μ →L[ℂ] GW.Spaces.WeightSum (F := G) ν)
  (M₀ M₁ : ℝ) (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
  (hT₀ : ∀ z, ‖T z‖ ≤ M₀*‖z‖)
  (hT₁ : ∀ a : GW.Spaces.sumWeightDomain (F := H) μ w,
    ∃ b : GW.Spaces.sumWeightDomain (F := G) ν v,
      b.val = T a.val ∧ ‖GW.Spaces.sumWeightValue (F := G) ν b‖ ≤ M₁*‖GW.Spaces.sumWeightValue (F := H) μ a‖)

include hw hw1 hM₀ hM₁ hT₀ hT₁ in
lemma sumKSquared_endpoint (t : ℝ) (ht : 0 < t) (u : GW.Spaces.WeightSum (F := H) μ) :
    sumKSquared ν v t (T u) ≤ M₀^2*sumKSquared μ w (t*M₁/M₀) u := by
  let s := t*M₁/M₀
  have hs : 0 < s := div_pos (mul_pos ht hM₁) hM₀
  let a := sumKMinimizer μ w hw hw1 s hs u
  obtain ⟨b,hb,hbnd⟩ := hT₁ a
  have hbelow : BddBelow (Set.range (sumKCost ν v t (T u))) := by
    refine ⟨0,?_⟩
    rintro _ ⟨b,rfl⟩
    exact add_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hle : sumKSquared ν v t (T u) ≤ sumKCost ν v t (T u) b := csInf_le hbelow (Set.mem_range_self b)
  have hzero := hT₀ (u-a.val)
  rw [map_sub] at hzero
  have hsq₀ := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM₀.le (norm_nonneg _))).mpr hzero
  have hsq₁ := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM₁.le (norm_nonneg _))).mpr hbnd
  have hcost : sumKCost ν v t (T u) b ≤ M₀^2*sumKCost μ w s u a := by
    unfold sumKCost
    rw [hb]
    have hscale : M₀^2*s^2 = t^2*M₁^2 := by dsimp [s]; field_simp
    nlinarith [mul_le_mul_of_nonneg_left hsq₁ (sq_nonneg t)]
  apply (hle.trans hcost).trans_eq
  congr 1
  exact (sumKCost_minimizer μ w hw hw1 s hs u).trans (sumKSquared_eq μ w hw hw1 s hs u).symm

include hw hv hw1 hv1 hM₀ hM₁ hT₀ hT₁ in
lemma sumInterpolationMass_estimate (u : GW.Spaces.WeightSum (F := H) μ)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    ENNReal.ofReal (interpolationConstant θ)*sumInterpolationMass ν (fun n y => (v n y)^θ) (T u) ≤
      (ENNReal.ofReal (M₀^2)*ENNReal.ofReal ((M₁/M₀)^(2*θ))) *
        (ENNReal.ofReal (interpolationConstant θ)*sumInterpolationMass μ (fun n x => (w n x)^θ) u) := by
  let a := M₁/M₀
  have ha : 0 < a := div_pos hM₁ hM₀
  unfold sumInterpolationMass
  rw [← sumK_extended_identity ν v hv hv1 θ hθ0 hθ1 (T u),
    ← sumK_extended_identity μ w hw hw1 θ hθ0 hθ1 u]
  calc
    _ ≤ ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ (-2*θ-1)) *
        (ENNReal.ofReal (M₀^2)*ENNReal.ofReal (sumKSquared μ w (a*t) u)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      apply mul_le_mul_right
      rw [← ENNReal.ofReal_mul (sq_nonneg M₀)]
      apply ENNReal.ofReal_le_ofReal
      have he : a*t = t*M₁/M₀ := by dsimp [a]; ring
      rw [he]
      exact sumKSquared_endpoint μ ν w v hw hw1 T M₀ M₁ hM₀ hM₁ hT₀ hT₁ t ht u
    _ = ENNReal.ofReal (M₀^2) *
        (ENNReal.ofReal (a ^ (2*θ)) *
          ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ (-2*θ-1))*ENNReal.ofReal (sumKSquared μ w t u)) := by
      have he : (fun t : ℝ => ENNReal.ofReal (t ^ (-2*θ-1)) *
          (ENNReal.ofReal (M₀^2)*ENNReal.ofReal (sumKSquared μ w (a*t) u))) =
        (fun t => ENNReal.ofReal (M₀^2) *
          (ENNReal.ofReal (t ^ (-2*θ-1))*ENNReal.ofReal (sumKSquared μ w (a*t) u))) := by
        funext t
        ring
      rw [he,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        weightedPositiveHalfLine_scaling θ a ha (fun t => ENNReal.ofReal (sumKSquared μ w t u))]
    _ = _ := by rw [mul_assoc]

include hw hv hw1 hv1 hM₀ hM₁ hT₀ hT₁ in
lemma sumInterpolation_interior_mem
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (u : GW.Spaces.sumWeightDomain (F := H) μ (fun n x => (w n x)^θ)) :
    T u.val ∈ GW.Spaces.sumWeightDomain (F := G) ν (fun n y => (v n y)^θ) := by
  have hc := interpolationConstant_pos θ hθ0 hθ1
  have he := sumInterpolationMass_estimate μ ν w v hw hv hw1 hv1 T M₀ M₁ hM₀ hM₁ hT₀ hT₁ u.val θ hθ0 hθ1
  rw [sumInterpolationMass_norm μ (fun n x => (w n x)^θ) u] at he
  have hf : (ENNReal.ofReal (M₀^2)*ENNReal.ofReal ((M₁/M₀) ^ (2*θ))) *
      (ENNReal.ofReal (interpolationConstant θ) *
        ENNReal.ofReal (‖GW.Spaces.sumWeightValue (F := H) μ u‖^2)) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
  have ht := (lt_of_le_of_lt he (lt_top_iff_ne_top.mpr hf)).ne
  apply sumInterpolationMass_mem ν (fun n y => (v n y)^θ) (fun n => (hv n).pow_const θ)
  exact (ENNReal.lt_top_of_mul_ne_top_right ht (ENNReal.ofReal_pos.mpr hc).ne').ne


include hw hv hw1 hv1 hM₀ hM₁ hT₀ hT₁ in
lemma sumWeightedInterpolation_interior
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (u : GW.Spaces.sumWeightDomain (F := H) μ (fun n x => (w n x)^θ)) :
    ∃ b : GW.Spaces.sumWeightDomain (F := G) ν (fun n y => (v n y)^θ),
      b.val = T u.val ∧ ‖GW.Spaces.sumWeightValue (F := G) ν b‖ ≤
        M₀^(1-θ)*M₁^θ*‖GW.Spaces.sumWeightValue (F := H) μ u‖ := by
  let b : GW.Spaces.sumWeightDomain (F := G) ν (fun n y => (v n y)^θ) :=
    ⟨T u.val,sumInterpolation_interior_mem μ ν w v hw hv hw1 hv1 T M₀ M₁ hM₀ hM₁ hT₀ hT₁ θ hθ0 hθ1 u⟩
  refine ⟨b,rfl,?_⟩
  have hc := interpolationConstant_pos θ hθ0 hθ1
  have he := sumInterpolationMass_estimate μ ν w v hw hv hw1 hv1 T M₀ M₁ hM₀ hM₁ hT₀ hT₁ u.val θ hθ0 hθ1
  have hbmass := sumInterpolationMass_norm ν (fun n y => (v n y)^θ) b
  change sumInterpolationMass ν (fun n y => (v n y)^θ) (T u.val) = _ at hbmass
  rw [hbmass,sumInterpolationMass_norm μ (fun n x => (w n x)^θ) u] at he
  have hf : (ENNReal.ofReal (M₀^2)*ENNReal.ofReal ((M₁/M₀) ^ (2*θ))) *
      (ENNReal.ofReal (interpolationConstant θ) *
        ENNReal.ofReal (‖GW.Spaces.sumWeightValue (F := H) μ u‖^2)) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
  have hr := ENNReal.toReal_mono hf he
  simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal hc.le,
    ENNReal.toReal_ofReal (sq_nonneg _),
    ENNReal.toReal_ofReal (Real.rpow_nonneg (div_pos hM₁ hM₀).le _)] at hr
  have hs : ‖GW.Spaces.sumWeightValue (F := G) ν b‖^2 ≤
      M₀^2*(M₁/M₀)^(2*θ)*‖GW.Spaces.sumWeightValue (F := H) μ u‖^2 := by
    apply (mul_le_mul_iff_right₀ hc).mp
    nlinarith [hr]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg
    (mul_nonneg (Real.rpow_nonneg hM₀.le _) (Real.rpow_nonneg hM₁.le _)) (norm_nonneg _))).mp
  rw [mul_pow,interpolationCoefficient_sq M₀ M₁ θ hM₀ hM₁]
  exact hs


include hw hv hw1 hv1 hM₀ hM₁ hT₀ hT₁ in
lemma sumWeightedInterpolation
    (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (u : GW.Spaces.sumWeightDomain (F := H) μ (fun n x => (w n x)^θ)) :
    ∃ b : GW.Spaces.sumWeightDomain (F := G) ν (fun n y => (v n y)^θ),
      b.val = T u.val ∧ ‖GW.Spaces.sumWeightValue (F := G) ν b‖ ≤
        M₀^(1-θ)*M₁^θ*‖GW.Spaces.sumWeightValue (F := H) μ u‖ := by
  by_cases hz : θ = 0
  · subst θ
    let b : GW.Spaces.sumWeightDomain (F := G) ν (fun n y => (v n y)^(0:ℝ)) :=
      ⟨T u.val,T u.val,fun n => Eventually.of_forall (fun y => by simp)⟩
    refine ⟨b,rfl,?_⟩
    have hu : GW.Spaces.sumWeightValue (F := H) μ u = u.val := by
      let a : GW.Spaces.sumWeightDomain (F := H) μ (fun _ _ => 1) := ⟨u.val,by simpa only [Real.rpow_zero] using u.property⟩
      exact (sumWeightValue_coeff_congr μ _ _ (fun _ _ => Real.rpow_zero _) u a rfl).trans (sumWeightValue_one μ a)
    have hb : GW.Spaces.sumWeightValue (F := G) ν b = T u.val := by
      let a : GW.Spaces.sumWeightDomain (F := G) ν (fun _ _ => 1) := ⟨b.val,by simpa only [Real.rpow_zero] using b.property⟩
      exact (sumWeightValue_coeff_congr ν _ _ (fun _ _ => Real.rpow_zero _) b a rfl).trans (sumWeightValue_one ν a)
    rw [hu,hb]
    simpa using hT₀ u.val
  by_cases ho : θ = 1
  · subst θ
    let a : GW.Spaces.sumWeightDomain (F := H) μ w := ⟨u.val,by simpa only [Real.rpow_one] using u.property⟩
    obtain ⟨b₀,hb₀,hbound⟩ := hT₁ a
    let b : GW.Spaces.sumWeightDomain (F := G) ν (fun n y => (v n y)^(1:ℝ)) :=
      ⟨b₀.val,by simpa only [Real.rpow_one] using b₀.property⟩
    refine ⟨b,hb₀,?_⟩
    have hu := sumWeightValue_coeff_congr μ _ _ (fun _ _ => Real.rpow_one _) u a rfl
    have hb := sumWeightValue_coeff_congr ν _ _ (fun _ _ => Real.rpow_one _) b b₀ rfl
    rw [hu,hb]
    simpa using hbound
  exact sumWeightedInterpolation_interior μ ν w v hw hv hw1 hv1 T M₀ M₁ hM₀ hM₁ hT₀ hT₁
    θ (lt_of_le_of_ne hθ0 (Ne.symm hz)) (lt_of_le_of_ne hθ1 ho) u

end SumEndpoint
lemma sumKMinimizerMap_invariant {X H : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace ℂ (H n)]
    (μ : ∀ n, Measure (X n)) (w : ∀ n, X n → ℝ) (hw : ∀ n, Measurable (w n))
    (S : ClosedSubmodule ℂ (GW.Spaces.WeightSum (F := H) μ))
    (hS : GW.Spaces.FunctionalSumWeightInvariant (F := H) μ S hw)
    (t : ℝ) (u : S) : sumKMinimizerMap μ w hw t u.val ∈ S := by
  have hm : Measurable (fun r : ℝ => (kMinimizerCoefficient r t : ℂ)) := by
    unfold kMinimizerCoefficient
    fun_prop
  have hb : ∀ r : ℝ, ‖(kMinimizerCoefficient r t : ℂ)‖ ≤ 1 := by
    intro r
    rw [Complex.norm_real,Real.norm_of_nonneg (kMinimizerCoefficient_bound r t).1]
    exact (kMinimizerCoefficient_bound r t).2
  exact hS _ hm hb u

lemma sumKSquared_restricted_endpoint
    {X Y H G : ℕ → Type*} [∀ n, MeasurableSpace (X n)] [∀ n, MeasurableSpace (Y n)]
    [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace ℂ (H n)]
    [∀ n, NormedAddCommGroup (G n)] [∀ n, InnerProductSpace ℂ (G n)]
    (μ : ∀ n, Measure (X n)) (ν : ∀ n, Measure (Y n))
    (w : ∀ n, X n → ℝ) (v : ∀ n, Y n → ℝ)
    (hw : ∀ n, Measurable (w n)) (hw1 : ∀ n x, 1 ≤ w n x)
    (S : ClosedSubmodule ℂ (GW.Spaces.WeightSum (F := H) μ))
    (R : ClosedSubmodule ℂ (GW.Spaces.WeightSum (F := G) ν))
    (hS : GW.Spaces.FunctionalSumWeightInvariant (F := H) μ S hw)
    (T : S →L[ℂ] R) (M₀ M₁ : ℝ) (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (hT₀ : ∀ z, ‖T z‖ ≤ M₀*‖z‖)
    (hT₁ : ∀ (a : GW.Spaces.sumWeightDomain (F := H) μ w) (ha : a.val ∈ S),
      ∃ b : GW.Spaces.sumWeightDomain (F := G) ν v,
        b.val = (T ⟨a.val,ha⟩).val ∧
          ‖GW.Spaces.sumWeightValue (F := G) ν b‖ ≤ M₁*‖GW.Spaces.sumWeightValue (F := H) μ a‖)
    (t : ℝ) (ht : 0 < t) (u : S) :
    sumKSquared ν v t (T u).val ≤ M₀^2*sumKSquared μ w (t*M₁/M₀) u.val := by
  let s := t*M₁/M₀
  have hs : 0 < s := div_pos (mul_pos ht hM₁) hM₀
  let a := sumKMinimizer μ w hw hw1 s hs u.val
  have haS : a.val ∈ S := sumKMinimizerMap_invariant μ w hw S hS s u
  let aS : S := ⟨a.val,haS⟩
  obtain ⟨b,hb,hbnd⟩ := hT₁ a haS
  have hbelow : BddBelow (Set.range (sumKCost ν v t (T u).val)) := by
    refine ⟨0,?_⟩
    rintro _ ⟨b,rfl⟩
    exact add_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hle : sumKSquared ν v t (T u).val ≤ sumKCost ν v t (T u).val b := csInf_le hbelow (Set.mem_range_self b)
  have hzero := hT₀ (u-aS)
  rw [map_sub] at hzero
  change ‖(T u).val-(T aS).val‖ ≤ M₀*‖u.val-a.val‖ at hzero
  have hsq₀ := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM₀.le (norm_nonneg _))).mpr hzero
  have hsq₁ := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM₁.le (norm_nonneg _))).mpr hbnd
  have hcost : sumKCost ν v t (T u).val b ≤ M₀^2*sumKCost μ w s u.val a := by
    unfold sumKCost
    rw [hb]
    change ‖(T u).val-(T aS).val‖^2+t^2*‖GW.Spaces.sumWeightValue (F := G) ν b‖^2 ≤ _
    have hscale : M₀^2*s^2 = t^2*M₁^2 := by dsimp [s]; field_simp
    nlinarith [mul_le_mul_of_nonneg_left hsq₁ (sq_nonneg t)]
  apply (hle.trans hcost).trans_eq
  congr 1
  exact (sumKCost_minimizer μ w hw hw1 s hs u.val).trans (sumKSquared_eq μ w hw hw1 s hs u.val).symm

lemma functionalSumWeightInvariant_rpow {X H : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace ℂ (H n)]
    (μ : ∀ n, Measure (X n)) {w : ∀ n, X n → ℝ} {hw : ∀ n, Measurable (w n)}
    {S : ClosedSubmodule ℂ (GW.Spaces.WeightSum (F := H) μ)}
    (hS : GW.Spaces.FunctionalSumWeightInvariant (F := H) μ S hw) (θ : ℝ) :
    GW.Spaces.FunctionalSumWeightInvariant (F := H) μ S (fun n => (hw n).pow_const θ) := by
  intro a ha c hc u
  exact hS (fun r => a (r^θ)) (ha.comp (measurable_id.pow_const θ)) (fun r => hc (r^θ)) u

lemma sumWeightedInterpolation_restricted_interior
    {X Y H G : ℕ → Type*} [∀ n, MeasurableSpace (X n)] [∀ n, MeasurableSpace (Y n)]
    [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace ℂ (H n)]
    [∀ n, NormedAddCommGroup (G n)] [∀ n, InnerProductSpace ℂ (G n)]
    (μ : ∀ n, Measure (X n)) (ν : ∀ n, Measure (Y n))
    (w : ∀ n, X n → ℝ) (v : ∀ n, Y n → ℝ)
    (hw : ∀ n, Measurable (w n)) (hv : ∀ n, Measurable (v n))
    (hw1 : ∀ n x, 1 ≤ w n x) (hv1 : ∀ n y, 1 ≤ v n y)
    (S : ClosedSubmodule ℂ (GW.Spaces.WeightSum (F := H) μ))
    (R : ClosedSubmodule ℂ (GW.Spaces.WeightSum (F := G) ν))
    (hS : GW.Spaces.FunctionalSumWeightInvariant (F := H) μ S hw)
    (hR : GW.Spaces.FunctionalSumWeightInvariant (F := G) ν R hv)
    (T : S →L[ℂ] R) (M₀ M₁ : ℝ) (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (hT₀ : ∀ z, ‖T z‖ ≤ M₀*‖z‖)
    (hT₁ : ∀ (a : GW.Spaces.sumWeightDomain (F := H) μ w) (ha : a.val ∈ S),
      ∃ b : GW.Spaces.sumWeightDomain (F := G) ν v,
        b.val = (T ⟨a.val,ha⟩).val ∧
          ‖GW.Spaces.sumWeightValue (F := G) ν b‖ ≤ M₁*‖GW.Spaces.sumWeightValue (F := H) μ a‖)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (u : S)
    (hu : u.val ∈ GW.Spaces.sumWeightDomain (F := H) μ (fun n x => (w n x)^θ)) :
    ∃ b : GW.Spaces.sumWeightDomain (F := G) ν (fun n y => (v n y)^θ),
      b.val = (T u).val ∧ ‖GW.Spaces.sumWeightValue (F := G) ν b‖ ≤
        M₀^(1-θ)*M₁^θ*‖GW.Spaces.sumWeightValue (F := H) μ ⟨u.val,hu⟩‖ ∧
      GW.Spaces.sumWeightValue (F := G) ν b ∈ R := by
  have hK := sumKSquared_restricted_endpoint μ ν w v hw hw1 S R hS T M₀ M₁ hM₀ hM₁ hT₀ hT₁
  obtain ⟨b,hb,hbound⟩ := sumWeightedInterpolation_interior_of_KBound μ ν w v hw hv hw1 hv1 M₀ M₁ hM₀ hM₁
    θ hθ0 hθ1 ⟨u.val,hu⟩ (T u).val (fun t ht => hK t ht u)
  refine ⟨b,hb,hbound,?_⟩
  apply GW.Spaces.sum_invariant_product_mem ν
    (GW.Spaces.sumWeightInvariant_of_functional ν (fun n y => Real.one_le_rpow (hv1 n y) hθ0.le)
      (functionalSumWeightInvariant_rpow ν hR θ)) b
  rw [hb]
  exact (T u).property

lemma weightedInterpolation_restricted
    {X Y H G : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (μ : Measure X) (ν : Measure Y) (w : X → ℝ) (v : Y → ℝ)
    (hw : Measurable w) (hv : Measurable v) (hw1 : ∀ x, 1 ≤ w x) (hv1 : ∀ y, 1 ≤ v y)
    (S : ClosedSubmodule ℂ (Lp H 2 μ)) (R : ClosedSubmodule ℂ (Lp G 2 ν))
    (hS : GW.Spaces.FunctionalWeightInvariant S hw) (hR : GW.Spaces.FunctionalWeightInvariant R hv)
    (T : S →L[ℂ] R) (M₀ M₁ : ℝ) (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (hT₀ : ∀ z, ‖T z‖ ≤ M₀*‖z‖)
    (hT₁ : ∀ (a : (GW.Analysis.realMultiplier (H := H) w μ).domain) (ha : a.val ∈ S),
      ∃ b : (GW.Analysis.realMultiplier (H := G) v ν).domain,
        b.val = (T ⟨a.val,ha⟩).val ∧
          ‖GW.Analysis.realMultiplier v ν b‖ ≤ M₁*‖GW.Analysis.realMultiplier w μ a‖)
    (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (u : S)
    (hu : u.val ∈ (GW.Analysis.realMultiplier (H := H) (fun x => (w x)^θ) μ).domain) :
    ∃ b : (GW.Analysis.realMultiplier (H := G) (fun y => (v y)^θ) ν).domain,
      b.val = (T u).val ∧
      ‖GW.Analysis.realMultiplier (fun y => (v y)^θ) ν b‖ ≤
        M₀^(1-θ)*M₁^θ*‖GW.Analysis.realMultiplier (fun x => (w x)^θ) μ ⟨u.val,hu⟩‖ ∧
      GW.Analysis.realMultiplier (fun y => (v y)^θ) ν b ∈ R := by
  have hresult : ∃ b : (GW.Analysis.realMultiplier (H := G) (fun y => (v y)^θ) ν).domain,
      b.val = (T u).val ∧ ‖GW.Analysis.realMultiplier (fun y => (v y)^θ) ν b‖ ≤
        M₀^(1-θ)*M₁^θ*‖GW.Analysis.realMultiplier (fun x => (w x)^θ) μ ⟨u.val,hu⟩‖ := by
    by_cases hz : θ = 0
    · subst θ
      let a : (GW.Analysis.realMultiplier (H := H) (fun x => (w x)^(0:ℝ)) μ).domain := ⟨u.val,hu⟩
      let b : (GW.Analysis.realMultiplier (H := G) (fun y => (v y)^(0:ℝ)) ν).domain :=
        ⟨(T u).val,(T u).val,Eventually.of_forall (fun y => by simp)⟩
      refine ⟨b,rfl,?_⟩
      have ha : GW.Analysis.realMultiplier (fun x => (w x)^(0:ℝ)) μ a = u.val := by
        apply Lp.ext
        filter_upwards [GW.Analysis.realMultiplier_ae (fun x => (w x)^(0:ℝ)) a] with x hx
        simpa using hx.symm
      have hb : GW.Analysis.realMultiplier (fun y => (v y)^(0:ℝ)) ν b = (T u).val := by
        apply Lp.ext
        filter_upwards [GW.Analysis.realMultiplier_ae (fun y => (v y)^(0:ℝ)) b] with y hy
        simpa using hy.symm
      change ‖GW.Analysis.realMultiplier (fun y => (v y)^(0:ℝ)) ν b‖ ≤ _*‖GW.Analysis.realMultiplier (fun x => (w x)^(0:ℝ)) μ a‖
      rw [ha,hb]
      simpa using hT₀ u
    by_cases ho : θ = 1
    · subst θ
      let a : (GW.Analysis.realMultiplier (H := H) w μ).domain := ⟨u.val,by simpa only [Real.rpow_one] using hu⟩
      obtain ⟨b₀,hb₀,hbound⟩ := hT₁ a u.property
      let b : (GW.Analysis.realMultiplier (H := G) (fun y => (v y)^(1:ℝ)) ν).domain :=
        ⟨b₀.val,by simpa only [Real.rpow_one] using b₀.property⟩
      refine ⟨b,hb₀,?_⟩
      have ha : GW.Analysis.realMultiplier (fun x => (w x)^(1:ℝ)) μ ⟨u.val,hu⟩ = GW.Analysis.realMultiplier w μ a := by
        apply Lp.ext
        filter_upwards [GW.Analysis.realMultiplier_ae (fun x => (w x)^(1:ℝ)) ⟨u.val,hu⟩,
          GW.Analysis.realMultiplier_ae w a] with x hx hy
        exact hx.symm.trans (by simpa only [Real.rpow_one] using hy)
      have hb : GW.Analysis.realMultiplier (fun y => (v y)^(1:ℝ)) ν b = GW.Analysis.realMultiplier v ν b₀ := by
        apply Lp.ext
        filter_upwards [GW.Analysis.realMultiplier_ae (fun y => (v y)^(1:ℝ)) b,
          GW.Analysis.realMultiplier_ae v b₀] with y hx hy
        exact hx.symm.trans (by simpa only [Real.rpow_one] using hy)
      rw [ha,hb]
      simpa using hbound
    obtain ⟨b,hb,hbound,_⟩ := weightedInterpolation_restricted_interior μ ν w v hw hv hw1 hv1 S R hS hR T M₀ M₁ hM₀ hM₁ hT₀ hT₁
      θ (lt_of_le_of_ne hθ0 (Ne.symm hz)) (lt_of_le_of_ne hθ1 ho) u hu
    exact ⟨b,hb,hbound⟩
  obtain ⟨b,hb,hbound⟩ := hresult
  refine ⟨b,hb,hbound,?_⟩
  apply GW.Spaces.invariant_product_mem
    (GW.Spaces.weightInvariant_of_functional (fun y => Real.one_le_rpow (hv1 y) hθ0)
      (functionalWeightInvariant_rpow hR θ)) b
  rw [hb]
  exact (T u).property

lemma sumWeightedInterpolation_restricted
    {X Y H G : ℕ → Type*} [∀ n, MeasurableSpace (X n)] [∀ n, MeasurableSpace (Y n)]
    [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace ℂ (H n)]
    [∀ n, NormedAddCommGroup (G n)] [∀ n, InnerProductSpace ℂ (G n)]
    (μ : ∀ n, Measure (X n)) (ν : ∀ n, Measure (Y n))
    (w : ∀ n, X n → ℝ) (v : ∀ n, Y n → ℝ)
    (hw : ∀ n, Measurable (w n)) (hv : ∀ n, Measurable (v n))
    (hw1 : ∀ n x, 1 ≤ w n x) (hv1 : ∀ n y, 1 ≤ v n y)
    (S : ClosedSubmodule ℂ (GW.Spaces.WeightSum (F := H) μ))
    (R : ClosedSubmodule ℂ (GW.Spaces.WeightSum (F := G) ν))
    (hS : GW.Spaces.FunctionalSumWeightInvariant (F := H) μ S hw)
    (hR : GW.Spaces.FunctionalSumWeightInvariant (F := G) ν R hv)
    (T : S →L[ℂ] R) (M₀ M₁ : ℝ) (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (hT₀ : ∀ z, ‖T z‖ ≤ M₀*‖z‖)
    (hT₁ : ∀ (a : GW.Spaces.sumWeightDomain (F := H) μ w) (ha : a.val ∈ S),
      ∃ b : GW.Spaces.sumWeightDomain (F := G) ν v,
        b.val = (T ⟨a.val,ha⟩).val ∧
          ‖GW.Spaces.sumWeightValue (F := G) ν b‖ ≤ M₁*‖GW.Spaces.sumWeightValue (F := H) μ a‖)
    (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (u : S)
    (hu : u.val ∈ GW.Spaces.sumWeightDomain (F := H) μ (fun n x => (w n x)^θ)) :
    ∃ b : GW.Spaces.sumWeightDomain (F := G) ν (fun n y => (v n y)^θ),
      b.val = (T u).val ∧ ‖GW.Spaces.sumWeightValue (F := G) ν b‖ ≤
        M₀^(1-θ)*M₁^θ*‖GW.Spaces.sumWeightValue (F := H) μ ⟨u.val,hu⟩‖ ∧
      GW.Spaces.sumWeightValue (F := G) ν b ∈ R := by
  have hresult : ∃ b : GW.Spaces.sumWeightDomain (F := G) ν (fun n y => (v n y)^θ),
      b.val = (T u).val ∧ ‖GW.Spaces.sumWeightValue (F := G) ν b‖ ≤
        M₀^(1-θ)*M₁^θ*‖GW.Spaces.sumWeightValue (F := H) μ ⟨u.val,hu⟩‖ := by
    by_cases hz : θ = 0
    · subst θ
      let a : GW.Spaces.sumWeightDomain (F := H) μ (fun n x => (w n x)^(0:ℝ)) := ⟨u.val,hu⟩
      let b : GW.Spaces.sumWeightDomain (F := G) ν (fun n y => (v n y)^(0:ℝ)) :=
        ⟨(T u).val,(T u).val,fun n => Eventually.of_forall (fun y => by simp)⟩
      refine ⟨b,rfl,?_⟩
      have ha : GW.Spaces.sumWeightValue (F := H) μ a = u.val := by
        let a₀ : GW.Spaces.sumWeightDomain (F := H) μ (fun _ _ => 1) :=
          ⟨a.val,by simpa only [Real.rpow_zero] using a.property⟩
        exact (sumWeightValue_coeff_congr μ _ _ (fun _ _ => Real.rpow_zero _) a a₀ rfl).trans (sumWeightValue_one μ a₀)
      have hb : GW.Spaces.sumWeightValue (F := G) ν b = (T u).val := by
        let b₀ : GW.Spaces.sumWeightDomain (F := G) ν (fun _ _ => 1) :=
          ⟨b.val,by simpa only [Real.rpow_zero] using b.property⟩
        exact (sumWeightValue_coeff_congr ν _ _ (fun _ _ => Real.rpow_zero _) b b₀ rfl).trans (sumWeightValue_one ν b₀)
      change ‖GW.Spaces.sumWeightValue (F := G) ν b‖ ≤ _*‖GW.Spaces.sumWeightValue (F := H) μ a‖
      rw [ha,hb]
      simpa using hT₀ u
    by_cases ho : θ = 1
    · subst θ
      let a : GW.Spaces.sumWeightDomain (F := H) μ w := ⟨u.val,by simpa only [Real.rpow_one] using hu⟩
      obtain ⟨b₀,hb₀,hbound⟩ := hT₁ a u.property
      let b : GW.Spaces.sumWeightDomain (F := G) ν (fun n y => (v n y)^(1:ℝ)) :=
        ⟨b₀.val,by simpa only [Real.rpow_one] using b₀.property⟩
      refine ⟨b,hb₀,?_⟩
      have ha := sumWeightValue_coeff_congr μ _ _ (fun _ _ => Real.rpow_one _) ⟨u.val,hu⟩ a rfl
      have hb := sumWeightValue_coeff_congr ν _ _ (fun _ _ => Real.rpow_one _) b b₀ rfl
      rw [ha,hb]
      simpa using hbound
    obtain ⟨b,hb,hbound,_⟩ := sumWeightedInterpolation_restricted_interior μ ν w v hw hv hw1 hv1 S R hS hR T M₀ M₁ hM₀ hM₁ hT₀ hT₁
      θ (lt_of_le_of_ne hθ0 (Ne.symm hz)) (lt_of_le_of_ne hθ1 ho) u hu
    exact ⟨b,hb,hbound⟩
  obtain ⟨b,hb,hbound⟩ := hresult
  refine ⟨b,hb,hbound,?_⟩
  apply GW.Spaces.sum_invariant_product_mem ν
    (GW.Spaces.sumWeightInvariant_of_functional ν (fun n y => Real.one_le_rpow (hv1 n y) hθ0)
      (functionalSumWeightInvariant_rpow ν hR θ)) b
  rw [hb]
  exact (T u).property

def electronProductMultiplier (n : ℕ) (b : GW.Space → ℂ) (hb : Measurable b)
    {C : ℝ} (hC : ∀ q, ‖b q‖ ≤ C) :
    Lp ℂ 2 ((volume : Measure GW.Space).prod (GW.Fock.sectorMeasure n)) →L[ℂ]
      Lp ℂ 2 ((volume : Measure GW.Space).prod (GW.Fock.sectorMeasure n)) :=
  GW.Analysis.boundedMultiplier (fun p => b p.1) (hb.comp measurable_fst)
    (Eventually.of_forall (fun p => hC p.1))

set_option backward.isDefEq.respectTransparency.types false in
lemma electronProductMultiplier_commutes (n : ℕ) (τ : Equiv.Perm (Fin n))
    (b : GW.Space → ℂ) (hb : Measurable b) {C : ℝ} (hC : ∀ q, ‖b q‖ ≤ C)
    (u : Lp ℂ 2 ((volume : Measure GW.Space).prod (GW.Fock.sectorMeasure n))) :
    GW.Fock.productPermutation volume n τ (electronProductMultiplier n b hb hC u) =
      electronProductMultiplier n b hb hC (GW.Fock.productPermutation volume n τ u) := by
  let ν := GW.Fock.sectorMeasure n
  let ρ := GW.Fock.coordinatePermutation n τ
  have hρ := GW.Fock.coordinatePermutation_preserving n τ
  have hp := (MeasurePreserving.id (volume : Measure GW.Space)).prod hρ
  apply Lp.ext
  filter_upwards [GW.Fock.productPermutation_ae volume n τ (electronProductMultiplier n b hb hC u),
    hp.quasiMeasurePreserving.ae (GW.Analysis.boundedMultiplier_ae (fun p : GW.Space × GW.Fock.Coordinates n => b p.1)
      (hb.comp measurable_fst) (Eventually.of_forall (fun p => hC p.1)) u),
    GW.Analysis.boundedMultiplier_ae (fun p : GW.Space × GW.Fock.Coordinates n => b p.1)
      (hb.comp measurable_fst) (Eventually.of_forall (fun p => hC p.1)) (GW.Fock.productPermutation volume n τ u),
    GW.Fock.productPermutation_ae volume n τ u] with p h₁ h₂ h₃ h₄
  change GW.Fock.productPermutation volume n τ (electronProductMultiplier n b hb hC u) p =
    GW.Analysis.boundedMultiplier (fun p : GW.Space × GW.Fock.Coordinates n => b p.1) _ _
      (GW.Fock.productPermutation volume n τ u) p
  rw [h₁,← h₃,h₄]
  have he : Prod.map id ρ p = (p.1,fun i => p.2 (τ i)) := by
    change (p.1,GW.Fock.coordinatePermutation n τ p.2) = _
    rw [GW.Fock.coordinatePermutation_eq]
  have hh := h₂.symm
  change electronProductMultiplier n b hb hC u (Prod.map id ρ p) =
    b (Prod.map id ρ p).1 • u (Prod.map id ρ p) at hh
  rw [he] at hh
  exact hh

lemma electronProductMultiplier_symmetric (n : ℕ) (b : GW.Space → ℂ) (hb : Measurable b)
    {C : ℝ} (hC : ∀ q, ‖b q‖ ≤ C)
    (u : Lp ℂ 2 ((volume : Measure GW.Space).prod (GW.Fock.sectorMeasure n)))
    (hu : u ∈ Set.range (GW.Fock.symmetricProductInclusion volume n)) :
    electronProductMultiplier n b hb hC u ∈ Set.range (GW.Fock.symmetricProductInclusion volume n) := by
  apply (GW.Fock.symmetricProduct_range volume n _).mpr
  intro τ
  rw [electronProductMultiplier_commutes,(GW.Fock.symmetricProduct_range volume n u).mp hu τ]

lemma quadraticKSquared_restricted_endpoint_minimal
    {X Y H G : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (μ : Measure X) (ν : Measure Y) (w : X → ℝ) (v : Y → ℝ)
    (hw : Measurable w) (hw1 : ∀ x, 1 ≤ w x)
    (S : ClosedSubmodule ℂ (Lp H 2 μ)) (R : ClosedSubmodule ℂ (Lp G 2 ν))
    (hmin : ∀ t, 0 < t → ∀ u : S, kMinimizerMap μ w hw t u.val ∈ S)
    (T : S →L[ℂ] R) (M₀ M₁ : ℝ) (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (hT₀ : ∀ z, ‖T z‖ ≤ M₀*‖z‖)
    (hT₁ : ∀ (a : (GW.Analysis.realMultiplier (H := H) w μ).domain) (ha : a.val ∈ S),
      ∃ b : (GW.Analysis.realMultiplier (H := G) v ν).domain,
        b.val = (T ⟨a.val,ha⟩).val ∧
          ‖GW.Analysis.realMultiplier v ν b‖ ≤ M₁*‖GW.Analysis.realMultiplier w μ a‖)
    (t : ℝ) (ht : 0 < t) (u : S) :
    quadraticKSquared ν v t (T u).val ≤ M₀^2*quadraticKSquared μ w (t*M₁/M₀) u.val := by
  let s := t*M₁/M₀
  have hs : 0 < s := div_pos (mul_pos ht hM₁) hM₀
  let a := kMinimizer μ w hw hw1 s hs u.val
  have haS : a.val ∈ S := hmin s hs u
  let aS : S := ⟨a.val,haS⟩
  obtain ⟨b,hb,hbnd⟩ := hT₁ a haS
  have hbelow : BddBelow (Set.range (quadraticKCost ν v t (T u).val)) :=
    ⟨0,fun _ hz => by obtain ⟨z,rfl⟩ := hz; exact quadraticKCost_nonneg ν v t (T u).val z⟩
  have hle : quadraticKSquared ν v t (T u).val ≤ quadraticKCost ν v t (T u).val b :=
    csInf_le hbelow (Set.mem_range_self b)
  have hzero := hT₀ (u-aS)
  rw [map_sub] at hzero
  change ‖(T u).val-(T aS).val‖ ≤ M₀*‖u.val-a.val‖ at hzero
  have hsq₀ := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM₀.le (norm_nonneg _))).mpr hzero
  have hsq₁ := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM₁.le (norm_nonneg _))).mpr hbnd
  have hcost : quadraticKCost ν v t (T u).val b ≤ M₀^2*quadraticKCost μ w s u.val a := by
    unfold quadraticKCost
    rw [hb]
    change ‖(T u).val-(T aS).val‖^2+t^2*‖GW.Analysis.realMultiplier v ν b‖^2 ≤ _
    have hscale : M₀^2*s^2 = t^2*M₁^2 := by dsimp [s]; field_simp
    nlinarith [mul_le_mul_of_nonneg_left hsq₁ (sq_nonneg t)]
  apply (hle.trans hcost).trans_eq
  congr 1
  exact (quadraticKCost_minimizer μ w hw hw1 s hs u.val).trans
    (quadraticKSquared_eq μ w hw hw1 s hs u.val).symm


lemma sumKSquared_restricted_endpoint_minimal
    {X Y H G : ℕ → Type*} [∀ n, MeasurableSpace (X n)] [∀ n, MeasurableSpace (Y n)]
    [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace ℂ (H n)]
    [∀ n, NormedAddCommGroup (G n)] [∀ n, InnerProductSpace ℂ (G n)]
    (μ : ∀ n, Measure (X n)) (ν : ∀ n, Measure (Y n))
    (w : ∀ n, X n → ℝ) (v : ∀ n, Y n → ℝ)
    (hw : ∀ n, Measurable (w n)) (hw1 : ∀ n x, 1 ≤ w n x)
    (S : ClosedSubmodule ℂ (GW.Spaces.WeightSum (F := H) μ))
    (R : ClosedSubmodule ℂ (GW.Spaces.WeightSum (F := G) ν))
    (hmin : ∀ t, 0 < t → ∀ u : S, sumKMinimizerMap μ w hw t u.val ∈ S)
    (T : S →L[ℂ] R) (M₀ M₁ : ℝ) (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (hT₀ : ∀ z, ‖T z‖ ≤ M₀*‖z‖)
    (hT₁ : ∀ (a : GW.Spaces.sumWeightDomain (F := H) μ w) (ha : a.val ∈ S),
      ∃ b : GW.Spaces.sumWeightDomain (F := G) ν v,
        b.val = (T ⟨a.val,ha⟩).val ∧
          ‖GW.Spaces.sumWeightValue (F := G) ν b‖ ≤ M₁*‖GW.Spaces.sumWeightValue (F := H) μ a‖)
    (t : ℝ) (ht : 0 < t) (u : S) :
    sumKSquared ν v t (T u).val ≤ M₀^2*sumKSquared μ w (t*M₁/M₀) u.val := by
  let s := t*M₁/M₀
  have hs : 0 < s := div_pos (mul_pos ht hM₁) hM₀
  let a := sumKMinimizer μ w hw hw1 s hs u.val
  have haS : a.val ∈ S := hmin s hs u
  let aS : S := ⟨a.val,haS⟩
  obtain ⟨b,hb,hbnd⟩ := hT₁ a haS
  have hbelow : BddBelow (Set.range (sumKCost ν v t (T u).val)) := by
    refine ⟨0,?_⟩
    rintro _ ⟨b,rfl⟩
    exact add_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hle : sumKSquared ν v t (T u).val ≤ sumKCost ν v t (T u).val b := csInf_le hbelow (Set.mem_range_self b)
  have hzero := hT₀ (u-aS)
  rw [map_sub] at hzero
  change ‖(T u).val-(T aS).val‖ ≤ M₀*‖u.val-a.val‖ at hzero
  have hsq₀ := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM₀.le (norm_nonneg _))).mpr hzero
  have hsq₁ := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM₁.le (norm_nonneg _))).mpr hbnd
  have hcost : sumKCost ν v t (T u).val b ≤ M₀^2*sumKCost μ w s u.val a := by
    unfold sumKCost
    rw [hb]
    change ‖(T u).val-(T aS).val‖^2+t^2*‖GW.Spaces.sumWeightValue (F := G) ν b‖^2 ≤ _
    have hscale : M₀^2*s^2 = t^2*M₁^2 := by dsimp [s]; field_simp
    nlinarith [mul_le_mul_of_nonneg_left hsq₁ (sq_nonneg t)]
  apply (hle.trans hcost).trans_eq
  congr 1
  exact (sumKCost_minimizer μ w hw hw1 s hs u.val).trans (sumKSquared_eq μ w hw hw1 s hs u.val).symm


lemma weightedInterpolation_restricted_minimal
    {X Y H G : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (μ : Measure X) (ν : Measure Y) (w : X → ℝ) (v : Y → ℝ)
    (hw : Measurable w) (hv : Measurable v) (hw1 : ∀ x, 1 ≤ w x) (hv1 : ∀ y, 1 ≤ v y)
    (S : ClosedSubmodule ℂ (Lp H 2 μ)) (R : ClosedSubmodule ℂ (Lp G 2 ν))
    (hmin : ∀ t, 0 < t → ∀ u : S, kMinimizerMap μ w hw t u.val ∈ S)
    (T : S →L[ℂ] R) (M₀ M₁ : ℝ) (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (hT₀ : ∀ z, ‖T z‖ ≤ M₀*‖z‖)
    (hT₁ : ∀ (a : (GW.Analysis.realMultiplier (H := H) w μ).domain) (ha : a.val ∈ S),
      ∃ b : (GW.Analysis.realMultiplier (H := G) v ν).domain,
        b.val = (T ⟨a.val,ha⟩).val ∧
          ‖GW.Analysis.realMultiplier v ν b‖ ≤ M₁*‖GW.Analysis.realMultiplier w μ a‖)
    (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hRθ : GW.Spaces.WeightInvariant R (hv.pow_const θ) (fun y => Real.one_le_rpow (hv1 y) hθ0)) (u : S)
    (hu : u.val ∈ (GW.Analysis.realMultiplier (H := H) (fun x => (w x)^θ) μ).domain) :
    ∃ b : (GW.Analysis.realMultiplier (H := G) (fun y => (v y)^θ) ν).domain,
      b.val = (T u).val ∧
      ‖GW.Analysis.realMultiplier (fun y => (v y)^θ) ν b‖ ≤
        M₀^(1-θ)*M₁^θ*‖GW.Analysis.realMultiplier (fun x => (w x)^θ) μ ⟨u.val,hu⟩‖ ∧
      GW.Analysis.realMultiplier (fun y => (v y)^θ) ν b ∈ R := by
  have hresult : ∃ b : (GW.Analysis.realMultiplier (H := G) (fun y => (v y)^θ) ν).domain,
      b.val = (T u).val ∧ ‖GW.Analysis.realMultiplier (fun y => (v y)^θ) ν b‖ ≤
        M₀^(1-θ)*M₁^θ*‖GW.Analysis.realMultiplier (fun x => (w x)^θ) μ ⟨u.val,hu⟩‖ := by
    by_cases hz : θ = 0
    · subst θ
      let a : (GW.Analysis.realMultiplier (H := H) (fun x => (w x)^(0:ℝ)) μ).domain := ⟨u.val,hu⟩
      let b : (GW.Analysis.realMultiplier (H := G) (fun y => (v y)^(0:ℝ)) ν).domain :=
        ⟨(T u).val,(T u).val,Eventually.of_forall (fun y => by simp)⟩
      refine ⟨b,rfl,?_⟩
      have ha : GW.Analysis.realMultiplier (fun x => (w x)^(0:ℝ)) μ a = u.val := by
        apply Lp.ext
        filter_upwards [GW.Analysis.realMultiplier_ae (fun x => (w x)^(0:ℝ)) a] with x hx
        simpa using hx.symm
      have hb : GW.Analysis.realMultiplier (fun y => (v y)^(0:ℝ)) ν b = (T u).val := by
        apply Lp.ext
        filter_upwards [GW.Analysis.realMultiplier_ae (fun y => (v y)^(0:ℝ)) b] with y hy
        simpa using hy.symm
      change ‖GW.Analysis.realMultiplier (fun y => (v y)^(0:ℝ)) ν b‖ ≤ _*‖GW.Analysis.realMultiplier (fun x => (w x)^(0:ℝ)) μ a‖
      rw [ha,hb]
      simpa using hT₀ u
    by_cases ho : θ = 1
    · subst θ
      let a : (GW.Analysis.realMultiplier (H := H) w μ).domain := ⟨u.val,by simpa only [Real.rpow_one] using hu⟩
      obtain ⟨b₀,hb₀,hbound⟩ := hT₁ a u.property
      let b : (GW.Analysis.realMultiplier (H := G) (fun y => (v y)^(1:ℝ)) ν).domain :=
        ⟨b₀.val,by simpa only [Real.rpow_one] using b₀.property⟩
      refine ⟨b,hb₀,?_⟩
      have ha : GW.Analysis.realMultiplier (fun x => (w x)^(1:ℝ)) μ ⟨u.val,hu⟩ = GW.Analysis.realMultiplier w μ a := by
        apply Lp.ext
        filter_upwards [GW.Analysis.realMultiplier_ae (fun x => (w x)^(1:ℝ)) ⟨u.val,hu⟩,
          GW.Analysis.realMultiplier_ae w a] with x hx hy
        exact hx.symm.trans (by simpa only [Real.rpow_one] using hy)
      have hb : GW.Analysis.realMultiplier (fun y => (v y)^(1:ℝ)) ν b = GW.Analysis.realMultiplier v ν b₀ := by
        apply Lp.ext
        filter_upwards [GW.Analysis.realMultiplier_ae (fun y => (v y)^(1:ℝ)) b,
          GW.Analysis.realMultiplier_ae v b₀] with y hx hy
        exact hx.symm.trans (by simpa only [Real.rpow_one] using hy)
      rw [ha,hb]
      simpa using hbound
    obtain ⟨b,hb,hbound⟩ := weightedInterpolation_interior_of_KBound μ ν w v hw hv hw1 hv1 M₀ M₁ hM₀ hM₁
      θ (lt_of_le_of_ne hθ0 (Ne.symm hz)) (lt_of_le_of_ne hθ1 ho) ⟨u.val,hu⟩ (T u).val
      (fun t ht => quadraticKSquared_restricted_endpoint_minimal μ ν w v hw hw1 S R hmin T M₀ M₁ hM₀ hM₁ hT₀ hT₁ t ht u)
    exact ⟨b,hb,hbound⟩
  obtain ⟨b,hb,hbound⟩ := hresult
  refine ⟨b,hb,hbound,?_⟩
  apply GW.Spaces.invariant_product_mem
    hRθ b
  rw [hb]
  exact (T u).property


lemma sumWeightedInterpolation_restricted_minimal
    {X Y H G : ℕ → Type*} [∀ n, MeasurableSpace (X n)] [∀ n, MeasurableSpace (Y n)]
    [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace ℂ (H n)]
    [∀ n, NormedAddCommGroup (G n)] [∀ n, InnerProductSpace ℂ (G n)]
    (μ : ∀ n, Measure (X n)) (ν : ∀ n, Measure (Y n))
    (w : ∀ n, X n → ℝ) (v : ∀ n, Y n → ℝ)
    (hw : ∀ n, Measurable (w n)) (hv : ∀ n, Measurable (v n))
    (hw1 : ∀ n x, 1 ≤ w n x) (hv1 : ∀ n y, 1 ≤ v n y)
    (S : ClosedSubmodule ℂ (GW.Spaces.WeightSum (F := H) μ))
    (R : ClosedSubmodule ℂ (GW.Spaces.WeightSum (F := G) ν))
    (hmin : ∀ t, 0 < t → ∀ u : S, sumKMinimizerMap μ w hw t u.val ∈ S)
    (T : S →L[ℂ] R) (M₀ M₁ : ℝ) (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (hT₀ : ∀ z, ‖T z‖ ≤ M₀*‖z‖)
    (hT₁ : ∀ (a : GW.Spaces.sumWeightDomain (F := H) μ w) (ha : a.val ∈ S),
      ∃ b : GW.Spaces.sumWeightDomain (F := G) ν v,
        b.val = (T ⟨a.val,ha⟩).val ∧
          ‖GW.Spaces.sumWeightValue (F := G) ν b‖ ≤ M₁*‖GW.Spaces.sumWeightValue (F := H) μ a‖)
    (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hRθ : GW.Spaces.SumWeightInvariant (F := G) ν R (fun n => (hv n).pow_const θ)
      (fun n y => Real.one_le_rpow (hv1 n y) hθ0)) (u : S)
    (hu : u.val ∈ GW.Spaces.sumWeightDomain (F := H) μ (fun n x => (w n x)^θ)) :
    ∃ b : GW.Spaces.sumWeightDomain (F := G) ν (fun n y => (v n y)^θ),
      b.val = (T u).val ∧ ‖GW.Spaces.sumWeightValue (F := G) ν b‖ ≤
        M₀^(1-θ)*M₁^θ*‖GW.Spaces.sumWeightValue (F := H) μ ⟨u.val,hu⟩‖ ∧
      GW.Spaces.sumWeightValue (F := G) ν b ∈ R := by
  have hresult : ∃ b : GW.Spaces.sumWeightDomain (F := G) ν (fun n y => (v n y)^θ),
      b.val = (T u).val ∧ ‖GW.Spaces.sumWeightValue (F := G) ν b‖ ≤
        M₀^(1-θ)*M₁^θ*‖GW.Spaces.sumWeightValue (F := H) μ ⟨u.val,hu⟩‖ := by
    by_cases hz : θ = 0
    · subst θ
      let a : GW.Spaces.sumWeightDomain (F := H) μ (fun n x => (w n x)^(0:ℝ)) := ⟨u.val,hu⟩
      let b : GW.Spaces.sumWeightDomain (F := G) ν (fun n y => (v n y)^(0:ℝ)) :=
        ⟨(T u).val,(T u).val,fun n => Eventually.of_forall (fun y => by simp)⟩
      refine ⟨b,rfl,?_⟩
      have ha : GW.Spaces.sumWeightValue (F := H) μ a = u.val := by
        let a₀ : GW.Spaces.sumWeightDomain (F := H) μ (fun _ _ => 1) :=
          ⟨a.val,by simpa only [Real.rpow_zero] using a.property⟩
        exact (sumWeightValue_coeff_congr μ _ _ (fun _ _ => Real.rpow_zero _) a a₀ rfl).trans (sumWeightValue_one μ a₀)
      have hb : GW.Spaces.sumWeightValue (F := G) ν b = (T u).val := by
        let b₀ : GW.Spaces.sumWeightDomain (F := G) ν (fun _ _ => 1) :=
          ⟨b.val,by simpa only [Real.rpow_zero] using b.property⟩
        exact (sumWeightValue_coeff_congr ν _ _ (fun _ _ => Real.rpow_zero _) b b₀ rfl).trans (sumWeightValue_one ν b₀)
      change ‖GW.Spaces.sumWeightValue (F := G) ν b‖ ≤ _*‖GW.Spaces.sumWeightValue (F := H) μ a‖
      rw [ha,hb]
      simpa using hT₀ u
    by_cases ho : θ = 1
    · subst θ
      let a : GW.Spaces.sumWeightDomain (F := H) μ w := ⟨u.val,by simpa only [Real.rpow_one] using hu⟩
      obtain ⟨b₀,hb₀,hbound⟩ := hT₁ a u.property
      let b : GW.Spaces.sumWeightDomain (F := G) ν (fun n y => (v n y)^(1:ℝ)) :=
        ⟨b₀.val,by simpa only [Real.rpow_one] using b₀.property⟩
      refine ⟨b,hb₀,?_⟩
      have ha := sumWeightValue_coeff_congr μ _ _ (fun _ _ => Real.rpow_one _) ⟨u.val,hu⟩ a rfl
      have hb := sumWeightValue_coeff_congr ν _ _ (fun _ _ => Real.rpow_one _) b b₀ rfl
      rw [ha,hb]
      simpa using hbound
    obtain ⟨b,hb,hbound⟩ := sumWeightedInterpolation_interior_of_KBound μ ν w v hw hv hw1 hv1 M₀ M₁ hM₀ hM₁
      θ (lt_of_le_of_ne hθ0 (Ne.symm hz)) (lt_of_le_of_ne hθ1 ho) ⟨u.val,hu⟩ (T u).val
      (fun t ht => sumKSquared_restricted_endpoint_minimal μ ν w v hw hw1 S R hmin T M₀ M₁ hM₀ hM₁ hT₀ hT₁ t ht u)
    exact ⟨b,hb,hbound⟩
  obtain ⟨b,hb,hbound⟩ := hresult
  refine ⟨b,hb,hbound,?_⟩
  apply GW.Spaces.sum_invariant_product_mem ν
    hRθ b
  rw [hb]
  exact (T u).property


lemma sumWeightedInterpolation_unitary
    {X Y H G : ℕ → Type*} {A B : Type*} [∀ n, MeasurableSpace (X n)] [∀ n, MeasurableSpace (Y n)]
    [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace ℂ (H n)]
    [∀ n, NormedAddCommGroup (G n)] [∀ n, InnerProductSpace ℂ (G n)]
    [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    [NormedAddCommGroup B] [InnerProductSpace ℂ B]
    (μ : ∀ n, Measure (X n)) (ν : ∀ n, Measure (Y n)) (w : ∀ n, X n → ℝ) (v : ∀ n, Y n → ℝ)
    (hw : ∀ n, Measurable (w n)) (hv : ∀ n, Measurable (v n)) (hw1 : ∀ n x, 1 ≤ w n x) (hv1 : ∀ n y, 1 ≤ v n y)
    (U : A ≃ₗᵢ[ℂ] GW.Spaces.WeightSum (F := H) μ) (V : B ≃ₗᵢ[ℂ] GW.Spaces.WeightSum (F := G) ν)
    (T : A →L[ℂ] B) (M₀ M₁ : ℝ) (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (hT₀ : ∀ z, ‖T z‖ ≤ M₀*‖z‖)
    (hT₁ : ∀ a : GW.Spaces.sumWeightDomain (F := H) μ w,
      ∃ b : GW.Spaces.sumWeightDomain (F := G) ν v,
        b.val = V (T (U.symm a.val)) ∧
          ‖GW.Spaces.sumWeightValue (F := G) ν b‖ ≤ M₁*‖GW.Spaces.sumWeightValue (F := H) μ a‖)
    (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (z : A)
    (hz : U z ∈ GW.Spaces.sumWeightDomain (F := H) μ (fun n x => (w n x)^θ)) :
    ∃ b : GW.Spaces.sumWeightDomain (F := G) ν (fun n y => (v n y)^θ),
      b.val = V (T z) ∧ ‖GW.Spaces.sumWeightValue (F := G) ν b‖ ≤
        M₀^(1-θ)*M₁^θ*‖GW.Spaces.sumWeightValue (F := H) μ ⟨U z,hz⟩‖ := by
  let S := V.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (T.comp U.symm.toContinuousLinearEquiv.toContinuousLinearMap)
  have hS₀ : ∀ u, ‖S u‖ ≤ M₀*‖u‖ := by
    intro u
    change ‖V (T (U.symm u))‖ ≤ _
    rw [V.norm_map]
    exact (hT₀ (U.symm u)).trans_eq (congrArg (fun r : ℝ => M₀*r) (U.symm.norm_map u))
  obtain ⟨b,hb,hbound⟩ := sumWeightedInterpolation μ ν w v hw hv hw1 hv1 S M₀ M₁ hM₀ hM₁ hS₀ hT₁ θ hθ0 hθ1 ⟨U z,hz⟩
  refine ⟨b,?_,hbound⟩
  change b.val = V (T (U.symm (U z))) at hb
  simpa only [U.symm_apply_apply] using hb

end GW.Operators
