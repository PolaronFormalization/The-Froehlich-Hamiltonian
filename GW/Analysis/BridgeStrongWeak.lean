module
public import GW.Analysis.BridgePhaseDerivative
public import Mathlib.MeasureTheory.Group.Integral
@[expose] public section
noncomputable section
open MeasureTheory Filter Set Function
open scoped Topology InnerProductSpace ENNReal Pointwise Interval
namespace GW.Analysis
section StrongPartial

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def HasStrongPartial (u d : GW.Space → E) (j : Fin 3) : Prop :=
  ∀ x, HasDerivAt (fun t : ℝ => u (x+t • momentumAxis j)) (d x) 0

lemma strongPartial_zero_off_support {u d : GW.Space → E} {j : Fin 3}
    (hd : HasStrongPartial u d j) (x : GW.Space) (hx : x ∉ tsupport u) :
    d x = 0 := by
  have he : (fun t : ℝ => u (x+t • momentumAxis j)) =ᶠ[𝓝 0] fun _ => (0:E) := by
    have hcont : ContinuousAt (fun t : ℝ => x+t • momentumAxis j) 0 := (by fun_prop : Continuous _).continuousAt
    have hn : (tsupport u)ᶜ ∈ 𝓝 (x+(0:ℝ) • momentumAxis j) := by
      simpa only [zero_smul,add_zero] using (isClosed_tsupport u).isOpen_compl.mem_nhds hx
    filter_upwards [hcont.eventually hn] with t ht
    exact image_eq_zero_of_notMem_tsupport ht
  exact (hd x).unique ((hasDerivAt_const (0:ℝ) (0:E)).congr_of_eventuallyEq he)

lemma strongPartial_hasCompactSupport {u d : GW.Space → E} {j : Fin 3}
    (hu : HasCompactSupport u) (hd : HasStrongPartial u d j) : HasCompactSupport d := by
  have h : tsupport d ⊆ tsupport u := by
    apply closure_minimal _ (isClosed_tsupport u)
    intro x hx
    by_contra! h
    exact hx (strongPartial_zero_off_support hd x h)
  exact hu.of_isClosed_subset (isClosed_tsupport d) h

lemma strongPartial_at_param {u d : GW.Space → E} {j : Fin 3}
    (hd : HasStrongPartial u d j) (x : GW.Space) (a : ℝ) :
    HasDerivAt (fun t : ℝ => u (x+t • momentumAxis j)) (d (x+a • momentumAxis j)) a := by
  let D : Fin 3 → GW.Space → E := fun _ => d
  have h := hd (x+a • momentumAxis j)
  have ht : HasDerivAt (fun t : ℝ => t-a) 1 a := (hasDerivAt_id a).sub_const a
  have hp := HasDerivAt.scomp_of_eq a h ht (sub_self a).symm
  rw [one_smul] at hp
  have he : (fun t : ℝ => u ((x+a • momentumAxis j)+(t-a) • momentumAxis j)) =
      fun t : ℝ => u (x+t • momentumAxis j) := by
    funext t
    rw [add_assoc,← add_smul]
    congr 2
    ring
  exact he ▸ (show HasDerivAt (fun t : ℝ => u ((x+a • momentumAxis j)+(t-a) • momentumAxis j))
    (d (x+a • momentumAxis j)) a from hp)

def strongPartialDiff (u : GW.Space → E) (j : Fin 3) (h : ℝ) (x : GW.Space) : E :=
  h⁻¹ • (u (x+h • momentumAxis j)-u x)

lemma strongPartialDiff_bound {u d : GW.Space → E} {j : Fin 3}
    (hd : HasStrongPartial u d j) (hc : Continuous d) {C : ℝ} (hC : ∀ x, ‖d x‖ ≤ C)
    (h : ℝ) (x : GW.Space) :
    ‖strongPartialDiff u j h x‖ ≤ C := by
  by_cases hh : h = 0
  · rw [hh,strongPartialDiff,inv_zero,zero_smul,norm_zero]
    exact (norm_nonneg (d x)).trans (hC x)
  let g := fun t : ℝ => d (x+t • momentumAxis j)
  have hg : Continuous g := hc.comp (by fun_prop)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ => u (x+t • momentumAxis j)) (f' := g) (a := 0) (b := h)
    (fun t _ => strongPartial_at_param hd x t) (hg.intervalIntegrable 0 h)
  simp only [zero_smul,add_zero] at hi
  rw [strongPartialDiff,← hi,norm_smul,Real.norm_eq_abs,abs_inv]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := h) (C := C) (f := g) (fun t _ => hC _)
  rw [sub_zero] at hb
  calc
    _ ≤ |h|⁻¹ * (C*|h|) := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (abs_nonneg h))
    _ = _ := by field_simp [abs_ne_zero.mpr hh]

def strongPartialThickening (u : GW.Space → E) : Set GW.Space :=
  tsupport u + Metric.closedBall 0 1

lemma strongPartialThickening_compact {u : GW.Space → E} (hu : HasCompactSupport u) :
    IsCompact (strongPartialThickening u) :=
  IsCompact.add (show IsCompact (tsupport u) from hu) (isCompact_closedBall _ _)

lemma strongPartialDiff_zero_off_thickening (u : GW.Space → E) (j : Fin 3) (h : ℝ)
    (hh : |h| ≤ 1) (x : GW.Space) (hx : x ∉ strongPartialThickening u) :
    strongPartialDiff u j h x = 0 := by
  have h₀ : x ∉ tsupport u := by
    intro hm
    apply hx
    exact ⟨x,hm,0,by simp [Metric.mem_closedBall],add_zero _⟩
  have h₁ : x+h • momentumAxis j ∉ tsupport u := by
    intro hm
    apply hx
    refine ⟨x+h • momentumAxis j,hm,-(h • momentumAxis j),?_,by abel⟩
    rw [Metric.mem_closedBall,dist_zero_right,norm_neg,norm_smul,Real.norm_eq_abs,momentumAxis_norm,mul_one]
    exact hh
  rw [strongPartialDiff,image_eq_zero_of_notMem_tsupport h₀,image_eq_zero_of_notMem_tsupport h₁,sub_zero,smul_zero]

def compactFunctionL2 (u : GW.Space → E) (hu : Continuous u) (hs : HasCompactSupport u) :
    Lp E 2 (volume : Measure GW.Space) :=
  (hu.memLp_of_hasCompactSupport hs).toLp u

lemma compactFunctionL2_ae (u : GW.Space → E) (hu : Continuous u) (hs : HasCompactSupport u) :
    compactFunctionL2 u hu hs =ᵐ[(volume : Measure GW.Space)] u :=
  MemLp.coeFn_toLp _

lemma strongPartialDiff_memLp (u : GW.Space → E) (hu : Continuous u) (hs : HasCompactSupport u)
    (j : Fin 3) (h : ℝ) : MemLp (strongPartialDiff u j h) 2 (volume : Measure GW.Space) := by
  have hm : MemLp u 2 (volume : Measure GW.Space) := hu.memLp_of_hasCompactSupport hs
  have ht := hm.comp_measurePreserving (measurePreserving_add_right (volume : Measure GW.Space) (h • momentumAxis j))
  exact (ht.sub hm).const_smul h⁻¹

def strongPartialDiffL2 (u : GW.Space → E) (hu : Continuous u) (hs : HasCompactSupport u)
    (j : Fin 3) (h : ℝ) : Lp E 2 (volume : Measure GW.Space) :=
  (strongPartialDiff_memLp u hu hs j h).toLp _

lemma strongPartialDiffL2_ae (u : GW.Space → E) (hu : Continuous u) (hs : HasCompactSupport u)
    (j : Fin 3) (h : ℝ) : strongPartialDiffL2 u hu hs j h =ᵐ[(volume : Measure GW.Space)] strongPartialDiff u j h :=
  MemLp.coeFn_toLp _

lemma strongPartialDiffL2_tendsto {u d : GW.Space → E} {j : Fin 3}
    (hu : Continuous u) (hs : HasCompactSupport u) (hd : HasStrongPartial u d j) (hc : Continuous d)
    (hN : ℕ → ℝ) (hh : Tendsto hN atTop (𝓝[≠] (0:ℝ))) (hb : ∀ n, |hN n| ≤ 1) :
    Tendsto (fun n => strongPartialDiffL2 u hu hs j (hN n)) atTop
      (𝓝 (compactFunctionL2 d hc (strongPartial_hasCompactSupport hs hd))) := by
  obtain ⟨C,hC⟩ := hc.bounded_above_of_compact_support (strongPartial_hasCompactSupport hs hd)
  have hC₀ : 0 ≤ C := (norm_nonneg (d 0)).trans (hC 0)
  let K := strongPartialThickening u
  have hK : IsCompact K := strongPartialThickening_compact hs
  let g : GW.Space → ℝ := K.indicator (fun _ => C)
  have hgm : Measurable g := measurable_const.indicator hK.isClosed.measurableSet
  have hgs : HasCompactSupport g := by
    have he : tsupport g ⊆ K := by
      apply closure_minimal _ hK.isClosed
      intro k hk
      by_contra! h
      exact hk (Set.indicator_of_notMem h _)
    exact hK.of_isClosed_subset (isClosed_tsupport g) he
  have hg : MemLp g 2 (volume : Measure GW.Space) :=
    hgs.memLp_of_bound hgm.aestronglyMeasurable C (Eventually.of_forall (fun k => by
      by_cases hk : k ∈ K
      · rw [show g k = C from Set.indicator_of_mem hk _,Real.norm_of_nonneg hC₀]
      · rw [show g k = 0 from Set.indicator_of_notMem hk _,norm_zero]
        exact hC₀))
  have hl : ∀ᵐ k ∂(volume : Measure GW.Space),
      Tendsto (fun n => strongPartialDiff u j (hN n) k) atTop (𝓝 (d k)) := by
    apply Eventually.of_forall
    intro k
    have h : Tendsto (fun t => strongPartialDiff u j t k) (𝓝[≠] (0:ℝ)) (𝓝 (d k)) := by
      simpa only [zero_add,zero_smul,add_zero,strongPartialDiff] using (hd k).tendsto_slope_zero
    exact h.comp hh
  have hbound (n : ℕ) : ∀ᵐ k ∂(volume : Measure GW.Space), ‖strongPartialDiff u j (hN n) k‖ ≤ g k := by
    apply Eventually.of_forall
    intro k
    by_cases hk : k ∈ K
    · rw [show g k = C from Set.indicator_of_mem hk _]
      exact strongPartialDiff_bound hd hc hC (hN n) k
    · rw [show g k = 0 from Set.indicator_of_notMem hk _,
        strongPartialDiff_zero_off_thickening u j (hN n) (hb n) k hk,norm_zero]
  obtain ⟨h₁,h₂,ht⟩ := dominated_l2_convergence (𝕜 := ℂ)
    (fun n => (strongPartialDiff_memLp u hu hs j (hN n)).aestronglyMeasurable) hl hgm
    ((memLp_two_iff_integrable_sq hgm.aestronglyMeasurable).mp hg) hbound
  have he (n : ℕ) : (h₁ n).toLp (strongPartialDiff u j (hN n)) = strongPartialDiffL2 u hu hs j (hN n) := by
    apply Lp.ext
    exact (MemLp.coeFn_toLp (h₁ n)).trans (strongPartialDiffL2_ae u hu hs j _).symm
  have he' : h₂.toLp d = compactFunctionL2 d hc (strongPartial_hasCompactSupport hs hd) := by
    apply Lp.ext
    exact (MemLp.coeFn_toLp h₂).trans (compactFunctionL2_ae d hc _).symm
  simp_rw [he,he'] at ht
  exact tendsto_iff_norm_sub_tendsto_zero.mpr ht

lemma memLp_inner_pairing {u w : GW.Space → E}
    (hu : MemLp u 2 (volume : Measure GW.Space)) (hw : MemLp w 2 (volume : Measure GW.Space)) :
    ⟪hw.toLp w,hu.toLp u⟫_ℂ = ∫ x, ⟪w x,u x⟫_ℂ ∂(volume : Measure GW.Space) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp hu,MemLp.coeFn_toLp hw] with x hx hy
  rw [hx,hy]

lemma memLp_inner_integrable {u w : GW.Space → E}
    (hu : MemLp u 2 (volume : Measure GW.Space)) (hw : MemLp w 2 (volume : Measure GW.Space)) :
    Integrable (fun x => ⟪w x,u x⟫_ℂ) (volume : Measure GW.Space) := by
  apply (L2.integrable_inner (hw.toLp w) (hu.toLp u)).congr
  filter_upwards [MemLp.coeFn_toLp hu,MemLp.coeFn_toLp hw] with x hx hy
  rw [hx,hy]

lemma strongPartialDiff_pairing_integrals {u w : GW.Space → E} {j : Fin 3}
    (hu : MemLp u 2 (volume : Measure GW.Space)) (hw : MemLp w 2 (volume : Measure GW.Space))
    (h : ℝ) :
    (∫ x, ⟪w x,strongPartialDiff u j h x⟫_ℂ ∂(volume : Measure GW.Space)) =
      -(∫ x, ⟪strongPartialDiff w j (-h) x,u x⟫_ℂ ∂(volume : Measure GW.Space)) := by
  let a := h • momentumAxis j
  let iZero := fun x : GW.Space => ⟪w x,u x⟫_ℂ
  let iPlus := fun x : GW.Space => ⟪w x,u (x+a)⟫_ℂ
  let iMinus := fun x : GW.Space => ⟪w (x-a),u x⟫_ℂ
  have h₀ : Integrable iZero (volume : Measure GW.Space) := memLp_inner_integrable hu hw
  have hPlus : Integrable iPlus (volume : Measure GW.Space) :=
    memLp_inner_integrable (hu.comp_measurePreserving (measurePreserving_add_right volume a)) hw
  have hMinus : Integrable iMinus (volume : Measure GW.Space) :=
    memLp_inner_integrable hu (hw.comp_measurePreserving (measurePreserving_sub_right volume a))
  have he : (∫ x, iPlus x ∂(volume : Measure GW.Space)) = ∫ x, iMinus x ∂(volume : Measure GW.Space) := by
    calc
      _ = ∫ x, iMinus (x+a) ∂(volume : Measure GW.Space) := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun x => by simp [iPlus,iMinus,add_sub_cancel_right])
      _ = _ := integral_add_right_eq_self iMinus a
  have hleft (x : GW.Space) : ⟪w x,strongPartialDiff u j h x⟫_ℂ =
      (↑h⁻¹ : ℂ) * (iPlus x-iZero x) := by
    rw [strongPartialDiff,RCLike.real_smul_eq_coe_smul (K := ℂ),inner_smul_right,inner_sub_right]
    rfl
  have hright (x : GW.Space) : ⟪strongPartialDiff w j (-h) x,u x⟫_ℂ =
      -(↑h⁻¹ : ℂ) * (iMinus x-iZero x) := by
    rw [strongPartialDiff,RCLike.real_smul_eq_coe_smul (K := ℂ),inner_smul_left,
      inv_neg,inner_sub_left,neg_smul]
    change (starRingEnd ℂ) (Complex.ofReal (-h⁻¹)) * (⟪w (x + -a),u x⟫_ℂ - iZero x) = _
    rw [Complex.conj_ofReal,Complex.ofReal_neg]
    rw [← sub_eq_add_neg x a]
  simp_rw [hleft,hright,integral_const_mul]
  rw [integral_sub hPlus h₀,integral_sub hMinus h₀,he]
  ring

lemma strongPartialDiff_pairing {u w : GW.Space → E} {j : Fin 3}
    (hu : Continuous u) (hs : HasCompactSupport u)
    (hw : Continuous w) (hws : HasCompactSupport w) (h : ℝ) :
    ⟪compactFunctionL2 w hw hws,strongPartialDiffL2 u hu hs j h⟫_ℂ =
      -⟪strongPartialDiffL2 w hw hws j (-h),compactFunctionL2 u hu hs⟫_ℂ := by
  have hu' : MemLp u 2 (volume : Measure GW.Space) := hu.memLp_of_hasCompactSupport hs
  have hw' : MemLp w 2 (volume : Measure GW.Space) := hw.memLp_of_hasCompactSupport hws
  exact (memLp_inner_pairing (strongPartialDiff_memLp u hu hs j h) hw').trans
    ((strongPartialDiff_pairing_integrals hu' hw' h).trans
      (congrArg Neg.neg (memLp_inner_pairing hu' (strongPartialDiff_memLp w hw hws j (-h))).symm))

def strongPartialStep (n : ℕ) : ℝ := 1/((n:ℝ)+1)

lemma strongPartialStep_tendsto (sgn : ℝ) (hsgn : sgn ≠ 0) :
    Tendsto (fun n => sgn * strongPartialStep n) atTop (𝓝[≠] (0:ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul sgn
    simpa only [strongPartialStep,mul_zero] using h
  · apply Eventually.of_forall
    intro n
    change sgn * (1/((n:ℝ)+1)) ≠ 0
    exact mul_ne_zero hsgn (one_div_ne_zero (by positivity))

lemma strongPartialStep_abs_le (n : ℕ) : |strongPartialStep n| ≤ 1 := by
  have hp : 0 < (n:ℝ)+1 := by positivity
  rw [strongPartialStep,abs_of_nonneg (one_div_nonneg.mpr hp.le)]
  exact (div_le_iff₀ hp).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])

lemma strongPartial_weakPairing {u d w e : GW.Space → E} {j : Fin 3}
    (hu : Continuous u) (hus : HasCompactSupport u) (hud : HasStrongPartial u d j) (huc : Continuous d)
    (hw : Continuous w) (hws : HasCompactSupport w) (hwd : HasStrongPartial w e j) (hwc : Continuous e) :
    ⟪compactFunctionL2 w hw hws,compactFunctionL2 d huc (strongPartial_hasCompactSupport hus hud)⟫_ℂ =
      -⟪compactFunctionL2 e hwc (strongPartial_hasCompactSupport hws hwd),compactFunctionL2 u hu hus⟫_ℂ := by
  have hp : Tendsto strongPartialStep atTop (𝓝[≠] (0:ℝ)) := by
    simpa only [one_mul] using strongPartialStep_tendsto 1 one_ne_zero
  have hm : Tendsto (fun n => -strongPartialStep n) atTop (𝓝[≠] (0:ℝ)) := by
    simpa only [neg_one_mul] using strongPartialStep_tendsto (-1) (by norm_num)
  have h₁ := strongPartialDiffL2_tendsto hu hus hud huc strongPartialStep hp strongPartialStep_abs_le
  have h₂ := strongPartialDiffL2_tendsto hw hws hwd hwc (fun n => -strongPartialStep n) hm
    (fun n => by rw [abs_neg]; exact strongPartialStep_abs_le n)
  have hleft := (tendsto_const_nhds (x := compactFunctionL2 w hw hws)).inner (𝕜 := ℂ) h₁
  have hright := (h₂.inner (𝕜 := ℂ) (tendsto_const_nhds (x := compactFunctionL2 u hu hus))).neg
  apply tendsto_nhds_unique hleft
  exact hright.congr' (Eventually.of_forall (fun n => (strongPartialDiff_pairing hu hus hw hws (j := j) (strongPartialStep n)).symm))

lemma strongPartial_weakMomentum {u d w e : GW.Space → E} {j : Fin 3}
    (hu : Continuous u) (hus : HasCompactSupport u) (hud : HasStrongPartial u d j) (huc : Continuous d)
    (hw : Continuous w) (hws : HasCompactSupport w) (hwd : HasStrongPartial w e j) (hwc : Continuous e) :
    ⟪(-Complex.I) • compactFunctionL2 e hwc (strongPartial_hasCompactSupport hws hwd),
      compactFunctionL2 u hu hus⟫_ℂ =
        ⟪compactFunctionL2 w hw hws,
          (-Complex.I) • compactFunctionL2 d huc (strongPartial_hasCompactSupport hus hud)⟫_ℂ := by
  rw [inner_smul_left,inner_smul_right,map_neg,Complex.conj_I,neg_neg,
    strongPartial_weakPairing hu hus hud huc hw hws hwd hwc]
  ring

def smoothTestAxisDerivative (w : GW.Space → E) (j : Fin 3) (x : GW.Space) : E :=
  fderiv ℝ w x (momentumAxis j)

lemma smoothTestAxisDerivative_continuous (w : GW.Space → E) (j : Fin 3) (hw : ContDiff ℝ 1 w) :
    Continuous (smoothTestAxisDerivative w j) :=
  (hw.continuous_fderiv (by norm_num)).clm_apply continuous_const

lemma smoothTest_hasStrongPartial (w : GW.Space → E) (j : Fin 3) (hw : ContDiff ℝ 1 w) :
    HasStrongPartial w (smoothTestAxisDerivative w j) j := by
  intro x
  have h : HasDerivAt (fun t : ℝ => x+t • momentumAxis j) (momentumAxis j) 0 := by
    have h := ((hasDerivAt_id (0:ℝ)).smul_const (momentumAxis j)).const_add x
    simpa only [id_eq,one_smul] using h
  have hw' := ((hw.differentiable (by norm_num)) x).hasFDerivAt
  exact hw'.comp_hasDerivAt_of_eq 0 h (by simp)

lemma smoothTest_weakPairing {u d w : GW.Space → E} {j : Fin 3}
    (hu : Continuous u) (hus : HasCompactSupport u) (hud : HasStrongPartial u d j) (huc : Continuous d)
    (hw : ContDiff ℝ 1 w) (hws : HasCompactSupport w) :
    ⟪compactFunctionL2 w hw.continuous hws,
      compactFunctionL2 d huc (strongPartial_hasCompactSupport hus hud)⟫_ℂ =
      -⟪compactFunctionL2 (smoothTestAxisDerivative w j) (smoothTestAxisDerivative_continuous w j hw)
        (strongPartial_hasCompactSupport hws (smoothTest_hasStrongPartial w j hw)),
        compactFunctionL2 u hu hus⟫_ℂ :=
  strongPartial_weakPairing hu hus hud huc hw.continuous hws (smoothTest_hasStrongPartial w j hw)
    (smoothTestAxisDerivative_continuous w j hw)

end StrongPartial
end GW.Analysis
